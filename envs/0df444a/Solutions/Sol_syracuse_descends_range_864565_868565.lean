-- Prove2me | solution 1 for syracuse_descends_range_864565_868565
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:40.972895+00:00
-- url     : https://prove2.me/submissions/ac52d5f0-9e47-4c6b-9f2d-d09b1ba5e033

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


theorem B2195525 : Blo 864565 2195525 := bbase (se 4 (by rfl) ⟨205830, by rfl⟩ : syracuseStep 2195525 = 411661) (by norm_num)
theorem B1409125 : Blo 864565 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B2195869 : Blo 864565 2195869 := bbase (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) (by norm_num)
theorem B4391333 : Blo 864565 4391333 := bbase (se 4 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 4391333 = 823375) (by norm_num)
theorem B2195981 : Blo 864565 2195981 := bbase (se 3 (by rfl) ⟨411746, by rfl⟩ : syracuseStep 2195981 = 823493) (by norm_num)
theorem B2196173 : Blo 864565 2196173 := bbase (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) (by norm_num)
theorem B1409909 : Blo 864565 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B7406549 : Blo 864565 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B2196517 : Blo 864565 2196517 := bbase (se 4 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 2196517 = 411847) (by norm_num)
theorem B5276821 : Blo 864565 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B2196629 : Blo 864565 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2196821 : Blo 864565 2196821 := bbase (se 12 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2196821 = 1609) (by norm_num)
theorem B2197165 : Blo 864565 2197165 := bbase (se 3 (by rfl) ⟨411968, by rfl⟩ : syracuseStep 2197165 = 823937) (by norm_num)
theorem B4392629 : Blo 864565 4392629 := bbase (se 5 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 4392629 = 411809) (by norm_num)
theorem B2197277 : Blo 864565 2197277 := bbase (se 3 (by rfl) ⟨411989, by rfl⟩ : syracuseStep 2197277 = 823979) (by norm_num)
theorem B2918213 : Blo 864565 2918213 := bbase (se 4 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 2918213 = 547165) (by norm_num)
theorem B2197469 : Blo 864565 2197469 := bbase (se 3 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 2197469 = 824051) (by norm_num)
theorem B2918645 : Blo 864565 2918645 := bbase (se 5 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 2918645 = 273623) (by norm_num)
theorem B2197813 : Blo 864565 2197813 := bbase (se 5 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 2197813 = 206045) (by norm_num)
theorem B3705173 : Blo 864565 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B4163957 : Blo 864565 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B2197925 : Blo 864565 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B2198117 : Blo 864565 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B2919077 : Blo 864565 2919077 := bbase (se 4 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 2919077 = 547327) (by norm_num)
theorem B12684053 : Blo 864565 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B1641397 : Blo 864565 1641397 := bbase (se 5 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 1641397 = 153881) (by norm_num)
theorem B2198461 : Blo 864565 2198461 := bbase (se 3 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 2198461 = 824423) (by norm_num)
theorem B4393925 : Blo 864565 4393925 := bbase (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) (by norm_num)
theorem B1641541 : Blo 864565 1641541 := bbase (se 4 (by rfl) ⟨153894, by rfl⟩ : syracuseStep 1641541 = 307789) (by norm_num)
theorem B2919509 : Blo 864565 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1641701 : Blo 864565 1641701 := bbase (se 4 (by rfl) ⟨153909, by rfl⟩ : syracuseStep 1641701 = 307819) (by norm_num)
theorem B3706181 : Blo 864565 3706181 := bbase (se 4 (by rfl) ⟨347454, by rfl⟩ : syracuseStep 3706181 = 694909) (by norm_num)
theorem B1641845 : Blo 864565 1641845 := bbase (se 5 (by rfl) ⟨76961, by rfl⟩ : syracuseStep 1641845 = 153923) (by norm_num)
theorem B2919941 : Blo 864565 2919941 := bbase (se 4 (by rfl) ⟨273744, by rfl⟩ : syracuseStep 2919941 = 547489) (by norm_num)
theorem B1642133 : Blo 864565 1642133 := bbase (se 6 (by rfl) ⟨38487, by rfl⟩ : syracuseStep 1642133 = 76975) (by norm_num)
theorem B1642285 : Blo 864565 1642285 := bbase (se 3 (by rfl) ⟨307928, by rfl⟩ : syracuseStep 1642285 = 615857) (by norm_num)
theorem B986941 : Blo 864565 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B2920373 : Blo 864565 2920373 := bbase (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) (by norm_num)
theorem B1642589 : Blo 864565 1642589 := bbase (se 3 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 1642589 = 615971) (by norm_num)
theorem B6590645 : Blo 864565 6590645 := bbase (se 5 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 6590645 = 617873) (by norm_num)
theorem B4395221 : Blo 864565 4395221 := bbase (se 7 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 4395221 = 103013) (by norm_num)
theorem B2920805 : Blo 864565 2920805 := bbase (se 4 (by rfl) ⟨273825, by rfl⟩ : syracuseStep 2920805 = 547651) (by norm_num)
theorem B2921237 : Blo 864565 2921237 := bbase (se 6 (by rfl) ⟨68466, by rfl⟩ : syracuseStep 2921237 = 136933) (by norm_num)
theorem B1643341 : Blo 864565 1643341 := bbase (se 3 (by rfl) ⟨308126, by rfl⟩ : syracuseStep 1643341 = 616253) (by norm_num)
theorem B1643485 : Blo 864565 1643485 := bbase (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) (by norm_num)
theorem B4166645 : Blo 864565 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B3707957 : Blo 864565 3707957 := bbase (se 5 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 3707957 = 347621) (by norm_num)
theorem B1643645 : Blo 864565 1643645 := bbase (se 3 (by rfl) ⟨308183, by rfl⟩ : syracuseStep 1643645 = 616367) (by norm_num)
theorem B2921669 : Blo 864565 2921669 := bbase (se 4 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 2921669 = 547813) (by norm_num)
theorem B1643789 : Blo 864565 1643789 := bbase (se 3 (by rfl) ⟨308210, by rfl⟩ : syracuseStep 1643789 = 616421) (by norm_num)
theorem B1479973 : Blo 864565 1479973 := bbase (se 4 (by rfl) ⟨138747, by rfl⟩ : syracuseStep 1479973 = 277495) (by norm_num)
theorem B1316261 : Blo 864565 1316261 := bbase (se 4 (by rfl) ⟨123399, by rfl⟩ : syracuseStep 1316261 = 246799) (by norm_num)
theorem B4396517 : Blo 864565 4396517 := bbase (se 4 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 4396517 = 824347) (by norm_num)
theorem B1644077 : Blo 864565 1644077 := bbase (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) (by norm_num)
theorem B2922101 : Blo 864565 2922101 := bbase (se 5 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 2922101 = 273947) (by norm_num)
theorem B1644229 : Blo 864565 1644229 := bbase (se 4 (by rfl) ⟨154146, by rfl⟩ : syracuseStep 1644229 = 308293) (by norm_num)
theorem B3282869 : Blo 864565 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B1054661 : Blo 864565 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B1644533 : Blo 864565 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B2922533 : Blo 864565 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B923833 : Blo 864565 923833 := bbase (se 2 (by rfl) ⟨346437, by rfl⟩ : syracuseStep 923833 = 692875) (by norm_num)
theorem B923905 : Blo 864565 923905 := bbase (se 2 (by rfl) ⟨346464, by rfl⟩ : syracuseStep 923905 = 692929) (by norm_num)
theorem B924085 : Blo 864565 924085 := bbase (se 5 (by rfl) ⟨43316, by rfl⟩ : syracuseStep 924085 = 86633) (by norm_num)
theorem B2922965 : Blo 864565 2922965 := bbase (se 7 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 2922965 = 68507) (by norm_num)
theorem B1645285 : Blo 864565 1645285 := bbase (se 4 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 1645285 = 308491) (by norm_num)
theorem B989965 : Blo 864565 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B2464613 : Blo 864565 2464613 := bbase (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) (by norm_num)
theorem B924529 : Blo 864565 924529 := bbase (se 2 (by rfl) ⟨346698, by rfl⟩ : syracuseStep 924529 = 693397) (by norm_num)
theorem B1645429 : Blo 864565 1645429 := bbase (se 5 (by rfl) ⟨77129, by rfl⟩ : syracuseStep 1645429 = 154259) (by norm_num)
theorem B2923397 : Blo 864565 2923397 := bbase (se 4 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 2923397 = 548137) (by norm_num)
theorem B924653 : Blo 864565 924653 := bbase (se 3 (by rfl) ⟨173372, by rfl⟩ : syracuseStep 924653 = 346745) (by norm_num)
theorem B1645589 : Blo 864565 1645589 := bbase (se 6 (by rfl) ⟨38568, by rfl⟩ : syracuseStep 1645589 = 77137) (by norm_num)
theorem B1055797 : Blo 864565 1055797 := bbase (se 5 (by rfl) ⟨49490, by rfl⟩ : syracuseStep 1055797 = 98981) (by norm_num)
theorem B1645733 : Blo 864565 1645733 := bbase (se 4 (by rfl) ⟨154287, by rfl⟩ : syracuseStep 1645733 = 308575) (by norm_num)
theorem B4168901 : Blo 864565 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B924905 : Blo 864565 924905 := bbase (se 2 (by rfl) ⟨346839, by rfl⟩ : syracuseStep 924905 = 693679) (by norm_num)
theorem B2923829 : Blo 864565 2923829 := bbase (se 5 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 2923829 = 274109) (by norm_num)
theorem B1646021 : Blo 864565 1646021 := bbase (se 4 (by rfl) ⟨154314, by rfl⟩ : syracuseStep 1646021 = 308629) (by norm_num)
theorem B1318349 : Blo 864565 1318349 := bbase (se 3 (by rfl) ⟨247190, by rfl⟩ : syracuseStep 1318349 = 494381) (by norm_num)
theorem B1646173 : Blo 864565 1646173 := bbase (se 3 (by rfl) ⟨308657, by rfl⟩ : syracuseStep 1646173 = 617315) (by norm_num)
theorem B925349 : Blo 864565 925349 := bbase (se 4 (by rfl) ⟨86751, by rfl⟩ : syracuseStep 925349 = 173503) (by norm_num)
theorem B5545685 : Blo 864565 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B2924261 : Blo 864565 2924261 := bbase (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) (by norm_num)
theorem B1875725 : Blo 864565 1875725 := bbase (se 3 (by rfl) ⟨351698, by rfl⟩ : syracuseStep 1875725 = 703397) (by norm_num)
theorem B1646477 : Blo 864565 1646477 := bbase (se 3 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 1646477 = 617429) (by norm_num)
theorem B925597 : Blo 864565 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B3284981 : Blo 864565 3284981 := bbase (se 5 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 3284981 = 307967) (by norm_num)
theorem B2465797 : Blo 864565 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B2924693 : Blo 864565 2924693 := bbase (se 6 (by rfl) ⟨68547, by rfl⟩ : syracuseStep 2924693 = 137095) (by norm_num)
theorem B2465957 : Blo 864565 2465957 := bbase (se 4 (by rfl) ⟨231183, by rfl⟩ : syracuseStep 2465957 = 462367) (by norm_num)
theorem B3285269 : Blo 864565 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B926041 : Blo 864565 926041 := bbase (se 2 (by rfl) ⟨347265, by rfl⟩ : syracuseStep 926041 = 694531) (by norm_num)
theorem B2466197 : Blo 864565 2466197 := bbase (se 6 (by rfl) ⟨57801, by rfl⟩ : syracuseStep 2466197 = 115603) (by norm_num)
theorem B926101 : Blo 864565 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B3121669 : Blo 864565 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B2925125 : Blo 864565 2925125 := bbase (se 4 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 2925125 = 548461) (by norm_num)
theorem B2466389 : Blo 864565 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B1647229 : Blo 864565 1647229 := bbase (se 3 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 1647229 = 617711) (by norm_num)
theorem B2171525 : Blo 864565 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B11870869 : Blo 864565 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B926417 : Blo 864565 926417 := bbase (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) (by norm_num)
theorem B16622293 : Blo 864565 16622293 := bbase (se 7 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 16622293 = 389585) (by norm_num)
theorem B1647373 : Blo 864565 1647373 := bbase (se 3 (by rfl) ⟨308882, by rfl⟩ : syracuseStep 1647373 = 617765) (by norm_num)
theorem B1385237 : Blo 864565 1385237 := bbase (se 6 (by rfl) ⟨32466, by rfl⟩ : syracuseStep 1385237 = 64933) (by norm_num)
theorem B1647533 : Blo 864565 1647533 := bbase (se 3 (by rfl) ⟨308912, by rfl⟩ : syracuseStep 1647533 = 617825) (by norm_num)
theorem B1385461 : Blo 864565 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B2925557 : Blo 864565 2925557 := bbase (se 5 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 2925557 = 274271) (by norm_num)
theorem B1385525 : Blo 864565 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B1647677 : Blo 864565 1647677 := bbase (se 3 (by rfl) ⟨308939, by rfl⟩ : syracuseStep 1647677 = 617879) (by norm_num)
theorem B6661237 : Blo 864565 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B926861 : Blo 864565 926861 := bbase (se 3 (by rfl) ⟨173786, by rfl⟩ : syracuseStep 926861 = 347573) (by norm_num)
theorem B1385653 : Blo 864565 1385653 := bbase (se 5 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 1385653 = 129905) (by norm_num)
theorem B926921 : Blo 864565 926921 := bbase (se 2 (by rfl) ⟨347595, by rfl⟩ : syracuseStep 926921 = 695191) (by norm_num)
theorem B927049 : Blo 864565 927049 := bbase (se 2 (by rfl) ⟨347643, by rfl⟩ : syracuseStep 927049 = 695287) (by norm_num)
theorem B1647965 : Blo 864565 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B2925989 : Blo 864565 2925989 := bbase (se 4 (by rfl) ⟨274311, by rfl⟩ : syracuseStep 2925989 = 548623) (by norm_num)
theorem B3286453 : Blo 864565 3286453 := bbase (se 5 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 3286453 = 308105) (by norm_num)
theorem B1648117 : Blo 864565 1648117 := bbase (se 5 (by rfl) ⟨77255, by rfl⟩ : syracuseStep 1648117 = 154511) (by norm_num)
theorem B1975853 : Blo 864565 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B2467381 : Blo 864565 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B3286757 : Blo 864565 3286757 := bbase (se 4 (by rfl) ⟨308133, by rfl⟩ : syracuseStep 3286757 = 616267) (by norm_num)
theorem B927493 : Blo 864565 927493 := bbase (se 4 (by rfl) ⟨86952, by rfl⟩ : syracuseStep 927493 = 173905) (by norm_num)
theorem B1648421 : Blo 864565 1648421 := bbase (se 4 (by rfl) ⟨154539, by rfl⟩ : syracuseStep 1648421 = 309079) (by norm_num)
theorem B6235957 : Blo 864565 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B2926421 : Blo 864565 2926421 := bbase (se 9 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 2926421 = 17147) (by norm_num)
theorem B2435221 : Blo 864565 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B15804629 : Blo 864565 15804629 := bbase (se 7 (by rfl) ⟨185210, by rfl⟩ : syracuseStep 15804629 = 370421) (by norm_num)
theorem B2926853 : Blo 864565 2926853 := bbase (se 4 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 2926853 = 548785) (by norm_num)
theorem B4925717 : Blo 864565 4925717 := bbase (se 6 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 4925717 = 230893) (by norm_num)
theorem B1386877 : Blo 864565 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1878565 : Blo 864565 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B2107949 : Blo 864565 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B5548661 : Blo 864565 5548661 := bbase (se 5 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 5548661 = 520187) (by norm_num)
theorem B2468485 : Blo 864565 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B2927285 : Blo 864565 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B2960165 : Blo 864565 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1387549 : Blo 864565 1387549 := bbase (se 3 (by rfl) ⟨260165, by rfl⟩ : syracuseStep 1387549 = 520331) (by norm_num)
theorem B2927717 : Blo 864565 2927717 := bbase (se 4 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 2927717 = 548947) (by norm_num)
theorem B4172933 : Blo 864565 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B4173029 : Blo 864565 4173029 := bbase (se 4 (by rfl) ⟨391221, by rfl⟩ : syracuseStep 4173029 = 782443) (by norm_num)
theorem B1977605 : Blo 864565 1977605 := bbase (se 4 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 1977605 = 370801) (by norm_num)
theorem B1846709 : Blo 864565 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B2928149 : Blo 864565 2928149 := bbase (se 6 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 2928149 = 137257) (by norm_num)
theorem B1945277 : Blo 864565 1945277 := bbase (se 3 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 1945277 = 729479) (by norm_num)
theorem B1945349 : Blo 864565 1945349 := bbase (se 4 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 1945349 = 364753) (by norm_num)
theorem B3288869 : Blo 864565 3288869 := bbase (se 4 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 3288869 = 616663) (by norm_num)
theorem B1945421 : Blo 864565 1945421 := bbase (se 3 (by rfl) ⟨364766, by rfl⟩ : syracuseStep 1945421 = 729533) (by norm_num)
theorem B1945493 : Blo 864565 1945493 := bbase (se 6 (by rfl) ⟨45597, by rfl⟩ : syracuseStep 1945493 = 91195) (by norm_num)
theorem B2928581 : Blo 864565 2928581 := bbase (se 4 (by rfl) ⟨274554, by rfl⟩ : syracuseStep 2928581 = 549109) (by norm_num)
theorem B1945565 : Blo 864565 1945565 := bbase (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) (by norm_num)
theorem B1388549 : Blo 864565 1388549 := bbase (se 4 (by rfl) ⟨130176, by rfl⟩ : syracuseStep 1388549 = 260353) (by norm_num)
theorem B1945637 : Blo 864565 1945637 := bbase (se 4 (by rfl) ⟨182403, by rfl⟩ : syracuseStep 1945637 = 364807) (by norm_num)
theorem B3289157 : Blo 864565 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B2469989 : Blo 864565 2469989 := bbase (se 4 (by rfl) ⟨231561, by rfl⟩ : syracuseStep 2469989 = 463123) (by norm_num)
theorem B1945709 : Blo 864565 1945709 := bbase (se 3 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 1945709 = 729641) (by norm_num)
theorem B1847461 : Blo 864565 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B1945781 : Blo 864565 1945781 := bbase (se 5 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 1945781 = 182417) (by norm_num)
theorem B1945853 : Blo 864565 1945853 := bbase (se 3 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 1945853 = 729695) (by norm_num)
theorem B1847605 : Blo 864565 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B1945925 : Blo 864565 1945925 := bbase (se 4 (by rfl) ⟨182430, by rfl⟩ : syracuseStep 1945925 = 364861) (by norm_num)
theorem B2929013 : Blo 864565 2929013 := bbase (se 5 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 2929013 = 274595) (by norm_num)
theorem B1945997 : Blo 864565 1945997 := bbase (se 3 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 1945997 = 729749) (by norm_num)
theorem B1946069 : Blo 864565 1946069 := bbase (se 7 (by rfl) ⟨22805, by rfl⟩ : syracuseStep 1946069 = 45611) (by norm_num)
theorem B1946141 : Blo 864565 1946141 := bbase (se 3 (by rfl) ⟨364901, by rfl⟩ : syracuseStep 1946141 = 729803) (by norm_num)
theorem B1946213 : Blo 864565 1946213 := bbase (se 4 (by rfl) ⟨182457, by rfl⟩ : syracuseStep 1946213 = 364915) (by norm_num)
theorem B1094249 : Blo 864565 1094249 := bbase (se 2 (by rfl) ⟨410343, by rfl⟩ : syracuseStep 1094249 = 820687) (by norm_num)
theorem B1094305 : Blo 864565 1094305 := bbase (se 2 (by rfl) ⟨410364, by rfl⟩ : syracuseStep 1094305 = 820729) (by norm_num)
theorem B1946285 : Blo 864565 1946285 := bbase (se 3 (by rfl) ⟨364928, by rfl⟩ : syracuseStep 1946285 = 729857) (by norm_num)
theorem B1847981 : Blo 864565 1847981 := bbase (se 3 (by rfl) ⟨346496, by rfl⟩ : syracuseStep 1847981 = 692993) (by norm_num)
theorem B1946357 : Blo 864565 1946357 := bbase (se 5 (by rfl) ⟨91235, by rfl⟩ : syracuseStep 1946357 = 182471) (by norm_num)
theorem B1094401 : Blo 864565 1094401 := bbase (se 2 (by rfl) ⟨410400, by rfl⟩ : syracuseStep 1094401 = 820801) (by norm_num)
theorem B2929445 : Blo 864565 2929445 := bbase (se 4 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 2929445 = 549271) (by norm_num)
theorem B1946429 : Blo 864565 1946429 := bbase (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) (by norm_num)
theorem B1946501 : Blo 864565 1946501 := bbase (se 4 (by rfl) ⟨182484, by rfl⟩ : syracuseStep 1946501 = 364969) (by norm_num)
theorem B1094573 : Blo 864565 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B1946573 : Blo 864565 1946573 := bbase (se 3 (by rfl) ⟨364982, by rfl⟩ : syracuseStep 1946573 = 729965) (by norm_num)
theorem B1094629 : Blo 864565 1094629 := bbase (se 4 (by rfl) ⟨102621, by rfl⟩ : syracuseStep 1094629 = 205243) (by norm_num)
theorem B1946645 : Blo 864565 1946645 := bbase (se 6 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 1946645 = 91249) (by norm_num)
theorem B1848349 : Blo 864565 1848349 := bbase (se 3 (by rfl) ⟨346565, by rfl⟩ : syracuseStep 1848349 = 693131) (by norm_num)
theorem B1094725 : Blo 864565 1094725 := bbase (se 4 (by rfl) ⟨102630, by rfl⟩ : syracuseStep 1094725 = 205261) (by norm_num)
theorem B3847253 : Blo 864565 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B1946717 : Blo 864565 1946717 := bbase (se 3 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 1946717 = 730019) (by norm_num)
theorem B16888981 : Blo 864565 16888981 := bbase (se 6 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 16888981 = 791671) (by norm_num)
theorem B1946789 : Blo 864565 1946789 := bbase (se 4 (by rfl) ⟨182511, by rfl⟩ : syracuseStep 1946789 = 365023) (by norm_num)
theorem B2929877 : Blo 864565 2929877 := bbase (se 7 (by rfl) ⟨34334, by rfl⟩ : syracuseStep 2929877 = 68669) (by norm_num)
theorem B3290341 : Blo 864565 3290341 := bbase (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) (by norm_num)
theorem B1946861 : Blo 864565 1946861 := bbase (se 3 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 1946861 = 730073) (by norm_num)
theorem B1094897 : Blo 864565 1094897 := bbase (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) (by norm_num)
theorem B7386389 : Blo 864565 7386389 := bbase (se 6 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 7386389 = 346237) (by norm_num)
theorem B1094953 : Blo 864565 1094953 := bbase (se 2 (by rfl) ⟨410607, by rfl⟩ : syracuseStep 1094953 = 821215) (by norm_num)
theorem B1946933 : Blo 864565 1946933 := bbase (se 5 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 1946933 = 182525) (by norm_num)
theorem B1947005 : Blo 864565 1947005 := bbase (se 3 (by rfl) ⟨365063, by rfl⟩ : syracuseStep 1947005 = 730127) (by norm_num)
theorem B1095049 : Blo 864565 1095049 := bbase (se 2 (by rfl) ⟨410643, by rfl⟩ : syracuseStep 1095049 = 821287) (by norm_num)
theorem B6567317 : Blo 864565 6567317 := bbase (se 6 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 6567317 = 307843) (by norm_num)
theorem B1947077 : Blo 864565 1947077 := bbase (se 4 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 1947077 = 365077) (by norm_num)
theorem B1390061 : Blo 864565 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B1947149 : Blo 864565 1947149 := bbase (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) (by norm_num)
theorem B3290645 : Blo 864565 3290645 := bbase (se 6 (by rfl) ⟨77124, by rfl⟩ : syracuseStep 3290645 = 154249) (by norm_num)
theorem B1095221 : Blo 864565 1095221 := bbase (se 5 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 1095221 = 102677) (by norm_num)
theorem B1947221 : Blo 864565 1947221 := bbase (se 8 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 1947221 = 22819) (by norm_num)
theorem B8336981 : Blo 864565 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1095277 : Blo 864565 1095277 := bbase (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) (by norm_num)
theorem B2930309 : Blo 864565 2930309 := bbase (se 4 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 2930309 = 549433) (by norm_num)
theorem B2471573 : Blo 864565 2471573 := bbase (se 6 (by rfl) ⟨57927, by rfl⟩ : syracuseStep 2471573 = 115855) (by norm_num)
theorem B1947293 : Blo 864565 1947293 := bbase (se 3 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 1947293 = 730235) (by norm_num)
theorem B1095373 : Blo 864565 1095373 := bbase (se 3 (by rfl) ⟨205382, by rfl⟩ : syracuseStep 1095373 = 410765) (by norm_num)
theorem B1947365 : Blo 864565 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B2143997 : Blo 864565 2143997 := bbase (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) (by norm_num)
theorem B2635541 : Blo 864565 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B3127061 : Blo 864565 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1947437 : Blo 864565 1947437 := bbase (se 3 (by rfl) ⟨365144, by rfl⟩ : syracuseStep 1947437 = 730289) (by norm_num)
theorem B1947509 : Blo 864565 1947509 := bbase (se 5 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 1947509 = 182579) (by norm_num)
theorem B1095545 : Blo 864565 1095545 := bbase (se 2 (by rfl) ⟨410829, by rfl⟩ : syracuseStep 1095545 = 821659) (by norm_num)
theorem B11384725 : Blo 864565 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B3127205 : Blo 864565 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B1095601 : Blo 864565 1095601 := bbase (se 2 (by rfl) ⟨410850, by rfl⟩ : syracuseStep 1095601 = 821701) (by norm_num)
theorem B1390517 : Blo 864565 1390517 := bbase (se 5 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 1390517 = 130361) (by norm_num)
theorem B1947581 : Blo 864565 1947581 := bbase (se 3 (by rfl) ⟨365171, by rfl⟩ : syracuseStep 1947581 = 730343) (by norm_num)
theorem B1947653 : Blo 864565 1947653 := bbase (se 4 (by rfl) ⟨182592, by rfl⟩ : syracuseStep 1947653 = 365185) (by norm_num)
theorem B1095697 : Blo 864565 1095697 := bbase (se 2 (by rfl) ⟨410886, by rfl⟩ : syracuseStep 1095697 = 821773) (by norm_num)
theorem B2930741 : Blo 864565 2930741 := bbase (se 5 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 2930741 = 274757) (by norm_num)
theorem B1947725 : Blo 864565 1947725 := bbase (se 3 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 1947725 = 730397) (by norm_num)
theorem B1947797 : Blo 864565 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B1095869 : Blo 864565 1095869 := bbase (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) (by norm_num)
theorem B2078941 : Blo 864565 2078941 := bbase (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) (by norm_num)
theorem B1947869 : Blo 864565 1947869 := bbase (se 3 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 1947869 = 730451) (by norm_num)
theorem B1095925 : Blo 864565 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B1947941 : Blo 864565 1947941 := bbase (se 4 (by rfl) ⟨182619, by rfl⟩ : syracuseStep 1947941 = 365239) (by norm_num)
theorem B2472245 : Blo 864565 2472245 := bbase (se 5 (by rfl) ⟨115886, by rfl⟩ : syracuseStep 2472245 = 231773) (by norm_num)
theorem B1096021 : Blo 864565 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B1948013 : Blo 864565 1948013 := bbase (se 3 (by rfl) ⟨365252, by rfl⟩ : syracuseStep 1948013 = 730505) (by norm_num)
theorem B1948085 : Blo 864565 1948085 := bbase (se 5 (by rfl) ⟨91316, by rfl⟩ : syracuseStep 1948085 = 182633) (by norm_num)
theorem B2931173 : Blo 864565 2931173 := bbase (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) (by norm_num)
theorem B1948157 : Blo 864565 1948157 := bbase (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) (by norm_num)
theorem B1849853 : Blo 864565 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B1096193 : Blo 864565 1096193 := bbase (se 2 (by rfl) ⟨411072, by rfl⟩ : syracuseStep 1096193 = 822145) (by norm_num)
theorem B1096249 : Blo 864565 1096249 := bbase (se 2 (by rfl) ⟨411093, by rfl⟩ : syracuseStep 1096249 = 822187) (by norm_num)
theorem B1948229 : Blo 864565 1948229 := bbase (se 4 (by rfl) ⟨182646, by rfl⟩ : syracuseStep 1948229 = 365293) (by norm_num)
theorem B2964053 : Blo 864565 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B2374229 : Blo 864565 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B1784413 : Blo 864565 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B1948301 : Blo 864565 1948301 := bbase (se 3 (by rfl) ⟨365306, by rfl⟩ : syracuseStep 1948301 = 730613) (by norm_num)
theorem B1849997 : Blo 864565 1849997 := bbase (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) (by norm_num)
theorem B3521173 : Blo 864565 3521173 := bbase (se 6 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 3521173 = 165055) (by norm_num)
theorem B1096345 : Blo 864565 1096345 := bbase (se 2 (by rfl) ⟨411129, by rfl⟩ : syracuseStep 1096345 = 822259) (by norm_num)
theorem B1948373 : Blo 864565 1948373 := bbase (se 7 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 1948373 = 45665) (by norm_num)
theorem B2472677 : Blo 864565 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B1948445 : Blo 864565 1948445 := bbase (se 3 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 1948445 = 730667) (by norm_num)
theorem B2079557 : Blo 864565 2079557 := bbase (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) (by norm_num)
theorem B1096517 : Blo 864565 1096517 := bbase (se 4 (by rfl) ⟨102798, by rfl⟩ : syracuseStep 1096517 = 205597) (by norm_num)
theorem B1948517 : Blo 864565 1948517 := bbase (se 4 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 1948517 = 365347) (by norm_num)
theorem B2112365 : Blo 864565 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B1096573 : Blo 864565 1096573 := bbase (se 3 (by rfl) ⟨205607, by rfl⟩ : syracuseStep 1096573 = 411215) (by norm_num)
theorem B1948589 : Blo 864565 1948589 := bbase (se 3 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 1948589 = 730721) (by norm_num)
theorem B1096669 : Blo 864565 1096669 := bbase (se 3 (by rfl) ⟨205625, by rfl⟩ : syracuseStep 1096669 = 411251) (by norm_num)
theorem B1948661 : Blo 864565 1948661 := bbase (se 5 (by rfl) ⟨91343, by rfl⟩ : syracuseStep 1948661 = 182687) (by norm_num)
theorem B1850357 : Blo 864565 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B2079749 : Blo 864565 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B1948733 : Blo 864565 1948733 := bbase (se 3 (by rfl) ⟨365387, by rfl⟩ : syracuseStep 1948733 = 730775) (by norm_num)
theorem B1948805 : Blo 864565 1948805 := bbase (se 4 (by rfl) ⟨182700, by rfl⟩ : syracuseStep 1948805 = 365401) (by norm_num)
theorem B1096841 : Blo 864565 1096841 := bbase (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) (by norm_num)
theorem B1096897 : Blo 864565 1096897 := bbase (se 2 (by rfl) ⟨411336, by rfl⟩ : syracuseStep 1096897 = 822673) (by norm_num)
theorem B1948877 : Blo 864565 1948877 := bbase (se 3 (by rfl) ⟨365414, by rfl⟩ : syracuseStep 1948877 = 730829) (by norm_num)
theorem B1948949 : Blo 864565 1948949 := bbase (se 6 (by rfl) ⟨45678, by rfl⟩ : syracuseStep 1948949 = 91357) (by norm_num)
theorem B1096993 : Blo 864565 1096993 := bbase (se 2 (by rfl) ⟨411372, by rfl⟩ : syracuseStep 1096993 = 822745) (by norm_num)
theorem B1949021 : Blo 864565 1949021 := bbase (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) (by norm_num)
theorem B1949093 : Blo 864565 1949093 := bbase (se 4 (by rfl) ⟨182727, by rfl⟩ : syracuseStep 1949093 = 365455) (by norm_num)
theorem B1097165 : Blo 864565 1097165 := bbase (se 3 (by rfl) ⟨205718, by rfl⟩ : syracuseStep 1097165 = 411437) (by norm_num)
theorem B1949165 : Blo 864565 1949165 := bbase (se 3 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 1949165 = 730937) (by norm_num)
theorem B1097221 : Blo 864565 1097221 := bbase (se 4 (by rfl) ⟨102864, by rfl⟩ : syracuseStep 1097221 = 205729) (by norm_num)
theorem B1949237 : Blo 864565 1949237 := bbase (se 5 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 1949237 = 182741) (by norm_num)
theorem B2080325 : Blo 864565 2080325 := bbase (se 4 (by rfl) ⟨195030, by rfl⟩ : syracuseStep 2080325 = 390061) (by norm_num)
theorem B3292757 : Blo 864565 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B1097317 : Blo 864565 1097317 := bbase (se 4 (by rfl) ⟨102873, by rfl⟩ : syracuseStep 1097317 = 205747) (by norm_num)
theorem B1949309 : Blo 864565 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B1523333 : Blo 864565 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B1949381 : Blo 864565 1949381 := bbase (se 4 (by rfl) ⟨182754, by rfl⟩ : syracuseStep 1949381 = 365509) (by norm_num)
theorem B1949453 : Blo 864565 1949453 := bbase (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) (by norm_num)
theorem B1097489 : Blo 864565 1097489 := bbase (se 2 (by rfl) ⟨411558, by rfl⟩ : syracuseStep 1097489 = 823117) (by norm_num)
theorem B1425197 : Blo 864565 1425197 := bbase (se 3 (by rfl) ⟨267224, by rfl⟩ : syracuseStep 1425197 = 534449) (by norm_num)
theorem B1097545 : Blo 864565 1097545 := bbase (se 2 (by rfl) ⟨411579, by rfl⟩ : syracuseStep 1097545 = 823159) (by norm_num)
theorem B1949525 : Blo 864565 1949525 := bbase (se 9 (by rfl) ⟨5711, by rfl⟩ : syracuseStep 1949525 = 11423) (by norm_num)
theorem B1851245 : Blo 864565 1851245 := bbase (se 3 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 1851245 = 694217) (by norm_num)
theorem B3293045 : Blo 864565 3293045 := bbase (se 5 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 3293045 = 308723) (by norm_num)
theorem B1949597 : Blo 864565 1949597 := bbase (se 3 (by rfl) ⟨365549, by rfl⟩ : syracuseStep 1949597 = 731099) (by norm_num)
theorem B1097641 : Blo 864565 1097641 := bbase (se 2 (by rfl) ⟨411615, by rfl⟩ : syracuseStep 1097641 = 823231) (by norm_num)
theorem B2080709 : Blo 864565 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B1949669 : Blo 864565 1949669 := bbase (se 4 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 1949669 = 365563) (by norm_num)
theorem B1753069 : Blo 864565 1753069 := bbase (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) (by norm_num)
theorem B1949741 : Blo 864565 1949741 := bbase (se 3 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 1949741 = 731153) (by norm_num)
theorem B1097813 : Blo 864565 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1851493 : Blo 864565 1851493 := bbase (se 4 (by rfl) ⟨173577, by rfl⟩ : syracuseStep 1851493 = 347155) (by norm_num)
theorem B1949813 : Blo 864565 1949813 := bbase (se 5 (by rfl) ⟨91397, by rfl⟩ : syracuseStep 1949813 = 182795) (by norm_num)
theorem B1097869 : Blo 864565 1097869 := bbase (se 3 (by rfl) ⟨205850, by rfl⟩ : syracuseStep 1097869 = 411701) (by norm_num)
theorem B3162277 : Blo 864565 3162277 := bbase (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) (by norm_num)
theorem B1949885 : Blo 864565 1949885 := bbase (se 3 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 1949885 = 731207) (by norm_num)
theorem B1097965 : Blo 864565 1097965 := bbase (se 3 (by rfl) ⟨205868, by rfl⟩ : syracuseStep 1097965 = 411737) (by norm_num)
theorem B1949957 : Blo 864565 1949957 := bbase (se 4 (by rfl) ⟨182808, by rfl⟩ : syracuseStep 1949957 = 365617) (by norm_num)
theorem B1950029 : Blo 864565 1950029 := bbase (se 3 (by rfl) ⟨365630, by rfl⟩ : syracuseStep 1950029 = 731261) (by norm_num)
theorem B1950101 : Blo 864565 1950101 := bbase (se 6 (by rfl) ⟨45705, by rfl⟩ : syracuseStep 1950101 = 91411) (by norm_num)
theorem B1098137 : Blo 864565 1098137 := bbase (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) (by norm_num)
theorem B2539957 : Blo 864565 2539957 := bbase (se 5 (by rfl) ⟨119060, by rfl⟩ : syracuseStep 2539957 = 238121) (by norm_num)
theorem B1098193 : Blo 864565 1098193 := bbase (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) (by norm_num)
theorem B1950173 : Blo 864565 1950173 := bbase (se 3 (by rfl) ⟨365657, by rfl⟩ : syracuseStep 1950173 = 731315) (by norm_num)
theorem B1950245 : Blo 864565 1950245 := bbase (se 4 (by rfl) ⟨182835, by rfl⟩ : syracuseStep 1950245 = 365671) (by norm_num)
theorem B1098289 : Blo 864565 1098289 := bbase (se 2 (by rfl) ⟨411858, by rfl⟩ : syracuseStep 1098289 = 823717) (by norm_num)
theorem B1851997 : Blo 864565 1851997 := bbase (se 3 (by rfl) ⟨347249, by rfl⟩ : syracuseStep 1851997 = 694499) (by norm_num)
theorem B1950317 : Blo 864565 1950317 := bbase (se 3 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 1950317 = 731369) (by norm_num)
theorem B9355925 : Blo 864565 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B1950389 : Blo 864565 1950389 := bbase (se 5 (by rfl) ⟨91424, by rfl⟩ : syracuseStep 1950389 = 182849) (by norm_num)
theorem B2966213 : Blo 864565 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1098461 : Blo 864565 1098461 := bbase (se 3 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 1098461 = 411923) (by norm_num)
theorem B1950461 : Blo 864565 1950461 := bbase (se 3 (by rfl) ⟨365711, by rfl⟩ : syracuseStep 1950461 = 731423) (by norm_num)
theorem B1458965 : Blo 864565 1458965 := bbase (se 6 (by rfl) ⟨34194, by rfl⟩ : syracuseStep 1458965 = 68389) (by norm_num)
theorem B1098517 : Blo 864565 1098517 := bbase (se 6 (by rfl) ⟨25746, by rfl⟩ : syracuseStep 1098517 = 51493) (by norm_num)
theorem B5260085 : Blo 864565 5260085 := bbase (se 5 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 5260085 = 493133) (by norm_num)
theorem B1950533 : Blo 864565 1950533 := bbase (se 4 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 1950533 = 365725) (by norm_num)
theorem B1098613 : Blo 864565 1098613 := bbase (se 5 (by rfl) ⟨51497, by rfl⟩ : syracuseStep 1098613 = 102995) (by norm_num)
theorem B1950605 : Blo 864565 1950605 := bbase (se 3 (by rfl) ⟨365738, by rfl⟩ : syracuseStep 1950605 = 731477) (by norm_num)
theorem B1459093 : Blo 864565 1459093 := bbase (se 6 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 1459093 = 68395) (by norm_num)
theorem B1000369 : Blo 864565 1000369 := bbase (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) (by norm_num)
theorem B1950677 : Blo 864565 1950677 := bbase (se 7 (by rfl) ⟨22859, by rfl⟩ : syracuseStep 1950677 = 45719) (by norm_num)
theorem B1459181 : Blo 864565 1459181 := bbase (se 3 (by rfl) ⟨273596, by rfl⟩ : syracuseStep 1459181 = 547193) (by norm_num)
theorem B3294229 : Blo 864565 3294229 := bbase (se 6 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 3294229 = 154417) (by norm_num)
theorem B1950749 : Blo 864565 1950749 := bbase (se 3 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 1950749 = 731531) (by norm_num)
theorem B1098785 : Blo 864565 1098785 := bbase (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) (by norm_num)
theorem B5260373 : Blo 864565 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B9389141 : Blo 864565 9389141 := bbase (se 8 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 9389141 = 110029) (by norm_num)
theorem B1098841 : Blo 864565 1098841 := bbase (se 2 (by rfl) ⟨412065, by rfl⟩ : syracuseStep 1098841 = 824131) (by norm_num)
theorem B1950821 : Blo 864565 1950821 := bbase (se 4 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 1950821 = 365779) (by norm_num)
theorem B1459309 : Blo 864565 1459309 := bbase (se 3 (by rfl) ⟨273620, by rfl⟩ : syracuseStep 1459309 = 547241) (by norm_num)
theorem B1950893 : Blo 864565 1950893 := bbase (se 3 (by rfl) ⟨365792, by rfl⟩ : syracuseStep 1950893 = 731585) (by norm_num)
theorem B1098937 : Blo 864565 1098937 := bbase (se 2 (by rfl) ⟨412101, by rfl⟩ : syracuseStep 1098937 = 824203) (by norm_num)
theorem B1459397 : Blo 864565 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B1950965 : Blo 864565 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B1951037 : Blo 864565 1951037 := bbase (se 3 (by rfl) ⟨365819, by rfl⟩ : syracuseStep 1951037 = 731639) (by norm_num)
theorem B1459525 : Blo 864565 1459525 := bbase (se 4 (by rfl) ⟨136830, by rfl⟩ : syracuseStep 1459525 = 273661) (by norm_num)
theorem B3294533 : Blo 864565 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B1099109 : Blo 864565 1099109 := bbase (se 4 (by rfl) ⟨103041, by rfl⟩ : syracuseStep 1099109 = 206083) (by norm_num)
theorem B4441477 : Blo 864565 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B1951109 : Blo 864565 1951109 := bbase (se 4 (by rfl) ⟨182916, by rfl⟩ : syracuseStep 1951109 = 365833) (by norm_num)
theorem B1459613 : Blo 864565 1459613 := bbase (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) (by norm_num)
theorem B1099165 : Blo 864565 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B1951181 : Blo 864565 1951181 := bbase (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) (by norm_num)
theorem B1852885 : Blo 864565 1852885 := bbase (se 7 (by rfl) ⟨21713, by rfl⟩ : syracuseStep 1852885 = 43427) (by norm_num)
theorem B1099261 : Blo 864565 1099261 := bbase (se 3 (by rfl) ⟨206111, by rfl⟩ : syracuseStep 1099261 = 412223) (by norm_num)
theorem B1951253 : Blo 864565 1951253 := bbase (se 6 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 1951253 = 91465) (by norm_num)
theorem B1459741 : Blo 864565 1459741 := bbase (se 3 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 1459741 = 547403) (by norm_num)
theorem B1951325 : Blo 864565 1951325 := bbase (se 3 (by rfl) ⟨365873, by rfl⟩ : syracuseStep 1951325 = 731747) (by norm_num)
theorem B1459829 : Blo 864565 1459829 := bbase (se 5 (by rfl) ⟨68429, by rfl⟩ : syracuseStep 1459829 = 136859) (by norm_num)
theorem B2082469 : Blo 864565 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B1951397 : Blo 864565 1951397 := bbase (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) (by norm_num)
theorem B1951469 : Blo 864565 1951469 := bbase (se 3 (by rfl) ⟨365900, by rfl⟩ : syracuseStep 1951469 = 731801) (by norm_num)
theorem B1459957 : Blo 864565 1459957 := bbase (se 5 (by rfl) ⟨68435, by rfl⟩ : syracuseStep 1459957 = 136871) (by norm_num)
theorem B1951541 : Blo 864565 1951541 := bbase (se 5 (by rfl) ⟨91478, by rfl⟩ : syracuseStep 1951541 = 182957) (by norm_num)
theorem B1460045 : Blo 864565 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B2410357 : Blo 864565 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B1951613 : Blo 864565 1951613 := bbase (se 3 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 1951613 = 731855) (by norm_num)
theorem B1951685 : Blo 864565 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B1853381 : Blo 864565 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B1460173 : Blo 864565 1460173 := bbase (se 3 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 1460173 = 547565) (by norm_num)
theorem B9848789 : Blo 864565 9848789 := bbase (se 7 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 9848789 = 230831) (by norm_num)
theorem B1951757 : Blo 864565 1951757 := bbase (se 3 (by rfl) ⟨365954, by rfl⟩ : syracuseStep 1951757 = 731909) (by norm_num)
theorem B1460261 : Blo 864565 1460261 := bbase (se 4 (by rfl) ⟨136899, by rfl⟩ : syracuseStep 1460261 = 273799) (by norm_num)
theorem B1951829 : Blo 864565 1951829 := bbase (se 8 (by rfl) ⟨11436, by rfl⟩ : syracuseStep 1951829 = 22873) (by norm_num)
theorem B4933781 : Blo 864565 4933781 := bbase (se 6 (by rfl) ⟨115635, by rfl⟩ : syracuseStep 4933781 = 231271) (by norm_num)
theorem B1951901 : Blo 864565 1951901 := bbase (se 3 (by rfl) ⟨365981, by rfl⟩ : syracuseStep 1951901 = 731963) (by norm_num)
theorem B1460389 : Blo 864565 1460389 := bbase (se 4 (by rfl) ⟨136911, by rfl⟩ : syracuseStep 1460389 = 273823) (by norm_num)
theorem B2967749 : Blo 864565 2967749 := bbase (se 4 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 2967749 = 556453) (by norm_num)
theorem B1951973 : Blo 864565 1951973 := bbase (se 4 (by rfl) ⟨182997, by rfl⟩ : syracuseStep 1951973 = 365995) (by norm_num)
theorem B1460477 : Blo 864565 1460477 := bbase (se 3 (by rfl) ⟨273839, by rfl⟩ : syracuseStep 1460477 = 547679) (by norm_num)
theorem B1952045 : Blo 864565 1952045 := bbase (se 3 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 1952045 = 732017) (by norm_num)
theorem B1558853 : Blo 864565 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1231213 : Blo 864565 1231213 := bbase (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) (by norm_num)
theorem B1952117 : Blo 864565 1952117 := bbase (se 5 (by rfl) ⟨91505, by rfl⟩ : syracuseStep 1952117 = 183011) (by norm_num)
theorem B1460605 : Blo 864565 1460605 := bbase (se 3 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 1460605 = 547727) (by norm_num)
theorem B1952189 : Blo 864565 1952189 := bbase (se 3 (by rfl) ⟨366035, by rfl⟩ : syracuseStep 1952189 = 732071) (by norm_num)
theorem B1460693 : Blo 864565 1460693 := bbase (se 7 (by rfl) ⟨17117, by rfl⟩ : syracuseStep 1460693 = 34235) (by norm_num)
theorem B1296869 : Blo 864565 1296869 := bbase (se 4 (by rfl) ⟨121581, by rfl⟩ : syracuseStep 1296869 = 243163) (by norm_num)
theorem B4377077 : Blo 864565 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B1296893 : Blo 864565 1296893 := bbase (se 3 (by rfl) ⟨243167, by rfl⟩ : syracuseStep 1296893 = 486335) (by norm_num)
theorem B1952261 : Blo 864565 1952261 := bbase (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) (by norm_num)
theorem B1296917 : Blo 864565 1296917 := bbase (se 6 (by rfl) ⟨30396, by rfl⟩ : syracuseStep 1296917 = 60793) (by norm_num)
theorem B5556757 : Blo 864565 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B9390613 : Blo 864565 9390613 := bbase (se 6 (by rfl) ⟨220092, by rfl⟩ : syracuseStep 9390613 = 440185) (by norm_num)
theorem B1296941 : Blo 864565 1296941 := bbase (se 3 (by rfl) ⟨243176, by rfl⟩ : syracuseStep 1296941 = 486353) (by norm_num)
theorem B1296965 : Blo 864565 1296965 := bbase (se 4 (by rfl) ⟨121590, by rfl⟩ : syracuseStep 1296965 = 243181) (by norm_num)
theorem B1952333 : Blo 864565 1952333 := bbase (se 3 (by rfl) ⟨366062, by rfl⟩ : syracuseStep 1952333 = 732125) (by norm_num)
theorem B1460821 : Blo 864565 1460821 := bbase (se 8 (by rfl) ⟨8559, by rfl⟩ : syracuseStep 1460821 = 17119) (by norm_num)
theorem B1296989 : Blo 864565 1296989 := bbase (se 3 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 1296989 = 486371) (by norm_num)
theorem B1297013 : Blo 864565 1297013 := bbase (se 5 (by rfl) ⟨60797, by rfl⟩ : syracuseStep 1297013 = 121595) (by norm_num)
theorem B1297037 : Blo 864565 1297037 := bbase (se 3 (by rfl) ⟨243194, by rfl⟩ : syracuseStep 1297037 = 486389) (by norm_num)
theorem B2083477 : Blo 864565 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B1952405 : Blo 864565 1952405 := bbase (se 6 (by rfl) ⟨45759, by rfl⟩ : syracuseStep 1952405 = 91519) (by norm_num)
theorem B1297061 : Blo 864565 1297061 := bbase (se 4 (by rfl) ⟨121599, by rfl⟩ : syracuseStep 1297061 = 243199) (by norm_num)
theorem B1460909 : Blo 864565 1460909 := bbase (se 3 (by rfl) ⟨273920, by rfl⟩ : syracuseStep 1460909 = 547841) (by norm_num)
theorem B1297085 : Blo 864565 1297085 := bbase (se 3 (by rfl) ⟨243203, by rfl⟩ : syracuseStep 1297085 = 486407) (by norm_num)
theorem B1297109 : Blo 864565 1297109 := bbase (se 7 (by rfl) ⟨15200, by rfl⟩ : syracuseStep 1297109 = 30401) (by norm_num)
theorem B1952477 : Blo 864565 1952477 := bbase (se 3 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 1952477 = 732179) (by norm_num)
theorem B1297133 : Blo 864565 1297133 := bbase (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) (by norm_num)
theorem B2083573 : Blo 864565 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B1297157 : Blo 864565 1297157 := bbase (se 4 (by rfl) ⟨121608, by rfl⟩ : syracuseStep 1297157 = 243217) (by norm_num)
theorem B1297181 : Blo 864565 1297181 := bbase (se 3 (by rfl) ⟨243221, by rfl⟩ : syracuseStep 1297181 = 486443) (by norm_num)
theorem B1952549 : Blo 864565 1952549 := bbase (se 4 (by rfl) ⟨183051, by rfl⟩ : syracuseStep 1952549 = 366103) (by norm_num)
theorem B1461037 : Blo 864565 1461037 := bbase (se 3 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 1461037 = 547889) (by norm_num)
theorem B1297205 : Blo 864565 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B1854269 : Blo 864565 1854269 := bbase (se 3 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 1854269 = 695351) (by norm_num)
theorem B1297229 : Blo 864565 1297229 := bbase (se 3 (by rfl) ⟨243230, by rfl⟩ : syracuseStep 1297229 = 486461) (by norm_num)
theorem B1297253 : Blo 864565 1297253 := bbase (se 4 (by rfl) ⟨121617, by rfl⟩ : syracuseStep 1297253 = 243235) (by norm_num)
theorem B1952621 : Blo 864565 1952621 := bbase (se 3 (by rfl) ⟨366116, by rfl⟩ : syracuseStep 1952621 = 732233) (by norm_num)
theorem B1297277 : Blo 864565 1297277 := bbase (se 3 (by rfl) ⟨243239, by rfl⟩ : syracuseStep 1297277 = 486479) (by norm_num)
theorem B1461125 : Blo 864565 1461125 := bbase (se 4 (by rfl) ⟨136980, by rfl⟩ : syracuseStep 1461125 = 273961) (by norm_num)
theorem B1297301 : Blo 864565 1297301 := bbase (se 6 (by rfl) ⟨30405, by rfl⟩ : syracuseStep 1297301 = 60811) (by norm_num)
theorem B1297325 : Blo 864565 1297325 := bbase (se 3 (by rfl) ⟨243248, by rfl⟩ : syracuseStep 1297325 = 486497) (by norm_num)
theorem B5622709 : Blo 864565 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B1952693 : Blo 864565 1952693 := bbase (se 5 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 1952693 = 183065) (by norm_num)
theorem B1854389 : Blo 864565 1854389 := bbase (se 5 (by rfl) ⟨86924, by rfl⟩ : syracuseStep 1854389 = 173849) (by norm_num)
theorem B1231805 : Blo 864565 1231805 := bbase (se 3 (by rfl) ⟨230963, by rfl⟩ : syracuseStep 1231805 = 461927) (by norm_num)
theorem B1297349 : Blo 864565 1297349 := bbase (se 4 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 1297349 = 243253) (by norm_num)
theorem B1297373 : Blo 864565 1297373 := bbase (se 3 (by rfl) ⟨243257, by rfl⟩ : syracuseStep 1297373 = 486515) (by norm_num)
theorem B1297397 : Blo 864565 1297397 := bbase (se 5 (by rfl) ⟨60815, by rfl⟩ : syracuseStep 1297397 = 121631) (by norm_num)
theorem B1952765 : Blo 864565 1952765 := bbase (se 3 (by rfl) ⟨366143, by rfl⟩ : syracuseStep 1952765 = 732287) (by norm_num)
theorem B1461253 : Blo 864565 1461253 := bbase (se 4 (by rfl) ⟨136992, by rfl⟩ : syracuseStep 1461253 = 273985) (by norm_num)
theorem B1297421 : Blo 864565 1297421 := bbase (se 3 (by rfl) ⟨243266, by rfl⟩ : syracuseStep 1297421 = 486533) (by norm_num)
theorem B1231885 : Blo 864565 1231885 := bbase (se 3 (by rfl) ⟨230978, by rfl⟩ : syracuseStep 1231885 = 461957) (by norm_num)
theorem B2640917 : Blo 864565 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B1297445 : Blo 864565 1297445 := bbase (se 4 (by rfl) ⟨121635, by rfl⟩ : syracuseStep 1297445 = 243271) (by norm_num)
theorem B1297469 : Blo 864565 1297469 := bbase (se 3 (by rfl) ⟨243275, by rfl⟩ : syracuseStep 1297469 = 486551) (by norm_num)
theorem B1952837 : Blo 864565 1952837 := bbase (se 4 (by rfl) ⟨183078, by rfl⟩ : syracuseStep 1952837 = 366157) (by norm_num)
theorem B1297493 : Blo 864565 1297493 := bbase (se 8 (by rfl) ⟨7602, by rfl⟩ : syracuseStep 1297493 = 15205) (by norm_num)
theorem B1461341 : Blo 864565 1461341 := bbase (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) (by norm_num)
theorem B1297517 : Blo 864565 1297517 := bbase (se 3 (by rfl) ⟨243284, by rfl⟩ : syracuseStep 1297517 = 486569) (by norm_num)
theorem B1297541 : Blo 864565 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B1232005 : Blo 864565 1232005 := bbase (se 4 (by rfl) ⟨115500, by rfl⟩ : syracuseStep 1232005 = 231001) (by norm_num)
theorem B1952909 : Blo 864565 1952909 := bbase (se 3 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 1952909 = 732341) (by norm_num)
theorem B1297565 : Blo 864565 1297565 := bbase (se 3 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 1297565 = 486587) (by norm_num)
theorem B1297589 : Blo 864565 1297589 := bbase (se 5 (by rfl) ⟨60824, by rfl⟩ : syracuseStep 1297589 = 121649) (by norm_num)
theorem B1297613 : Blo 864565 1297613 := bbase (se 3 (by rfl) ⟨243302, by rfl⟩ : syracuseStep 1297613 = 486605) (by norm_num)
theorem B1952981 : Blo 864565 1952981 := bbase (se 7 (by rfl) ⟨22886, by rfl⟩ : syracuseStep 1952981 = 45773) (by norm_num)
theorem B1461469 : Blo 864565 1461469 := bbase (se 3 (by rfl) ⟨274025, by rfl⟩ : syracuseStep 1461469 = 548051) (by norm_num)
theorem B1297637 : Blo 864565 1297637 := bbase (se 4 (by rfl) ⟨121653, by rfl⟩ : syracuseStep 1297637 = 243307) (by norm_num)
theorem B1232101 : Blo 864565 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B1297661 : Blo 864565 1297661 := bbase (se 3 (by rfl) ⟨243311, by rfl⟩ : syracuseStep 1297661 = 486623) (by norm_num)
theorem B2084093 : Blo 864565 2084093 := bbase (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) (by norm_num)
theorem B1297685 : Blo 864565 1297685 := bbase (se 6 (by rfl) ⟨30414, by rfl⟩ : syracuseStep 1297685 = 60829) (by norm_num)
theorem B1953053 : Blo 864565 1953053 := bbase (se 3 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 1953053 = 732395) (by norm_num)
theorem B1297709 : Blo 864565 1297709 := bbase (se 3 (by rfl) ⟨243320, by rfl⟩ : syracuseStep 1297709 = 486641) (by norm_num)
theorem B1461557 : Blo 864565 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B4934965 : Blo 864565 4934965 := bbase (se 5 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 4934965 = 462653) (by norm_num)
theorem B1297733 : Blo 864565 1297733 := bbase (se 4 (by rfl) ⟨121662, by rfl⟩ : syracuseStep 1297733 = 243325) (by norm_num)
theorem B1297757 : Blo 864565 1297757 := bbase (se 3 (by rfl) ⟨243329, by rfl⟩ : syracuseStep 1297757 = 486659) (by norm_num)
theorem B1953125 : Blo 864565 1953125 := bbase (se 4 (by rfl) ⟨183105, by rfl⟩ : syracuseStep 1953125 = 366211) (by norm_num)
theorem B1297781 : Blo 864565 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B3296645 : Blo 864565 3296645 := bbase (se 4 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 3296645 = 618121) (by norm_num)
theorem B1297805 : Blo 864565 1297805 := bbase (se 3 (by rfl) ⟨243338, by rfl⟩ : syracuseStep 1297805 = 486677) (by norm_num)
theorem B1297829 : Blo 864565 1297829 := bbase (se 4 (by rfl) ⟨121671, by rfl⟩ : syracuseStep 1297829 = 243343) (by norm_num)
theorem B1953197 : Blo 864565 1953197 := bbase (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) (by norm_num)
theorem B1461685 : Blo 864565 1461685 := bbase (se 5 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 1461685 = 137033) (by norm_num)
theorem B1297853 : Blo 864565 1297853 := bbase (se 3 (by rfl) ⟨243347, by rfl⟩ : syracuseStep 1297853 = 486695) (by norm_num)
theorem B1297877 : Blo 864565 1297877 := bbase (se 7 (by rfl) ⟨15209, by rfl⟩ : syracuseStep 1297877 = 30419) (by norm_num)
theorem B1297901 : Blo 864565 1297901 := bbase (se 3 (by rfl) ⟨243356, by rfl⟩ : syracuseStep 1297901 = 486713) (by norm_num)
theorem B1953269 : Blo 864565 1953269 := bbase (se 5 (by rfl) ⟨91559, by rfl⟩ : syracuseStep 1953269 = 183119) (by norm_num)
theorem B1297925 : Blo 864565 1297925 := bbase (se 4 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 1297925 = 243361) (by norm_num)
theorem B1461773 : Blo 864565 1461773 := bbase (se 3 (by rfl) ⟨274082, by rfl⟩ : syracuseStep 1461773 = 548165) (by norm_num)
theorem B1297949 : Blo 864565 1297949 := bbase (se 3 (by rfl) ⟨243365, by rfl⟩ : syracuseStep 1297949 = 486731) (by norm_num)
theorem B1855021 : Blo 864565 1855021 := bbase (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) (by norm_num)
theorem B1297973 : Blo 864565 1297973 := bbase (se 5 (by rfl) ⟨60842, by rfl⟩ : syracuseStep 1297973 = 121685) (by norm_num)
theorem B1953341 : Blo 864565 1953341 := bbase (se 3 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 1953341 = 732503) (by norm_num)
theorem B1297997 : Blo 864565 1297997 := bbase (se 3 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 1297997 = 486749) (by norm_num)
theorem B1298021 : Blo 864565 1298021 := bbase (se 4 (by rfl) ⟨121689, by rfl⟩ : syracuseStep 1298021 = 243379) (by norm_num)
theorem B1298045 : Blo 864565 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B1953413 : Blo 864565 1953413 := bbase (se 4 (by rfl) ⟨183132, by rfl⟩ : syracuseStep 1953413 = 366265) (by norm_num)
theorem B1461901 : Blo 864565 1461901 := bbase (se 3 (by rfl) ⟨274106, by rfl⟩ : syracuseStep 1461901 = 548213) (by norm_num)
theorem B1298069 : Blo 864565 1298069 := bbase (se 6 (by rfl) ⟨30423, by rfl⟩ : syracuseStep 1298069 = 60847) (by norm_num)
theorem B1068701 : Blo 864565 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B3296933 : Blo 864565 3296933 := bbase (se 4 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 3296933 = 618175) (by norm_num)
theorem B1298093 : Blo 864565 1298093 := bbase (se 3 (by rfl) ⟨243392, by rfl⟩ : syracuseStep 1298093 = 486785) (by norm_num)
theorem B1298117 : Blo 864565 1298117 := bbase (se 4 (by rfl) ⟨121698, by rfl⟩ : syracuseStep 1298117 = 243397) (by norm_num)
theorem B1953485 : Blo 864565 1953485 := bbase (se 3 (by rfl) ⟨366278, by rfl⟩ : syracuseStep 1953485 = 732557) (by norm_num)
theorem B1232597 : Blo 864565 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1298141 : Blo 864565 1298141 := bbase (se 3 (by rfl) ⟨243401, by rfl⟩ : syracuseStep 1298141 = 486803) (by norm_num)
theorem B1461989 : Blo 864565 1461989 := bbase (se 4 (by rfl) ⟨137061, by rfl⟩ : syracuseStep 1461989 = 274123) (by norm_num)
theorem B1298165 : Blo 864565 1298165 := bbase (se 5 (by rfl) ⟨60851, by rfl⟩ : syracuseStep 1298165 = 121703) (by norm_num)
theorem B4378373 : Blo 864565 4378373 := bbase (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) (by norm_num)
theorem B1298189 : Blo 864565 1298189 := bbase (se 3 (by rfl) ⟨243410, by rfl⟩ : syracuseStep 1298189 = 486821) (by norm_num)
theorem B2084621 : Blo 864565 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B1953557 : Blo 864565 1953557 := bbase (se 6 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 1953557 = 91573) (by norm_num)
theorem B1298213 : Blo 864565 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B1298237 : Blo 864565 1298237 := bbase (se 3 (by rfl) ⟨243419, by rfl⟩ : syracuseStep 1298237 = 486839) (by norm_num)
theorem B1298261 : Blo 864565 1298261 := bbase (se 9 (by rfl) ⟨3803, by rfl⟩ : syracuseStep 1298261 = 7607) (by norm_num)
theorem B1953629 : Blo 864565 1953629 := bbase (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) (by norm_num)
theorem B1462117 : Blo 864565 1462117 := bbase (se 4 (by rfl) ⟨137073, by rfl⟩ : syracuseStep 1462117 = 274147) (by norm_num)
theorem B2346853 : Blo 864565 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B1298285 : Blo 864565 1298285 := bbase (se 3 (by rfl) ⟨243428, by rfl⟩ : syracuseStep 1298285 = 486857) (by norm_num)
theorem B1298309 : Blo 864565 1298309 := bbase (se 4 (by rfl) ⟨121716, by rfl⟩ : syracuseStep 1298309 = 243433) (by norm_num)
theorem B1298333 : Blo 864565 1298333 := bbase (se 3 (by rfl) ⟨243437, by rfl⟩ : syracuseStep 1298333 = 486875) (by norm_num)
theorem B1953701 : Blo 864565 1953701 := bbase (se 4 (by rfl) ⟨183159, by rfl⟩ : syracuseStep 1953701 = 366319) (by norm_num)
theorem B1298357 : Blo 864565 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B1462205 : Blo 864565 1462205 := bbase (se 3 (by rfl) ⟨274163, by rfl⟩ : syracuseStep 1462205 = 548327) (by norm_num)
theorem B1298381 : Blo 864565 1298381 := bbase (se 3 (by rfl) ⟨243446, by rfl⟩ : syracuseStep 1298381 = 486893) (by norm_num)
theorem B1298405 : Blo 864565 1298405 := bbase (se 4 (by rfl) ⟨121725, by rfl⟩ : syracuseStep 1298405 = 243451) (by norm_num)
theorem B1953773 : Blo 864565 1953773 := bbase (se 3 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 1953773 = 732665) (by norm_num)
theorem B1298429 : Blo 864565 1298429 := bbase (se 3 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 1298429 = 486911) (by norm_num)
theorem B2084861 : Blo 864565 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B1298453 : Blo 864565 1298453 := bbase (se 6 (by rfl) ⟨30432, by rfl⟩ : syracuseStep 1298453 = 60865) (by norm_num)
theorem B17813525 : Blo 864565 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B1298477 : Blo 864565 1298477 := bbase (se 3 (by rfl) ⟨243464, by rfl⟩ : syracuseStep 1298477 = 486929) (by norm_num)
theorem B1953845 : Blo 864565 1953845 := bbase (se 5 (by rfl) ⟨91586, by rfl⟩ : syracuseStep 1953845 = 183173) (by norm_num)
theorem B1462333 : Blo 864565 1462333 := bbase (se 3 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 1462333 = 548375) (by norm_num)
theorem B1298501 : Blo 864565 1298501 := bbase (se 4 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 1298501 = 243469) (by norm_num)
theorem B3952709 : Blo 864565 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B1298525 : Blo 864565 1298525 := bbase (se 3 (by rfl) ⟨243473, by rfl⟩ : syracuseStep 1298525 = 486947) (by norm_num)
theorem B1298549 : Blo 864565 1298549 := bbase (se 5 (by rfl) ⟨60869, by rfl⟩ : syracuseStep 1298549 = 121739) (by norm_num)
theorem B1953917 : Blo 864565 1953917 := bbase (se 3 (by rfl) ⟨366359, by rfl⟩ : syracuseStep 1953917 = 732719) (by norm_num)
theorem B1298573 : Blo 864565 1298573 := bbase (se 3 (by rfl) ⟨243482, by rfl⟩ : syracuseStep 1298573 = 486965) (by norm_num)
theorem B1462421 : Blo 864565 1462421 := bbase (se 6 (by rfl) ⟨34275, by rfl⟩ : syracuseStep 1462421 = 68551) (by norm_num)
theorem B2347157 : Blo 864565 2347157 := bbase (se 6 (by rfl) ⟨55011, by rfl⟩ : syracuseStep 2347157 = 110023) (by norm_num)
theorem B1298597 : Blo 864565 1298597 := bbase (se 4 (by rfl) ⟨121743, by rfl⟩ : syracuseStep 1298597 = 243487) (by norm_num)
theorem B5263541 : Blo 864565 5263541 := bbase (se 5 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 5263541 = 493457) (by norm_num)
theorem B1298621 : Blo 864565 1298621 := bbase (se 3 (by rfl) ⟨243491, by rfl⟩ : syracuseStep 1298621 = 486983) (by norm_num)
theorem B1953989 : Blo 864565 1953989 := bbase (se 4 (by rfl) ⟨183186, by rfl⟩ : syracuseStep 1953989 = 366373) (by norm_num)
theorem B1298645 : Blo 864565 1298645 := bbase (se 7 (by rfl) ⟨15218, by rfl⟩ : syracuseStep 1298645 = 30437) (by norm_num)
theorem B1298669 : Blo 864565 1298669 := bbase (se 3 (by rfl) ⟨243500, by rfl⟩ : syracuseStep 1298669 = 487001) (by norm_num)
theorem B1233149 : Blo 864565 1233149 := bbase (se 3 (by rfl) ⟨231215, by rfl⟩ : syracuseStep 1233149 = 462431) (by norm_num)
theorem B2773253 : Blo 864565 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B1298693 : Blo 864565 1298693 := bbase (se 4 (by rfl) ⟨121752, by rfl⟩ : syracuseStep 1298693 = 243505) (by norm_num)
theorem B1954061 : Blo 864565 1954061 := bbase (se 3 (by rfl) ⟨366386, by rfl⟩ : syracuseStep 1954061 = 732773) (by norm_num)
theorem B1462549 : Blo 864565 1462549 := bbase (se 6 (by rfl) ⟨34278, by rfl⟩ : syracuseStep 1462549 = 68557) (by norm_num)
theorem B1298717 : Blo 864565 1298717 := bbase (se 3 (by rfl) ⟨243509, by rfl⟩ : syracuseStep 1298717 = 487019) (by norm_num)
theorem B1298741 : Blo 864565 1298741 := bbase (se 5 (by rfl) ⟨60878, by rfl⟩ : syracuseStep 1298741 = 121757) (by norm_num)
theorem B1298765 : Blo 864565 1298765 := bbase (se 3 (by rfl) ⟨243518, by rfl⟩ : syracuseStep 1298765 = 487037) (by norm_num)
theorem B1954133 : Blo 864565 1954133 := bbase (se 10 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 1954133 = 5725) (by norm_num)
theorem B1298789 : Blo 864565 1298789 := bbase (se 4 (by rfl) ⟨121761, by rfl⟩ : syracuseStep 1298789 = 243523) (by norm_num)
theorem B1462637 : Blo 864565 1462637 := bbase (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) (by norm_num)
theorem B1298813 : Blo 864565 1298813 := bbase (se 3 (by rfl) ⟨243527, by rfl⟩ : syracuseStep 1298813 = 487055) (by norm_num)
theorem B1298837 : Blo 864565 1298837 := bbase (se 6 (by rfl) ⟨30441, by rfl⟩ : syracuseStep 1298837 = 60883) (by norm_num)
theorem B1954205 : Blo 864565 1954205 := bbase (se 3 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 1954205 = 732827) (by norm_num)
theorem B1298861 : Blo 864565 1298861 := bbase (se 3 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 1298861 = 487073) (by norm_num)
theorem B1298885 : Blo 864565 1298885 := bbase (se 4 (by rfl) ⟨121770, by rfl⟩ : syracuseStep 1298885 = 243541) (by norm_num)
theorem B1298909 : Blo 864565 1298909 := bbase (se 3 (by rfl) ⟨243545, by rfl⟩ : syracuseStep 1298909 = 487091) (by norm_num)
theorem B1462765 : Blo 864565 1462765 := bbase (se 3 (by rfl) ⟨274268, by rfl⟩ : syracuseStep 1462765 = 548537) (by norm_num)
theorem B1298933 : Blo 864565 1298933 := bbase (se 5 (by rfl) ⟨60887, by rfl⟩ : syracuseStep 1298933 = 121775) (by norm_num)
theorem B1298957 : Blo 864565 1298957 := bbase (se 3 (by rfl) ⟨243554, by rfl⟩ : syracuseStep 1298957 = 487109) (by norm_num)
theorem B1692181 : Blo 864565 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B1298981 : Blo 864565 1298981 := bbase (se 4 (by rfl) ⟨121779, by rfl⟩ : syracuseStep 1298981 = 243559) (by norm_num)
theorem B938537 : Blo 864565 938537 := bbase (se 2 (by rfl) ⟨351951, by rfl⟩ : syracuseStep 938537 = 703903) (by norm_num)
theorem B1299005 : Blo 864565 1299005 := bbase (se 3 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 1299005 = 487127) (by norm_num)
theorem B1462853 : Blo 864565 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B1299029 : Blo 864565 1299029 := bbase (se 8 (by rfl) ⟨7611, by rfl⟩ : syracuseStep 1299029 = 15223) (by norm_num)
theorem B1299053 : Blo 864565 1299053 := bbase (se 3 (by rfl) ⟨243572, by rfl⟩ : syracuseStep 1299053 = 487145) (by norm_num)
theorem B1299077 : Blo 864565 1299077 := bbase (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) (by norm_num)
theorem B1299101 : Blo 864565 1299101 := bbase (se 3 (by rfl) ⟨243581, by rfl⟩ : syracuseStep 1299101 = 487163) (by norm_num)
theorem B1299125 : Blo 864565 1299125 := bbase (se 5 (by rfl) ⟨60896, by rfl⟩ : syracuseStep 1299125 = 121793) (by norm_num)
theorem B1462981 : Blo 864565 1462981 := bbase (se 4 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 1462981 = 274309) (by norm_num)
theorem B938693 : Blo 864565 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B1299149 : Blo 864565 1299149 := bbase (se 3 (by rfl) ⟨243590, by rfl⟩ : syracuseStep 1299149 = 487181) (by norm_num)
theorem B1299173 : Blo 864565 1299173 := bbase (se 4 (by rfl) ⟨121797, by rfl⟩ : syracuseStep 1299173 = 243595) (by norm_num)
theorem B1299197 : Blo 864565 1299197 := bbase (se 3 (by rfl) ⟨243599, by rfl⟩ : syracuseStep 1299197 = 487199) (by norm_num)
theorem B1299221 : Blo 864565 1299221 := bbase (se 6 (by rfl) ⟨30450, by rfl⟩ : syracuseStep 1299221 = 60901) (by norm_num)
theorem B1463069 : Blo 864565 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B1299245 : Blo 864565 1299245 := bbase (se 3 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 1299245 = 487217) (by norm_num)
theorem B1299269 : Blo 864565 1299269 := bbase (se 4 (by rfl) ⟨121806, by rfl⟩ : syracuseStep 1299269 = 243613) (by norm_num)
theorem B1299293 : Blo 864565 1299293 := bbase (se 3 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 1299293 = 487235) (by norm_num)
theorem B1299317 : Blo 864565 1299317 := bbase (se 5 (by rfl) ⟨60905, by rfl⟩ : syracuseStep 1299317 = 121811) (by norm_num)
theorem B1299341 : Blo 864565 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B1463197 : Blo 864565 1463197 := bbase (se 3 (by rfl) ⟨274349, by rfl⟩ : syracuseStep 1463197 = 548699) (by norm_num)
theorem B1299365 : Blo 864565 1299365 := bbase (se 4 (by rfl) ⟨121815, by rfl⟩ : syracuseStep 1299365 = 243631) (by norm_num)
theorem B1299389 : Blo 864565 1299389 := bbase (se 3 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 1299389 = 487271) (by norm_num)
theorem B1299413 : Blo 864565 1299413 := bbase (se 7 (by rfl) ⟨15227, by rfl⟩ : syracuseStep 1299413 = 30455) (by norm_num)
theorem B1299437 : Blo 864565 1299437 := bbase (se 3 (by rfl) ⟨243644, by rfl⟩ : syracuseStep 1299437 = 487289) (by norm_num)
theorem B1233901 : Blo 864565 1233901 := bbase (se 3 (by rfl) ⟨231356, by rfl⟩ : syracuseStep 1233901 = 462713) (by norm_num)
theorem B6575093 : Blo 864565 6575093 := bbase (se 5 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 6575093 = 616415) (by norm_num)
theorem B1463285 : Blo 864565 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B1299461 : Blo 864565 1299461 := bbase (se 4 (by rfl) ⟨121824, by rfl⟩ : syracuseStep 1299461 = 243649) (by norm_num)
theorem B4379669 : Blo 864565 4379669 := bbase (se 6 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 4379669 = 205297) (by norm_num)
theorem B1561621 : Blo 864565 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B1299485 : Blo 864565 1299485 := bbase (se 3 (by rfl) ⟨243653, by rfl⟩ : syracuseStep 1299485 = 487307) (by norm_num)
theorem B1299509 : Blo 864565 1299509 := bbase (se 5 (by rfl) ⟨60914, by rfl⟩ : syracuseStep 1299509 = 121829) (by norm_num)
theorem B1299533 : Blo 864565 1299533 := bbase (se 3 (by rfl) ⟨243662, by rfl⟩ : syracuseStep 1299533 = 487325) (by norm_num)
theorem B1561685 : Blo 864565 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B1299557 : Blo 864565 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B1463413 : Blo 864565 1463413 := bbase (se 5 (by rfl) ⟨68597, by rfl⟩ : syracuseStep 1463413 = 137195) (by norm_num)
theorem B1299581 : Blo 864565 1299581 := bbase (se 3 (by rfl) ⟨243671, by rfl⟩ : syracuseStep 1299581 = 487343) (by norm_num)
theorem B1299605 : Blo 864565 1299605 := bbase (se 6 (by rfl) ⟨30459, by rfl⟩ : syracuseStep 1299605 = 60919) (by norm_num)
theorem B1299629 : Blo 864565 1299629 := bbase (se 3 (by rfl) ⟨243680, by rfl⟩ : syracuseStep 1299629 = 487361) (by norm_num)
theorem B1299653 : Blo 864565 1299653 := bbase (se 4 (by rfl) ⟨121842, by rfl⟩ : syracuseStep 1299653 = 243685) (by norm_num)
theorem B1463501 : Blo 864565 1463501 := bbase (se 3 (by rfl) ⟨274406, by rfl⟩ : syracuseStep 1463501 = 548813) (by norm_num)
theorem B1299677 : Blo 864565 1299677 := bbase (se 3 (by rfl) ⟨243689, by rfl⟩ : syracuseStep 1299677 = 487379) (by norm_num)
theorem B1299701 : Blo 864565 1299701 := bbase (se 5 (by rfl) ⟨60923, by rfl⟩ : syracuseStep 1299701 = 121847) (by norm_num)
theorem B4936949 : Blo 864565 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B1299725 : Blo 864565 1299725 := bbase (se 3 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 1299725 = 487397) (by norm_num)
theorem B1168669 : Blo 864565 1168669 := bbase (se 3 (by rfl) ⟨219125, by rfl⟩ : syracuseStep 1168669 = 438251) (by norm_num)
theorem B1299749 : Blo 864565 1299749 := bbase (se 4 (by rfl) ⟨121851, by rfl⟩ : syracuseStep 1299749 = 243703) (by norm_num)
theorem B1299773 : Blo 864565 1299773 := bbase (se 3 (by rfl) ⟨243707, by rfl⟩ : syracuseStep 1299773 = 487415) (by norm_num)
theorem B1463629 : Blo 864565 1463629 := bbase (se 3 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 1463629 = 548861) (by norm_num)
theorem B1299797 : Blo 864565 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B1299821 : Blo 864565 1299821 := bbase (se 3 (by rfl) ⟨243716, by rfl⟩ : syracuseStep 1299821 = 487433) (by norm_num)
theorem B1299845 : Blo 864565 1299845 := bbase (se 4 (by rfl) ⟨121860, by rfl⟩ : syracuseStep 1299845 = 243721) (by norm_num)
theorem B1299869 : Blo 864565 1299869 := bbase (se 3 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 1299869 = 487451) (by norm_num)
theorem B1463717 : Blo 864565 1463717 := bbase (se 4 (by rfl) ⟨137223, by rfl⟩ : syracuseStep 1463717 = 274447) (by norm_num)
theorem B1299893 : Blo 864565 1299893 := bbase (se 5 (by rfl) ⟨60932, by rfl⟩ : syracuseStep 1299893 = 121865) (by norm_num)
theorem B1299917 : Blo 864565 1299917 := bbase (se 3 (by rfl) ⟨243734, by rfl⟩ : syracuseStep 1299917 = 487469) (by norm_num)
theorem B1299941 : Blo 864565 1299941 := bbase (se 4 (by rfl) ⟨121869, by rfl⟩ : syracuseStep 1299941 = 243739) (by norm_num)
theorem B1299965 : Blo 864565 1299965 := bbase (se 3 (by rfl) ⟨243743, by rfl⟩ : syracuseStep 1299965 = 487487) (by norm_num)
theorem B1299989 : Blo 864565 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B1463845 : Blo 864565 1463845 := bbase (se 4 (by rfl) ⟨137235, by rfl⟩ : syracuseStep 1463845 = 274471) (by norm_num)
theorem B1300013 : Blo 864565 1300013 := bbase (se 3 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 1300013 = 487505) (by norm_num)
theorem B1300037 : Blo 864565 1300037 := bbase (se 4 (by rfl) ⟨121878, by rfl⟩ : syracuseStep 1300037 = 243757) (by norm_num)
theorem B1300061 : Blo 864565 1300061 := bbase (se 3 (by rfl) ⟨243761, by rfl⟩ : syracuseStep 1300061 = 487523) (by norm_num)
theorem B1300085 : Blo 864565 1300085 := bbase (se 5 (by rfl) ⟨60941, by rfl⟩ : syracuseStep 1300085 = 121883) (by norm_num)
theorem B1463933 : Blo 864565 1463933 := bbase (se 3 (by rfl) ⟨274487, by rfl⟩ : syracuseStep 1463933 = 548975) (by norm_num)
theorem B1300109 : Blo 864565 1300109 := bbase (se 3 (by rfl) ⟨243770, by rfl⟩ : syracuseStep 1300109 = 487541) (by norm_num)
theorem B1300133 : Blo 864565 1300133 := bbase (se 4 (by rfl) ⟨121887, by rfl⟩ : syracuseStep 1300133 = 243775) (by norm_num)
theorem B2086573 : Blo 864565 2086573 := bbase (se 3 (by rfl) ⟨391232, by rfl⟩ : syracuseStep 2086573 = 782465) (by norm_num)
theorem B1300157 : Blo 864565 1300157 := bbase (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) (by norm_num)
theorem B1300181 : Blo 864565 1300181 := bbase (se 7 (by rfl) ⟨15236, by rfl⟩ : syracuseStep 1300181 = 30473) (by norm_num)
theorem B1300205 : Blo 864565 1300205 := bbase (se 3 (by rfl) ⟨243788, by rfl⟩ : syracuseStep 1300205 = 487577) (by norm_num)
theorem B1464061 : Blo 864565 1464061 := bbase (se 3 (by rfl) ⟨274511, by rfl⟩ : syracuseStep 1464061 = 549023) (by norm_num)
theorem B2807557 : Blo 864565 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B1300229 : Blo 864565 1300229 := bbase (se 4 (by rfl) ⟨121896, by rfl⟩ : syracuseStep 1300229 = 243793) (by norm_num)
theorem B1234693 : Blo 864565 1234693 := bbase (se 4 (by rfl) ⟨115752, by rfl⟩ : syracuseStep 1234693 = 231505) (by norm_num)
theorem B1300253 : Blo 864565 1300253 := bbase (se 3 (by rfl) ⟨243797, by rfl⟩ : syracuseStep 1300253 = 487595) (by norm_num)
theorem B1300277 : Blo 864565 1300277 := bbase (se 5 (by rfl) ⟨60950, by rfl⟩ : syracuseStep 1300277 = 121901) (by norm_num)
theorem B1300301 : Blo 864565 1300301 := bbase (se 3 (by rfl) ⟨243806, by rfl⟩ : syracuseStep 1300301 = 487613) (by norm_num)
theorem B1464149 : Blo 864565 1464149 := bbase (se 9 (by rfl) ⟨4289, by rfl⟩ : syracuseStep 1464149 = 8579) (by norm_num)
theorem B1300325 : Blo 864565 1300325 := bbase (se 4 (by rfl) ⟨121905, by rfl⟩ : syracuseStep 1300325 = 243811) (by norm_num)
theorem B972661 : Blo 864565 972661 := bbase (se 5 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 972661 = 91187) (by norm_num)
theorem B1300349 : Blo 864565 1300349 := bbase (se 3 (by rfl) ⟨243815, by rfl⟩ : syracuseStep 1300349 = 487631) (by norm_num)
theorem B1300373 : Blo 864565 1300373 := bbase (se 6 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 1300373 = 60955) (by norm_num)
theorem B972697 : Blo 864565 972697 := bbase (se 2 (by rfl) ⟨364761, by rfl⟩ : syracuseStep 972697 = 729523) (by norm_num)
theorem B1300397 : Blo 864565 1300397 := bbase (se 3 (by rfl) ⟨243824, by rfl⟩ : syracuseStep 1300397 = 487649) (by norm_num)
theorem B972733 : Blo 864565 972733 := bbase (se 3 (by rfl) ⟨182387, by rfl⟩ : syracuseStep 972733 = 364775) (by norm_num)
theorem B1300421 : Blo 864565 1300421 := bbase (se 4 (by rfl) ⟨121914, by rfl⟩ : syracuseStep 1300421 = 243829) (by norm_num)
theorem B1464277 : Blo 864565 1464277 := bbase (se 7 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 1464277 = 34319) (by norm_num)
theorem B1300445 : Blo 864565 1300445 := bbase (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) (by norm_num)
theorem B972769 : Blo 864565 972769 := bbase (se 2 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 972769 = 729577) (by norm_num)
theorem B1300469 : Blo 864565 1300469 := bbase (se 5 (by rfl) ⟨60959, by rfl⟩ : syracuseStep 1300469 = 121919) (by norm_num)
theorem B972805 : Blo 864565 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B1300493 : Blo 864565 1300493 := bbase (se 3 (by rfl) ⟨243842, by rfl⟩ : syracuseStep 1300493 = 487685) (by norm_num)
theorem B1300517 : Blo 864565 1300517 := bbase (se 4 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 1300517 = 243847) (by norm_num)
theorem B972841 : Blo 864565 972841 := bbase (se 2 (by rfl) ⟨364815, by rfl⟩ : syracuseStep 972841 = 729631) (by norm_num)
theorem B1464365 : Blo 864565 1464365 := bbase (se 3 (by rfl) ⟨274568, by rfl⟩ : syracuseStep 1464365 = 549137) (by norm_num)
theorem B1300541 : Blo 864565 1300541 := bbase (se 3 (by rfl) ⟨243851, by rfl⟩ : syracuseStep 1300541 = 487703) (by norm_num)
theorem B972877 : Blo 864565 972877 := bbase (se 3 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 972877 = 364829) (by norm_num)
theorem B1300565 : Blo 864565 1300565 := bbase (se 8 (by rfl) ⟨7620, by rfl⟩ : syracuseStep 1300565 = 15241) (by norm_num)
theorem B1235029 : Blo 864565 1235029 := bbase (se 8 (by rfl) ⟨7236, by rfl⟩ : syracuseStep 1235029 = 14473) (by norm_num)
theorem B1300589 : Blo 864565 1300589 := bbase (se 3 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 1300589 = 487721) (by norm_num)
theorem B972913 : Blo 864565 972913 := bbase (se 2 (by rfl) ⟨364842, by rfl⟩ : syracuseStep 972913 = 729685) (by norm_num)
theorem B1300613 : Blo 864565 1300613 := bbase (se 4 (by rfl) ⟨121932, by rfl⟩ : syracuseStep 1300613 = 243865) (by norm_num)
theorem B972949 : Blo 864565 972949 := bbase (se 6 (by rfl) ⟨22803, by rfl⟩ : syracuseStep 972949 = 45607) (by norm_num)
theorem B1300637 : Blo 864565 1300637 := bbase (se 3 (by rfl) ⟨243869, by rfl⟩ : syracuseStep 1300637 = 487739) (by norm_num)
theorem B1464493 : Blo 864565 1464493 := bbase (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) (by norm_num)
theorem B1300661 : Blo 864565 1300661 := bbase (se 5 (by rfl) ⟨60968, by rfl⟩ : syracuseStep 1300661 = 121937) (by norm_num)
theorem B972985 : Blo 864565 972985 := bbase (se 2 (by rfl) ⟨364869, by rfl⟩ : syracuseStep 972985 = 729739) (by norm_num)
theorem B1300685 : Blo 864565 1300685 := bbase (se 3 (by rfl) ⟨243878, by rfl⟩ : syracuseStep 1300685 = 487757) (by norm_num)
theorem B973021 : Blo 864565 973021 := bbase (se 3 (by rfl) ⟨182441, by rfl⟩ : syracuseStep 973021 = 364883) (by norm_num)
theorem B1300709 : Blo 864565 1300709 := bbase (se 4 (by rfl) ⟨121941, by rfl⟩ : syracuseStep 1300709 = 243883) (by norm_num)
theorem B1300733 : Blo 864565 1300733 := bbase (se 3 (by rfl) ⟨243887, by rfl⟩ : syracuseStep 1300733 = 487775) (by norm_num)
theorem B973057 : Blo 864565 973057 := bbase (se 2 (by rfl) ⟨364896, by rfl⟩ : syracuseStep 973057 = 729793) (by norm_num)
theorem B1464581 : Blo 864565 1464581 := bbase (se 4 (by rfl) ⟨137304, by rfl⟩ : syracuseStep 1464581 = 274609) (by norm_num)
theorem B1300757 : Blo 864565 1300757 := bbase (se 6 (by rfl) ⟨30486, by rfl⟩ : syracuseStep 1300757 = 60973) (by norm_num)
theorem B973093 : Blo 864565 973093 := bbase (se 4 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 973093 = 182455) (by norm_num)
theorem B4380965 : Blo 864565 4380965 := bbase (se 4 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 4380965 = 821431) (by norm_num)
theorem B1300781 : Blo 864565 1300781 := bbase (se 3 (by rfl) ⟨243896, by rfl⟩ : syracuseStep 1300781 = 487793) (by norm_num)
theorem B1235245 : Blo 864565 1235245 := bbase (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) (by norm_num)
theorem B1300805 : Blo 864565 1300805 := bbase (se 4 (by rfl) ⟨121950, by rfl⟩ : syracuseStep 1300805 = 243901) (by norm_num)
theorem B973129 : Blo 864565 973129 := bbase (se 2 (by rfl) ⟨364923, by rfl⟩ : syracuseStep 973129 = 729847) (by norm_num)
theorem B1038673 : Blo 864565 1038673 := bbase (se 2 (by rfl) ⟨389502, by rfl⟩ : syracuseStep 1038673 = 779005) (by norm_num)
theorem B1759573 : Blo 864565 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B1300829 : Blo 864565 1300829 := bbase (se 3 (by rfl) ⟨243905, by rfl⟩ : syracuseStep 1300829 = 487811) (by norm_num)
theorem B973165 : Blo 864565 973165 := bbase (se 3 (by rfl) ⟨182468, by rfl⟩ : syracuseStep 973165 = 364937) (by norm_num)
theorem B1300853 : Blo 864565 1300853 := bbase (se 5 (by rfl) ⟨60977, by rfl⟩ : syracuseStep 1300853 = 121955) (by norm_num)
theorem B1563005 : Blo 864565 1563005 := bbase (se 3 (by rfl) ⟨293063, by rfl⟩ : syracuseStep 1563005 = 586127) (by norm_num)
theorem B1464709 : Blo 864565 1464709 := bbase (se 4 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 1464709 = 274633) (by norm_num)
theorem B1300877 : Blo 864565 1300877 := bbase (se 3 (by rfl) ⟨243914, by rfl⟩ : syracuseStep 1300877 = 487829) (by norm_num)
theorem B973201 : Blo 864565 973201 := bbase (se 2 (by rfl) ⟨364950, by rfl⟩ : syracuseStep 973201 = 729901) (by norm_num)
theorem B1300901 : Blo 864565 1300901 := bbase (se 4 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 1300901 = 243919) (by norm_num)
theorem B973237 : Blo 864565 973237 := bbase (se 5 (by rfl) ⟨45620, by rfl⟩ : syracuseStep 973237 = 91241) (by norm_num)
theorem B8444341 : Blo 864565 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B5560757 : Blo 864565 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B1300925 : Blo 864565 1300925 := bbase (se 3 (by rfl) ⟨243923, by rfl⟩ : syracuseStep 1300925 = 487847) (by norm_num)
theorem B2775509 : Blo 864565 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B1300949 : Blo 864565 1300949 := bbase (se 7 (by rfl) ⟨15245, by rfl⟩ : syracuseStep 1300949 = 30491) (by norm_num)
theorem B973273 : Blo 864565 973273 := bbase (se 2 (by rfl) ⟨364977, by rfl⟩ : syracuseStep 973273 = 729955) (by norm_num)
theorem B1464797 : Blo 864565 1464797 := bbase (se 3 (by rfl) ⟨274649, by rfl⟩ : syracuseStep 1464797 = 549299) (by norm_num)
theorem B1300973 : Blo 864565 1300973 := bbase (se 3 (by rfl) ⟨243932, by rfl⟩ : syracuseStep 1300973 = 487865) (by norm_num)
theorem B973309 : Blo 864565 973309 := bbase (se 3 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 973309 = 364991) (by norm_num)
theorem B1300997 : Blo 864565 1300997 := bbase (se 4 (by rfl) ⟨121968, by rfl⟩ : syracuseStep 1300997 = 243937) (by norm_num)
theorem B2808341 : Blo 864565 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B1301021 : Blo 864565 1301021 := bbase (se 3 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 1301021 = 487883) (by norm_num)
theorem B973345 : Blo 864565 973345 := bbase (se 2 (by rfl) ⟨365004, by rfl⟩ : syracuseStep 973345 = 730009) (by norm_num)
theorem B1301045 : Blo 864565 1301045 := bbase (se 5 (by rfl) ⟨60986, by rfl⟩ : syracuseStep 1301045 = 121973) (by norm_num)
theorem B973381 : Blo 864565 973381 := bbase (se 4 (by rfl) ⟨91254, by rfl⟩ : syracuseStep 973381 = 182509) (by norm_num)
theorem B1301069 : Blo 864565 1301069 := bbase (se 3 (by rfl) ⟨243950, by rfl⟩ : syracuseStep 1301069 = 487901) (by norm_num)
theorem B2775637 : Blo 864565 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B1464925 : Blo 864565 1464925 := bbase (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) (by norm_num)
theorem B1301093 : Blo 864565 1301093 := bbase (se 4 (by rfl) ⟨121977, by rfl⟩ : syracuseStep 1301093 = 243955) (by norm_num)
theorem B973417 : Blo 864565 973417 := bbase (se 2 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 973417 = 730063) (by norm_num)
theorem B1301117 : Blo 864565 1301117 := bbase (se 3 (by rfl) ⟨243959, by rfl⟩ : syracuseStep 1301117 = 487919) (by norm_num)
theorem B973453 : Blo 864565 973453 := bbase (se 3 (by rfl) ⟨182522, by rfl⟩ : syracuseStep 973453 = 365045) (by norm_num)
theorem B1301141 : Blo 864565 1301141 := bbase (se 6 (by rfl) ⟨30495, by rfl⟩ : syracuseStep 1301141 = 60991) (by norm_num)
theorem B2808485 : Blo 864565 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B1235621 : Blo 864565 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B1301165 : Blo 864565 1301165 := bbase (se 3 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 1301165 = 487937) (by norm_num)
theorem B973489 : Blo 864565 973489 := bbase (se 2 (by rfl) ⟨365058, by rfl⟩ : syracuseStep 973489 = 730117) (by norm_num)
theorem B1465013 : Blo 864565 1465013 := bbase (se 5 (by rfl) ⟨68672, by rfl⟩ : syracuseStep 1465013 = 137345) (by norm_num)
theorem B1301189 : Blo 864565 1301189 := bbase (se 4 (by rfl) ⟨121986, by rfl⟩ : syracuseStep 1301189 = 243973) (by norm_num)
theorem B973525 : Blo 864565 973525 := bbase (se 7 (by rfl) ⟨11408, by rfl⟩ : syracuseStep 973525 = 22817) (by norm_num)
theorem B1301213 : Blo 864565 1301213 := bbase (se 3 (by rfl) ⟨243977, by rfl⟩ : syracuseStep 1301213 = 487955) (by norm_num)
theorem B1301237 : Blo 864565 1301237 := bbase (se 5 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 1301237 = 121991) (by norm_num)
theorem B973561 : Blo 864565 973561 := bbase (se 2 (by rfl) ⟨365085, by rfl⟩ : syracuseStep 973561 = 730171) (by norm_num)
theorem B1301261 : Blo 864565 1301261 := bbase (se 3 (by rfl) ⟨243986, by rfl⟩ : syracuseStep 1301261 = 487973) (by norm_num)
theorem B973597 : Blo 864565 973597 := bbase (se 3 (by rfl) ⟨182549, by rfl⟩ : syracuseStep 973597 = 365099) (by norm_num)
theorem B1301285 : Blo 864565 1301285 := bbase (se 4 (by rfl) ⟨121995, by rfl⟩ : syracuseStep 1301285 = 243991) (by norm_num)
theorem B1465141 : Blo 864565 1465141 := bbase (se 5 (by rfl) ⟨68678, by rfl⟩ : syracuseStep 1465141 = 137357) (by norm_num)
theorem B1301309 : Blo 864565 1301309 := bbase (se 3 (by rfl) ⟨243995, by rfl⟩ : syracuseStep 1301309 = 487991) (by norm_num)
theorem B973633 : Blo 864565 973633 := bbase (se 2 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 973633 = 730225) (by norm_num)
theorem B1760069 : Blo 864565 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1301333 : Blo 864565 1301333 := bbase (se 9 (by rfl) ⟨3812, by rfl⟩ : syracuseStep 1301333 = 7625) (by norm_num)
theorem B973669 : Blo 864565 973669 := bbase (se 4 (by rfl) ⟨91281, by rfl⟩ : syracuseStep 973669 = 182563) (by norm_num)
theorem B1301357 : Blo 864565 1301357 := bbase (se 3 (by rfl) ⟨244004, by rfl⟩ : syracuseStep 1301357 = 488009) (by norm_num)
theorem B1301381 : Blo 864565 1301381 := bbase (se 4 (by rfl) ⟨122004, by rfl⟩ : syracuseStep 1301381 = 244009) (by norm_num)
theorem B973705 : Blo 864565 973705 := bbase (se 2 (by rfl) ⟨365139, by rfl⟩ : syracuseStep 973705 = 730279) (by norm_num)
theorem B1465229 : Blo 864565 1465229 := bbase (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) (by norm_num)
theorem B1301405 : Blo 864565 1301405 := bbase (se 3 (by rfl) ⟨244013, by rfl⟩ : syracuseStep 1301405 = 488027) (by norm_num)
theorem B973741 : Blo 864565 973741 := bbase (se 3 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 973741 = 365153) (by norm_num)
theorem B1301429 : Blo 864565 1301429 := bbase (se 5 (by rfl) ⟨61004, by rfl⟩ : syracuseStep 1301429 = 122009) (by norm_num)
theorem B1301453 : Blo 864565 1301453 := bbase (se 3 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 1301453 = 488045) (by norm_num)
theorem B973777 : Blo 864565 973777 := bbase (se 2 (by rfl) ⟨365166, by rfl⟩ : syracuseStep 973777 = 730333) (by norm_num)
theorem B1301477 : Blo 864565 1301477 := bbase (se 4 (by rfl) ⟨122013, by rfl⟩ : syracuseStep 1301477 = 244027) (by norm_num)
theorem B973813 : Blo 864565 973813 := bbase (se 5 (by rfl) ⟨45647, by rfl⟩ : syracuseStep 973813 = 91295) (by norm_num)
theorem B1301501 : Blo 864565 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B1465357 : Blo 864565 1465357 := bbase (se 3 (by rfl) ⟨274754, by rfl⟩ : syracuseStep 1465357 = 549509) (by norm_num)
theorem B1301525 : Blo 864565 1301525 := bbase (se 6 (by rfl) ⟨30504, by rfl⟩ : syracuseStep 1301525 = 61009) (by norm_num)
theorem B973849 : Blo 864565 973849 := bbase (se 2 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 973849 = 730387) (by norm_num)
theorem B1301549 : Blo 864565 1301549 := bbase (se 3 (by rfl) ⟨244040, by rfl⟩ : syracuseStep 1301549 = 488081) (by norm_num)
theorem B1170485 : Blo 864565 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B973885 : Blo 864565 973885 := bbase (se 3 (by rfl) ⟨182603, by rfl⟩ : syracuseStep 973885 = 365207) (by norm_num)
theorem B1301573 : Blo 864565 1301573 := bbase (se 4 (by rfl) ⟨122022, by rfl⟩ : syracuseStep 1301573 = 244045) (by norm_num)
theorem B1301597 : Blo 864565 1301597 := bbase (se 3 (by rfl) ⟨244049, by rfl⟩ : syracuseStep 1301597 = 488099) (by norm_num)
theorem B973921 : Blo 864565 973921 := bbase (se 2 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 973921 = 730441) (by norm_num)
theorem B1465445 : Blo 864565 1465445 := bbase (se 4 (by rfl) ⟨137385, by rfl⟩ : syracuseStep 1465445 = 274771) (by norm_num)
theorem B1301621 : Blo 864565 1301621 := bbase (se 5 (by rfl) ⟨61013, by rfl⟩ : syracuseStep 1301621 = 122027) (by norm_num)
theorem B973957 : Blo 864565 973957 := bbase (se 4 (by rfl) ⟨91308, by rfl⟩ : syracuseStep 973957 = 182617) (by norm_num)
theorem B1301645 : Blo 864565 1301645 := bbase (se 3 (by rfl) ⟨244058, by rfl⟩ : syracuseStep 1301645 = 488117) (by norm_num)
theorem B1301669 : Blo 864565 1301669 := bbase (se 4 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 1301669 = 244063) (by norm_num)
theorem B973993 : Blo 864565 973993 := bbase (se 2 (by rfl) ⟨365247, by rfl⟩ : syracuseStep 973993 = 730495) (by norm_num)
theorem B1301693 : Blo 864565 1301693 := bbase (se 3 (by rfl) ⟨244067, by rfl⟩ : syracuseStep 1301693 = 488135) (by norm_num)
theorem B974029 : Blo 864565 974029 := bbase (se 3 (by rfl) ⟨182630, by rfl⟩ : syracuseStep 974029 = 365261) (by norm_num)
theorem B1301717 : Blo 864565 1301717 := bbase (se 7 (by rfl) ⟨15254, by rfl⟩ : syracuseStep 1301717 = 30509) (by norm_num)
theorem B1465573 : Blo 864565 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B1301741 : Blo 864565 1301741 := bbase (se 3 (by rfl) ⟨244076, by rfl⟩ : syracuseStep 1301741 = 488153) (by norm_num)
theorem B974065 : Blo 864565 974065 := bbase (se 2 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 974065 = 730549) (by norm_num)
theorem B1301765 : Blo 864565 1301765 := bbase (se 4 (by rfl) ⟨122040, by rfl⟩ : syracuseStep 1301765 = 244081) (by norm_num)
theorem B974101 : Blo 864565 974101 := bbase (se 6 (by rfl) ⟨22830, by rfl⟩ : syracuseStep 974101 = 45661) (by norm_num)
theorem B1301789 : Blo 864565 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B1301813 : Blo 864565 1301813 := bbase (se 5 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 1301813 = 122045) (by norm_num)
theorem B974137 : Blo 864565 974137 := bbase (se 2 (by rfl) ⟨365301, by rfl⟩ : syracuseStep 974137 = 730603) (by norm_num)
theorem B1465661 : Blo 864565 1465661 := bbase (se 3 (by rfl) ⟨274811, by rfl⟩ : syracuseStep 1465661 = 549623) (by norm_num)
theorem B1301837 : Blo 864565 1301837 := bbase (se 3 (by rfl) ⟨244094, by rfl⟩ : syracuseStep 1301837 = 488189) (by norm_num)
theorem B974173 : Blo 864565 974173 := bbase (se 3 (by rfl) ⟨182657, by rfl⟩ : syracuseStep 974173 = 365315) (by norm_num)
theorem B1301861 : Blo 864565 1301861 := bbase (se 4 (by rfl) ⟨122049, by rfl⟩ : syracuseStep 1301861 = 244099) (by norm_num)
theorem B1301885 : Blo 864565 1301885 := bbase (se 3 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 1301885 = 488207) (by norm_num)
theorem B974209 : Blo 864565 974209 := bbase (se 2 (by rfl) ⟨365328, by rfl⟩ : syracuseStep 974209 = 730657) (by norm_num)
theorem B4939157 : Blo 864565 4939157 := bbase (se 6 (by rfl) ⟨115761, by rfl⟩ : syracuseStep 4939157 = 231523) (by norm_num)
theorem B1301909 : Blo 864565 1301909 := bbase (se 6 (by rfl) ⟨30513, by rfl⟩ : syracuseStep 1301909 = 61027) (by norm_num)
theorem B974245 : Blo 864565 974245 := bbase (se 4 (by rfl) ⟨91335, by rfl⟩ : syracuseStep 974245 = 182671) (by norm_num)
theorem B1301933 : Blo 864565 1301933 := bbase (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) (by norm_num)
theorem B1301957 : Blo 864565 1301957 := bbase (se 4 (by rfl) ⟨122058, by rfl⟩ : syracuseStep 1301957 = 244117) (by norm_num)
theorem B974281 : Blo 864565 974281 := bbase (se 2 (by rfl) ⟨365355, by rfl⟩ : syracuseStep 974281 = 730711) (by norm_num)
theorem B1760717 : Blo 864565 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B1301981 : Blo 864565 1301981 := bbase (se 3 (by rfl) ⟨244121, by rfl⟩ : syracuseStep 1301981 = 488243) (by norm_num)
theorem B974317 : Blo 864565 974317 := bbase (se 3 (by rfl) ⟨182684, by rfl⟩ : syracuseStep 974317 = 365369) (by norm_num)
theorem B1302005 : Blo 864565 1302005 := bbase (se 5 (by rfl) ⟨61031, by rfl⟩ : syracuseStep 1302005 = 122063) (by norm_num)
theorem B1302029 : Blo 864565 1302029 := bbase (se 3 (by rfl) ⟨244130, by rfl⟩ : syracuseStep 1302029 = 488261) (by norm_num)
theorem B974353 : Blo 864565 974353 := bbase (se 2 (by rfl) ⟨365382, by rfl⟩ : syracuseStep 974353 = 730765) (by norm_num)
theorem B1302053 : Blo 864565 1302053 := bbase (se 4 (by rfl) ⟨122067, by rfl⟩ : syracuseStep 1302053 = 244135) (by norm_num)
theorem B4382261 : Blo 864565 4382261 := bbase (se 5 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 4382261 = 410837) (by norm_num)
theorem B974389 : Blo 864565 974389 := bbase (se 5 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 974389 = 91349) (by norm_num)
theorem B1302077 : Blo 864565 1302077 := bbase (se 3 (by rfl) ⟨244139, by rfl⟩ : syracuseStep 1302077 = 488279) (by norm_num)
theorem B1826381 : Blo 864565 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B1302101 : Blo 864565 1302101 := bbase (se 8 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 1302101 = 15259) (by norm_num)
theorem B974425 : Blo 864565 974425 := bbase (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) (by norm_num)
theorem B1302125 : Blo 864565 1302125 := bbase (se 3 (by rfl) ⟨244148, by rfl⟩ : syracuseStep 1302125 = 488297) (by norm_num)
theorem B974461 : Blo 864565 974461 := bbase (se 3 (by rfl) ⟨182711, by rfl⟩ : syracuseStep 974461 = 365423) (by norm_num)
theorem B2219653 : Blo 864565 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B1302149 : Blo 864565 1302149 := bbase (se 4 (by rfl) ⟨122076, by rfl⟩ : syracuseStep 1302149 = 244153) (by norm_num)
theorem B1564309 : Blo 864565 1564309 := bbase (se 6 (by rfl) ⟨36663, by rfl⟩ : syracuseStep 1564309 = 73327) (by norm_num)
theorem B1302173 : Blo 864565 1302173 := bbase (se 3 (by rfl) ⟨244157, by rfl⟩ : syracuseStep 1302173 = 488315) (by norm_num)
theorem B974497 : Blo 864565 974497 := bbase (se 2 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 974497 = 730873) (by norm_num)
theorem B1302197 : Blo 864565 1302197 := bbase (se 5 (by rfl) ⟨61040, by rfl⟩ : syracuseStep 1302197 = 122081) (by norm_num)
theorem B974533 : Blo 864565 974533 := bbase (se 4 (by rfl) ⟨91362, by rfl⟩ : syracuseStep 974533 = 182725) (by norm_num)
theorem B1302221 : Blo 864565 1302221 := bbase (se 3 (by rfl) ⟨244166, by rfl⟩ : syracuseStep 1302221 = 488333) (by norm_num)
theorem B1302245 : Blo 864565 1302245 := bbase (se 4 (by rfl) ⟨122085, by rfl⟩ : syracuseStep 1302245 = 244171) (by norm_num)
theorem B974569 : Blo 864565 974569 := bbase (se 2 (by rfl) ⟨365463, by rfl⟩ : syracuseStep 974569 = 730927) (by norm_num)
theorem B1302269 : Blo 864565 1302269 := bbase (se 3 (by rfl) ⟨244175, by rfl⟩ : syracuseStep 1302269 = 488351) (by norm_num)
theorem B974605 : Blo 864565 974605 := bbase (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) (by norm_num)
theorem B1302293 : Blo 864565 1302293 := bbase (se 6 (by rfl) ⟨30522, by rfl⟩ : syracuseStep 1302293 = 61045) (by norm_num)
theorem B1302317 : Blo 864565 1302317 := bbase (se 3 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 1302317 = 488369) (by norm_num)
theorem B974641 : Blo 864565 974641 := bbase (se 2 (by rfl) ⟨365490, by rfl⟩ : syracuseStep 974641 = 730981) (by norm_num)
theorem B1302341 : Blo 864565 1302341 := bbase (se 4 (by rfl) ⟨122094, by rfl⟩ : syracuseStep 1302341 = 244189) (by norm_num)
theorem B974677 : Blo 864565 974677 := bbase (se 9 (by rfl) ⟨2855, by rfl⟩ : syracuseStep 974677 = 5711) (by norm_num)
theorem B1302365 : Blo 864565 1302365 := bbase (se 3 (by rfl) ⟨244193, by rfl⟩ : syracuseStep 1302365 = 488387) (by norm_num)
theorem B1302389 : Blo 864565 1302389 := bbase (se 5 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 1302389 = 122099) (by norm_num)
theorem B1040249 : Blo 864565 1040249 := bbase (se 2 (by rfl) ⟨390093, by rfl⟩ : syracuseStep 1040249 = 780187) (by norm_num)
theorem B974713 : Blo 864565 974713 := bbase (se 2 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 974713 = 731035) (by norm_num)
theorem B1302413 : Blo 864565 1302413 := bbase (se 3 (by rfl) ⟨244202, by rfl⟩ : syracuseStep 1302413 = 488405) (by norm_num)
theorem B974749 : Blo 864565 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B1302437 : Blo 864565 1302437 := bbase (se 4 (by rfl) ⟨122103, by rfl⟩ : syracuseStep 1302437 = 244207) (by norm_num)
theorem B1302461 : Blo 864565 1302461 := bbase (se 3 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 1302461 = 488423) (by norm_num)
theorem B974785 : Blo 864565 974785 := bbase (se 2 (by rfl) ⟨365544, by rfl⟩ : syracuseStep 974785 = 731089) (by norm_num)
theorem B1302485 : Blo 864565 1302485 := bbase (se 7 (by rfl) ⟨15263, by rfl⟩ : syracuseStep 1302485 = 30527) (by norm_num)
theorem B974821 : Blo 864565 974821 := bbase (se 4 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 974821 = 182779) (by norm_num)
theorem B1302509 : Blo 864565 1302509 := bbase (se 3 (by rfl) ⟨244220, by rfl⟩ : syracuseStep 1302509 = 488441) (by norm_num)
theorem B1302533 : Blo 864565 1302533 := bbase (se 4 (by rfl) ⟨122112, by rfl⟩ : syracuseStep 1302533 = 244225) (by norm_num)
theorem B974857 : Blo 864565 974857 := bbase (se 2 (by rfl) ⟨365571, by rfl⟩ : syracuseStep 974857 = 731143) (by norm_num)
theorem B1302557 : Blo 864565 1302557 := bbase (se 3 (by rfl) ⟨244229, by rfl⟩ : syracuseStep 1302557 = 488459) (by norm_num)
theorem B974893 : Blo 864565 974893 := bbase (se 3 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 974893 = 365585) (by norm_num)
theorem B1302581 : Blo 864565 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B1302605 : Blo 864565 1302605 := bbase (se 3 (by rfl) ⟨244238, by rfl⟩ : syracuseStep 1302605 = 488477) (by norm_num)
theorem B974929 : Blo 864565 974929 := bbase (se 2 (by rfl) ⟨365598, by rfl⟩ : syracuseStep 974929 = 731197) (by norm_num)
theorem B1302629 : Blo 864565 1302629 := bbase (se 4 (by rfl) ⟨122121, by rfl⟩ : syracuseStep 1302629 = 244243) (by norm_num)
theorem B974965 : Blo 864565 974965 := bbase (se 5 (by rfl) ⟨45701, by rfl⟩ : syracuseStep 974965 = 91403) (by norm_num)
theorem B1302653 : Blo 864565 1302653 := bbase (se 3 (by rfl) ⟨244247, by rfl⟩ : syracuseStep 1302653 = 488495) (by norm_num)
theorem B1302677 : Blo 864565 1302677 := bbase (se 6 (by rfl) ⟨30531, by rfl⟩ : syracuseStep 1302677 = 61063) (by norm_num)
theorem B975001 : Blo 864565 975001 := bbase (se 2 (by rfl) ⟨365625, by rfl⟩ : syracuseStep 975001 = 731251) (by norm_num)
theorem B1302701 : Blo 864565 1302701 := bbase (se 3 (by rfl) ⟨244256, by rfl⟩ : syracuseStep 1302701 = 488513) (by norm_num)
theorem B876725 : Blo 864565 876725 := bbase (se 5 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 876725 = 82193) (by norm_num)
theorem B975037 : Blo 864565 975037 := bbase (se 3 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 975037 = 365639) (by norm_num)
theorem B1302725 : Blo 864565 1302725 := bbase (se 4 (by rfl) ⟨122130, by rfl⟩ : syracuseStep 1302725 = 244261) (by norm_num)
theorem B1040585 : Blo 864565 1040585 := bbase (se 2 (by rfl) ⟨390219, by rfl⟩ : syracuseStep 1040585 = 780439) (by norm_num)
theorem B1302749 : Blo 864565 1302749 := bbase (se 3 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 1302749 = 488531) (by norm_num)
theorem B975073 : Blo 864565 975073 := bbase (se 2 (by rfl) ⟨365652, by rfl⟩ : syracuseStep 975073 = 731305) (by norm_num)
theorem B1302773 : Blo 864565 1302773 := bbase (se 5 (by rfl) ⟨61067, by rfl⟩ : syracuseStep 1302773 = 122135) (by norm_num)
theorem B975109 : Blo 864565 975109 := bbase (se 4 (by rfl) ⟨91416, by rfl⟩ : syracuseStep 975109 = 182833) (by norm_num)
theorem B1302797 : Blo 864565 1302797 := bbase (se 3 (by rfl) ⟨244274, by rfl⟩ : syracuseStep 1302797 = 488549) (by norm_num)
theorem B1302821 : Blo 864565 1302821 := bbase (se 4 (by rfl) ⟨122139, by rfl⟩ : syracuseStep 1302821 = 244279) (by norm_num)
theorem B975145 : Blo 864565 975145 := bbase (se 2 (by rfl) ⟨365679, by rfl⟩ : syracuseStep 975145 = 731359) (by norm_num)
theorem B1040701 : Blo 864565 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B1302845 : Blo 864565 1302845 := bbase (se 3 (by rfl) ⟨244283, by rfl⟩ : syracuseStep 1302845 = 488567) (by norm_num)
theorem B3760453 : Blo 864565 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B975181 : Blo 864565 975181 := bbase (se 3 (by rfl) ⟨182846, by rfl⟩ : syracuseStep 975181 = 365693) (by norm_num)
theorem B1171805 : Blo 864565 1171805 := bbase (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) (by norm_num)
theorem B975217 : Blo 864565 975217 := bbase (se 2 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 975217 = 731413) (by norm_num)
theorem B1040773 : Blo 864565 1040773 := bbase (se 4 (by rfl) ⟨97572, by rfl⟩ : syracuseStep 1040773 = 195145) (by norm_num)
theorem B2810261 : Blo 864565 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B975253 : Blo 864565 975253 := bbase (se 6 (by rfl) ⟨22857, by rfl⟩ : syracuseStep 975253 = 45715) (by norm_num)
theorem B1040797 : Blo 864565 1040797 := bbase (se 3 (by rfl) ⟨195149, by rfl⟩ : syracuseStep 1040797 = 390299) (by norm_num)
theorem B975289 : Blo 864565 975289 := bbase (se 2 (by rfl) ⟨365733, by rfl⟩ : syracuseStep 975289 = 731467) (by norm_num)
theorem B975325 : Blo 864565 975325 := bbase (se 3 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 975325 = 365747) (by norm_num)
theorem B5071349 : Blo 864565 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B975361 : Blo 864565 975361 := bbase (se 2 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 975361 = 731521) (by norm_num)
theorem B975397 : Blo 864565 975397 := bbase (se 4 (by rfl) ⟨91443, by rfl⟩ : syracuseStep 975397 = 182887) (by norm_num)
theorem B1040941 : Blo 864565 1040941 := bbase (se 3 (by rfl) ⟨195176, by rfl⟩ : syracuseStep 1040941 = 390353) (by norm_num)
theorem B975433 : Blo 864565 975433 := bbase (se 2 (by rfl) ⟨365787, by rfl⟩ : syracuseStep 975433 = 731575) (by norm_num)
theorem B975469 : Blo 864565 975469 := bbase (se 3 (by rfl) ⟨182900, by rfl⟩ : syracuseStep 975469 = 365801) (by norm_num)
theorem B975505 : Blo 864565 975505 := bbase (se 2 (by rfl) ⟨365814, by rfl⟩ : syracuseStep 975505 = 731629) (by norm_num)
theorem B975541 : Blo 864565 975541 := bbase (se 5 (by rfl) ⟨45728, by rfl⟩ : syracuseStep 975541 = 91457) (by norm_num)
theorem B1172173 : Blo 864565 1172173 := bbase (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) (by norm_num)
theorem B975577 : Blo 864565 975577 := bbase (se 2 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 975577 = 731683) (by norm_num)
theorem B975613 : Blo 864565 975613 := bbase (se 3 (by rfl) ⟨182927, by rfl⟩ : syracuseStep 975613 = 365855) (by norm_num)
theorem B975649 : Blo 864565 975649 := bbase (se 2 (by rfl) ⟨365868, by rfl⟩ : syracuseStep 975649 = 731737) (by norm_num)
theorem B1336109 : Blo 864565 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B2220853 : Blo 864565 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B4383557 : Blo 864565 4383557 := bbase (se 4 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 4383557 = 821917) (by norm_num)
theorem B975685 : Blo 864565 975685 := bbase (se 4 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 975685 = 182941) (by norm_num)
theorem B975721 : Blo 864565 975721 := bbase (se 2 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 975721 = 731791) (by norm_num)
theorem B975757 : Blo 864565 975757 := bbase (se 3 (by rfl) ⟨182954, by rfl⟩ : syracuseStep 975757 = 365909) (by norm_num)
theorem B975793 : Blo 864565 975793 := bbase (se 2 (by rfl) ⟨365922, by rfl⟩ : syracuseStep 975793 = 731845) (by norm_num)
theorem B975829 : Blo 864565 975829 := bbase (se 7 (by rfl) ⟨11435, by rfl⟩ : syracuseStep 975829 = 22871) (by norm_num)
theorem B975865 : Blo 864565 975865 := bbase (se 2 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 975865 = 731899) (by norm_num)
theorem B975901 : Blo 864565 975901 := bbase (se 3 (by rfl) ⟨182981, by rfl⟩ : syracuseStep 975901 = 365963) (by norm_num)
theorem B975937 : Blo 864565 975937 := bbase (se 2 (by rfl) ⟨365976, by rfl⟩ : syracuseStep 975937 = 731953) (by norm_num)
theorem B1664077 : Blo 864565 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B1172557 : Blo 864565 1172557 := bbase (se 3 (by rfl) ⟨219854, by rfl⟩ : syracuseStep 1172557 = 439709) (by norm_num)
theorem B7398485 : Blo 864565 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B975973 : Blo 864565 975973 := bbase (se 4 (by rfl) ⟨91497, by rfl⟩ : syracuseStep 975973 = 182995) (by norm_num)
theorem B4285541 : Blo 864565 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B976009 : Blo 864565 976009 := bbase (se 2 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 976009 = 732007) (by norm_num)
theorem B976045 : Blo 864565 976045 := bbase (se 3 (by rfl) ⟨183008, by rfl⟩ : syracuseStep 976045 = 366017) (by norm_num)
theorem B976081 : Blo 864565 976081 := bbase (se 2 (by rfl) ⟨366030, by rfl⟩ : syracuseStep 976081 = 732061) (by norm_num)
theorem B5268725 : Blo 864565 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B976117 : Blo 864565 976117 := bbase (se 5 (by rfl) ⟨45755, by rfl⟩ : syracuseStep 976117 = 91511) (by norm_num)
theorem B976153 : Blo 864565 976153 := bbase (se 2 (by rfl) ⟨366057, by rfl⟩ : syracuseStep 976153 = 732115) (by norm_num)
theorem B2221357 : Blo 864565 2221357 := bbase (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) (by norm_num)
theorem B976189 : Blo 864565 976189 := bbase (se 3 (by rfl) ⟨183035, by rfl⟩ : syracuseStep 976189 = 366071) (by norm_num)
theorem B976225 : Blo 864565 976225 := bbase (se 2 (by rfl) ⟨366084, by rfl⟩ : syracuseStep 976225 = 732169) (by norm_num)
theorem B976261 : Blo 864565 976261 := bbase (se 4 (by rfl) ⟨91524, by rfl⟩ : syracuseStep 976261 = 183049) (by norm_num)
theorem B2778533 : Blo 864565 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B976297 : Blo 864565 976297 := bbase (se 2 (by rfl) ⟨366111, by rfl⟩ : syracuseStep 976297 = 732223) (by norm_num)
theorem B8316341 : Blo 864565 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B2188741 : Blo 864565 2188741 := bbase (se 4 (by rfl) ⟨205194, by rfl⟩ : syracuseStep 2188741 = 410389) (by norm_num)
theorem B976333 : Blo 864565 976333 := bbase (se 3 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 976333 = 366125) (by norm_num)
theorem B1664477 : Blo 864565 1664477 := bbase (se 3 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 1664477 = 624179) (by norm_num)
theorem B976369 : Blo 864565 976369 := bbase (se 2 (by rfl) ⟨366138, by rfl⟩ : syracuseStep 976369 = 732277) (by norm_num)
theorem B976405 : Blo 864565 976405 := bbase (se 6 (by rfl) ⟨22884, by rfl⟩ : syracuseStep 976405 = 45769) (by norm_num)
theorem B2188853 : Blo 864565 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B976441 : Blo 864565 976441 := bbase (se 2 (by rfl) ⟨366165, by rfl⟩ : syracuseStep 976441 = 732331) (by norm_num)
theorem B976477 : Blo 864565 976477 := bbase (se 3 (by rfl) ⟨183089, by rfl⟩ : syracuseStep 976477 = 366179) (by norm_num)
theorem B976513 : Blo 864565 976513 := bbase (se 2 (by rfl) ⟨366192, by rfl⟩ : syracuseStep 976513 = 732385) (by norm_num)
theorem B976549 : Blo 864565 976549 := bbase (se 4 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 976549 = 183103) (by norm_num)
theorem B976585 : Blo 864565 976585 := bbase (se 2 (by rfl) ⟨366219, by rfl⟩ : syracuseStep 976585 = 732439) (by norm_num)
theorem B1042157 : Blo 864565 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B976621 : Blo 864565 976621 := bbase (se 3 (by rfl) ⟨183116, by rfl⟩ : syracuseStep 976621 = 366233) (by norm_num)
theorem B2189045 : Blo 864565 2189045 := bbase (se 5 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 2189045 = 205223) (by norm_num)
theorem B976657 : Blo 864565 976657 := bbase (se 2 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 976657 = 732493) (by norm_num)
theorem B976693 : Blo 864565 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B976729 : Blo 864565 976729 := bbase (se 2 (by rfl) ⟨366273, by rfl⟩ : syracuseStep 976729 = 732547) (by norm_num)
theorem B976765 : Blo 864565 976765 := bbase (se 3 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 976765 = 366287) (by norm_num)
theorem B976801 : Blo 864565 976801 := bbase (se 2 (by rfl) ⟨366300, by rfl⟩ : syracuseStep 976801 = 732601) (by norm_num)
theorem B976837 : Blo 864565 976837 := bbase (se 4 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 976837 = 183157) (by norm_num)
theorem B976873 : Blo 864565 976873 := bbase (se 2 (by rfl) ⟨366327, by rfl⟩ : syracuseStep 976873 = 732655) (by norm_num)
theorem B976909 : Blo 864565 976909 := bbase (se 3 (by rfl) ⟨183170, by rfl⟩ : syracuseStep 976909 = 366341) (by norm_num)
theorem B6252565 : Blo 864565 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B1042465 : Blo 864565 1042465 := bbase (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) (by norm_num)
theorem B976945 : Blo 864565 976945 := bbase (se 2 (by rfl) ⟨366354, by rfl⟩ : syracuseStep 976945 = 732709) (by norm_num)
theorem B4155461 : Blo 864565 4155461 := bbase (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) (by norm_num)
theorem B2189389 : Blo 864565 2189389 := bbase (se 3 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 2189389 = 821021) (by norm_num)
theorem B4384853 : Blo 864565 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B976981 : Blo 864565 976981 := bbase (se 8 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 976981 = 11449) (by norm_num)
theorem B977017 : Blo 864565 977017 := bbase (se 2 (by rfl) ⟨366381, by rfl⟩ : syracuseStep 977017 = 732763) (by norm_num)
theorem B1042565 : Blo 864565 1042565 := bbase (se 4 (by rfl) ⟨97740, by rfl⟩ : syracuseStep 1042565 = 195481) (by norm_num)
theorem B1927325 : Blo 864565 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B977053 : Blo 864565 977053 := bbase (se 3 (by rfl) ⟨183197, by rfl⟩ : syracuseStep 977053 = 366395) (by norm_num)
theorem B2189501 : Blo 864565 2189501 := bbase (se 3 (by rfl) ⟨410531, by rfl⟩ : syracuseStep 2189501 = 821063) (by norm_num)
theorem B977089 : Blo 864565 977089 := bbase (se 2 (by rfl) ⟨366408, by rfl⟩ : syracuseStep 977089 = 732817) (by norm_num)
theorem B878801 : Blo 864565 878801 := bbase (se 2 (by rfl) ⟨329550, by rfl⟩ : syracuseStep 878801 = 659101) (by norm_num)
theorem B977125 : Blo 864565 977125 := bbase (se 4 (by rfl) ⟨91605, by rfl⟩ : syracuseStep 977125 = 183211) (by norm_num)
theorem B1665293 : Blo 864565 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B2189693 : Blo 864565 2189693 := bbase (se 3 (by rfl) ⟨410567, by rfl⟩ : syracuseStep 2189693 = 821135) (by norm_num)
theorem B3697109 : Blo 864565 3697109 := bbase (se 7 (by rfl) ⟨43325, by rfl⟩ : syracuseStep 3697109 = 86651) (by norm_num)
theorem B1042969 : Blo 864565 1042969 := bbase (se 2 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 1042969 = 782227) (by norm_num)
theorem B2190037 : Blo 864565 2190037 := bbase (se 7 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 2190037 = 51329) (by norm_num)
theorem B3697397 : Blo 864565 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B879421 : Blo 864565 879421 := bbase (se 3 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 879421 = 329783) (by norm_num)
theorem B2190149 : Blo 864565 2190149 := bbase (se 4 (by rfl) ⟨205326, by rfl⟩ : syracuseStep 2190149 = 410653) (by norm_num)
theorem B1043353 : Blo 864565 1043353 := bbase (se 2 (by rfl) ⟨391257, by rfl⟩ : syracuseStep 1043353 = 782515) (by norm_num)
theorem B9989077 : Blo 864565 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B2190341 : Blo 864565 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B2190685 : Blo 864565 2190685 := bbase (se 3 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 2190685 = 821507) (by norm_num)
theorem B4386149 : Blo 864565 4386149 := bbase (se 4 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 4386149 = 822403) (by norm_num)
theorem B5270933 : Blo 864565 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B2190797 : Blo 864565 2190797 := bbase (se 3 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 2190797 = 821549) (by norm_num)
theorem B3698149 : Blo 864565 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B1404469 : Blo 864565 1404469 := bbase (se 5 (by rfl) ⟨65834, by rfl⟩ : syracuseStep 1404469 = 131669) (by norm_num)
theorem B2780725 : Blo 864565 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B1109569 : Blo 864565 1109569 := bbase (se 2 (by rfl) ⟨416088, by rfl⟩ : syracuseStep 1109569 = 832177) (by norm_num)
theorem B880265 : Blo 864565 880265 := bbase (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) (by norm_num)
theorem B2190989 : Blo 864565 2190989 := bbase (se 3 (by rfl) ⟨410810, by rfl⟩ : syracuseStep 2190989 = 821621) (by norm_num)
theorem B1502885 : Blo 864565 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B1044149 : Blo 864565 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B2191333 : Blo 864565 2191333 := bbase (se 4 (by rfl) ⟨205437, by rfl⟩ : syracuseStep 2191333 = 410875) (by norm_num)
theorem B7041077 : Blo 864565 7041077 := bbase (se 5 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 7041077 = 660101) (by norm_num)
theorem B2191445 : Blo 864565 2191445 := bbase (se 8 (by rfl) ⟨12840, by rfl⟩ : syracuseStep 2191445 = 25681) (by norm_num)
theorem B4681813 : Blo 864565 4681813 := bbase (se 8 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 4681813 = 54865) (by norm_num)
theorem B1110125 : Blo 864565 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1110181 : Blo 864565 1110181 := bbase (se 4 (by rfl) ⟨104079, by rfl⟩ : syracuseStep 1110181 = 208159) (by norm_num)
theorem B3698885 : Blo 864565 3698885 := bbase (se 4 (by rfl) ⟨346770, by rfl⟩ : syracuseStep 3698885 = 693541) (by norm_num)
theorem B2191637 : Blo 864565 2191637 := bbase (se 6 (by rfl) ⟨51366, by rfl⟩ : syracuseStep 2191637 = 102733) (by norm_num)
theorem B2781557 : Blo 864565 2781557 := bbase (se 5 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 2781557 = 260771) (by norm_num)
theorem B1667525 : Blo 864565 1667525 := bbase (se 4 (by rfl) ⟨156330, by rfl⟩ : syracuseStep 1667525 = 312661) (by norm_num)
theorem B4747733 : Blo 864565 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B1667557 : Blo 864565 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B6582869 : Blo 864565 6582869 := bbase (se 8 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 6582869 = 77143) (by norm_num)
theorem B2191981 : Blo 864565 2191981 := bbase (se 3 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 2191981 = 821993) (by norm_num)
theorem B4387445 : Blo 864565 4387445 := bbase (se 5 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 4387445 = 411323) (by norm_num)
theorem B2257573 : Blo 864565 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B2192093 : Blo 864565 2192093 := bbase (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) (by norm_num)
theorem B1110781 : Blo 864565 1110781 := bbase (se 3 (by rfl) ⟨208271, by rfl⟩ : syracuseStep 1110781 = 416543) (by norm_num)
theorem B4682549 : Blo 864565 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B2192285 : Blo 864565 2192285 := bbase (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) (by norm_num)
theorem B2192629 : Blo 864565 2192629 := bbase (se 5 (by rfl) ⟨102779, by rfl⟩ : syracuseStep 2192629 = 205559) (by norm_num)
theorem B16676117 : Blo 864565 16676117 := bbase (se 6 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 16676117 = 781693) (by norm_num)
theorem B2225461 : Blo 864565 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2192741 : Blo 864565 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B2192933 : Blo 864565 2192933 := bbase (se 4 (by rfl) ⟨205587, by rfl⟩ : syracuseStep 2192933 = 411175) (by norm_num)
theorem B2193277 : Blo 864565 2193277 := bbase (se 3 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 2193277 = 822479) (by norm_num)
theorem B4388741 : Blo 864565 4388741 := bbase (se 4 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 4388741 = 822889) (by norm_num)
theorem B2193389 : Blo 864565 2193389 := bbase (se 3 (by rfl) ⟨411260, by rfl⟩ : syracuseStep 2193389 = 822521) (by norm_num)
theorem B4454453 : Blo 864565 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B1112177 : Blo 864565 1112177 := bbase (se 2 (by rfl) ⟨417066, by rfl⟩ : syracuseStep 1112177 = 834133) (by norm_num)
theorem B1112197 : Blo 864565 1112197 := bbase (se 4 (by rfl) ⟨104268, by rfl⟩ : syracuseStep 1112197 = 208537) (by norm_num)
theorem B2193581 : Blo 864565 2193581 := bbase (se 3 (by rfl) ⟨411296, by rfl⟩ : syracuseStep 2193581 = 822593) (by norm_num)
theorem B1112249 : Blo 864565 1112249 := bbase (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) (by norm_num)
theorem B4159765 : Blo 864565 4159765 := bbase (se 6 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 4159765 = 194989) (by norm_num)
theorem B16644437 : Blo 864565 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B1603997 : Blo 864565 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B2193925 : Blo 864565 2193925 := bbase (se 4 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 2193925 = 411361) (by norm_num)
theorem B2194037 : Blo 864565 2194037 := bbase (se 5 (by rfl) ⟨102845, by rfl⟩ : syracuseStep 2194037 = 205691) (by norm_num)
theorem B1112833 : Blo 864565 1112833 := bbase (se 2 (by rfl) ⟨417312, by rfl⟩ : syracuseStep 1112833 = 834625) (by norm_num)
theorem B2194229 : Blo 864565 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B1407877 : Blo 864565 1407877 := bbase (se 4 (by rfl) ⟨131988, by rfl⟩ : syracuseStep 1407877 = 263977) (by norm_num)
theorem B916561 : Blo 864565 916561 := bbase (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) (by norm_num)
theorem B2194573 : Blo 864565 2194573 := bbase (se 3 (by rfl) ⟨411482, by rfl⟩ : syracuseStep 2194573 = 822965) (by norm_num)
theorem B4390037 : Blo 864565 4390037 := bbase (se 6 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 4390037 = 205783) (by norm_num)
theorem B2194685 : Blo 864565 2194685 := bbase (se 3 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 2194685 = 823007) (by norm_num)
theorem B3702181 : Blo 864565 3702181 := bbase (se 4 (by rfl) ⟨347079, by rfl⟩ : syracuseStep 3702181 = 694159) (by norm_num)
theorem B2194877 : Blo 864565 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B2195221 : Blo 864565 2195221 := bbase (se 6 (by rfl) ⟨51450, by rfl⟩ : syracuseStep 2195221 = 102901) (by norm_num)
theorem B2195333 : Blo 864565 2195333 := bbase (se 4 (by rfl) ⟨205812, by rfl⟩ : syracuseStep 2195333 = 411625) (by norm_num)
theorem B3702797 : Blo 864565 3702797 := bstep (se 3 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 3702797 = 1388549) B1388549
theorem B5013937 : Blo 864565 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B3506723 : Blo 864565 3506723 := bstep (se 1 (by rfl) ⟨2630042, by rfl⟩ : syracuseStep 3506723 = 5260085) B5260085
theorem B12485173 : Blo 864565 12485173 := bstep (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) B1170485
theorem B3506915 : Blo 864565 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B6259427 : Blo 864565 6259427 := bstep (se 1 (by rfl) ⟨4694570, by rfl⟩ : syracuseStep 6259427 = 9389141) B9389141
theorem B2196305 : Blo 864565 2196305 := bstep (se 2 (by rfl) ⟨823614, by rfl⟩ : syracuseStep 2196305 = 1647229) B1647229
theorem B15827825 : Blo 864565 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B2196355 : Blo 864565 2196355 := bstep (se 1 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 2196355 = 3294533) B3294533
theorem B2196497 : Blo 864565 2196497 := bstep (se 2 (by rfl) ⟨823686, by rfl⟩ : syracuseStep 2196497 = 1647373) B1647373
theorem B4392305 : Blo 864565 4392305 := bstep (se 2 (by rfl) ⟨1647114, by rfl⟩ : syracuseStep 4392305 = 3294229) B3294229
theorem B8881649 : Blo 864565 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B2917997 : Blo 864565 2917997 := bstep (se 3 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 2917997 = 1094249) B1094249
theorem B2918051 : Blo 864565 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B5539589 : Blo 864565 5539589 := bstep (se 4 (by rfl) ⟨519336, by rfl⟩ : syracuseStep 5539589 = 1038673) B1038673
theorem B8456035 : Blo 864565 8456035 := bstep (se 1 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 8456035 = 12684053) B12684053
theorem B2918321 : Blo 864565 2918321 := bstep (se 2 (by rfl) ⟨1094370, by rfl⟩ : syracuseStep 2918321 = 2188741) B2188741
theorem B2197489 : Blo 864565 2197489 := bstep (se 2 (by rfl) ⟨824058, by rfl⟩ : syracuseStep 2197489 = 1648117) B1648117
theorem B9373877 : Blo 864565 9373877 := bstep (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) B878801
theorem B2197763 : Blo 864565 2197763 := bstep (se 1 (by rfl) ⟨1648322, by rfl⟩ : syracuseStep 2197763 = 3296645) B3296645
theorem B2197955 : Blo 864565 2197955 := bstep (se 1 (by rfl) ⟨1648466, by rfl⟩ : syracuseStep 2197955 = 3296933) B3296933
theorem B2918861 : Blo 864565 2918861 := bstep (se 3 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 2918861 = 1094573) B1094573
theorem B3213809 : Blo 864565 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B2918915 : Blo 864565 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B11111053 : Blo 864565 11111053 := bstep (se 3 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 11111053 = 4166645) B4166645
theorem B16648901 : Blo 864565 16648901 := bstep (se 4 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 16648901 = 3121669) B3121669
theorem B2919185 : Blo 864565 2919185 := bstep (se 2 (by rfl) ⟨1094694, by rfl⟩ : syracuseStep 2919185 = 2189389) B2189389
theorem B3509027 : Blo 864565 3509027 := bstep (se 1 (by rfl) ⟨2631770, by rfl⟩ : syracuseStep 3509027 = 5263541) B5263541
theorem B4393763 : Blo 864565 4393763 := bstep (se 1 (by rfl) ⟨3295322, by rfl⟩ : syracuseStep 4393763 = 6590645) B6590645
theorem B3246961 : Blo 864565 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B10259341 : Blo 864565 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B4164493 : Blo 864565 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B1641617 : Blo 864565 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B2919725 : Blo 864565 2919725 := bstep (se 3 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 2919725 = 1094897) B1094897
theorem B2919779 : Blo 864565 2919779 := bstep (se 1 (by rfl) ⟨2189834, by rfl⟩ : syracuseStep 2919779 = 4379669) B4379669
theorem B7409009 : Blo 864565 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B12520817 : Blo 864565 12520817 := bstep (se 2 (by rfl) ⟨4695306, by rfl⟩ : syracuseStep 12520817 = 9390613) B9390613
theorem B4394573 : Blo 864565 4394573 := bstep (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) B1647965
theorem B2920049 : Blo 864565 2920049 := bstep (se 2 (by rfl) ⟨1095018, by rfl⟩ : syracuseStep 2920049 = 2190037) B2190037
theorem B3510029 : Blo 864565 3510029 := bstep (se 3 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 3510029 = 1316261) B1316261
theorem B11112389 : Blo 864565 11112389 := bstep (se 4 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 11112389 = 2083573) B2083573
theorem B3706829 : Blo 864565 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B1642513 : Blo 864565 1642513 := bstep (se 2 (by rfl) ⟨615942, by rfl⟩ : syracuseStep 1642513 = 1231885) B1231885
theorem B2920589 : Blo 864565 2920589 := bstep (se 3 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 2920589 = 1095221) B1095221
theorem B1642673 : Blo 864565 1642673 := bstep (se 2 (by rfl) ⟨616002, by rfl⟩ : syracuseStep 1642673 = 1232005) B1232005
theorem B2920643 : Blo 864565 2920643 := bstep (se 1 (by rfl) ⟨2190482, by rfl⟩ : syracuseStep 2920643 = 4380965) B4380965
theorem B3707171 : Blo 864565 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B1872227 : Blo 864565 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B1872323 : Blo 864565 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B2920913 : Blo 864565 2920913 := bstep (se 2 (by rfl) ⟨1095342, by rfl⟩ : syracuseStep 2920913 = 2190685) B2190685
theorem B1643075 : Blo 864565 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B1872625 : Blo 864565 1872625 := bstep (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) B1404469
theorem B3707633 : Blo 864565 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B1479425 : Blo 864565 1479425 := bstep (se 2 (by rfl) ⟨554784, by rfl⟩ : syracuseStep 1479425 = 1109569) B1109569
theorem B2921453 : Blo 864565 2921453 := bstep (se 3 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 2921453 = 1095545) B1095545
theorem B2921507 : Blo 864565 2921507 := bstep (se 1 (by rfl) ⟨2191130, by rfl⟩ : syracuseStep 2921507 = 4382261) B4382261
theorem B1217587 : Blo 864565 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B1315921 : Blo 864565 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1250483 : Blo 864565 1250483 := bstep (se 1 (by rfl) ⟨937862, by rfl⟩ : syracuseStep 1250483 = 1875725) B1875725
theorem B2921777 : Blo 864565 2921777 := bstep (se 2 (by rfl) ⟨1095666, by rfl⟩ : syracuseStep 2921777 = 2191333) B2191333
theorem B1643971 : Blo 864565 1643971 := bstep (se 1 (by rfl) ⟨1232978, by rfl⟩ : syracuseStep 1643971 = 2465957) B2465957
theorem B2463281 : Blo 864565 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1480241 : Blo 864565 1480241 := bstep (se 2 (by rfl) ⟨555090, by rfl⟩ : syracuseStep 1480241 = 1110181) B1110181
theorem B1644131 : Blo 864565 1644131 := bstep (se 1 (by rfl) ⟨1233098, by rfl⟩ : syracuseStep 1644131 = 2466197) B2466197
theorem B2463473 : Blo 864565 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B4888325 : Blo 864565 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B22484789 : Blo 864565 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B2922317 : Blo 864565 2922317 := bstep (se 3 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 2922317 = 1095869) B1095869
theorem B923491 : Blo 864565 923491 := bstep (se 1 (by rfl) ⟨692618, by rfl⟩ : syracuseStep 923491 = 1385237) B1385237
theorem B2922371 : Blo 864565 2922371 := bstep (se 1 (by rfl) ⟨2191778, by rfl⟩ : syracuseStep 2922371 = 4383557) B4383557
theorem B2857027 : Blo 864565 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B2922641 : Blo 864565 2922641 := bstep (se 2 (by rfl) ⟨1095990, by rfl⟩ : syracuseStep 2922641 = 2191981) B2191981
theorem B3512483 : Blo 864565 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B5544227 : Blo 864565 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B1481041 : Blo 864565 1481041 := bstep (se 2 (by rfl) ⟨555390, by rfl⟩ : syracuseStep 1481041 = 1110781) B1110781
theorem B1317235 : Blo 864565 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1645201 : Blo 864565 1645201 := bstep (se 2 (by rfl) ⟨616950, by rfl⟩ : syracuseStep 1645201 = 1233901) B1233901
theorem B2923181 : Blo 864565 2923181 := bstep (se 3 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 2923181 = 1096193) B1096193
theorem B2464465 : Blo 864565 2464465 := bstep (se 2 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 2464465 = 1848349) B1848349
theorem B2923235 : Blo 864565 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B3283811 : Blo 864565 3283811 := bstep (se 1 (by rfl) ⟨2462858, by rfl⟩ : syracuseStep 3283811 = 4925717) B4925717
theorem B22518641 : Blo 864565 22518641 := bstep (se 2 (by rfl) ⟨8444490, by rfl⟩ : syracuseStep 22518641 = 16888981) B16888981
theorem B6331277 : Blo 864565 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B2464739 : Blo 864565 2464739 := bstep (se 1 (by rfl) ⟨1848554, by rfl⟩ : syracuseStep 2464739 = 3697109) B3697109
theorem B2923505 : Blo 864565 2923505 := bstep (se 2 (by rfl) ⟨1096314, by rfl⟩ : syracuseStep 2923505 = 2192629) B2192629
theorem B1973297 : Blo 864565 1973297 := bstep (se 2 (by rfl) ⟨739986, by rfl⟩ : syracuseStep 1973297 = 1479973) B1479973
theorem B2464931 : Blo 864565 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B1973443 : Blo 864565 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B1318403 : Blo 864565 1318403 := bstep (se 1 (by rfl) ⟨988802, by rfl⟩ : syracuseStep 1318403 = 1977605) B1977605
theorem B2924045 : Blo 864565 2924045 := bstep (se 3 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 2924045 = 1096517) B1096517
theorem B2924099 : Blo 864565 2924099 := bstep (se 1 (by rfl) ⟨2193074, by rfl⟩ : syracuseStep 2924099 = 4386149) B4386149
theorem B3513955 : Blo 864565 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1646257 : Blo 864565 1646257 := bstep (se 2 (by rfl) ⟨617346, by rfl⟩ : syracuseStep 1646257 = 1234693) B1234693
theorem B3284813 : Blo 864565 3284813 := bstep (se 3 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 3284813 = 1231805) B1231805
theorem B2924369 : Blo 864565 2924369 := bstep (se 2 (by rfl) ⟨1096638, by rfl⟩ : syracuseStep 2924369 = 2193277) B2193277
theorem B15179633 : Blo 864565 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B2465741 : Blo 864565 2465741 := bstep (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) B924653
theorem B4694051 : Blo 864565 4694051 := bstep (se 1 (by rfl) ⟨3520538, by rfl⟩ : syracuseStep 4694051 = 7041077) B7041077
theorem B1646659 : Blo 864565 1646659 := bstep (se 1 (by rfl) ⟨1234994, by rfl⟩ : syracuseStep 1646659 = 2469989) B2469989
theorem B1646705 : Blo 864565 1646705 := bstep (se 2 (by rfl) ⟨617514, by rfl⟩ : syracuseStep 1646705 = 1235029) B1235029
theorem B2465923 : Blo 864565 2465923 := bstep (se 1 (by rfl) ⟨1849442, by rfl⟩ : syracuseStep 2465923 = 3698885) B3698885
theorem B1482929 : Blo 864565 1482929 := bstep (se 2 (by rfl) ⟨556098, by rfl⟩ : syracuseStep 1482929 = 1112197) B1112197
theorem B2924909 : Blo 864565 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B5546353 : Blo 864565 5546353 := bstep (se 2 (by rfl) ⟨2079882, by rfl⟩ : syracuseStep 5546353 = 4159765) B4159765
theorem B1646993 : Blo 864565 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B2924963 : Blo 864565 2924963 := bstep (se 1 (by rfl) ⟨2193722, by rfl⟩ : syracuseStep 2924963 = 4387445) B4387445
theorem B3121699 : Blo 864565 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B2466413 : Blo 864565 2466413 := bstep (se 3 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 2466413 = 924905) B924905
theorem B2925233 : Blo 864565 2925233 := bstep (se 2 (by rfl) ⟨1096962, by rfl⟩ : syracuseStep 2925233 = 2193925) B2193925
theorem B11838149 : Blo 864565 11838149 := bstep (se 4 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 11838149 = 2219653) B2219653
theorem B4924259 : Blo 864565 4924259 := bstep (se 1 (by rfl) ⟨3693194, by rfl⟩ : syracuseStep 4924259 = 7386389) B7386389
theorem B11117411 : Blo 864565 11117411 := bstep (se 1 (by rfl) ⟨8338058, by rfl⟩ : syracuseStep 11117411 = 16676117) B16676117
theorem B4694897 : Blo 864565 4694897 := bstep (se 2 (by rfl) ⟨1760586, by rfl⟩ : syracuseStep 4694897 = 3521173) B3521173
theorem B1483777 : Blo 864565 1483777 := bstep (se 2 (by rfl) ⟨556416, by rfl⟩ : syracuseStep 1483777 = 1112833) B1112833
theorem B1319953 : Blo 864565 1319953 := bstep (se 2 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 1319953 = 989965) B989965
theorem B1647715 : Blo 864565 1647715 := bstep (se 1 (by rfl) ⟨1235786, by rfl⟩ : syracuseStep 1647715 = 2471573) B2471573
theorem B2925773 : Blo 864565 2925773 := bstep (se 3 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 2925773 = 1097165) B1097165
theorem B4695245 : Blo 864565 4695245 := bstep (se 3 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 4695245 = 1760717) B1760717
theorem B2925827 : Blo 864565 2925827 := bstep (se 1 (by rfl) ⟨2194370, by rfl⟩ : syracuseStep 2925827 = 4388741) B4388741
theorem B927011 : Blo 864565 927011 := bstep (se 1 (by rfl) ⟨695258, by rfl⟩ : syracuseStep 927011 = 1390517) B1390517
theorem B2926097 : Blo 864565 2926097 := bstep (se 2 (by rfl) ⟨1097286, by rfl⟩ : syracuseStep 2926097 = 2194573) B2194573
theorem B1648163 : Blo 864565 1648163 := bstep (se 1 (by rfl) ⟨1236122, by rfl⟩ : syracuseStep 1648163 = 2472245) B2472245
theorem B1976035 : Blo 864565 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B2467597 : Blo 864565 2467597 := bstep (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) B925349
theorem B4007693 : Blo 864565 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B1648451 : Blo 864565 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B1386371 : Blo 864565 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B14788493 : Blo 864565 14788493 := bstep (se 3 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 14788493 = 5545685) B5545685
theorem B3286925 : Blo 864565 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B1386499 : Blo 864565 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B2926637 : Blo 864565 2926637 := bstep (se 3 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 2926637 = 1097489) B1097489
theorem B2926691 : Blo 864565 2926691 := bstep (se 1 (by rfl) ⟨2195018, by rfl⟩ : syracuseStep 2926691 = 4390037) B4390037
theorem B2926961 : Blo 864565 2926961 := bstep (se 2 (by rfl) ⟨1097610, by rfl⟩ : syracuseStep 2926961 = 2195221) B2195221
theorem B1386883 : Blo 864565 1386883 := bstep (se 1 (by rfl) ⟨1040162, by rfl⟩ : syracuseStep 1386883 = 2080325) B2080325
theorem B1387139 : Blo 864565 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B2337425 : Blo 864565 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B3287729 : Blo 864565 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B2468657 : Blo 864565 2468657 := bstep (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) B1851493
theorem B1878833 : Blo 864565 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B2927501 : Blo 864565 2927501 := bstep (se 3 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 2927501 = 1097813) B1097813
theorem B2927555 : Blo 864565 2927555 := bstep (se 1 (by rfl) ⟨2195666, by rfl⟩ : syracuseStep 2927555 = 4391333) B4391333
theorem B2960333 : Blo 864565 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B1387601 : Blo 864565 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B6237283 : Blo 864565 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B1387697 : Blo 864565 1387697 := bstep (se 2 (by rfl) ⟨520386, by rfl⟩ : syracuseStep 1387697 = 1040773) B1040773
theorem B1387729 : Blo 864565 1387729 := bstep (se 2 (by rfl) ⟨520398, by rfl⟩ : syracuseStep 1387729 = 1040797) B1040797
theorem B2927825 : Blo 864565 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B3386609 : Blo 864565 3386609 := bstep (se 2 (by rfl) ⟨1269978, by rfl⟩ : syracuseStep 3386609 = 2539957) B2539957
theorem B3288397 : Blo 864565 3288397 := bstep (se 3 (by rfl) ⟨616574, by rfl⟩ : syracuseStep 3288397 = 1233149) B1233149
theorem B2469329 : Blo 864565 2469329 := bstep (se 2 (by rfl) ⟨925998, by rfl⟩ : syracuseStep 2469329 = 1851997) B1851997
theorem B3124813 : Blo 864565 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B22163057 : Blo 864565 22163057 := bstep (se 2 (by rfl) ⟨8311146, by rfl⟩ : syracuseStep 22163057 = 16622293) B16622293
theorem B2928365 : Blo 864565 2928365 := bstep (se 3 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 2928365 = 1098137) B1098137
theorem B2961137 : Blo 864565 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B2928419 : Blo 864565 2928419 := bstep (se 1 (by rfl) ⟨2196314, by rfl⟩ : syracuseStep 2928419 = 4392629) B4392629
theorem B1945457 : Blo 864565 1945457 := bstep (se 2 (by rfl) ⟨729546, by rfl⟩ : syracuseStep 1945457 = 1459093) B1459093
theorem B1945475 : Blo 864565 1945475 := bstep (se 1 (by rfl) ⟨1459106, by rfl⟩ : syracuseStep 1945475 = 2918213) B2918213
theorem B6565859 : Blo 864565 6565859 := bstep (se 1 (by rfl) ⟨4924394, by rfl⟩ : syracuseStep 6565859 = 9848789) B9848789
theorem B1847281 : Blo 864565 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B4927493 : Blo 864565 4927493 := bstep (se 4 (by rfl) ⟨461952, by rfl⟩ : syracuseStep 4927493 = 923905) B923905
theorem B2928689 : Blo 864565 2928689 := bstep (se 2 (by rfl) ⟨1098258, by rfl⟩ : syracuseStep 2928689 = 2196517) B2196517
theorem B3289187 : Blo 864565 3289187 := bstep (se 1 (by rfl) ⟨2466890, by rfl⟩ : syracuseStep 3289187 = 4933781) B4933781
theorem B1978499 : Blo 864565 1978499 := bstep (se 1 (by rfl) ⟨1483874, by rfl⟩ : syracuseStep 1978499 = 2967749) B2967749
theorem B1945745 : Blo 864565 1945745 := bstep (se 2 (by rfl) ⟨729654, by rfl⟩ : syracuseStep 1945745 = 1459309) B1459309
theorem B1945763 : Blo 864565 1945763 := bstep (se 1 (by rfl) ⟨1459322, by rfl⟩ : syracuseStep 1945763 = 2918645) B2918645
theorem B2470115 : Blo 864565 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B1847537 : Blo 864565 1847537 := bstep (se 2 (by rfl) ⟨692826, by rfl⟩ : syracuseStep 1847537 = 1385653) B1385653
theorem B864579 : Blo 864565 864579 := bstep (se 1 (by rfl) ⟨648434, by rfl⟩ : syracuseStep 864579 = 1296869) B1296869
theorem B864595 : Blo 864565 864595 := bstep (se 1 (by rfl) ⟨648446, by rfl⟩ : syracuseStep 864595 = 1296893) B1296893
theorem B864611 : Blo 864565 864611 := bstep (se 1 (by rfl) ⟨648458, by rfl⟩ : syracuseStep 864611 = 1296917) B1296917
theorem B864627 : Blo 864565 864627 := bstep (se 1 (by rfl) ⟨648470, by rfl⟩ : syracuseStep 864627 = 1296941) B1296941
theorem B864643 : Blo 864565 864643 := bstep (se 1 (by rfl) ⟨648482, by rfl⟩ : syracuseStep 864643 = 1296965) B1296965
theorem B2961809 : Blo 864565 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B864659 : Blo 864565 864659 := bstep (se 1 (by rfl) ⟨648494, by rfl⟩ : syracuseStep 864659 = 1296989) B1296989
theorem B864675 : Blo 864565 864675 := bstep (se 1 (by rfl) ⟨648506, by rfl⟩ : syracuseStep 864675 = 1297013) B1297013
theorem B1946033 : Blo 864565 1946033 := bstep (se 2 (by rfl) ⟨729762, by rfl⟩ : syracuseStep 1946033 = 1459525) B1459525
theorem B864691 : Blo 864565 864691 := bstep (se 1 (by rfl) ⟨648518, by rfl⟩ : syracuseStep 864691 = 1297037) B1297037
theorem B864707 : Blo 864565 864707 := bstep (se 1 (by rfl) ⟨648530, by rfl⟩ : syracuseStep 864707 = 1297061) B1297061
theorem B1946051 : Blo 864565 1946051 := bstep (se 1 (by rfl) ⟨1459538, by rfl⟩ : syracuseStep 1946051 = 2919077) B2919077
theorem B4927949 : Blo 864565 4927949 := bstep (se 3 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 4927949 = 1847981) B1847981
theorem B864723 : Blo 864565 864723 := bstep (se 1 (by rfl) ⟨648542, by rfl⟩ : syracuseStep 864723 = 1297085) B1297085
theorem B864739 : Blo 864565 864739 := bstep (se 1 (by rfl) ⟨648554, by rfl⟩ : syracuseStep 864739 = 1297109) B1297109
theorem B864755 : Blo 864565 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B864771 : Blo 864565 864771 := bstep (se 1 (by rfl) ⟨648578, by rfl⟩ : syracuseStep 864771 = 1297157) B1297157
theorem B2503181 : Blo 864565 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B7909901 : Blo 864565 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B864787 : Blo 864565 864787 := bstep (se 1 (by rfl) ⟨648590, by rfl⟩ : syracuseStep 864787 = 1297181) B1297181
theorem B864803 : Blo 864565 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B2470445 : Blo 864565 2470445 := bstep (se 3 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 2470445 = 926417) B926417
theorem B864819 : Blo 864565 864819 := bstep (se 1 (by rfl) ⟨648614, by rfl⟩ : syracuseStep 864819 = 1297229) B1297229
theorem B9351733 : Blo 864565 9351733 := bstep (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) B876725
theorem B864835 : Blo 864565 864835 := bstep (se 1 (by rfl) ⟨648626, by rfl⟩ : syracuseStep 864835 = 1297253) B1297253
theorem B2929229 : Blo 864565 2929229 := bstep (se 3 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 2929229 = 1098461) B1098461
theorem B864851 : Blo 864565 864851 := bstep (se 1 (by rfl) ⟨648638, by rfl⟩ : syracuseStep 864851 = 1297277) B1297277
theorem B864867 : Blo 864565 864867 := bstep (se 1 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 864867 = 1297301) B1297301
theorem B2470513 : Blo 864565 2470513 := bstep (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) B1852885
theorem B864883 : Blo 864565 864883 := bstep (se 1 (by rfl) ⟨648662, by rfl⟩ : syracuseStep 864883 = 1297325) B1297325
theorem B864899 : Blo 864565 864899 := bstep (se 1 (by rfl) ⟨648674, by rfl⟩ : syracuseStep 864899 = 1297349) B1297349
theorem B2929283 : Blo 864565 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B864915 : Blo 864565 864915 := bstep (se 1 (by rfl) ⟨648686, by rfl⟩ : syracuseStep 864915 = 1297373) B1297373
theorem B864931 : Blo 864565 864931 := bstep (se 1 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 864931 = 1297397) B1297397
theorem B864947 : Blo 864565 864947 := bstep (se 1 (by rfl) ⟨648710, by rfl⟩ : syracuseStep 864947 = 1297421) B1297421
theorem B864963 : Blo 864565 864963 := bstep (se 1 (by rfl) ⟨648722, by rfl⟩ : syracuseStep 864963 = 1297445) B1297445
theorem B1946321 : Blo 864565 1946321 := bstep (se 2 (by rfl) ⟨729870, by rfl⟩ : syracuseStep 1946321 = 1459741) B1459741
theorem B864979 : Blo 864565 864979 := bstep (se 1 (by rfl) ⟨648734, by rfl⟩ : syracuseStep 864979 = 1297469) B1297469
theorem B864995 : Blo 864565 864995 := bstep (se 1 (by rfl) ⟨648746, by rfl⟩ : syracuseStep 864995 = 1297493) B1297493
theorem B1946339 : Blo 864565 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B3289841 : Blo 864565 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B865011 : Blo 864565 865011 := bstep (se 1 (by rfl) ⟨648758, by rfl⟩ : syracuseStep 865011 = 1297517) B1297517
theorem B865027 : Blo 864565 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B865043 : Blo 864565 865043 := bstep (se 1 (by rfl) ⟨648782, by rfl⟩ : syracuseStep 865043 = 1297565) B1297565
theorem B865059 : Blo 864565 865059 := bstep (se 1 (by rfl) ⟨648794, by rfl⟩ : syracuseStep 865059 = 1297589) B1297589
theorem B865075 : Blo 864565 865075 := bstep (se 1 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 865075 = 1297613) B1297613
theorem B1094467 : Blo 864565 1094467 := bstep (se 1 (by rfl) ⟨820850, by rfl⟩ : syracuseStep 1094467 = 1641701) B1641701
theorem B865091 : Blo 864565 865091 := bstep (se 1 (by rfl) ⟨648818, by rfl⟩ : syracuseStep 865091 = 1297637) B1297637
theorem B865107 : Blo 864565 865107 := bstep (se 1 (by rfl) ⟨648830, by rfl⟩ : syracuseStep 865107 = 1297661) B1297661
theorem B1389395 : Blo 864565 1389395 := bstep (se 1 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 1389395 = 2084093) B2084093
theorem B865123 : Blo 864565 865123 := bstep (se 1 (by rfl) ⟨648842, by rfl⟩ : syracuseStep 865123 = 1297685) B1297685
theorem B865139 : Blo 864565 865139 := bstep (se 1 (by rfl) ⟨648854, by rfl⟩ : syracuseStep 865139 = 1297709) B1297709
theorem B865155 : Blo 864565 865155 := bstep (se 1 (by rfl) ⟨648866, by rfl⟩ : syracuseStep 865155 = 1297733) B1297733
theorem B2470787 : Blo 864565 2470787 := bstep (se 1 (by rfl) ⟨1853090, by rfl⟩ : syracuseStep 2470787 = 3706181) B3706181
theorem B2929553 : Blo 864565 2929553 := bstep (se 2 (by rfl) ⟨1098582, by rfl⟩ : syracuseStep 2929553 = 2197165) B2197165
theorem B865171 : Blo 864565 865171 := bstep (se 1 (by rfl) ⟨648878, by rfl⟩ : syracuseStep 865171 = 1297757) B1297757
theorem B1094563 : Blo 864565 1094563 := bstep (se 1 (by rfl) ⟨820922, by rfl⟩ : syracuseStep 1094563 = 1641845) B1641845
theorem B865187 : Blo 864565 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B865203 : Blo 864565 865203 := bstep (se 1 (by rfl) ⟨648902, by rfl⟩ : syracuseStep 865203 = 1297805) B1297805
theorem B865219 : Blo 864565 865219 := bstep (se 1 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 865219 = 1297829) B1297829
theorem B865235 : Blo 864565 865235 := bstep (se 1 (by rfl) ⟨648926, by rfl⟩ : syracuseStep 865235 = 1297853) B1297853
theorem B865251 : Blo 864565 865251 := bstep (se 1 (by rfl) ⟨648938, by rfl⟩ : syracuseStep 865251 = 1297877) B1297877
theorem B1946609 : Blo 864565 1946609 := bstep (se 2 (by rfl) ⟨729978, by rfl⟩ : syracuseStep 1946609 = 1459957) B1459957
theorem B865267 : Blo 864565 865267 := bstep (se 1 (by rfl) ⟨648950, by rfl⟩ : syracuseStep 865267 = 1297901) B1297901
theorem B1946627 : Blo 864565 1946627 := bstep (se 1 (by rfl) ⟨1459970, by rfl⟩ : syracuseStep 1946627 = 2919941) B2919941
theorem B865283 : Blo 864565 865283 := bstep (se 1 (by rfl) ⟨648962, by rfl⟩ : syracuseStep 865283 = 1297925) B1297925
theorem B865299 : Blo 864565 865299 := bstep (se 1 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 865299 = 1297949) B1297949
theorem B865315 : Blo 864565 865315 := bstep (se 1 (by rfl) ⟨648986, by rfl⟩ : syracuseStep 865315 = 1297973) B1297973
theorem B865331 : Blo 864565 865331 := bstep (se 1 (by rfl) ⟨648998, by rfl⟩ : syracuseStep 865331 = 1297997) B1297997
theorem B865347 : Blo 864565 865347 := bstep (se 1 (by rfl) ⟨649010, by rfl⟩ : syracuseStep 865347 = 1298021) B1298021
theorem B865363 : Blo 864565 865363 := bstep (se 1 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 865363 = 1298045) B1298045
theorem B865379 : Blo 864565 865379 := bstep (se 1 (by rfl) ⟨649034, by rfl⟩ : syracuseStep 865379 = 1298069) B1298069
theorem B865395 : Blo 864565 865395 := bstep (se 1 (by rfl) ⟨649046, by rfl⟩ : syracuseStep 865395 = 1298093) B1298093
theorem B865411 : Blo 864565 865411 := bstep (se 1 (by rfl) ⟨649058, by rfl⟩ : syracuseStep 865411 = 1298117) B1298117
theorem B865427 : Blo 864565 865427 := bstep (se 1 (by rfl) ⟨649070, by rfl⟩ : syracuseStep 865427 = 1298141) B1298141
theorem B865443 : Blo 864565 865443 := bstep (se 1 (by rfl) ⟨649082, by rfl⟩ : syracuseStep 865443 = 1298165) B1298165
theorem B865459 : Blo 864565 865459 := bstep (se 1 (by rfl) ⟨649094, by rfl⟩ : syracuseStep 865459 = 1298189) B1298189
theorem B865475 : Blo 864565 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B865491 : Blo 864565 865491 := bstep (se 1 (by rfl) ⟨649118, by rfl⟩ : syracuseStep 865491 = 1298237) B1298237
theorem B865507 : Blo 864565 865507 := bstep (se 1 (by rfl) ⟨649130, by rfl⟩ : syracuseStep 865507 = 1298261) B1298261
theorem B865523 : Blo 864565 865523 := bstep (se 1 (by rfl) ⟨649142, by rfl⟩ : syracuseStep 865523 = 1298285) B1298285
theorem B865539 : Blo 864565 865539 := bstep (se 1 (by rfl) ⟨649154, by rfl⟩ : syracuseStep 865539 = 1298309) B1298309
theorem B1946897 : Blo 864565 1946897 := bstep (se 2 (by rfl) ⟨730086, by rfl⟩ : syracuseStep 1946897 = 1460173) B1460173
theorem B865555 : Blo 864565 865555 := bstep (se 1 (by rfl) ⟨649166, by rfl⟩ : syracuseStep 865555 = 1298333) B1298333
theorem B1946915 : Blo 864565 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B865571 : Blo 864565 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B865587 : Blo 864565 865587 := bstep (se 1 (by rfl) ⟨649190, by rfl⟩ : syracuseStep 865587 = 1298381) B1298381
theorem B865603 : Blo 864565 865603 := bstep (se 1 (by rfl) ⟨649202, by rfl⟩ : syracuseStep 865603 = 1298405) B1298405
theorem B865619 : Blo 864565 865619 := bstep (se 1 (by rfl) ⟨649214, by rfl⟩ : syracuseStep 865619 = 1298429) B1298429
theorem B1389907 : Blo 864565 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B865635 : Blo 864565 865635 := bstep (se 1 (by rfl) ⟨649226, by rfl⟩ : syracuseStep 865635 = 1298453) B1298453
theorem B8336753 : Blo 864565 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B865651 : Blo 864565 865651 := bstep (se 1 (by rfl) ⟨649238, by rfl⟩ : syracuseStep 865651 = 1298477) B1298477
theorem B1389953 : Blo 864565 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B865667 : Blo 864565 865667 := bstep (se 1 (by rfl) ⟨649250, by rfl⟩ : syracuseStep 865667 = 1298501) B1298501
theorem B2635139 : Blo 864565 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B1095059 : Blo 864565 1095059 := bstep (se 1 (by rfl) ⟨821294, by rfl⟩ : syracuseStep 1095059 = 1642589) B1642589
theorem B865683 : Blo 864565 865683 := bstep (se 1 (by rfl) ⟨649262, by rfl⟩ : syracuseStep 865683 = 1298525) B1298525
theorem B865699 : Blo 864565 865699 := bstep (se 1 (by rfl) ⟨649274, by rfl⟩ : syracuseStep 865699 = 1298549) B1298549
theorem B2930093 : Blo 864565 2930093 := bstep (se 3 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 2930093 = 1098785) B1098785
theorem B865715 : Blo 864565 865715 := bstep (se 1 (by rfl) ⟨649286, by rfl⟩ : syracuseStep 865715 = 1298573) B1298573
theorem B865731 : Blo 864565 865731 := bstep (se 1 (by rfl) ⟨649298, by rfl⟩ : syracuseStep 865731 = 1298597) B1298597
theorem B9024965 : Blo 864565 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B865747 : Blo 864565 865747 := bstep (se 1 (by rfl) ⟨649310, by rfl⟩ : syracuseStep 865747 = 1298621) B1298621
theorem B865763 : Blo 864565 865763 := bstep (se 1 (by rfl) ⟨649322, by rfl⟩ : syracuseStep 865763 = 1298645) B1298645
theorem B2930147 : Blo 864565 2930147 := bstep (se 1 (by rfl) ⟨2197610, by rfl⟩ : syracuseStep 2930147 = 4395221) B4395221
theorem B865779 : Blo 864565 865779 := bstep (se 1 (by rfl) ⟨649334, by rfl⟩ : syracuseStep 865779 = 1298669) B1298669
theorem B1848835 : Blo 864565 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B865795 : Blo 864565 865795 := bstep (se 1 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 865795 = 1298693) B1298693
theorem B865811 : Blo 864565 865811 := bstep (se 1 (by rfl) ⟨649358, by rfl⟩ : syracuseStep 865811 = 1298717) B1298717
theorem B865827 : Blo 864565 865827 := bstep (se 1 (by rfl) ⟨649370, by rfl⟩ : syracuseStep 865827 = 1298741) B1298741
theorem B1947185 : Blo 864565 1947185 := bstep (se 2 (by rfl) ⟨730194, by rfl⟩ : syracuseStep 1947185 = 1460389) B1460389
theorem B865843 : Blo 864565 865843 := bstep (se 1 (by rfl) ⟨649382, by rfl⟩ : syracuseStep 865843 = 1298765) B1298765
theorem B1947203 : Blo 864565 1947203 := bstep (se 1 (by rfl) ⟨1460402, by rfl⟩ : syracuseStep 1947203 = 2920805) B2920805
theorem B865859 : Blo 864565 865859 := bstep (se 1 (by rfl) ⟨649394, by rfl⟩ : syracuseStep 865859 = 1298789) B1298789
theorem B5551685 : Blo 864565 5551685 := bstep (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) B1040941
theorem B865875 : Blo 864565 865875 := bstep (se 1 (by rfl) ⟨649406, by rfl⟩ : syracuseStep 865875 = 1298813) B1298813
theorem B865891 : Blo 864565 865891 := bstep (se 1 (by rfl) ⟨649418, by rfl⟩ : syracuseStep 865891 = 1298837) B1298837
theorem B865907 : Blo 864565 865907 := bstep (se 1 (by rfl) ⟨649430, by rfl⟩ : syracuseStep 865907 = 1298861) B1298861
theorem B865923 : Blo 864565 865923 := bstep (se 1 (by rfl) ⟨649442, by rfl⟩ : syracuseStep 865923 = 1298885) B1298885
theorem B865939 : Blo 864565 865939 := bstep (se 1 (by rfl) ⟨649454, by rfl⟩ : syracuseStep 865939 = 1298909) B1298909
theorem B865955 : Blo 864565 865955 := bstep (se 1 (by rfl) ⟨649466, by rfl⟩ : syracuseStep 865955 = 1298933) B1298933
theorem B865971 : Blo 864565 865971 := bstep (se 1 (by rfl) ⟨649478, by rfl⟩ : syracuseStep 865971 = 1298957) B1298957
theorem B865987 : Blo 864565 865987 := bstep (se 1 (by rfl) ⟨649490, by rfl⟩ : syracuseStep 865987 = 1298981) B1298981
theorem B2471629 : Blo 864565 2471629 := bstep (se 3 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 2471629 = 926861) B926861
theorem B866003 : Blo 864565 866003 := bstep (se 1 (by rfl) ⟨649502, by rfl⟩ : syracuseStep 866003 = 1299005) B1299005
theorem B866019 : Blo 864565 866019 := bstep (se 1 (by rfl) ⟨649514, by rfl⟩ : syracuseStep 866019 = 1299029) B1299029
theorem B2930417 : Blo 864565 2930417 := bstep (se 2 (by rfl) ⟨1098906, by rfl⟩ : syracuseStep 2930417 = 2197813) B2197813
theorem B866035 : Blo 864565 866035 := bstep (se 1 (by rfl) ⟨649526, by rfl⟩ : syracuseStep 866035 = 1299053) B1299053
theorem B866051 : Blo 864565 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B866067 : Blo 864565 866067 := bstep (se 1 (by rfl) ⟨649550, by rfl⟩ : syracuseStep 866067 = 1299101) B1299101
theorem B866083 : Blo 864565 866083 := bstep (se 1 (by rfl) ⟨649562, by rfl⟩ : syracuseStep 866083 = 1299125) B1299125
theorem B866099 : Blo 864565 866099 := bstep (se 1 (by rfl) ⟨649574, by rfl⟩ : syracuseStep 866099 = 1299149) B1299149
theorem B866115 : Blo 864565 866115 := bstep (se 1 (by rfl) ⟨649586, by rfl⟩ : syracuseStep 866115 = 1299173) B1299173
theorem B1947473 : Blo 864565 1947473 := bstep (se 2 (by rfl) ⟨730302, by rfl⟩ : syracuseStep 1947473 = 1460605) B1460605
theorem B1849169 : Blo 864565 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B866131 : Blo 864565 866131 := bstep (se 1 (by rfl) ⟨649598, by rfl⟩ : syracuseStep 866131 = 1299197) B1299197
theorem B1947491 : Blo 864565 1947491 := bstep (se 1 (by rfl) ⟨1460618, by rfl⟩ : syracuseStep 1947491 = 2921237) B2921237
theorem B866147 : Blo 864565 866147 := bstep (se 1 (by rfl) ⟨649610, by rfl⟩ : syracuseStep 866147 = 1299221) B1299221
theorem B2471789 : Blo 864565 2471789 := bstep (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) B926921
theorem B866163 : Blo 864565 866163 := bstep (se 1 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 866163 = 1299245) B1299245
theorem B866179 : Blo 864565 866179 := bstep (se 1 (by rfl) ⟨649634, by rfl⟩ : syracuseStep 866179 = 1299269) B1299269
theorem B866195 : Blo 864565 866195 := bstep (se 1 (by rfl) ⟨649646, by rfl⟩ : syracuseStep 866195 = 1299293) B1299293
theorem B866211 : Blo 864565 866211 := bstep (se 1 (by rfl) ⟨649658, by rfl⟩ : syracuseStep 866211 = 1299317) B1299317
theorem B866227 : Blo 864565 866227 := bstep (se 1 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 866227 = 1299341) B1299341
theorem B866243 : Blo 864565 866243 := bstep (se 1 (by rfl) ⟨649682, by rfl⟩ : syracuseStep 866243 = 1299365) B1299365
theorem B866259 : Blo 864565 866259 := bstep (se 1 (by rfl) ⟨649694, by rfl⟩ : syracuseStep 866259 = 1299389) B1299389
theorem B866275 : Blo 864565 866275 := bstep (se 1 (by rfl) ⟨649706, by rfl⟩ : syracuseStep 866275 = 1299413) B1299413
theorem B866291 : Blo 864565 866291 := bstep (se 1 (by rfl) ⟨649718, by rfl⟩ : syracuseStep 866291 = 1299437) B1299437
theorem B866307 : Blo 864565 866307 := bstep (se 1 (by rfl) ⟨649730, by rfl⟩ : syracuseStep 866307 = 1299461) B1299461
theorem B866323 : Blo 864565 866323 := bstep (se 1 (by rfl) ⟨649742, by rfl⟩ : syracuseStep 866323 = 1299485) B1299485
theorem B1390625 : Blo 864565 1390625 := bstep (se 2 (by rfl) ⟨521484, by rfl⟩ : syracuseStep 1390625 = 1042969) B1042969
theorem B866339 : Blo 864565 866339 := bstep (se 1 (by rfl) ⟨649754, by rfl⟩ : syracuseStep 866339 = 1299509) B1299509
theorem B2471971 : Blo 864565 2471971 := bstep (se 1 (by rfl) ⟨1853978, by rfl⟩ : syracuseStep 2471971 = 3707957) B3707957
theorem B2504753 : Blo 864565 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B866355 : Blo 864565 866355 := bstep (se 1 (by rfl) ⟨649766, by rfl⟩ : syracuseStep 866355 = 1299533) B1299533
theorem B866371 : Blo 864565 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B1095763 : Blo 864565 1095763 := bstep (se 1 (by rfl) ⟨821822, by rfl⟩ : syracuseStep 1095763 = 1643645) B1643645
theorem B866387 : Blo 864565 866387 := bstep (se 1 (by rfl) ⟨649790, by rfl⟩ : syracuseStep 866387 = 1299581) B1299581
theorem B866403 : Blo 864565 866403 := bstep (se 1 (by rfl) ⟨649802, by rfl⟩ : syracuseStep 866403 = 1299605) B1299605
theorem B1947761 : Blo 864565 1947761 := bstep (se 2 (by rfl) ⟨730410, by rfl⟩ : syracuseStep 1947761 = 1460821) B1460821
theorem B866419 : Blo 864565 866419 := bstep (se 1 (by rfl) ⟨649814, by rfl⟩ : syracuseStep 866419 = 1299629) B1299629
theorem B1947779 : Blo 864565 1947779 := bstep (se 1 (by rfl) ⟨1460834, by rfl⟩ : syracuseStep 1947779 = 2921669) B2921669
theorem B866435 : Blo 864565 866435 := bstep (se 1 (by rfl) ⟨649826, by rfl⟩ : syracuseStep 866435 = 1299653) B1299653
theorem B866451 : Blo 864565 866451 := bstep (se 1 (by rfl) ⟨649838, by rfl⟩ : syracuseStep 866451 = 1299677) B1299677
theorem B866467 : Blo 864565 866467 := bstep (se 1 (by rfl) ⟨649850, by rfl⟩ : syracuseStep 866467 = 1299701) B1299701
theorem B3291299 : Blo 864565 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B3291313 : Blo 864565 3291313 := bstep (se 2 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 3291313 = 2468485) B2468485
theorem B1095859 : Blo 864565 1095859 := bstep (se 1 (by rfl) ⟨821894, by rfl⟩ : syracuseStep 1095859 = 1643789) B1643789
theorem B866483 : Blo 864565 866483 := bstep (se 1 (by rfl) ⟨649862, by rfl⟩ : syracuseStep 866483 = 1299725) B1299725
theorem B866499 : Blo 864565 866499 := bstep (se 1 (by rfl) ⟨649874, by rfl⟩ : syracuseStep 866499 = 1299749) B1299749
theorem B866515 : Blo 864565 866515 := bstep (se 1 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 866515 = 1299773) B1299773
theorem B866531 : Blo 864565 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B866547 : Blo 864565 866547 := bstep (se 1 (by rfl) ⟨649910, by rfl⟩ : syracuseStep 866547 = 1299821) B1299821
theorem B866563 : Blo 864565 866563 := bstep (se 1 (by rfl) ⟨649922, by rfl⟩ : syracuseStep 866563 = 1299845) B1299845
theorem B2930957 : Blo 864565 2930957 := bstep (se 3 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 2930957 = 1099109) B1099109
theorem B866579 : Blo 864565 866579 := bstep (se 1 (by rfl) ⟨649934, by rfl⟩ : syracuseStep 866579 = 1299869) B1299869
theorem B866595 : Blo 864565 866595 := bstep (se 1 (by rfl) ⟨649946, by rfl⟩ : syracuseStep 866595 = 1299893) B1299893
theorem B866611 : Blo 864565 866611 := bstep (se 1 (by rfl) ⟨649958, by rfl⟩ : syracuseStep 866611 = 1299917) B1299917
theorem B866627 : Blo 864565 866627 := bstep (se 1 (by rfl) ⟨649970, by rfl⟩ : syracuseStep 866627 = 1299941) B1299941
theorem B2931011 : Blo 864565 2931011 := bstep (se 1 (by rfl) ⟨2198258, by rfl⟩ : syracuseStep 2931011 = 4396517) B4396517
theorem B866643 : Blo 864565 866643 := bstep (se 1 (by rfl) ⟨649982, by rfl⟩ : syracuseStep 866643 = 1299965) B1299965
theorem B866659 : Blo 864565 866659 := bstep (se 1 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 866659 = 1299989) B1299989
theorem B866675 : Blo 864565 866675 := bstep (se 1 (by rfl) ⟨650006, by rfl⟩ : syracuseStep 866675 = 1300013) B1300013
theorem B866691 : Blo 864565 866691 := bstep (se 1 (by rfl) ⟨650018, by rfl⟩ : syracuseStep 866691 = 1300037) B1300037
theorem B1948049 : Blo 864565 1948049 := bstep (se 2 (by rfl) ⟨730518, by rfl⟩ : syracuseStep 1948049 = 1461037) B1461037
theorem B866707 : Blo 864565 866707 := bstep (se 1 (by rfl) ⟨650030, by rfl⟩ : syracuseStep 866707 = 1300061) B1300061
theorem B1948067 : Blo 864565 1948067 := bstep (se 1 (by rfl) ⟨1461050, by rfl⟩ : syracuseStep 1948067 = 2922101) B2922101
theorem B866723 : Blo 864565 866723 := bstep (se 1 (by rfl) ⟨650042, by rfl⟩ : syracuseStep 866723 = 1300085) B1300085
theorem B866739 : Blo 864565 866739 := bstep (se 1 (by rfl) ⟨650054, by rfl⟩ : syracuseStep 866739 = 1300109) B1300109
theorem B866755 : Blo 864565 866755 := bstep (se 1 (by rfl) ⟨650066, by rfl⟩ : syracuseStep 866755 = 1300133) B1300133
theorem B866771 : Blo 864565 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B866787 : Blo 864565 866787 := bstep (se 1 (by rfl) ⟨650090, by rfl⟩ : syracuseStep 866787 = 1300181) B1300181
theorem B866803 : Blo 864565 866803 := bstep (se 1 (by rfl) ⟨650102, by rfl⟩ : syracuseStep 866803 = 1300205) B1300205
theorem B866819 : Blo 864565 866819 := bstep (se 1 (by rfl) ⟨650114, by rfl⟩ : syracuseStep 866819 = 1300229) B1300229
theorem B866835 : Blo 864565 866835 := bstep (se 1 (by rfl) ⟨650126, by rfl⟩ : syracuseStep 866835 = 1300253) B1300253
theorem B1391137 : Blo 864565 1391137 := bstep (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) B1043353
theorem B866851 : Blo 864565 866851 := bstep (se 1 (by rfl) ⟨650138, by rfl⟩ : syracuseStep 866851 = 1300277) B1300277
theorem B866867 : Blo 864565 866867 := bstep (se 1 (by rfl) ⟨650150, by rfl⟩ : syracuseStep 866867 = 1300301) B1300301
theorem B866883 : Blo 864565 866883 := bstep (se 1 (by rfl) ⟨650162, by rfl⟩ : syracuseStep 866883 = 1300325) B1300325
theorem B2931281 : Blo 864565 2931281 := bstep (se 2 (by rfl) ⟨1099230, by rfl⟩ : syracuseStep 2931281 = 2198461) B2198461
theorem B866899 : Blo 864565 866899 := bstep (se 1 (by rfl) ⟨650174, by rfl⟩ : syracuseStep 866899 = 1300349) B1300349
theorem B866915 : Blo 864565 866915 := bstep (se 1 (by rfl) ⟨650186, by rfl⟩ : syracuseStep 866915 = 1300373) B1300373
theorem B13318769 : Blo 864565 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B866931 : Blo 864565 866931 := bstep (se 1 (by rfl) ⟨650198, by rfl⟩ : syracuseStep 866931 = 1300397) B1300397
theorem B866947 : Blo 864565 866947 := bstep (se 1 (by rfl) ⟨650210, by rfl⟩ : syracuseStep 866947 = 1300421) B1300421
theorem B866963 : Blo 864565 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B1096355 : Blo 864565 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B866979 : Blo 864565 866979 := bstep (se 1 (by rfl) ⟨650234, by rfl⟩ : syracuseStep 866979 = 1300469) B1300469
theorem B1948337 : Blo 864565 1948337 := bstep (se 2 (by rfl) ⟨730626, by rfl⟩ : syracuseStep 1948337 = 1461253) B1461253
theorem B866995 : Blo 864565 866995 := bstep (se 1 (by rfl) ⟨650246, by rfl⟩ : syracuseStep 866995 = 1300493) B1300493
theorem B1948355 : Blo 864565 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B867011 : Blo 864565 867011 := bstep (se 1 (by rfl) ⟨650258, by rfl⟩ : syracuseStep 867011 = 1300517) B1300517
theorem B867027 : Blo 864565 867027 := bstep (se 1 (by rfl) ⟨650270, by rfl⟩ : syracuseStep 867027 = 1300541) B1300541
theorem B867043 : Blo 864565 867043 := bstep (se 1 (by rfl) ⟨650282, by rfl⟩ : syracuseStep 867043 = 1300565) B1300565
theorem B867059 : Blo 864565 867059 := bstep (se 1 (by rfl) ⟨650294, by rfl⟩ : syracuseStep 867059 = 1300589) B1300589
theorem B867075 : Blo 864565 867075 := bstep (se 1 (by rfl) ⟨650306, by rfl⟩ : syracuseStep 867075 = 1300613) B1300613
theorem B867091 : Blo 864565 867091 := bstep (se 1 (by rfl) ⟨650318, by rfl⟩ : syracuseStep 867091 = 1300637) B1300637
theorem B867107 : Blo 864565 867107 := bstep (se 1 (by rfl) ⟨650330, by rfl⟩ : syracuseStep 867107 = 1300661) B1300661
theorem B867123 : Blo 864565 867123 := bstep (se 1 (by rfl) ⟨650342, by rfl⟩ : syracuseStep 867123 = 1300685) B1300685
theorem B867139 : Blo 864565 867139 := bstep (se 1 (by rfl) ⟨650354, by rfl⟩ : syracuseStep 867139 = 1300709) B1300709
theorem B867155 : Blo 864565 867155 := bstep (se 1 (by rfl) ⟨650366, by rfl⟩ : syracuseStep 867155 = 1300733) B1300733
theorem B867171 : Blo 864565 867171 := bstep (se 1 (by rfl) ⟨650378, by rfl⟩ : syracuseStep 867171 = 1300757) B1300757
theorem B867187 : Blo 864565 867187 := bstep (se 1 (by rfl) ⟨650390, by rfl⟩ : syracuseStep 867187 = 1300781) B1300781
theorem B867203 : Blo 864565 867203 := bstep (se 1 (by rfl) ⟨650402, by rfl⟩ : syracuseStep 867203 = 1300805) B1300805
theorem B867219 : Blo 864565 867219 := bstep (se 1 (by rfl) ⟨650414, by rfl⟩ : syracuseStep 867219 = 1300829) B1300829
theorem B867235 : Blo 864565 867235 := bstep (se 1 (by rfl) ⟨650426, by rfl⟩ : syracuseStep 867235 = 1300853) B1300853
theorem B867251 : Blo 864565 867251 := bstep (se 1 (by rfl) ⟨650438, by rfl⟩ : syracuseStep 867251 = 1300877) B1300877
theorem B867267 : Blo 864565 867267 := bstep (se 1 (by rfl) ⟨650450, by rfl⟩ : syracuseStep 867267 = 1300901) B1300901
theorem B1948625 : Blo 864565 1948625 := bstep (se 2 (by rfl) ⟨730734, by rfl⟩ : syracuseStep 1948625 = 1461469) B1461469
theorem B867283 : Blo 864565 867283 := bstep (se 1 (by rfl) ⟨650462, by rfl⟩ : syracuseStep 867283 = 1300925) B1300925
theorem B1948643 : Blo 864565 1948643 := bstep (se 1 (by rfl) ⟨1461482, by rfl⟩ : syracuseStep 1948643 = 2922965) B2922965
theorem B1850339 : Blo 864565 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B867299 : Blo 864565 867299 := bstep (se 1 (by rfl) ⟨650474, by rfl⟩ : syracuseStep 867299 = 1300949) B1300949
theorem B867315 : Blo 864565 867315 := bstep (se 1 (by rfl) ⟨650486, by rfl⟩ : syracuseStep 867315 = 1300973) B1300973
theorem B867331 : Blo 864565 867331 := bstep (se 1 (by rfl) ⟨650498, by rfl⟩ : syracuseStep 867331 = 1300997) B1300997
theorem B867347 : Blo 864565 867347 := bstep (se 1 (by rfl) ⟨650510, by rfl⟩ : syracuseStep 867347 = 1301021) B1301021
theorem B867363 : Blo 864565 867363 := bstep (se 1 (by rfl) ⟨650522, by rfl⟩ : syracuseStep 867363 = 1301045) B1301045
theorem B867379 : Blo 864565 867379 := bstep (se 1 (by rfl) ⟨650534, by rfl⟩ : syracuseStep 867379 = 1301069) B1301069
theorem B867395 : Blo 864565 867395 := bstep (se 1 (by rfl) ⟨650546, by rfl⟩ : syracuseStep 867395 = 1301093) B1301093
theorem B867411 : Blo 864565 867411 := bstep (se 1 (by rfl) ⟨650558, by rfl⟩ : syracuseStep 867411 = 1301117) B1301117
theorem B867427 : Blo 864565 867427 := bstep (se 1 (by rfl) ⟨650570, by rfl⟩ : syracuseStep 867427 = 1301141) B1301141
theorem B867443 : Blo 864565 867443 := bstep (se 1 (by rfl) ⟨650582, by rfl⟩ : syracuseStep 867443 = 1301165) B1301165
theorem B867459 : Blo 864565 867459 := bstep (se 1 (by rfl) ⟨650594, by rfl⟩ : syracuseStep 867459 = 1301189) B1301189
theorem B867475 : Blo 864565 867475 := bstep (se 1 (by rfl) ⟨650606, by rfl⟩ : syracuseStep 867475 = 1301213) B1301213
theorem B867491 : Blo 864565 867491 := bstep (se 1 (by rfl) ⟨650618, by rfl⟩ : syracuseStep 867491 = 1301237) B1301237
theorem B867507 : Blo 864565 867507 := bstep (se 1 (by rfl) ⟨650630, by rfl⟩ : syracuseStep 867507 = 1301261) B1301261
theorem B867523 : Blo 864565 867523 := bstep (se 1 (by rfl) ⟨650642, by rfl⟩ : syracuseStep 867523 = 1301285) B1301285
theorem B867539 : Blo 864565 867539 := bstep (se 1 (by rfl) ⟨650654, by rfl⟩ : syracuseStep 867539 = 1301309) B1301309
theorem B867555 : Blo 864565 867555 := bstep (se 1 (by rfl) ⟨650666, by rfl⟩ : syracuseStep 867555 = 1301333) B1301333
theorem B1948913 : Blo 864565 1948913 := bstep (se 2 (by rfl) ⟨730842, by rfl⟩ : syracuseStep 1948913 = 1461685) B1461685
theorem B867571 : Blo 864565 867571 := bstep (se 1 (by rfl) ⟨650678, by rfl⟩ : syracuseStep 867571 = 1301357) B1301357
theorem B1948931 : Blo 864565 1948931 := bstep (se 1 (by rfl) ⟨1461698, by rfl⟩ : syracuseStep 1948931 = 2923397) B2923397
theorem B867587 : Blo 864565 867587 := bstep (se 1 (by rfl) ⟨650690, by rfl⟩ : syracuseStep 867587 = 1301381) B1301381
theorem B867603 : Blo 864565 867603 := bstep (se 1 (by rfl) ⟨650702, by rfl⟩ : syracuseStep 867603 = 1301405) B1301405
theorem B867619 : Blo 864565 867619 := bstep (se 1 (by rfl) ⟨650714, by rfl⟩ : syracuseStep 867619 = 1301429) B1301429
theorem B4930865 : Blo 864565 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B867635 : Blo 864565 867635 := bstep (se 1 (by rfl) ⟨650726, by rfl⟩ : syracuseStep 867635 = 1301453) B1301453
theorem B867651 : Blo 864565 867651 := bstep (se 1 (by rfl) ⟨650738, by rfl⟩ : syracuseStep 867651 = 1301477) B1301477
theorem B867667 : Blo 864565 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B1097059 : Blo 864565 1097059 := bstep (se 1 (by rfl) ⟨822794, by rfl⟩ : syracuseStep 1097059 = 1645589) B1645589
theorem B867683 : Blo 864565 867683 := bstep (se 1 (by rfl) ⟨650762, by rfl⟩ : syracuseStep 867683 = 1301525) B1301525
theorem B867699 : Blo 864565 867699 := bstep (se 1 (by rfl) ⟨650774, by rfl⟩ : syracuseStep 867699 = 1301549) B1301549
theorem B867715 : Blo 864565 867715 := bstep (se 1 (by rfl) ⟨650786, by rfl⟩ : syracuseStep 867715 = 1301573) B1301573
theorem B2473361 : Blo 864565 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B867731 : Blo 864565 867731 := bstep (se 1 (by rfl) ⟨650798, by rfl⟩ : syracuseStep 867731 = 1301597) B1301597
theorem B867747 : Blo 864565 867747 := bstep (se 1 (by rfl) ⟨650810, by rfl⟩ : syracuseStep 867747 = 1301621) B1301621
theorem B867763 : Blo 864565 867763 := bstep (se 1 (by rfl) ⟨650822, by rfl⟩ : syracuseStep 867763 = 1301645) B1301645
theorem B1097155 : Blo 864565 1097155 := bstep (se 1 (by rfl) ⟨822866, by rfl⟩ : syracuseStep 1097155 = 1645733) B1645733
theorem B867779 : Blo 864565 867779 := bstep (se 1 (by rfl) ⟨650834, by rfl⟩ : syracuseStep 867779 = 1301669) B1301669
theorem B867795 : Blo 864565 867795 := bstep (se 1 (by rfl) ⟨650846, by rfl⟩ : syracuseStep 867795 = 1301693) B1301693
theorem B867811 : Blo 864565 867811 := bstep (se 1 (by rfl) ⟨650858, by rfl⟩ : syracuseStep 867811 = 1301717) B1301717
theorem B867827 : Blo 864565 867827 := bstep (se 1 (by rfl) ⟨650870, by rfl⟩ : syracuseStep 867827 = 1301741) B1301741
theorem B867843 : Blo 864565 867843 := bstep (se 1 (by rfl) ⟨650882, by rfl⟩ : syracuseStep 867843 = 1301765) B1301765
theorem B1949201 : Blo 864565 1949201 := bstep (se 2 (by rfl) ⟨730950, by rfl⟩ : syracuseStep 1949201 = 1461901) B1461901
theorem B867859 : Blo 864565 867859 := bstep (se 1 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 867859 = 1301789) B1301789
theorem B1949219 : Blo 864565 1949219 := bstep (se 1 (by rfl) ⟨1461914, by rfl⟩ : syracuseStep 1949219 = 2923829) B2923829
theorem B867875 : Blo 864565 867875 := bstep (se 1 (by rfl) ⟨650906, by rfl⟩ : syracuseStep 867875 = 1301813) B1301813
theorem B867891 : Blo 864565 867891 := bstep (se 1 (by rfl) ⟨650918, by rfl⟩ : syracuseStep 867891 = 1301837) B1301837
theorem B867907 : Blo 864565 867907 := bstep (se 1 (by rfl) ⟨650930, by rfl⟩ : syracuseStep 867907 = 1301861) B1301861
theorem B867923 : Blo 864565 867923 := bstep (se 1 (by rfl) ⟨650942, by rfl⟩ : syracuseStep 867923 = 1301885) B1301885
theorem B3292771 : Blo 864565 3292771 := bstep (se 1 (by rfl) ⟨2469578, by rfl⟩ : syracuseStep 3292771 = 4939157) B4939157
theorem B867939 : Blo 864565 867939 := bstep (se 1 (by rfl) ⟨650954, by rfl⟩ : syracuseStep 867939 = 1301909) B1301909
theorem B867955 : Blo 864565 867955 := bstep (se 1 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 867955 = 1301933) B1301933
theorem B867971 : Blo 864565 867971 := bstep (se 1 (by rfl) ⟨650978, by rfl⟩ : syracuseStep 867971 = 1301957) B1301957
theorem B867987 : Blo 864565 867987 := bstep (se 1 (by rfl) ⟨650990, by rfl⟩ : syracuseStep 867987 = 1301981) B1301981
theorem B868003 : Blo 864565 868003 := bstep (se 1 (by rfl) ⟨651002, by rfl⟩ : syracuseStep 868003 = 1302005) B1302005
theorem B868019 : Blo 864565 868019 := bstep (se 1 (by rfl) ⟨651014, by rfl⟩ : syracuseStep 868019 = 1302029) B1302029
theorem B868035 : Blo 864565 868035 := bstep (se 1 (by rfl) ⟨651026, by rfl⟩ : syracuseStep 868035 = 1302053) B1302053
theorem B868051 : Blo 864565 868051 := bstep (se 1 (by rfl) ⟨651038, by rfl⟩ : syracuseStep 868051 = 1302077) B1302077
theorem B868067 : Blo 864565 868067 := bstep (se 1 (by rfl) ⟨651050, by rfl⟩ : syracuseStep 868067 = 1302101) B1302101
theorem B868083 : Blo 864565 868083 := bstep (se 1 (by rfl) ⟨651062, by rfl⟩ : syracuseStep 868083 = 1302125) B1302125
theorem B868099 : Blo 864565 868099 := bstep (se 1 (by rfl) ⟨651074, by rfl⟩ : syracuseStep 868099 = 1302149) B1302149
theorem B8339213 : Blo 864565 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B868115 : Blo 864565 868115 := bstep (se 1 (by rfl) ⟨651086, by rfl⟩ : syracuseStep 868115 = 1302173) B1302173
theorem B868131 : Blo 864565 868131 := bstep (se 1 (by rfl) ⟨651098, by rfl⟩ : syracuseStep 868131 = 1302197) B1302197
theorem B1949489 : Blo 864565 1949489 := bstep (se 2 (by rfl) ⟨731058, by rfl⟩ : syracuseStep 1949489 = 1462117) B1462117
theorem B3129137 : Blo 864565 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B868147 : Blo 864565 868147 := bstep (se 1 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 868147 = 1302221) B1302221
theorem B1949507 : Blo 864565 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B868163 : Blo 864565 868163 := bstep (se 1 (by rfl) ⟨651122, by rfl⟩ : syracuseStep 868163 = 1302245) B1302245
theorem B868179 : Blo 864565 868179 := bstep (se 1 (by rfl) ⟨651134, by rfl⟩ : syracuseStep 868179 = 1302269) B1302269
theorem B868195 : Blo 864565 868195 := bstep (se 1 (by rfl) ⟨651146, by rfl⟩ : syracuseStep 868195 = 1302293) B1302293
theorem B868211 : Blo 864565 868211 := bstep (se 1 (by rfl) ⟨651158, by rfl⟩ : syracuseStep 868211 = 1302317) B1302317
theorem B868227 : Blo 864565 868227 := bstep (se 1 (by rfl) ⟨651170, by rfl⟩ : syracuseStep 868227 = 1302341) B1302341
theorem B868243 : Blo 864565 868243 := bstep (se 1 (by rfl) ⟨651182, by rfl⟩ : syracuseStep 868243 = 1302365) B1302365
theorem B868259 : Blo 864565 868259 := bstep (se 1 (by rfl) ⟨651194, by rfl⟩ : syracuseStep 868259 = 1302389) B1302389
theorem B1097651 : Blo 864565 1097651 := bstep (se 1 (by rfl) ⟨823238, by rfl⟩ : syracuseStep 1097651 = 1646477) B1646477
theorem B868275 : Blo 864565 868275 := bstep (se 1 (by rfl) ⟨651206, by rfl⟩ : syracuseStep 868275 = 1302413) B1302413
theorem B868291 : Blo 864565 868291 := bstep (se 1 (by rfl) ⟨651218, by rfl⟩ : syracuseStep 868291 = 1302437) B1302437
theorem B868307 : Blo 864565 868307 := bstep (se 1 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 868307 = 1302461) B1302461
theorem B868323 : Blo 864565 868323 := bstep (se 1 (by rfl) ⟨651242, by rfl⟩ : syracuseStep 868323 = 1302485) B1302485
theorem B868339 : Blo 864565 868339 := bstep (se 1 (by rfl) ⟨651254, by rfl⟩ : syracuseStep 868339 = 1302509) B1302509
theorem B868355 : Blo 864565 868355 := bstep (se 1 (by rfl) ⟨651266, by rfl⟩ : syracuseStep 868355 = 1302533) B1302533
theorem B868371 : Blo 864565 868371 := bstep (se 1 (by rfl) ⟨651278, by rfl⟩ : syracuseStep 868371 = 1302557) B1302557
theorem B868387 : Blo 864565 868387 := bstep (se 1 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 868387 = 1302581) B1302581
theorem B868403 : Blo 864565 868403 := bstep (se 1 (by rfl) ⟨651302, by rfl⟩ : syracuseStep 868403 = 1302605) B1302605
theorem B868419 : Blo 864565 868419 := bstep (se 1 (by rfl) ⟨651314, by rfl⟩ : syracuseStep 868419 = 1302629) B1302629
theorem B1949777 : Blo 864565 1949777 := bstep (se 2 (by rfl) ⟨731166, by rfl⟩ : syracuseStep 1949777 = 1462333) B1462333
theorem B868435 : Blo 864565 868435 := bstep (se 1 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 868435 = 1302653) B1302653
theorem B1949795 : Blo 864565 1949795 := bstep (se 1 (by rfl) ⟨1462346, by rfl⟩ : syracuseStep 1949795 = 2924693) B2924693
theorem B868451 : Blo 864565 868451 := bstep (se 1 (by rfl) ⟨651338, by rfl⟩ : syracuseStep 868451 = 1302677) B1302677
theorem B6242417 : Blo 864565 6242417 := bstep (se 2 (by rfl) ⟨2340906, by rfl⟩ : syracuseStep 6242417 = 4681813) B4681813
theorem B868467 : Blo 864565 868467 := bstep (se 1 (by rfl) ⟨651350, by rfl⟩ : syracuseStep 868467 = 1302701) B1302701
theorem B868483 : Blo 864565 868483 := bstep (se 1 (by rfl) ⟨651362, by rfl⟩ : syracuseStep 868483 = 1302725) B1302725
theorem B868499 : Blo 864565 868499 := bstep (se 1 (by rfl) ⟨651374, by rfl⟩ : syracuseStep 868499 = 1302749) B1302749
theorem B868515 : Blo 864565 868515 := bstep (se 1 (by rfl) ⟨651386, by rfl⟩ : syracuseStep 868515 = 1302773) B1302773
theorem B868531 : Blo 864565 868531 := bstep (se 1 (by rfl) ⟨651398, by rfl⟩ : syracuseStep 868531 = 1302797) B1302797
theorem B868547 : Blo 864565 868547 := bstep (se 1 (by rfl) ⟨651410, by rfl⟩ : syracuseStep 868547 = 1302821) B1302821
theorem B868563 : Blo 864565 868563 := bstep (se 1 (by rfl) ⟨651422, by rfl⟩ : syracuseStep 868563 = 1302845) B1302845
theorem B2965805 : Blo 864565 2965805 := bstep (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) B1112177
theorem B1950065 : Blo 864565 1950065 := bstep (se 2 (by rfl) ⟨731274, by rfl⟩ : syracuseStep 1950065 = 1462549) B1462549
theorem B1950083 : Blo 864565 1950083 := bstep (se 1 (by rfl) ⟨1462562, by rfl⟩ : syracuseStep 1950083 = 2925125) B2925125
theorem B10011061 : Blo 864565 10011061 := bstep (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) B938537
theorem B2965997 : Blo 864565 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B1098355 : Blo 864565 1098355 := bstep (se 1 (by rfl) ⟨823766, by rfl⟩ : syracuseStep 1098355 = 1647533) B1647533
theorem B1950353 : Blo 864565 1950353 := bstep (se 2 (by rfl) ⟨731382, by rfl⟩ : syracuseStep 1950353 = 1462765) B1462765
theorem B1950371 : Blo 864565 1950371 := bstep (se 1 (by rfl) ⟨1462778, by rfl⟩ : syracuseStep 1950371 = 2925557) B2925557
theorem B4440781 : Blo 864565 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B1098451 : Blo 864565 1098451 := bstep (se 1 (by rfl) ⟨823838, by rfl⟩ : syracuseStep 1098451 = 1647677) B1647677
theorem B4932323 : Blo 864565 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B1459073 : Blo 864565 1459073 := bstep (se 2 (by rfl) ⟨547152, by rfl⟩ : syracuseStep 1459073 = 1094305) B1094305
theorem B1950641 : Blo 864565 1950641 := bstep (se 2 (by rfl) ⟨731490, by rfl⟩ : syracuseStep 1950641 = 1462981) B1462981
theorem B1950659 : Blo 864565 1950659 := bstep (se 1 (by rfl) ⟨1462994, by rfl⟩ : syracuseStep 1950659 = 2925989) B2925989
theorem B1852355 : Blo 864565 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B1459201 : Blo 864565 1459201 := bstep (se 2 (by rfl) ⟨547200, by rfl⟩ : syracuseStep 1459201 = 1094401) B1094401
theorem B1459235 : Blo 864565 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B1459363 : Blo 864565 1459363 := bstep (se 1 (by rfl) ⟨1094522, by rfl⟩ : syracuseStep 1459363 = 2189045) B2189045
theorem B1098947 : Blo 864565 1098947 := bstep (se 1 (by rfl) ⟨824210, by rfl⟩ : syracuseStep 1098947 = 1648421) B1648421
theorem B6571205 : Blo 864565 6571205 := bstep (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) B1232101
theorem B1950929 : Blo 864565 1950929 := bstep (se 2 (by rfl) ⟨731598, by rfl⟩ : syracuseStep 1950929 = 1463197) B1463197
theorem B1950947 : Blo 864565 1950947 := bstep (se 1 (by rfl) ⟨1463210, by rfl⟩ : syracuseStep 1950947 = 2926421) B2926421
theorem B1459505 : Blo 864565 1459505 := bstep (se 2 (by rfl) ⟨547314, by rfl⟩ : syracuseStep 1459505 = 1094629) B1094629
theorem B2082161 : Blo 864565 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B2770307 : Blo 864565 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B1459633 : Blo 864565 1459633 := bstep (se 2 (by rfl) ⟨547362, by rfl⟩ : syracuseStep 1459633 = 1094725) B1094725
theorem B1459667 : Blo 864565 1459667 := bstep (se 1 (by rfl) ⟨1094750, by rfl⟩ : syracuseStep 1459667 = 2189501) B2189501
theorem B10536419 : Blo 864565 10536419 := bstep (se 1 (by rfl) ⟨7902314, by rfl⟩ : syracuseStep 10536419 = 15804629) B15804629
theorem B1951217 : Blo 864565 1951217 := bstep (se 2 (by rfl) ⟨731706, by rfl⟩ : syracuseStep 1951217 = 1463413) B1463413
theorem B1951235 : Blo 864565 1951235 := bstep (se 1 (by rfl) ⟨1463426, by rfl⟩ : syracuseStep 1951235 = 2926853) B2926853
theorem B1459795 : Blo 864565 1459795 := bstep (se 1 (by rfl) ⟨1094846, by rfl⟩ : syracuseStep 1459795 = 2189693) B2189693
theorem B4933325 : Blo 864565 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B1558225 : Blo 864565 1558225 := bstep (se 2 (by rfl) ⟨584334, by rfl⟩ : syracuseStep 1558225 = 1168669) B1168669
theorem B1459937 : Blo 864565 1459937 := bstep (se 2 (by rfl) ⟨547476, by rfl⟩ : syracuseStep 1459937 = 1094953) B1094953
theorem B2967281 : Blo 864565 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B3294989 : Blo 864565 3294989 := bstep (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) B1235621
theorem B1951505 : Blo 864565 1951505 := bstep (se 2 (by rfl) ⟨731814, by rfl⟩ : syracuseStep 1951505 = 1463629) B1463629
theorem B1951523 : Blo 864565 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B1460065 : Blo 864565 1460065 := bstep (se 2 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 1460065 = 1095049) B1095049
theorem B1460099 : Blo 864565 1460099 := bstep (se 1 (by rfl) ⟨1095074, by rfl⟩ : syracuseStep 1460099 = 2190149) B2190149
theorem B1460227 : Blo 864565 1460227 := bstep (se 1 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 1460227 = 2190341) B2190341
theorem B1951793 : Blo 864565 1951793 := bstep (se 2 (by rfl) ⟨731922, by rfl⟩ : syracuseStep 1951793 = 1463845) B1463845
theorem B1951811 : Blo 864565 1951811 := bstep (se 1 (by rfl) ⟨1463858, by rfl⟩ : syracuseStep 1951811 = 2927717) B2927717
theorem B1460369 : Blo 864565 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B1460497 : Blo 864565 1460497 := bstep (se 2 (by rfl) ⟨547686, by rfl⟩ : syracuseStep 1460497 = 1095373) B1095373
theorem B1231139 : Blo 864565 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B1460531 : Blo 864565 1460531 := bstep (se 1 (by rfl) ⟨1095398, by rfl⟩ : syracuseStep 1460531 = 2190797) B2190797
theorem B1952081 : Blo 864565 1952081 := bstep (se 2 (by rfl) ⟨732030, by rfl⟩ : syracuseStep 1952081 = 1464061) B1464061
theorem B1952099 : Blo 864565 1952099 := bstep (se 1 (by rfl) ⟨1464074, by rfl⟩ : syracuseStep 1952099 = 2928149) B2928149
theorem B1460659 : Blo 864565 1460659 := bstep (se 1 (by rfl) ⟨1095494, by rfl⟩ : syracuseStep 1460659 = 2190989) B2190989
theorem B1296851 : Blo 864565 1296851 := bstep (se 1 (by rfl) ⟨972638, by rfl⟩ : syracuseStep 1296851 = 1945277) B1945277
theorem B1296881 : Blo 864565 1296881 := bstep (se 2 (by rfl) ⟨486330, by rfl⟩ : syracuseStep 1296881 = 972661) B972661
theorem B1296899 : Blo 864565 1296899 := bstep (se 1 (by rfl) ⟨972674, by rfl⟩ : syracuseStep 1296899 = 1945349) B1945349
theorem B1296929 : Blo 864565 1296929 := bstep (se 2 (by rfl) ⟨486348, by rfl⟩ : syracuseStep 1296929 = 972697) B972697
theorem B1296947 : Blo 864565 1296947 := bstep (se 1 (by rfl) ⟨972710, by rfl⟩ : syracuseStep 1296947 = 1945421) B1945421
theorem B1460801 : Blo 864565 1460801 := bstep (se 2 (by rfl) ⟨547800, by rfl⟩ : syracuseStep 1460801 = 1095601) B1095601
theorem B1296977 : Blo 864565 1296977 := bstep (se 2 (by rfl) ⟨486366, by rfl⟩ : syracuseStep 1296977 = 972733) B972733
theorem B1296995 : Blo 864565 1296995 := bstep (se 1 (by rfl) ⟨972746, by rfl⟩ : syracuseStep 1296995 = 1945493) B1945493
theorem B1952369 : Blo 864565 1952369 := bstep (se 2 (by rfl) ⟨732138, by rfl⟩ : syracuseStep 1952369 = 1464277) B1464277
theorem B1297025 : Blo 864565 1297025 := bstep (se 2 (by rfl) ⟨486384, by rfl⟩ : syracuseStep 1297025 = 972769) B972769
theorem B1952387 : Blo 864565 1952387 := bstep (se 1 (by rfl) ⟨1464290, by rfl⟩ : syracuseStep 1952387 = 2928581) B2928581
theorem B1297043 : Blo 864565 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B1297073 : Blo 864565 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B1460929 : Blo 864565 1460929 := bstep (se 2 (by rfl) ⟨547848, by rfl⟩ : syracuseStep 1460929 = 1095697) B1095697
theorem B1297091 : Blo 864565 1297091 := bstep (se 1 (by rfl) ⟨972818, by rfl⟩ : syracuseStep 1297091 = 1945637) B1945637
theorem B1297121 : Blo 864565 1297121 := bstep (se 2 (by rfl) ⟨486420, by rfl⟩ : syracuseStep 1297121 = 972841) B972841
theorem B1460963 : Blo 864565 1460963 := bstep (se 1 (by rfl) ⟨1095722, by rfl⟩ : syracuseStep 1460963 = 2191445) B2191445
theorem B1297139 : Blo 864565 1297139 := bstep (se 1 (by rfl) ⟨972854, by rfl⟩ : syracuseStep 1297139 = 1945709) B1945709
theorem B1297169 : Blo 864565 1297169 := bstep (se 2 (by rfl) ⟨486438, by rfl⟩ : syracuseStep 1297169 = 972877) B972877
theorem B30034709 : Blo 864565 30034709 := bstep (se 6 (by rfl) ⟨703938, by rfl⟩ : syracuseStep 30034709 = 1407877) B1407877
theorem B1297187 : Blo 864565 1297187 := bstep (se 1 (by rfl) ⟨972890, by rfl⟩ : syracuseStep 1297187 = 1945781) B1945781
theorem B1297217 : Blo 864565 1297217 := bstep (se 2 (by rfl) ⟨486456, by rfl⟩ : syracuseStep 1297217 = 972913) B972913
theorem B1297235 : Blo 864565 1297235 := bstep (se 1 (by rfl) ⟨972926, by rfl⟩ : syracuseStep 1297235 = 1945853) B1945853
theorem B1461091 : Blo 864565 1461091 := bstep (se 1 (by rfl) ⟨1095818, by rfl⟩ : syracuseStep 1461091 = 2191637) B2191637
theorem B1297265 : Blo 864565 1297265 := bstep (se 2 (by rfl) ⟨486474, by rfl⟩ : syracuseStep 1297265 = 972949) B972949
theorem B1297283 : Blo 864565 1297283 := bstep (se 1 (by rfl) ⟨972962, by rfl⟩ : syracuseStep 1297283 = 1945925) B1945925
theorem B1952657 : Blo 864565 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B1297313 : Blo 864565 1297313 := bstep (se 2 (by rfl) ⟨486492, by rfl⟩ : syracuseStep 1297313 = 972985) B972985
theorem B1231777 : Blo 864565 1231777 := bstep (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) B923833
theorem B1952675 : Blo 864565 1952675 := bstep (se 1 (by rfl) ⟨1464506, by rfl⟩ : syracuseStep 1952675 = 2929013) B2929013
theorem B1854371 : Blo 864565 1854371 := bstep (se 1 (by rfl) ⟨1390778, by rfl⟩ : syracuseStep 1854371 = 2781557) B2781557
theorem B1297331 : Blo 864565 1297331 := bstep (se 1 (by rfl) ⟨972998, by rfl⟩ : syracuseStep 1297331 = 1945997) B1945997
theorem B1297361 : Blo 864565 1297361 := bstep (se 2 (by rfl) ⟨486510, by rfl⟩ : syracuseStep 1297361 = 973021) B973021
theorem B2771921 : Blo 864565 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B1297379 : Blo 864565 1297379 := bstep (se 1 (by rfl) ⟨973034, by rfl⟩ : syracuseStep 1297379 = 1946069) B1946069
theorem B3165155 : Blo 864565 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B1461233 : Blo 864565 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B1297409 : Blo 864565 1297409 := bstep (se 2 (by rfl) ⟨486528, by rfl⟩ : syracuseStep 1297409 = 973057) B973057
theorem B1297427 : Blo 864565 1297427 := bstep (se 1 (by rfl) ⟨973070, by rfl⟩ : syracuseStep 1297427 = 1946141) B1946141
theorem B1297457 : Blo 864565 1297457 := bstep (se 2 (by rfl) ⟨486546, by rfl⟩ : syracuseStep 1297457 = 973093) B973093
theorem B1297475 : Blo 864565 1297475 := bstep (se 1 (by rfl) ⟨973106, by rfl⟩ : syracuseStep 1297475 = 1946213) B1946213
theorem B1297505 : Blo 864565 1297505 := bstep (se 2 (by rfl) ⟨486564, by rfl⟩ : syracuseStep 1297505 = 973129) B973129
theorem B1461361 : Blo 864565 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B2346097 : Blo 864565 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B1297523 : Blo 864565 1297523 := bstep (se 1 (by rfl) ⟨973142, by rfl⟩ : syracuseStep 1297523 = 1946285) B1946285
theorem B1297553 : Blo 864565 1297553 := bstep (se 2 (by rfl) ⟨486582, by rfl⟩ : syracuseStep 1297553 = 973165) B973165
theorem B1461395 : Blo 864565 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B1297571 : Blo 864565 1297571 := bstep (se 1 (by rfl) ⟨973178, by rfl⟩ : syracuseStep 1297571 = 1946357) B1946357
theorem B1952945 : Blo 864565 1952945 := bstep (se 2 (by rfl) ⟨732354, by rfl⟩ : syracuseStep 1952945 = 1464709) B1464709
theorem B1297601 : Blo 864565 1297601 := bstep (se 2 (by rfl) ⟨486600, by rfl⟩ : syracuseStep 1297601 = 973201) B973201
theorem B1952963 : Blo 864565 1952963 := bstep (se 1 (by rfl) ⟨1464722, by rfl⟩ : syracuseStep 1952963 = 2929445) B2929445
theorem B1297619 : Blo 864565 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B1297649 : Blo 864565 1297649 := bstep (se 2 (by rfl) ⟨486618, by rfl⟩ : syracuseStep 1297649 = 973237) B973237
theorem B1232113 : Blo 864565 1232113 := bstep (se 2 (by rfl) ⟨462042, by rfl⟩ : syracuseStep 1232113 = 924085) B924085
theorem B11259121 : Blo 864565 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B1297667 : Blo 864565 1297667 := bstep (se 1 (by rfl) ⟨973250, by rfl⟩ : syracuseStep 1297667 = 1946501) B1946501
theorem B1461523 : Blo 864565 1461523 := bstep (se 1 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 1461523 = 2192285) B2192285
theorem B1297697 : Blo 864565 1297697 := bstep (se 2 (by rfl) ⟨486636, by rfl⟩ : syracuseStep 1297697 = 973273) B973273
theorem B1297715 : Blo 864565 1297715 := bstep (se 1 (by rfl) ⟨973286, by rfl⟩ : syracuseStep 1297715 = 1946573) B1946573
theorem B1297745 : Blo 864565 1297745 := bstep (se 2 (by rfl) ⟨486654, by rfl⟩ : syracuseStep 1297745 = 973309) B973309
theorem B1297763 : Blo 864565 1297763 := bstep (se 1 (by rfl) ⟨973322, by rfl⟩ : syracuseStep 1297763 = 1946645) B1946645
theorem B1297793 : Blo 864565 1297793 := bstep (se 2 (by rfl) ⟨486672, by rfl⟩ : syracuseStep 1297793 = 973345) B973345
theorem B1297811 : Blo 864565 1297811 := bstep (se 1 (by rfl) ⟨973358, by rfl⟩ : syracuseStep 1297811 = 1946717) B1946717
theorem B1461665 : Blo 864565 1461665 := bstep (se 2 (by rfl) ⟨548124, by rfl⟩ : syracuseStep 1461665 = 1096249) B1096249
theorem B1297841 : Blo 864565 1297841 := bstep (se 2 (by rfl) ⟨486690, by rfl⟩ : syracuseStep 1297841 = 973381) B973381
theorem B1297859 : Blo 864565 1297859 := bstep (se 1 (by rfl) ⟨973394, by rfl⟩ : syracuseStep 1297859 = 1946789) B1946789
theorem B1953233 : Blo 864565 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B2379217 : Blo 864565 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B1297889 : Blo 864565 1297889 := bstep (se 2 (by rfl) ⟨486708, by rfl⟩ : syracuseStep 1297889 = 973417) B973417
theorem B1953251 : Blo 864565 1953251 := bstep (se 1 (by rfl) ⟨1464938, by rfl⟩ : syracuseStep 1953251 = 2929877) B2929877
theorem B1297907 : Blo 864565 1297907 := bstep (se 1 (by rfl) ⟨973430, by rfl⟩ : syracuseStep 1297907 = 1946861) B1946861
theorem B1297937 : Blo 864565 1297937 := bstep (se 2 (by rfl) ⟨486726, by rfl⟩ : syracuseStep 1297937 = 973453) B973453
theorem B1461793 : Blo 864565 1461793 := bstep (se 2 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 1461793 = 1096345) B1096345
theorem B1297955 : Blo 864565 1297955 := bstep (se 1 (by rfl) ⟨973466, by rfl⟩ : syracuseStep 1297955 = 1946933) B1946933
theorem B1297985 : Blo 864565 1297985 := bstep (se 2 (by rfl) ⟨486744, by rfl⟩ : syracuseStep 1297985 = 973489) B973489
theorem B1461827 : Blo 864565 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B1298003 : Blo 864565 1298003 := bstep (se 1 (by rfl) ⟨973502, by rfl⟩ : syracuseStep 1298003 = 1947005) B1947005
theorem B4378211 : Blo 864565 4378211 := bstep (se 1 (by rfl) ⟨3283658, by rfl⟩ : syracuseStep 4378211 = 6567317) B6567317
theorem B1298033 : Blo 864565 1298033 := bstep (se 2 (by rfl) ⟨486762, by rfl⟩ : syracuseStep 1298033 = 973525) B973525
theorem B1298051 : Blo 864565 1298051 := bstep (se 1 (by rfl) ⟨973538, by rfl⟩ : syracuseStep 1298051 = 1947077) B1947077
theorem B1298081 : Blo 864565 1298081 := bstep (se 2 (by rfl) ⟨486780, by rfl⟩ : syracuseStep 1298081 = 973561) B973561
theorem B1298099 : Blo 864565 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B1461955 : Blo 864565 1461955 := bstep (se 1 (by rfl) ⟨1096466, by rfl⟩ : syracuseStep 1461955 = 2192933) B2192933
theorem B1298129 : Blo 864565 1298129 := bstep (se 2 (by rfl) ⟨486798, by rfl⟩ : syracuseStep 1298129 = 973597) B973597
theorem B1298147 : Blo 864565 1298147 := bstep (se 1 (by rfl) ⟨973610, by rfl⟩ : syracuseStep 1298147 = 1947221) B1947221
theorem B5557987 : Blo 864565 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B1953521 : Blo 864565 1953521 := bstep (se 2 (by rfl) ⟨732570, by rfl⟩ : syracuseStep 1953521 = 1465141) B1465141
theorem B1298177 : Blo 864565 1298177 := bstep (se 2 (by rfl) ⟨486816, by rfl⟩ : syracuseStep 1298177 = 973633) B973633
theorem B1953539 : Blo 864565 1953539 := bstep (se 1 (by rfl) ⟨1465154, by rfl⟩ : syracuseStep 1953539 = 2930309) B2930309
theorem B1298195 : Blo 864565 1298195 := bstep (se 1 (by rfl) ⟨973646, by rfl⟩ : syracuseStep 1298195 = 1947293) B1947293
theorem B1298225 : Blo 864565 1298225 := bstep (se 2 (by rfl) ⟨486834, by rfl⟩ : syracuseStep 1298225 = 973669) B973669
theorem B1232705 : Blo 864565 1232705 := bstep (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) B924529
theorem B1298243 : Blo 864565 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B1462097 : Blo 864565 1462097 := bstep (se 2 (by rfl) ⟨548286, by rfl⟩ : syracuseStep 1462097 = 1096573) B1096573
theorem B1429331 : Blo 864565 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B1298273 : Blo 864565 1298273 := bstep (se 2 (by rfl) ⟨486852, by rfl⟩ : syracuseStep 1298273 = 973705) B973705
theorem B1757027 : Blo 864565 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B2084707 : Blo 864565 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B1298291 : Blo 864565 1298291 := bstep (se 1 (by rfl) ⟨973718, by rfl⟩ : syracuseStep 1298291 = 1947437) B1947437
theorem B1298321 : Blo 864565 1298321 := bstep (se 2 (by rfl) ⟨486870, by rfl⟩ : syracuseStep 1298321 = 973741) B973741
theorem B1298339 : Blo 864565 1298339 := bstep (se 1 (by rfl) ⟨973754, by rfl⟩ : syracuseStep 1298339 = 1947509) B1947509
theorem B1298369 : Blo 864565 1298369 := bstep (se 2 (by rfl) ⟨486888, by rfl⟩ : syracuseStep 1298369 = 973777) B973777
theorem B1462225 : Blo 864565 1462225 := bstep (se 2 (by rfl) ⟨548334, by rfl⟩ : syracuseStep 1462225 = 1096669) B1096669
theorem B1298387 : Blo 864565 1298387 := bstep (se 1 (by rfl) ⟨973790, by rfl⟩ : syracuseStep 1298387 = 1947581) B1947581
theorem B1298417 : Blo 864565 1298417 := bstep (se 2 (by rfl) ⟨486906, by rfl⟩ : syracuseStep 1298417 = 973813) B973813
theorem B1462259 : Blo 864565 1462259 := bstep (se 1 (by rfl) ⟨1096694, by rfl⟩ : syracuseStep 1462259 = 2193389) B2193389
theorem B1298435 : Blo 864565 1298435 := bstep (se 1 (by rfl) ⟨973826, by rfl⟩ : syracuseStep 1298435 = 1947653) B1947653
theorem B1953809 : Blo 864565 1953809 := bstep (se 2 (by rfl) ⟨732678, by rfl⟩ : syracuseStep 1953809 = 1465357) B1465357
theorem B1298465 : Blo 864565 1298465 := bstep (se 2 (by rfl) ⟨486924, by rfl⟩ : syracuseStep 1298465 = 973849) B973849
theorem B2969635 : Blo 864565 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1953827 : Blo 864565 1953827 := bstep (se 1 (by rfl) ⟨1465370, by rfl⟩ : syracuseStep 1953827 = 2930741) B2930741
theorem B1298483 : Blo 864565 1298483 := bstep (se 1 (by rfl) ⟨973862, by rfl⟩ : syracuseStep 1298483 = 1947725) B1947725
theorem B1298513 : Blo 864565 1298513 := bstep (se 2 (by rfl) ⟨486942, by rfl⟩ : syracuseStep 1298513 = 973885) B973885
theorem B1298531 : Blo 864565 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B1462387 : Blo 864565 1462387 := bstep (se 1 (by rfl) ⟨1096790, by rfl⟩ : syracuseStep 1462387 = 2193581) B2193581
theorem B1298561 : Blo 864565 1298561 := bstep (se 2 (by rfl) ⟨486960, by rfl⟩ : syracuseStep 1298561 = 973921) B973921
theorem B1298579 : Blo 864565 1298579 := bstep (se 1 (by rfl) ⟨973934, by rfl⟩ : syracuseStep 1298579 = 1947869) B1947869
theorem B1298609 : Blo 864565 1298609 := bstep (se 2 (by rfl) ⟨486978, by rfl⟩ : syracuseStep 1298609 = 973957) B973957
theorem B1298627 : Blo 864565 1298627 := bstep (se 1 (by rfl) ⟨973970, by rfl⟩ : syracuseStep 1298627 = 1947941) B1947941
theorem B1298657 : Blo 864565 1298657 := bstep (se 2 (by rfl) ⟨486996, by rfl⟩ : syracuseStep 1298657 = 973993) B973993
theorem B11096291 : Blo 864565 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B1298675 : Blo 864565 1298675 := bstep (se 1 (by rfl) ⟨974006, by rfl⟩ : syracuseStep 1298675 = 1948013) B1948013
theorem B1462529 : Blo 864565 1462529 := bstep (se 2 (by rfl) ⟨548448, by rfl⟩ : syracuseStep 1462529 = 1096897) B1096897
theorem B1298705 : Blo 864565 1298705 := bstep (se 2 (by rfl) ⟨487014, by rfl⟩ : syracuseStep 1298705 = 974029) B974029
theorem B1069331 : Blo 864565 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B1298723 : Blo 864565 1298723 := bstep (se 1 (by rfl) ⟨974042, by rfl⟩ : syracuseStep 1298723 = 1948085) B1948085
theorem B1954097 : Blo 864565 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B1298753 : Blo 864565 1298753 := bstep (se 2 (by rfl) ⟨487032, by rfl⟩ : syracuseStep 1298753 = 974065) B974065
theorem B1954115 : Blo 864565 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B1298771 : Blo 864565 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B1233235 : Blo 864565 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B2347373 : Blo 864565 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B1298801 : Blo 864565 1298801 := bstep (se 2 (by rfl) ⟨487050, by rfl⟩ : syracuseStep 1298801 = 974101) B974101
theorem B1462657 : Blo 864565 1462657 := bstep (se 2 (by rfl) ⟨548496, by rfl⟩ : syracuseStep 1462657 = 1096993) B1096993
theorem B1298819 : Blo 864565 1298819 := bstep (se 1 (by rfl) ⟨974114, by rfl⟩ : syracuseStep 1298819 = 1948229) B1948229
theorem B4379021 : Blo 864565 4379021 := bstep (se 3 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 4379021 = 1642133) B1642133
theorem B1298849 : Blo 864565 1298849 := bstep (se 2 (by rfl) ⟨487068, by rfl⟩ : syracuseStep 1298849 = 974137) B974137
theorem B1462691 : Blo 864565 1462691 := bstep (se 1 (by rfl) ⟨1097018, by rfl⟩ : syracuseStep 1462691 = 2194037) B2194037
theorem B1298867 : Blo 864565 1298867 := bstep (se 1 (by rfl) ⟨974150, by rfl⟩ : syracuseStep 1298867 = 1948301) B1948301
theorem B1298897 : Blo 864565 1298897 := bstep (se 2 (by rfl) ⟨487086, by rfl⟩ : syracuseStep 1298897 = 974173) B974173
theorem B1298915 : Blo 864565 1298915 := bstep (se 1 (by rfl) ⟨974186, by rfl⟩ : syracuseStep 1298915 = 1948373) B1948373
theorem B1298945 : Blo 864565 1298945 := bstep (se 2 (by rfl) ⟨487104, by rfl⟩ : syracuseStep 1298945 = 974209) B974209
theorem B1298963 : Blo 864565 1298963 := bstep (se 1 (by rfl) ⟨974222, by rfl⟩ : syracuseStep 1298963 = 1948445) B1948445
theorem B1462819 : Blo 864565 1462819 := bstep (se 1 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 1462819 = 2194229) B2194229
theorem B1298993 : Blo 864565 1298993 := bstep (se 2 (by rfl) ⟨487122, by rfl⟩ : syracuseStep 1298993 = 974245) B974245
theorem B4936241 : Blo 864565 4936241 := bstep (se 2 (by rfl) ⟨1851090, by rfl⟩ : syracuseStep 4936241 = 3702181) B3702181
theorem B1299011 : Blo 864565 1299011 := bstep (se 1 (by rfl) ⟨974258, by rfl⟩ : syracuseStep 1299011 = 1948517) B1948517
theorem B1299041 : Blo 864565 1299041 := bstep (se 2 (by rfl) ⟨487140, by rfl⟩ : syracuseStep 1299041 = 974281) B974281
theorem B1299059 : Blo 864565 1299059 := bstep (se 1 (by rfl) ⟨974294, by rfl⟩ : syracuseStep 1299059 = 1948589) B1948589
theorem B1299089 : Blo 864565 1299089 := bstep (se 2 (by rfl) ⟨487158, by rfl⟩ : syracuseStep 1299089 = 974317) B974317
theorem B1299107 : Blo 864565 1299107 := bstep (se 1 (by rfl) ⟨974330, by rfl⟩ : syracuseStep 1299107 = 1948661) B1948661
theorem B1233571 : Blo 864565 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B1462961 : Blo 864565 1462961 := bstep (se 2 (by rfl) ⟨548610, by rfl⟩ : syracuseStep 1462961 = 1097221) B1097221
theorem B1299137 : Blo 864565 1299137 := bstep (se 2 (by rfl) ⟨487176, by rfl⟩ : syracuseStep 1299137 = 974353) B974353
theorem B5558989 : Blo 864565 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B1299155 : Blo 864565 1299155 := bstep (se 1 (by rfl) ⟨974366, by rfl⟩ : syracuseStep 1299155 = 1948733) B1948733
theorem B1299185 : Blo 864565 1299185 := bstep (se 2 (by rfl) ⟨487194, by rfl⟩ : syracuseStep 1299185 = 974389) B974389
theorem B1299203 : Blo 864565 1299203 := bstep (se 1 (by rfl) ⟨974402, by rfl⟩ : syracuseStep 1299203 = 1948805) B1948805
theorem B1299233 : Blo 864565 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B1463089 : Blo 864565 1463089 := bstep (se 2 (by rfl) ⟨548658, by rfl⟩ : syracuseStep 1463089 = 1097317) B1097317
theorem B1299251 : Blo 864565 1299251 := bstep (se 1 (by rfl) ⟨974438, by rfl⟩ : syracuseStep 1299251 = 1948877) B1948877
theorem B1299281 : Blo 864565 1299281 := bstep (se 2 (by rfl) ⟨487230, by rfl⟩ : syracuseStep 1299281 = 974461) B974461
theorem B1463123 : Blo 864565 1463123 := bstep (se 1 (by rfl) ⟨1097342, by rfl⟩ : syracuseStep 1463123 = 2194685) B2194685
theorem B1299299 : Blo 864565 1299299 := bstep (se 1 (by rfl) ⟨974474, by rfl⟩ : syracuseStep 1299299 = 1948949) B1948949
theorem B2085745 : Blo 864565 2085745 := bstep (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) B1564309
theorem B1299329 : Blo 864565 1299329 := bstep (se 2 (by rfl) ⟨487248, by rfl⟩ : syracuseStep 1299329 = 974497) B974497
theorem B1299347 : Blo 864565 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B1299377 : Blo 864565 1299377 := bstep (se 2 (by rfl) ⟨487266, by rfl⟩ : syracuseStep 1299377 = 974533) B974533
theorem B1299395 : Blo 864565 1299395 := bstep (se 1 (by rfl) ⟨974546, by rfl⟩ : syracuseStep 1299395 = 1949093) B1949093
theorem B1463251 : Blo 864565 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B1299425 : Blo 864565 1299425 := bstep (se 2 (by rfl) ⟨487284, by rfl⟩ : syracuseStep 1299425 = 974569) B974569
theorem B2773997 : Blo 864565 2773997 := bstep (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) B1040249
theorem B1299443 : Blo 864565 1299443 := bstep (se 1 (by rfl) ⟨974582, by rfl⟩ : syracuseStep 1299443 = 1949165) B1949165
theorem B1299473 : Blo 864565 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B1299491 : Blo 864565 1299491 := bstep (se 1 (by rfl) ⟨974618, by rfl⟩ : syracuseStep 1299491 = 1949237) B1949237
theorem B1299521 : Blo 864565 1299521 := bstep (se 2 (by rfl) ⟨487320, by rfl⟩ : syracuseStep 1299521 = 974641) B974641
theorem B1299539 : Blo 864565 1299539 := bstep (se 1 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 1299539 = 1949309) B1949309
theorem B1463393 : Blo 864565 1463393 := bstep (se 2 (by rfl) ⟨548772, by rfl⟩ : syracuseStep 1463393 = 1097545) B1097545
theorem B1299569 : Blo 864565 1299569 := bstep (se 2 (by rfl) ⟨487338, by rfl⟩ : syracuseStep 1299569 = 974677) B974677
theorem B1299587 : Blo 864565 1299587 := bstep (se 1 (by rfl) ⟨974690, by rfl⟩ : syracuseStep 1299587 = 1949381) B1949381
theorem B1299617 : Blo 864565 1299617 := bstep (se 2 (by rfl) ⟨487356, by rfl⟩ : syracuseStep 1299617 = 974713) B974713
theorem B1299635 : Blo 864565 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B1299665 : Blo 864565 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B1234129 : Blo 864565 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B1463521 : Blo 864565 1463521 := bstep (se 2 (by rfl) ⟨548820, by rfl⟩ : syracuseStep 1463521 = 1097641) B1097641
theorem B1299683 : Blo 864565 1299683 := bstep (se 1 (by rfl) ⟨974762, by rfl⟩ : syracuseStep 1299683 = 1949525) B1949525
theorem B1234163 : Blo 864565 1234163 := bstep (se 1 (by rfl) ⟨925622, by rfl⟩ : syracuseStep 1234163 = 1851245) B1851245
theorem B1299713 : Blo 864565 1299713 := bstep (se 2 (by rfl) ⟨487392, by rfl⟩ : syracuseStep 1299713 = 974785) B974785
theorem B1463555 : Blo 864565 1463555 := bstep (se 1 (by rfl) ⟨1097666, by rfl⟩ : syracuseStep 1463555 = 2195333) B2195333
theorem B1299731 : Blo 864565 1299731 := bstep (se 1 (by rfl) ⟨974798, by rfl⟩ : syracuseStep 1299731 = 1949597) B1949597
theorem B1299761 : Blo 864565 1299761 := bstep (se 2 (by rfl) ⟨487410, by rfl⟩ : syracuseStep 1299761 = 974821) B974821
theorem B1299779 : Blo 864565 1299779 := bstep (se 1 (by rfl) ⟨974834, by rfl⟩ : syracuseStep 1299779 = 1949669) B1949669
theorem B1299809 : Blo 864565 1299809 := bstep (se 2 (by rfl) ⟨487428, by rfl⟩ : syracuseStep 1299809 = 974857) B974857
theorem B1299827 : Blo 864565 1299827 := bstep (se 1 (by rfl) ⟨974870, by rfl⟩ : syracuseStep 1299827 = 1949741) B1949741
theorem B1463683 : Blo 864565 1463683 := bstep (se 1 (by rfl) ⟨1097762, by rfl⟩ : syracuseStep 1463683 = 2195525) B2195525
theorem B47502733 : Blo 864565 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B1299857 : Blo 864565 1299857 := bstep (se 2 (by rfl) ⟨487446, by rfl⟩ : syracuseStep 1299857 = 974893) B974893
theorem B1299875 : Blo 864565 1299875 := bstep (se 1 (by rfl) ⟨974906, by rfl⟩ : syracuseStep 1299875 = 1949813) B1949813
theorem B1299905 : Blo 864565 1299905 := bstep (se 2 (by rfl) ⟨487464, by rfl⟩ : syracuseStep 1299905 = 974929) B974929
theorem B1299923 : Blo 864565 1299923 := bstep (se 1 (by rfl) ⟨974942, by rfl⟩ : syracuseStep 1299923 = 1949885) B1949885
theorem B1299953 : Blo 864565 1299953 := bstep (se 2 (by rfl) ⟨487482, by rfl⟩ : syracuseStep 1299953 = 974965) B974965
theorem B1299971 : Blo 864565 1299971 := bstep (se 1 (by rfl) ⟨974978, by rfl⟩ : syracuseStep 1299971 = 1949957) B1949957
theorem B1463825 : Blo 864565 1463825 := bstep (se 2 (by rfl) ⟨548934, by rfl⟩ : syracuseStep 1463825 = 1097869) B1097869
theorem B1300001 : Blo 864565 1300001 := bstep (se 2 (by rfl) ⟨487500, by rfl⟩ : syracuseStep 1300001 = 975001) B975001
theorem B4216369 : Blo 864565 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B1300019 : Blo 864565 1300019 := bstep (se 1 (by rfl) ⟨975014, by rfl⟩ : syracuseStep 1300019 = 1950029) B1950029
theorem B1300049 : Blo 864565 1300049 := bstep (se 2 (by rfl) ⟨487518, by rfl⟩ : syracuseStep 1300049 = 975037) B975037
theorem B1300067 : Blo 864565 1300067 := bstep (se 1 (by rfl) ⟨975050, by rfl⟩ : syracuseStep 1300067 = 1950101) B1950101
theorem B1300097 : Blo 864565 1300097 := bstep (se 2 (by rfl) ⟨487536, by rfl⟩ : syracuseStep 1300097 = 975073) B975073
theorem B1463953 : Blo 864565 1463953 := bstep (se 2 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 1463953 = 1097965) B1097965
theorem B1300115 : Blo 864565 1300115 := bstep (se 1 (by rfl) ⟨975086, by rfl⟩ : syracuseStep 1300115 = 1950173) B1950173
theorem B1300145 : Blo 864565 1300145 := bstep (se 2 (by rfl) ⟨487554, by rfl⟩ : syracuseStep 1300145 = 975109) B975109
theorem B1463987 : Blo 864565 1463987 := bstep (se 1 (by rfl) ⟨1097990, by rfl⟩ : syracuseStep 1463987 = 2195981) B2195981
theorem B1300163 : Blo 864565 1300163 := bstep (se 1 (by rfl) ⟨975122, by rfl⟩ : syracuseStep 1300163 = 1950245) B1950245
theorem B1300193 : Blo 864565 1300193 := bstep (se 2 (by rfl) ⟨487572, by rfl⟩ : syracuseStep 1300193 = 975145) B975145
theorem B1300211 : Blo 864565 1300211 := bstep (se 1 (by rfl) ⟨975158, by rfl⟩ : syracuseStep 1300211 = 1950317) B1950317
theorem B1300241 : Blo 864565 1300241 := bstep (se 2 (by rfl) ⟨487590, by rfl⟩ : syracuseStep 1300241 = 975181) B975181
theorem B1234721 : Blo 864565 1234721 := bstep (se 2 (by rfl) ⟨463020, by rfl⟩ : syracuseStep 1234721 = 926041) B926041
theorem B1300259 : Blo 864565 1300259 := bstep (se 1 (by rfl) ⟨975194, by rfl⟩ : syracuseStep 1300259 = 1950389) B1950389
theorem B1464115 : Blo 864565 1464115 := bstep (se 1 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 1464115 = 2196173) B2196173
theorem B1300289 : Blo 864565 1300289 := bstep (se 2 (by rfl) ⟨487608, by rfl⟩ : syracuseStep 1300289 = 975217) B975217
theorem B1300307 : Blo 864565 1300307 := bstep (se 1 (by rfl) ⟨975230, by rfl⟩ : syracuseStep 1300307 = 1950461) B1950461
theorem B972643 : Blo 864565 972643 := bstep (se 1 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 972643 = 1458965) B1458965
theorem B2774893 : Blo 864565 2774893 := bstep (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) B1040585
theorem B1300337 : Blo 864565 1300337 := bstep (se 2 (by rfl) ⟨487626, by rfl⟩ : syracuseStep 1300337 = 975253) B975253
theorem B1234801 : Blo 864565 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B1300355 : Blo 864565 1300355 := bstep (se 1 (by rfl) ⟨975266, by rfl⟩ : syracuseStep 1300355 = 1950533) B1950533
theorem B1300385 : Blo 864565 1300385 := bstep (se 2 (by rfl) ⟨487644, by rfl⟩ : syracuseStep 1300385 = 975289) B975289
theorem B1300403 : Blo 864565 1300403 := bstep (se 1 (by rfl) ⟨975302, by rfl⟩ : syracuseStep 1300403 = 1950605) B1950605
theorem B1464257 : Blo 864565 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B1300433 : Blo 864565 1300433 := bstep (se 2 (by rfl) ⟨487662, by rfl⟩ : syracuseStep 1300433 = 975325) B975325
theorem B1300451 : Blo 864565 1300451 := bstep (se 1 (by rfl) ⟨975338, by rfl⟩ : syracuseStep 1300451 = 1950677) B1950677
theorem B4937699 : Blo 864565 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B972787 : Blo 864565 972787 := bstep (se 1 (by rfl) ⟨729590, by rfl⟩ : syracuseStep 972787 = 1459181) B1459181
theorem B1300481 : Blo 864565 1300481 := bstep (se 2 (by rfl) ⟨487680, by rfl⟩ : syracuseStep 1300481 = 975361) B975361
theorem B1300499 : Blo 864565 1300499 := bstep (se 1 (by rfl) ⟨975374, by rfl⟩ : syracuseStep 1300499 = 1950749) B1950749
theorem B1300529 : Blo 864565 1300529 := bstep (se 2 (by rfl) ⟨487698, by rfl⟩ : syracuseStep 1300529 = 975397) B975397
theorem B1464385 : Blo 864565 1464385 := bstep (se 2 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 1464385 = 1098289) B1098289
theorem B1300547 : Blo 864565 1300547 := bstep (se 1 (by rfl) ⟨975410, by rfl⟩ : syracuseStep 1300547 = 1950821) B1950821
theorem B1300577 : Blo 864565 1300577 := bstep (se 2 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 1300577 = 975433) B975433
theorem B1464419 : Blo 864565 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1300595 : Blo 864565 1300595 := bstep (se 1 (by rfl) ⟨975446, by rfl⟩ : syracuseStep 1300595 = 1950893) B1950893
theorem B972931 : Blo 864565 972931 := bstep (se 1 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 972931 = 1459397) B1459397
theorem B1300625 : Blo 864565 1300625 := bstep (se 2 (by rfl) ⟨487734, by rfl⟩ : syracuseStep 1300625 = 975469) B975469
theorem B1300643 : Blo 864565 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B1300673 : Blo 864565 1300673 := bstep (se 2 (by rfl) ⟨487752, by rfl⟩ : syracuseStep 1300673 = 975505) B975505
theorem B1300691 : Blo 864565 1300691 := bstep (se 1 (by rfl) ⟨975518, by rfl⟩ : syracuseStep 1300691 = 1951037) B1951037
theorem B1464547 : Blo 864565 1464547 := bstep (se 1 (by rfl) ⟨1098410, by rfl⟩ : syracuseStep 1464547 = 2196821) B2196821
theorem B1300721 : Blo 864565 1300721 := bstep (se 2 (by rfl) ⟨487770, by rfl⟩ : syracuseStep 1300721 = 975541) B975541
theorem B1300739 : Blo 864565 1300739 := bstep (se 1 (by rfl) ⟨975554, by rfl⟩ : syracuseStep 1300739 = 1951109) B1951109
theorem B1562897 : Blo 864565 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B973075 : Blo 864565 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B1300769 : Blo 864565 1300769 := bstep (se 2 (by rfl) ⟨487788, by rfl⟩ : syracuseStep 1300769 = 975577) B975577
theorem B1300787 : Blo 864565 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B1300817 : Blo 864565 1300817 := bstep (se 2 (by rfl) ⟨487806, by rfl⟩ : syracuseStep 1300817 = 975613) B975613
theorem B1300835 : Blo 864565 1300835 := bstep (se 1 (by rfl) ⟨975626, by rfl⟩ : syracuseStep 1300835 = 1951253) B1951253
theorem B1464689 : Blo 864565 1464689 := bstep (se 2 (by rfl) ⟨549258, by rfl⟩ : syracuseStep 1464689 = 1098517) B1098517
theorem B1300865 : Blo 864565 1300865 := bstep (se 2 (by rfl) ⟨487824, by rfl⟩ : syracuseStep 1300865 = 975649) B975649
theorem B7494029 : Blo 864565 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B1300883 : Blo 864565 1300883 := bstep (se 1 (by rfl) ⟨975662, by rfl⟩ : syracuseStep 1300883 = 1951325) B1951325
theorem B973219 : Blo 864565 973219 := bstep (se 1 (by rfl) ⟨729914, by rfl⟩ : syracuseStep 973219 = 1459829) B1459829
theorem B1300913 : Blo 864565 1300913 := bstep (se 2 (by rfl) ⟨487842, by rfl⟩ : syracuseStep 1300913 = 975685) B975685
theorem B1300931 : Blo 864565 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B1300961 : Blo 864565 1300961 := bstep (se 2 (by rfl) ⟨487860, by rfl⟩ : syracuseStep 1300961 = 975721) B975721
theorem B1464817 : Blo 864565 1464817 := bstep (se 2 (by rfl) ⟨549306, by rfl⟩ : syracuseStep 1464817 = 1098613) B1098613
theorem B1300979 : Blo 864565 1300979 := bstep (se 1 (by rfl) ⟨975734, by rfl⟩ : syracuseStep 1300979 = 1951469) B1951469
theorem B4446733 : Blo 864565 4446733 := bstep (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) B1667525
theorem B1301009 : Blo 864565 1301009 := bstep (se 2 (by rfl) ⟨487878, by rfl⟩ : syracuseStep 1301009 = 975757) B975757
theorem B1464851 : Blo 864565 1464851 := bstep (se 1 (by rfl) ⟨1098638, by rfl⟩ : syracuseStep 1464851 = 2197277) B2197277
theorem B1301027 : Blo 864565 1301027 := bstep (se 1 (by rfl) ⟨975770, by rfl⟩ : syracuseStep 1301027 = 1951541) B1951541
theorem B973363 : Blo 864565 973363 := bstep (se 1 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 973363 = 1460045) B1460045
theorem B1301057 : Blo 864565 1301057 := bstep (se 2 (by rfl) ⟨487896, by rfl⟩ : syracuseStep 1301057 = 975793) B975793
theorem B1301075 : Blo 864565 1301075 := bstep (se 1 (by rfl) ⟨975806, by rfl⟩ : syracuseStep 1301075 = 1951613) B1951613
theorem B1301105 : Blo 864565 1301105 := bstep (se 2 (by rfl) ⟨487914, by rfl⟩ : syracuseStep 1301105 = 975829) B975829
theorem B1301123 : Blo 864565 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B1235587 : Blo 864565 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B13523597 : Blo 864565 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B1464979 : Blo 864565 1464979 := bstep (se 1 (by rfl) ⟨1098734, by rfl⟩ : syracuseStep 1464979 = 2197469) B2197469
theorem B1301153 : Blo 864565 1301153 := bstep (se 2 (by rfl) ⟨487932, by rfl⟩ : syracuseStep 1301153 = 975865) B975865
theorem B1301171 : Blo 864565 1301171 := bstep (se 1 (by rfl) ⟨975878, by rfl⟩ : syracuseStep 1301171 = 1951757) B1951757
theorem B973507 : Blo 864565 973507 := bstep (se 1 (by rfl) ⟨730130, by rfl⟩ : syracuseStep 973507 = 1460261) B1460261
theorem B1301201 : Blo 864565 1301201 := bstep (se 2 (by rfl) ⟨487950, by rfl⟩ : syracuseStep 1301201 = 975901) B975901
theorem B1301219 : Blo 864565 1301219 := bstep (se 1 (by rfl) ⟨975914, by rfl⟩ : syracuseStep 1301219 = 1951829) B1951829
theorem B1301249 : Blo 864565 1301249 := bstep (se 2 (by rfl) ⟨487968, by rfl⟩ : syracuseStep 1301249 = 975937) B975937
theorem B2218769 : Blo 864565 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B1563409 : Blo 864565 1563409 := bstep (se 2 (by rfl) ⟨586278, by rfl⟩ : syracuseStep 1563409 = 1172557) B1172557
theorem B1301267 : Blo 864565 1301267 := bstep (se 1 (by rfl) ⟨975950, by rfl⟩ : syracuseStep 1301267 = 1951901) B1951901
theorem B1465121 : Blo 864565 1465121 := bstep (se 2 (by rfl) ⟨549420, by rfl⟩ : syracuseStep 1465121 = 1098841) B1098841
theorem B1301297 : Blo 864565 1301297 := bstep (se 2 (by rfl) ⟨487986, by rfl⟩ : syracuseStep 1301297 = 975973) B975973
theorem B1301315 : Blo 864565 1301315 := bstep (se 1 (by rfl) ⟨975986, by rfl⟩ : syracuseStep 1301315 = 1951973) B1951973
theorem B973651 : Blo 864565 973651 := bstep (se 1 (by rfl) ⟨730238, by rfl⟩ : syracuseStep 973651 = 1460477) B1460477
theorem B1301345 : Blo 864565 1301345 := bstep (se 2 (by rfl) ⟨488004, by rfl⟩ : syracuseStep 1301345 = 976009) B976009
theorem B7035761 : Blo 864565 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1301363 : Blo 864565 1301363 := bstep (se 1 (by rfl) ⟨976022, by rfl⟩ : syracuseStep 1301363 = 1952045) B1952045
theorem B1039235 : Blo 864565 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B6577037 : Blo 864565 6577037 := bstep (se 3 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 6577037 = 2466389) B2466389
theorem B1301393 : Blo 864565 1301393 := bstep (se 2 (by rfl) ⟨488022, by rfl⟩ : syracuseStep 1301393 = 976045) B976045
theorem B1465249 : Blo 864565 1465249 := bstep (se 2 (by rfl) ⟨549468, by rfl⟩ : syracuseStep 1465249 = 1098937) B1098937
theorem B2775971 : Blo 864565 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B1301411 : Blo 864565 1301411 := bstep (se 1 (by rfl) ⟨976058, by rfl⟩ : syracuseStep 1301411 = 1952117) B1952117
theorem B1301441 : Blo 864565 1301441 := bstep (se 2 (by rfl) ⟨488040, by rfl⟩ : syracuseStep 1301441 = 976081) B976081
theorem B1465283 : Blo 864565 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B1301459 : Blo 864565 1301459 := bstep (se 1 (by rfl) ⟨976094, by rfl⟩ : syracuseStep 1301459 = 1952189) B1952189
theorem B973795 : Blo 864565 973795 := bstep (se 1 (by rfl) ⟨730346, by rfl⟩ : syracuseStep 973795 = 1460693) B1460693
theorem B1301489 : Blo 864565 1301489 := bstep (se 2 (by rfl) ⟨488058, by rfl⟩ : syracuseStep 1301489 = 976117) B976117
theorem B1301507 : Blo 864565 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B5790733 : Blo 864565 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B1301537 : Blo 864565 1301537 := bstep (se 2 (by rfl) ⟨488076, by rfl⟩ : syracuseStep 1301537 = 976153) B976153
theorem B1301555 : Blo 864565 1301555 := bstep (se 1 (by rfl) ⟨976166, by rfl⟩ : syracuseStep 1301555 = 1952333) B1952333
theorem B1465411 : Blo 864565 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B1301585 : Blo 864565 1301585 := bstep (se 2 (by rfl) ⟨488094, by rfl⟩ : syracuseStep 1301585 = 976189) B976189
theorem B1236065 : Blo 864565 1236065 := bstep (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) B927049
theorem B1301603 : Blo 864565 1301603 := bstep (se 1 (by rfl) ⟨976202, by rfl⟩ : syracuseStep 1301603 = 1952405) B1952405
theorem B973939 : Blo 864565 973939 := bstep (se 1 (by rfl) ⟨730454, by rfl⟩ : syracuseStep 973939 = 1460909) B1460909
theorem B1301633 : Blo 864565 1301633 := bstep (se 2 (by rfl) ⟨488112, by rfl⟩ : syracuseStep 1301633 = 976225) B976225
theorem B1301651 : Blo 864565 1301651 := bstep (se 1 (by rfl) ⟨976238, by rfl⟩ : syracuseStep 1301651 = 1952477) B1952477
theorem B5921969 : Blo 864565 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B1301681 : Blo 864565 1301681 := bstep (se 2 (by rfl) ⟨488130, by rfl⟩ : syracuseStep 1301681 = 976261) B976261
theorem B1301699 : Blo 864565 1301699 := bstep (se 1 (by rfl) ⟨976274, by rfl⟩ : syracuseStep 1301699 = 1952549) B1952549
theorem B1465553 : Blo 864565 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B1236179 : Blo 864565 1236179 := bstep (se 1 (by rfl) ⟨927134, by rfl⟩ : syracuseStep 1236179 = 1854269) B1854269
theorem B1301729 : Blo 864565 1301729 := bstep (se 2 (by rfl) ⟨488148, by rfl⟩ : syracuseStep 1301729 = 976297) B976297
theorem B4381937 : Blo 864565 4381937 := bstep (se 2 (by rfl) ⟨1643226, by rfl⟩ : syracuseStep 4381937 = 3286453) B3286453
theorem B1301747 : Blo 864565 1301747 := bstep (se 1 (by rfl) ⟨976310, by rfl⟩ : syracuseStep 1301747 = 1952621) B1952621
theorem B974083 : Blo 864565 974083 := bstep (se 1 (by rfl) ⟨730562, by rfl⟩ : syracuseStep 974083 = 1461125) B1461125
theorem B1301777 : Blo 864565 1301777 := bstep (se 2 (by rfl) ⟨488166, by rfl⟩ : syracuseStep 1301777 = 976333) B976333
theorem B1301795 : Blo 864565 1301795 := bstep (se 1 (by rfl) ⟨976346, by rfl⟩ : syracuseStep 1301795 = 1952693) B1952693
theorem B1236259 : Blo 864565 1236259 := bstep (se 1 (by rfl) ⟨927194, by rfl⟩ : syracuseStep 1236259 = 1854389) B1854389
theorem B1301825 : Blo 864565 1301825 := bstep (se 2 (by rfl) ⟨488184, by rfl⟩ : syracuseStep 1301825 = 976369) B976369
theorem B1465681 : Blo 864565 1465681 := bstep (se 2 (by rfl) ⟨549630, by rfl⟩ : syracuseStep 1465681 = 1099261) B1099261
theorem B1301843 : Blo 864565 1301843 := bstep (se 1 (by rfl) ⟨976382, by rfl⟩ : syracuseStep 1301843 = 1952765) B1952765
theorem B1760611 : Blo 864565 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B1301873 : Blo 864565 1301873 := bstep (se 2 (by rfl) ⟨488202, by rfl⟩ : syracuseStep 1301873 = 976405) B976405
theorem B1301891 : Blo 864565 1301891 := bstep (se 1 (by rfl) ⟨976418, by rfl⟩ : syracuseStep 1301891 = 1952837) B1952837
theorem B974227 : Blo 864565 974227 := bstep (se 1 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 974227 = 1461341) B1461341
theorem B1301921 : Blo 864565 1301921 := bstep (se 2 (by rfl) ⟨488220, by rfl⟩ : syracuseStep 1301921 = 976441) B976441
theorem B1301939 : Blo 864565 1301939 := bstep (se 1 (by rfl) ⟨976454, by rfl⟩ : syracuseStep 1301939 = 1952909) B1952909
theorem B3562957 : Blo 864565 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1301969 : Blo 864565 1301969 := bstep (se 2 (by rfl) ⟨488238, by rfl⟩ : syracuseStep 1301969 = 976477) B976477
theorem B1301987 : Blo 864565 1301987 := bstep (se 1 (by rfl) ⟨976490, by rfl⟩ : syracuseStep 1301987 = 1952981) B1952981
theorem B1302017 : Blo 864565 1302017 := bstep (se 2 (by rfl) ⟨488256, by rfl⟩ : syracuseStep 1302017 = 976513) B976513
theorem B1302035 : Blo 864565 1302035 := bstep (se 1 (by rfl) ⟨976526, by rfl⟩ : syracuseStep 1302035 = 1953053) B1953053
theorem B974371 : Blo 864565 974371 := bstep (se 1 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 974371 = 1461557) B1461557
theorem B2776625 : Blo 864565 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B1302065 : Blo 864565 1302065 := bstep (se 2 (by rfl) ⟨488274, by rfl⟩ : syracuseStep 1302065 = 976549) B976549
theorem B1302083 : Blo 864565 1302083 := bstep (se 1 (by rfl) ⟨976562, by rfl⟩ : syracuseStep 1302083 = 1953125) B1953125
theorem B1302113 : Blo 864565 1302113 := bstep (se 2 (by rfl) ⟨488292, by rfl⟩ : syracuseStep 1302113 = 976585) B976585
theorem B1302131 : Blo 864565 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B1302161 : Blo 864565 1302161 := bstep (se 2 (by rfl) ⟨488310, by rfl⟩ : syracuseStep 1302161 = 976621) B976621
theorem B1302179 : Blo 864565 1302179 := bstep (se 1 (by rfl) ⟨976634, by rfl⟩ : syracuseStep 1302179 = 1953269) B1953269
theorem B974515 : Blo 864565 974515 := bstep (se 1 (by rfl) ⟨730886, by rfl⟩ : syracuseStep 974515 = 1461773) B1461773
theorem B1302209 : Blo 864565 1302209 := bstep (se 2 (by rfl) ⟨488328, by rfl⟩ : syracuseStep 1302209 = 976657) B976657
theorem B1302227 : Blo 864565 1302227 := bstep (se 1 (by rfl) ⟨976670, by rfl⟩ : syracuseStep 1302227 = 1953341) B1953341
theorem B8314609 : Blo 864565 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B1302257 : Blo 864565 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B1302275 : Blo 864565 1302275 := bstep (se 1 (by rfl) ⟨976706, by rfl⟩ : syracuseStep 1302275 = 1953413) B1953413
theorem B1302305 : Blo 864565 1302305 := bstep (se 2 (by rfl) ⟨488364, by rfl⟩ : syracuseStep 1302305 = 976729) B976729
theorem B1302323 : Blo 864565 1302323 := bstep (se 1 (by rfl) ⟨976742, by rfl⟩ : syracuseStep 1302323 = 1953485) B1953485
theorem B974659 : Blo 864565 974659 := bstep (se 1 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 974659 = 1461989) B1461989
theorem B1302353 : Blo 864565 1302353 := bstep (se 2 (by rfl) ⟨488382, by rfl⟩ : syracuseStep 1302353 = 976765) B976765
theorem B1302371 : Blo 864565 1302371 := bstep (se 1 (by rfl) ⟨976778, by rfl⟩ : syracuseStep 1302371 = 1953557) B1953557
theorem B1302401 : Blo 864565 1302401 := bstep (se 2 (by rfl) ⟨488400, by rfl⟩ : syracuseStep 1302401 = 976801) B976801
theorem B1302419 : Blo 864565 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B1302449 : Blo 864565 1302449 := bstep (se 2 (by rfl) ⟨488418, by rfl⟩ : syracuseStep 1302449 = 976837) B976837
theorem B1302467 : Blo 864565 1302467 := bstep (se 1 (by rfl) ⟨976850, by rfl⟩ : syracuseStep 1302467 = 1953701) B1953701
theorem B974803 : Blo 864565 974803 := bstep (se 1 (by rfl) ⟨731102, by rfl⟩ : syracuseStep 974803 = 1462205) B1462205
theorem B1302497 : Blo 864565 1302497 := bstep (se 2 (by rfl) ⟨488436, by rfl⟩ : syracuseStep 1302497 = 976873) B976873
theorem B1302515 : Blo 864565 1302515 := bstep (se 1 (by rfl) ⟨976886, by rfl⟩ : syracuseStep 1302515 = 1953773) B1953773
theorem B1302545 : Blo 864565 1302545 := bstep (se 2 (by rfl) ⟨488454, by rfl⟩ : syracuseStep 1302545 = 976909) B976909
theorem B1302563 : Blo 864565 1302563 := bstep (se 1 (by rfl) ⟨976922, by rfl⟩ : syracuseStep 1302563 = 1953845) B1953845
theorem B1302593 : Blo 864565 1302593 := bstep (se 2 (by rfl) ⟨488472, by rfl⟩ : syracuseStep 1302593 = 976945) B976945
theorem B1302611 : Blo 864565 1302611 := bstep (se 1 (by rfl) ⟨976958, by rfl⟩ : syracuseStep 1302611 = 1953917) B1953917
theorem B974947 : Blo 864565 974947 := bstep (se 1 (by rfl) ⟨731210, by rfl⟩ : syracuseStep 974947 = 1462421) B1462421
theorem B1564771 : Blo 864565 1564771 := bstep (se 1 (by rfl) ⟨1173578, by rfl⟩ : syracuseStep 1564771 = 2347157) B2347157
theorem B1302641 : Blo 864565 1302641 := bstep (se 2 (by rfl) ⟨488490, by rfl⟩ : syracuseStep 1302641 = 976981) B976981
theorem B1302659 : Blo 864565 1302659 := bstep (se 1 (by rfl) ⟨976994, by rfl⟩ : syracuseStep 1302659 = 1953989) B1953989
theorem B3694733 : Blo 864565 3694733 := bstep (se 3 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 3694733 = 1385525) B1385525
theorem B1302689 : Blo 864565 1302689 := bstep (se 2 (by rfl) ⟨488508, by rfl⟩ : syracuseStep 1302689 = 977017) B977017
theorem B1302707 : Blo 864565 1302707 := bstep (se 1 (by rfl) ⟨977030, by rfl⟩ : syracuseStep 1302707 = 1954061) B1954061
theorem B1302737 : Blo 864565 1302737 := bstep (se 2 (by rfl) ⟨488526, by rfl⟩ : syracuseStep 1302737 = 977053) B977053
theorem B1302755 : Blo 864565 1302755 := bstep (se 1 (by rfl) ⟨977066, by rfl⟩ : syracuseStep 1302755 = 1954133) B1954133
theorem B975091 : Blo 864565 975091 := bstep (se 1 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 975091 = 1462637) B1462637
theorem B1302785 : Blo 864565 1302785 := bstep (se 2 (by rfl) ⟨488544, by rfl⟩ : syracuseStep 1302785 = 977089) B977089
theorem B1302803 : Blo 864565 1302803 := bstep (se 1 (by rfl) ⟨977102, by rfl⟩ : syracuseStep 1302803 = 1954205) B1954205
theorem B1302833 : Blo 864565 1302833 := bstep (se 2 (by rfl) ⟨488562, by rfl⟩ : syracuseStep 1302833 = 977125) B977125
theorem B975235 : Blo 864565 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B975379 : Blo 864565 975379 := bstep (se 1 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 975379 = 1463069) B1463069
theorem B4383395 : Blo 864565 4383395 := bstep (se 1 (by rfl) ⟨3287546, by rfl⟩ : syracuseStep 4383395 = 6575093) B6575093
theorem B975523 : Blo 864565 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B975667 : Blo 864565 975667 := bstep (se 1 (by rfl) ⟨731750, by rfl⟩ : syracuseStep 975667 = 1463501) B1463501
theorem B2777969 : Blo 864565 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B975811 : Blo 864565 975811 := bstep (se 1 (by rfl) ⟨731858, by rfl⟩ : syracuseStep 975811 = 1463717) B1463717
theorem B1172561 : Blo 864565 1172561 := bstep (se 2 (by rfl) ⟨439710, by rfl⟩ : syracuseStep 1172561 = 879421) B879421
theorem B975955 : Blo 864565 975955 := bstep (se 1 (by rfl) ⟨731966, by rfl⟩ : syracuseStep 975955 = 1463933) B1463933
theorem B976099 : Blo 864565 976099 := bstep (se 1 (by rfl) ⟨732074, by rfl⟩ : syracuseStep 976099 = 1464149) B1464149
theorem B2188529 : Blo 864565 2188529 := bstep (se 2 (by rfl) ⟨820698, by rfl⟩ : syracuseStep 2188529 = 1641397) B1641397
theorem B7496945 : Blo 864565 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B2188579 : Blo 864565 2188579 := bstep (se 1 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 2188579 = 3282869) B3282869
theorem B976243 : Blo 864565 976243 := bstep (se 1 (by rfl) ⟨732182, by rfl⟩ : syracuseStep 976243 = 1464365) B1464365
theorem B2188721 : Blo 864565 2188721 := bstep (se 2 (by rfl) ⟨820770, by rfl⟩ : syracuseStep 2188721 = 1641541) B1641541
theorem B4384205 : Blo 864565 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B976387 : Blo 864565 976387 := bstep (se 1 (by rfl) ⟨732290, by rfl⟩ : syracuseStep 976387 = 1464581) B1464581
theorem B1042003 : Blo 864565 1042003 := bstep (se 1 (by rfl) ⟨781502, by rfl⟩ : syracuseStep 1042003 = 1563005) B1563005
theorem B976531 : Blo 864565 976531 := bstep (se 1 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 976531 = 1464797) B1464797
theorem B6579953 : Blo 864565 6579953 := bstep (se 2 (by rfl) ⟨2467482, by rfl⟩ : syracuseStep 6579953 = 4934965) B4934965
theorem B976675 : Blo 864565 976675 := bstep (se 1 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 976675 = 1465013) B1465013
theorem B1173379 : Blo 864565 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B976819 : Blo 864565 976819 := bstep (se 1 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 976819 = 1465229) B1465229
theorem B2779085 : Blo 864565 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B976963 : Blo 864565 976963 := bstep (se 1 (by rfl) ⟨732722, by rfl⟩ : syracuseStep 976963 = 1465445) B1465445
theorem B2779267 : Blo 864565 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B977107 : Blo 864565 977107 := bstep (se 1 (by rfl) ⟨732830, by rfl⟩ : syracuseStep 977107 = 1465661) B1465661
theorem B5335301 : Blo 864565 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B878899 : Blo 864565 878899 := bstep (se 1 (by rfl) ⟨659174, by rfl⟩ : syracuseStep 878899 = 1318349) B1318349
theorem B2189713 : Blo 864565 2189713 := bstep (se 2 (by rfl) ⟨821142, by rfl⟩ : syracuseStep 2189713 = 1642285) B1642285
theorem B2812429 : Blo 864565 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B2189987 : Blo 864565 2189987 := bstep (se 1 (by rfl) ⟨1642490, by rfl⟩ : syracuseStep 2189987 = 3284981) B3284981
theorem B59894549 : Blo 864565 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B7400261 : Blo 864565 7400261 := bstep (se 4 (by rfl) ⟨693774, by rfl⟩ : syracuseStep 7400261 = 1387549) B1387549
theorem B2190179 : Blo 864565 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B5630917 : Blo 864565 5630917 := bstep (se 4 (by rfl) ⟨527898, by rfl⟩ : syracuseStep 5630917 = 1055797) B1055797
theorem B2780173 : Blo 864565 2780173 := bstep (se 3 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 2780173 = 1042565) B1042565
theorem B5139533 : Blo 864565 5139533 := bstep (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) B1927325
theorem B2223409 : Blo 864565 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B3010097 : Blo 864565 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B1109651 : Blo 864565 1109651 := bstep (se 1 (by rfl) ⟨832238, by rfl⟩ : syracuseStep 1109651 = 1664477) B1664477
theorem B2191121 : Blo 864565 2191121 := bstep (se 2 (by rfl) ⟨821670, by rfl⟩ : syracuseStep 2191121 = 1643341) B1643341
theorem B2191171 : Blo 864565 2191171 := bstep (se 1 (by rfl) ⟨1643378, by rfl⟩ : syracuseStep 2191171 = 3286757) B3286757
theorem B2191313 : Blo 864565 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B4387121 : Blo 864565 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B3699107 : Blo 864565 3699107 := bstep (se 1 (by rfl) ⟨2774330, by rfl⟩ : syracuseStep 3699107 = 5548661) B5548661
theorem B2781955 : Blo 864565 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B2782019 : Blo 864565 2782019 := bstep (se 1 (by rfl) ⟨2086514, by rfl⟩ : syracuseStep 2782019 = 4173029) B4173029
theorem B2782097 : Blo 864565 2782097 := bstep (se 2 (by rfl) ⟨1043286, by rfl⟩ : syracuseStep 2782097 = 2086573) B2086573
theorem B2192305 : Blo 864565 2192305 := bstep (se 2 (by rfl) ⟨822114, by rfl⟩ : syracuseStep 2192305 = 1644229) B1644229
theorem B5632973 : Blo 864565 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B2192579 : Blo 864565 2192579 := bstep (se 1 (by rfl) ⟨1644434, by rfl⟩ : syracuseStep 2192579 = 3288869) B3288869
theorem B2192771 : Blo 864565 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B4388579 : Blo 864565 4388579 := bstep (se 1 (by rfl) ⟨3291434, by rfl⟩ : syracuseStep 4388579 = 6582869) B6582869
theorem B3700849 : Blo 864565 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B2193713 : Blo 864565 2193713 := bstep (se 2 (by rfl) ⟨822642, by rfl⟩ : syracuseStep 2193713 = 1645285) B1645285
theorem B2193763 : Blo 864565 2193763 := bstep (se 1 (by rfl) ⟨1645322, by rfl⟩ : syracuseStep 2193763 = 3290645) B3290645
theorem B2193905 : Blo 864565 2193905 := bstep (se 2 (by rfl) ⟨822714, by rfl⟩ : syracuseStep 2193905 = 1645429) B1645429
theorem B4389389 : Blo 864565 4389389 := bstep (se 3 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 4389389 = 1646021) B1646021
theorem B15039029 : Blo 864565 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B4946629 : Blo 864565 4946629 := bstep (se 4 (by rfl) ⟨463746, by rfl⟩ : syracuseStep 4946629 = 927493) B927493
theorem B4062221 : Blo 864565 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B2849869 : Blo 864565 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B2784397 : Blo 864565 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B2194897 : Blo 864565 2194897 := bstep (se 2 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 2194897 = 1646173) B1646173
theorem B2195171 : Blo 864565 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B950131 : Blo 864565 950131 := bstep (se 1 (by rfl) ⟨712598, by rfl⟩ : syracuseStep 950131 = 1425197) B1425197
theorem B2195363 : Blo 864565 2195363 := bstep (se 1 (by rfl) ⟨1646522, by rfl⟩ : syracuseStep 2195363 = 3293045) B3293045
theorem B4161611 : Blo 864565 4161611 := bstep (se 1 (by rfl) ⟨3121208, by rfl⟩ : syracuseStep 4161611 = 6242417) B6242417
theorem B2195545 : Blo 864565 2195545 := bstep (se 2 (by rfl) ⟨823329, by rfl⟩ : syracuseStep 2195545 = 1646659) B1646659
theorem B6685249 : Blo 864565 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B10551883 : Blo 864565 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B4162265 : Blo 864565 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B2851549 : Blo 864565 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B16646897 : Blo 864565 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B4391981 : Blo 864565 4391981 := bstep (se 3 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 4391981 = 1646993) B1646993
theorem B2196659 : Blo 864565 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B2196953 : Blo 864565 2196953 := bstep (se 2 (by rfl) ⟨823857, by rfl⟩ : syracuseStep 2196953 = 1647715) B1647715
theorem B2918105 : Blo 864565 2918105 := bstep (se 2 (by rfl) ⟨1094289, by rfl⟩ : syracuseStep 2918105 = 2188579) B2188579
theorem B20023139 : Blo 864565 20023139 := bstep (se 1 (by rfl) ⟨15017354, by rfl⟩ : syracuseStep 20023139 = 30034709) B30034709
theorem B2918807 : Blo 864565 2918807 := bstep (se 1 (by rfl) ⟨2189105, by rfl⟩ : syracuseStep 2918807 = 4378211) B4378211
theorem B11274713 : Blo 864565 11274713 := bstep (se 2 (by rfl) ⟨4228017, by rfl⟩ : syracuseStep 11274713 = 8456035) B8456035
theorem B7408259 : Blo 864565 7408259 := bstep (se 1 (by rfl) ⟨5556194, by rfl⟩ : syracuseStep 7408259 = 11112389) B11112389
theorem B3705689 : Blo 864565 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B1248151 : Blo 864565 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B2919347 : Blo 864565 2919347 := bstep (se 1 (by rfl) ⟨2189510, by rfl⟩ : syracuseStep 2919347 = 4379021) B4379021
theorem B1248215 : Blo 864565 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B2919617 : Blo 864565 2919617 := bstep (se 2 (by rfl) ⟨1094856, by rfl⟩ : syracuseStep 2919617 = 2189713) B2189713
theorem B14814737 : Blo 864565 14814737 := bstep (se 2 (by rfl) ⟨5555526, by rfl⟩ : syracuseStep 14814737 = 11111053) B11111053
theorem B1642187 : Blo 864565 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B986827 : Blo 864565 986827 := bstep (se 1 (by rfl) ⟨740120, by rfl⟩ : syracuseStep 986827 = 1480241) B1480241
theorem B2920157 : Blo 864565 2920157 := bstep (se 3 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 2920157 = 1095059) B1095059
theorem B4329281 : Blo 864565 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B1642369 : Blo 864565 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B7507889 : Blo 864565 7507889 := bstep (se 2 (by rfl) ⟨2815458, by rfl⟩ : syracuseStep 7507889 = 5630917) B5630917
theorem B3706897 : Blo 864565 3706897 := bstep (se 2 (by rfl) ⟨1390086, by rfl⟩ : syracuseStep 3706897 = 2780173) B2780173
theorem B1642817 : Blo 864565 1642817 := bstep (se 2 (by rfl) ⟨616056, by rfl⟩ : syracuseStep 1642817 = 1232113) B1232113
theorem B15012161 : Blo 864565 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B9015731 : Blo 864565 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B1479179 : Blo 864565 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B15012427 : Blo 864565 15012427 := bstep (se 1 (by rfl) ⟨11259320, by rfl⟩ : syracuseStep 15012427 = 22518641) B22518641
theorem B4690507 : Blo 864565 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1643159 : Blo 864565 1643159 := bstep (se 1 (by rfl) ⟨1232369, by rfl⟩ : syracuseStep 1643159 = 2464739) B2464739
theorem B1315531 : Blo 864565 1315531 := bstep (se 1 (by rfl) ⟨986648, by rfl⟩ : syracuseStep 1315531 = 1973297) B1973297
theorem B4166417 : Blo 864565 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B2921291 : Blo 864565 2921291 := bstep (se 1 (by rfl) ⟨2190968, by rfl⟩ : syracuseStep 2921291 = 4381937) B4381937
theorem B4395869 : Blo 864565 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B7410649 : Blo 864565 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B2921561 : Blo 864565 2921561 := bstep (se 2 (by rfl) ⟨1095585, by rfl⟩ : syracuseStep 2921561 = 2191171) B2191171
theorem B1643827 : Blo 864565 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B2463041 : Blo 864565 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B2463155 : Blo 864565 2463155 := bstep (se 1 (by rfl) ⟨1847366, by rfl⟩ : syracuseStep 2463155 = 3694733) B3694733
theorem B988619 : Blo 864565 988619 := bstep (se 1 (by rfl) ⟨741464, by rfl⟩ : syracuseStep 988619 = 1482929) B1482929
theorem B1644275 : Blo 864565 1644275 := bstep (se 1 (by rfl) ⟨1233206, by rfl⟩ : syracuseStep 1644275 = 2466413) B2466413
theorem B2922263 : Blo 864565 2922263 := bstep (se 1 (by rfl) ⟨2191697, by rfl⟩ : syracuseStep 2922263 = 4383395) B4383395
theorem B1644313 : Blo 864565 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B3282839 : Blo 864565 3282839 := bstep (se 1 (by rfl) ⟨2462129, by rfl⟩ : syracuseStep 3282839 = 4924259) B4924259
theorem B7411607 : Blo 864565 7411607 := bstep (se 1 (by rfl) ⟨5558705, by rfl⟩ : syracuseStep 7411607 = 11117411) B11117411
theorem B3283037 : Blo 864565 3283037 := bstep (se 3 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 3283037 = 1231139) B1231139
theorem B1644761 : Blo 864565 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B7411985 : Blo 864565 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B2922803 : Blo 864565 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B2496833 : Blo 864565 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B3709273 : Blo 864565 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B2923073 : Blo 864565 2923073 := bstep (se 2 (by rfl) ⟨1096152, by rfl⟩ : syracuseStep 2923073 = 2192305) B2192305
theorem B924247 : Blo 864565 924247 := bstep (se 1 (by rfl) ⟨693185, by rfl⟩ : syracuseStep 924247 = 1386371) B1386371
theorem B11836277 : Blo 864565 11836277 := bstep (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) B1109651
theorem B1645505 : Blo 864565 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B2923613 : Blo 864565 2923613 := bstep (se 3 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 2923613 = 1096355) B1096355
theorem B1645771 : Blo 864565 1645771 := bstep (se 1 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 1645771 = 2468657) B2468657
theorem B1973555 : Blo 864565 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B925067 : Blo 864565 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B1646219 : Blo 864565 1646219 := bstep (se 1 (by rfl) ⟨1234664, by rfl⟩ : syracuseStep 1646219 = 2469329) B2469329
theorem B2006731 : Blo 864565 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B1646401 : Blo 864565 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B3284995 : Blo 864565 3284995 := bstep (se 1 (by rfl) ⟨2463746, by rfl⟩ : syracuseStep 3284995 = 4927493) B4927493
theorem B1318999 : Blo 864565 1318999 := bstep (se 1 (by rfl) ⟨989249, by rfl⟩ : syracuseStep 1318999 = 1978499) B1978499
theorem B3809369 : Blo 864565 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B1646743 : Blo 864565 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B2924747 : Blo 864565 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B13705421 : Blo 864565 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B1974539 : Blo 864565 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B2466071 : Blo 864565 2466071 := bstep (se 1 (by rfl) ⟨1849553, by rfl⟩ : syracuseStep 2466071 = 3699107) B3699107
theorem B3285299 : Blo 864565 3285299 := bstep (se 1 (by rfl) ⟨2463974, by rfl⟩ : syracuseStep 3285299 = 4927949) B4927949
theorem B1646963 : Blo 864565 1646963 := bstep (se 1 (by rfl) ⟨1235222, by rfl⟩ : syracuseStep 1646963 = 2470445) B2470445
theorem B1974721 : Blo 864565 1974721 := bstep (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) B1481041
theorem B2925017 : Blo 864565 2925017 := bstep (se 2 (by rfl) ⟨1096881, by rfl⟩ : syracuseStep 2925017 = 2193763) B2193763
theorem B926263 : Blo 864565 926263 := bstep (se 1 (by rfl) ⟨694697, by rfl⟩ : syracuseStep 926263 = 1389395) B1389395
theorem B1647191 : Blo 864565 1647191 := bstep (se 1 (by rfl) ⟨1235393, by rfl⟩ : syracuseStep 1647191 = 2470787) B2470787
theorem B1647449 : Blo 864565 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B926635 : Blo 864565 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B6595505 : Blo 864565 6595505 := bstep (se 2 (by rfl) ⟨2473314, by rfl⟩ : syracuseStep 6595505 = 4946629) B4946629
theorem B3285953 : Blo 864565 3285953 := bstep (se 2 (by rfl) ⟨1232232, by rfl⟩ : syracuseStep 3285953 = 2464465) B2464465
theorem B2925719 : Blo 864565 2925719 := bstep (se 1 (by rfl) ⟨2194289, by rfl⟩ : syracuseStep 2925719 = 4388579) B4388579
theorem B1647859 : Blo 864565 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B927083 : Blo 864565 927083 := bstep (se 1 (by rfl) ⟨695312, by rfl⟩ : syracuseStep 927083 = 1390625) B1390625
theorem B11085173 : Blo 864565 11085173 := bstep (se 5 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 11085173 = 1039235) B1039235
theorem B3712529 : Blo 864565 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B2631257 : Blo 864565 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B2926259 : Blo 864565 2926259 := bstep (se 1 (by rfl) ⟨2194694, by rfl⟩ : syracuseStep 2926259 = 4389389) B4389389
theorem B1648345 : Blo 864565 1648345 := bstep (se 2 (by rfl) ⟨618129, by rfl⟩ : syracuseStep 1648345 = 1236259) B1236259
theorem B4925285 : Blo 864565 4925285 := bstep (se 4 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 4925285 = 923491) B923491
theorem B2926529 : Blo 864565 2926529 := bstep (se 2 (by rfl) ⟨1097448, by rfl⟩ : syracuseStep 2926529 = 2194897) B2194897
theorem B3287213 : Blo 864565 3287213 := bstep (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) B1232705
theorem B3287243 : Blo 864565 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B3811549 : Blo 864565 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B1648907 : Blo 864565 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B11086145 : Blo 864565 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B2927069 : Blo 864565 2927069 := bstep (se 3 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 2927069 = 1097651) B1097651
theorem B2468531 : Blo 864565 2468531 := bstep (se 1 (by rfl) ⟨1851398, by rfl⟩ : syracuseStep 2468531 = 3702797) B3702797
theorem B3287897 : Blo 864565 3287897 := bstep (se 2 (by rfl) ⟨1232961, by rfl⟩ : syracuseStep 3287897 = 2465923) B2465923
theorem B1977203 : Blo 864565 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B1977331 : Blo 864565 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B2337815 : Blo 864565 2337815 := bstep (se 1 (by rfl) ⟨1753361, by rfl⟩ : syracuseStep 2337815 = 3506723) B3506723
theorem B3288215 : Blo 864565 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B4172951 : Blo 864565 4172951 := bstep (se 1 (by rfl) ⟨3129713, by rfl⟩ : syracuseStep 4172951 = 6259427) B6259427
theorem B13348081 : Blo 864565 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B1388107 : Blo 864565 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B2928203 : Blo 864565 2928203 := bstep (se 1 (by rfl) ⟨2196152, by rfl⟩ : syracuseStep 2928203 = 4392305) B4392305
theorem B1846871 : Blo 864565 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B7024279 : Blo 864565 7024279 := bstep (se 1 (by rfl) ⟨5268209, by rfl⟩ : syracuseStep 7024279 = 10536419) B10536419
theorem B1945331 : Blo 864565 1945331 := bstep (se 1 (by rfl) ⟨1458998, by rfl⟩ : syracuseStep 1945331 = 2917997) B2917997
theorem B1945367 : Blo 864565 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B3288883 : Blo 864565 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B1978187 : Blo 864565 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B2928473 : Blo 864565 2928473 := bstep (se 2 (by rfl) ⟨1098177, by rfl⟩ : syracuseStep 2928473 = 2196355) B2196355
theorem B1945547 : Blo 864565 1945547 := bstep (se 1 (by rfl) ⟨1459160, by rfl⟩ : syracuseStep 1945547 = 2918321) B2918321
theorem B1945601 : Blo 864565 1945601 := bstep (se 2 (by rfl) ⟨729600, by rfl⟩ : syracuseStep 1945601 = 1459201) B1459201
theorem B1945817 : Blo 864565 1945817 := bstep (se 2 (by rfl) ⟨729681, by rfl⟩ : syracuseStep 1945817 = 1459363) B1459363
theorem B1945907 : Blo 864565 1945907 := bstep (se 1 (by rfl) ⟨1459430, by rfl⟩ : syracuseStep 1945907 = 2918861) B2918861
theorem B864567 : Blo 864565 864567 := bstep (se 1 (by rfl) ⟨648425, by rfl⟩ : syracuseStep 864567 = 1296851) B1296851
theorem B864587 : Blo 864565 864587 := bstep (se 1 (by rfl) ⟨648440, by rfl⟩ : syracuseStep 864587 = 1296881) B1296881
theorem B2142539 : Blo 864565 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B864599 : Blo 864565 864599 := bstep (se 1 (by rfl) ⟨648449, by rfl⟩ : syracuseStep 864599 = 1296899) B1296899
theorem B1945943 : Blo 864565 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B864619 : Blo 864565 864619 := bstep (se 1 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 864619 = 1296929) B1296929
theorem B864631 : Blo 864565 864631 := bstep (se 1 (by rfl) ⟨648473, by rfl⟩ : syracuseStep 864631 = 1296947) B1296947
theorem B864651 : Blo 864565 864651 := bstep (se 1 (by rfl) ⟨648488, by rfl⟩ : syracuseStep 864651 = 1296977) B1296977
theorem B864663 : Blo 864565 864663 := bstep (se 1 (by rfl) ⟨648497, by rfl⟩ : syracuseStep 864663 = 1296995) B1296995
theorem B864683 : Blo 864565 864683 := bstep (se 1 (by rfl) ⟨648512, by rfl⟩ : syracuseStep 864683 = 1297025) B1297025
theorem B864695 : Blo 864565 864695 := bstep (se 1 (by rfl) ⟨648521, by rfl⟩ : syracuseStep 864695 = 1297043) B1297043
theorem B864715 : Blo 864565 864715 := bstep (se 1 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 864715 = 1297073) B1297073
theorem B864727 : Blo 864565 864727 := bstep (se 1 (by rfl) ⟨648545, by rfl⟩ : syracuseStep 864727 = 1297091) B1297091
theorem B864747 : Blo 864565 864747 := bstep (se 1 (by rfl) ⟨648560, by rfl⟩ : syracuseStep 864747 = 1297121) B1297121
theorem B864759 : Blo 864565 864759 := bstep (se 1 (by rfl) ⟨648569, by rfl⟩ : syracuseStep 864759 = 1297139) B1297139
theorem B864779 : Blo 864565 864779 := bstep (se 1 (by rfl) ⟨648584, by rfl⟩ : syracuseStep 864779 = 1297169) B1297169
theorem B1946123 : Blo 864565 1946123 := bstep (se 1 (by rfl) ⟨1459592, by rfl⟩ : syracuseStep 1946123 = 2919185) B2919185
theorem B864791 : Blo 864565 864791 := bstep (se 1 (by rfl) ⟨648593, by rfl⟩ : syracuseStep 864791 = 1297187) B1297187
theorem B2339351 : Blo 864565 2339351 := bstep (se 1 (by rfl) ⟨1754513, by rfl⟩ : syracuseStep 2339351 = 3509027) B3509027
theorem B2929175 : Blo 864565 2929175 := bstep (se 1 (by rfl) ⟨2196881, by rfl⟩ : syracuseStep 2929175 = 4393763) B4393763
theorem B864811 : Blo 864565 864811 := bstep (se 1 (by rfl) ⟨648608, by rfl⟩ : syracuseStep 864811 = 1297217) B1297217
theorem B864823 : Blo 864565 864823 := bstep (se 1 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 864823 = 1297235) B1297235
theorem B1946177 : Blo 864565 1946177 := bstep (se 2 (by rfl) ⟨729816, by rfl⟩ : syracuseStep 1946177 = 1459633) B1459633
theorem B864843 : Blo 864565 864843 := bstep (se 1 (by rfl) ⟨648632, by rfl⟩ : syracuseStep 864843 = 1297265) B1297265
theorem B864855 : Blo 864565 864855 := bstep (se 1 (by rfl) ⟨648641, by rfl⟩ : syracuseStep 864855 = 1297283) B1297283
theorem B9351773 : Blo 864565 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B864875 : Blo 864565 864875 := bstep (se 1 (by rfl) ⟨648656, by rfl⟩ : syracuseStep 864875 = 1297313) B1297313
theorem B864887 : Blo 864565 864887 := bstep (se 1 (by rfl) ⟨648665, by rfl⟩ : syracuseStep 864887 = 1297331) B1297331
theorem B864907 : Blo 864565 864907 := bstep (se 1 (by rfl) ⟨648680, by rfl⟩ : syracuseStep 864907 = 1297361) B1297361
theorem B1847947 : Blo 864565 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B864919 : Blo 864565 864919 := bstep (se 1 (by rfl) ⟨648689, by rfl⟩ : syracuseStep 864919 = 1297379) B1297379
theorem B2110103 : Blo 864565 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B864939 : Blo 864565 864939 := bstep (se 1 (by rfl) ⟨648704, by rfl⟩ : syracuseStep 864939 = 1297409) B1297409
theorem B3945133 : Blo 864565 3945133 := bstep (se 3 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 3945133 = 1479425) B1479425
theorem B864951 : Blo 864565 864951 := bstep (se 1 (by rfl) ⟨648713, by rfl⟩ : syracuseStep 864951 = 1297427) B1297427
theorem B864971 : Blo 864565 864971 := bstep (se 1 (by rfl) ⟨648728, by rfl⟩ : syracuseStep 864971 = 1297457) B1297457
theorem B864983 : Blo 864565 864983 := bstep (se 1 (by rfl) ⟨648737, by rfl⟩ : syracuseStep 864983 = 1297475) B1297475
theorem B865003 : Blo 864565 865003 := bstep (se 1 (by rfl) ⟨648752, by rfl⟩ : syracuseStep 865003 = 1297505) B1297505
theorem B865015 : Blo 864565 865015 := bstep (se 1 (by rfl) ⟨648761, by rfl⟩ : syracuseStep 865015 = 1297523) B1297523
theorem B1094411 : Blo 864565 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B865035 : Blo 864565 865035 := bstep (se 1 (by rfl) ⟨648776, by rfl⟩ : syracuseStep 865035 = 1297553) B1297553
theorem B865047 : Blo 864565 865047 := bstep (se 1 (by rfl) ⟨648785, by rfl⟩ : syracuseStep 865047 = 1297571) B1297571
theorem B1946393 : Blo 864565 1946393 := bstep (se 2 (by rfl) ⟨729897, by rfl⟩ : syracuseStep 1946393 = 1459795) B1459795
theorem B865067 : Blo 864565 865067 := bstep (se 1 (by rfl) ⟨648800, by rfl⟩ : syracuseStep 865067 = 1297601) B1297601
theorem B865079 : Blo 864565 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B865099 : Blo 864565 865099 := bstep (se 1 (by rfl) ⟨648824, by rfl⟩ : syracuseStep 865099 = 1297649) B1297649
theorem B865111 : Blo 864565 865111 := bstep (se 1 (by rfl) ⟨648833, by rfl⟩ : syracuseStep 865111 = 1297667) B1297667
theorem B865131 : Blo 864565 865131 := bstep (se 1 (by rfl) ⟨648848, by rfl⟩ : syracuseStep 865131 = 1297697) B1297697
theorem B1946483 : Blo 864565 1946483 := bstep (se 1 (by rfl) ⟨1459862, by rfl⟩ : syracuseStep 1946483 = 2919725) B2919725
theorem B865143 : Blo 864565 865143 := bstep (se 1 (by rfl) ⟨648857, by rfl⟩ : syracuseStep 865143 = 1297715) B1297715
theorem B865163 : Blo 864565 865163 := bstep (se 1 (by rfl) ⟨648872, by rfl⟩ : syracuseStep 865163 = 1297745) B1297745
theorem B1946519 : Blo 864565 1946519 := bstep (se 1 (by rfl) ⟨1459889, by rfl⟩ : syracuseStep 1946519 = 2919779) B2919779
theorem B865175 : Blo 864565 865175 := bstep (se 1 (by rfl) ⟨648881, by rfl⟩ : syracuseStep 865175 = 1297763) B1297763
theorem B865195 : Blo 864565 865195 := bstep (se 1 (by rfl) ⟨648896, by rfl⟩ : syracuseStep 865195 = 1297793) B1297793
theorem B865207 : Blo 864565 865207 := bstep (se 1 (by rfl) ⟨648905, by rfl⟩ : syracuseStep 865207 = 1297811) B1297811
theorem B2077633 : Blo 864565 2077633 := bstep (se 2 (by rfl) ⟨779112, by rfl⟩ : syracuseStep 2077633 = 1558225) B1558225
theorem B865227 : Blo 864565 865227 := bstep (se 1 (by rfl) ⟨648920, by rfl⟩ : syracuseStep 865227 = 1297841) B1297841
theorem B865239 : Blo 864565 865239 := bstep (se 1 (by rfl) ⟨648929, by rfl⟩ : syracuseStep 865239 = 1297859) B1297859
theorem B2634713 : Blo 864565 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B865259 : Blo 864565 865259 := bstep (se 1 (by rfl) ⟨648944, by rfl⟩ : syracuseStep 865259 = 1297889) B1297889
theorem B865271 : Blo 864565 865271 := bstep (se 1 (by rfl) ⟨648953, by rfl⟩ : syracuseStep 865271 = 1297907) B1297907
theorem B865291 : Blo 864565 865291 := bstep (se 1 (by rfl) ⟨648968, by rfl⟩ : syracuseStep 865291 = 1297937) B1297937
theorem B3290129 : Blo 864565 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B865303 : Blo 864565 865303 := bstep (se 1 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 865303 = 1297955) B1297955
theorem B865323 : Blo 864565 865323 := bstep (se 1 (by rfl) ⟨648992, by rfl⟩ : syracuseStep 865323 = 1297985) B1297985
theorem B2929715 : Blo 864565 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B865335 : Blo 864565 865335 := bstep (se 1 (by rfl) ⟨649001, by rfl⟩ : syracuseStep 865335 = 1298003) B1298003
theorem B1946699 : Blo 864565 1946699 := bstep (se 1 (by rfl) ⟨1460024, by rfl⟩ : syracuseStep 1946699 = 2920049) B2920049
theorem B865355 : Blo 864565 865355 := bstep (se 1 (by rfl) ⟨649016, by rfl⟩ : syracuseStep 865355 = 1298033) B1298033
theorem B865367 : Blo 864565 865367 := bstep (se 1 (by rfl) ⟨649025, by rfl⟩ : syracuseStep 865367 = 1298051) B1298051
theorem B865387 : Blo 864565 865387 := bstep (se 1 (by rfl) ⟨649040, by rfl⟩ : syracuseStep 865387 = 1298081) B1298081
theorem B865399 : Blo 864565 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B1946753 : Blo 864565 1946753 := bstep (se 2 (by rfl) ⟨730032, by rfl⟩ : syracuseStep 1946753 = 1460065) B1460065
theorem B865419 : Blo 864565 865419 := bstep (se 1 (by rfl) ⟨649064, by rfl⟩ : syracuseStep 865419 = 1298129) B1298129
theorem B865431 : Blo 864565 865431 := bstep (se 1 (by rfl) ⟨649073, by rfl⟩ : syracuseStep 865431 = 1298147) B1298147
theorem B865451 : Blo 864565 865451 := bstep (se 1 (by rfl) ⟨649088, by rfl⟩ : syracuseStep 865451 = 1298177) B1298177
theorem B2340019 : Blo 864565 2340019 := bstep (se 1 (by rfl) ⟨1755014, by rfl⟩ : syracuseStep 2340019 = 3510029) B3510029
theorem B865463 : Blo 864565 865463 := bstep (se 1 (by rfl) ⟨649097, by rfl⟩ : syracuseStep 865463 = 1298195) B1298195
theorem B865483 : Blo 864565 865483 := bstep (se 1 (by rfl) ⟨649112, by rfl⟩ : syracuseStep 865483 = 1298225) B1298225
theorem B865495 : Blo 864565 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B865515 : Blo 864565 865515 := bstep (se 1 (by rfl) ⟨649136, by rfl⟩ : syracuseStep 865515 = 1298273) B1298273
theorem B865527 : Blo 864565 865527 := bstep (se 1 (by rfl) ⟨649145, by rfl⟩ : syracuseStep 865527 = 1298291) B1298291
theorem B865547 : Blo 864565 865547 := bstep (se 1 (by rfl) ⟨649160, by rfl⟩ : syracuseStep 865547 = 1298321) B1298321
theorem B865559 : Blo 864565 865559 := bstep (se 1 (by rfl) ⟨649169, by rfl⟩ : syracuseStep 865559 = 1298339) B1298339
theorem B865579 : Blo 864565 865579 := bstep (se 1 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 865579 = 1298369) B1298369
theorem B2471219 : Blo 864565 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B865591 : Blo 864565 865591 := bstep (se 1 (by rfl) ⟨649193, by rfl⟩ : syracuseStep 865591 = 1298387) B1298387
theorem B2929985 : Blo 864565 2929985 := bstep (se 2 (by rfl) ⟨1098744, by rfl⟩ : syracuseStep 2929985 = 2197489) B2197489
theorem B865611 : Blo 864565 865611 := bstep (se 1 (by rfl) ⟨649208, by rfl⟩ : syracuseStep 865611 = 1298417) B1298417
theorem B865623 : Blo 864565 865623 := bstep (se 1 (by rfl) ⟨649217, by rfl⟩ : syracuseStep 865623 = 1298435) B1298435
theorem B1946969 : Blo 864565 1946969 := bstep (se 2 (by rfl) ⟨730113, by rfl⟩ : syracuseStep 1946969 = 1460227) B1460227
theorem B1848665 : Blo 864565 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B865643 : Blo 864565 865643 := bstep (se 1 (by rfl) ⟨649232, by rfl⟩ : syracuseStep 865643 = 1298465) B1298465
theorem B865655 : Blo 864565 865655 := bstep (se 1 (by rfl) ⟨649241, by rfl⟩ : syracuseStep 865655 = 1298483) B1298483
theorem B865675 : Blo 864565 865675 := bstep (se 1 (by rfl) ⟨649256, by rfl⟩ : syracuseStep 865675 = 1298513) B1298513
theorem B865687 : Blo 864565 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B865707 : Blo 864565 865707 := bstep (se 1 (by rfl) ⟨649280, by rfl⟩ : syracuseStep 865707 = 1298561) B1298561
theorem B1947059 : Blo 864565 1947059 := bstep (se 1 (by rfl) ⟨1460294, by rfl⟩ : syracuseStep 1947059 = 2920589) B2920589
theorem B865719 : Blo 864565 865719 := bstep (se 1 (by rfl) ⟨649289, by rfl⟩ : syracuseStep 865719 = 1298579) B1298579
theorem B1095115 : Blo 864565 1095115 := bstep (se 1 (by rfl) ⟨821336, by rfl⟩ : syracuseStep 1095115 = 1642673) B1642673
theorem B865739 : Blo 864565 865739 := bstep (se 1 (by rfl) ⟨649304, by rfl⟩ : syracuseStep 865739 = 1298609) B1298609
theorem B1947095 : Blo 864565 1947095 := bstep (se 1 (by rfl) ⟨1460321, by rfl⟩ : syracuseStep 1947095 = 2920643) B2920643
theorem B865751 : Blo 864565 865751 := bstep (se 1 (by rfl) ⟨649313, by rfl⟩ : syracuseStep 865751 = 1298627) B1298627
theorem B865771 : Blo 864565 865771 := bstep (se 1 (by rfl) ⟨649328, by rfl⟩ : syracuseStep 865771 = 1298657) B1298657
theorem B865783 : Blo 864565 865783 := bstep (se 1 (by rfl) ⟨649337, by rfl⟩ : syracuseStep 865783 = 1298675) B1298675
theorem B7419397 : Blo 864565 7419397 := bstep (se 4 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 7419397 = 1391137) B1391137
theorem B865803 : Blo 864565 865803 := bstep (se 1 (by rfl) ⟨649352, by rfl⟩ : syracuseStep 865803 = 1298705) B1298705
theorem B865815 : Blo 864565 865815 := bstep (se 1 (by rfl) ⟨649361, by rfl⟩ : syracuseStep 865815 = 1298723) B1298723
theorem B2471447 : Blo 864565 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B865835 : Blo 864565 865835 := bstep (se 1 (by rfl) ⟨649376, by rfl⟩ : syracuseStep 865835 = 1298753) B1298753
theorem B865847 : Blo 864565 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B865867 : Blo 864565 865867 := bstep (se 1 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 865867 = 1298801) B1298801
theorem B865879 : Blo 864565 865879 := bstep (se 1 (by rfl) ⟨649409, by rfl⟩ : syracuseStep 865879 = 1298819) B1298819
theorem B865899 : Blo 864565 865899 := bstep (se 1 (by rfl) ⟨649424, by rfl⟩ : syracuseStep 865899 = 1298849) B1298849
theorem B865911 : Blo 864565 865911 := bstep (se 1 (by rfl) ⟨649433, by rfl⟩ : syracuseStep 865911 = 1298867) B1298867
theorem B1947275 : Blo 864565 1947275 := bstep (se 1 (by rfl) ⟨1460456, by rfl⟩ : syracuseStep 1947275 = 2920913) B2920913
theorem B865931 : Blo 864565 865931 := bstep (se 1 (by rfl) ⟨649448, by rfl⟩ : syracuseStep 865931 = 1298897) B1298897
theorem B865943 : Blo 864565 865943 := bstep (se 1 (by rfl) ⟨649457, by rfl⟩ : syracuseStep 865943 = 1298915) B1298915
theorem B865963 : Blo 864565 865963 := bstep (se 1 (by rfl) ⟨649472, by rfl⟩ : syracuseStep 865963 = 1298945) B1298945
theorem B865975 : Blo 864565 865975 := bstep (se 1 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 865975 = 1298963) B1298963
theorem B1947329 : Blo 864565 1947329 := bstep (se 2 (by rfl) ⟨730248, by rfl⟩ : syracuseStep 1947329 = 1460497) B1460497
theorem B865995 : Blo 864565 865995 := bstep (se 1 (by rfl) ⟨649496, by rfl⟩ : syracuseStep 865995 = 1298993) B1298993
theorem B3290827 : Blo 864565 3290827 := bstep (se 1 (by rfl) ⟨2468120, by rfl⟩ : syracuseStep 3290827 = 4936241) B4936241
theorem B1095383 : Blo 864565 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B866007 : Blo 864565 866007 := bstep (se 1 (by rfl) ⟨649505, by rfl⟩ : syracuseStep 866007 = 1299011) B1299011
theorem B866027 : Blo 864565 866027 := bstep (se 1 (by rfl) ⟨649520, by rfl⟩ : syracuseStep 866027 = 1299041) B1299041
theorem B866039 : Blo 864565 866039 := bstep (se 1 (by rfl) ⟨649529, by rfl⟩ : syracuseStep 866039 = 1299059) B1299059
theorem B866059 : Blo 864565 866059 := bstep (se 1 (by rfl) ⟨649544, by rfl⟩ : syracuseStep 866059 = 1299089) B1299089
theorem B866071 : Blo 864565 866071 := bstep (se 1 (by rfl) ⟨649553, by rfl⟩ : syracuseStep 866071 = 1299107) B1299107
theorem B866091 : Blo 864565 866091 := bstep (se 1 (by rfl) ⟨649568, by rfl⟩ : syracuseStep 866091 = 1299137) B1299137
theorem B866103 : Blo 864565 866103 := bstep (se 1 (by rfl) ⟨649577, by rfl⟩ : syracuseStep 866103 = 1299155) B1299155
theorem B866123 : Blo 864565 866123 := bstep (se 1 (by rfl) ⟨649592, by rfl⟩ : syracuseStep 866123 = 1299185) B1299185
theorem B2471755 : Blo 864565 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B866135 : Blo 864565 866135 := bstep (se 1 (by rfl) ⟨649601, by rfl⟩ : syracuseStep 866135 = 1299203) B1299203
theorem B1849177 : Blo 864565 1849177 := bstep (se 2 (by rfl) ⟨693441, by rfl⟩ : syracuseStep 1849177 = 1386883) B1386883
theorem B2930525 : Blo 864565 2930525 := bstep (se 3 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 2930525 = 1098947) B1098947
theorem B866155 : Blo 864565 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B866167 : Blo 864565 866167 := bstep (se 1 (by rfl) ⟨649625, by rfl⟩ : syracuseStep 866167 = 1299251) B1299251
theorem B866187 : Blo 864565 866187 := bstep (se 1 (by rfl) ⟨649640, by rfl⟩ : syracuseStep 866187 = 1299281) B1299281
theorem B866199 : Blo 864565 866199 := bstep (se 1 (by rfl) ⟨649649, by rfl⟩ : syracuseStep 866199 = 1299299) B1299299
theorem B1947545 : Blo 864565 1947545 := bstep (se 2 (by rfl) ⟨730329, by rfl⟩ : syracuseStep 1947545 = 1460659) B1460659
theorem B866219 : Blo 864565 866219 := bstep (se 1 (by rfl) ⟨649664, by rfl⟩ : syracuseStep 866219 = 1299329) B1299329
theorem B866231 : Blo 864565 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B866251 : Blo 864565 866251 := bstep (se 1 (by rfl) ⟨649688, by rfl⟩ : syracuseStep 866251 = 1299377) B1299377
theorem B866263 : Blo 864565 866263 := bstep (se 1 (by rfl) ⟨649697, by rfl⟩ : syracuseStep 866263 = 1299395) B1299395
theorem B3291101 : Blo 864565 3291101 := bstep (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) B1234163
theorem B866283 : Blo 864565 866283 := bstep (se 1 (by rfl) ⟨649712, by rfl⟩ : syracuseStep 866283 = 1299425) B1299425
theorem B1947635 : Blo 864565 1947635 := bstep (se 1 (by rfl) ⟨1460726, by rfl⟩ : syracuseStep 1947635 = 2921453) B2921453
theorem B1849331 : Blo 864565 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B866295 : Blo 864565 866295 := bstep (se 1 (by rfl) ⟨649721, by rfl⟩ : syracuseStep 866295 = 1299443) B1299443
theorem B866315 : Blo 864565 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B3749905 : Blo 864565 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1947671 : Blo 864565 1947671 := bstep (se 1 (by rfl) ⟨1460753, by rfl⟩ : syracuseStep 1947671 = 2921507) B2921507
theorem B866327 : Blo 864565 866327 := bstep (se 1 (by rfl) ⟨649745, by rfl⟩ : syracuseStep 866327 = 1299491) B1299491
theorem B866347 : Blo 864565 866347 := bstep (se 1 (by rfl) ⟨649760, by rfl⟩ : syracuseStep 866347 = 1299521) B1299521
theorem B866359 : Blo 864565 866359 := bstep (se 1 (by rfl) ⟨649769, by rfl⟩ : syracuseStep 866359 = 1299539) B1299539
theorem B866379 : Blo 864565 866379 := bstep (se 1 (by rfl) ⟨649784, by rfl⟩ : syracuseStep 866379 = 1299569) B1299569
theorem B866391 : Blo 864565 866391 := bstep (se 1 (by rfl) ⟨649793, by rfl⟩ : syracuseStep 866391 = 1299587) B1299587
theorem B2472029 : Blo 864565 2472029 := bstep (se 3 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 2472029 = 927011) B927011
theorem B866411 : Blo 864565 866411 := bstep (se 1 (by rfl) ⟨649808, by rfl⟩ : syracuseStep 866411 = 1299617) B1299617
theorem B866423 : Blo 864565 866423 := bstep (se 1 (by rfl) ⟨649817, by rfl⟩ : syracuseStep 866423 = 1299635) B1299635
theorem B866443 : Blo 864565 866443 := bstep (se 1 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 866443 = 1299665) B1299665
theorem B866455 : Blo 864565 866455 := bstep (se 1 (by rfl) ⟨649841, by rfl⟩ : syracuseStep 866455 = 1299683) B1299683
theorem B866475 : Blo 864565 866475 := bstep (se 1 (by rfl) ⟨649856, by rfl⟩ : syracuseStep 866475 = 1299713) B1299713
theorem B866487 : Blo 864565 866487 := bstep (se 1 (by rfl) ⟨649865, by rfl⟩ : syracuseStep 866487 = 1299731) B1299731
theorem B1947851 : Blo 864565 1947851 := bstep (se 1 (by rfl) ⟨1460888, by rfl⟩ : syracuseStep 1947851 = 2921777) B2921777
theorem B866507 : Blo 864565 866507 := bstep (se 1 (by rfl) ⟨649880, by rfl⟩ : syracuseStep 866507 = 1299761) B1299761
theorem B866519 : Blo 864565 866519 := bstep (se 1 (by rfl) ⟨649889, by rfl⟩ : syracuseStep 866519 = 1299779) B1299779
theorem B866539 : Blo 864565 866539 := bstep (se 1 (by rfl) ⟨649904, by rfl⟩ : syracuseStep 866539 = 1299809) B1299809
theorem B866551 : Blo 864565 866551 := bstep (se 1 (by rfl) ⟨649913, by rfl⟩ : syracuseStep 866551 = 1299827) B1299827
theorem B1947905 : Blo 864565 1947905 := bstep (se 2 (by rfl) ⟨730464, by rfl⟩ : syracuseStep 1947905 = 1460929) B1460929
theorem B866571 : Blo 864565 866571 := bstep (se 1 (by rfl) ⟨649928, by rfl⟩ : syracuseStep 866571 = 1299857) B1299857
theorem B866583 : Blo 864565 866583 := bstep (se 1 (by rfl) ⟨649937, by rfl⟩ : syracuseStep 866583 = 1299875) B1299875
theorem B866603 : Blo 864565 866603 := bstep (se 1 (by rfl) ⟨649952, by rfl⟩ : syracuseStep 866603 = 1299905) B1299905
theorem B866615 : Blo 864565 866615 := bstep (se 1 (by rfl) ⟨649961, by rfl⟩ : syracuseStep 866615 = 1299923) B1299923
theorem B866635 : Blo 864565 866635 := bstep (se 1 (by rfl) ⟨649976, by rfl⟩ : syracuseStep 866635 = 1299953) B1299953
theorem B866647 : Blo 864565 866647 := bstep (se 1 (by rfl) ⟨649985, by rfl⟩ : syracuseStep 866647 = 1299971) B1299971
theorem B7027037 : Blo 864565 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B866667 : Blo 864565 866667 := bstep (se 1 (by rfl) ⟨650000, by rfl⟩ : syracuseStep 866667 = 1300001) B1300001
theorem B866679 : Blo 864565 866679 := bstep (se 1 (by rfl) ⟨650009, by rfl⟩ : syracuseStep 866679 = 1300019) B1300019
theorem B866699 : Blo 864565 866699 := bstep (se 1 (by rfl) ⟨650024, by rfl⟩ : syracuseStep 866699 = 1300049) B1300049
theorem B1096087 : Blo 864565 1096087 := bstep (se 1 (by rfl) ⟨822065, by rfl⟩ : syracuseStep 1096087 = 1644131) B1644131
theorem B866711 : Blo 864565 866711 := bstep (se 1 (by rfl) ⟨650033, by rfl⟩ : syracuseStep 866711 = 1300067) B1300067
theorem B866731 : Blo 864565 866731 := bstep (se 1 (by rfl) ⟨650048, by rfl⟩ : syracuseStep 866731 = 1300097) B1300097
theorem B866743 : Blo 864565 866743 := bstep (se 1 (by rfl) ⟨650057, by rfl⟩ : syracuseStep 866743 = 1300115) B1300115
theorem B866763 : Blo 864565 866763 := bstep (se 1 (by rfl) ⟨650072, by rfl⟩ : syracuseStep 866763 = 1300145) B1300145
theorem B866775 : Blo 864565 866775 := bstep (se 1 (by rfl) ⟨650081, by rfl⟩ : syracuseStep 866775 = 1300163) B1300163
theorem B1948121 : Blo 864565 1948121 := bstep (se 2 (by rfl) ⟨730545, by rfl⟩ : syracuseStep 1948121 = 1461091) B1461091
theorem B866795 : Blo 864565 866795 := bstep (se 1 (by rfl) ⟨650096, by rfl⟩ : syracuseStep 866795 = 1300193) B1300193
theorem B866807 : Blo 864565 866807 := bstep (se 1 (by rfl) ⟨650105, by rfl⟩ : syracuseStep 866807 = 1300211) B1300211
theorem B3258883 : Blo 864565 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B866827 : Blo 864565 866827 := bstep (se 1 (by rfl) ⟨650120, by rfl⟩ : syracuseStep 866827 = 1300241) B1300241
theorem B5552657 : Blo 864565 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B866839 : Blo 864565 866839 := bstep (se 1 (by rfl) ⟨650129, by rfl⟩ : syracuseStep 866839 = 1300259) B1300259
theorem B14989859 : Blo 864565 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B866859 : Blo 864565 866859 := bstep (se 1 (by rfl) ⟨650144, by rfl⟩ : syracuseStep 866859 = 1300289) B1300289
theorem B1948211 : Blo 864565 1948211 := bstep (se 1 (by rfl) ⟨1461158, by rfl⟩ : syracuseStep 1948211 = 2922317) B2922317
theorem B866871 : Blo 864565 866871 := bstep (se 1 (by rfl) ⟨650153, by rfl⟩ : syracuseStep 866871 = 1300307) B1300307
theorem B866891 : Blo 864565 866891 := bstep (se 1 (by rfl) ⟨650168, by rfl⟩ : syracuseStep 866891 = 1300337) B1300337
theorem B1948247 : Blo 864565 1948247 := bstep (se 1 (by rfl) ⟨1461185, by rfl⟩ : syracuseStep 1948247 = 2922371) B2922371
theorem B866903 : Blo 864565 866903 := bstep (se 1 (by rfl) ⟨650177, by rfl⟩ : syracuseStep 866903 = 1300355) B1300355
theorem B866923 : Blo 864565 866923 := bstep (se 1 (by rfl) ⟨650192, by rfl⟩ : syracuseStep 866923 = 1300385) B1300385
theorem B866935 : Blo 864565 866935 := bstep (se 1 (by rfl) ⟨650201, by rfl⟩ : syracuseStep 866935 = 1300403) B1300403
theorem B866955 : Blo 864565 866955 := bstep (se 1 (by rfl) ⟨650216, by rfl⟩ : syracuseStep 866955 = 1300433) B1300433
theorem B866967 : Blo 864565 866967 := bstep (se 1 (by rfl) ⟨650225, by rfl⟩ : syracuseStep 866967 = 1300451) B1300451
theorem B3291799 : Blo 864565 3291799 := bstep (se 1 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 3291799 = 4937699) B4937699
theorem B866987 : Blo 864565 866987 := bstep (se 1 (by rfl) ⟨650240, by rfl⟩ : syracuseStep 866987 = 1300481) B1300481
theorem B866999 : Blo 864565 866999 := bstep (se 1 (by rfl) ⟨650249, by rfl⟩ : syracuseStep 866999 = 1300499) B1300499
theorem B867019 : Blo 864565 867019 := bstep (se 1 (by rfl) ⟨650264, by rfl⟩ : syracuseStep 867019 = 1300529) B1300529
theorem B867031 : Blo 864565 867031 := bstep (se 1 (by rfl) ⟨650273, by rfl⟩ : syracuseStep 867031 = 1300547) B1300547
theorem B867051 : Blo 864565 867051 := bstep (se 1 (by rfl) ⟨650288, by rfl⟩ : syracuseStep 867051 = 1300577) B1300577
theorem B867063 : Blo 864565 867063 := bstep (se 1 (by rfl) ⟨650297, by rfl⟩ : syracuseStep 867063 = 1300595) B1300595
theorem B1948427 : Blo 864565 1948427 := bstep (se 1 (by rfl) ⟨1461320, by rfl⟩ : syracuseStep 1948427 = 2922641) B2922641
theorem B867083 : Blo 864565 867083 := bstep (se 1 (by rfl) ⟨650312, by rfl⟩ : syracuseStep 867083 = 1300625) B1300625
theorem B2341655 : Blo 864565 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B867095 : Blo 864565 867095 := bstep (se 1 (by rfl) ⟨650321, by rfl⟩ : syracuseStep 867095 = 1300643) B1300643
theorem B867115 : Blo 864565 867115 := bstep (se 1 (by rfl) ⟨650336, by rfl⟩ : syracuseStep 867115 = 1300673) B1300673
theorem B867127 : Blo 864565 867127 := bstep (se 1 (by rfl) ⟨650345, by rfl⟩ : syracuseStep 867127 = 1300691) B1300691
theorem B1948481 : Blo 864565 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B3128129 : Blo 864565 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B867147 : Blo 864565 867147 := bstep (se 1 (by rfl) ⟨650360, by rfl⟩ : syracuseStep 867147 = 1300721) B1300721
theorem B867159 : Blo 864565 867159 := bstep (se 1 (by rfl) ⟨650369, by rfl⟩ : syracuseStep 867159 = 1300739) B1300739
theorem B867179 : Blo 864565 867179 := bstep (se 1 (by rfl) ⟨650384, by rfl⟩ : syracuseStep 867179 = 1300769) B1300769
theorem B867191 : Blo 864565 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B867211 : Blo 864565 867211 := bstep (se 1 (by rfl) ⟨650408, by rfl⟩ : syracuseStep 867211 = 1300817) B1300817
theorem B867223 : Blo 864565 867223 := bstep (se 1 (by rfl) ⟨650417, by rfl⟩ : syracuseStep 867223 = 1300835) B1300835
theorem B867243 : Blo 864565 867243 := bstep (se 1 (by rfl) ⟨650432, by rfl⟩ : syracuseStep 867243 = 1300865) B1300865
theorem B4996019 : Blo 864565 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B867255 : Blo 864565 867255 := bstep (se 1 (by rfl) ⟨650441, by rfl⟩ : syracuseStep 867255 = 1300883) B1300883
theorem B1850305 : Blo 864565 1850305 := bstep (se 2 (by rfl) ⟨693864, by rfl⟩ : syracuseStep 1850305 = 1387729) B1387729
theorem B867275 : Blo 864565 867275 := bstep (se 1 (by rfl) ⟨650456, by rfl⟩ : syracuseStep 867275 = 1300913) B1300913
theorem B867287 : Blo 864565 867287 := bstep (se 1 (by rfl) ⟨650465, by rfl⟩ : syracuseStep 867287 = 1300931) B1300931
theorem B867307 : Blo 864565 867307 := bstep (se 1 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 867307 = 1300961) B1300961
theorem B867319 : Blo 864565 867319 := bstep (se 1 (by rfl) ⟨650489, by rfl⟩ : syracuseStep 867319 = 1300979) B1300979
theorem B867339 : Blo 864565 867339 := bstep (se 1 (by rfl) ⟨650504, by rfl⟩ : syracuseStep 867339 = 1301009) B1301009
theorem B867351 : Blo 864565 867351 := bstep (se 1 (by rfl) ⟨650513, by rfl⟩ : syracuseStep 867351 = 1301027) B1301027
theorem B1948697 : Blo 864565 1948697 := bstep (se 2 (by rfl) ⟨730761, by rfl⟩ : syracuseStep 1948697 = 1461523) B1461523
theorem B867371 : Blo 864565 867371 := bstep (se 1 (by rfl) ⟨650528, by rfl⟩ : syracuseStep 867371 = 1301057) B1301057
theorem B867383 : Blo 864565 867383 := bstep (se 1 (by rfl) ⟨650537, by rfl⟩ : syracuseStep 867383 = 1301075) B1301075
theorem B2964545 : Blo 864565 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B867403 : Blo 864565 867403 := bstep (se 1 (by rfl) ⟨650552, by rfl⟩ : syracuseStep 867403 = 1301105) B1301105
theorem B867415 : Blo 864565 867415 := bstep (se 1 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 867415 = 1301123) B1301123
theorem B867435 : Blo 864565 867435 := bstep (se 1 (by rfl) ⟨650576, by rfl⟩ : syracuseStep 867435 = 1301153) B1301153
theorem B1948787 : Blo 864565 1948787 := bstep (se 1 (by rfl) ⟨1461590, by rfl⟩ : syracuseStep 1948787 = 2923181) B2923181
theorem B867447 : Blo 864565 867447 := bstep (se 1 (by rfl) ⟨650585, by rfl⟩ : syracuseStep 867447 = 1301171) B1301171
theorem B867467 : Blo 864565 867467 := bstep (se 1 (by rfl) ⟨650600, by rfl⟩ : syracuseStep 867467 = 1301201) B1301201
theorem B1948823 : Blo 864565 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B867479 : Blo 864565 867479 := bstep (se 1 (by rfl) ⟨650609, by rfl⟩ : syracuseStep 867479 = 1301219) B1301219
theorem B867499 : Blo 864565 867499 := bstep (se 1 (by rfl) ⟨650624, by rfl⟩ : syracuseStep 867499 = 1301249) B1301249
theorem B867511 : Blo 864565 867511 := bstep (se 1 (by rfl) ⟨650633, by rfl⟩ : syracuseStep 867511 = 1301267) B1301267
theorem B867531 : Blo 864565 867531 := bstep (se 1 (by rfl) ⟨650648, by rfl⟩ : syracuseStep 867531 = 1301297) B1301297
theorem B867543 : Blo 864565 867543 := bstep (se 1 (by rfl) ⟨650657, by rfl⟩ : syracuseStep 867543 = 1301315) B1301315
theorem B867563 : Blo 864565 867563 := bstep (se 1 (by rfl) ⟨650672, by rfl⟩ : syracuseStep 867563 = 1301345) B1301345
theorem B867575 : Blo 864565 867575 := bstep (se 1 (by rfl) ⟨650681, by rfl⟩ : syracuseStep 867575 = 1301363) B1301363
theorem B867595 : Blo 864565 867595 := bstep (se 1 (by rfl) ⟨650696, by rfl⟩ : syracuseStep 867595 = 1301393) B1301393
theorem B1850647 : Blo 864565 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B867607 : Blo 864565 867607 := bstep (se 1 (by rfl) ⟨650705, by rfl⟩ : syracuseStep 867607 = 1301411) B1301411
theorem B867627 : Blo 864565 867627 := bstep (se 1 (by rfl) ⟨650720, by rfl⟩ : syracuseStep 867627 = 1301441) B1301441
theorem B6569261 : Blo 864565 6569261 := bstep (se 3 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 6569261 = 2463473) B2463473
theorem B867639 : Blo 864565 867639 := bstep (se 1 (by rfl) ⟨650729, by rfl⟩ : syracuseStep 867639 = 1301459) B1301459
theorem B1949003 : Blo 864565 1949003 := bstep (se 1 (by rfl) ⟨1461752, by rfl⟩ : syracuseStep 1949003 = 2923505) B2923505
theorem B867659 : Blo 864565 867659 := bstep (se 1 (by rfl) ⟨650744, by rfl⟩ : syracuseStep 867659 = 1301489) B1301489
theorem B867671 : Blo 864565 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B867691 : Blo 864565 867691 := bstep (se 1 (by rfl) ⟨650768, by rfl⟩ : syracuseStep 867691 = 1301537) B1301537
theorem B867703 : Blo 864565 867703 := bstep (se 1 (by rfl) ⟨650777, by rfl⟩ : syracuseStep 867703 = 1301555) B1301555
theorem B1949057 : Blo 864565 1949057 := bstep (se 2 (by rfl) ⟨730896, by rfl⟩ : syracuseStep 1949057 = 1461793) B1461793
theorem B867723 : Blo 864565 867723 := bstep (se 1 (by rfl) ⟨650792, by rfl⟩ : syracuseStep 867723 = 1301585) B1301585
theorem B867735 : Blo 864565 867735 := bstep (se 1 (by rfl) ⟨650801, by rfl⟩ : syracuseStep 867735 = 1301603) B1301603
theorem B867755 : Blo 864565 867755 := bstep (se 1 (by rfl) ⟨650816, by rfl⟩ : syracuseStep 867755 = 1301633) B1301633
theorem B3292589 : Blo 864565 3292589 := bstep (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) B1234721
theorem B867767 : Blo 864565 867767 := bstep (se 1 (by rfl) ⟨650825, by rfl⟩ : syracuseStep 867767 = 1301651) B1301651
theorem B867787 : Blo 864565 867787 := bstep (se 1 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 867787 = 1301681) B1301681
theorem B867799 : Blo 864565 867799 := bstep (se 1 (by rfl) ⟨650849, by rfl⟩ : syracuseStep 867799 = 1301699) B1301699
theorem B867819 : Blo 864565 867819 := bstep (se 1 (by rfl) ⟨650864, by rfl⟩ : syracuseStep 867819 = 1301729) B1301729
theorem B867831 : Blo 864565 867831 := bstep (se 1 (by rfl) ⟨650873, by rfl⟩ : syracuseStep 867831 = 1301747) B1301747
theorem B867851 : Blo 864565 867851 := bstep (se 1 (by rfl) ⟨650888, by rfl⟩ : syracuseStep 867851 = 1301777) B1301777
theorem B867863 : Blo 864565 867863 := bstep (se 1 (by rfl) ⟨650897, by rfl⟩ : syracuseStep 867863 = 1301795) B1301795
theorem B867883 : Blo 864565 867883 := bstep (se 1 (by rfl) ⟨650912, by rfl⟩ : syracuseStep 867883 = 1301825) B1301825
theorem B4931117 : Blo 864565 4931117 := bstep (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) B1849169
theorem B867895 : Blo 864565 867895 := bstep (se 1 (by rfl) ⟨650921, by rfl⟩ : syracuseStep 867895 = 1301843) B1301843
theorem B867915 : Blo 864565 867915 := bstep (se 1 (by rfl) ⟨650936, by rfl⟩ : syracuseStep 867915 = 1301873) B1301873
theorem B867927 : Blo 864565 867927 := bstep (se 1 (by rfl) ⟨650945, by rfl⟩ : syracuseStep 867927 = 1301891) B1301891
theorem B1949273 : Blo 864565 1949273 := bstep (se 2 (by rfl) ⟨730977, by rfl⟩ : syracuseStep 1949273 = 1461955) B1461955
theorem B867947 : Blo 864565 867947 := bstep (se 1 (by rfl) ⟨650960, by rfl⟩ : syracuseStep 867947 = 1301921) B1301921
theorem B867959 : Blo 864565 867959 := bstep (se 1 (by rfl) ⟨650969, by rfl⟩ : syracuseStep 867959 = 1301939) B1301939
theorem B867979 : Blo 864565 867979 := bstep (se 1 (by rfl) ⟨650984, by rfl⟩ : syracuseStep 867979 = 1301969) B1301969
theorem B867991 : Blo 864565 867991 := bstep (se 1 (by rfl) ⟨650993, by rfl⟩ : syracuseStep 867991 = 1301987) B1301987
theorem B868011 : Blo 864565 868011 := bstep (se 1 (by rfl) ⟨651008, by rfl⟩ : syracuseStep 868011 = 1302017) B1302017
theorem B1949363 : Blo 864565 1949363 := bstep (se 1 (by rfl) ⟨1462022, by rfl⟩ : syracuseStep 1949363 = 2924045) B2924045
theorem B868023 : Blo 864565 868023 := bstep (se 1 (by rfl) ⟨651017, by rfl⟩ : syracuseStep 868023 = 1302035) B1302035
theorem B1851083 : Blo 864565 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B868043 : Blo 864565 868043 := bstep (se 1 (by rfl) ⟨651032, by rfl⟩ : syracuseStep 868043 = 1302065) B1302065
theorem B1949399 : Blo 864565 1949399 := bstep (se 1 (by rfl) ⟨1462049, by rfl⟩ : syracuseStep 1949399 = 2924099) B2924099
theorem B868055 : Blo 864565 868055 := bstep (se 1 (by rfl) ⟨651041, by rfl⟩ : syracuseStep 868055 = 1302083) B1302083
theorem B868075 : Blo 864565 868075 := bstep (se 1 (by rfl) ⟨651056, by rfl⟩ : syracuseStep 868075 = 1302113) B1302113
theorem B868087 : Blo 864565 868087 := bstep (se 1 (by rfl) ⟨651065, by rfl⟩ : syracuseStep 868087 = 1302131) B1302131
theorem B868107 : Blo 864565 868107 := bstep (se 1 (by rfl) ⟨651080, by rfl⟩ : syracuseStep 868107 = 1302161) B1302161
theorem B868119 : Blo 864565 868119 := bstep (se 1 (by rfl) ⟨651089, by rfl⟩ : syracuseStep 868119 = 1302179) B1302179
theorem B868139 : Blo 864565 868139 := bstep (se 1 (by rfl) ⟨651104, by rfl⟩ : syracuseStep 868139 = 1302209) B1302209
theorem B868151 : Blo 864565 868151 := bstep (se 1 (by rfl) ⟨651113, by rfl⟩ : syracuseStep 868151 = 1302227) B1302227
theorem B868171 : Blo 864565 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B868183 : Blo 864565 868183 := bstep (se 1 (by rfl) ⟨651137, by rfl⟩ : syracuseStep 868183 = 1302275) B1302275
theorem B868203 : Blo 864565 868203 := bstep (se 1 (by rfl) ⟨651152, by rfl⟩ : syracuseStep 868203 = 1302305) B1302305
theorem B868215 : Blo 864565 868215 := bstep (se 1 (by rfl) ⟨651161, by rfl⟩ : syracuseStep 868215 = 1302323) B1302323
theorem B1949579 : Blo 864565 1949579 := bstep (se 1 (by rfl) ⟨1462184, by rfl⟩ : syracuseStep 1949579 = 2924369) B2924369
theorem B868235 : Blo 864565 868235 := bstep (se 1 (by rfl) ⟨651176, by rfl⟩ : syracuseStep 868235 = 1302353) B1302353
theorem B868247 : Blo 864565 868247 := bstep (se 1 (by rfl) ⟨651185, by rfl⟩ : syracuseStep 868247 = 1302371) B1302371
theorem B868267 : Blo 864565 868267 := bstep (se 1 (by rfl) ⟨651200, by rfl⟩ : syracuseStep 868267 = 1302401) B1302401
theorem B868279 : Blo 864565 868279 := bstep (se 1 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 868279 = 1302419) B1302419
theorem B1949633 : Blo 864565 1949633 := bstep (se 2 (by rfl) ⟨731112, by rfl⟩ : syracuseStep 1949633 = 1462225) B1462225
theorem B868299 : Blo 864565 868299 := bstep (se 1 (by rfl) ⟨651224, by rfl⟩ : syracuseStep 868299 = 1302449) B1302449
theorem B868311 : Blo 864565 868311 := bstep (se 1 (by rfl) ⟨651233, by rfl⟩ : syracuseStep 868311 = 1302467) B1302467
theorem B868331 : Blo 864565 868331 := bstep (se 1 (by rfl) ⟨651248, by rfl⟩ : syracuseStep 868331 = 1302497) B1302497
theorem B868343 : Blo 864565 868343 := bstep (se 1 (by rfl) ⟨651257, by rfl⟩ : syracuseStep 868343 = 1302515) B1302515
theorem B7913477 : Blo 864565 7913477 := bstep (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) B1483777
theorem B868363 : Blo 864565 868363 := bstep (se 1 (by rfl) ⟨651272, by rfl⟩ : syracuseStep 868363 = 1302545) B1302545
theorem B3129367 : Blo 864565 3129367 := bstep (se 1 (by rfl) ⟨2347025, by rfl⟩ : syracuseStep 3129367 = 4694051) B4694051
theorem B868375 : Blo 864565 868375 := bstep (se 1 (by rfl) ⟨651281, by rfl⟩ : syracuseStep 868375 = 1302563) B1302563
theorem B868395 : Blo 864565 868395 := bstep (se 1 (by rfl) ⟨651296, by rfl⟩ : syracuseStep 868395 = 1302593) B1302593
theorem B868407 : Blo 864565 868407 := bstep (se 1 (by rfl) ⟨651305, by rfl⟩ : syracuseStep 868407 = 1302611) B1302611
theorem B30883909 : Blo 864565 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B1097803 : Blo 864565 1097803 := bstep (se 1 (by rfl) ⟨823352, by rfl⟩ : syracuseStep 1097803 = 1646705) B1646705
theorem B868427 : Blo 864565 868427 := bstep (se 1 (by rfl) ⟨651320, by rfl⟩ : syracuseStep 868427 = 1302641) B1302641
theorem B868439 : Blo 864565 868439 := bstep (se 1 (by rfl) ⟨651329, by rfl⟩ : syracuseStep 868439 = 1302659) B1302659
theorem B868459 : Blo 864565 868459 := bstep (se 1 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 868459 = 1302689) B1302689
theorem B868471 : Blo 864565 868471 := bstep (se 1 (by rfl) ⟨651353, by rfl⟩ : syracuseStep 868471 = 1302707) B1302707
theorem B868491 : Blo 864565 868491 := bstep (se 1 (by rfl) ⟨651368, by rfl⟩ : syracuseStep 868491 = 1302737) B1302737
theorem B868503 : Blo 864565 868503 := bstep (se 1 (by rfl) ⟨651377, by rfl⟩ : syracuseStep 868503 = 1302755) B1302755
theorem B1949849 : Blo 864565 1949849 := bstep (se 2 (by rfl) ⟨731193, by rfl⟩ : syracuseStep 1949849 = 1462387) B1462387
theorem B868523 : Blo 864565 868523 := bstep (se 1 (by rfl) ⟨651392, by rfl⟩ : syracuseStep 868523 = 1302785) B1302785
theorem B868535 : Blo 864565 868535 := bstep (se 1 (by rfl) ⟨651401, by rfl⟩ : syracuseStep 868535 = 1302803) B1302803
theorem B868555 : Blo 864565 868555 := bstep (se 1 (by rfl) ⟨651416, by rfl⟩ : syracuseStep 868555 = 1302833) B1302833
theorem B1949939 : Blo 864565 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B1949975 : Blo 864565 1949975 := bstep (se 1 (by rfl) ⟨1462481, by rfl⟩ : syracuseStep 1949975 = 2924963) B2924963
theorem B1950155 : Blo 864565 1950155 := bstep (se 1 (by rfl) ⟨1462616, by rfl⟩ : syracuseStep 1950155 = 2925233) B2925233
theorem B1950209 : Blo 864565 1950209 := bstep (se 2 (by rfl) ⟨731328, by rfl⟩ : syracuseStep 1950209 = 1462657) B1462657
theorem B1851979 : Blo 864565 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B3129931 : Blo 864565 3129931 := bstep (se 1 (by rfl) ⟨2347448, by rfl⟩ : syracuseStep 3129931 = 4694897) B4694897
theorem B1950425 : Blo 864565 1950425 := bstep (se 2 (by rfl) ⟨731409, by rfl⟩ : syracuseStep 1950425 = 1462819) B1462819
theorem B12468977 : Blo 864565 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B1950515 : Blo 864565 1950515 := bstep (se 1 (by rfl) ⟨1462886, by rfl⟩ : syracuseStep 1950515 = 2925773) B2925773
theorem B3130163 : Blo 864565 3130163 := bstep (se 1 (by rfl) ⟨2347622, by rfl⟩ : syracuseStep 3130163 = 4695245) B4695245
theorem B3294017 : Blo 864565 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B1459019 : Blo 864565 1459019 := bstep (se 1 (by rfl) ⟨1094264, by rfl⟩ : syracuseStep 1459019 = 2188529) B2188529
theorem B4997963 : Blo 864565 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B1950551 : Blo 864565 1950551 := bstep (se 1 (by rfl) ⟨1462913, by rfl⟩ : syracuseStep 1950551 = 2925827) B2925827
theorem B1459147 : Blo 864565 1459147 := bstep (se 1 (by rfl) ⟨1094360, by rfl⟩ : syracuseStep 1459147 = 2188721) B2188721
theorem B1950731 : Blo 864565 1950731 := bstep (se 1 (by rfl) ⟨1463048, by rfl⟩ : syracuseStep 1950731 = 2926097) B2926097
theorem B1098775 : Blo 864565 1098775 := bstep (se 1 (by rfl) ⟨824081, by rfl⟩ : syracuseStep 1098775 = 1648163) B1648163
theorem B1950785 : Blo 864565 1950785 := bstep (se 2 (by rfl) ⟨731544, by rfl⟩ : syracuseStep 1950785 = 1463089) B1463089
theorem B1459289 : Blo 864565 1459289 := bstep (se 2 (by rfl) ⟨547233, by rfl⟩ : syracuseStep 1459289 = 1094467) B1094467
theorem B2671795 : Blo 864565 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1459417 : Blo 864565 1459417 := bstep (se 2 (by rfl) ⟨547281, by rfl⟩ : syracuseStep 1459417 = 1094563) B1094563
theorem B1951001 : Blo 864565 1951001 := bstep (se 2 (by rfl) ⟨731625, by rfl⟩ : syracuseStep 1951001 = 1463251) B1463251
theorem B1852723 : Blo 864565 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B1951091 : Blo 864565 1951091 := bstep (se 1 (by rfl) ⟨1463318, by rfl⟩ : syracuseStep 1951091 = 2926637) B2926637
theorem B1951127 : Blo 864565 1951127 := bstep (se 1 (by rfl) ⟨1463345, by rfl⟩ : syracuseStep 1951127 = 2926691) B2926691
theorem B1623449 : Blo 864565 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B1754561 : Blo 864565 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B3556867 : Blo 864565 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1951307 : Blo 864565 1951307 := bstep (se 1 (by rfl) ⟨1463480, by rfl⟩ : syracuseStep 1951307 = 2926961) B2926961
theorem B1951361 : Blo 864565 1951361 := bstep (se 2 (by rfl) ⟨731760, by rfl⟩ : syracuseStep 1951361 = 1463521) B1463521
theorem B1558283 : Blo 864565 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1459991 : Blo 864565 1459991 := bstep (se 1 (by rfl) ⟨1094993, by rfl⟩ : syracuseStep 1459991 = 2189987) B2189987
theorem B1853209 : Blo 864565 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B1951577 : Blo 864565 1951577 := bstep (se 2 (by rfl) ⟨731841, by rfl⟩ : syracuseStep 1951577 = 1463683) B1463683
theorem B39929699 : Blo 864565 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B4933507 : Blo 864565 4933507 := bstep (se 1 (by rfl) ⟨3700130, by rfl⟩ : syracuseStep 4933507 = 7400261) B7400261
theorem B1460119 : Blo 864565 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B1951667 : Blo 864565 1951667 := bstep (se 1 (by rfl) ⟨1463750, by rfl⟩ : syracuseStep 1951667 = 2927501) B2927501
theorem B1951703 : Blo 864565 1951703 := bstep (se 1 (by rfl) ⟨1463777, by rfl⟩ : syracuseStep 1951703 = 2927555) B2927555
theorem B5621825 : Blo 864565 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B1951883 : Blo 864565 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B1951937 : Blo 864565 1951937 := bstep (se 2 (by rfl) ⟨731976, by rfl⟩ : syracuseStep 1951937 = 1463953) B1463953
theorem B3295505 : Blo 864565 3295505 := bstep (se 2 (by rfl) ⟨1235814, by rfl⟩ : syracuseStep 3295505 = 2471629) B2471629
theorem B1952153 : Blo 864565 1952153 := bstep (se 2 (by rfl) ⟨732057, by rfl⟩ : syracuseStep 1952153 = 1464115) B1464115
theorem B1296857 : Blo 864565 1296857 := bstep (se 2 (by rfl) ⟨486321, by rfl⟩ : syracuseStep 1296857 = 972643) B972643
theorem B1952243 : Blo 864565 1952243 := bstep (se 1 (by rfl) ⟨1464182, by rfl⟩ : syracuseStep 1952243 = 2928365) B2928365
theorem B1460747 : Blo 864565 1460747 := bstep (se 1 (by rfl) ⟨1095560, by rfl⟩ : syracuseStep 1460747 = 2191121) B2191121
theorem B1952279 : Blo 864565 1952279 := bstep (se 1 (by rfl) ⟨1464209, by rfl⟩ : syracuseStep 1952279 = 2928419) B2928419
theorem B1296971 : Blo 864565 1296971 := bstep (se 1 (by rfl) ⟨972728, by rfl⟩ : syracuseStep 1296971 = 1945457) B1945457
theorem B1296983 : Blo 864565 1296983 := bstep (se 1 (by rfl) ⟨972737, by rfl⟩ : syracuseStep 1296983 = 1945475) B1945475
theorem B1460875 : Blo 864565 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B4377239 : Blo 864565 4377239 := bstep (se 1 (by rfl) ⟨3282929, by rfl⟩ : syracuseStep 4377239 = 6565859) B6565859
theorem B1297049 : Blo 864565 1297049 := bstep (se 2 (by rfl) ⟨486393, by rfl⟩ : syracuseStep 1297049 = 972787) B972787
theorem B1952459 : Blo 864565 1952459 := bstep (se 1 (by rfl) ⟨1464344, by rfl⟩ : syracuseStep 1952459 = 2928689) B2928689
theorem B3295961 : Blo 864565 3295961 := bstep (se 2 (by rfl) ⟨1235985, by rfl⟩ : syracuseStep 3295961 = 2471971) B2471971
theorem B1952513 : Blo 864565 1952513 := bstep (se 2 (by rfl) ⟨732192, by rfl⟩ : syracuseStep 1952513 = 1464385) B1464385
theorem B1297163 : Blo 864565 1297163 := bstep (se 1 (by rfl) ⟨972872, by rfl⟩ : syracuseStep 1297163 = 1945745) B1945745
theorem B1297175 : Blo 864565 1297175 := bstep (se 1 (by rfl) ⟨972881, by rfl⟩ : syracuseStep 1297175 = 1945763) B1945763
theorem B1461017 : Blo 864565 1461017 := bstep (se 2 (by rfl) ⟨547881, by rfl⟩ : syracuseStep 1461017 = 1095763) B1095763
theorem B4934465 : Blo 864565 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B1231691 : Blo 864565 1231691 := bstep (se 1 (by rfl) ⟨923768, by rfl⟩ : syracuseStep 1231691 = 1847537) B1847537
theorem B1297241 : Blo 864565 1297241 := bstep (se 2 (by rfl) ⟨486465, by rfl⟩ : syracuseStep 1297241 = 972931) B972931
theorem B1461145 : Blo 864565 1461145 := bstep (se 2 (by rfl) ⟨547929, by rfl⟩ : syracuseStep 1461145 = 1095859) B1095859
theorem B3296173 : Blo 864565 3296173 := bstep (se 3 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 3296173 = 1236065) B1236065
theorem B1297355 : Blo 864565 1297355 := bstep (se 1 (by rfl) ⟨973016, by rfl⟩ : syracuseStep 1297355 = 1946033) B1946033
theorem B1297367 : Blo 864565 1297367 := bstep (se 1 (by rfl) ⟨973025, by rfl⟩ : syracuseStep 1297367 = 1946051) B1946051
theorem B1952729 : Blo 864565 1952729 := bstep (se 2 (by rfl) ⟨732273, by rfl⟩ : syracuseStep 1952729 = 1464547) B1464547
theorem B1297433 : Blo 864565 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B1952819 : Blo 864565 1952819 := bstep (se 1 (by rfl) ⟨1464614, by rfl⟩ : syracuseStep 1952819 = 2929229) B2929229
theorem B1952855 : Blo 864565 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B6573149 : Blo 864565 6573149 := bstep (se 3 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 6573149 = 2464931) B2464931
theorem B5557349 : Blo 864565 5557349 := bstep (se 4 (by rfl) ⟨521001, by rfl⟩ : syracuseStep 5557349 = 1042003) B1042003
theorem B1297547 : Blo 864565 1297547 := bstep (se 1 (by rfl) ⟨973160, by rfl⟩ : syracuseStep 1297547 = 1946321) B1946321
theorem B1297559 : Blo 864565 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B1756313 : Blo 864565 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B1854679 : Blo 864565 1854679 := bstep (se 1 (by rfl) ⟨1391009, by rfl⟩ : syracuseStep 1854679 = 2782019) B2782019
theorem B1297625 : Blo 864565 1297625 := bstep (se 2 (by rfl) ⟨486609, by rfl⟩ : syracuseStep 1297625 = 973219) B973219
theorem B3296477 : Blo 864565 3296477 := bstep (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) B1236179
theorem B1953035 : Blo 864565 1953035 := bstep (se 1 (by rfl) ⟨1464776, by rfl⟩ : syracuseStep 1953035 = 2929553) B2929553
theorem B1854731 : Blo 864565 1854731 := bstep (se 1 (by rfl) ⟨1391048, by rfl⟩ : syracuseStep 1854731 = 2782097) B2782097
theorem B3755315 : Blo 864565 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B1953089 : Blo 864565 1953089 := bstep (se 2 (by rfl) ⟨732408, by rfl⟩ : syracuseStep 1953089 = 1464817) B1464817
theorem B1297739 : Blo 864565 1297739 := bstep (se 1 (by rfl) ⟨973304, by rfl⟩ : syracuseStep 1297739 = 1946609) B1946609
theorem B1297751 : Blo 864565 1297751 := bstep (se 1 (by rfl) ⟨973313, by rfl⟩ : syracuseStep 1297751 = 1946627) B1946627
theorem B1297817 : Blo 864565 1297817 := bstep (se 2 (by rfl) ⟨486681, by rfl⟩ : syracuseStep 1297817 = 973363) B973363
theorem B1461719 : Blo 864565 1461719 := bstep (se 1 (by rfl) ⟨1096289, by rfl⟩ : syracuseStep 1461719 = 2192579) B2192579
theorem B1297931 : Blo 864565 1297931 := bstep (se 1 (by rfl) ⟨973448, by rfl⟩ : syracuseStep 1297931 = 1946897) B1946897
theorem B1297943 : Blo 864565 1297943 := bstep (se 1 (by rfl) ⟨973457, by rfl⟩ : syracuseStep 1297943 = 1946915) B1946915
theorem B1953305 : Blo 864565 1953305 := bstep (se 2 (by rfl) ⟨732489, by rfl⟩ : syracuseStep 1953305 = 1464979) B1464979
theorem B5557835 : Blo 864565 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B1461847 : Blo 864565 1461847 := bstep (se 1 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 1461847 = 2192771) B2192771
theorem B1298009 : Blo 864565 1298009 := bstep (se 2 (by rfl) ⟨486753, by rfl⟩ : syracuseStep 1298009 = 973507) B973507
theorem B1953395 : Blo 864565 1953395 := bstep (se 1 (by rfl) ⟨1465046, by rfl⟩ : syracuseStep 1953395 = 2930093) B2930093
theorem B6016643 : Blo 864565 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B1953431 : Blo 864565 1953431 := bstep (se 1 (by rfl) ⟨1465073, by rfl⟩ : syracuseStep 1953431 = 2930147) B2930147
theorem B2084545 : Blo 864565 2084545 := bstep (se 2 (by rfl) ⟨781704, by rfl⟩ : syracuseStep 2084545 = 1563409) B1563409
theorem B1298123 : Blo 864565 1298123 := bstep (se 1 (by rfl) ⟨973592, by rfl⟩ : syracuseStep 1298123 = 1947185) B1947185
theorem B1298135 : Blo 864565 1298135 := bstep (se 1 (by rfl) ⟨973601, by rfl⟩ : syracuseStep 1298135 = 1947203) B1947203
theorem B1298201 : Blo 864565 1298201 := bstep (se 2 (by rfl) ⟨486825, by rfl⟩ : syracuseStep 1298201 = 973651) B973651
theorem B1953611 : Blo 864565 1953611 := bstep (se 1 (by rfl) ⟨1465208, by rfl⟩ : syracuseStep 1953611 = 2930417) B2930417
theorem B1953665 : Blo 864565 1953665 := bstep (se 2 (by rfl) ⟨732624, by rfl⟩ : syracuseStep 1953665 = 1465249) B1465249
theorem B1298315 : Blo 864565 1298315 := bstep (se 1 (by rfl) ⟨973736, by rfl⟩ : syracuseStep 1298315 = 1947473) B1947473
theorem B1298327 : Blo 864565 1298327 := bstep (se 1 (by rfl) ⟨973745, by rfl⟩ : syracuseStep 1298327 = 1947491) B1947491
theorem B1298393 : Blo 864565 1298393 := bstep (se 2 (by rfl) ⟨486897, by rfl⟩ : syracuseStep 1298393 = 973795) B973795
theorem B1298507 : Blo 864565 1298507 := bstep (se 1 (by rfl) ⟨973880, by rfl⟩ : syracuseStep 1298507 = 1947761) B1947761
theorem B1298519 : Blo 864565 1298519 := bstep (se 1 (by rfl) ⟨973889, by rfl⟩ : syracuseStep 1298519 = 1947779) B1947779
theorem B1953881 : Blo 864565 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B1298585 : Blo 864565 1298585 := bstep (se 2 (by rfl) ⟨486969, by rfl⟩ : syracuseStep 1298585 = 973939) B973939
theorem B1953971 : Blo 864565 1953971 := bstep (se 1 (by rfl) ⟨1465478, by rfl⟩ : syracuseStep 1953971 = 2930957) B2930957
theorem B1462475 : Blo 864565 1462475 := bstep (se 1 (by rfl) ⟨1096856, by rfl⟩ : syracuseStep 1462475 = 2193713) B2193713
theorem B1954007 : Blo 864565 1954007 := bstep (se 1 (by rfl) ⟨1465505, by rfl⟩ : syracuseStep 1954007 = 2931011) B2931011
theorem B1298699 : Blo 864565 1298699 := bstep (se 1 (by rfl) ⟨974024, by rfl⟩ : syracuseStep 1298699 = 1948049) B1948049
theorem B1298711 : Blo 864565 1298711 := bstep (se 1 (by rfl) ⟨974033, by rfl⟩ : syracuseStep 1298711 = 1948067) B1948067
theorem B1462603 : Blo 864565 1462603 := bstep (se 1 (by rfl) ⟨1096952, by rfl⟩ : syracuseStep 1462603 = 2193905) B2193905
theorem B1298777 : Blo 864565 1298777 := bstep (se 2 (by rfl) ⟨487041, by rfl⟩ : syracuseStep 1298777 = 974083) B974083
theorem B1954187 : Blo 864565 1954187 := bstep (se 1 (by rfl) ⟨1465640, by rfl⟩ : syracuseStep 1954187 = 2931281) B2931281
theorem B1954241 : Blo 864565 1954241 := bstep (se 2 (by rfl) ⟨732840, by rfl⟩ : syracuseStep 1954241 = 1465681) B1465681
theorem B1298891 : Blo 864565 1298891 := bstep (se 1 (by rfl) ⟨974168, by rfl⟩ : syracuseStep 1298891 = 1948337) B1948337
theorem B1298903 : Blo 864565 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B1462745 : Blo 864565 1462745 := bstep (se 2 (by rfl) ⟨548529, by rfl⟩ : syracuseStep 1462745 = 1097059) B1097059
theorem B2347481 : Blo 864565 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B1298969 : Blo 864565 1298969 := bstep (se 2 (by rfl) ⟨487113, by rfl⟩ : syracuseStep 1298969 = 974227) B974227
theorem B1462873 : Blo 864565 1462873 := bstep (se 2 (by rfl) ⟨548577, by rfl⟩ : syracuseStep 1462873 = 1097155) B1097155
theorem B1299083 : Blo 864565 1299083 := bstep (se 1 (by rfl) ⟨974312, by rfl⟩ : syracuseStep 1299083 = 1948625) B1948625
theorem B1299095 : Blo 864565 1299095 := bstep (se 1 (by rfl) ⟨974321, by rfl⟩ : syracuseStep 1299095 = 1948643) B1948643
theorem B1233559 : Blo 864565 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B2708147 : Blo 864565 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B1299161 : Blo 864565 1299161 := bstep (se 2 (by rfl) ⟨487185, by rfl⟩ : syracuseStep 1299161 = 974371) B974371
theorem B1299275 : Blo 864565 1299275 := bstep (se 1 (by rfl) ⟨974456, by rfl⟩ : syracuseStep 1299275 = 1948913) B1948913
theorem B1299287 : Blo 864565 1299287 := bstep (se 1 (by rfl) ⟨974465, by rfl⟩ : syracuseStep 1299287 = 1948931) B1948931
theorem B1299353 : Blo 864565 1299353 := bstep (se 2 (by rfl) ⟨487257, by rfl⟩ : syracuseStep 1299353 = 974515) B974515
theorem B1299467 : Blo 864565 1299467 := bstep (se 1 (by rfl) ⟨974600, by rfl⟩ : syracuseStep 1299467 = 1949201) B1949201
theorem B1299479 : Blo 864565 1299479 := bstep (se 1 (by rfl) ⟨974609, by rfl⟩ : syracuseStep 1299479 = 1949219) B1949219
theorem B1299545 : Blo 864565 1299545 := bstep (se 2 (by rfl) ⟨487329, by rfl⟩ : syracuseStep 1299545 = 974659) B974659
theorem B1463447 : Blo 864565 1463447 := bstep (se 1 (by rfl) ⟨1097585, by rfl⟩ : syracuseStep 1463447 = 2195171) B2195171
theorem B1266841 : Blo 864565 1266841 := bstep (se 2 (by rfl) ⟨475065, by rfl⟩ : syracuseStep 1266841 = 950131) B950131
theorem B5559475 : Blo 864565 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B1299659 : Blo 864565 1299659 := bstep (se 1 (by rfl) ⟨974744, by rfl⟩ : syracuseStep 1299659 = 1949489) B1949489
theorem B2086091 : Blo 864565 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B1299671 : Blo 864565 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B1463575 : Blo 864565 1463575 := bstep (se 1 (by rfl) ⟨1097681, by rfl⟩ : syracuseStep 1463575 = 2195363) B2195363
theorem B1299737 : Blo 864565 1299737 := bstep (se 2 (by rfl) ⟨487401, by rfl⟩ : syracuseStep 1299737 = 974803) B974803
theorem B1299851 : Blo 864565 1299851 := bstep (se 1 (by rfl) ⟨974888, by rfl⟩ : syracuseStep 1299851 = 1949777) B1949777
theorem B1299863 : Blo 864565 1299863 := bstep (se 1 (by rfl) ⟨974897, by rfl⟩ : syracuseStep 1299863 = 1949795) B1949795
theorem B1299929 : Blo 864565 1299929 := bstep (se 2 (by rfl) ⟨487473, by rfl⟩ : syracuseStep 1299929 = 974947) B974947
theorem B2086361 : Blo 864565 2086361 := bstep (se 2 (by rfl) ⟨782385, by rfl⟩ : syracuseStep 2086361 = 1564771) B1564771
theorem B1300043 : Blo 864565 1300043 := bstep (se 1 (by rfl) ⟨975032, by rfl⟩ : syracuseStep 1300043 = 1950065) B1950065
theorem B1300055 : Blo 864565 1300055 := bstep (se 1 (by rfl) ⟨975041, by rfl⟩ : syracuseStep 1300055 = 1950083) B1950083
theorem B1300121 : Blo 864565 1300121 := bstep (se 2 (by rfl) ⟨487545, by rfl⟩ : syracuseStep 1300121 = 975091) B975091
theorem B1300235 : Blo 864565 1300235 := bstep (se 1 (by rfl) ⟨975176, by rfl⟩ : syracuseStep 1300235 = 1950353) B1950353
theorem B1300247 : Blo 864565 1300247 := bstep (se 1 (by rfl) ⟨975185, by rfl⟩ : syracuseStep 1300247 = 1950371) B1950371
theorem B7395137 : Blo 864565 7395137 := bstep (se 2 (by rfl) ⟨2773176, by rfl⟩ : syracuseStep 7395137 = 5546353) B5546353
theorem B1300313 : Blo 864565 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B1464203 : Blo 864565 1464203 := bstep (se 1 (by rfl) ⟨1098152, by rfl⟩ : syracuseStep 1464203 = 2196305) B2196305
theorem B972715 : Blo 864565 972715 := bstep (se 1 (by rfl) ⟨729536, by rfl⟩ : syracuseStep 972715 = 1459073) B1459073
theorem B1300427 : Blo 864565 1300427 := bstep (se 1 (by rfl) ⟨975320, by rfl⟩ : syracuseStep 1300427 = 1950641) B1950641
theorem B1300439 : Blo 864565 1300439 := bstep (se 1 (by rfl) ⟨975329, by rfl⟩ : syracuseStep 1300439 = 1950659) B1950659
theorem B1464331 : Blo 864565 1464331 := bstep (se 1 (by rfl) ⟨1098248, by rfl⟩ : syracuseStep 1464331 = 2196497) B2196497
theorem B972823 : Blo 864565 972823 := bstep (se 1 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 972823 = 1459235) B1459235
theorem B1300505 : Blo 864565 1300505 := bstep (se 2 (by rfl) ⟨487689, by rfl⟩ : syracuseStep 1300505 = 975379) B975379
theorem B4380803 : Blo 864565 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B1300619 : Blo 864565 1300619 := bstep (se 1 (by rfl) ⟨975464, by rfl⟩ : syracuseStep 1300619 = 1950929) B1950929
theorem B1300631 : Blo 864565 1300631 := bstep (se 1 (by rfl) ⟨975473, by rfl⟩ : syracuseStep 1300631 = 1950947) B1950947
theorem B1464473 : Blo 864565 1464473 := bstep (se 2 (by rfl) ⟨549177, by rfl⟩ : syracuseStep 1464473 = 1098355) B1098355
theorem B12507317 : Blo 864565 12507317 := bstep (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) B1172561
theorem B973003 : Blo 864565 973003 := bstep (se 1 (by rfl) ⟨729752, by rfl⟩ : syracuseStep 973003 = 1459505) B1459505
theorem B1300697 : Blo 864565 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B5921041 : Blo 864565 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1464601 : Blo 864565 1464601 := bstep (se 2 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 1464601 = 1098451) B1098451
theorem B973111 : Blo 864565 973111 := bstep (se 1 (by rfl) ⟨729833, by rfl⟩ : syracuseStep 973111 = 1459667) B1459667
theorem B5921099 : Blo 864565 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1300811 : Blo 864565 1300811 := bstep (se 1 (by rfl) ⟨975608, by rfl⟩ : syracuseStep 1300811 = 1951217) B1951217
theorem B1300823 : Blo 864565 1300823 := bstep (se 1 (by rfl) ⟨975617, by rfl⟩ : syracuseStep 1300823 = 1951235) B1951235
theorem B1300889 : Blo 864565 1300889 := bstep (se 2 (by rfl) ⟨487833, by rfl⟩ : syracuseStep 1300889 = 975667) B975667
theorem B973291 : Blo 864565 973291 := bstep (se 1 (by rfl) ⟨729968, by rfl⟩ : syracuseStep 973291 = 1459937) B1459937
theorem B3693059 : Blo 864565 3693059 := bstep (se 1 (by rfl) ⟨2769794, by rfl⟩ : syracuseStep 3693059 = 5539589) B5539589
theorem B1301003 : Blo 864565 1301003 := bstep (se 1 (by rfl) ⟨975752, by rfl⟩ : syracuseStep 1301003 = 1951505) B1951505
theorem B1301015 : Blo 864565 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B973399 : Blo 864565 973399 := bstep (se 1 (by rfl) ⟨730049, by rfl⟩ : syracuseStep 973399 = 1460099) B1460099
theorem B1301081 : Blo 864565 1301081 := bstep (se 2 (by rfl) ⟨487905, by rfl⟩ : syracuseStep 1301081 = 975811) B975811
theorem B1759937 : Blo 864565 1759937 := bstep (se 2 (by rfl) ⟨659976, by rfl⟩ : syracuseStep 1759937 = 1319953) B1319953
theorem B1301195 : Blo 864565 1301195 := bstep (se 1 (by rfl) ⟨975896, by rfl⟩ : syracuseStep 1301195 = 1951793) B1951793
theorem B6675149 : Blo 864565 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B1301207 : Blo 864565 1301207 := bstep (se 1 (by rfl) ⟨975905, by rfl⟩ : syracuseStep 1301207 = 1951811) B1951811
theorem B973579 : Blo 864565 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B1301273 : Blo 864565 1301273 := bstep (se 2 (by rfl) ⟨487977, by rfl⟩ : syracuseStep 1301273 = 975955) B975955
theorem B6249251 : Blo 864565 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B1465175 : Blo 864565 1465175 := bstep (se 1 (by rfl) ⟨1098881, by rfl⟩ : syracuseStep 1465175 = 2197763) B2197763
theorem B973687 : Blo 864565 973687 := bstep (se 1 (by rfl) ⟨730265, by rfl⟩ : syracuseStep 973687 = 1460531) B1460531
theorem B1301387 : Blo 864565 1301387 := bstep (se 1 (by rfl) ⟨976040, by rfl⟩ : syracuseStep 1301387 = 1952081) B1952081
theorem B1301399 : Blo 864565 1301399 := bstep (se 1 (by rfl) ⟨976049, by rfl⟩ : syracuseStep 1301399 = 1952099) B1952099
theorem B1465303 : Blo 864565 1465303 := bstep (se 1 (by rfl) ⟨1098977, by rfl⟩ : syracuseStep 1465303 = 2197955) B2197955
theorem B1301465 : Blo 864565 1301465 := bstep (se 2 (by rfl) ⟨488049, by rfl⟩ : syracuseStep 1301465 = 976099) B976099
theorem B973867 : Blo 864565 973867 := bstep (se 1 (by rfl) ⟨730400, by rfl⟩ : syracuseStep 973867 = 1460801) B1460801
theorem B1301579 : Blo 864565 1301579 := bstep (se 1 (by rfl) ⟨976184, by rfl⟩ : syracuseStep 1301579 = 1952369) B1952369
theorem B1301591 : Blo 864565 1301591 := bstep (se 1 (by rfl) ⟨976193, by rfl⟩ : syracuseStep 1301591 = 1952387) B1952387
theorem B11099267 : Blo 864565 11099267 := bstep (se 1 (by rfl) ⟨8324450, by rfl⟩ : syracuseStep 11099267 = 16648901) B16648901
theorem B973975 : Blo 864565 973975 := bstep (se 1 (by rfl) ⟨730481, by rfl⟩ : syracuseStep 973975 = 1460963) B1460963
theorem B1301657 : Blo 864565 1301657 := bstep (se 2 (by rfl) ⟨488121, by rfl⟩ : syracuseStep 1301657 = 976243) B976243
theorem B1301771 : Blo 864565 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B1301783 : Blo 864565 1301783 := bstep (se 1 (by rfl) ⟨976337, by rfl⟩ : syracuseStep 1301783 = 1952675) B1952675
theorem B974155 : Blo 864565 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B1301849 : Blo 864565 1301849 := bstep (se 2 (by rfl) ⟨488193, by rfl⟩ : syracuseStep 1301849 = 976387) B976387
theorem B974263 : Blo 864565 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B1301963 : Blo 864565 1301963 := bstep (se 1 (by rfl) ⟨976472, by rfl⟩ : syracuseStep 1301963 = 1952945) B1952945
theorem B1301975 : Blo 864565 1301975 := bstep (se 1 (by rfl) ⟨976481, by rfl⟩ : syracuseStep 1301975 = 1952963) B1952963
theorem B1302041 : Blo 864565 1302041 := bstep (se 2 (by rfl) ⟨488265, by rfl⟩ : syracuseStep 1302041 = 976531) B976531
theorem B4939339 : Blo 864565 4939339 := bstep (se 1 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 4939339 = 7409009) B7409009
theorem B8347211 : Blo 864565 8347211 := bstep (se 1 (by rfl) ⟨6260408, by rfl⟩ : syracuseStep 8347211 = 12520817) B12520817
theorem B974443 : Blo 864565 974443 := bstep (se 1 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 974443 = 1461665) B1461665
theorem B1302155 : Blo 864565 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B1302167 : Blo 864565 1302167 := bstep (se 1 (by rfl) ⟨976625, by rfl⟩ : syracuseStep 1302167 = 1953251) B1953251
theorem B974551 : Blo 864565 974551 := bstep (se 1 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 974551 = 1461827) B1461827
theorem B1302233 : Blo 864565 1302233 := bstep (se 2 (by rfl) ⟨488337, by rfl⟩ : syracuseStep 1302233 = 976675) B976675
theorem B1302347 : Blo 864565 1302347 := bstep (se 1 (by rfl) ⟨976760, by rfl⟩ : syracuseStep 1302347 = 1953521) B1953521
theorem B1302359 : Blo 864565 1302359 := bstep (se 1 (by rfl) ⟨976769, by rfl⟩ : syracuseStep 1302359 = 1953539) B1953539
theorem B1564505 : Blo 864565 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B4939613 : Blo 864565 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B974731 : Blo 864565 974731 := bstep (se 1 (by rfl) ⟨731048, by rfl⟩ : syracuseStep 974731 = 1462097) B1462097
theorem B1171351 : Blo 864565 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B1302425 : Blo 864565 1302425 := bstep (se 2 (by rfl) ⟨488409, by rfl⟩ : syracuseStep 1302425 = 976819) B976819
theorem B974839 : Blo 864565 974839 := bstep (se 1 (by rfl) ⟨731129, by rfl⟩ : syracuseStep 974839 = 1462259) B1462259
theorem B1302539 : Blo 864565 1302539 := bstep (se 1 (by rfl) ⟨976904, by rfl⟩ : syracuseStep 1302539 = 1953809) B1953809
theorem B1302551 : Blo 864565 1302551 := bstep (se 1 (by rfl) ⟨976913, by rfl⟩ : syracuseStep 1302551 = 1953827) B1953827
theorem B1302617 : Blo 864565 1302617 := bstep (se 2 (by rfl) ⟨488481, by rfl⟩ : syracuseStep 1302617 = 976963) B976963
theorem B7397527 : Blo 864565 7397527 := bstep (se 1 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 7397527 = 11096291) B11096291
theorem B975019 : Blo 864565 975019 := bstep (se 1 (by rfl) ⟨731264, by rfl⟩ : syracuseStep 975019 = 1462529) B1462529
theorem B1302731 : Blo 864565 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B1302743 : Blo 864565 1302743 := bstep (se 1 (by rfl) ⟨977057, by rfl⟩ : syracuseStep 1302743 = 1954115) B1954115
theorem B1564915 : Blo 864565 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B975127 : Blo 864565 975127 := bstep (se 1 (by rfl) ⟨731345, by rfl⟩ : syracuseStep 975127 = 1462691) B1462691
theorem B1302809 : Blo 864565 1302809 := bstep (se 2 (by rfl) ⟨488553, by rfl⟩ : syracuseStep 1302809 = 977107) B977107
theorem B1171865 : Blo 864565 1171865 := bstep (se 2 (by rfl) ⟨439449, by rfl⟩ : syracuseStep 1171865 = 878899) B878899
theorem B975307 : Blo 864565 975307 := bstep (se 1 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 975307 = 1462961) B1462961
theorem B3334621 : Blo 864565 3334621 := bstep (se 3 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 3334621 = 1250483) B1250483
theorem B975415 : Blo 864565 975415 := bstep (se 1 (by rfl) ⟨731561, by rfl⟩ : syracuseStep 975415 = 1463123) B1463123
theorem B975595 : Blo 864565 975595 := bstep (se 1 (by rfl) ⟨731696, by rfl⟩ : syracuseStep 975595 = 1463393) B1463393
theorem B975703 : Blo 864565 975703 := bstep (se 1 (by rfl) ⟨731777, by rfl⟩ : syracuseStep 975703 = 1463555) B1463555
theorem B975883 : Blo 864565 975883 := bstep (se 1 (by rfl) ⟨731912, by rfl⟩ : syracuseStep 975883 = 1463825) B1463825
theorem B975991 : Blo 864565 975991 := bstep (se 1 (by rfl) ⟨731993, by rfl⟩ : syracuseStep 975991 = 1463987) B1463987
theorem B976171 : Blo 864565 976171 := bstep (se 1 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 976171 = 1464257) B1464257
theorem B976279 : Blo 864565 976279 := bstep (se 1 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 976279 = 1464419) B1464419
theorem B8316377 : Blo 864565 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B1041931 : Blo 864565 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B3696151 : Blo 864565 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B976459 : Blo 864565 976459 := bstep (se 1 (by rfl) ⟨732344, by rfl⟩ : syracuseStep 976459 = 1464689) B1464689
theorem B976567 : Blo 864565 976567 := bstep (se 1 (by rfl) ⟨732425, by rfl⟩ : syracuseStep 976567 = 1464851) B1464851
theorem B4384529 : Blo 864565 4384529 := bstep (se 2 (by rfl) ⟨1644198, by rfl⟩ : syracuseStep 4384529 = 3288397) B3288397
theorem B976747 : Blo 864565 976747 := bstep (se 1 (by rfl) ⟨732560, by rfl⟩ : syracuseStep 976747 = 1465121) B1465121
theorem B2189207 : Blo 864565 2189207 := bstep (se 1 (by rfl) ⟨1641905, by rfl⟩ : syracuseStep 2189207 = 3283811) B3283811
theorem B4384691 : Blo 864565 4384691 := bstep (se 1 (by rfl) ⟨3288518, by rfl⟩ : syracuseStep 4384691 = 6577037) B6577037
theorem B4220851 : Blo 864565 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B3172289 : Blo 864565 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B976855 : Blo 864565 976855 := bstep (se 1 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 976855 = 1465283) B1465283
theorem B54716485 : Blo 864565 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B977035 : Blo 864565 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B878935 : Blo 864565 878935 := bstep (se 1 (by rfl) ⟨659201, by rfl⟩ : syracuseStep 878935 = 1318403) B1318403
theorem B2779609 : Blo 864565 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B2189875 : Blo 864565 2189875 := bstep (se 1 (by rfl) ⟨1642406, by rfl⟩ : syracuseStep 2189875 = 3284813) B3284813
theorem B10119755 : Blo 864565 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B2190017 : Blo 864565 2190017 := bstep (se 2 (by rfl) ⟨821256, by rfl⟩ : syracuseStep 2190017 = 1642513) B1642513
theorem B3959513 : Blo 864565 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B15199301 : Blo 864565 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B7892099 : Blo 864565 7892099 := bstep (se 1 (by rfl) ⟨5919074, by rfl⟩ : syracuseStep 7892099 = 11838149) B11838149
theorem B2780993 : Blo 864565 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B4386635 : Blo 864565 4386635 := bstep (se 1 (by rfl) ⟨3289976, by rfl⟩ : syracuseStep 4386635 = 6579953) B6579953
theorem B9858995 : Blo 864565 9858995 := bstep (se 1 (by rfl) ⟨7394246, by rfl⟩ : syracuseStep 9858995 = 14788493) B14788493
theorem B2191283 : Blo 864565 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B3699037 : Blo 864565 3699037 := bstep (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) B1387139
theorem B2191819 : Blo 864565 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B63336977 : Blo 864565 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B2191961 : Blo 864565 2191961 := bstep (se 2 (by rfl) ⟨821985, by rfl⟩ : syracuseStep 2191961 = 1643971) B1643971
theorem B5010221 : Blo 864565 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B2257739 : Blo 864565 2257739 := bstep (se 1 (by rfl) ⟨1693304, by rfl⟩ : syracuseStep 2257739 = 3386609) B3386609
theorem B14775371 : Blo 864565 14775371 := bstep (se 1 (by rfl) ⟨11081528, by rfl⟩ : syracuseStep 14775371 = 22163057) B22163057
theorem B4944989 : Blo 864565 4944989 := bstep (se 3 (by rfl) ⟨927185, by rfl⟩ : syracuseStep 4944989 = 1854371) B1854371
theorem B3699857 : Blo 864565 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B9860453 : Blo 864565 9860453 := bstep (se 4 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 9860453 = 1848835) B1848835
theorem B2192791 : Blo 864565 2192791 := bstep (se 1 (by rfl) ⟨1644593, by rfl⟩ : syracuseStep 2192791 = 3289187) B3289187
theorem B4388417 : Blo 864565 4388417 := bstep (se 2 (by rfl) ⟨1645656, by rfl⟩ : syracuseStep 4388417 = 3291313) B3291313
theorem B5273267 : Blo 864565 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B15791917 : Blo 864565 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B3700525 : Blo 864565 3700525 := bstep (se 3 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 3700525 = 1387697) B1387697
theorem B2193227 : Blo 864565 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B5928977 : Blo 864565 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B2193601 : Blo 864565 2193601 := bstep (se 2 (by rfl) ⟨822600, by rfl⟩ : syracuseStep 2193601 = 1645201) B1645201
theorem B3701123 : Blo 864565 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B1669835 : Blo 864565 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B2194199 : Blo 864565 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B10026019 : Blo 864565 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B8879179 : Blo 864565 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B4750609 : Blo 864565 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B7896365 : Blo 864565 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B4685273 : Blo 864565 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B4390361 : Blo 864565 4390361 := bstep (se 2 (by rfl) ⟨1646385, by rfl⟩ : syracuseStep 4390361 = 3292771) B3292771
theorem B2195009 : Blo 864565 2195009 := bstep (se 2 (by rfl) ⟨823128, by rfl⟩ : syracuseStep 2195009 = 1646257) B1646257
theorem B21102605 : Blo 864565 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B9863369 : Blo 864565 9863369 := bstep (se 2 (by rfl) ⟨3698763, by rfl⟩ : syracuseStep 9863369 = 7397527) B7397527
theorem B2195657 : Blo 864565 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B2196011 : Blo 864565 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B8913665 : Blo 864565 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B1082299 : Blo 864565 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B2197003 : Blo 864565 2197003 := bstep (se 1 (by rfl) ⟨1647752, by rfl⟩ : syracuseStep 2197003 = 3295505) B3295505
theorem B2197145 : Blo 864565 2197145 := bstep (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) B1647859
theorem B2918159 : Blo 864565 2918159 := bstep (se 1 (by rfl) ⟨2188619, by rfl⟩ : syracuseStep 2918159 = 4377239) B4377239
theorem B2197307 : Blo 864565 2197307 := bstep (se 1 (by rfl) ⟨1647980, by rfl⟩ : syracuseStep 2197307 = 3295961) B3295961
theorem B2918429 : Blo 864565 2918429 := bstep (se 3 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 2918429 = 1094411) B1094411
theorem B3704899 : Blo 864565 3704899 := bstep (se 1 (by rfl) ⟨2778674, by rfl⟩ : syracuseStep 3704899 = 5557349) B5557349
theorem B2197651 : Blo 864565 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B2197793 : Blo 864565 2197793 := bstep (se 2 (by rfl) ⟨824172, by rfl⟩ : syracuseStep 2197793 = 1648345) B1648345
theorem B3705223 : Blo 864565 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B2886187 : Blo 864565 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B5082065 : Blo 864565 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B9866285 : Blo 864565 9866285 := bstep (se 3 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 9866285 = 3699857) B3699857
theorem B1805431 : Blo 864565 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B3706145 : Blo 864565 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B2919833 : Blo 864565 2919833 := bstep (se 2 (by rfl) ⟨1094937, by rfl⟩ : syracuseStep 2919833 = 2189875) B2189875
theorem B1642027 : Blo 864565 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1642103 : Blo 864565 1642103 := bstep (se 1 (by rfl) ⟨1231577, by rfl⟩ : syracuseStep 1642103 = 2463155) B2463155
theorem B7016165 : Blo 864565 7016165 := bstep (se 4 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 7016165 = 1315531) B1315531
theorem B4394897 : Blo 864565 4394897 := bstep (se 2 (by rfl) ⟨1648086, by rfl⟩ : syracuseStep 4394897 = 3296173) B3296173
theorem B2920535 : Blo 864565 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B17797441 : Blo 864565 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B2462039 : Blo 864565 2462039 := bstep (se 1 (by rfl) ⟨1846529, by rfl⟩ : syracuseStep 2462039 = 3693059) B3693059
theorem B14062045 : Blo 864565 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B4166167 : Blo 864565 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B2921021 : Blo 864565 2921021 := bstep (se 3 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 2921021 = 1095383) B1095383
theorem B1315703 : Blo 864565 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1315769 : Blo 864565 1315769 := bstep (se 2 (by rfl) ⟨493413, by rfl⟩ : syracuseStep 1315769 = 986827) B986827
theorem B11080709 : Blo 864565 11080709 := bstep (se 4 (by rfl) ⟨1038816, by rfl⟩ : syracuseStep 11080709 = 2077633) B2077633
theorem B8459437 : Blo 864565 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B1316359 : Blo 864565 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B1644047 : Blo 864565 1644047 := bstep (se 1 (by rfl) ⟨1233035, by rfl⟩ : syracuseStep 1644047 = 2466071) B2466071
theorem B2922425 : Blo 864565 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B4397003 : Blo 864565 4397003 := bstep (se 1 (by rfl) ⟨3297752, by rfl⟩ : syracuseStep 4397003 = 6595505) B6595505
theorem B2463929 : Blo 864565 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B5544251 : Blo 864565 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B2923019 : Blo 864565 2923019 := bstep (se 1 (by rfl) ⟨2192264, by rfl⟩ : syracuseStep 2923019 = 4384529) B4384529
theorem B3283523 : Blo 864565 3283523 := bstep (se 1 (by rfl) ⟨2462642, by rfl⟩ : syracuseStep 3283523 = 4925285) B4925285
theorem B2923127 : Blo 864565 2923127 := bstep (se 1 (by rfl) ⟨2192345, by rfl⟩ : syracuseStep 2923127 = 4384691) B4384691
theorem B7412633 : Blo 864565 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B1645687 : Blo 864565 1645687 := bstep (se 1 (by rfl) ⟨1234265, by rfl⟩ : syracuseStep 1645687 = 2468531) B2468531
theorem B2923721 : Blo 864565 2923721 := bstep (se 2 (by rfl) ⟨1096395, by rfl⟩ : syracuseStep 2923721 = 2192791) B2192791
theorem B1318135 : Blo 864565 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B10132867 : Blo 864565 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B3284509 : Blo 864565 3284509 := bstep (se 3 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 3284509 = 1231691) B1231691
theorem B2465569 : Blo 864565 2465569 := bstep (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) B1849177
theorem B2924423 : Blo 864565 2924423 := bstep (se 1 (by rfl) ⟨2193317, by rfl⟩ : syracuseStep 2924423 = 4386635) B4386635
theorem B2924801 : Blo 864565 2924801 := bstep (se 2 (by rfl) ⟨1096800, by rfl⟩ : syracuseStep 2924801 = 2193601) B2193601
theorem B6234515 : Blo 864565 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B1647479 : Blo 864565 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B1647631 : Blo 864565 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B2466845 : Blo 864565 2466845 := bstep (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) B925067
theorem B2925611 : Blo 864565 2925611 := bstep (se 1 (by rfl) ⟨2194208, by rfl⟩ : syracuseStep 2925611 = 4388417) B4388417
theorem B2467073 : Blo 864565 2467073 := bstep (se 2 (by rfl) ⟨925152, by rfl⟩ : syracuseStep 2467073 = 1850305) B1850305
theorem B1648019 : Blo 864565 1648019 := bstep (se 1 (by rfl) ⟨1236014, by rfl⟩ : syracuseStep 1648019 = 2472029) B2472029
theorem B11838905 : Blo 864565 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B2467415 : Blo 864565 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B6334145 : Blo 864565 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B2467529 : Blo 864565 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B1976363 : Blo 864565 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B7415981 : Blo 864565 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B3123515 : Blo 864565 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B2926907 : Blo 864565 2926907 := bstep (se 1 (by rfl) ⟨2195180, by rfl⟩ : syracuseStep 2926907 = 4390361) B4390361
theorem B3287411 : Blo 864565 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B4172489 : Blo 864565 4172489 := bstep (se 2 (by rfl) ⟨1564683, by rfl⟩ : syracuseStep 4172489 = 3129367) B3129367
theorem B19999493 : Blo 864565 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B2927393 : Blo 864565 2927393 := bstep (se 2 (by rfl) ⟨1097772, by rfl⟩ : syracuseStep 2927393 = 2195545) B2195545
theorem B36547789 : Blo 864565 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B2632961 : Blo 864565 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B2927987 : Blo 864565 2927987 := bstep (se 1 (by rfl) ⟨2195990, by rfl⟩ : syracuseStep 2927987 = 4391981) B4391981
theorem B2469305 : Blo 864565 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B14069177 : Blo 864565 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B4173241 : Blo 864565 4173241 := bstep (se 2 (by rfl) ⟨1564965, by rfl⟩ : syracuseStep 4173241 = 3129931) B3129931
theorem B3124973 : Blo 864565 3124973 := bstep (se 3 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 3124973 = 1171865) B1171865
theorem B1945403 : Blo 864565 1945403 := bstep (se 1 (by rfl) ⟨1459052, by rfl⟩ : syracuseStep 1945403 = 2918105) B2918105
theorem B26619799 : Blo 864565 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1945529 : Blo 864565 1945529 := bstep (se 2 (by rfl) ⟨729573, by rfl⟩ : syracuseStep 1945529 = 1459147) B1459147
theorem B3944477 : Blo 864565 3944477 := bstep (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) B1479179
theorem B3747883 : Blo 864565 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B1945871 : Blo 864565 1945871 := bstep (se 1 (by rfl) ⟨1459403, by rfl⟩ : syracuseStep 1945871 = 2918807) B2918807
theorem B1945889 : Blo 864565 1945889 := bstep (se 2 (by rfl) ⟨729708, by rfl⟩ : syracuseStep 1945889 = 1459417) B1459417
theorem B864571 : Blo 864565 864571 := bstep (se 1 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 864571 = 1296857) B1296857
theorem B7516475 : Blo 864565 7516475 := bstep (se 1 (by rfl) ⟨5637356, by rfl⟩ : syracuseStep 7516475 = 11274713) B11274713
theorem B864647 : Blo 864565 864647 := bstep (se 1 (by rfl) ⟨648485, by rfl⟩ : syracuseStep 864647 = 1296971) B1296971
theorem B864655 : Blo 864565 864655 := bstep (se 1 (by rfl) ⟨648491, by rfl⟩ : syracuseStep 864655 = 1296983) B1296983
theorem B2470297 : Blo 864565 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B864699 : Blo 864565 864699 := bstep (se 1 (by rfl) ⟨648524, by rfl⟩ : syracuseStep 864699 = 1297049) B1297049
theorem B864775 : Blo 864565 864775 := bstep (se 1 (by rfl) ⟨648581, by rfl⟩ : syracuseStep 864775 = 1297163) B1297163
theorem B864783 : Blo 864565 864783 := bstep (se 1 (by rfl) ⟨648587, by rfl⟩ : syracuseStep 864783 = 1297175) B1297175
theorem B3289643 : Blo 864565 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B864827 : Blo 864565 864827 := bstep (se 1 (by rfl) ⟨648620, by rfl⟩ : syracuseStep 864827 = 1297241) B1297241
theorem B2470459 : Blo 864565 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B1946231 : Blo 864565 1946231 := bstep (se 1 (by rfl) ⟨1459673, by rfl⟩ : syracuseStep 1946231 = 2919347) B2919347
theorem B864903 : Blo 864565 864903 := bstep (se 1 (by rfl) ⟨648677, by rfl⟩ : syracuseStep 864903 = 1297355) B1297355
theorem B864911 : Blo 864565 864911 := bstep (se 1 (by rfl) ⟨648683, by rfl⟩ : syracuseStep 864911 = 1297367) B1297367
theorem B1389241 : Blo 864565 1389241 := bstep (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) B1041931
theorem B864955 : Blo 864565 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B4928201 : Blo 864565 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B865031 : Blo 864565 865031 := bstep (se 1 (by rfl) ⟨648773, by rfl⟩ : syracuseStep 865031 = 1297547) B1297547
theorem B865039 : Blo 864565 865039 := bstep (se 1 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 865039 = 1297559) B1297559
theorem B1946411 : Blo 864565 1946411 := bstep (se 1 (by rfl) ⟨1459808, by rfl⟩ : syracuseStep 1946411 = 2919617) B2919617
theorem B865083 : Blo 864565 865083 := bstep (se 1 (by rfl) ⟨648812, by rfl⟩ : syracuseStep 865083 = 1297625) B1297625
theorem B2503543 : Blo 864565 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B865159 : Blo 864565 865159 := bstep (se 1 (by rfl) ⟨648869, by rfl⟩ : syracuseStep 865159 = 1297739) B1297739
theorem B865167 : Blo 864565 865167 := bstep (se 1 (by rfl) ⟨648875, by rfl⟩ : syracuseStep 865167 = 1297751) B1297751
theorem B865211 : Blo 864565 865211 := bstep (se 1 (by rfl) ⟨648908, by rfl⟩ : syracuseStep 865211 = 1297817) B1297817
theorem B865287 : Blo 864565 865287 := bstep (se 1 (by rfl) ⟨648965, by rfl⟩ : syracuseStep 865287 = 1297931) B1297931
theorem B9876491 : Blo 864565 9876491 := bstep (se 1 (by rfl) ⟨7407368, by rfl⟩ : syracuseStep 9876491 = 14814737) B14814737
theorem B865295 : Blo 864565 865295 := bstep (se 1 (by rfl) ⟨648971, by rfl⟩ : syracuseStep 865295 = 1297943) B1297943
theorem B865339 : Blo 864565 865339 := bstep (se 1 (by rfl) ⟨649004, by rfl⟩ : syracuseStep 865339 = 1298009) B1298009
theorem B4011095 : Blo 864565 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B1094791 : Blo 864565 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B865415 : Blo 864565 865415 := bstep (se 1 (by rfl) ⟨649061, by rfl⟩ : syracuseStep 865415 = 1298123) B1298123
theorem B865423 : Blo 864565 865423 := bstep (se 1 (by rfl) ⟨649067, by rfl⟩ : syracuseStep 865423 = 1298135) B1298135
theorem B1946771 : Blo 864565 1946771 := bstep (se 1 (by rfl) ⟨1460078, by rfl⟩ : syracuseStep 1946771 = 2920157) B2920157
theorem B865467 : Blo 864565 865467 := bstep (se 1 (by rfl) ⟨649100, by rfl⟩ : syracuseStep 865467 = 1298201) B1298201
theorem B1946825 : Blo 864565 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B865543 : Blo 864565 865543 := bstep (se 1 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 865543 = 1298315) B1298315
theorem B865551 : Blo 864565 865551 := bstep (se 1 (by rfl) ⟨649163, by rfl⟩ : syracuseStep 865551 = 1298327) B1298327
theorem B865595 : Blo 864565 865595 := bstep (se 1 (by rfl) ⟨649196, by rfl⟩ : syracuseStep 865595 = 1298393) B1298393
theorem B865671 : Blo 864565 865671 := bstep (se 1 (by rfl) ⟨649253, by rfl⟩ : syracuseStep 865671 = 1298507) B1298507
theorem B865679 : Blo 864565 865679 := bstep (se 1 (by rfl) ⟨649259, by rfl⟩ : syracuseStep 865679 = 1298519) B1298519
theorem B72955313 : Blo 864565 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B865723 : Blo 864565 865723 := bstep (se 1 (by rfl) ⟨649292, by rfl⟩ : syracuseStep 865723 = 1298585) B1298585
theorem B865799 : Blo 864565 865799 := bstep (se 1 (by rfl) ⟨649349, by rfl⟩ : syracuseStep 865799 = 1298699) B1298699
theorem B865807 : Blo 864565 865807 := bstep (se 1 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 865807 = 1298711) B1298711
theorem B1095211 : Blo 864565 1095211 := bstep (se 1 (by rfl) ⟨821408, by rfl⟩ : syracuseStep 1095211 = 1642817) B1642817
theorem B10008107 : Blo 864565 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B865851 : Blo 864565 865851 := bstep (se 1 (by rfl) ⟨649388, by rfl⟩ : syracuseStep 865851 = 1298777) B1298777
theorem B6010487 : Blo 864565 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B865927 : Blo 864565 865927 := bstep (se 1 (by rfl) ⟨649445, by rfl⟩ : syracuseStep 865927 = 1298891) B1298891
theorem B865935 : Blo 864565 865935 := bstep (se 1 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 865935 = 1298903) B1298903
theorem B865979 : Blo 864565 865979 := bstep (se 1 (by rfl) ⟨649484, by rfl⟩ : syracuseStep 865979 = 1298969) B1298969
theorem B866055 : Blo 864565 866055 := bstep (se 1 (by rfl) ⟨649541, by rfl⟩ : syracuseStep 866055 = 1299083) B1299083
theorem B1095439 : Blo 864565 1095439 := bstep (se 1 (by rfl) ⟨821579, by rfl⟩ : syracuseStep 1095439 = 1643159) B1643159
theorem B866063 : Blo 864565 866063 := bstep (se 1 (by rfl) ⟨649547, by rfl⟩ : syracuseStep 866063 = 1299095) B1299095
theorem B866107 : Blo 864565 866107 := bstep (se 1 (by rfl) ⟨649580, by rfl⟩ : syracuseStep 866107 = 1299161) B1299161
theorem B1947527 : Blo 864565 1947527 := bstep (se 1 (by rfl) ⟨1460645, by rfl⟩ : syracuseStep 1947527 = 2921291) B2921291
theorem B866183 : Blo 864565 866183 := bstep (se 1 (by rfl) ⟨649637, by rfl⟩ : syracuseStep 866183 = 1299275) B1299275
theorem B866191 : Blo 864565 866191 := bstep (se 1 (by rfl) ⟨649643, by rfl⟩ : syracuseStep 866191 = 1299287) B1299287
theorem B2930579 : Blo 864565 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B866235 : Blo 864565 866235 := bstep (se 1 (by rfl) ⟨649676, by rfl⟩ : syracuseStep 866235 = 1299353) B1299353
theorem B866311 : Blo 864565 866311 := bstep (se 1 (by rfl) ⟨649733, by rfl⟩ : syracuseStep 866311 = 1299467) B1299467
theorem B866319 : Blo 864565 866319 := bstep (se 1 (by rfl) ⟨649739, by rfl⟩ : syracuseStep 866319 = 1299479) B1299479
theorem B1947707 : Blo 864565 1947707 := bstep (se 1 (by rfl) ⟨1460780, by rfl⟩ : syracuseStep 1947707 = 2921561) B2921561
theorem B866363 : Blo 864565 866363 := bstep (se 1 (by rfl) ⟨649772, by rfl⟩ : syracuseStep 866363 = 1299545) B1299545
theorem B866439 : Blo 864565 866439 := bstep (se 1 (by rfl) ⟨649829, by rfl⟩ : syracuseStep 866439 = 1299659) B1299659
theorem B1390727 : Blo 864565 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B866447 : Blo 864565 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B1947833 : Blo 864565 1947833 := bstep (se 2 (by rfl) ⟨730437, by rfl⟩ : syracuseStep 1947833 = 1460875) B1460875
theorem B866491 : Blo 864565 866491 := bstep (se 1 (by rfl) ⟨649868, by rfl⟩ : syracuseStep 866491 = 1299737) B1299737
theorem B866567 : Blo 864565 866567 := bstep (se 1 (by rfl) ⟨649925, by rfl⟩ : syracuseStep 866567 = 1299851) B1299851
theorem B866575 : Blo 864565 866575 := bstep (se 1 (by rfl) ⟨649931, by rfl⟩ : syracuseStep 866575 = 1299863) B1299863
theorem B2472221 : Blo 864565 2472221 := bstep (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) B927083
theorem B866619 : Blo 864565 866619 := bstep (se 1 (by rfl) ⟨649964, by rfl⟩ : syracuseStep 866619 = 1299929) B1299929
theorem B1390907 : Blo 864565 1390907 := bstep (se 1 (by rfl) ⟨1043180, by rfl⟩ : syracuseStep 1390907 = 2086361) B2086361
theorem B866695 : Blo 864565 866695 := bstep (se 1 (by rfl) ⟨650021, by rfl⟩ : syracuseStep 866695 = 1300043) B1300043
theorem B866703 : Blo 864565 866703 := bstep (se 1 (by rfl) ⟨650027, by rfl⟩ : syracuseStep 866703 = 1300055) B1300055
theorem B866747 : Blo 864565 866747 := bstep (se 1 (by rfl) ⟨650060, by rfl⟩ : syracuseStep 866747 = 1300121) B1300121
theorem B1096183 : Blo 864565 1096183 := bstep (se 1 (by rfl) ⟨822137, by rfl⟩ : syracuseStep 1096183 = 1644275) B1644275
theorem B866823 : Blo 864565 866823 := bstep (se 1 (by rfl) ⟨650117, by rfl⟩ : syracuseStep 866823 = 1300235) B1300235
theorem B1948175 : Blo 864565 1948175 := bstep (se 1 (by rfl) ⟨1461131, by rfl⟩ : syracuseStep 1948175 = 2922263) B2922263
theorem B866831 : Blo 864565 866831 := bstep (se 1 (by rfl) ⟨650123, by rfl⟩ : syracuseStep 866831 = 1300247) B1300247
theorem B2636317 : Blo 864565 2636317 := bstep (se 3 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 2636317 = 988619) B988619
theorem B1948193 : Blo 864565 1948193 := bstep (se 2 (by rfl) ⟨730572, by rfl⟩ : syracuseStep 1948193 = 1461145) B1461145
theorem B4930091 : Blo 864565 4930091 := bstep (se 1 (by rfl) ⟨3697568, by rfl⟩ : syracuseStep 4930091 = 7395137) B7395137
theorem B866875 : Blo 864565 866875 := bstep (se 1 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 866875 = 1300313) B1300313
theorem B866951 : Blo 864565 866951 := bstep (se 1 (by rfl) ⟨650213, by rfl⟩ : syracuseStep 866951 = 1300427) B1300427
theorem B866959 : Blo 864565 866959 := bstep (se 1 (by rfl) ⟨650219, by rfl⟩ : syracuseStep 866959 = 1300439) B1300439
theorem B2636441 : Blo 864565 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B867003 : Blo 864565 867003 := bstep (se 1 (by rfl) ⟨650252, by rfl⟩ : syracuseStep 867003 = 1300505) B1300505
theorem B867079 : Blo 864565 867079 := bstep (se 1 (by rfl) ⟨650309, by rfl⟩ : syracuseStep 867079 = 1300619) B1300619
theorem B867087 : Blo 864565 867087 := bstep (se 1 (by rfl) ⟨650315, by rfl⟩ : syracuseStep 867087 = 1300631) B1300631
theorem B8338211 : Blo 864565 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B1096507 : Blo 864565 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B867131 : Blo 864565 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B1948535 : Blo 864565 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B3947399 : Blo 864565 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B867207 : Blo 864565 867207 := bstep (se 1 (by rfl) ⟨650405, by rfl⟩ : syracuseStep 867207 = 1300811) B1300811
theorem B867215 : Blo 864565 867215 := bstep (se 1 (by rfl) ⟨650411, by rfl⟩ : syracuseStep 867215 = 1300823) B1300823
theorem B867259 : Blo 864565 867259 := bstep (se 1 (by rfl) ⟨650444, by rfl⟩ : syracuseStep 867259 = 1300889) B1300889
theorem B2472905 : Blo 864565 2472905 := bstep (se 2 (by rfl) ⟨927339, by rfl⟩ : syracuseStep 2472905 = 1854679) B1854679
theorem B867335 : Blo 864565 867335 := bstep (se 1 (by rfl) ⟨650501, by rfl⟩ : syracuseStep 867335 = 1301003) B1301003
theorem B867343 : Blo 864565 867343 := bstep (se 1 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 867343 = 1301015) B1301015
theorem B1948715 : Blo 864565 1948715 := bstep (se 1 (by rfl) ⟨1461536, by rfl⟩ : syracuseStep 1948715 = 2923073) B2923073
theorem B867387 : Blo 864565 867387 := bstep (se 1 (by rfl) ⟨650540, by rfl⟩ : syracuseStep 867387 = 1301081) B1301081
theorem B867463 : Blo 864565 867463 := bstep (se 1 (by rfl) ⟨650597, by rfl⟩ : syracuseStep 867463 = 1301195) B1301195
theorem B867471 : Blo 864565 867471 := bstep (se 1 (by rfl) ⟨650603, by rfl⟩ : syracuseStep 867471 = 1301207) B1301207
theorem B867515 : Blo 864565 867515 := bstep (se 1 (by rfl) ⟨650636, by rfl⟩ : syracuseStep 867515 = 1301273) B1301273
theorem B867591 : Blo 864565 867591 := bstep (se 1 (by rfl) ⟨650693, by rfl⟩ : syracuseStep 867591 = 1301387) B1301387
theorem B867599 : Blo 864565 867599 := bstep (se 1 (by rfl) ⟨650699, by rfl⟩ : syracuseStep 867599 = 1301399) B1301399
theorem B60833045 : Blo 864565 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1097003 : Blo 864565 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B867643 : Blo 864565 867643 := bstep (se 1 (by rfl) ⟨650732, by rfl⟩ : syracuseStep 867643 = 1301465) B1301465
theorem B867719 : Blo 864565 867719 := bstep (se 1 (by rfl) ⟨650789, by rfl⟩ : syracuseStep 867719 = 1301579) B1301579
theorem B867727 : Blo 864565 867727 := bstep (se 1 (by rfl) ⟨650795, by rfl⟩ : syracuseStep 867727 = 1301591) B1301591
theorem B1949075 : Blo 864565 1949075 := bstep (se 1 (by rfl) ⟨1461806, by rfl⟩ : syracuseStep 1949075 = 2923613) B2923613
theorem B867771 : Blo 864565 867771 := bstep (se 1 (by rfl) ⟨650828, by rfl⟩ : syracuseStep 867771 = 1301657) B1301657
theorem B1949129 : Blo 864565 1949129 := bstep (se 2 (by rfl) ⟨730923, by rfl⟩ : syracuseStep 1949129 = 1461847) B1461847
theorem B867847 : Blo 864565 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B867855 : Blo 864565 867855 := bstep (se 1 (by rfl) ⟨650891, by rfl⟩ : syracuseStep 867855 = 1301783) B1301783
theorem B867899 : Blo 864565 867899 := bstep (se 1 (by rfl) ⟨650924, by rfl⟩ : syracuseStep 867899 = 1301849) B1301849
theorem B53395037 : Blo 864565 53395037 := bstep (se 3 (by rfl) ⟨10011569, by rfl⟩ : syracuseStep 53395037 = 20023139) B20023139
theorem B867975 : Blo 864565 867975 := bstep (se 1 (by rfl) ⟨650981, by rfl⟩ : syracuseStep 867975 = 1301963) B1301963
theorem B867983 : Blo 864565 867983 := bstep (se 1 (by rfl) ⟨650987, by rfl⟩ : syracuseStep 867983 = 1301975) B1301975
theorem B868027 : Blo 864565 868027 := bstep (se 1 (by rfl) ⟨651020, by rfl⟩ : syracuseStep 868027 = 1302041) B1302041
theorem B1097479 : Blo 864565 1097479 := bstep (se 1 (by rfl) ⟨823109, by rfl⟩ : syracuseStep 1097479 = 1646219) B1646219
theorem B868103 : Blo 864565 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B868111 : Blo 864565 868111 := bstep (se 1 (by rfl) ⟨651083, by rfl⟩ : syracuseStep 868111 = 1302167) B1302167
theorem B868155 : Blo 864565 868155 := bstep (se 1 (by rfl) ⟨651116, by rfl⟩ : syracuseStep 868155 = 1302233) B1302233
theorem B868231 : Blo 864565 868231 := bstep (se 1 (by rfl) ⟨651173, by rfl⟩ : syracuseStep 868231 = 1302347) B1302347
theorem B868239 : Blo 864565 868239 := bstep (se 1 (by rfl) ⟨651179, by rfl⟩ : syracuseStep 868239 = 1302359) B1302359
theorem B3293075 : Blo 864565 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B868283 : Blo 864565 868283 := bstep (se 1 (by rfl) ⟨651212, by rfl⟩ : syracuseStep 868283 = 1302425) B1302425
theorem B4931549 : Blo 864565 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B868359 : Blo 864565 868359 := bstep (se 1 (by rfl) ⟨651269, by rfl⟩ : syracuseStep 868359 = 1302539) B1302539
theorem B868367 : Blo 864565 868367 := bstep (se 1 (by rfl) ⟨651275, by rfl⟩ : syracuseStep 868367 = 1302551) B1302551
theorem B2539579 : Blo 864565 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B868411 : Blo 864565 868411 := bstep (se 1 (by rfl) ⟨651308, by rfl⟩ : syracuseStep 868411 = 1302617) B1302617
theorem B1949831 : Blo 864565 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B868487 : Blo 864565 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B868495 : Blo 864565 868495 := bstep (se 1 (by rfl) ⟨651371, by rfl⟩ : syracuseStep 868495 = 1302743) B1302743
theorem B868539 : Blo 864565 868539 := bstep (se 1 (by rfl) ⟨651404, by rfl⟩ : syracuseStep 868539 = 1302809) B1302809
theorem B1097975 : Blo 864565 1097975 := bstep (se 1 (by rfl) ⟨823481, by rfl⟩ : syracuseStep 1097975 = 1646963) B1646963
theorem B1950011 : Blo 864565 1950011 := bstep (se 1 (by rfl) ⟨1462508, by rfl⟩ : syracuseStep 1950011 = 2925017) B2925017
theorem B1098127 : Blo 864565 1098127 := bstep (se 1 (by rfl) ⟨823595, by rfl⟩ : syracuseStep 1098127 = 1647191) B1647191
theorem B1950137 : Blo 864565 1950137 := bstep (se 2 (by rfl) ⟨731301, by rfl⟩ : syracuseStep 1950137 = 1462603) B1462603
theorem B4932049 : Blo 864565 4932049 := bstep (se 2 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 4932049 = 3699037) B3699037
theorem B1098299 : Blo 864565 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B1950479 : Blo 864565 1950479 := bstep (se 1 (by rfl) ⟨1462859, by rfl⟩ : syracuseStep 1950479 = 2925719) B2925719
theorem B1950497 : Blo 864565 1950497 := bstep (se 2 (by rfl) ⟨731436, by rfl⟩ : syracuseStep 1950497 = 1462873) B1462873
theorem B5260177 : Blo 864565 5260177 := bstep (se 2 (by rfl) ⟨1972566, by rfl⟩ : syracuseStep 5260177 = 3945133) B3945133
theorem B7390115 : Blo 864565 7390115 := bstep (se 1 (by rfl) ⟨5542586, by rfl⟩ : syracuseStep 7390115 = 11085173) B11085173
theorem B2475019 : Blo 864565 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B1754171 : Blo 864565 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B1950839 : Blo 864565 1950839 := bstep (se 1 (by rfl) ⟨1463129, by rfl⟩ : syracuseStep 1950839 = 2926259) B2926259
theorem B1459471 : Blo 864565 1459471 := bstep (se 1 (by rfl) ⟨1094603, by rfl⟩ : syracuseStep 1459471 = 2189207) B2189207
theorem B9880865 : Blo 864565 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B1951019 : Blo 864565 1951019 := bstep (se 1 (by rfl) ⟨1463264, by rfl⟩ : syracuseStep 1951019 = 2926529) B2926529
theorem B1099271 : Blo 864565 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B1689121 : Blo 864565 1689121 := bstep (se 2 (by rfl) ⟨633420, by rfl⟩ : syracuseStep 1689121 = 1266841) B1266841
theorem B7390763 : Blo 864565 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B1951379 : Blo 864565 1951379 := bstep (se 1 (by rfl) ⟨1463534, by rfl⟩ : syracuseStep 1951379 = 2927069) B2927069
theorem B1951433 : Blo 864565 1951433 := bstep (se 2 (by rfl) ⟨731787, by rfl⟩ : syracuseStep 1951433 = 1463575) B1463575
theorem B1460011 : Blo 864565 1460011 := bstep (se 1 (by rfl) ⟨1095008, by rfl⟩ : syracuseStep 1460011 = 2190017) B2190017
theorem B2639675 : Blo 864565 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B1460153 : Blo 864565 1460153 := bstep (se 2 (by rfl) ⟨547557, by rfl⟩ : syracuseStep 1460153 = 1095115) B1095115
theorem B1558543 : Blo 864565 1558543 := bstep (se 1 (by rfl) ⟨1168907, by rfl⟩ : syracuseStep 1558543 = 2337815) B2337815
theorem B5261399 : Blo 864565 5261399 := bstep (se 1 (by rfl) ⟨3946049, by rfl⟩ : syracuseStep 5261399 = 7892099) B7892099
theorem B1952135 : Blo 864565 1952135 := bstep (se 1 (by rfl) ⟨1464101, by rfl⟩ : syracuseStep 1952135 = 2928203) B2928203
theorem B1231247 : Blo 864565 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B21055889 : Blo 864565 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B4934033 : Blo 864565 4934033 := bstep (se 2 (by rfl) ⟨1850262, by rfl⟩ : syracuseStep 4934033 = 3700525) B3700525
theorem B3295673 : Blo 864565 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B1296887 : Blo 864565 1296887 := bstep (se 1 (by rfl) ⟨972665, by rfl⟩ : syracuseStep 1296887 = 1945331) B1945331
theorem B1296911 : Blo 864565 1296911 := bstep (se 1 (by rfl) ⟨972683, by rfl⟩ : syracuseStep 1296911 = 1945367) B1945367
theorem B1296953 : Blo 864565 1296953 := bstep (se 2 (by rfl) ⟨486357, by rfl⟩ : syracuseStep 1296953 = 972715) B972715
theorem B1952315 : Blo 864565 1952315 := bstep (se 1 (by rfl) ⟨1464236, by rfl⟩ : syracuseStep 1952315 = 2928473) B2928473
theorem B3328573 : Blo 864565 3328573 := bstep (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) B1248215
theorem B6572663 : Blo 864565 6572663 := bstep (se 1 (by rfl) ⟨4929497, by rfl⟩ : syracuseStep 6572663 = 9858995) B9858995
theorem B1460855 : Blo 864565 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B1297031 : Blo 864565 1297031 := bstep (se 1 (by rfl) ⟨972773, by rfl⟩ : syracuseStep 1297031 = 1945547) B1945547
theorem B1297067 : Blo 864565 1297067 := bstep (se 1 (by rfl) ⟨972800, by rfl⟩ : syracuseStep 1297067 = 1945601) B1945601
theorem B1952441 : Blo 864565 1952441 := bstep (se 2 (by rfl) ⟨732165, by rfl⟩ : syracuseStep 1952441 = 1464331) B1464331
theorem B1297097 : Blo 864565 1297097 := bstep (se 2 (by rfl) ⟨486411, by rfl⟩ : syracuseStep 1297097 = 972823) B972823
theorem B1297211 : Blo 864565 1297211 := bstep (se 1 (by rfl) ⟨972908, by rfl⟩ : syracuseStep 1297211 = 1945817) B1945817
theorem B1297271 : Blo 864565 1297271 := bstep (se 1 (by rfl) ⟨972953, by rfl⟩ : syracuseStep 1297271 = 1945907) B1945907
theorem B1428359 : Blo 864565 1428359 := bstep (se 1 (by rfl) ⟨1071269, by rfl⟩ : syracuseStep 1428359 = 2142539) B2142539
theorem B1297295 : Blo 864565 1297295 := bstep (se 1 (by rfl) ⟨972971, by rfl⟩ : syracuseStep 1297295 = 1945943) B1945943
theorem B1297337 : Blo 864565 1297337 := bstep (se 2 (by rfl) ⟨486501, by rfl⟩ : syracuseStep 1297337 = 973003) B973003
theorem B1297415 : Blo 864565 1297415 := bstep (se 1 (by rfl) ⟨973061, by rfl⟩ : syracuseStep 1297415 = 1946123) B1946123
theorem B42224651 : Blo 864565 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B1559567 : Blo 864565 1559567 := bstep (se 1 (by rfl) ⟨1169675, by rfl⟩ : syracuseStep 1559567 = 2339351) B2339351
theorem B1952783 : Blo 864565 1952783 := bstep (se 1 (by rfl) ⟨1464587, by rfl⟩ : syracuseStep 1952783 = 2929175) B2929175
theorem B1952801 : Blo 864565 1952801 := bstep (se 2 (by rfl) ⟨732300, by rfl⟩ : syracuseStep 1952801 = 1464601) B1464601
theorem B1297451 : Blo 864565 1297451 := bstep (se 1 (by rfl) ⟨973088, by rfl⟩ : syracuseStep 1297451 = 1946177) B1946177
theorem B1461307 : Blo 864565 1461307 := bstep (se 1 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 1461307 = 2191961) B2191961
theorem B1297481 : Blo 864565 1297481 := bstep (se 2 (by rfl) ⟨486555, by rfl⟩ : syracuseStep 1297481 = 973111) B973111
theorem B1297595 : Blo 864565 1297595 := bstep (se 1 (by rfl) ⟨973196, by rfl⟩ : syracuseStep 1297595 = 1946393) B1946393
theorem B1461449 : Blo 864565 1461449 := bstep (se 2 (by rfl) ⟨548043, by rfl⟩ : syracuseStep 1461449 = 1096087) B1096087
theorem B1297655 : Blo 864565 1297655 := bstep (se 1 (by rfl) ⟨973241, by rfl⟩ : syracuseStep 1297655 = 1946483) B1946483
theorem B1297679 : Blo 864565 1297679 := bstep (se 1 (by rfl) ⟨973259, by rfl⟩ : syracuseStep 1297679 = 1946519) B1946519
theorem B1297721 : Blo 864565 1297721 := bstep (se 2 (by rfl) ⟨486645, by rfl⟩ : syracuseStep 1297721 = 973291) B973291
theorem B1756475 : Blo 864565 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B4345177 : Blo 864565 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B1953143 : Blo 864565 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B9850247 : Blo 864565 9850247 := bstep (se 1 (by rfl) ⟨7387685, by rfl⟩ : syracuseStep 9850247 = 14775371) B14775371
theorem B1297799 : Blo 864565 1297799 := bstep (se 1 (by rfl) ⟨973349, by rfl⟩ : syracuseStep 1297799 = 1946699) B1946699
theorem B3296659 : Blo 864565 3296659 := bstep (se 1 (by rfl) ⟨2472494, by rfl⟩ : syracuseStep 3296659 = 4944989) B4944989
theorem B1297835 : Blo 864565 1297835 := bstep (se 1 (by rfl) ⟨973376, by rfl⟩ : syracuseStep 1297835 = 1946753) B1946753
theorem B1297865 : Blo 864565 1297865 := bstep (se 2 (by rfl) ⟨486699, by rfl⟩ : syracuseStep 1297865 = 973399) B973399
theorem B1232329 : Blo 864565 1232329 := bstep (se 2 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 1232329 = 924247) B924247
theorem B1953323 : Blo 864565 1953323 := bstep (se 1 (by rfl) ⟨1464992, by rfl⟩ : syracuseStep 1953323 = 2929985) B2929985
theorem B1297979 : Blo 864565 1297979 := bstep (se 1 (by rfl) ⟨973484, by rfl⟩ : syracuseStep 1297979 = 1946969) B1946969
theorem B1232443 : Blo 864565 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B6573635 : Blo 864565 6573635 := bstep (se 1 (by rfl) ⟨4930226, by rfl⟩ : syracuseStep 6573635 = 9860453) B9860453
theorem B1298039 : Blo 864565 1298039 := bstep (se 1 (by rfl) ⟨973529, by rfl⟩ : syracuseStep 1298039 = 1947059) B1947059
theorem B1298063 : Blo 864565 1298063 := bstep (se 1 (by rfl) ⟨973547, by rfl⟩ : syracuseStep 1298063 = 1947095) B1947095
theorem B1298105 : Blo 864565 1298105 := bstep (se 2 (by rfl) ⟨486789, by rfl⟩ : syracuseStep 1298105 = 973579) B973579
theorem B1298183 : Blo 864565 1298183 := bstep (se 1 (by rfl) ⟨973637, by rfl⟩ : syracuseStep 1298183 = 1947275) B1947275
theorem B1298219 : Blo 864565 1298219 := bstep (se 1 (by rfl) ⟨973664, by rfl⟩ : syracuseStep 1298219 = 1947329) B1947329
theorem B1298249 : Blo 864565 1298249 := bstep (se 2 (by rfl) ⟨486843, by rfl⟩ : syracuseStep 1298249 = 973687) B973687
theorem B1462151 : Blo 864565 1462151 := bstep (se 1 (by rfl) ⟨1096613, by rfl⟩ : syracuseStep 1462151 = 2193227) B2193227
theorem B1953683 : Blo 864565 1953683 := bstep (se 1 (by rfl) ⟨1465262, by rfl⟩ : syracuseStep 1953683 = 2930525) B2930525
theorem B1298363 : Blo 864565 1298363 := bstep (se 1 (by rfl) ⟨973772, by rfl⟩ : syracuseStep 1298363 = 1947545) B1947545
theorem B1953737 : Blo 864565 1953737 := bstep (se 2 (by rfl) ⟨732651, by rfl⟩ : syracuseStep 1953737 = 1465303) B1465303
theorem B1298423 : Blo 864565 1298423 := bstep (se 1 (by rfl) ⟨973817, by rfl⟩ : syracuseStep 1298423 = 1947635) B1947635
theorem B3952651 : Blo 864565 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B1298447 : Blo 864565 1298447 := bstep (se 1 (by rfl) ⟨973835, by rfl⟩ : syracuseStep 1298447 = 1947671) B1947671
theorem B1298489 : Blo 864565 1298489 := bstep (se 2 (by rfl) ⟨486933, by rfl⟩ : syracuseStep 1298489 = 973867) B973867
theorem B9883781 : Blo 864565 9883781 := bstep (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) B1853209
theorem B1298567 : Blo 864565 1298567 := bstep (se 1 (by rfl) ⟨973925, by rfl⟩ : syracuseStep 1298567 = 1947851) B1947851
theorem B1298603 : Blo 864565 1298603 := bstep (se 1 (by rfl) ⟨973952, by rfl⟩ : syracuseStep 1298603 = 1947905) B1947905
theorem B1298633 : Blo 864565 1298633 := bstep (se 2 (by rfl) ⟨486987, by rfl⟩ : syracuseStep 1298633 = 973975) B973975
theorem B1298747 : Blo 864565 1298747 := bstep (se 1 (by rfl) ⟨974060, by rfl⟩ : syracuseStep 1298747 = 1948121) B1948121
theorem B1298807 : Blo 864565 1298807 := bstep (se 1 (by rfl) ⟨974105, by rfl⟩ : syracuseStep 1298807 = 1948211) B1948211
theorem B1298831 : Blo 864565 1298831 := bstep (se 1 (by rfl) ⟨974123, by rfl⟩ : syracuseStep 1298831 = 1948247) B1948247
theorem B1298873 : Blo 864565 1298873 := bstep (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) B974155
theorem B1298951 : Blo 864565 1298951 := bstep (se 1 (by rfl) ⟨974213, by rfl⟩ : syracuseStep 1298951 = 1948427) B1948427
theorem B1561103 : Blo 864565 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B1462799 : Blo 864565 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B1298987 : Blo 864565 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B2085419 : Blo 864565 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B1299017 : Blo 864565 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B3330679 : Blo 864565 3330679 := bstep (se 1 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 3330679 = 4996019) B4996019
theorem B1299131 : Blo 864565 1299131 := bstep (se 1 (by rfl) ⟨974348, by rfl⟩ : syracuseStep 1299131 = 1948697) B1948697
theorem B1299191 : Blo 864565 1299191 := bstep (se 1 (by rfl) ⟨974393, by rfl⟩ : syracuseStep 1299191 = 1948787) B1948787
theorem B1299215 : Blo 864565 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B1299257 : Blo 864565 1299257 := bstep (se 2 (by rfl) ⟨487221, by rfl⟩ : syracuseStep 1299257 = 974443) B974443
theorem B4379507 : Blo 864565 4379507 := bstep (se 1 (by rfl) ⟨3284630, by rfl⟩ : syracuseStep 4379507 = 6569261) B6569261
theorem B5264243 : Blo 864565 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B1299335 : Blo 864565 1299335 := bstep (se 1 (by rfl) ⟨974501, by rfl⟩ : syracuseStep 1299335 = 1949003) B1949003
theorem B1299371 : Blo 864565 1299371 := bstep (se 1 (by rfl) ⟨974528, by rfl⟩ : syracuseStep 1299371 = 1949057) B1949057
theorem B2675641 : Blo 864565 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B1299401 : Blo 864565 1299401 := bstep (se 2 (by rfl) ⟨487275, by rfl⟩ : syracuseStep 1299401 = 974551) B974551
theorem B1463339 : Blo 864565 1463339 := bstep (se 1 (by rfl) ⟨1097504, by rfl⟩ : syracuseStep 1463339 = 2195009) B2195009
theorem B1299515 : Blo 864565 1299515 := bstep (se 1 (by rfl) ⟨974636, by rfl⟩ : syracuseStep 1299515 = 1949273) B1949273
theorem B1299575 : Blo 864565 1299575 := bstep (se 1 (by rfl) ⟨974681, by rfl⟩ : syracuseStep 1299575 = 1949363) B1949363
theorem B1234055 : Blo 864565 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B1299599 : Blo 864565 1299599 := bstep (se 1 (by rfl) ⟨974699, by rfl⟩ : syracuseStep 1299599 = 1949399) B1949399
theorem B1299641 : Blo 864565 1299641 := bstep (se 2 (by rfl) ⟨487365, by rfl⟩ : syracuseStep 1299641 = 974731) B974731
theorem B1561801 : Blo 864565 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B1299719 : Blo 864565 1299719 := bstep (se 1 (by rfl) ⟨974789, by rfl⟩ : syracuseStep 1299719 = 1949579) B1949579
theorem B1299755 : Blo 864565 1299755 := bstep (se 1 (by rfl) ⟨974816, by rfl⟩ : syracuseStep 1299755 = 1949633) B1949633
theorem B1299785 : Blo 864565 1299785 := bstep (se 2 (by rfl) ⟨487419, by rfl⟩ : syracuseStep 1299785 = 974839) B974839
theorem B4379993 : Blo 864565 4379993 := bstep (se 2 (by rfl) ⟨1642497, by rfl⟩ : syracuseStep 4379993 = 3284995) B3284995
theorem B2774407 : Blo 864565 2774407 := bstep (se 1 (by rfl) ⟨2080805, by rfl⟩ : syracuseStep 2774407 = 4161611) B4161611
theorem B41178545 : Blo 864565 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B1463737 : Blo 864565 1463737 := bstep (se 2 (by rfl) ⟨548901, by rfl⟩ : syracuseStep 1463737 = 1097803) B1097803
theorem B1299899 : Blo 864565 1299899 := bstep (se 1 (by rfl) ⟨974924, by rfl⟩ : syracuseStep 1299899 = 1949849) B1949849
theorem B1758665 : Blo 864565 1758665 := bstep (se 2 (by rfl) ⟨659499, by rfl⟩ : syracuseStep 1758665 = 1318999) B1318999
theorem B1299959 : Blo 864565 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B1299983 : Blo 864565 1299983 := bstep (se 1 (by rfl) ⟨974987, by rfl⟩ : syracuseStep 1299983 = 1949975) B1949975
theorem B1300025 : Blo 864565 1300025 := bstep (se 2 (by rfl) ⟨487509, by rfl⟩ : syracuseStep 1300025 = 975019) B975019
theorem B1300103 : Blo 864565 1300103 := bstep (se 1 (by rfl) ⟨975077, by rfl⟩ : syracuseStep 1300103 = 1950155) B1950155
theorem B2086553 : Blo 864565 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B1300139 : Blo 864565 1300139 := bstep (se 1 (by rfl) ⟨975104, by rfl⟩ : syracuseStep 1300139 = 1950209) B1950209
theorem B1300169 : Blo 864565 1300169 := bstep (se 2 (by rfl) ⟨487563, by rfl⟩ : syracuseStep 1300169 = 975127) B975127
theorem B2774843 : Blo 864565 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B1300283 : Blo 864565 1300283 := bstep (se 1 (by rfl) ⟨975212, by rfl⟩ : syracuseStep 1300283 = 1950425) B1950425
theorem B8312651 : Blo 864565 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B11097931 : Blo 864565 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B1300343 : Blo 864565 1300343 := bstep (se 1 (by rfl) ⟨975257, by rfl⟩ : syracuseStep 1300343 = 1950515) B1950515
theorem B2086775 : Blo 864565 2086775 := bstep (se 1 (by rfl) ⟨1565081, by rfl⟩ : syracuseStep 2086775 = 3130163) B3130163
theorem B972679 : Blo 864565 972679 := bstep (se 1 (by rfl) ⟨729509, by rfl⟩ : syracuseStep 972679 = 1459019) B1459019
theorem B3331975 : Blo 864565 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B1300367 : Blo 864565 1300367 := bstep (se 1 (by rfl) ⟨975275, by rfl⟩ : syracuseStep 1300367 = 1950551) B1950551
theorem B1300409 : Blo 864565 1300409 := bstep (se 2 (by rfl) ⟨487653, by rfl⟩ : syracuseStep 1300409 = 975307) B975307
theorem B4446161 : Blo 864565 4446161 := bstep (se 2 (by rfl) ⟨1667310, by rfl⟩ : syracuseStep 4446161 = 3334621) B3334621
theorem B1300487 : Blo 864565 1300487 := bstep (se 1 (by rfl) ⟨975365, by rfl⟩ : syracuseStep 1300487 = 1950731) B1950731
theorem B1300523 : Blo 864565 1300523 := bstep (se 1 (by rfl) ⟨975392, by rfl⟩ : syracuseStep 1300523 = 1950785) B1950785
theorem B972859 : Blo 864565 972859 := bstep (se 1 (by rfl) ⟨729644, by rfl⟩ : syracuseStep 972859 = 1459289) B1459289
theorem B1300553 : Blo 864565 1300553 := bstep (se 2 (by rfl) ⟨487707, by rfl⟩ : syracuseStep 1300553 = 975415) B975415
theorem B1235017 : Blo 864565 1235017 := bstep (se 2 (by rfl) ⟨463131, by rfl⟩ : syracuseStep 1235017 = 926263) B926263
theorem B1464439 : Blo 864565 1464439 := bstep (se 1 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 1464439 = 2196659) B2196659
theorem B1300667 : Blo 864565 1300667 := bstep (se 1 (by rfl) ⟨975500, by rfl⟩ : syracuseStep 1300667 = 1951001) B1951001
theorem B1300727 : Blo 864565 1300727 := bstep (se 1 (by rfl) ⟨975545, by rfl⟩ : syracuseStep 1300727 = 1951091) B1951091
theorem B1300751 : Blo 864565 1300751 := bstep (se 1 (by rfl) ⟨975563, by rfl⟩ : syracuseStep 1300751 = 1951127) B1951127
theorem B1300793 : Blo 864565 1300793 := bstep (se 2 (by rfl) ⟨487797, by rfl⟩ : syracuseStep 1300793 = 975595) B975595
theorem B1464635 : Blo 864565 1464635 := bstep (se 1 (by rfl) ⟨1098476, by rfl⟩ : syracuseStep 1464635 = 2196953) B2196953
theorem B1300871 : Blo 864565 1300871 := bstep (se 1 (by rfl) ⟨975653, by rfl⟩ : syracuseStep 1300871 = 1951307) B1951307
theorem B1300907 : Blo 864565 1300907 := bstep (se 1 (by rfl) ⟨975680, by rfl⟩ : syracuseStep 1300907 = 1951361) B1951361
theorem B1300937 : Blo 864565 1300937 := bstep (se 2 (by rfl) ⟨487851, by rfl⟩ : syracuseStep 1300937 = 975703) B975703
theorem B973327 : Blo 864565 973327 := bstep (se 1 (by rfl) ⟨729995, by rfl⟩ : syracuseStep 973327 = 1459991) B1459991
theorem B1235513 : Blo 864565 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B1301051 : Blo 864565 1301051 := bstep (se 1 (by rfl) ⟨975788, by rfl⟩ : syracuseStep 1301051 = 1951577) B1951577
theorem B1301111 : Blo 864565 1301111 := bstep (se 1 (by rfl) ⟨975833, by rfl⟩ : syracuseStep 1301111 = 1951667) B1951667
theorem B1301135 : Blo 864565 1301135 := bstep (se 1 (by rfl) ⟨975851, by rfl⟩ : syracuseStep 1301135 = 1951703) B1951703
theorem B1301177 : Blo 864565 1301177 := bstep (se 2 (by rfl) ⟨487941, by rfl⟩ : syracuseStep 1301177 = 975883) B975883
theorem B1465033 : Blo 864565 1465033 := bstep (se 2 (by rfl) ⟨549387, by rfl⟩ : syracuseStep 1465033 = 1098775) B1098775
theorem B1301255 : Blo 864565 1301255 := bstep (se 1 (by rfl) ⟨975941, by rfl⟩ : syracuseStep 1301255 = 1951883) B1951883
theorem B1301291 : Blo 864565 1301291 := bstep (se 1 (by rfl) ⟨975968, by rfl⟩ : syracuseStep 1301291 = 1951937) B1951937
theorem B1301321 : Blo 864565 1301321 := bstep (se 2 (by rfl) ⟨487995, by rfl⟩ : syracuseStep 1301321 = 975991) B975991
theorem B3562393 : Blo 864565 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B1301435 : Blo 864565 1301435 := bstep (se 1 (by rfl) ⟨976076, by rfl⟩ : syracuseStep 1301435 = 1952153) B1952153
theorem B1301495 : Blo 864565 1301495 := bstep (se 1 (by rfl) ⟨976121, by rfl⟩ : syracuseStep 1301495 = 1952243) B1952243
theorem B973831 : Blo 864565 973831 := bstep (se 1 (by rfl) ⟨730373, by rfl⟩ : syracuseStep 973831 = 1460747) B1460747
theorem B1301519 : Blo 864565 1301519 := bstep (se 1 (by rfl) ⟨976139, by rfl⟩ : syracuseStep 1301519 = 1952279) B1952279
theorem B1301561 : Blo 864565 1301561 := bstep (se 2 (by rfl) ⟨488085, by rfl⟩ : syracuseStep 1301561 = 976171) B976171
theorem B4938839 : Blo 864565 4938839 := bstep (se 1 (by rfl) ⟨3704129, by rfl⟩ : syracuseStep 4938839 = 7408259) B7408259
theorem B1301639 : Blo 864565 1301639 := bstep (se 1 (by rfl) ⟨976229, by rfl⟩ : syracuseStep 1301639 = 1952459) B1952459
theorem B1301675 : Blo 864565 1301675 := bstep (se 1 (by rfl) ⟨976256, by rfl⟩ : syracuseStep 1301675 = 1952513) B1952513
theorem B974011 : Blo 864565 974011 := bstep (se 1 (by rfl) ⟨730508, by rfl⟩ : syracuseStep 974011 = 1461017) B1461017
theorem B1301705 : Blo 864565 1301705 := bstep (se 2 (by rfl) ⟨488139, by rfl⟩ : syracuseStep 1301705 = 976279) B976279
theorem B1301819 : Blo 864565 1301819 := bstep (se 1 (by rfl) ⟨976364, by rfl⟩ : syracuseStep 1301819 = 1952729) B1952729
theorem B4742489 : Blo 864565 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B1301879 : Blo 864565 1301879 := bstep (se 1 (by rfl) ⟨976409, by rfl⟩ : syracuseStep 1301879 = 1952819) B1952819
theorem B1301903 : Blo 864565 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B4382099 : Blo 864565 4382099 := bstep (se 1 (by rfl) ⟨3286574, by rfl⟩ : syracuseStep 4382099 = 6573149) B6573149
theorem B1301945 : Blo 864565 1301945 := bstep (se 2 (by rfl) ⟨488229, by rfl⟩ : syracuseStep 1301945 = 976459) B976459
theorem B1170875 : Blo 864565 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B13360589 : Blo 864565 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B1302023 : Blo 864565 1302023 := bstep (se 1 (by rfl) ⟨976517, by rfl⟩ : syracuseStep 1302023 = 1953035) B1953035
theorem B1236487 : Blo 864565 1236487 := bstep (se 1 (by rfl) ⟨927365, by rfl⟩ : syracuseStep 1236487 = 1854731) B1854731
theorem B1302059 : Blo 864565 1302059 := bstep (se 1 (by rfl) ⟨976544, by rfl⟩ : syracuseStep 1302059 = 1953089) B1953089
theorem B1302089 : Blo 864565 1302089 := bstep (se 2 (by rfl) ⟨488283, by rfl⟩ : syracuseStep 1302089 = 976567) B976567
theorem B974479 : Blo 864565 974479 := bstep (se 1 (by rfl) ⟨730859, by rfl⟩ : syracuseStep 974479 = 1461719) B1461719
theorem B1302203 : Blo 864565 1302203 := bstep (se 1 (by rfl) ⟨976652, by rfl⟩ : syracuseStep 1302203 = 1953305) B1953305
theorem B1302263 : Blo 864565 1302263 := bstep (se 1 (by rfl) ⟨976697, by rfl⟩ : syracuseStep 1302263 = 1953395) B1953395
theorem B1302287 : Blo 864565 1302287 := bstep (se 1 (by rfl) ⟨976715, by rfl⟩ : syracuseStep 1302287 = 1953431) B1953431
theorem B1302329 : Blo 864565 1302329 := bstep (se 2 (by rfl) ⟨488373, by rfl⟩ : syracuseStep 1302329 = 976747) B976747
theorem B6578009 : Blo 864565 6578009 := bstep (se 2 (by rfl) ⟨2466753, by rfl⟩ : syracuseStep 6578009 = 4933507) B4933507
theorem B1302407 : Blo 864565 1302407 := bstep (se 1 (by rfl) ⟨976805, by rfl⟩ : syracuseStep 1302407 = 1953611) B1953611
theorem B5627801 : Blo 864565 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B1302443 : Blo 864565 1302443 := bstep (se 1 (by rfl) ⟨976832, by rfl⟩ : syracuseStep 1302443 = 1953665) B1953665
theorem B1302473 : Blo 864565 1302473 := bstep (se 2 (by rfl) ⟨488427, by rfl⟩ : syracuseStep 1302473 = 976855) B976855
theorem B5005259 : Blo 864565 5005259 := bstep (se 1 (by rfl) ⟨3753944, by rfl⟩ : syracuseStep 5005259 = 7507889) B7507889
theorem B1302587 : Blo 864565 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B1302647 : Blo 864565 1302647 := bstep (se 1 (by rfl) ⟨976985, by rfl⟩ : syracuseStep 1302647 = 1953971) B1953971
theorem B974983 : Blo 864565 974983 := bstep (se 1 (by rfl) ⟨731237, by rfl⟩ : syracuseStep 974983 = 1462475) B1462475
theorem B1302671 : Blo 864565 1302671 := bstep (se 1 (by rfl) ⟨977003, by rfl⟩ : syracuseStep 1302671 = 1954007) B1954007
theorem B1302713 : Blo 864565 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B1302791 : Blo 864565 1302791 := bstep (se 1 (by rfl) ⟨977093, by rfl⟩ : syracuseStep 1302791 = 1954187) B1954187
theorem B1302827 : Blo 864565 1302827 := bstep (se 1 (by rfl) ⟨977120, by rfl⟩ : syracuseStep 1302827 = 1954241) B1954241
theorem B975163 : Blo 864565 975163 := bstep (se 1 (by rfl) ⟨731372, by rfl⟩ : syracuseStep 975163 = 1462745) B1462745
theorem B1564987 : Blo 864565 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B1171913 : Blo 864565 1171913 := bstep (se 2 (by rfl) ⟨439467, by rfl⟩ : syracuseStep 1171913 = 878935) B878935
theorem B2777611 : Blo 864565 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B975631 : Blo 864565 975631 := bstep (se 1 (by rfl) ⟨731723, by rfl⟩ : syracuseStep 975631 = 1463447) B1463447
theorem B6578981 : Blo 864565 6578981 := bstep (se 4 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 6578981 = 1233559) B1233559
theorem B4678829 : Blo 864565 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1664201 : Blo 864565 1664201 := bstep (se 2 (by rfl) ⟨624075, by rfl⟩ : syracuseStep 1664201 = 1248151) B1248151
theorem B976135 : Blo 864565 976135 := bstep (se 1 (by rfl) ⟨732101, by rfl⟩ : syracuseStep 976135 = 1464203) B1464203
theorem B2188559 : Blo 864565 2188559 := bstep (se 1 (by rfl) ⟨1641419, by rfl⟩ : syracuseStep 2188559 = 3282839) B3282839
theorem B4941071 : Blo 864565 4941071 := bstep (se 1 (by rfl) ⟨3705803, by rfl⟩ : syracuseStep 4941071 = 7411607) B7411607
theorem B2188691 : Blo 864565 2188691 := bstep (se 1 (by rfl) ⟨1641518, by rfl⟩ : syracuseStep 2188691 = 3283037) B3283037
theorem B976315 : Blo 864565 976315 := bstep (se 1 (by rfl) ⟨732236, by rfl⟩ : syracuseStep 976315 = 1464473) B1464473
theorem B4941323 : Blo 864565 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B1664555 : Blo 864565 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B4450099 : Blo 864565 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B976783 : Blo 864565 976783 := bstep (se 1 (by rfl) ⟨732587, by rfl⟩ : syracuseStep 976783 = 1465175) B1465175
theorem B7890851 : Blo 864565 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B4155421 : Blo 864565 4155421 := bstep (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) B1558283
theorem B7399511 : Blo 864565 7399511 := bstep (se 1 (by rfl) ⟨5549633, by rfl⟩ : syracuseStep 7399511 = 11099267) B11099267
theorem B9365705 : Blo 864565 9365705 := bstep (se 2 (by rfl) ⟨3512139, by rfl⟩ : syracuseStep 9365705 = 7024279) B7024279
theorem B2779393 : Blo 864565 2779393 := bstep (se 2 (by rfl) ⟨1042272, by rfl⟩ : syracuseStep 2779393 = 2084545) B2084545
theorem B5564807 : Blo 864565 5564807 := bstep (se 1 (by rfl) ⟨4173605, by rfl⟩ : syracuseStep 5564807 = 8347211) B8347211
theorem B4385177 : Blo 864565 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B2189825 : Blo 864565 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B1043003 : Blo 864565 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B4942529 : Blo 864565 4942529 := bstep (se 2 (by rfl) ⟨1853448, by rfl⟩ : syracuseStep 4942529 = 3706897) B3706897
theorem B2190199 : Blo 864565 2190199 := bstep (se 1 (by rfl) ⟨1642649, by rfl⟩ : syracuseStep 2190199 = 3285299) B3285299
theorem B2190635 : Blo 864565 2190635 := bstep (se 1 (by rfl) ⟨1642976, by rfl⟩ : syracuseStep 2190635 = 3285953) B3285953
theorem B20016569 : Blo 864565 20016569 := bstep (se 2 (by rfl) ⟨7506213, by rfl⟩ : syracuseStep 20016569 = 15012427) B15012427
theorem B6254009 : Blo 864565 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B12480101 : Blo 864565 12480101 := bstep (se 4 (by rfl) ⟨1170009, by rfl⟩ : syracuseStep 12480101 = 2340019) B2340019
theorem B2191475 : Blo 864565 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B2191495 : Blo 864565 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B6746503 : Blo 864565 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B2191769 : Blo 864565 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B4452893 : Blo 864565 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B2191931 : Blo 864565 2191931 := bstep (se 1 (by rfl) ⟨1643948, by rfl⟩ : syracuseStep 2191931 = 3287897) B3287897
theorem B9892529 : Blo 864565 9892529 := bstep (se 2 (by rfl) ⟨3709698, by rfl⟩ : syracuseStep 9892529 = 7419397) B7419397
theorem B18772661 : Blo 864565 18772661 := bstep (se 5 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 18772661 = 1759937) B1759937
theorem B2192143 : Blo 864565 2192143 := bstep (se 1 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 2192143 = 3288215) B3288215
theorem B2781967 : Blo 864565 2781967 := bstep (se 1 (by rfl) ⟨2086475, by rfl⟩ : syracuseStep 2781967 = 4172951) B4172951
theorem B4387769 : Blo 864565 4387769 := bstep (se 2 (by rfl) ⟨1645413, by rfl⟩ : syracuseStep 4387769 = 3290827) B3290827
theorem B2192417 : Blo 864565 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B7894721 : Blo 864565 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B7403237 : Blo 864565 7403237 := bstep (se 4 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 7403237 = 1388107) B1388107
theorem B1406735 : Blo 864565 1406735 := bstep (se 1 (by rfl) ⟨1055051, by rfl⟩ : syracuseStep 1406735 = 2110103) B2110103
theorem B4945697 : Blo 864565 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B1505159 : Blo 864565 1505159 := bstep (se 1 (by rfl) ⟨1128869, by rfl⟩ : syracuseStep 1505159 = 2257739) B2257739
theorem B2193419 : Blo 864565 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B4389065 : Blo 864565 4389065 := bstep (se 2 (by rfl) ⟨1645899, by rfl⟩ : syracuseStep 4389065 = 3291799) B3291799
theorem B2194067 : Blo 864565 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B13368025 : Blo 864565 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B4684691 : Blo 864565 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B2194361 : Blo 864565 2194361 := bstep (se 2 (by rfl) ⟨822885, by rfl⟩ : syracuseStep 2194361 = 1645771) B1645771
theorem B3701771 : Blo 864565 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B9993239 : Blo 864565 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B6585785 : Blo 864565 6585785 := bstep (se 2 (by rfl) ⟨2469669, by rfl⟩ : syracuseStep 6585785 = 4939339) B4939339
theorem B5275165 : Blo 864565 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B2195059 : Blo 864565 2195059 := bstep (se 1 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 2195059 = 3292589) B3292589
theorem B2195201 : Blo 864565 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B10518605 : Blo 864565 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B6586757 : Blo 864565 6586757 := bstep (se 4 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 6586757 = 1235017) B1235017
theorem B3703481 : Blo 864565 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B6587243 : Blo 864565 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B7013569 : Blo 864565 7013569 := bstep (se 2 (by rfl) ⟨2630088, by rfl⟩ : syracuseStep 7013569 = 5260177) B5260177
theorem B1443065 : Blo 864565 1443065 := bstep (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) B1082299
theorem B2196841 : Blo 864565 2196841 := bstep (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) B1647631
theorem B3507599 : Blo 864565 3507599 := bstep (se 1 (by rfl) ⟨2630699, by rfl⟩ : syracuseStep 3507599 = 5261399) B5261399
theorem B2197115 : Blo 864565 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B28149767 : Blo 864565 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B3508541 : Blo 864565 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B4393277 : Blo 864565 4393277 := bstep (se 3 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 4393277 = 1647479) B1647479
theorem B5933465 : Blo 864565 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B5540561 : Blo 864565 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B6589187 : Blo 864565 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B1641359 : Blo 864565 1641359 := bstep (se 1 (by rfl) ⟨1231019, by rfl⟩ : syracuseStep 1641359 = 2462039) B2462039
theorem B3705857 : Blo 864565 3705857 := bstep (se 2 (by rfl) ⟨1389696, by rfl⟩ : syracuseStep 3705857 = 2779393) B2779393
theorem B2919671 : Blo 864565 2919671 := bstep (se 1 (by rfl) ⟨2189753, by rfl⟩ : syracuseStep 2919671 = 4379507) B4379507
theorem B3509495 : Blo 864565 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B2919995 : Blo 864565 2919995 := bstep (se 1 (by rfl) ⟨2189996, by rfl⟩ : syracuseStep 2919995 = 4379993) B4379993
theorem B2920265 : Blo 864565 2920265 := bstep (se 2 (by rfl) ⟨1095099, by rfl⟩ : syracuseStep 2920265 = 2190199) B2190199
theorem B5541767 : Blo 864565 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B1642619 : Blo 864565 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B48730385 : Blo 864565 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B4395545 : Blo 864565 4395545 := bstep (se 2 (by rfl) ⟨1648329, by rfl⟩ : syracuseStep 4395545 = 3296659) B3296659
theorem B1643105 : Blo 864565 1643105 := bstep (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) B1232329
theorem B1643257 : Blo 864565 1643257 := bstep (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) B1232443
theorem B2921399 : Blo 864565 2921399 := bstep (se 1 (by rfl) ⟨2191049, by rfl⟩ : syracuseStep 2921399 = 4382099) B4382099
theorem B35493065 : Blo 864565 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B2921993 : Blo 864565 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B3708605 : Blo 864565 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B23729921 : Blo 864565 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B18749393 : Blo 864565 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1644563 : Blo 864565 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B6592589 : Blo 864565 6592589 := bstep (se 3 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 6592589 = 2472221) B2472221
theorem B3119219 : Blo 864565 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1644715 : Blo 864565 1644715 := bstep (se 1 (by rfl) ⟨1233536, by rfl⟩ : syracuseStep 1644715 = 2467073) B2467073
theorem B2922857 : Blo 864565 2922857 := bstep (se 2 (by rfl) ⟨1096071, by rfl⟩ : syracuseStep 2922857 = 2192143) B2192143
theorem B3709289 : Blo 864565 3709289 := bstep (se 2 (by rfl) ⟨1390983, by rfl⟩ : syracuseStep 3709289 = 2781967) B2781967
theorem B3283325 : Blo 864565 3283325 := bstep (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) B1231247
theorem B1644943 : Blo 864565 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B1645019 : Blo 864565 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B1317575 : Blo 864565 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B11279249 : Blo 864565 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B3709871 : Blo 864565 3709871 := bstep (se 1 (by rfl) ⟨2782403, by rfl⟩ : syracuseStep 3709871 = 5564807) B5564807
theorem B2923451 : Blo 864565 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B9379451 : Blo 864565 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B4169339 : Blo 864565 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B3808957 : Blo 864565 3808957 := bstep (se 3 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 3808957 = 1428359) B1428359
theorem B6595019 : Blo 864565 6595019 := bstep (se 1 (by rfl) ⟨4946264, by rfl⟩ : syracuseStep 6595019 = 9892529) B9892529
theorem B3285467 : Blo 864565 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B2925179 : Blo 864565 2925179 := bstep (se 1 (by rfl) ⟨2193884, by rfl⟩ : syracuseStep 2925179 = 4387769) B4387769
theorem B3515089 : Blo 864565 3515089 := bstep (se 2 (by rfl) ⟨1318158, by rfl⟩ : syracuseStep 3515089 = 2636317) B2636317
theorem B2925341 : Blo 864565 2925341 := bstep (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) B1097003
theorem B48636875 : Blo 864565 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B4006991 : Blo 864565 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B3122333 : Blo 864565 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B2926043 : Blo 864565 2926043 := bstep (se 1 (by rfl) ⟨2194532, by rfl⟩ : syracuseStep 2926043 = 4389065) B4389065
theorem B927271 : Blo 864565 927271 := bstep (se 1 (by rfl) ⟨695453, by rfl⟩ : syracuseStep 927271 = 1390907) B1390907
theorem B3286727 : Blo 864565 3286727 := bstep (se 1 (by rfl) ⟨2465045, by rfl⟩ : syracuseStep 3286727 = 4930091) B4930091
theorem B13510489 : Blo 864565 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2631599 : Blo 864565 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B14034869 : Blo 864565 14034869 := bstep (se 5 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 14034869 = 1315769) B1315769
theorem B3123127 : Blo 864565 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B1648603 : Blo 864565 1648603 := bstep (se 1 (by rfl) ⟨1236452, by rfl⟩ : syracuseStep 1648603 = 2472905) B2472905
theorem B2467847 : Blo 864565 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B1648649 : Blo 864565 1648649 := bstep (se 2 (by rfl) ⟨618243, by rfl⟩ : syracuseStep 1648649 = 1236487) B1236487
theorem B6662159 : Blo 864565 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B2926745 : Blo 864565 2926745 := bstep (se 2 (by rfl) ⟨1097529, by rfl⟩ : syracuseStep 2926745 = 2195059) B2195059
theorem B3287425 : Blo 864565 3287425 := bstep (se 2 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 3287425 = 2465569) B2465569
theorem B35596691 : Blo 864565 35596691 := bstep (se 1 (by rfl) ⟨26697518, by rfl⟩ : syracuseStep 35596691 = 53395037) B53395037
theorem B3287699 : Blo 864565 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B14068403 : Blo 864565 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B3386105 : Blo 864565 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B5942443 : Blo 864565 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B4926743 : Blo 864565 4926743 := bstep (se 1 (by rfl) ⟨3695057, by rfl⟩ : syracuseStep 4926743 = 7390115) B7390115
theorem B2927933 : Blo 864565 2927933 := bstep (se 3 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 2927933 = 1097975) B1097975
theorem B4927175 : Blo 864565 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B1945439 : Blo 864565 1945439 := bstep (se 1 (by rfl) ⟨1459079, by rfl⟩ : syracuseStep 1945439 = 2918159) B2918159
theorem B3125101 : Blo 864565 3125101 := bstep (se 3 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 3125101 = 1171913) B1171913
theorem B1945619 : Blo 864565 1945619 := bstep (se 1 (by rfl) ⟨1459214, by rfl⟩ : syracuseStep 1945619 = 2918429) B2918429
theorem B2928797 : Blo 864565 2928797 := bstep (se 3 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 2928797 = 1098299) B1098299
theorem B3289355 : Blo 864565 3289355 := bstep (se 1 (by rfl) ⟨2467016, by rfl⟩ : syracuseStep 3289355 = 4934033) B4934033
theorem B864591 : Blo 864565 864591 := bstep (se 1 (by rfl) ⟨648443, by rfl⟩ : syracuseStep 864591 = 1296887) B1296887
theorem B864607 : Blo 864565 864607 := bstep (se 1 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 864607 = 1296911) B1296911
theorem B1945961 : Blo 864565 1945961 := bstep (se 2 (by rfl) ⟨729735, by rfl⟩ : syracuseStep 1945961 = 1459471) B1459471
theorem B864635 : Blo 864565 864635 := bstep (se 1 (by rfl) ⟨648476, by rfl⟩ : syracuseStep 864635 = 1296953) B1296953
theorem B864687 : Blo 864565 864687 := bstep (se 1 (by rfl) ⟨648515, by rfl⟩ : syracuseStep 864687 = 1297031) B1297031
theorem B864711 : Blo 864565 864711 := bstep (se 1 (by rfl) ⟨648533, by rfl⟩ : syracuseStep 864711 = 1297067) B1297067
theorem B864731 : Blo 864565 864731 := bstep (se 1 (by rfl) ⟨648548, by rfl⟩ : syracuseStep 864731 = 1297097) B1297097
theorem B864807 : Blo 864565 864807 := bstep (se 1 (by rfl) ⟨648605, by rfl⟩ : syracuseStep 864807 = 1297211) B1297211
theorem B864847 : Blo 864565 864847 := bstep (se 1 (by rfl) ⟨648635, by rfl⟩ : syracuseStep 864847 = 1297271) B1297271
theorem B864863 : Blo 864565 864863 := bstep (se 1 (by rfl) ⟨648647, by rfl⟩ : syracuseStep 864863 = 1297295) B1297295
theorem B864891 : Blo 864565 864891 := bstep (se 1 (by rfl) ⟨648668, by rfl⟩ : syracuseStep 864891 = 1297337) B1297337
theorem B3388043 : Blo 864565 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B864943 : Blo 864565 864943 := bstep (se 1 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 864943 = 1297415) B1297415
theorem B2929337 : Blo 864565 2929337 := bstep (se 2 (by rfl) ⟨1098501, by rfl⟩ : syracuseStep 2929337 = 2197003) B2197003
theorem B864967 : Blo 864565 864967 := bstep (se 1 (by rfl) ⟨648725, by rfl⟩ : syracuseStep 864967 = 1297451) B1297451
theorem B864987 : Blo 864565 864987 := bstep (se 1 (by rfl) ⟨648740, by rfl⟩ : syracuseStep 864987 = 1297481) B1297481
theorem B865063 : Blo 864565 865063 := bstep (se 1 (by rfl) ⟨648797, by rfl⟩ : syracuseStep 865063 = 1297595) B1297595
theorem B865103 : Blo 864565 865103 := bstep (se 1 (by rfl) ⟨648827, by rfl⟩ : syracuseStep 865103 = 1297655) B1297655
theorem B865119 : Blo 864565 865119 := bstep (se 1 (by rfl) ⟨648839, by rfl⟩ : syracuseStep 865119 = 1297679) B1297679
theorem B2470763 : Blo 864565 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B865147 : Blo 864565 865147 := bstep (se 1 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 865147 = 1297721) B1297721
theorem B6566831 : Blo 864565 6566831 := bstep (se 1 (by rfl) ⟨4925123, by rfl⟩ : syracuseStep 6566831 = 9850247) B9850247
theorem B865199 : Blo 864565 865199 := bstep (se 1 (by rfl) ⟨648899, by rfl⟩ : syracuseStep 865199 = 1297799) B1297799
theorem B1946555 : Blo 864565 1946555 := bstep (se 1 (by rfl) ⟨1459916, by rfl⟩ : syracuseStep 1946555 = 2919833) B2919833
theorem B865223 : Blo 864565 865223 := bstep (se 1 (by rfl) ⟨648917, by rfl⟩ : syracuseStep 865223 = 1297835) B1297835
theorem B865243 : Blo 864565 865243 := bstep (se 1 (by rfl) ⟨648932, by rfl⟩ : syracuseStep 865243 = 1297865) B1297865
theorem B865319 : Blo 864565 865319 := bstep (se 1 (by rfl) ⟨648989, by rfl⟩ : syracuseStep 865319 = 1297979) B1297979
theorem B1946681 : Blo 864565 1946681 := bstep (se 2 (by rfl) ⟨730005, by rfl⟩ : syracuseStep 1946681 = 1460011) B1460011
theorem B1094735 : Blo 864565 1094735 := bstep (se 1 (by rfl) ⟨821051, by rfl⟩ : syracuseStep 1094735 = 1642103) B1642103
theorem B865359 : Blo 864565 865359 := bstep (se 1 (by rfl) ⟨649019, by rfl⟩ : syracuseStep 865359 = 1298039) B1298039
theorem B865375 : Blo 864565 865375 := bstep (se 1 (by rfl) ⟨649031, by rfl⟩ : syracuseStep 865375 = 1298063) B1298063
theorem B865403 : Blo 864565 865403 := bstep (se 1 (by rfl) ⟨649052, by rfl⟩ : syracuseStep 865403 = 1298105) B1298105
theorem B865455 : Blo 864565 865455 := bstep (se 1 (by rfl) ⟨649091, by rfl⟩ : syracuseStep 865455 = 1298183) B1298183
theorem B865479 : Blo 864565 865479 := bstep (se 1 (by rfl) ⟨649109, by rfl⟩ : syracuseStep 865479 = 1298219) B1298219
theorem B865499 : Blo 864565 865499 := bstep (se 1 (by rfl) ⟨649124, by rfl⟩ : syracuseStep 865499 = 1298249) B1298249
theorem B2929931 : Blo 864565 2929931 := bstep (se 1 (by rfl) ⟨2197448, by rfl⟩ : syracuseStep 2929931 = 4394897) B4394897
theorem B865575 : Blo 864565 865575 := bstep (se 1 (by rfl) ⟨649181, by rfl⟩ : syracuseStep 865575 = 1298363) B1298363
theorem B865615 : Blo 864565 865615 := bstep (se 1 (by rfl) ⟨649211, by rfl⟩ : syracuseStep 865615 = 1298423) B1298423
theorem B865631 : Blo 864565 865631 := bstep (se 1 (by rfl) ⟨649223, by rfl⟩ : syracuseStep 865631 = 1298447) B1298447
theorem B2078057 : Blo 864565 2078057 := bstep (se 2 (by rfl) ⟨779271, by rfl⟩ : syracuseStep 2078057 = 1558543) B1558543
theorem B865659 : Blo 864565 865659 := bstep (se 1 (by rfl) ⟨649244, by rfl⟩ : syracuseStep 865659 = 1298489) B1298489
theorem B1947023 : Blo 864565 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B865711 : Blo 864565 865711 := bstep (se 1 (by rfl) ⟨649283, by rfl⟩ : syracuseStep 865711 = 1298567) B1298567
theorem B865735 : Blo 864565 865735 := bstep (se 1 (by rfl) ⟨649301, by rfl⟩ : syracuseStep 865735 = 1298603) B1298603
theorem B865755 : Blo 864565 865755 := bstep (se 1 (by rfl) ⟨649316, by rfl⟩ : syracuseStep 865755 = 1298633) B1298633
theorem B2930201 : Blo 864565 2930201 := bstep (se 2 (by rfl) ⟨1098825, by rfl⟩ : syracuseStep 2930201 = 2197651) B2197651
theorem B865831 : Blo 864565 865831 := bstep (se 1 (by rfl) ⟨649373, by rfl⟩ : syracuseStep 865831 = 1298747) B1298747
theorem B865871 : Blo 864565 865871 := bstep (se 1 (by rfl) ⟨649403, by rfl⟩ : syracuseStep 865871 = 1298807) B1298807
theorem B865887 : Blo 864565 865887 := bstep (se 1 (by rfl) ⟨649415, by rfl⟩ : syracuseStep 865887 = 1298831) B1298831
theorem B865915 : Blo 864565 865915 := bstep (se 1 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 865915 = 1298873) B1298873
theorem B865967 : Blo 864565 865967 := bstep (se 1 (by rfl) ⟨649475, by rfl⟩ : syracuseStep 865967 = 1298951) B1298951
theorem B3290813 : Blo 864565 3290813 := bstep (se 3 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 3290813 = 1234055) B1234055
theorem B865991 : Blo 864565 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B1390279 : Blo 864565 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B1947347 : Blo 864565 1947347 := bstep (se 1 (by rfl) ⟨1460510, by rfl⟩ : syracuseStep 1947347 = 2921021) B2921021
theorem B866011 : Blo 864565 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B866087 : Blo 864565 866087 := bstep (se 1 (by rfl) ⟨649565, by rfl⟩ : syracuseStep 866087 = 1299131) B1299131
theorem B866127 : Blo 864565 866127 := bstep (se 1 (by rfl) ⟨649595, by rfl⟩ : syracuseStep 866127 = 1299191) B1299191
theorem B866143 : Blo 864565 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B866171 : Blo 864565 866171 := bstep (se 1 (by rfl) ⟨649628, by rfl⟩ : syracuseStep 866171 = 1299257) B1299257
theorem B866223 : Blo 864565 866223 := bstep (se 1 (by rfl) ⟨649667, by rfl⟩ : syracuseStep 866223 = 1299335) B1299335
theorem B866247 : Blo 864565 866247 := bstep (se 1 (by rfl) ⟨649685, by rfl⟩ : syracuseStep 866247 = 1299371) B1299371
theorem B866267 : Blo 864565 866267 := bstep (se 1 (by rfl) ⟨649700, by rfl⟩ : syracuseStep 866267 = 1299401) B1299401
theorem B7387139 : Blo 864565 7387139 := bstep (se 1 (by rfl) ⟨5540354, by rfl⟩ : syracuseStep 7387139 = 11080709) B11080709
theorem B866343 : Blo 864565 866343 := bstep (se 1 (by rfl) ⟨649757, by rfl⟩ : syracuseStep 866343 = 1299515) B1299515
theorem B3848249 : Blo 864565 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B866383 : Blo 864565 866383 := bstep (se 1 (by rfl) ⟨649787, by rfl⟩ : syracuseStep 866383 = 1299575) B1299575
theorem B4438097 : Blo 864565 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B866399 : Blo 864565 866399 := bstep (se 1 (by rfl) ⟨649799, by rfl⟩ : syracuseStep 866399 = 1299599) B1299599
theorem B866427 : Blo 864565 866427 := bstep (se 1 (by rfl) ⟨649820, by rfl⟩ : syracuseStep 866427 = 1299641) B1299641
theorem B866479 : Blo 864565 866479 := bstep (se 1 (by rfl) ⟨649859, by rfl⟩ : syracuseStep 866479 = 1299719) B1299719
theorem B866503 : Blo 864565 866503 := bstep (se 1 (by rfl) ⟨649877, by rfl⟩ : syracuseStep 866503 = 1299755) B1299755
theorem B866523 : Blo 864565 866523 := bstep (se 1 (by rfl) ⟨649892, by rfl⟩ : syracuseStep 866523 = 1299785) B1299785
theorem B866599 : Blo 864565 866599 := bstep (se 1 (by rfl) ⟨649949, by rfl⟩ : syracuseStep 866599 = 1299899) B1299899
theorem B866639 : Blo 864565 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B1096031 : Blo 864565 1096031 := bstep (se 1 (by rfl) ⟨822023, by rfl⟩ : syracuseStep 1096031 = 1644047) B1644047
theorem B866655 : Blo 864565 866655 := bstep (se 1 (by rfl) ⟨649991, by rfl⟩ : syracuseStep 866655 = 1299983) B1299983
theorem B866683 : Blo 864565 866683 := bstep (se 1 (by rfl) ⟨650012, by rfl⟩ : syracuseStep 866683 = 1300025) B1300025
theorem B866735 : Blo 864565 866735 := bstep (se 1 (by rfl) ⟨650051, by rfl⟩ : syracuseStep 866735 = 1300103) B1300103
theorem B1391035 : Blo 864565 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B866759 : Blo 864565 866759 := bstep (se 1 (by rfl) ⟨650069, by rfl⟩ : syracuseStep 866759 = 1300139) B1300139
theorem B866779 : Blo 864565 866779 := bstep (se 1 (by rfl) ⟨650084, by rfl⟩ : syracuseStep 866779 = 1300169) B1300169
theorem B1849895 : Blo 864565 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B866855 : Blo 864565 866855 := bstep (se 1 (by rfl) ⟨650141, by rfl⟩ : syracuseStep 866855 = 1300283) B1300283
theorem B866895 : Blo 864565 866895 := bstep (se 1 (by rfl) ⟨650171, by rfl⟩ : syracuseStep 866895 = 1300343) B1300343
theorem B1391183 : Blo 864565 1391183 := bstep (se 1 (by rfl) ⟨1043387, by rfl⟩ : syracuseStep 1391183 = 2086775) B2086775
theorem B866911 : Blo 864565 866911 := bstep (se 1 (by rfl) ⟨650183, by rfl⟩ : syracuseStep 866911 = 1300367) B1300367
theorem B1948283 : Blo 864565 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B866939 : Blo 864565 866939 := bstep (se 1 (by rfl) ⟨650204, by rfl⟩ : syracuseStep 866939 = 1300409) B1300409
theorem B2931335 : Blo 864565 2931335 := bstep (se 1 (by rfl) ⟨2198501, by rfl⟩ : syracuseStep 2931335 = 4397003) B4397003
theorem B2964107 : Blo 864565 2964107 := bstep (se 1 (by rfl) ⟨2223080, by rfl⟩ : syracuseStep 2964107 = 4446161) B4446161
theorem B866991 : Blo 864565 866991 := bstep (se 1 (by rfl) ⟨650243, by rfl⟩ : syracuseStep 866991 = 1300487) B1300487
theorem B2931389 : Blo 864565 2931389 := bstep (se 3 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 2931389 = 1099271) B1099271
theorem B867015 : Blo 864565 867015 := bstep (se 1 (by rfl) ⟨650261, by rfl⟩ : syracuseStep 867015 = 1300523) B1300523
theorem B867035 : Blo 864565 867035 := bstep (se 1 (by rfl) ⟨650276, by rfl⟩ : syracuseStep 867035 = 1300553) B1300553
theorem B1948409 : Blo 864565 1948409 := bstep (se 2 (by rfl) ⟨730653, by rfl⟩ : syracuseStep 1948409 = 1461307) B1461307
theorem B4438813 : Blo 864565 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B867111 : Blo 864565 867111 := bstep (se 1 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 867111 = 1300667) B1300667
theorem B2407241 : Blo 864565 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B867151 : Blo 864565 867151 := bstep (se 1 (by rfl) ⟨650363, by rfl⟩ : syracuseStep 867151 = 1300727) B1300727
theorem B867167 : Blo 864565 867167 := bstep (se 1 (by rfl) ⟨650375, by rfl⟩ : syracuseStep 867167 = 1300751) B1300751
theorem B867195 : Blo 864565 867195 := bstep (se 1 (by rfl) ⟨650396, by rfl⟩ : syracuseStep 867195 = 1300793) B1300793
theorem B867247 : Blo 864565 867247 := bstep (se 1 (by rfl) ⟨650435, by rfl⟩ : syracuseStep 867247 = 1300871) B1300871
theorem B867271 : Blo 864565 867271 := bstep (se 1 (by rfl) ⟨650453, by rfl⟩ : syracuseStep 867271 = 1300907) B1300907
theorem B867291 : Blo 864565 867291 := bstep (se 1 (by rfl) ⟨650468, by rfl⟩ : syracuseStep 867291 = 1300937) B1300937
theorem B1948679 : Blo 864565 1948679 := bstep (se 1 (by rfl) ⟨1461509, by rfl⟩ : syracuseStep 1948679 = 2923019) B2923019
theorem B867367 : Blo 864565 867367 := bstep (se 1 (by rfl) ⟨650525, by rfl⟩ : syracuseStep 867367 = 1301051) B1301051
theorem B1948751 : Blo 864565 1948751 := bstep (se 1 (by rfl) ⟨1461563, by rfl⟩ : syracuseStep 1948751 = 2923127) B2923127
theorem B867407 : Blo 864565 867407 := bstep (se 1 (by rfl) ⟨650555, by rfl⟩ : syracuseStep 867407 = 1301111) B1301111
theorem B867423 : Blo 864565 867423 := bstep (se 1 (by rfl) ⟨650567, by rfl⟩ : syracuseStep 867423 = 1301135) B1301135
theorem B867451 : Blo 864565 867451 := bstep (se 1 (by rfl) ⟨650588, by rfl⟩ : syracuseStep 867451 = 1301177) B1301177
theorem B867503 : Blo 864565 867503 := bstep (se 1 (by rfl) ⟨650627, by rfl⟩ : syracuseStep 867503 = 1301255) B1301255
theorem B867527 : Blo 864565 867527 := bstep (se 1 (by rfl) ⟨650645, by rfl⟩ : syracuseStep 867527 = 1301291) B1301291
theorem B867547 : Blo 864565 867547 := bstep (se 1 (by rfl) ⟨650660, by rfl⟩ : syracuseStep 867547 = 1301321) B1301321
theorem B867623 : Blo 864565 867623 := bstep (se 1 (by rfl) ⟨650717, by rfl⟩ : syracuseStep 867623 = 1301435) B1301435
theorem B867663 : Blo 864565 867663 := bstep (se 1 (by rfl) ⟨650747, by rfl⟩ : syracuseStep 867663 = 1301495) B1301495
theorem B867679 : Blo 864565 867679 := bstep (se 1 (by rfl) ⟨650759, by rfl⟩ : syracuseStep 867679 = 1301519) B1301519
theorem B867707 : Blo 864565 867707 := bstep (se 1 (by rfl) ⟨650780, by rfl⟩ : syracuseStep 867707 = 1301561) B1301561
theorem B3292559 : Blo 864565 3292559 := bstep (se 1 (by rfl) ⟨2469419, by rfl⟩ : syracuseStep 3292559 = 4938839) B4938839
theorem B867759 : Blo 864565 867759 := bstep (se 1 (by rfl) ⟨650819, by rfl⟩ : syracuseStep 867759 = 1301639) B1301639
theorem B867783 : Blo 864565 867783 := bstep (se 1 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 867783 = 1301675) B1301675
theorem B1949147 : Blo 864565 1949147 := bstep (se 1 (by rfl) ⟨1461860, by rfl⟩ : syracuseStep 1949147 = 2923721) B2923721
theorem B867803 : Blo 864565 867803 := bstep (se 1 (by rfl) ⟨650852, by rfl⟩ : syracuseStep 867803 = 1301705) B1301705
theorem B867879 : Blo 864565 867879 := bstep (se 1 (by rfl) ⟨650909, by rfl⟩ : syracuseStep 867879 = 1301819) B1301819
theorem B3161659 : Blo 864565 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B867919 : Blo 864565 867919 := bstep (se 1 (by rfl) ⟨650939, by rfl⟩ : syracuseStep 867919 = 1301879) B1301879
theorem B867935 : Blo 864565 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B867963 : Blo 864565 867963 := bstep (se 1 (by rfl) ⟨650972, by rfl⟩ : syracuseStep 867963 = 1301945) B1301945
theorem B868015 : Blo 864565 868015 := bstep (se 1 (by rfl) ⟨651011, by rfl⟩ : syracuseStep 868015 = 1302023) B1302023
theorem B868039 : Blo 864565 868039 := bstep (se 1 (by rfl) ⟨651029, by rfl⟩ : syracuseStep 868039 = 1302059) B1302059
theorem B868059 : Blo 864565 868059 := bstep (se 1 (by rfl) ⟨651044, by rfl⟩ : syracuseStep 868059 = 1302089) B1302089
theorem B868135 : Blo 864565 868135 := bstep (se 1 (by rfl) ⟨651101, by rfl⟩ : syracuseStep 868135 = 1302203) B1302203
theorem B868175 : Blo 864565 868175 := bstep (se 1 (by rfl) ⟨651131, by rfl⟩ : syracuseStep 868175 = 1302263) B1302263
theorem B868191 : Blo 864565 868191 := bstep (se 1 (by rfl) ⟨651143, by rfl⟩ : syracuseStep 868191 = 1302287) B1302287
theorem B868219 : Blo 864565 868219 := bstep (se 1 (by rfl) ⟨651164, by rfl⟩ : syracuseStep 868219 = 1302329) B1302329
theorem B1949615 : Blo 864565 1949615 := bstep (se 1 (by rfl) ⟨1462211, by rfl⟩ : syracuseStep 1949615 = 2924423) B2924423
theorem B868271 : Blo 864565 868271 := bstep (se 1 (by rfl) ⟨651203, by rfl⟩ : syracuseStep 868271 = 1302407) B1302407
theorem B3751867 : Blo 864565 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B868295 : Blo 864565 868295 := bstep (se 1 (by rfl) ⟨651221, by rfl⟩ : syracuseStep 868295 = 1302443) B1302443
theorem B868315 : Blo 864565 868315 := bstep (se 1 (by rfl) ⟨651236, by rfl⟩ : syracuseStep 868315 = 1302473) B1302473
theorem B868391 : Blo 864565 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B4997177 : Blo 864565 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B868431 : Blo 864565 868431 := bstep (se 1 (by rfl) ⟨651323, by rfl⟩ : syracuseStep 868431 = 1302647) B1302647
theorem B868447 : Blo 864565 868447 := bstep (se 1 (by rfl) ⟨651335, by rfl⟩ : syracuseStep 868447 = 1302671) B1302671
theorem B868475 : Blo 864565 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B1949867 : Blo 864565 1949867 := bstep (se 1 (by rfl) ⟨1462400, by rfl⟩ : syracuseStep 1949867 = 2924801) B2924801
theorem B868527 : Blo 864565 868527 := bstep (se 1 (by rfl) ⟨651395, by rfl⟩ : syracuseStep 868527 = 1302791) B1302791
theorem B868551 : Blo 864565 868551 := bstep (se 1 (by rfl) ⟨651413, by rfl⟩ : syracuseStep 868551 = 1302827) B1302827
theorem B8995337 : Blo 864565 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B3293729 : Blo 864565 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B1950407 : Blo 864565 1950407 := bstep (se 1 (by rfl) ⟨1462805, by rfl⟩ : syracuseStep 1950407 = 2925611) B2925611
theorem B5554889 : Blo 864565 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B3293945 : Blo 864565 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B4440905 : Blo 864565 4440905 := bstep (se 2 (by rfl) ⟨1665339, by rfl⟩ : syracuseStep 4440905 = 3330679) B3330679
theorem B1459039 : Blo 864565 1459039 := bstep (se 1 (by rfl) ⟨1094279, by rfl⟩ : syracuseStep 1459039 = 2188559) B2188559
theorem B3294047 : Blo 864565 3294047 := bstep (se 1 (by rfl) ⟨2470535, by rfl⟩ : syracuseStep 3294047 = 4941071) B4941071
theorem B1852321 : Blo 864565 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B1459127 : Blo 864565 1459127 := bstep (se 1 (by rfl) ⟨1094345, by rfl⟩ : syracuseStep 1459127 = 2188691) B2188691
theorem B1098679 : Blo 864565 1098679 := bstep (se 1 (by rfl) ⟨824009, by rfl⟩ : syracuseStep 1098679 = 1648019) B1648019
theorem B3294215 : Blo 864565 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B56149037 : Blo 864565 56149037 := bstep (se 3 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 56149037 = 21055889) B21055889
theorem B5260567 : Blo 864565 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B4933007 : Blo 864565 4933007 := bstep (se 1 (by rfl) ⟨3699755, by rfl⟩ : syracuseStep 4933007 = 7399511) B7399511
theorem B6243803 : Blo 864565 6243803 := bstep (se 1 (by rfl) ⟨4682852, by rfl⟩ : syracuseStep 6243803 = 9365705) B9365705
theorem B3294701 : Blo 864565 3294701 := bstep (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) B1235513
theorem B1459721 : Blo 864565 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B2082343 : Blo 864565 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B1951271 : Blo 864565 1951271 := bstep (se 1 (by rfl) ⟨1463453, by rfl⟩ : syracuseStep 1951271 = 2926907) B2926907
theorem B2082401 : Blo 864565 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B1459883 : Blo 864565 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B3295019 : Blo 864565 3295019 := bstep (se 1 (by rfl) ⟨2471264, by rfl⟩ : syracuseStep 3295019 = 4942529) B4942529
theorem B1951595 : Blo 864565 1951595 := bstep (se 1 (by rfl) ⟨1463696, by rfl⟩ : syracuseStep 1951595 = 2927393) B2927393
theorem B1951649 : Blo 864565 1951649 := bstep (se 2 (by rfl) ⟨731868, by rfl⟩ : syracuseStep 1951649 = 1463737) B1463737
theorem B1755145 : Blo 864565 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B1460281 : Blo 864565 1460281 := bstep (se 2 (by rfl) ⟨547605, by rfl⟩ : syracuseStep 1460281 = 1095211) B1095211
theorem B1755307 : Blo 864565 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B1460423 : Blo 864565 1460423 := bstep (se 1 (by rfl) ⟨1095317, by rfl⟩ : syracuseStep 1460423 = 2190635) B2190635
theorem B1951991 : Blo 864565 1951991 := bstep (se 1 (by rfl) ⟨1463993, by rfl⟩ : syracuseStep 1951991 = 2927987) B2927987
theorem B1460585 : Blo 864565 1460585 := bstep (se 2 (by rfl) ⟨547719, by rfl⟩ : syracuseStep 1460585 = 1095439) B1095439
theorem B14797241 : Blo 864565 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B2083315 : Blo 864565 2083315 := bstep (se 1 (by rfl) ⟨1562486, by rfl⟩ : syracuseStep 2083315 = 3124973) B3124973
theorem B1296905 : Blo 864565 1296905 := bstep (se 2 (by rfl) ⟨486339, by rfl⟩ : syracuseStep 1296905 = 972679) B972679
theorem B4442633 : Blo 864565 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B1296935 : Blo 864565 1296935 := bstep (se 1 (by rfl) ⟨972701, by rfl⟩ : syracuseStep 1296935 = 1945403) B1945403
theorem B1297019 : Blo 864565 1297019 := bstep (se 1 (by rfl) ⟨972764, by rfl⟩ : syracuseStep 1297019 = 1945529) B1945529
theorem B1460983 : Blo 864565 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B1297145 : Blo 864565 1297145 := bstep (se 2 (by rfl) ⟨486429, by rfl⟩ : syracuseStep 1297145 = 972859) B972859
theorem B1952585 : Blo 864565 1952585 := bstep (se 2 (by rfl) ⟨732219, by rfl⟩ : syracuseStep 1952585 = 1464439) B1464439
theorem B1297247 : Blo 864565 1297247 := bstep (se 1 (by rfl) ⟨972935, by rfl⟩ : syracuseStep 1297247 = 1945871) B1945871
theorem B1297259 : Blo 864565 1297259 := bstep (se 1 (by rfl) ⟨972944, by rfl⟩ : syracuseStep 1297259 = 1945889) B1945889
theorem B1461179 : Blo 864565 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B2968595 : Blo 864565 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1461287 : Blo 864565 1461287 := bstep (se 1 (by rfl) ⟨1095965, by rfl⟩ : syracuseStep 1461287 = 2191931) B2191931
theorem B1297487 : Blo 864565 1297487 := bstep (se 1 (by rfl) ⟨973115, by rfl⟩ : syracuseStep 1297487 = 1946231) B1946231
theorem B1297607 : Blo 864565 1297607 := bstep (se 1 (by rfl) ⟨973205, by rfl⟩ : syracuseStep 1297607 = 1946411) B1946411
theorem B1461577 : Blo 864565 1461577 := bstep (se 2 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 1461577 = 1096183) B1096183
theorem B1297769 : Blo 864565 1297769 := bstep (se 2 (by rfl) ⟨486663, by rfl⟩ : syracuseStep 1297769 = 973327) B973327
theorem B1461611 : Blo 864565 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B2674063 : Blo 864565 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B1297847 : Blo 864565 1297847 := bstep (se 1 (by rfl) ⟨973385, by rfl⟩ : syracuseStep 1297847 = 1946771) B1946771
theorem B1297883 : Blo 864565 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B1953377 : Blo 864565 1953377 := bstep (se 2 (by rfl) ⟨732516, by rfl⟩ : syracuseStep 1953377 = 1465033) B1465033
theorem B6672071 : Blo 864565 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B1462009 : Blo 864565 1462009 := bstep (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) B1096507
theorem B5263147 : Blo 864565 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B4935491 : Blo 864565 4935491 := bstep (se 1 (by rfl) ⟨3701618, by rfl⟩ : syracuseStep 4935491 = 7403237) B7403237
theorem B937823 : Blo 864565 937823 := bstep (se 1 (by rfl) ⟨703367, by rfl⟩ : syracuseStep 937823 = 1406735) B1406735
theorem B3297131 : Blo 864565 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B1298351 : Blo 864565 1298351 := bstep (se 1 (by rfl) ⟨973763, by rfl⟩ : syracuseStep 1298351 = 1947527) B1947527
theorem B1003439 : Blo 864565 1003439 := bstep (se 1 (by rfl) ⟨752579, by rfl⟩ : syracuseStep 1003439 = 1505159) B1505159
theorem B1953719 : Blo 864565 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B1462279 : Blo 864565 1462279 := bstep (se 1 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 1462279 = 2193419) B2193419
theorem B1298441 : Blo 864565 1298441 := bstep (se 2 (by rfl) ⟨486915, by rfl⟩ : syracuseStep 1298441 = 973831) B973831
theorem B1298471 : Blo 864565 1298471 := bstep (se 1 (by rfl) ⟨973853, by rfl⟩ : syracuseStep 1298471 = 1947707) B1947707
theorem B1298555 : Blo 864565 1298555 := bstep (se 1 (by rfl) ⟨973916, by rfl⟩ : syracuseStep 1298555 = 1947833) B1947833
theorem B1298681 : Blo 864565 1298681 := bstep (se 2 (by rfl) ⟨487005, by rfl⟩ : syracuseStep 1298681 = 974011) B974011
theorem B1757513 : Blo 864565 1757513 := bstep (se 2 (by rfl) ⟨659067, by rfl⟩ : syracuseStep 1757513 = 1318135) B1318135
theorem B1298783 : Blo 864565 1298783 := bstep (se 1 (by rfl) ⟨974087, by rfl⟩ : syracuseStep 1298783 = 1948175) B1948175
theorem B1298795 : Blo 864565 1298795 := bstep (se 1 (by rfl) ⟨974096, by rfl⟩ : syracuseStep 1298795 = 1948193) B1948193
theorem B1462711 : Blo 864565 1462711 := bstep (se 1 (by rfl) ⟨1097033, by rfl⟩ : syracuseStep 1462711 = 2194067) B2194067
theorem B1757627 : Blo 864565 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B5558807 : Blo 864565 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B1299023 : Blo 864565 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B1462907 : Blo 864565 1462907 := bstep (se 1 (by rfl) ⟨1097180, by rfl⟩ : syracuseStep 1462907 = 2194361) B2194361
theorem B1299143 : Blo 864565 1299143 := bstep (se 1 (by rfl) ⟨974357, by rfl⟩ : syracuseStep 1299143 = 1948715) B1948715
theorem B4379345 : Blo 864565 4379345 := bstep (se 2 (by rfl) ⟨1642254, by rfl⟩ : syracuseStep 4379345 = 3284509) B3284509
theorem B7033553 : Blo 864565 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B40555363 : Blo 864565 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1299305 : Blo 864565 1299305 := bstep (se 2 (by rfl) ⟨487239, by rfl⟩ : syracuseStep 1299305 = 974479) B974479
theorem B1299383 : Blo 864565 1299383 := bstep (se 1 (by rfl) ⟨974537, by rfl⟩ : syracuseStep 1299383 = 1949075) B1949075
theorem B1299419 : Blo 864565 1299419 := bstep (se 1 (by rfl) ⟨974564, by rfl⟩ : syracuseStep 1299419 = 1949129) B1949129
theorem B1463305 : Blo 864565 1463305 := bstep (se 2 (by rfl) ⟨548739, by rfl⟩ : syracuseStep 1463305 = 1097479) B1097479
theorem B1463467 : Blo 864565 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B1299887 : Blo 864565 1299887 := bstep (se 1 (by rfl) ⟨974915, by rfl⟩ : syracuseStep 1299887 = 1949831) B1949831
theorem B6575579 : Blo 864565 6575579 := bstep (se 1 (by rfl) ⟨4931684, by rfl⟩ : syracuseStep 6575579 = 9863369) B9863369
theorem B1463771 : Blo 864565 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B1299977 : Blo 864565 1299977 := bstep (se 2 (by rfl) ⟨487491, by rfl⟩ : syracuseStep 1299977 = 974983) B974983
theorem B1300007 : Blo 864565 1300007 := bstep (se 1 (by rfl) ⟨975005, by rfl⟩ : syracuseStep 1300007 = 1950011) B1950011
theorem B1300091 : Blo 864565 1300091 := bstep (se 1 (by rfl) ⟨975068, by rfl⟩ : syracuseStep 1300091 = 1950137) B1950137
theorem B1464007 : Blo 864565 1464007 := bstep (se 1 (by rfl) ⟨1098005, by rfl⟩ : syracuseStep 1464007 = 2196011) B2196011
theorem B1300217 : Blo 864565 1300217 := bstep (se 2 (by rfl) ⟨487581, by rfl⟩ : syracuseStep 1300217 = 975163) B975163
theorem B2086649 : Blo 864565 2086649 := bstep (se 2 (by rfl) ⟨782493, by rfl⟩ : syracuseStep 2086649 = 1564987) B1564987
theorem B1300319 : Blo 864565 1300319 := bstep (se 1 (by rfl) ⟨975239, by rfl⟩ : syracuseStep 1300319 = 1950479) B1950479
theorem B1464169 : Blo 864565 1464169 := bstep (se 2 (by rfl) ⟨549063, by rfl⟩ : syracuseStep 1464169 = 1098127) B1098127
theorem B1300331 : Blo 864565 1300331 := bstep (se 1 (by rfl) ⟨975248, by rfl⟩ : syracuseStep 1300331 = 1950497) B1950497
theorem B6576065 : Blo 864565 6576065 := bstep (se 2 (by rfl) ⟨2466024, by rfl⟩ : syracuseStep 6576065 = 4932049) B4932049
theorem B1169447 : Blo 864565 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B1300559 : Blo 864565 1300559 := bstep (se 1 (by rfl) ⟨975419, by rfl⟩ : syracuseStep 1300559 = 1950839) B1950839
theorem B1300679 : Blo 864565 1300679 := bstep (se 1 (by rfl) ⟨975509, by rfl⟩ : syracuseStep 1300679 = 1951019) B1951019
theorem B1300841 : Blo 864565 1300841 := bstep (se 2 (by rfl) ⟨487815, by rfl⟩ : syracuseStep 1300841 = 975631) B975631
theorem B1300919 : Blo 864565 1300919 := bstep (se 1 (by rfl) ⟨975689, by rfl⟩ : syracuseStep 1300919 = 1951379) B1951379
theorem B1464763 : Blo 864565 1464763 := bstep (se 1 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 1464763 = 2197145) B2197145
theorem B1300955 : Blo 864565 1300955 := bstep (se 1 (by rfl) ⟨975716, by rfl⟩ : syracuseStep 1300955 = 1951433) B1951433
theorem B1464871 : Blo 864565 1464871 := bstep (se 1 (by rfl) ⟨1098653, by rfl⟩ : syracuseStep 1464871 = 2197307) B2197307
theorem B973435 : Blo 864565 973435 := bstep (se 1 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 973435 = 1460153) B1460153
theorem B1465195 : Blo 864565 1465195 := bstep (se 1 (by rfl) ⟨1098896, by rfl⟩ : syracuseStep 1465195 = 2197793) B2197793
theorem B1301423 : Blo 864565 1301423 := bstep (se 1 (by rfl) ⟨976067, by rfl⟩ : syracuseStep 1301423 = 1952135) B1952135
theorem B1301513 : Blo 864565 1301513 := bstep (se 2 (by rfl) ⟨488067, by rfl⟩ : syracuseStep 1301513 = 976135) B976135
theorem B1301543 : Blo 864565 1301543 := bstep (se 1 (by rfl) ⟨976157, by rfl⟩ : syracuseStep 1301543 = 1952315) B1952315
theorem B4381775 : Blo 864565 4381775 := bstep (se 1 (by rfl) ⟨3286331, by rfl⟩ : syracuseStep 4381775 = 6572663) B6572663
theorem B973903 : Blo 864565 973903 := bstep (se 1 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 973903 = 1460855) B1460855
theorem B1301627 : Blo 864565 1301627 := bstep (se 1 (by rfl) ⟨976220, by rfl⟩ : syracuseStep 1301627 = 1952441) B1952441
theorem B1301753 : Blo 864565 1301753 := bstep (se 2 (by rfl) ⟨488157, by rfl⟩ : syracuseStep 1301753 = 976315) B976315
theorem B1039711 : Blo 864565 1039711 := bstep (se 1 (by rfl) ⟨779783, by rfl⟩ : syracuseStep 1039711 = 1559567) B1559567
theorem B1301855 : Blo 864565 1301855 := bstep (se 1 (by rfl) ⟨976391, by rfl⟩ : syracuseStep 1301855 = 1952783) B1952783
theorem B1301867 : Blo 864565 1301867 := bstep (se 1 (by rfl) ⟨976400, by rfl⟩ : syracuseStep 1301867 = 1952801) B1952801
theorem B6577523 : Blo 864565 6577523 := bstep (se 1 (by rfl) ⟨4933142, by rfl⟩ : syracuseStep 6577523 = 9866285) B9866285
theorem B2252161 : Blo 864565 2252161 := bstep (se 2 (by rfl) ⟨844560, by rfl⟩ : syracuseStep 2252161 = 1689121) B1689121
theorem B974299 : Blo 864565 974299 := bstep (se 1 (by rfl) ⟨730724, by rfl⟩ : syracuseStep 974299 = 1461449) B1461449
theorem B1170983 : Blo 864565 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B1302095 : Blo 864565 1302095 := bstep (se 1 (by rfl) ⟨976571, by rfl⟩ : syracuseStep 1302095 = 1953143) B1953143
theorem B1302215 : Blo 864565 1302215 := bstep (se 1 (by rfl) ⟨976661, by rfl⟩ : syracuseStep 1302215 = 1953323) B1953323
theorem B4382423 : Blo 864565 4382423 := bstep (se 1 (by rfl) ⟨3286817, by rfl⟩ : syracuseStep 4382423 = 6573635) B6573635
theorem B4677443 : Blo 864565 4677443 := bstep (se 1 (by rfl) ⟨3508082, by rfl⟩ : syracuseStep 4677443 = 7016165) B7016165
theorem B1302377 : Blo 864565 1302377 := bstep (se 2 (by rfl) ⟨488391, by rfl⟩ : syracuseStep 1302377 = 976783) B976783
theorem B974767 : Blo 864565 974767 := bstep (se 1 (by rfl) ⟨731075, by rfl⟩ : syracuseStep 974767 = 1462151) B1462151
theorem B1302455 : Blo 864565 1302455 := bstep (se 1 (by rfl) ⟨976841, by rfl⟩ : syracuseStep 1302455 = 1953683) B1953683
theorem B1302491 : Blo 864565 1302491 := bstep (se 1 (by rfl) ⟨976868, by rfl⟩ : syracuseStep 1302491 = 1953737) B1953737
theorem B4939865 : Blo 864565 4939865 := bstep (se 2 (by rfl) ⟨1852449, by rfl⟩ : syracuseStep 4939865 = 3704899) B3704899
theorem B1040735 : Blo 864565 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B975199 : Blo 864565 975199 := bstep (se 1 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 975199 = 1462799) B1462799
theorem B4940297 : Blo 864565 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B975559 : Blo 864565 975559 := bstep (se 1 (by rfl) ⟨731669, by rfl⟩ : syracuseStep 975559 = 1463339) B1463339
theorem B27452363 : Blo 864565 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B1172443 : Blo 864565 1172443 := bstep (se 1 (by rfl) ⟨879332, by rfl⟩ : syracuseStep 1172443 = 1758665) B1758665
theorem B3696167 : Blo 864565 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B976423 : Blo 864565 976423 := bstep (se 1 (by rfl) ⟨732317, by rfl⟩ : syracuseStep 976423 = 1464635) B1464635
theorem B2189015 : Blo 864565 2189015 := bstep (se 1 (by rfl) ⟨1641761, by rfl⟩ : syracuseStep 2189015 = 3283523) B3283523
theorem B5793569 : Blo 864565 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B5564321 : Blo 864565 5564321 := bstep (se 2 (by rfl) ⟨2086620, by rfl⟩ : syracuseStep 5564321 = 4173241) B4173241
theorem B4941755 : Blo 864565 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B2189369 : Blo 864565 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B7039133 : Blo 864565 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B8907059 : Blo 864565 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B4385339 : Blo 864565 4385339 := bstep (se 1 (by rfl) ⟨3289004, by rfl⟩ : syracuseStep 4385339 = 6578009) B6578009
theorem B3336839 : Blo 864565 3336839 := bstep (se 1 (by rfl) ⟨2502629, by rfl⟩ : syracuseStep 3336839 = 5005259) B5005259
theorem B5270201 : Blo 864565 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B13200101 : Blo 864565 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B4156343 : Blo 864565 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B4385987 : Blo 864565 4385987 := bstep (se 1 (by rfl) ⟨3289490, by rfl⟩ : syracuseStep 4385987 = 6578981) B6578981
theorem B1109467 : Blo 864565 1109467 := bstep (se 1 (by rfl) ⟨832100, by rfl⟩ : syracuseStep 1109467 = 1664201) B1664201
theorem B7892603 : Blo 864565 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B4222763 : Blo 864565 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B3338057 : Blo 864565 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B3567521 : Blo 864565 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B4943987 : Blo 864565 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B2781341 : Blo 864565 2781341 := bstep (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) B1043003
theorem B2191607 : Blo 864565 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B2781659 : Blo 864565 2781659 := bstep (se 1 (by rfl) ⟨2086244, by rfl⟩ : syracuseStep 2781659 = 4172489) B4172489
theorem B13332995 : Blo 864565 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B3699209 : Blo 864565 3699209 := bstep (se 2 (by rfl) ⟨1387203, by rfl⟩ : syracuseStep 3699209 = 2774407) B2774407
theorem B8320067 : Blo 864565 8320067 := bstep (se 1 (by rfl) ⟨6240050, by rfl⟩ : syracuseStep 8320067 = 12480101) B12480101
theorem B5010983 : Blo 864565 5010983 := bstep (se 1 (by rfl) ⟨3758237, by rfl⟩ : syracuseStep 5010983 = 7516475) B7516475
theorem B2193095 : Blo 864565 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B12515107 : Blo 864565 12515107 := bstep (se 1 (by rfl) ⟨9386330, by rfl⟩ : syracuseStep 12515107 = 18772661) B18772661
theorem B6584327 : Blo 864565 6584327 := bstep (se 1 (by rfl) ⟨4938245, by rfl⟩ : syracuseStep 6584327 = 9876491) B9876491
theorem B17824033 : Blo 864565 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B53377517 : Blo 864565 53377517 := bstep (se 3 (by rfl) ⟨10008284, by rfl⟩ : syracuseStep 53377517 = 20016569) B20016569
theorem B6584813 : Blo 864565 6584813 := bstep (se 3 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 6584813 = 2469305) B2469305
theorem B4749857 : Blo 864565 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B2194249 : Blo 864565 2194249 := bstep (se 2 (by rfl) ⟨822843, by rfl⟩ : syracuseStep 2194249 = 1645687) B1645687
theorem B4390523 : Blo 864565 4390523 := bstep (se 1 (by rfl) ⟨3292892, by rfl⟩ : syracuseStep 4390523 = 6585785) B6585785
theorem B2195383 : Blo 864565 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B7012403 : Blo 864565 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B4391171 : Blo 864565 4391171 := bstep (se 1 (by rfl) ⟨3293378, by rfl⟩ : syracuseStep 4391171 = 6586757) B6586757
theorem B5996891 : Blo 864565 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B2195819 : Blo 864565 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B3703259 : Blo 864565 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B2195963 : Blo 864565 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B2196031 : Blo 864565 2196031 := bstep (se 1 (by rfl) ⟨1647023, by rfl⟩ : syracuseStep 2196031 = 3294047) B3294047
theorem B4391495 : Blo 864565 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B2196143 : Blo 864565 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B4686785 : Blo 864565 4686785 := bstep (se 2 (by rfl) ⟨1757544, by rfl⟩ : syracuseStep 4686785 = 3515089) B3515089
theorem B4162535 : Blo 864565 4162535 := bstep (se 1 (by rfl) ⟨3121901, by rfl⟩ : syracuseStep 4162535 = 6243803) B6243803
theorem B2196467 : Blo 864565 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B2196679 : Blo 864565 2196679 := bstep (se 1 (by rfl) ⟨1647509, by rfl⟩ : syracuseStep 2196679 = 3295019) B3295019
theorem B95061509 : Blo 864565 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B9864827 : Blo 864565 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B7014089 : Blo 864565 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B4392791 : Blo 864565 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B6588701 : Blo 864565 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B73206301 : Blo 864565 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B2198087 : Blo 864565 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B4164169 : Blo 864565 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B2198137 : Blo 864565 2198137 := bstep (se 2 (by rfl) ⟨824301, by rfl⟩ : syracuseStep 2198137 = 1648603) B1648603
theorem B2919293 : Blo 864565 2919293 := bstep (se 3 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 2919293 = 1094735) B1094735
theorem B2919563 : Blo 864565 2919563 := bstep (se 1 (by rfl) ⟨2189672, by rfl⟩ : syracuseStep 2919563 = 4379345) B4379345
theorem B4689035 : Blo 864565 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B23662043 : Blo 864565 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B4395059 : Blo 864565 4395059 := bstep (se 1 (by rfl) ⟨3296294, by rfl⟩ : syracuseStep 4395059 = 6592589) B6592589
theorem B2921183 : Blo 864565 2921183 := bstep (se 1 (by rfl) ⟨2190887, by rfl⟩ : syracuseStep 2921183 = 4381775) B4381775
theorem B7017529 : Blo 864565 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B2921615 : Blo 864565 2921615 := bstep (se 1 (by rfl) ⟨2191211, by rfl⟩ : syracuseStep 2921615 = 4382423) B4382423
theorem B4166801 : Blo 864565 4166801 := bstep (se 2 (by rfl) ⟨1562550, by rfl⟩ : syracuseStep 4166801 = 3125101) B3125101
theorem B3118295 : Blo 864565 3118295 := bstep (se 1 (by rfl) ⟨2338721, by rfl⟩ : syracuseStep 3118295 = 4677443) B4677443
theorem B10261997 : Blo 864565 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B4396679 : Blo 864565 4396679 := bstep (se 1 (by rfl) ⟨3297509, by rfl⟩ : syracuseStep 4396679 = 6595019) B6595019
theorem B2922749 : Blo 864565 2922749 := bstep (se 3 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 2922749 = 1096031) B1096031
theorem B2464111 : Blo 864565 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B54073817 : Blo 864565 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B3709547 : Blo 864565 3709547 := bstep (se 1 (by rfl) ⟨2782160, by rfl⟩ : syracuseStep 3709547 = 5564321) B5564321
theorem B4692755 : Blo 864565 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B5938039 : Blo 864565 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B23731127 : Blo 864565 23731127 := bstep (se 1 (by rfl) ⟨17798345, by rfl⟩ : syracuseStep 23731127 = 35596691) B35596691
theorem B2923559 : Blo 864565 2923559 := bstep (se 1 (by rfl) ⟨2192669, by rfl⟩ : syracuseStep 2923559 = 4385339) B4385339
theorem B9378935 : Blo 864565 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B3513467 : Blo 864565 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B2923991 : Blo 864565 2923991 := bstep (se 1 (by rfl) ⟨2192993, by rfl⟩ : syracuseStep 2923991 = 4385987) B4385987
theorem B3284495 : Blo 864565 3284495 := bstep (se 1 (by rfl) ⟨2463371, by rfl⟩ : syracuseStep 3284495 = 4926743) B4926743
theorem B16686809 : Blo 864565 16686809 := bstep (se 2 (by rfl) ⟨6257553, by rfl⟩ : syracuseStep 16686809 = 12515107) B12515107
theorem B3284783 : Blo 864565 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B8888663 : Blo 864565 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B2466139 : Blo 864565 2466139 := bstep (se 1 (by rfl) ⟨1849604, by rfl⟩ : syracuseStep 2466139 = 3699209) B3699209
theorem B5546711 : Blo 864565 5546711 := bstep (se 1 (by rfl) ⟨4160033, by rfl⟩ : syracuseStep 5546711 = 8320067) B8320067
theorem B1385371 : Blo 864565 1385371 := bstep (se 1 (by rfl) ⟨1039028, by rfl⟩ : syracuseStep 1385371 = 2078057) B2078057
theorem B10003445 : Blo 864565 10003445 := bstep (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) B937823
theorem B2925665 : Blo 864565 2925665 := bstep (se 2 (by rfl) ⟨1097124, by rfl⟩ : syracuseStep 2925665 = 2194249) B2194249
theorem B4924759 : Blo 864565 4924759 := bstep (se 1 (by rfl) ⟨3693569, by rfl⟩ : syracuseStep 4924759 = 7387139) B7387139
theorem B2958731 : Blo 864565 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B3122621 : Blo 864565 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B927455 : Blo 864565 927455 := bstep (se 1 (by rfl) ⟨695591, by rfl⟩ : syracuseStep 927455 = 1391183) B1391183
theorem B1976071 : Blo 864565 1976071 := bstep (se 1 (by rfl) ⟨1482053, by rfl⟩ : syracuseStep 1976071 = 2964107) B2964107
theorem B1386281 : Blo 864565 1386281 := bstep (se 2 (by rfl) ⟨519855, by rfl⟩ : syracuseStep 1386281 = 1039711) B1039711
theorem B2927015 : Blo 864565 2927015 := bstep (se 1 (by rfl) ⟨2195261, by rfl⟩ : syracuseStep 2927015 = 4390523) B4390523
theorem B9513389 : Blo 864565 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B2927177 : Blo 864565 2927177 := bstep (se 2 (by rfl) ⟨1097691, by rfl⟩ : syracuseStep 2927177 = 2195383) B2195383
theorem B2468987 : Blo 864565 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B2960603 : Blo 864565 2960603 := bstep (se 1 (by rfl) ⟨2220452, by rfl⟩ : syracuseStep 2960603 = 4440905) B4440905
theorem B37432691 : Blo 864565 37432691 := bstep (se 1 (by rfl) ⟨28074518, by rfl⟩ : syracuseStep 37432691 = 56149037) B56149037
theorem B2338399 : Blo 864565 2338399 := bstep (se 1 (by rfl) ⟨1753799, by rfl⟩ : syracuseStep 2338399 = 3507599) B3507599
theorem B3288671 : Blo 864565 3288671 := bstep (se 1 (by rfl) ⟨2466503, by rfl⟩ : syracuseStep 3288671 = 4933007) B4933007
theorem B1388267 : Blo 864565 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B1945385 : Blo 864565 1945385 := bstep (se 2 (by rfl) ⟨729519, by rfl⟩ : syracuseStep 1945385 = 1459039) B1459039
theorem B2469761 : Blo 864565 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B7417757 : Blo 864565 7417757 := bstep (se 3 (by rfl) ⟨1390829, by rfl⟩ : syracuseStep 7417757 = 2781659) B2781659
theorem B14823485 : Blo 864565 14823485 := bstep (se 3 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 14823485 = 5558807) B5558807
theorem B2339027 : Blo 864565 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B2928851 : Blo 864565 2928851 := bstep (se 1 (by rfl) ⟨2196638, by rfl⟩ : syracuseStep 2928851 = 4393277) B4393277
theorem B9351425 : Blo 864565 9351425 := bstep (se 2 (by rfl) ⟨3506784, by rfl⟩ : syracuseStep 9351425 = 7013569) B7013569
theorem B864603 : Blo 864565 864603 := bstep (se 1 (by rfl) ⟨648452, by rfl⟩ : syracuseStep 864603 = 1296905) B1296905
theorem B2961755 : Blo 864565 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B864623 : Blo 864565 864623 := bstep (se 1 (by rfl) ⟨648467, by rfl⟩ : syracuseStep 864623 = 1296935) B1296935
theorem B864679 : Blo 864565 864679 := bstep (se 1 (by rfl) ⟨648509, by rfl⟩ : syracuseStep 864679 = 1297019) B1297019
theorem B2929121 : Blo 864565 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B864763 : Blo 864565 864763 := bstep (se 1 (by rfl) ⟨648572, by rfl⟩ : syracuseStep 864763 = 1297145) B1297145
theorem B864831 : Blo 864565 864831 := bstep (se 1 (by rfl) ⟨648623, by rfl⟩ : syracuseStep 864831 = 1297247) B1297247
theorem B864839 : Blo 864565 864839 := bstep (se 1 (by rfl) ⟨648629, by rfl⟩ : syracuseStep 864839 = 1297259) B1297259
theorem B1094239 : Blo 864565 1094239 := bstep (se 1 (by rfl) ⟨820679, by rfl⟩ : syracuseStep 1094239 = 1641359) B1641359
theorem B2470571 : Blo 864565 2470571 := bstep (se 1 (by rfl) ⟨1852928, by rfl⟩ : syracuseStep 2470571 = 3705857) B3705857
theorem B1979063 : Blo 864565 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B864991 : Blo 864565 864991 := bstep (se 1 (by rfl) ⟨648743, by rfl⟩ : syracuseStep 864991 = 1297487) B1297487
theorem B865071 : Blo 864565 865071 := bstep (se 1 (by rfl) ⟨648803, by rfl⟩ : syracuseStep 865071 = 1297607) B1297607
theorem B1946447 : Blo 864565 1946447 := bstep (se 1 (by rfl) ⟨1459835, by rfl⟩ : syracuseStep 1946447 = 2919671) B2919671
theorem B2339663 : Blo 864565 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B865179 : Blo 864565 865179 := bstep (se 1 (by rfl) ⟨648884, by rfl⟩ : syracuseStep 865179 = 1297769) B1297769
theorem B865231 : Blo 864565 865231 := bstep (se 1 (by rfl) ⟨648923, by rfl⟩ : syracuseStep 865231 = 1297847) B1297847
theorem B865255 : Blo 864565 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B1946663 : Blo 864565 1946663 := bstep (se 1 (by rfl) ⟨1459997, by rfl⟩ : syracuseStep 1946663 = 2919995) B2919995
theorem B3290327 : Blo 864565 3290327 := bstep (se 1 (by rfl) ⟨2467745, by rfl⟩ : syracuseStep 3290327 = 4935491) B4935491
theorem B1946843 : Blo 864565 1946843 := bstep (se 1 (by rfl) ⟨1460132, by rfl⟩ : syracuseStep 1946843 = 2920265) B2920265
theorem B865567 : Blo 864565 865567 := bstep (se 1 (by rfl) ⟨649175, by rfl⟩ : syracuseStep 865567 = 1298351) B1298351
theorem B865627 : Blo 864565 865627 := bstep (se 1 (by rfl) ⟨649220, by rfl⟩ : syracuseStep 865627 = 1298441) B1298441
theorem B2340193 : Blo 864565 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B865647 : Blo 864565 865647 := bstep (se 1 (by rfl) ⟨649235, by rfl⟩ : syracuseStep 865647 = 1298471) B1298471
theorem B1947041 : Blo 864565 1947041 := bstep (se 2 (by rfl) ⟨730140, by rfl⟩ : syracuseStep 1947041 = 1460281) B1460281
theorem B865703 : Blo 864565 865703 := bstep (se 1 (by rfl) ⟨649277, by rfl⟩ : syracuseStep 865703 = 1298555) B1298555
theorem B865787 : Blo 864565 865787 := bstep (se 1 (by rfl) ⟨649340, by rfl⟩ : syracuseStep 865787 = 1298681) B1298681
theorem B32486923 : Blo 864565 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B2340409 : Blo 864565 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B865855 : Blo 864565 865855 := bstep (se 1 (by rfl) ⟨649391, by rfl⟩ : syracuseStep 865855 = 1298783) B1298783
theorem B865863 : Blo 864565 865863 := bstep (se 1 (by rfl) ⟨649397, by rfl⟩ : syracuseStep 865863 = 1298795) B1298795
theorem B2930363 : Blo 864565 2930363 := bstep (se 1 (by rfl) ⟨2197772, by rfl⟩ : syracuseStep 2930363 = 4395545) B4395545
theorem B866015 : Blo 864565 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B866095 : Blo 864565 866095 := bstep (se 1 (by rfl) ⟨649571, by rfl⟩ : syracuseStep 866095 = 1299143) B1299143
theorem B866203 : Blo 864565 866203 := bstep (se 1 (by rfl) ⟨649652, by rfl⟩ : syracuseStep 866203 = 1299305) B1299305
theorem B1947599 : Blo 864565 1947599 := bstep (se 1 (by rfl) ⟨1460699, by rfl⟩ : syracuseStep 1947599 = 2921399) B2921399
theorem B866255 : Blo 864565 866255 := bstep (se 1 (by rfl) ⟨649691, by rfl⟩ : syracuseStep 866255 = 1299383) B1299383
theorem B866279 : Blo 864565 866279 := bstep (se 1 (by rfl) ⟨649709, by rfl⟩ : syracuseStep 866279 = 1299419) B1299419
theorem B866591 : Blo 864565 866591 := bstep (se 1 (by rfl) ⟨649943, by rfl⟩ : syracuseStep 866591 = 1299887) B1299887
theorem B1947977 : Blo 864565 1947977 := bstep (se 2 (by rfl) ⟨730491, by rfl⟩ : syracuseStep 1947977 = 1460983) B1460983
theorem B1947995 : Blo 864565 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B866651 : Blo 864565 866651 := bstep (se 1 (by rfl) ⟨649988, by rfl⟩ : syracuseStep 866651 = 1299977) B1299977
theorem B866671 : Blo 864565 866671 := bstep (se 1 (by rfl) ⟨650003, by rfl⟩ : syracuseStep 866671 = 1300007) B1300007
theorem B866727 : Blo 864565 866727 := bstep (se 1 (by rfl) ⟨650045, by rfl⟩ : syracuseStep 866727 = 1300091) B1300091
theorem B866811 : Blo 864565 866811 := bstep (se 1 (by rfl) ⟨650108, by rfl⟩ : syracuseStep 866811 = 1300217) B1300217
theorem B1391099 : Blo 864565 1391099 := bstep (se 1 (by rfl) ⟨1043324, by rfl⟩ : syracuseStep 1391099 = 2086649) B2086649
theorem B866879 : Blo 864565 866879 := bstep (se 1 (by rfl) ⟨650159, by rfl⟩ : syracuseStep 866879 = 1300319) B1300319
theorem B866887 : Blo 864565 866887 := bstep (se 1 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 866887 = 1300331) B1300331
theorem B12499595 : Blo 864565 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B867039 : Blo 864565 867039 := bstep (se 1 (by rfl) ⟨650279, by rfl⟩ : syracuseStep 867039 = 1300559) B1300559
theorem B2079479 : Blo 864565 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B867119 : Blo 864565 867119 := bstep (se 1 (by rfl) ⟨650339, by rfl⟩ : syracuseStep 867119 = 1300679) B1300679
theorem B1948571 : Blo 864565 1948571 := bstep (se 1 (by rfl) ⟨1461428, by rfl⟩ : syracuseStep 1948571 = 2922857) B2922857
theorem B867227 : Blo 864565 867227 := bstep (se 1 (by rfl) ⟨650420, by rfl⟩ : syracuseStep 867227 = 1300841) B1300841
theorem B2472859 : Blo 864565 2472859 := bstep (se 1 (by rfl) ⟨1854644, by rfl⟩ : syracuseStep 2472859 = 3709289) B3709289
theorem B867279 : Blo 864565 867279 := bstep (se 1 (by rfl) ⟨650459, by rfl⟩ : syracuseStep 867279 = 1300919) B1300919
theorem B1096679 : Blo 864565 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B867303 : Blo 864565 867303 := bstep (se 1 (by rfl) ⟨650477, by rfl⟩ : syracuseStep 867303 = 1300955) B1300955
theorem B1948769 : Blo 864565 1948769 := bstep (se 2 (by rfl) ⟨730788, by rfl⟩ : syracuseStep 1948769 = 1461577) B1461577
theorem B7519499 : Blo 864565 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B867615 : Blo 864565 867615 := bstep (se 1 (by rfl) ⟨650711, by rfl⟩ : syracuseStep 867615 = 1301423) B1301423
theorem B2473247 : Blo 864565 2473247 := bstep (se 1 (by rfl) ⟨1854935, by rfl⟩ : syracuseStep 2473247 = 3709871) B3709871
theorem B1948967 : Blo 864565 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B867675 : Blo 864565 867675 := bstep (se 1 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 867675 = 1301513) B1301513
theorem B867695 : Blo 864565 867695 := bstep (se 1 (by rfl) ⟨650771, by rfl⟩ : syracuseStep 867695 = 1301543) B1301543
theorem B867751 : Blo 864565 867751 := bstep (se 1 (by rfl) ⟨650813, by rfl⟩ : syracuseStep 867751 = 1301627) B1301627
theorem B867835 : Blo 864565 867835 := bstep (se 1 (by rfl) ⟨650876, by rfl⟩ : syracuseStep 867835 = 1301753) B1301753
theorem B867903 : Blo 864565 867903 := bstep (se 1 (by rfl) ⟨650927, by rfl⟩ : syracuseStep 867903 = 1301855) B1301855
theorem B867911 : Blo 864565 867911 := bstep (se 1 (by rfl) ⟨650933, by rfl⟩ : syracuseStep 867911 = 1301867) B1301867
theorem B1949345 : Blo 864565 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B868063 : Blo 864565 868063 := bstep (se 1 (by rfl) ⟨651047, by rfl⟩ : syracuseStep 868063 = 1302095) B1302095
theorem B868143 : Blo 864565 868143 := bstep (se 1 (by rfl) ⟨651107, by rfl⟩ : syracuseStep 868143 = 1302215) B1302215
theorem B868251 : Blo 864565 868251 := bstep (se 1 (by rfl) ⟨651188, by rfl⟩ : syracuseStep 868251 = 1302377) B1302377
theorem B868303 : Blo 864565 868303 := bstep (se 1 (by rfl) ⟨651227, by rfl⟩ : syracuseStep 868303 = 1302455) B1302455
theorem B868327 : Blo 864565 868327 := bstep (se 1 (by rfl) ⟨651245, by rfl⟩ : syracuseStep 868327 = 1302491) B1302491
theorem B1949705 : Blo 864565 1949705 := bstep (se 2 (by rfl) ⟨731139, by rfl⟩ : syracuseStep 1949705 = 1462279) B1462279
theorem B3293243 : Blo 864565 3293243 := bstep (se 1 (by rfl) ⟨2469932, by rfl⟩ : syracuseStep 3293243 = 4939865) B4939865
theorem B3293531 : Blo 864565 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B1950119 : Blo 864565 1950119 := bstep (se 1 (by rfl) ⟨1462589, by rfl⟩ : syracuseStep 1950119 = 2925179) B2925179
theorem B1950227 : Blo 864565 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B1950281 : Blo 864565 1950281 := bstep (se 2 (by rfl) ⟨731355, by rfl⟩ : syracuseStep 1950281 = 1462711) B1462711
theorem B32424583 : Blo 864565 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B2671327 : Blo 864565 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B2081555 : Blo 864565 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B1950695 : Blo 864565 1950695 := bstep (se 1 (by rfl) ⟨1463021, by rfl⟩ : syracuseStep 1950695 = 2926043) B2926043
theorem B1459343 : Blo 864565 1459343 := bstep (se 1 (by rfl) ⟨1094507, by rfl⟩ : syracuseStep 1459343 = 2189015) B2189015
theorem B1754399 : Blo 864565 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B9356579 : Blo 864565 9356579 := bstep (se 1 (by rfl) ⟨7017434, by rfl⟩ : syracuseStep 9356579 = 14034869) B14034869
theorem B3294503 : Blo 864565 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B1099099 : Blo 864565 1099099 := bstep (se 1 (by rfl) ⟨824324, by rfl⟩ : syracuseStep 1099099 = 1648649) B1648649
theorem B4441439 : Blo 864565 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B1951073 : Blo 864565 1951073 := bstep (se 2 (by rfl) ⟨731652, by rfl⟩ : syracuseStep 1951073 = 1463305) B1463305
theorem B1459579 : Blo 864565 1459579 := bstep (se 1 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 1459579 = 2189369) B2189369
theorem B1951163 : Blo 864565 1951163 := bstep (se 1 (by rfl) ⟨1463372, by rfl⟩ : syracuseStep 1951163 = 2926745) B2926745
theorem B1951289 : Blo 864565 1951289 := bstep (se 2 (by rfl) ⟨731733, by rfl⟩ : syracuseStep 1951289 = 1463467) B1463467
theorem B8800067 : Blo 864565 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B2770895 : Blo 864565 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B1951955 : Blo 864565 1951955 := bstep (se 1 (by rfl) ⟨1463966, by rfl⟩ : syracuseStep 1951955 = 2927933) B2927933
theorem B1952009 : Blo 864565 1952009 := bstep (se 2 (by rfl) ⟨732003, by rfl⟩ : syracuseStep 1952009 = 1464007) B1464007
theorem B1853705 : Blo 864565 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B5261735 : Blo 864565 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1952225 : Blo 864565 1952225 := bstep (se 2 (by rfl) ⟨732084, by rfl⟩ : syracuseStep 1952225 = 1464169) B1464169
theorem B5917157 : Blo 864565 5917157 := bstep (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) B1109467
theorem B1296959 : Blo 864565 1296959 := bstep (se 1 (by rfl) ⟨972719, by rfl⟩ : syracuseStep 1296959 = 1945439) B1945439
theorem B1297079 : Blo 864565 1297079 := bstep (se 1 (by rfl) ⟨972809, by rfl⟩ : syracuseStep 1297079 = 1945619) B1945619
theorem B3295991 : Blo 864565 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B1952531 : Blo 864565 1952531 := bstep (se 1 (by rfl) ⟨1464398, by rfl⟩ : syracuseStep 1952531 = 2928797) B2928797
theorem B1854227 : Blo 864565 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B1461071 : Blo 864565 1461071 := bstep (se 1 (by rfl) ⟨1095803, by rfl⟩ : syracuseStep 1461071 = 2191607) B2191607
theorem B1297307 : Blo 864565 1297307 := bstep (se 1 (by rfl) ⟨972980, by rfl⟩ : syracuseStep 1297307 = 1945961) B1945961
theorem B1952891 : Blo 864565 1952891 := bstep (se 1 (by rfl) ⟨1464668, by rfl⟩ : syracuseStep 1952891 = 2929337) B2929337
theorem B1953017 : Blo 864565 1953017 := bstep (se 2 (by rfl) ⟨732381, by rfl⟩ : syracuseStep 1953017 = 1464763) B1464763
theorem B1854713 : Blo 864565 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B4377887 : Blo 864565 4377887 := bstep (se 1 (by rfl) ⟨3283415, by rfl⟩ : syracuseStep 4377887 = 6566831) B6566831
theorem B1297703 : Blo 864565 1297703 := bstep (se 1 (by rfl) ⟨973277, by rfl⟩ : syracuseStep 1297703 = 1946555) B1946555
theorem B1297787 : Blo 864565 1297787 := bstep (se 1 (by rfl) ⟨973340, by rfl⟩ : syracuseStep 1297787 = 1946681) B1946681
theorem B1953161 : Blo 864565 1953161 := bstep (se 2 (by rfl) ⟨732435, by rfl⟩ : syracuseStep 1953161 = 1464871) B1464871
theorem B1297913 : Blo 864565 1297913 := bstep (se 2 (by rfl) ⟨486717, by rfl⟩ : syracuseStep 1297913 = 973435) B973435
theorem B1953287 : Blo 864565 1953287 := bstep (se 1 (by rfl) ⟨1464965, by rfl⟩ : syracuseStep 1953287 = 2929931) B2929931
theorem B1298015 : Blo 864565 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B1953467 : Blo 864565 1953467 := bstep (se 1 (by rfl) ⟨1465100, by rfl⟩ : syracuseStep 1953467 = 2930201) B2930201
theorem B5918417 : Blo 864565 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B1462063 : Blo 864565 1462063 := bstep (se 1 (by rfl) ⟨1096547, by rfl⟩ : syracuseStep 1462063 = 2193095) B2193095
theorem B1298231 : Blo 864565 1298231 := bstep (se 1 (by rfl) ⟨973673, by rfl⟩ : syracuseStep 1298231 = 1947347) B1947347
theorem B1953593 : Blo 864565 1953593 := bstep (se 2 (by rfl) ⟨732597, by rfl⟩ : syracuseStep 1953593 = 1465195) B1465195
theorem B1298537 : Blo 864565 1298537 := bstep (se 2 (by rfl) ⟨486951, by rfl⟩ : syracuseStep 1298537 = 973903) B973903
theorem B3166571 : Blo 864565 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1233263 : Blo 864565 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1298855 : Blo 864565 1298855 := bstep (se 1 (by rfl) ⟨974141, by rfl⟩ : syracuseStep 1298855 = 1948283) B1948283
theorem B1954223 : Blo 864565 1954223 := bstep (se 1 (by rfl) ⟨1465667, by rfl⟩ : syracuseStep 1954223 = 2931335) B2931335
theorem B1954259 : Blo 864565 1954259 := bstep (se 1 (by rfl) ⟨1465694, by rfl⟩ : syracuseStep 1954259 = 2931389) B2931389
theorem B1298939 : Blo 864565 1298939 := bstep (se 1 (by rfl) ⟨974204, by rfl⟩ : syracuseStep 1298939 = 1948409) B1948409
theorem B3002881 : Blo 864565 3002881 := bstep (se 2 (by rfl) ⟨1126080, by rfl⟩ : syracuseStep 3002881 = 2252161) B2252161
theorem B1299065 : Blo 864565 1299065 := bstep (se 2 (by rfl) ⟨487149, by rfl⟩ : syracuseStep 1299065 = 974299) B974299
theorem B1299119 : Blo 864565 1299119 := bstep (se 1 (by rfl) ⟨974339, by rfl⟩ : syracuseStep 1299119 = 1948679) B1948679
theorem B1299167 : Blo 864565 1299167 := bstep (se 1 (by rfl) ⟨974375, by rfl⟩ : syracuseStep 1299167 = 1948751) B1948751
theorem B4215545 : Blo 864565 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B8901485 : Blo 864565 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B1299431 : Blo 864565 1299431 := bstep (se 1 (by rfl) ⟨974573, by rfl⟩ : syracuseStep 1299431 = 1949147) B1949147
theorem B2675837 : Blo 864565 2675837 := bstep (se 3 (by rfl) ⟨501719, by rfl⟩ : syracuseStep 2675837 = 1003439) B1003439
theorem B1299689 : Blo 864565 1299689 := bstep (se 2 (by rfl) ⟨487383, by rfl⟩ : syracuseStep 1299689 = 974767) B974767
theorem B5002489 : Blo 864565 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B1299743 : Blo 864565 1299743 := bstep (se 1 (by rfl) ⟨974807, by rfl⟩ : syracuseStep 1299743 = 1949615) B1949615
theorem B3331451 : Blo 864565 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B1299911 : Blo 864565 1299911 := bstep (se 1 (by rfl) ⟨974933, by rfl⟩ : syracuseStep 1299911 = 1949867) B1949867
theorem B4380317 : Blo 864565 4380317 := bstep (se 3 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 4380317 = 1642619) B1642619
theorem B12474101 : Blo 864565 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B1300265 : Blo 864565 1300265 := bstep (se 2 (by rfl) ⟨487599, by rfl⟩ : syracuseStep 1300265 = 975199) B975199
theorem B1300271 : Blo 864565 1300271 := bstep (se 1 (by rfl) ⟨975203, by rfl⟩ : syracuseStep 1300271 = 1950407) B1950407
theorem B972751 : Blo 864565 972751 := bstep (se 1 (by rfl) ⟨729563, by rfl⟩ : syracuseStep 972751 = 1459127) B1459127
theorem B2775293 : Blo 864565 2775293 := bstep (se 3 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 2775293 = 1040735) B1040735
theorem B1300745 : Blo 864565 1300745 := bstep (se 2 (by rfl) ⟨487779, by rfl⟩ : syracuseStep 1300745 = 975559) B975559
theorem B973147 : Blo 864565 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B1300847 : Blo 864565 1300847 := bstep (se 1 (by rfl) ⟨975635, by rfl⟩ : syracuseStep 1300847 = 1951271) B1951271
theorem B1464743 : Blo 864565 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B973255 : Blo 864565 973255 := bstep (se 1 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 973255 = 1459883) B1459883
theorem B1301063 : Blo 864565 1301063 := bstep (se 1 (by rfl) ⟨975797, by rfl⟩ : syracuseStep 1301063 = 1951595) B1951595
theorem B1464905 : Blo 864565 1464905 := bstep (se 2 (by rfl) ⟨549339, by rfl⟩ : syracuseStep 1464905 = 1098679) B1098679
theorem B1301099 : Blo 864565 1301099 := bstep (se 1 (by rfl) ⟨975824, by rfl⟩ : syracuseStep 1301099 = 1951649) B1951649
theorem B1563257 : Blo 864565 1563257 := bstep (se 2 (by rfl) ⟨586221, by rfl⟩ : syracuseStep 1563257 = 1172443) B1172443
theorem B18766511 : Blo 864565 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B973615 : Blo 864565 973615 := bstep (se 1 (by rfl) ⟨730211, by rfl⟩ : syracuseStep 973615 = 1460423) B1460423
theorem B1301327 : Blo 864565 1301327 := bstep (se 1 (by rfl) ⟨975995, by rfl⟩ : syracuseStep 1301327 = 1951991) B1951991
theorem B973723 : Blo 864565 973723 := bstep (se 1 (by rfl) ⟨730292, by rfl⟩ : syracuseStep 973723 = 1460585) B1460585
theorem B4381613 : Blo 864565 4381613 := bstep (se 3 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 4381613 = 1643105) B1643105
theorem B3955643 : Blo 864565 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B3693707 : Blo 864565 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B1301723 : Blo 864565 1301723 := bstep (se 1 (by rfl) ⟨976292, by rfl⟩ : syracuseStep 1301723 = 1952585) B1952585
theorem B974119 : Blo 864565 974119 := bstep (se 1 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 974119 = 1461179) B1461179
theorem B974191 : Blo 864565 974191 := bstep (se 1 (by rfl) ⟨730643, by rfl⟩ : syracuseStep 974191 = 1461287) B1461287
theorem B2776457 : Blo 864565 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B1301897 : Blo 864565 1301897 := bstep (se 2 (by rfl) ⟨488211, by rfl⟩ : syracuseStep 1301897 = 976423) B976423
theorem B974407 : Blo 864565 974407 := bstep (se 1 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 974407 = 1461611) B1461611
theorem B1302251 : Blo 864565 1302251 := bstep (se 1 (by rfl) ⟨976688, by rfl⟩ : syracuseStep 1302251 = 1953377) B1953377
theorem B18013985 : Blo 864565 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B4448047 : Blo 864565 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B3694511 : Blo 864565 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B15392693 : Blo 864565 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B1302479 : Blo 864565 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B1171675 : Blo 864565 1171675 := bstep (se 1 (by rfl) ⟨878756, by rfl⟩ : syracuseStep 1171675 = 1757513) B1757513
theorem B1171751 : Blo 864565 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B975271 : Blo 864565 975271 := bstep (se 1 (by rfl) ⟨731453, by rfl⟩ : syracuseStep 975271 = 1462907) B1462907
theorem B4383233 : Blo 864565 4383233 := bstep (se 2 (by rfl) ⟨1643712, by rfl⟩ : syracuseStep 4383233 = 3287425) B3287425
theorem B2777753 : Blo 864565 2777753 := bstep (se 2 (by rfl) ⟨1041657, by rfl⟩ : syracuseStep 2777753 = 2083315) B2083315
theorem B4383719 : Blo 864565 4383719 := bstep (se 1 (by rfl) ⟨3287789, by rfl⟩ : syracuseStep 4383719 = 6575579) B6575579
theorem B975847 : Blo 864565 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B15819947 : Blo 864565 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B4384043 : Blo 864565 4384043 := bstep (se 1 (by rfl) ⟨3288032, by rfl⟩ : syracuseStep 4384043 = 6576065) B6576065
theorem B7923257 : Blo 864565 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B2188883 : Blo 864565 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B878383 : Blo 864565 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B9889613 : Blo 864565 9889613 := bstep (se 3 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 9889613 = 3708605) B3708605
theorem B3565417 : Blo 864565 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B4385015 : Blo 864565 4385015 := bstep (se 1 (by rfl) ⟨3288761, by rfl⟩ : syracuseStep 4385015 = 6577523) B6577523
theorem B6252967 : Blo 864565 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B2779559 : Blo 864565 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B6580925 : Blo 864565 6580925 := bstep (se 3 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 6580925 = 2467847) B2467847
theorem B4385501 : Blo 864565 4385501 := bstep (se 3 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 4385501 = 1644563) B1644563
theorem B2190311 : Blo 864565 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B2191009 : Blo 864565 2191009 := bstep (se 2 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 2191009 = 1643257) B1643257
theorem B2191151 : Blo 864565 2191151 := bstep (se 1 (by rfl) ⟨1643363, by rfl⟩ : syracuseStep 2191151 = 3286727) B3286727
theorem B3862379 : Blo 864565 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B2224559 : Blo 864565 2224559 := bstep (se 1 (by rfl) ⟨1668419, by rfl⟩ : syracuseStep 2224559 = 3336839) B3336839
theorem B2191799 : Blo 864565 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B2257403 : Blo 864565 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B2815175 : Blo 864565 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B2192903 : Blo 864565 2192903 := bstep (se 1 (by rfl) ⟨1644677, by rfl⟩ : syracuseStep 2192903 = 3289355) B3289355
theorem B4945445 : Blo 864565 4945445 := bstep (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) B927271
theorem B2192953 : Blo 864565 2192953 := bstep (se 2 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 2192953 = 1644715) B1644715
theorem B2258695 : Blo 864565 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B2193257 : Blo 864565 2193257 := bstep (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) B1644943
theorem B3340655 : Blo 864565 3340655 := bstep (se 1 (by rfl) ⟨2505491, by rfl⟩ : syracuseStep 3340655 = 5010983) B5010983
theorem B2193875 : Blo 864565 2193875 := bstep (se 1 (by rfl) ⟨1645406, by rfl⟩ : syracuseStep 2193875 = 3290813) B3290813
theorem B4389551 : Blo 864565 4389551 := bstep (se 1 (by rfl) ⟨3292163, by rfl⟩ : syracuseStep 4389551 = 6584327) B6584327
theorem B35585011 : Blo 864565 35585011 := bstep (se 1 (by rfl) ⟨26688758, by rfl⟩ : syracuseStep 35585011 = 53377517) B53377517
theorem B4389875 : Blo 864565 4389875 := bstep (se 1 (by rfl) ⟨3292406, by rfl⟩ : syracuseStep 4389875 = 6584813) B6584813
theorem B1604827 : Blo 864565 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B5078609 : Blo 864565 5078609 := bstep (se 2 (by rfl) ⟨1904478, by rfl⟩ : syracuseStep 5078609 = 3808957) B3808957
theorem B2195039 : Blo 864565 2195039 := bstep (se 1 (by rfl) ⟨1646279, by rfl⟩ : syracuseStep 2195039 = 3292559) B3292559
theorem B2195495 : Blo 864565 2195495 := bstep (se 1 (by rfl) ⟨1646621, by rfl⟩ : syracuseStep 2195495 = 3293243) B3293243
theorem B3997927 : Blo 864565 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B2195687 : Blo 864565 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B2196335 : Blo 864565 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B63374339 : Blo 864565 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B5866711 : Blo 864565 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B4392467 : Blo 864565 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B3507823 : Blo 864565 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B2197327 : Blo 864565 2197327 := bstep (se 1 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 2197327 = 3295991) B3295991
theorem B2918591 : Blo 864565 2918591 := bstep (se 1 (by rfl) ⟨2188943, by rfl⟩ : syracuseStep 2918591 = 4377887) B4377887
theorem B4753889 : Blo 864565 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B5934323 : Blo 864565 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B2920211 : Blo 864565 2920211 := bstep (se 1 (by rfl) ⟨2190158, by rfl⟩ : syracuseStep 2920211 = 4380317) B4380317
theorem B36049211 : Blo 864565 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B2921075 : Blo 864565 2921075 := bstep (se 1 (by rfl) ⟨2190806, by rfl⟩ : syracuseStep 2921075 = 4381613) B4381613
theorem B33264269 : Blo 864565 33264269 := bstep (se 3 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 33264269 = 12474101) B12474101
theorem B2462471 : Blo 864565 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B3117865 : Blo 864565 3117865 := bstep (se 2 (by rfl) ⟨1169199, by rfl⟩ : syracuseStep 3117865 = 2338399) B2338399
theorem B2921345 : Blo 864565 2921345 := bstep (se 2 (by rfl) ⟨1095504, by rfl⟩ : syracuseStep 2921345 = 2191009) B2191009
theorem B2463007 : Blo 864565 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B2922155 : Blo 864565 2922155 := bstep (se 1 (by rfl) ⟨2191616, by rfl⟩ : syracuseStep 2922155 = 4383233) B4383233
theorem B2922479 : Blo 864565 2922479 := bstep (se 1 (by rfl) ⟨2191859, by rfl⟩ : syracuseStep 2922479 = 4383719) B4383719
theorem B4003841 : Blo 864565 4003841 := bstep (se 2 (by rfl) ⟨1501440, by rfl⟩ : syracuseStep 4003841 = 3002881) B3002881
theorem B2922695 : Blo 864565 2922695 := bstep (se 1 (by rfl) ⟨2192021, by rfl⟩ : syracuseStep 2922695 = 4384043) B4384043
theorem B1972487 : Blo 864565 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B5282171 : Blo 864565 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B6593075 : Blo 864565 6593075 := bstep (se 1 (by rfl) ⟨4944806, by rfl⟩ : syracuseStep 6593075 = 9889613) B9889613
theorem B3709597 : Blo 864565 3709597 := bstep (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) B1391099
theorem B2923343 : Blo 864565 2923343 := bstep (se 1 (by rfl) ⟨2192507, by rfl⟩ : syracuseStep 2923343 = 4385015) B4385015
theorem B4168685 : Blo 864565 4168685 := bstep (se 3 (by rfl) ⟨781628, by rfl⟩ : syracuseStep 4168685 = 1563257) B1563257
theorem B3120257 : Blo 864565 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B2923667 : Blo 864565 2923667 := bstep (se 1 (by rfl) ⟨2192750, by rfl⟩ : syracuseStep 2923667 = 4385501) B4385501
theorem B3120545 : Blo 864565 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2923937 : Blo 864565 2923937 := bstep (se 2 (by rfl) ⟨1096476, by rfl⟩ : syracuseStep 2923937 = 2192953) B2192953
theorem B1645991 : Blo 864565 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1973735 : Blo 864565 1973735 := bstep (se 1 (by rfl) ⟨1480301, by rfl⟩ : syracuseStep 1973735 = 2960603) B2960603
theorem B925511 : Blo 864565 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B1646507 : Blo 864565 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B44965813 : Blo 864565 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B2924477 : Blo 864565 2924477 := bstep (se 3 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 2924477 = 1096679) B1096679
theorem B6234283 : Blo 864565 6234283 := bstep (se 1 (by rfl) ⟨4675712, by rfl⟩ : syracuseStep 6234283 = 9351425) B9351425
theorem B1974503 : Blo 864565 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B1483039 : Blo 864565 1483039 := bstep (se 1 (by rfl) ⟨1112279, by rfl⟩ : syracuseStep 1483039 = 2224559) B2224559
theorem B1647047 : Blo 864565 1647047 := bstep (se 1 (by rfl) ⟨1235285, by rfl⟩ : syracuseStep 1647047 = 2470571) B2470571
theorem B1319375 : Blo 864565 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B3285481 : Blo 864565 3285481 := bstep (se 2 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 3285481 = 2464111) B2464111
theorem B1876783 : Blo 864565 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B2139769 : Blo 864565 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B8333063 : Blo 864565 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B2926367 : Blo 864565 2926367 := bstep (se 1 (by rfl) ⟨2194775, by rfl⟩ : syracuseStep 2926367 = 4389551) B4389551
theorem B1386319 : Blo 864565 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B2926583 : Blo 864565 2926583 := bstep (se 1 (by rfl) ⟨2194937, by rfl⟩ : syracuseStep 2926583 = 4389875) B4389875
theorem B1648831 : Blo 864565 1648831 := bstep (se 1 (by rfl) ⟨1236623, by rfl⟩ : syracuseStep 1648831 = 2473247) B2473247
theorem B3385739 : Blo 864565 3385739 := bstep (se 1 (by rfl) ⟨2539304, by rfl⟩ : syracuseStep 3385739 = 5078609) B5078609
theorem B2927447 : Blo 864565 2927447 := bstep (se 1 (by rfl) ⟨2195585, by rfl⟩ : syracuseStep 2927447 = 4391171) B4391171
theorem B2468839 : Blo 864565 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B2927663 : Blo 864565 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B3288185 : Blo 864565 3288185 := bstep (se 2 (by rfl) ⟨1233069, by rfl⟩ : syracuseStep 3288185 = 2466139) B2466139
theorem B1387703 : Blo 864565 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B3124523 : Blo 864565 3124523 := bstep (se 1 (by rfl) ⟨2343392, by rfl⟩ : syracuseStep 3124523 = 4686785) B4686785
theorem B2928041 : Blo 864565 2928041 := bstep (se 2 (by rfl) ⟨1098015, by rfl⟩ : syracuseStep 2928041 = 2196031) B2196031
theorem B3124669 : Blo 864565 3124669 := bstep (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) B1171751
theorem B43232777 : Blo 864565 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B6237719 : Blo 864565 6237719 := bstep (se 1 (by rfl) ⟨4678289, by rfl⟩ : syracuseStep 6237719 = 9356579) B9356579
theorem B23703101 : Blo 864565 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B2960959 : Blo 864565 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B3288701 : Blo 864565 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B1847161 : Blo 864565 1847161 := bstep (se 2 (by rfl) ⟨692685, by rfl⟩ : syracuseStep 1847161 = 1385371) B1385371
theorem B2928527 : Blo 864565 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B2928905 : Blo 864565 2928905 := bstep (se 2 (by rfl) ⟨1098339, by rfl⟩ : syracuseStep 2928905 = 2196679) B2196679
theorem B3944771 : Blo 864565 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B864639 : Blo 864565 864639 := bstep (se 1 (by rfl) ⟨648479, by rfl⟩ : syracuseStep 864639 = 1296959) B1296959
theorem B6566345 : Blo 864565 6566345 := bstep (se 2 (by rfl) ⟨2462379, by rfl⟩ : syracuseStep 6566345 = 4924759) B4924759
theorem B864719 : Blo 864565 864719 := bstep (se 1 (by rfl) ⟨648539, by rfl⟩ : syracuseStep 864719 = 1297079) B1297079
theorem B1946105 : Blo 864565 1946105 := bstep (se 2 (by rfl) ⟨729789, by rfl⟩ : syracuseStep 1946105 = 1459579) B1459579
theorem B1946195 : Blo 864565 1946195 := bstep (se 1 (by rfl) ⟨1459646, by rfl⟩ : syracuseStep 1946195 = 2919293) B2919293
theorem B864871 : Blo 864565 864871 := bstep (se 1 (by rfl) ⟨648653, by rfl⟩ : syracuseStep 864871 = 1297307) B1297307
theorem B1946375 : Blo 864565 1946375 := bstep (se 1 (by rfl) ⟨1459781, by rfl⟩ : syracuseStep 1946375 = 2919563) B2919563
theorem B3126023 : Blo 864565 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B865135 : Blo 864565 865135 := bstep (se 1 (by rfl) ⟨648851, by rfl⟩ : syracuseStep 865135 = 1297703) B1297703
theorem B6239101 : Blo 864565 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B865191 : Blo 864565 865191 := bstep (se 1 (by rfl) ⟨648893, by rfl⟩ : syracuseStep 865191 = 1297787) B1297787
theorem B15774695 : Blo 864565 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B865275 : Blo 864565 865275 := bstep (se 1 (by rfl) ⟨648956, by rfl⟩ : syracuseStep 865275 = 1297913) B1297913
theorem B2634761 : Blo 864565 2634761 := bstep (se 2 (by rfl) ⟨988035, by rfl⟩ : syracuseStep 2634761 = 1976071) B1976071
theorem B865343 : Blo 864565 865343 := bstep (se 1 (by rfl) ⟨649007, by rfl⟩ : syracuseStep 865343 = 1298015) B1298015
theorem B3945611 : Blo 864565 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B865487 : Blo 864565 865487 := bstep (se 1 (by rfl) ⟨649115, by rfl⟩ : syracuseStep 865487 = 1298231) B1298231
theorem B2930039 : Blo 864565 2930039 := bstep (se 1 (by rfl) ⟨2197529, by rfl⟩ : syracuseStep 2930039 = 4395059) B4395059
theorem B865691 : Blo 864565 865691 := bstep (se 1 (by rfl) ⟨649268, by rfl⟩ : syracuseStep 865691 = 1298537) B1298537
theorem B865903 : Blo 864565 865903 := bstep (se 1 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 865903 = 1298855) B1298855
theorem B865959 : Blo 864565 865959 := bstep (se 1 (by rfl) ⟨649469, by rfl⟩ : syracuseStep 865959 = 1298939) B1298939
theorem B866043 : Blo 864565 866043 := bstep (se 1 (by rfl) ⟨649532, by rfl⟩ : syracuseStep 866043 = 1299065) B1299065
theorem B866079 : Blo 864565 866079 := bstep (se 1 (by rfl) ⟨649559, by rfl⟩ : syracuseStep 866079 = 1299119) B1299119
theorem B1947455 : Blo 864565 1947455 := bstep (se 1 (by rfl) ⟨1460591, by rfl⟩ : syracuseStep 1947455 = 2921183) B2921183
theorem B866111 : Blo 864565 866111 := bstep (se 1 (by rfl) ⟨649583, by rfl⟩ : syracuseStep 866111 = 1299167) B1299167
theorem B8337289 : Blo 864565 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B866287 : Blo 864565 866287 := bstep (se 1 (by rfl) ⟨649715, by rfl⟩ : syracuseStep 866287 = 1299431) B1299431
theorem B1783891 : Blo 864565 1783891 := bstep (se 1 (by rfl) ⟨1337918, by rfl⟩ : syracuseStep 1783891 = 2675837) B2675837
theorem B1947743 : Blo 864565 1947743 := bstep (se 1 (by rfl) ⟨1460807, by rfl⟩ : syracuseStep 1947743 = 2921615) B2921615
theorem B5552225 : Blo 864565 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B866459 : Blo 864565 866459 := bstep (se 1 (by rfl) ⟨649844, by rfl⟩ : syracuseStep 866459 = 1299689) B1299689
theorem B2930849 : Blo 864565 2930849 := bstep (se 2 (by rfl) ⟨1099068, by rfl⟩ : syracuseStep 2930849 = 2198137) B2198137
theorem B866495 : Blo 864565 866495 := bstep (se 1 (by rfl) ⟨649871, by rfl⟩ : syracuseStep 866495 = 1299743) B1299743
theorem B866607 : Blo 864565 866607 := bstep (se 1 (by rfl) ⟨649955, by rfl⟩ : syracuseStep 866607 = 1299911) B1299911
theorem B2931119 : Blo 864565 2931119 := bstep (se 1 (by rfl) ⟨2198339, by rfl⟩ : syracuseStep 2931119 = 4396679) B4396679
theorem B866843 : Blo 864565 866843 := bstep (se 1 (by rfl) ⟨650132, by rfl⟩ : syracuseStep 866843 = 1300265) B1300265
theorem B866847 : Blo 864565 866847 := bstep (se 1 (by rfl) ⟨650135, by rfl⟩ : syracuseStep 866847 = 1300271) B1300271
theorem B1948499 : Blo 864565 1948499 := bstep (se 1 (by rfl) ⟨1461374, by rfl⟩ : syracuseStep 1948499 = 2922749) B2922749
theorem B1850195 : Blo 864565 1850195 := bstep (se 1 (by rfl) ⟨1387646, by rfl⟩ : syracuseStep 1850195 = 2775293) B2775293
theorem B867163 : Blo 864565 867163 := bstep (se 1 (by rfl) ⟨650372, by rfl⟩ : syracuseStep 867163 = 1300745) B1300745
theorem B867231 : Blo 864565 867231 := bstep (se 1 (by rfl) ⟨650423, by rfl⟩ : syracuseStep 867231 = 1300847) B1300847
theorem B867375 : Blo 864565 867375 := bstep (se 1 (by rfl) ⟨650531, by rfl⟩ : syracuseStep 867375 = 1301063) B1301063
theorem B867399 : Blo 864565 867399 := bstep (se 1 (by rfl) ⟨650549, by rfl⟩ : syracuseStep 867399 = 1301099) B1301099
theorem B2473031 : Blo 864565 2473031 := bstep (se 1 (by rfl) ⟨1854773, by rfl⟩ : syracuseStep 2473031 = 3709547) B3709547
theorem B867551 : Blo 864565 867551 := bstep (se 1 (by rfl) ⟨650663, by rfl⟩ : syracuseStep 867551 = 1301327) B1301327
theorem B2473213 : Blo 864565 2473213 := bstep (se 3 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 2473213 = 927455) B927455
theorem B2637095 : Blo 864565 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B1949039 : Blo 864565 1949039 := bstep (se 1 (by rfl) ⟨1461779, by rfl⟩ : syracuseStep 1949039 = 2923559) B2923559
theorem B867815 : Blo 864565 867815 := bstep (se 1 (by rfl) ⟨650861, by rfl⟩ : syracuseStep 867815 = 1301723) B1301723
theorem B867931 : Blo 864565 867931 := bstep (se 1 (by rfl) ⟨650948, by rfl⟩ : syracuseStep 867931 = 1301897) B1301897
theorem B1949327 : Blo 864565 1949327 := bstep (se 1 (by rfl) ⟨1461995, by rfl⟩ : syracuseStep 1949327 = 2923991) B2923991
theorem B1949417 : Blo 864565 1949417 := bstep (se 2 (by rfl) ⟨731031, by rfl⟩ : syracuseStep 1949417 = 1462063) B1462063
theorem B11124539 : Blo 864565 11124539 := bstep (se 1 (by rfl) ⟨8343404, by rfl⟩ : syracuseStep 11124539 = 16686809) B16686809
theorem B868167 : Blo 864565 868167 := bstep (se 1 (by rfl) ⟨651125, by rfl⟩ : syracuseStep 868167 = 1302251) B1302251
theorem B12009323 : Blo 864565 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B7389053 : Blo 864565 7389053 := bstep (se 3 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 7389053 = 2770895) B2770895
theorem B868319 : Blo 864565 868319 := bstep (se 1 (by rfl) ⟨651239, by rfl⟩ : syracuseStep 868319 = 1302479) B1302479
theorem B1851835 : Blo 864565 1851835 := bstep (se 1 (by rfl) ⟨1388876, by rfl⟩ : syracuseStep 1851835 = 2777753) B2777753
theorem B6668963 : Blo 864565 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B1950443 : Blo 864565 1950443 := bstep (se 1 (by rfl) ⟨1462832, by rfl⟩ : syracuseStep 1950443 = 2925665) B2925665
theorem B1458985 : Blo 864565 1458985 := bstep (se 2 (by rfl) ⟨547119, by rfl⟩ : syracuseStep 1458985 = 1094239) B1094239
theorem B2081747 : Blo 864565 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B1459255 : Blo 864565 1459255 := bstep (se 1 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 1459255 = 2188883) B2188883
theorem B9356705 : Blo 864565 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B1951343 : Blo 864565 1951343 := bstep (se 1 (by rfl) ⟨1463507, by rfl⟩ : syracuseStep 1951343 = 2927015) B2927015
theorem B1853039 : Blo 864565 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B6342259 : Blo 864565 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B6669985 : Blo 864565 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B1951451 : Blo 864565 1951451 := bstep (se 1 (by rfl) ⟨1463588, by rfl⟩ : syracuseStep 1951451 = 2927177) B2927177
theorem B1460207 : Blo 864565 1460207 := bstep (se 1 (by rfl) ⟨1095155, by rfl⟩ : syracuseStep 1460207 = 2190311) B2190311
theorem B24955127 : Blo 864565 24955127 := bstep (se 1 (by rfl) ⟨18716345, by rfl⟩ : syracuseStep 24955127 = 37432691) B37432691
theorem B1296923 : Blo 864565 1296923 := bstep (se 1 (by rfl) ⟨972692, by rfl⟩ : syracuseStep 1296923 = 1945385) B1945385
theorem B1460767 : Blo 864565 1460767 := bstep (se 1 (by rfl) ⟨1095575, by rfl⟩ : syracuseStep 1460767 = 2191151) B2191151
theorem B2574919 : Blo 864565 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B1297001 : Blo 864565 1297001 := bstep (se 2 (by rfl) ⟨486375, by rfl⟩ : syracuseStep 1297001 = 972751) B972751
theorem B9882323 : Blo 864565 9882323 := bstep (se 1 (by rfl) ⟨7411742, by rfl⟩ : syracuseStep 9882323 = 14823485) B14823485
theorem B1559351 : Blo 864565 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B1952567 : Blo 864565 1952567 := bstep (se 1 (by rfl) ⟨1464425, by rfl⟩ : syracuseStep 1952567 = 2928851) B2928851
theorem B1461199 : Blo 864565 1461199 := bstep (se 1 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 1461199 = 2191799) B2191799
theorem B1952747 : Blo 864565 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B1297529 : Blo 864565 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B1297631 : Blo 864565 1297631 := bstep (se 1 (by rfl) ⟨973223, by rfl⟩ : syracuseStep 1297631 = 1946447) B1946447
theorem B1297673 : Blo 864565 1297673 := bstep (se 2 (by rfl) ⟨486627, by rfl⟩ : syracuseStep 1297673 = 973255) B973255
theorem B1297775 : Blo 864565 1297775 := bstep (se 1 (by rfl) ⟨973331, by rfl⟩ : syracuseStep 1297775 = 1946663) B1946663
theorem B1297895 : Blo 864565 1297895 := bstep (se 1 (by rfl) ⟨973421, by rfl⟩ : syracuseStep 1297895 = 1946843) B1946843
theorem B1298027 : Blo 864565 1298027 := bstep (se 1 (by rfl) ⟨973520, by rfl⟩ : syracuseStep 1298027 = 1947041) B1947041
theorem B1461935 : Blo 864565 1461935 := bstep (se 1 (by rfl) ⟨1096451, by rfl⟩ : syracuseStep 1461935 = 2192903) B2192903
theorem B3296963 : Blo 864565 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B1298153 : Blo 864565 1298153 := bstep (se 2 (by rfl) ⟨486807, by rfl⟩ : syracuseStep 1298153 = 973615) B973615
theorem B1953575 : Blo 864565 1953575 := bstep (se 1 (by rfl) ⟨1465181, by rfl⟩ : syracuseStep 1953575 = 2930363) B2930363
theorem B7917385 : Blo 864565 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B1298297 : Blo 864565 1298297 := bstep (se 2 (by rfl) ⟨486861, by rfl⟩ : syracuseStep 1298297 = 973723) B973723
theorem B3297145 : Blo 864565 3297145 := bstep (se 2 (by rfl) ⟨1236429, by rfl⟩ : syracuseStep 3297145 = 2472859) B2472859
theorem B1462171 : Blo 864565 1462171 := bstep (se 1 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 1462171 = 2193257) B2193257
theorem B1298399 : Blo 864565 1298399 := bstep (se 1 (by rfl) ⟨973799, by rfl⟩ : syracuseStep 1298399 = 1947599) B1947599
theorem B12046373 : Blo 864565 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B1298651 : Blo 864565 1298651 := bstep (se 1 (by rfl) ⟨973988, by rfl⟩ : syracuseStep 1298651 = 1947977) B1947977
theorem B1298663 : Blo 864565 1298663 := bstep (se 1 (by rfl) ⟨973997, by rfl⟩ : syracuseStep 1298663 = 1947995) B1947995
theorem B1462583 : Blo 864565 1462583 := bstep (se 1 (by rfl) ⟨1096937, by rfl⟩ : syracuseStep 1462583 = 2193875) B2193875
theorem B1298825 : Blo 864565 1298825 := bstep (se 2 (by rfl) ⟨487059, by rfl⟩ : syracuseStep 1298825 = 974119) B974119
theorem B1298921 : Blo 864565 1298921 := bstep (se 2 (by rfl) ⟨487095, by rfl⟩ : syracuseStep 1298921 = 974191) B974191
theorem B1299047 : Blo 864565 1299047 := bstep (se 1 (by rfl) ⟨974285, by rfl⟩ : syracuseStep 1299047 = 1948571) B1948571
theorem B1299179 : Blo 864565 1299179 := bstep (se 1 (by rfl) ⟨974384, by rfl⟩ : syracuseStep 1299179 = 1948769) B1948769
theorem B1299209 : Blo 864565 1299209 := bstep (se 2 (by rfl) ⟨487203, by rfl⟩ : syracuseStep 1299209 = 974407) B974407
theorem B1299311 : Blo 864565 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B1463359 : Blo 864565 1463359 := bstep (se 1 (by rfl) ⟨1097519, by rfl⟩ : syracuseStep 1463359 = 2195039) B2195039
theorem B1299563 : Blo 864565 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B41047181 : Blo 864565 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B1299803 : Blo 864565 1299803 := bstep (se 1 (by rfl) ⟨974852, by rfl⟩ : syracuseStep 1299803 = 1949705) B1949705
theorem B4674935 : Blo 864565 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B1463879 : Blo 864565 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B1300079 : Blo 864565 1300079 := bstep (se 1 (by rfl) ⟨975059, by rfl⟩ : syracuseStep 1300079 = 1950119) B1950119
theorem B1463975 : Blo 864565 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B1300151 : Blo 864565 1300151 := bstep (se 1 (by rfl) ⟨975113, by rfl⟩ : syracuseStep 1300151 = 1950227) B1950227
theorem B1300187 : Blo 864565 1300187 := bstep (se 1 (by rfl) ⟨975140, by rfl⟩ : syracuseStep 1300187 = 1950281) B1950281
theorem B1464095 : Blo 864565 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B1300361 : Blo 864565 1300361 := bstep (se 2 (by rfl) ⟨487635, by rfl⟩ : syracuseStep 1300361 = 975271) B975271
theorem B1300463 : Blo 864565 1300463 := bstep (se 1 (by rfl) ⟨975347, by rfl⟩ : syracuseStep 1300463 = 1950695) B1950695
theorem B2775023 : Blo 864565 2775023 := bstep (se 1 (by rfl) ⟨2081267, by rfl⟩ : syracuseStep 2775023 = 4162535) B4162535
theorem B1464311 : Blo 864565 1464311 := bstep (se 1 (by rfl) ⟨1098233, by rfl⟩ : syracuseStep 1464311 = 2196467) B2196467
theorem B972895 : Blo 864565 972895 := bstep (se 1 (by rfl) ⟨729671, by rfl⟩ : syracuseStep 972895 = 1459343) B1459343
theorem B1300715 : Blo 864565 1300715 := bstep (se 1 (by rfl) ⟨975536, by rfl⟩ : syracuseStep 1300715 = 1951073) B1951073
theorem B8444189 : Blo 864565 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1300775 : Blo 864565 1300775 := bstep (se 1 (by rfl) ⟨975581, by rfl⟩ : syracuseStep 1300775 = 1951163) B1951163
theorem B3561769 : Blo 864565 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B1300859 : Blo 864565 1300859 := bstep (se 1 (by rfl) ⟨975644, by rfl⟩ : syracuseStep 1300859 = 1951289) B1951289
theorem B6576551 : Blo 864565 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B4676059 : Blo 864565 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B6248933 : Blo 864565 6248933 := bstep (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) B1171675
theorem B1301129 : Blo 864565 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B1301303 : Blo 864565 1301303 := bstep (se 1 (by rfl) ⟨975977, by rfl⟩ : syracuseStep 1301303 = 1951955) B1951955
theorem B1301339 : Blo 864565 1301339 := bstep (se 1 (by rfl) ⟨976004, by rfl⟩ : syracuseStep 1301339 = 1952009) B1952009
theorem B1301483 : Blo 864565 1301483 := bstep (se 1 (by rfl) ⟨976112, by rfl⟩ : syracuseStep 1301483 = 1952225) B1952225
theorem B1465391 : Blo 864565 1465391 := bstep (se 1 (by rfl) ⟨1099043, by rfl⟩ : syracuseStep 1465391 = 2198087) B2198087
theorem B1465465 : Blo 864565 1465465 := bstep (se 2 (by rfl) ⟨549549, by rfl⟩ : syracuseStep 1465465 = 1099099) B1099099
theorem B1301687 : Blo 864565 1301687 := bstep (se 1 (by rfl) ⟨976265, by rfl⟩ : syracuseStep 1301687 = 1952531) B1952531
theorem B1236151 : Blo 864565 1236151 := bstep (se 1 (by rfl) ⟨927113, by rfl⟩ : syracuseStep 1236151 = 1854227) B1854227
theorem B974047 : Blo 864565 974047 := bstep (se 1 (by rfl) ⟨730535, by rfl⟩ : syracuseStep 974047 = 1461071) B1461071
theorem B1301927 : Blo 864565 1301927 := bstep (se 1 (by rfl) ⟨976445, by rfl⟩ : syracuseStep 1301927 = 1952891) B1952891
theorem B1302011 : Blo 864565 1302011 := bstep (se 1 (by rfl) ⟨976508, by rfl⟩ : syracuseStep 1302011 = 1953017) B1953017
theorem B1236475 : Blo 864565 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B1302107 : Blo 864565 1302107 := bstep (se 1 (by rfl) ⟨976580, by rfl⟩ : syracuseStep 1302107 = 1953161) B1953161
theorem B1302191 : Blo 864565 1302191 := bstep (se 1 (by rfl) ⟨976643, by rfl⟩ : syracuseStep 1302191 = 1953287) B1953287
theorem B1302311 : Blo 864565 1302311 := bstep (se 1 (by rfl) ⟨976733, by rfl⟩ : syracuseStep 1302311 = 1953467) B1953467
theorem B1302395 : Blo 864565 1302395 := bstep (se 1 (by rfl) ⟨976796, by rfl⟩ : syracuseStep 1302395 = 1953593) B1953593
theorem B1302815 : Blo 864565 1302815 := bstep (se 1 (by rfl) ⟨977111, by rfl⟩ : syracuseStep 1302815 = 1954223) B1954223
theorem B1302839 : Blo 864565 1302839 := bstep (se 1 (by rfl) ⟨977129, by rfl⟩ : syracuseStep 1302839 = 1954259) B1954259
theorem B8315453 : Blo 864565 8315453 := bstep (se 3 (by rfl) ⟨1559147, by rfl⟩ : syracuseStep 8315453 = 3118295) B3118295
theorem B97608401 : Blo 864565 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B4678397 : Blo 864565 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B2777867 : Blo 864565 2777867 := bstep (se 1 (by rfl) ⟨2083400, by rfl⟩ : syracuseStep 2777867 = 4166801) B4166801
theorem B2220967 : Blo 864565 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B6841331 : Blo 864565 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B976495 : Blo 864565 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B976603 : Blo 864565 976603 := bstep (se 1 (by rfl) ⟨732452, by rfl⟩ : syracuseStep 976603 = 1464905) B1464905
theorem B12511007 : Blo 864565 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B15820751 : Blo 864565 15820751 := bstep (se 1 (by rfl) ⟨11865563, by rfl⟩ : syracuseStep 15820751 = 23731127) B23731127
theorem B6252623 : Blo 864565 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B3696749 : Blo 864565 3696749 := bstep (se 3 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 3696749 = 1386281) B1386281
theorem B2189663 : Blo 864565 2189663 := bstep (se 1 (by rfl) ⟨1642247, by rfl⟩ : syracuseStep 2189663 = 3284495) B3284495
theorem B2189855 : Blo 864565 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B24078965 : Blo 864565 24078965 := bstep (se 5 (by rfl) ⟨1128701, by rfl⟩ : syracuseStep 24078965 = 2257403) B2257403
theorem B3697807 : Blo 864565 3697807 := bstep (se 1 (by rfl) ⟨2773355, by rfl⟩ : syracuseStep 3697807 = 5546711) B5546711
theorem B4943213 : Blo 864565 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B10546631 : Blo 864565 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B4387283 : Blo 864565 4387283 := bstep (se 1 (by rfl) ⟨3290462, by rfl⟩ : syracuseStep 4387283 = 6580925) B6580925
theorem B43315897 : Blo 864565 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B12514013 : Blo 864565 12514013 := bstep (se 3 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 12514013 = 4692755) B4692755
theorem B2192447 : Blo 864565 2192447 := bstep (se 1 (by rfl) ⟨1644335, by rfl⟩ : syracuseStep 2192447 = 3288671) B3288671
theorem B4945171 : Blo 864565 4945171 := bstep (se 1 (by rfl) ⟨3708878, by rfl⟩ : syracuseStep 4945171 = 7417757) B7417757
theorem B9369245 : Blo 864565 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B2193551 : Blo 864565 2193551 := bstep (se 1 (by rfl) ⟨1645163, by rfl⟩ : syracuseStep 2193551 = 3290327) B3290327
theorem B7403885 : Blo 864565 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B47446681 : Blo 864565 47446681 := bstep (se 2 (by rfl) ⟨17792505, by rfl⟩ : syracuseStep 47446681 = 35585011) B35585011
theorem B2227103 : Blo 864565 2227103 := bstep (se 1 (by rfl) ⟨1670327, by rfl⟩ : syracuseStep 2227103 = 3340655) B3340655
theorem B4684709 : Blo 864565 4684709 := bstep (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) B878383
theorem B5012999 : Blo 864565 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B5930729 : Blo 864565 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B6588215 : Blo 864565 6588215 := bstep (se 1 (by rfl) ⟨4941161, by rfl⟩ : syracuseStep 6588215 = 9882323) B9882323
theorem B8456345 : Blo 864565 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B2853025 : Blo 864565 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B2197975 : Blo 864565 2197975 := bstep (se 1 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 2197975 = 3296963) B3296963
theorem B8030915 : Blo 864565 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B2198441 : Blo 864565 2198441 := bstep (se 2 (by rfl) ⟨824415, by rfl⟩ : syracuseStep 2198441 = 1648831) B1648831
theorem B13732901 : Blo 864565 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B1641647 : Blo 864565 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B27364787 : Blo 864565 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B1314991 : Blo 864565 1314991 := bstep (se 1 (by rfl) ⟨986243, by rfl⟩ : syracuseStep 1314991 = 1972487) B1972487
theorem B4165955 : Blo 864565 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B4395383 : Blo 864565 4395383 := bstep (se 1 (by rfl) ⟨3296537, by rfl⟩ : syracuseStep 4395383 = 6593075) B6593075
theorem B4166225 : Blo 864565 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B1315823 : Blo 864565 1315823 := bstep (se 1 (by rfl) ⟨986867, by rfl⟩ : syracuseStep 1315823 = 1973735) B1973735
theorem B10556513 : Blo 864565 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B2462881 : Blo 864565 2462881 := bstep (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) B1847161
theorem B4396193 : Blo 864565 4396193 := bstep (se 2 (by rfl) ⟨1648572, by rfl⟩ : syracuseStep 4396193 = 3297145) B3297145
theorem B1316335 : Blo 864565 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B5543635 : Blo 864565 5543635 := bstep (se 1 (by rfl) ⟨4157726, by rfl⟩ : syracuseStep 5543635 = 8315453) B8315453
theorem B3118931 : Blo 864565 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B4560887 : Blo 864565 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B4168415 : Blo 864565 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B2464499 : Blo 864565 2464499 := bstep (se 1 (by rfl) ⟨1848374, by rfl⟩ : syracuseStep 2464499 = 3696749) B3696749
theorem B6593561 : Blo 864565 6593561 := bstep (se 2 (by rfl) ⟨2472585, by rfl⟩ : syracuseStep 6593561 = 4945171) B4945171
theorem B3284009 : Blo 864565 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B15802067 : Blo 864565 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B11116385 : Blo 864565 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B6594533 : Blo 864565 6594533 := bstep (se 4 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 6594533 = 1236475) B1236475
theorem B2629847 : Blo 864565 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B2924855 : Blo 864565 2924855 := bstep (se 1 (by rfl) ⟨2193641, by rfl⟩ : syracuseStep 2924855 = 4387283) B4387283
theorem B6234745 : Blo 864565 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B9872117 : Blo 864565 9872117 := bstep (se 5 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 9872117 = 925511) B925511
theorem B2630407 : Blo 864565 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B1648201 : Blo 864565 1648201 := bstep (se 2 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 1648201 = 1236151) B1236151
theorem B1484735 : Blo 864565 1484735 := bstep (se 1 (by rfl) ⟨1113551, by rfl⟩ : syracuseStep 1484735 = 2227103) B2227103
theorem B3123139 : Blo 864565 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B1648687 : Blo 864565 1648687 := bstep (se 1 (by rfl) ⟨1236515, by rfl⟩ : syracuseStep 1648687 = 2473031) B2473031
theorem B7416359 : Blo 864565 7416359 := bstep (se 1 (by rfl) ⟨5562269, by rfl⟩ : syracuseStep 7416359 = 11124539) B11124539
theorem B8006215 : Blo 864565 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B4926035 : Blo 864565 4926035 := bstep (se 1 (by rfl) ⟨3694526, by rfl⟩ : syracuseStep 4926035 = 7389053) B7389053
theorem B1977385 : Blo 864565 1977385 := bstep (se 2 (by rfl) ⟨741519, by rfl⟩ : syracuseStep 1977385 = 1483039) B1483039
theorem B2469113 : Blo 864565 2469113 := bstep (se 2 (by rfl) ⟨925917, by rfl⟩ : syracuseStep 2469113 = 1851835) B1851835
theorem B6237803 : Blo 864565 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B2928311 : Blo 864565 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B1945313 : Blo 864565 1945313 := bstep (se 2 (by rfl) ⟨729492, by rfl⟩ : syracuseStep 1945313 = 1458985) B1458985
theorem B2502377 : Blo 864565 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B3518333 : Blo 864565 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B2961289 : Blo 864565 2961289 := bstep (se 2 (by rfl) ⟨1110483, by rfl⟩ : syracuseStep 2961289 = 2220967) B2220967
theorem B1945673 : Blo 864565 1945673 := bstep (se 2 (by rfl) ⟨729627, by rfl⟩ : syracuseStep 1945673 = 1459255) B1459255
theorem B1945727 : Blo 864565 1945727 := bstep (se 1 (by rfl) ⟨1459295, by rfl⟩ : syracuseStep 1945727 = 2918591) B2918591
theorem B864615 : Blo 864565 864615 := bstep (se 1 (by rfl) ⟨648461, by rfl⟩ : syracuseStep 864615 = 1296923) B1296923
theorem B864667 : Blo 864565 864667 := bstep (se 1 (by rfl) ⟨648500, by rfl⟩ : syracuseStep 864667 = 1297001) B1297001
theorem B865019 : Blo 864565 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B865087 : Blo 864565 865087 := bstep (se 1 (by rfl) ⟨648815, by rfl⟩ : syracuseStep 865087 = 1297631) B1297631
theorem B865115 : Blo 864565 865115 := bstep (se 1 (by rfl) ⟨648836, by rfl⟩ : syracuseStep 865115 = 1297673) B1297673
theorem B8893313 : Blo 864565 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B865183 : Blo 864565 865183 := bstep (se 1 (by rfl) ⟨648887, by rfl⟩ : syracuseStep 865183 = 1297775) B1297775
theorem B865263 : Blo 864565 865263 := bstep (se 1 (by rfl) ⟨648947, by rfl⟩ : syracuseStep 865263 = 1297895) B1297895
theorem B865351 : Blo 864565 865351 := bstep (se 1 (by rfl) ⟨649013, by rfl⟩ : syracuseStep 865351 = 1298027) B1298027
theorem B1848425 : Blo 864565 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B2929769 : Blo 864565 2929769 := bstep (se 2 (by rfl) ⟨1098663, by rfl⟩ : syracuseStep 2929769 = 2197327) B2197327
theorem B865435 : Blo 864565 865435 := bstep (se 1 (by rfl) ⟨649076, by rfl⟩ : syracuseStep 865435 = 1298153) B1298153
theorem B1946807 : Blo 864565 1946807 := bstep (se 1 (by rfl) ⟨1460105, by rfl⟩ : syracuseStep 1946807 = 2920211) B2920211
theorem B5551325 : Blo 864565 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B865531 : Blo 864565 865531 := bstep (se 1 (by rfl) ⟨649148, by rfl⟩ : syracuseStep 865531 = 1298297) B1298297
theorem B865599 : Blo 864565 865599 := bstep (se 1 (by rfl) ⟨649199, by rfl⟩ : syracuseStep 865599 = 1298399) B1298399
theorem B168998237 : Blo 864565 168998237 := bstep (se 3 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 168998237 = 63374339) B63374339
theorem B865767 : Blo 864565 865767 := bstep (se 1 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 865767 = 1298651) B1298651
theorem B865775 : Blo 864565 865775 := bstep (se 1 (by rfl) ⟨649331, by rfl⟩ : syracuseStep 865775 = 1298663) B1298663
theorem B24032807 : Blo 864565 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B865883 : Blo 864565 865883 := bstep (se 1 (by rfl) ⟨649412, by rfl⟩ : syracuseStep 865883 = 1298825) B1298825
theorem B865947 : Blo 864565 865947 := bstep (se 1 (by rfl) ⟨649460, by rfl⟩ : syracuseStep 865947 = 1298921) B1298921
theorem B866031 : Blo 864565 866031 := bstep (se 1 (by rfl) ⟨649523, by rfl⟩ : syracuseStep 866031 = 1299047) B1299047
theorem B1947383 : Blo 864565 1947383 := bstep (se 1 (by rfl) ⟨1460537, by rfl⟩ : syracuseStep 1947383 = 2921075) B2921075
theorem B866119 : Blo 864565 866119 := bstep (se 1 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 866119 = 1299179) B1299179
theorem B866139 : Blo 864565 866139 := bstep (se 1 (by rfl) ⟨649604, by rfl⟩ : syracuseStep 866139 = 1299209) B1299209
theorem B866207 : Blo 864565 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B1947563 : Blo 864565 1947563 := bstep (se 1 (by rfl) ⟨1460672, by rfl⟩ : syracuseStep 1947563 = 2921345) B2921345
theorem B1947689 : Blo 864565 1947689 := bstep (se 2 (by rfl) ⟨730383, by rfl⟩ : syracuseStep 1947689 = 1460767) B1460767
theorem B866375 : Blo 864565 866375 := bstep (se 1 (by rfl) ⟨649781, by rfl⟩ : syracuseStep 866375 = 1299563) B1299563
theorem B866535 : Blo 864565 866535 := bstep (se 1 (by rfl) ⟨649901, by rfl⟩ : syracuseStep 866535 = 1299803) B1299803
theorem B12466493 : Blo 864565 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B866719 : Blo 864565 866719 := bstep (se 1 (by rfl) ⟨650039, by rfl⟩ : syracuseStep 866719 = 1300079) B1300079
theorem B1948103 : Blo 864565 1948103 := bstep (se 1 (by rfl) ⟨1461077, by rfl⟩ : syracuseStep 1948103 = 2922155) B2922155
theorem B866767 : Blo 864565 866767 := bstep (se 1 (by rfl) ⟨650075, by rfl⟩ : syracuseStep 866767 = 1300151) B1300151
theorem B866791 : Blo 864565 866791 := bstep (se 1 (by rfl) ⟨650093, by rfl⟩ : syracuseStep 866791 = 1300187) B1300187
theorem B866907 : Blo 864565 866907 := bstep (se 1 (by rfl) ⟨650180, by rfl⟩ : syracuseStep 866907 = 1300361) B1300361
theorem B1948265 : Blo 864565 1948265 := bstep (se 2 (by rfl) ⟨730599, by rfl⟩ : syracuseStep 1948265 = 1461199) B1461199
theorem B3291785 : Blo 864565 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B1948319 : Blo 864565 1948319 := bstep (se 1 (by rfl) ⟨1461239, by rfl⟩ : syracuseStep 1948319 = 2922479) B2922479
theorem B1850015 : Blo 864565 1850015 := bstep (se 1 (by rfl) ⟨1387511, by rfl⟩ : syracuseStep 1850015 = 2775023) B2775023
theorem B866975 : Blo 864565 866975 := bstep (se 1 (by rfl) ⟨650231, by rfl⟩ : syracuseStep 866975 = 1300463) B1300463
theorem B1948463 : Blo 864565 1948463 := bstep (se 1 (by rfl) ⟨1461347, by rfl⟩ : syracuseStep 1948463 = 2922695) B2922695
theorem B867143 : Blo 864565 867143 := bstep (se 1 (by rfl) ⟨650357, by rfl⟩ : syracuseStep 867143 = 1300715) B1300715
theorem B4930409 : Blo 864565 4930409 := bstep (se 2 (by rfl) ⟨1848903, by rfl⟩ : syracuseStep 4930409 = 3697807) B3697807
theorem B867183 : Blo 864565 867183 := bstep (se 1 (by rfl) ⟨650387, by rfl⟩ : syracuseStep 867183 = 1300775) B1300775
theorem B867239 : Blo 864565 867239 := bstep (se 1 (by rfl) ⟨650429, by rfl⟩ : syracuseStep 867239 = 1300859) B1300859
theorem B3521447 : Blo 864565 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B867419 : Blo 864565 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B867535 : Blo 864565 867535 := bstep (se 1 (by rfl) ⟨650651, by rfl⟩ : syracuseStep 867535 = 1301303) B1301303
theorem B1948895 : Blo 864565 1948895 := bstep (se 1 (by rfl) ⟨1461671, by rfl⟩ : syracuseStep 1948895 = 2923343) B2923343
theorem B867559 : Blo 864565 867559 := bstep (se 1 (by rfl) ⟨650669, by rfl⟩ : syracuseStep 867559 = 1301339) B1301339
theorem B867655 : Blo 864565 867655 := bstep (se 1 (by rfl) ⟨650741, by rfl⟩ : syracuseStep 867655 = 1301483) B1301483
theorem B3947945 : Blo 864565 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B2080171 : Blo 864565 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B1949111 : Blo 864565 1949111 := bstep (se 1 (by rfl) ⟨1461833, by rfl⟩ : syracuseStep 1949111 = 2923667) B2923667
theorem B867791 : Blo 864565 867791 := bstep (se 1 (by rfl) ⟨650843, by rfl⟩ : syracuseStep 867791 = 1301687) B1301687
theorem B1949291 : Blo 864565 1949291 := bstep (se 1 (by rfl) ⟨1461968, by rfl⟩ : syracuseStep 1949291 = 2923937) B2923937
theorem B1097327 : Blo 864565 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B867951 : Blo 864565 867951 := bstep (se 1 (by rfl) ⟨650963, by rfl⟩ : syracuseStep 867951 = 1301927) B1301927
theorem B868007 : Blo 864565 868007 := bstep (se 1 (by rfl) ⟨651005, by rfl⟩ : syracuseStep 868007 = 1302011) B1302011
theorem B868071 : Blo 864565 868071 := bstep (se 1 (by rfl) ⟨651053, by rfl⟩ : syracuseStep 868071 = 1302107) B1302107
theorem B868127 : Blo 864565 868127 := bstep (se 1 (by rfl) ⟨651095, by rfl⟩ : syracuseStep 868127 = 1302191) B1302191
theorem B868207 : Blo 864565 868207 := bstep (se 1 (by rfl) ⟨651155, by rfl⟩ : syracuseStep 868207 = 1302311) B1302311
theorem B1949561 : Blo 864565 1949561 := bstep (se 2 (by rfl) ⟨731085, by rfl⟩ : syracuseStep 1949561 = 1462171) B1462171
theorem B868263 : Blo 864565 868263 := bstep (se 1 (by rfl) ⟨651197, by rfl⟩ : syracuseStep 868263 = 1302395) B1302395
theorem B1949651 : Blo 864565 1949651 := bstep (se 1 (by rfl) ⟨1462238, by rfl⟩ : syracuseStep 1949651 = 2924477) B2924477
theorem B868543 : Blo 864565 868543 := bstep (se 1 (by rfl) ⟨651407, by rfl⟩ : syracuseStep 868543 = 1302815) B1302815
theorem B868559 : Blo 864565 868559 := bstep (se 1 (by rfl) ⟨651419, by rfl⟩ : syracuseStep 868559 = 1302839) B1302839
theorem B1098031 : Blo 864565 1098031 := bstep (se 1 (by rfl) ⟨823523, by rfl⟩ : syracuseStep 1098031 = 1647047) B1647047
theorem B1851911 : Blo 864565 1851911 := bstep (se 1 (by rfl) ⟨1388933, by rfl⟩ : syracuseStep 1851911 = 2777867) B2777867
theorem B57754529 : Blo 864565 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B5555375 : Blo 864565 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B1950911 : Blo 864565 1950911 := bstep (se 1 (by rfl) ⟨1463183, by rfl⟩ : syracuseStep 1950911 = 2926367) B2926367
theorem B8340671 : Blo 864565 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B1951055 : Blo 864565 1951055 := bstep (se 1 (by rfl) ⟨1463291, by rfl⟩ : syracuseStep 1951055 = 2926583) B2926583
theorem B1951145 : Blo 864565 1951145 := bstep (se 2 (by rfl) ⟨731679, by rfl⟩ : syracuseStep 1951145 = 1463359) B1463359
theorem B1459775 : Blo 864565 1459775 := bstep (se 1 (by rfl) ⟨1094831, by rfl⟩ : syracuseStep 1459775 = 2189663) B2189663
theorem B64210573 : Blo 864565 64210573 := bstep (se 3 (by rfl) ⟨12039482, by rfl⟩ : syracuseStep 64210573 = 24078965) B24078965
theorem B1459903 : Blo 864565 1459903 := bstep (se 1 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 1459903 = 2189855) B2189855
theorem B1951631 : Blo 864565 1951631 := bstep (se 1 (by rfl) ⟨1463723, by rfl⟩ : syracuseStep 1951631 = 2927447) B2927447
theorem B1951775 : Blo 864565 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B2083015 : Blo 864565 2083015 := bstep (se 1 (by rfl) ⟨1562261, by rfl⟩ : syracuseStep 2083015 = 3124523) B3124523
theorem B3295475 : Blo 864565 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B1952027 : Blo 864565 1952027 := bstep (se 1 (by rfl) ⟨1464020, by rfl⟩ : syracuseStep 1952027 = 2928041) B2928041
theorem B7031087 : Blo 864565 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B28821851 : Blo 864565 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B1952351 : Blo 864565 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B2378521 : Blo 864565 2378521 := bstep (se 2 (by rfl) ⟨891945, by rfl⟩ : syracuseStep 2378521 = 1783891) B1783891
theorem B1297193 : Blo 864565 1297193 := bstep (se 2 (by rfl) ⟨486447, by rfl⟩ : syracuseStep 1297193 = 972895) B972895
theorem B1952603 : Blo 864565 1952603 := bstep (se 1 (by rfl) ⟨1464452, by rfl⟩ : syracuseStep 1952603 = 2928905) B2928905
theorem B4377563 : Blo 864565 4377563 := bstep (se 1 (by rfl) ⟨3283172, by rfl⟩ : syracuseStep 4377563 = 6566345) B6566345
theorem B1297403 : Blo 864565 1297403 := bstep (se 1 (by rfl) ⟨973052, by rfl⟩ : syracuseStep 1297403 = 1946105) B1946105
theorem B1297463 : Blo 864565 1297463 := bstep (se 1 (by rfl) ⟨973097, by rfl⟩ : syracuseStep 1297463 = 1946195) B1946195
theorem B8342675 : Blo 864565 8342675 := bstep (se 1 (by rfl) ⟨6257006, by rfl⟩ : syracuseStep 8342675 = 12514013) B12514013
theorem B1297583 : Blo 864565 1297583 := bstep (se 1 (by rfl) ⟨973187, by rfl⟩ : syracuseStep 1297583 = 1946375) B1946375
theorem B2084015 : Blo 864565 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B1756507 : Blo 864565 1756507 := bstep (se 1 (by rfl) ⟨1317380, by rfl⟩ : syracuseStep 1756507 = 2634761) B2634761
theorem B1461631 : Blo 864565 1461631 := bstep (se 1 (by rfl) ⟨1096223, by rfl⟩ : syracuseStep 1461631 = 2192447) B2192447
theorem B7032253 : Blo 864565 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B63262241 : Blo 864565 63262241 := bstep (se 2 (by rfl) ⟨23723340, by rfl⟩ : syracuseStep 63262241 = 47446681) B47446681
theorem B1953359 : Blo 864565 1953359 := bstep (se 1 (by rfl) ⟨1465019, by rfl⟩ : syracuseStep 1953359 = 2930039) B2930039
theorem B6246163 : Blo 864565 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B1298303 : Blo 864565 1298303 := bstep (se 1 (by rfl) ⟨973727, by rfl⟩ : syracuseStep 1298303 = 1947455) B1947455
theorem B1298495 : Blo 864565 1298495 := bstep (se 1 (by rfl) ⟨973871, by rfl⟩ : syracuseStep 1298495 = 1947743) B1947743
theorem B1462367 : Blo 864565 1462367 := bstep (se 1 (by rfl) ⟨1096775, by rfl⟩ : syracuseStep 1462367 = 2193551) B2193551
theorem B1953899 : Blo 864565 1953899 := bstep (se 1 (by rfl) ⟨1465424, by rfl⟩ : syracuseStep 1953899 = 2930849) B2930849
theorem B1953953 : Blo 864565 1953953 := bstep (se 2 (by rfl) ⟨732732, by rfl⟩ : syracuseStep 1953953 = 1465465) B1465465
theorem B4935923 : Blo 864565 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B1954079 : Blo 864565 1954079 := bstep (se 1 (by rfl) ⟨1465559, by rfl⟩ : syracuseStep 1954079 = 2931119) B2931119
theorem B1298729 : Blo 864565 1298729 := bstep (se 2 (by rfl) ⟨487023, by rfl⟩ : syracuseStep 1298729 = 974047) B974047
theorem B3297617 : Blo 864565 3297617 := bstep (se 2 (by rfl) ⟨1236606, by rfl⟩ : syracuseStep 3297617 = 2473213) B2473213
theorem B1298999 : Blo 864565 1298999 := bstep (se 1 (by rfl) ⟨974249, by rfl⟩ : syracuseStep 1298999 = 1948499) B1948499
theorem B1233463 : Blo 864565 1233463 := bstep (se 1 (by rfl) ⟨925097, by rfl⟩ : syracuseStep 1233463 = 1850195) B1850195
theorem B1299359 : Blo 864565 1299359 := bstep (se 1 (by rfl) ⟨974519, by rfl⟩ : syracuseStep 1299359 = 1949039) B1949039
theorem B1299551 : Blo 864565 1299551 := bstep (se 1 (by rfl) ⟨974663, by rfl⟩ : syracuseStep 1299551 = 1949327) B1949327
theorem B1299611 : Blo 864565 1299611 := bstep (se 1 (by rfl) ⟨974708, by rfl⟩ : syracuseStep 1299611 = 1949417) B1949417
theorem B3953819 : Blo 864565 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B59954417 : Blo 864565 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B1463663 : Blo 864565 1463663 := bstep (se 1 (by rfl) ⟨1097747, by rfl⟩ : syracuseStep 1463663 = 2195495) B2195495
theorem B1463791 : Blo 864565 1463791 := bstep (se 1 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 1463791 = 2195687) B2195687
theorem B8312377 : Blo 864565 8312377 := bstep (se 2 (by rfl) ⟨3117141, by rfl⟩ : syracuseStep 8312377 = 6234283) B6234283
theorem B5330569 : Blo 864565 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B4445975 : Blo 864565 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B1300295 : Blo 864565 1300295 := bstep (se 1 (by rfl) ⟨975221, by rfl⟩ : syracuseStep 1300295 = 1950443) B1950443
theorem B1464223 : Blo 864565 1464223 := bstep (se 1 (by rfl) ⟨1098167, by rfl⟩ : syracuseStep 1464223 = 2196335) B2196335
theorem B4380641 : Blo 864565 4380641 := bstep (se 2 (by rfl) ⟨1642740, by rfl⟩ : syracuseStep 4380641 = 3285481) B3285481
theorem B1235359 : Blo 864565 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B1300895 : Blo 864565 1300895 := bstep (se 1 (by rfl) ⟨975671, by rfl⟩ : syracuseStep 1300895 = 1951343) B1951343
theorem B1300967 : Blo 864565 1300967 := bstep (se 1 (by rfl) ⟨975725, by rfl⟩ : syracuseStep 1300967 = 1951451) B1951451
theorem B973471 : Blo 864565 973471 := bstep (se 1 (by rfl) ⟨730103, by rfl⟩ : syracuseStep 973471 = 1460207) B1460207
theorem B16636751 : Blo 864565 16636751 := bstep (se 1 (by rfl) ⟨12477563, by rfl⟩ : syracuseStep 16636751 = 24955127) B24955127
theorem B3169259 : Blo 864565 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B1039567 : Blo 864565 1039567 := bstep (se 1 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 1039567 = 1559351) B1559351
theorem B1301711 : Blo 864565 1301711 := bstep (se 1 (by rfl) ⟨976283, by rfl⟩ : syracuseStep 1301711 = 1952567) B1952567
theorem B1301831 : Blo 864565 1301831 := bstep (se 1 (by rfl) ⟨976373, by rfl⟩ : syracuseStep 1301831 = 1952747) B1952747
theorem B4677097 : Blo 864565 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B1301993 : Blo 864565 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B3956215 : Blo 864565 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B1302137 : Blo 864565 1302137 := bstep (se 2 (by rfl) ⟨488301, by rfl⟩ : syracuseStep 1302137 = 976603) B976603
theorem B974623 : Blo 864565 974623 := bstep (se 1 (by rfl) ⟨730967, by rfl⟩ : syracuseStep 974623 = 1461935) B1461935
theorem B1302383 : Blo 864565 1302383 := bstep (se 1 (by rfl) ⟨976787, by rfl⟩ : syracuseStep 1302383 = 1953575) B1953575
theorem B975055 : Blo 864565 975055 := bstep (se 1 (by rfl) ⟨731291, by rfl⟩ : syracuseStep 975055 = 1462583) B1462583
theorem B22176179 : Blo 864565 22176179 := bstep (se 1 (by rfl) ⟨16632134, by rfl⟩ : syracuseStep 22176179 = 33264269) B33264269
theorem B975919 : Blo 864565 975919 := bstep (se 1 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 975919 = 1463879) B1463879
theorem B975983 : Blo 864565 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B976063 : Blo 864565 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B976207 : Blo 864565 976207 := bstep (se 1 (by rfl) ⟨732155, by rfl⟩ : syracuseStep 976207 = 1464311) B1464311
theorem B5629459 : Blo 864565 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B4384367 : Blo 864565 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B2779123 : Blo 864565 2779123 := bstep (se 1 (by rfl) ⟨2084342, by rfl⟩ : syracuseStep 2779123 = 4168685) B4168685
theorem B976927 : Blo 864565 976927 := bstep (se 1 (by rfl) ⟨732695, by rfl⟩ : syracuseStep 976927 = 1465391) B1465391
theorem B10676909 : Blo 864565 10676909 := bstep (se 3 (by rfl) ⟨2001920, by rfl⟩ : syracuseStep 10676909 = 4003841) B4003841
theorem B65072267 : Blo 864565 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B4157153 : Blo 864565 4157153 := bstep (se 2 (by rfl) ⟨1558932, by rfl⟩ : syracuseStep 4157153 = 3117865) B3117865
theorem B31289125 : Blo 864565 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B8318801 : Blo 864565 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B10547167 : Blo 864565 10547167 := bstep (se 1 (by rfl) ⟨7910375, by rfl⟩ : syracuseStep 10547167 = 15820751) B15820751
theorem B2257159 : Blo 864565 2257159 := bstep (se 1 (by rfl) ⟨1692869, by rfl⟩ : syracuseStep 2257159 = 3385739) B3385739
theorem B2192123 : Blo 864565 2192123 := bstep (se 1 (by rfl) ⟨1644092, by rfl⟩ : syracuseStep 2192123 = 3288185) B3288185
theorem B4158479 : Blo 864565 4158479 := bstep (se 1 (by rfl) ⟨3118859, by rfl⟩ : syracuseStep 4158479 = 6237719) B6237719
theorem B2192467 : Blo 864565 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B4749025 : Blo 864565 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B3700541 : Blo 864565 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B10516463 : Blo 864565 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B4946129 : Blo 864565 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B8321453 : Blo 864565 8321453 := bstep (se 3 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 8321453 = 3120545) B3120545
theorem B3701483 : Blo 864565 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B3341999 : Blo 864565 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B4390685 : Blo 864565 4390685 := bstep (se 3 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 4390685 = 1646507) B1646507
theorem B7012925 : Blo 864565 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B38503019 : Blo 864565 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B3703583 : Blo 864565 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B3507209 : Blo 864565 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B11109413 : Blo 864565 11109413 := bstep (se 4 (by rfl) ⟨1041507, by rfl⟩ : syracuseStep 11109413 = 2083015) B2083015
theorem B4392143 : Blo 864565 4392143 := bstep (se 1 (by rfl) ⟨3294107, by rfl⟩ : syracuseStep 4392143 = 6588215) B6588215
theorem B5637563 : Blo 864565 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B2196983 : Blo 864565 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B4687391 : Blo 864565 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B2918375 : Blo 864565 2918375 := bstep (se 1 (by rfl) ⟨2188781, by rfl⟩ : syracuseStep 2918375 = 4377563) B4377563
theorem B7505945 : Blo 864565 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B2197601 : Blo 864565 2197601 := bstep (se 2 (by rfl) ⟨824100, by rfl⟩ : syracuseStep 2197601 = 1648201) B1648201
theorem B42174827 : Blo 864565 42174827 := bstep (se 1 (by rfl) ⟨31631120, by rfl⟩ : syracuseStep 42174827 = 63262241) B63262241
theorem B4164185 : Blo 864565 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B3508861 : Blo 864565 3508861 := bstep (se 3 (by rfl) ⟨657911, by rfl⟩ : syracuseStep 3508861 = 1315823) B1315823
theorem B3705497 : Blo 864565 3705497 := bstep (se 2 (by rfl) ⟨1389561, by rfl⟩ : syracuseStep 3705497 = 2779123) B2779123
theorem B2198249 : Blo 864565 2198249 := bstep (se 2 (by rfl) ⟨824343, by rfl⟩ : syracuseStep 2198249 = 1648687) B1648687
theorem B2198411 : Blo 864565 2198411 := bstep (se 1 (by rfl) ⟨1648808, by rfl⟩ : syracuseStep 2198411 = 3297617) B3297617
theorem B2920427 : Blo 864565 2920427 := bstep (se 1 (by rfl) ⟨2190320, by rfl⟩ : syracuseStep 2920427 = 4380641) B4380641
theorem B1642999 : Blo 864565 1642999 := bstep (se 1 (by rfl) ⟨1232249, by rfl⟩ : syracuseStep 1642999 = 2464499) B2464499
theorem B9376337 : Blo 864565 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B4395707 : Blo 864565 4395707 := bstep (se 1 (by rfl) ⟨3296780, by rfl⟩ : syracuseStep 4395707 = 6593561) B6593561
theorem B8328217 : Blo 864565 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B41718833 : Blo 864565 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B7410923 : Blo 864565 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B14062889 : Blo 864565 14062889 := bstep (se 2 (by rfl) ⟨5273583, by rfl⟩ : syracuseStep 14062889 = 10547167) B10547167
theorem B4396355 : Blo 864565 4396355 := bstep (se 1 (by rfl) ⟨3297266, by rfl⟩ : syracuseStep 4396355 = 6594533) B6594533
theorem B14784119 : Blo 864565 14784119 := bstep (se 1 (by rfl) ⟨11088089, by rfl⟩ : syracuseStep 14784119 = 22176179) B22176179
theorem B1644617 : Blo 864565 1644617 := bstep (se 2 (by rfl) ⟨616731, by rfl⟩ : syracuseStep 1644617 = 1233463) B1233463
theorem B2922911 : Blo 864565 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B2923289 : Blo 864565 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B3283841 : Blo 864565 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B3284023 : Blo 864565 3284023 := bstep (se 1 (by rfl) ⟨2463017, by rfl⟩ : syracuseStep 3284023 = 4926035) B4926035
theorem B7117939 : Blo 864565 7117939 := bstep (se 1 (by rfl) ⟨5338454, by rfl⟩ : syracuseStep 7117939 = 10676909) B10676909
theorem B11083169 : Blo 864565 11083169 := bstep (se 2 (by rfl) ⟨4156188, by rfl⟩ : syracuseStep 11083169 = 8312377) B8312377
theorem B1646075 : Blo 864565 1646075 := bstep (se 1 (by rfl) ⟨1234556, by rfl⟩ : syracuseStep 1646075 = 2469113) B2469113
theorem B6332033 : Blo 864565 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B5545867 : Blo 864565 5545867 := bstep (se 1 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 5545867 = 8318801) B8318801
theorem B1647145 : Blo 864565 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B112665491 : Blo 864565 112665491 := bstep (se 1 (by rfl) ⟨84499118, by rfl⟩ : syracuseStep 112665491 = 168998237) B168998237
theorem B10527853 : Blo 864565 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B2467027 : Blo 864565 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1386089 : Blo 864565 1386089 := bstep (se 2 (by rfl) ⟨519783, by rfl⟩ : syracuseStep 1386089 = 1039567) B1039567
theorem B5547635 : Blo 864565 5547635 := bstep (se 1 (by rfl) ⟨4160726, by rfl⟩ : syracuseStep 5547635 = 8321453) B8321453
theorem B2926205 : Blo 864565 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B2467655 : Blo 864565 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B3286939 : Blo 864565 3286939 := bstep (se 1 (by rfl) ⟨2465204, by rfl⟩ : syracuseStep 3286939 = 4930409) B4930409
theorem B6236129 : Blo 864565 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B2927123 : Blo 864565 2927123 := bstep (se 1 (by rfl) ⟨2195342, by rfl⟩ : syracuseStep 2927123 = 4390685) B4390685
theorem B15216133 : Blo 864565 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B19214567 : Blo 864565 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B5353943 : Blo 864565 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B864795 : Blo 864565 864795 := bstep (se 1 (by rfl) ⟨648596, by rfl⟩ : syracuseStep 864795 = 1297193) B1297193
theorem B864935 : Blo 864565 864935 := bstep (se 1 (by rfl) ⟨648701, by rfl⟩ : syracuseStep 864935 = 1297403) B1297403
theorem B9155267 : Blo 864565 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B864975 : Blo 864565 864975 := bstep (se 1 (by rfl) ⟨648731, by rfl⟩ : syracuseStep 864975 = 1297463) B1297463
theorem B865055 : Blo 864565 865055 := bstep (se 1 (by rfl) ⟨648791, by rfl⟩ : syracuseStep 865055 = 1297583) B1297583
theorem B1946537 : Blo 864565 1946537 := bstep (se 2 (by rfl) ⟨729951, by rfl⟩ : syracuseStep 1946537 = 1459903) B1459903
theorem B865535 : Blo 864565 865535 := bstep (se 1 (by rfl) ⟨649151, by rfl⟩ : syracuseStep 865535 = 1298303) B1298303
theorem B865663 : Blo 864565 865663 := bstep (se 1 (by rfl) ⟨649247, by rfl⟩ : syracuseStep 865663 = 1298495) B1298495
theorem B3290615 : Blo 864565 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B865819 : Blo 864565 865819 := bstep (se 1 (by rfl) ⟨649364, by rfl⟩ : syracuseStep 865819 = 1298729) B1298729
theorem B2930255 : Blo 864565 2930255 := bstep (se 1 (by rfl) ⟨2197691, by rfl⟩ : syracuseStep 2930255 = 4395383) B4395383
theorem B4929133 : Blo 864565 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B2602621 : Blo 864565 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B865999 : Blo 864565 865999 := bstep (se 1 (by rfl) ⟨649499, by rfl⟩ : syracuseStep 865999 = 1298999) B1298999
theorem B866239 : Blo 864565 866239 := bstep (se 1 (by rfl) ⟨649679, by rfl⟩ : syracuseStep 866239 = 1299359) B1299359
theorem B2930633 : Blo 864565 2930633 := bstep (se 2 (by rfl) ⟨1098987, by rfl⟩ : syracuseStep 2930633 = 2197975) B2197975
theorem B866367 : Blo 864565 866367 := bstep (se 1 (by rfl) ⟨649775, by rfl⟩ : syracuseStep 866367 = 1299551) B1299551
theorem B866407 : Blo 864565 866407 := bstep (se 1 (by rfl) ⟨649805, by rfl⟩ : syracuseStep 866407 = 1299611) B1299611
theorem B2930795 : Blo 864565 2930795 := bstep (se 1 (by rfl) ⟨2198096, by rfl⟩ : syracuseStep 2930795 = 4396193) B4396193
theorem B866863 : Blo 864565 866863 := bstep (se 1 (by rfl) ⟨650147, by rfl⟩ : syracuseStep 866863 = 1300295) B1300295
theorem B2079287 : Blo 864565 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B2636513 : Blo 864565 2636513 := bstep (se 2 (by rfl) ⟨988692, by rfl⟩ : syracuseStep 2636513 = 1977385) B1977385
theorem B867263 : Blo 864565 867263 := bstep (se 1 (by rfl) ⟨650447, by rfl⟩ : syracuseStep 867263 = 1300895) B1300895
theorem B867311 : Blo 864565 867311 := bstep (se 1 (by rfl) ⟨650483, by rfl⟩ : syracuseStep 867311 = 1300967) B1300967
theorem B2342009 : Blo 864565 2342009 := bstep (se 2 (by rfl) ⟨878253, by rfl⟩ : syracuseStep 2342009 = 1756507) B1756507
theorem B1948841 : Blo 864565 1948841 := bstep (se 2 (by rfl) ⟨730815, by rfl⟩ : syracuseStep 1948841 = 1461631) B1461631
theorem B11091167 : Blo 864565 11091167 := bstep (se 1 (by rfl) ⟨8318375, by rfl⟩ : syracuseStep 11091167 = 16636751) B16636751
theorem B2112839 : Blo 864565 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B867807 : Blo 864565 867807 := bstep (se 1 (by rfl) ⟨650855, by rfl⟩ : syracuseStep 867807 = 1301711) B1301711
theorem B867887 : Blo 864565 867887 := bstep (se 1 (by rfl) ⟨650915, by rfl⟩ : syracuseStep 867887 = 1301831) B1301831
theorem B867995 : Blo 864565 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B868091 : Blo 864565 868091 := bstep (se 1 (by rfl) ⟨651068, by rfl⟩ : syracuseStep 868091 = 1302137) B1302137
theorem B10534711 : Blo 864565 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B3948385 : Blo 864565 3948385 := bstep (se 2 (by rfl) ⟨1480644, by rfl⟩ : syracuseStep 3948385 = 2961289) B2961289
theorem B868255 : Blo 864565 868255 := bstep (se 1 (by rfl) ⟨651191, by rfl⟩ : syracuseStep 868255 = 1302383) B1302383
theorem B1949903 : Blo 864565 1949903 := bstep (se 1 (by rfl) ⟨1462427, by rfl⟩ : syracuseStep 1949903 = 2924855) B2924855
theorem B1753321 : Blo 864565 1753321 := bstep (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) B1314991
theorem B1755113 : Blo 864565 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B1951721 : Blo 864565 1951721 := bstep (se 2 (by rfl) ⟨731895, by rfl⟩ : syracuseStep 1951721 = 1463791) B1463791
theorem B7391513 : Blo 864565 7391513 := bstep (se 2 (by rfl) ⟨2771817, by rfl⟩ : syracuseStep 7391513 = 5543635) B5543635
theorem B1952207 : Blo 864565 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B1296875 : Blo 864565 1296875 := bstep (se 1 (by rfl) ⟨972656, by rfl⟩ : syracuseStep 1296875 = 1945313) B1945313
theorem B2771435 : Blo 864565 2771435 := bstep (se 1 (by rfl) ⟨2078576, by rfl⟩ : syracuseStep 2771435 = 4157153) B4157153
theorem B1952297 : Blo 864565 1952297 := bstep (se 2 (by rfl) ⟨732111, by rfl⟩ : syracuseStep 1952297 = 1464223) B1464223
theorem B2345555 : Blo 864565 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B1297115 : Blo 864565 1297115 := bstep (se 1 (by rfl) ⟨972836, by rfl⟩ : syracuseStep 1297115 = 1945673) B1945673
theorem B1297151 : Blo 864565 1297151 := bstep (se 1 (by rfl) ⟨972863, by rfl⟩ : syracuseStep 1297151 = 1945727) B1945727
theorem B4377725 : Blo 864565 4377725 := bstep (se 3 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 4377725 = 1641647) B1641647
theorem B5557373 : Blo 864565 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B1461415 : Blo 864565 1461415 := bstep (se 1 (by rfl) ⟨1096061, by rfl⟩ : syracuseStep 1461415 = 2192123) B2192123
theorem B2772319 : Blo 864565 2772319 := bstep (se 1 (by rfl) ⟨2079239, by rfl⟩ : syracuseStep 2772319 = 4158479) B4158479
theorem B1953179 : Blo 864565 1953179 := bstep (se 1 (by rfl) ⟨1464884, by rfl⟩ : syracuseStep 1953179 = 2929769) B2929769
theorem B1297871 : Blo 864565 1297871 := bstep (se 1 (by rfl) ⟨973403, by rfl⟩ : syracuseStep 1297871 = 1946807) B1946807
theorem B1297961 : Blo 864565 1297961 := bstep (se 2 (by rfl) ⟨486735, by rfl⟩ : syracuseStep 1297961 = 973471) B973471
theorem B1298255 : Blo 864565 1298255 := bstep (se 1 (by rfl) ⟨973691, by rfl⟩ : syracuseStep 1298255 = 1947383) B1947383
theorem B1298375 : Blo 864565 1298375 := bstep (se 1 (by rfl) ⟨973781, by rfl⟩ : syracuseStep 1298375 = 1947563) B1947563
theorem B1298459 : Blo 864565 1298459 := bstep (se 1 (by rfl) ⟨973844, by rfl⟩ : syracuseStep 1298459 = 1947689) B1947689
theorem B3297419 : Blo 864565 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B8310995 : Blo 864565 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B1298735 : Blo 864565 1298735 := bstep (se 1 (by rfl) ⟨974051, by rfl⟩ : syracuseStep 1298735 = 1948103) B1948103
theorem B1298843 : Blo 864565 1298843 := bstep (se 1 (by rfl) ⟨974132, by rfl⟩ : syracuseStep 1298843 = 1948265) B1948265
theorem B1298879 : Blo 864565 1298879 := bstep (se 1 (by rfl) ⟨974159, by rfl⟩ : syracuseStep 1298879 = 1948319) B1948319
theorem B1233343 : Blo 864565 1233343 := bstep (se 1 (by rfl) ⟨925007, by rfl⟩ : syracuseStep 1233343 = 1850015) B1850015
theorem B1298975 : Blo 864565 1298975 := bstep (se 1 (by rfl) ⟨974231, by rfl⟩ : syracuseStep 1298975 = 1948463) B1948463
theorem B2773561 : Blo 864565 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B2347631 : Blo 864565 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B1299263 : Blo 864565 1299263 := bstep (se 1 (by rfl) ⟨974447, by rfl⟩ : syracuseStep 1299263 = 1948895) B1948895
theorem B1299407 : Blo 864565 1299407 := bstep (se 1 (by rfl) ⟨974555, by rfl⟩ : syracuseStep 1299407 = 1949111) B1949111
theorem B1299497 : Blo 864565 1299497 := bstep (se 2 (by rfl) ⟨487311, by rfl⟩ : syracuseStep 1299497 = 974623) B974623
theorem B1299527 : Blo 864565 1299527 := bstep (se 1 (by rfl) ⟨974645, by rfl⟩ : syracuseStep 1299527 = 1949291) B1949291
theorem B1299707 : Blo 864565 1299707 := bstep (se 1 (by rfl) ⟨974780, by rfl⟩ : syracuseStep 1299707 = 1949561) B1949561
theorem B1299767 : Blo 864565 1299767 := bstep (se 1 (by rfl) ⟨974825, by rfl⟩ : syracuseStep 1299767 = 1949651) B1949651
theorem B1300073 : Blo 864565 1300073 := bstep (se 2 (by rfl) ⟨487527, by rfl⟩ : syracuseStep 1300073 = 975055) B975055
theorem B1234607 : Blo 864565 1234607 := bstep (se 1 (by rfl) ⟨925955, by rfl⟩ : syracuseStep 1234607 = 1851911) B1851911
theorem B1464041 : Blo 864565 1464041 := bstep (se 2 (by rfl) ⟨549015, by rfl⟩ : syracuseStep 1464041 = 1098031) B1098031
theorem B1300607 : Blo 864565 1300607 := bstep (se 1 (by rfl) ⟨975455, by rfl⟩ : syracuseStep 1300607 = 1950911) B1950911
theorem B8312993 : Blo 864565 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B1300703 : Blo 864565 1300703 := bstep (se 1 (by rfl) ⟨975527, by rfl⟩ : syracuseStep 1300703 = 1951055) B1951055
theorem B1300763 : Blo 864565 1300763 := bstep (se 1 (by rfl) ⟨975572, by rfl⟩ : syracuseStep 1300763 = 1951145) B1951145
theorem B973183 : Blo 864565 973183 := bstep (se 1 (by rfl) ⟨729887, by rfl⟩ : syracuseStep 973183 = 1459775) B1459775
theorem B1301087 : Blo 864565 1301087 := bstep (se 1 (by rfl) ⟨975815, by rfl⟩ : syracuseStep 1301087 = 1951631) B1951631
theorem B1301183 : Blo 864565 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B1301225 : Blo 864565 1301225 := bstep (se 2 (by rfl) ⟨487959, by rfl⟩ : syracuseStep 1301225 = 975919) B975919
theorem B1301351 : Blo 864565 1301351 := bstep (se 1 (by rfl) ⟨976013, by rfl⟩ : syracuseStep 1301351 = 1952027) B1952027
theorem B1301417 : Blo 864565 1301417 := bstep (se 2 (by rfl) ⟨488031, by rfl⟩ : syracuseStep 1301417 = 976063) B976063
theorem B1301567 : Blo 864565 1301567 := bstep (se 1 (by rfl) ⟨976175, by rfl⟩ : syracuseStep 1301567 = 1952351) B1952351
theorem B1301609 : Blo 864565 1301609 := bstep (se 2 (by rfl) ⟨488103, by rfl⟩ : syracuseStep 1301609 = 976207) B976207
theorem B1301735 : Blo 864565 1301735 := bstep (se 1 (by rfl) ⟨976301, by rfl⟩ : syracuseStep 1301735 = 1952603) B1952603
theorem B1465627 : Blo 864565 1465627 := bstep (se 1 (by rfl) ⟨1099220, by rfl⟩ : syracuseStep 1465627 = 2198441) B2198441
theorem B5561783 : Blo 864565 5561783 := bstep (se 1 (by rfl) ⟨4171337, by rfl⟩ : syracuseStep 5561783 = 8342675) B8342675
theorem B85614097 : Blo 864565 85614097 := bstep (se 2 (by rfl) ⟨32105286, by rfl⟩ : syracuseStep 85614097 = 64210573) B64210573
theorem B18243191 : Blo 864565 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B1302239 : Blo 864565 1302239 := bstep (se 1 (by rfl) ⟨976679, by rfl⟩ : syracuseStep 1302239 = 1953359) B1953359
theorem B1302569 : Blo 864565 1302569 := bstep (se 2 (by rfl) ⟨488463, by rfl⟩ : syracuseStep 1302569 = 976927) B976927
theorem B974911 : Blo 864565 974911 := bstep (se 1 (by rfl) ⟨731183, by rfl⟩ : syracuseStep 974911 = 1462367) B1462367
theorem B1302599 : Blo 864565 1302599 := bstep (se 1 (by rfl) ⟨976949, by rfl⟩ : syracuseStep 1302599 = 1953899) B1953899
theorem B1302635 : Blo 864565 1302635 := bstep (se 1 (by rfl) ⟨976976, by rfl⟩ : syracuseStep 1302635 = 1953953) B1953953
theorem B1302719 : Blo 864565 1302719 := bstep (se 1 (by rfl) ⟨977039, by rfl⟩ : syracuseStep 1302719 = 1954079) B1954079
theorem B2777303 : Blo 864565 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B2777483 : Blo 864565 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B10543517 : Blo 864565 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B22241789 : Blo 864565 22241789 := bstep (se 3 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 22241789 = 8340671) B8340671
theorem B7037675 : Blo 864565 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B10674953 : Blo 864565 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B39969611 : Blo 864565 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B975775 : Blo 864565 975775 := bstep (se 1 (by rfl) ⟨731831, by rfl⟩ : syracuseStep 975775 = 1463663) B1463663
theorem B3171361 : Blo 864565 3171361 := bstep (se 2 (by rfl) ⟨1189260, by rfl⟩ : syracuseStep 3171361 = 2378521) B2378521
theorem B3040591 : Blo 864565 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B2778943 : Blo 864565 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B2189339 : Blo 864565 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B11855933 : Blo 864565 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B3959293 : Blo 864565 3959293 := bstep (se 3 (by rfl) ⟨742367, by rfl⟩ : syracuseStep 3959293 = 1484735) B1484735
theorem B3009545 : Blo 864565 3009545 := bstep (se 2 (by rfl) ⟨1128579, by rfl⟩ : syracuseStep 3009545 = 2257159) B2257159
theorem B6581411 : Blo 864565 6581411 := bstep (se 1 (by rfl) ⟨4936058, by rfl⟩ : syracuseStep 6581411 = 9872117) B9872117
theorem B4944239 : Blo 864565 4944239 := bstep (se 1 (by rfl) ⟨3708179, by rfl⟩ : syracuseStep 4944239 = 7416359) B7416359
theorem B43381511 : Blo 864565 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B7107425 : Blo 864565 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B4158535 : Blo 864565 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B1668251 : Blo 864565 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B5928875 : Blo 864565 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B3700883 : Blo 864565 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B16021871 : Blo 864565 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B7010975 : Blo 864565 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B2194523 : Blo 864565 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B5274953 : Blo 864565 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B2227999 : Blo 864565 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B7406275 : Blo 864565 7406275 := bstep (se 1 (by rfl) ⟨5554706, by rfl⟩ : syracuseStep 7406275 = 11109413) B11109413
theorem B2196193 : Blo 864565 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B4228481 : Blo 864565 4228481 := bstep (se 2 (by rfl) ⟨1585680, by rfl⟩ : syracuseStep 4228481 = 3171361) B3171361
theorem B28116551 : Blo 864565 28116551 := bstep (se 1 (by rfl) ⟨21087413, by rfl⟩ : syracuseStep 28116551 = 42174827) B42174827
theorem B2918483 : Blo 864565 2918483 := bstep (se 1 (by rfl) ⟨2188862, by rfl⟩ : syracuseStep 2918483 = 4377725) B4377725
theorem B3704915 : Blo 864565 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B3705257 : Blo 864565 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B2198279 : Blo 864565 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B5540663 : Blo 864565 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B5279057 : Blo 864565 5279057 := bstep (se 2 (by rfl) ⟨1979646, by rfl⟩ : syracuseStep 5279057 = 3959293) B3959293
theorem B9375259 : Blo 864565 9375259 := bstep (se 1 (by rfl) ⟨7031444, by rfl⟩ : syracuseStep 9375259 = 14062889) B14062889
theorem B5541995 : Blo 864565 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B20288177 : Blo 864565 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B3707855 : Blo 864565 3707855 := bstep (se 1 (by rfl) ⟨2780891, by rfl⟩ : syracuseStep 3707855 = 5561783) B5561783
theorem B4691783 : Blo 864565 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B7116635 : Blo 864565 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B26646407 : Blo 864565 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1644457 : Blo 864565 1644457 := bstep (se 2 (by rfl) ⟨616671, by rfl⟩ : syracuseStep 1644457 = 1233343) B1233343
theorem B75110327 : Blo 864565 75110327 := bstep (se 1 (by rfl) ⟨56332745, by rfl⟩ : syracuseStep 75110327 = 112665491) B112665491
theorem B924059 : Blo 864565 924059 := bstep (se 1 (by rfl) ⟨693044, by rfl⟩ : syracuseStep 924059 = 1386089) B1386089
theorem B1645103 : Blo 864565 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B7903955 : Blo 864565 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B5544713 : Blo 864565 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B2006363 : Blo 864565 2006363 := bstep (se 1 (by rfl) ⟨1504772, by rfl⟩ : syracuseStep 2006363 = 3009545) B3009545
theorem B6103511 : Blo 864565 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B2467255 : Blo 864565 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B1386191 : Blo 864565 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B3516635 : Blo 864565 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B2337761 : Blo 864565 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B25668679 : Blo 864565 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B2469055 : Blo 864565 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B2338139 : Blo 864565 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B2928095 : Blo 864565 2928095 := bstep (se 1 (by rfl) ⟨2196071, by rfl⟩ : syracuseStep 2928095 = 4392143) B4392143
theorem B3124927 : Blo 864565 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B1945583 : Blo 864565 1945583 := bstep (se 1 (by rfl) ⟨1459187, by rfl⟩ : syracuseStep 1945583 = 2918375) B2918375
theorem B14037137 : Blo 864565 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B4927675 : Blo 864565 4927675 := bstep (se 1 (by rfl) ⟨3695756, by rfl⟩ : syracuseStep 4927675 = 7391513) B7391513
theorem B3289369 : Blo 864565 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B864583 : Blo 864565 864583 := bstep (se 1 (by rfl) ⟨648437, by rfl⟩ : syracuseStep 864583 = 1296875) B1296875
theorem B1847623 : Blo 864565 1847623 := bstep (se 1 (by rfl) ⟨1385717, by rfl⟩ : syracuseStep 1847623 = 2771435) B2771435
theorem B2470331 : Blo 864565 2470331 := bstep (se 1 (by rfl) ⟨1852748, by rfl⟩ : syracuseStep 2470331 = 3705497) B3705497
theorem B864743 : Blo 864565 864743 := bstep (se 1 (by rfl) ⟨648557, by rfl⟩ : syracuseStep 864743 = 1297115) B1297115
theorem B864767 : Blo 864565 864767 := bstep (se 1 (by rfl) ⟨648575, by rfl⟩ : syracuseStep 864767 = 1297151) B1297151
theorem B865247 : Blo 864565 865247 := bstep (se 1 (by rfl) ⟨648935, by rfl⟩ : syracuseStep 865247 = 1297871) B1297871
theorem B865307 : Blo 864565 865307 := bstep (se 1 (by rfl) ⟨648980, by rfl⟩ : syracuseStep 865307 = 1297961) B1297961
theorem B865503 : Blo 864565 865503 := bstep (se 1 (by rfl) ⟨649127, by rfl⟩ : syracuseStep 865503 = 1298255) B1298255
theorem B865583 : Blo 864565 865583 := bstep (se 1 (by rfl) ⟨649187, by rfl⟩ : syracuseStep 865583 = 1298375) B1298375
theorem B1946951 : Blo 864565 1946951 := bstep (se 1 (by rfl) ⟨1460213, by rfl⟩ : syracuseStep 1946951 = 2920427) B2920427
theorem B865639 : Blo 864565 865639 := bstep (se 1 (by rfl) ⟨649229, by rfl⟩ : syracuseStep 865639 = 1298459) B1298459
theorem B865823 : Blo 864565 865823 := bstep (se 1 (by rfl) ⟨649367, by rfl⟩ : syracuseStep 865823 = 1298735) B1298735
theorem B865895 : Blo 864565 865895 := bstep (se 1 (by rfl) ⟨649421, by rfl⟩ : syracuseStep 865895 = 1298843) B1298843
theorem B865919 : Blo 864565 865919 := bstep (se 1 (by rfl) ⟨649439, by rfl⟩ : syracuseStep 865919 = 1298879) B1298879
theorem B865983 : Blo 864565 865983 := bstep (se 1 (by rfl) ⟨649487, by rfl⟩ : syracuseStep 865983 = 1298975) B1298975
theorem B2930471 : Blo 864565 2930471 := bstep (se 1 (by rfl) ⟨2197853, by rfl⟩ : syracuseStep 2930471 = 4395707) B4395707
theorem B866175 : Blo 864565 866175 := bstep (se 1 (by rfl) ⟨649631, by rfl⟩ : syracuseStep 866175 = 1299263) B1299263
theorem B866271 : Blo 864565 866271 := bstep (se 1 (by rfl) ⟨649703, by rfl⟩ : syracuseStep 866271 = 1299407) B1299407
theorem B866331 : Blo 864565 866331 := bstep (se 1 (by rfl) ⟨649748, by rfl⟩ : syracuseStep 866331 = 1299497) B1299497
theorem B866351 : Blo 864565 866351 := bstep (se 1 (by rfl) ⟨649763, by rfl⟩ : syracuseStep 866351 = 1299527) B1299527
theorem B866471 : Blo 864565 866471 := bstep (se 1 (by rfl) ⟨649853, by rfl⟩ : syracuseStep 866471 = 1299707) B1299707
theorem B866511 : Blo 864565 866511 := bstep (se 1 (by rfl) ⟨649883, by rfl⟩ : syracuseStep 866511 = 1299767) B1299767
theorem B2930903 : Blo 864565 2930903 := bstep (se 1 (by rfl) ⟨2198177, by rfl⟩ : syracuseStep 2930903 = 4396355) B4396355
theorem B866715 : Blo 864565 866715 := bstep (se 1 (by rfl) ⟨650036, by rfl⟩ : syracuseStep 866715 = 1300073) B1300073
theorem B1096411 : Blo 864565 1096411 := bstep (se 1 (by rfl) ⟨822308, by rfl⟩ : syracuseStep 1096411 = 1644617) B1644617
theorem B867071 : Blo 864565 867071 := bstep (se 1 (by rfl) ⟨650303, by rfl⟩ : syracuseStep 867071 = 1300607) B1300607
theorem B867135 : Blo 864565 867135 := bstep (se 1 (by rfl) ⟨650351, by rfl⟩ : syracuseStep 867135 = 1300703) B1300703
theorem B867175 : Blo 864565 867175 := bstep (se 1 (by rfl) ⟨650381, by rfl⟩ : syracuseStep 867175 = 1300763) B1300763
theorem B1948553 : Blo 864565 1948553 := bstep (se 2 (by rfl) ⟨730707, by rfl⟩ : syracuseStep 1948553 = 1461415) B1461415
theorem B1948607 : Blo 864565 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B867391 : Blo 864565 867391 := bstep (se 1 (by rfl) ⟨650543, by rfl⟩ : syracuseStep 867391 = 1301087) B1301087
theorem B3292285 : Blo 864565 3292285 := bstep (se 3 (by rfl) ⟨617303, by rfl⟩ : syracuseStep 3292285 = 1234607) B1234607
theorem B867455 : Blo 864565 867455 := bstep (se 1 (by rfl) ⟨650591, by rfl⟩ : syracuseStep 867455 = 1301183) B1301183
theorem B867483 : Blo 864565 867483 := bstep (se 1 (by rfl) ⟨650612, by rfl⟩ : syracuseStep 867483 = 1301225) B1301225
theorem B1948859 : Blo 864565 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B867567 : Blo 864565 867567 := bstep (se 1 (by rfl) ⟨650675, by rfl⟩ : syracuseStep 867567 = 1301351) B1301351
theorem B867611 : Blo 864565 867611 := bstep (se 1 (by rfl) ⟨650708, by rfl⟩ : syracuseStep 867611 = 1301417) B1301417
theorem B867711 : Blo 864565 867711 := bstep (se 1 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 867711 = 1301567) B1301567
theorem B867739 : Blo 864565 867739 := bstep (se 1 (by rfl) ⟨650804, by rfl⟩ : syracuseStep 867739 = 1301609) B1301609
theorem B867823 : Blo 864565 867823 := bstep (se 1 (by rfl) ⟨650867, by rfl⟩ : syracuseStep 867823 = 1301735) B1301735
theorem B7388779 : Blo 864565 7388779 := bstep (se 1 (by rfl) ⟨5541584, by rfl⟩ : syracuseStep 7388779 = 11083169) B11083169
theorem B1097383 : Blo 864565 1097383 := bstep (se 1 (by rfl) ⟨823037, by rfl⟩ : syracuseStep 1097383 = 1646075) B1646075
theorem B868159 : Blo 864565 868159 := bstep (se 1 (by rfl) ⟨651119, by rfl⟩ : syracuseStep 868159 = 1302239) B1302239
theorem B868379 : Blo 864565 868379 := bstep (se 1 (by rfl) ⟨651284, by rfl⟩ : syracuseStep 868379 = 1302569) B1302569
theorem B868399 : Blo 864565 868399 := bstep (se 1 (by rfl) ⟨651299, by rfl⟩ : syracuseStep 868399 = 1302599) B1302599
theorem B868423 : Blo 864565 868423 := bstep (se 1 (by rfl) ⟨651317, by rfl⟩ : syracuseStep 868423 = 1302635) B1302635
theorem B868479 : Blo 864565 868479 := bstep (se 1 (by rfl) ⟨651359, by rfl⟩ : syracuseStep 868479 = 1302719) B1302719
theorem B1851535 : Blo 864565 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B1851655 : Blo 864565 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B7029011 : Blo 864565 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B14827859 : Blo 864565 14827859 := bstep (se 1 (by rfl) ⟨11120894, by rfl⟩ : syracuseStep 14827859 = 22241789) B22241789
theorem B37962341 : Blo 864565 37962341 := bstep (se 4 (by rfl) ⟨3558969, by rfl⟩ : syracuseStep 37962341 = 7117939) B7117939
theorem B1950803 : Blo 864565 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B1459559 : Blo 864565 1459559 := bstep (se 1 (by rfl) ⟨1094669, by rfl⟩ : syracuseStep 1459559 = 2189339) B2189339
theorem B1951415 : Blo 864565 1951415 := bstep (se 1 (by rfl) ⟨1463561, by rfl⟩ : syracuseStep 1951415 = 2927123) B2927123
theorem B18695933 : Blo 864565 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B6572177 : Blo 864565 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B3296159 : Blo 864565 3296159 := bstep (se 1 (by rfl) ⟨2472119, by rfl⟩ : syracuseStep 3296159 = 4944239) B4944239
theorem B1297577 : Blo 864565 1297577 := bstep (se 2 (by rfl) ⟨486591, by rfl⟩ : syracuseStep 1297577 = 973183) B973183
theorem B28921007 : Blo 864565 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B4738283 : Blo 864565 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B1297691 : Blo 864565 1297691 := bstep (se 1 (by rfl) ⟨973268, by rfl⟩ : syracuseStep 1297691 = 1946537) B1946537
theorem B1953503 : Blo 864565 1953503 := bstep (se 1 (by rfl) ⟨1465127, by rfl⟩ : syracuseStep 1953503 = 2930255) B2930255
theorem B3952583 : Blo 864565 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B1953755 : Blo 864565 1953755 := bstep (se 1 (by rfl) ⟨1465316, by rfl⟩ : syracuseStep 1953755 = 2930633) B2930633
theorem B1953863 : Blo 864565 1953863 := bstep (se 1 (by rfl) ⟨1465397, by rfl⟩ : syracuseStep 1953863 = 2930795) B2930795
theorem B4378697 : Blo 864565 4378697 := bstep (se 2 (by rfl) ⟨1642011, by rfl⟩ : syracuseStep 4378697 = 3284023) B3284023
theorem B48648509 : Blo 864565 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B1954169 : Blo 864565 1954169 := bstep (se 2 (by rfl) ⟨732813, by rfl⟩ : syracuseStep 1954169 = 1465627) B1465627
theorem B1757675 : Blo 864565 1757675 := bstep (se 1 (by rfl) ⟨1318256, by rfl⟩ : syracuseStep 1757675 = 2636513) B2636513
theorem B114152129 : Blo 864565 114152129 := bstep (se 2 (by rfl) ⟨42807048, by rfl⟩ : syracuseStep 114152129 = 85614097) B85614097
theorem B1463015 : Blo 864565 1463015 := bstep (se 1 (by rfl) ⟨1097261, by rfl⟩ : syracuseStep 1463015 = 2194523) B2194523
theorem B1561339 : Blo 864565 1561339 := bstep (se 1 (by rfl) ⟨1171004, by rfl⟩ : syracuseStep 1561339 = 2342009) B2342009
theorem B1299227 : Blo 864565 1299227 := bstep (se 1 (by rfl) ⟨974420, by rfl⟩ : syracuseStep 1299227 = 1948841) B1948841
theorem B7394111 : Blo 864565 7394111 := bstep (se 1 (by rfl) ⟨5545583, by rfl⟩ : syracuseStep 7394111 = 11091167) B11091167
theorem B2970665 : Blo 864565 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B14046281 : Blo 864565 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B5264513 : Blo 864565 5264513 := bstep (se 2 (by rfl) ⟨1974192, by rfl⟩ : syracuseStep 5264513 = 3948385) B3948385
theorem B7394489 : Blo 864565 7394489 := bstep (se 2 (by rfl) ⟨2772933, by rfl⟩ : syracuseStep 7394489 = 5545867) B5545867
theorem B1299881 : Blo 864565 1299881 := bstep (se 2 (by rfl) ⟨487455, by rfl⟩ : syracuseStep 1299881 = 974911) B974911
theorem B1299935 : Blo 864565 1299935 := bstep (se 1 (by rfl) ⟨974951, by rfl⟩ : syracuseStep 1299935 = 1949903) B1949903
theorem B4675283 : Blo 864565 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B3758375 : Blo 864565 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B1464655 : Blo 864565 1464655 := bstep (se 1 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 1464655 = 2196983) B2196983
theorem B1301033 : Blo 864565 1301033 := bstep (se 2 (by rfl) ⟨487887, by rfl⟩ : syracuseStep 1301033 = 975775) B975775
theorem B14277181 : Blo 864565 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B1301147 : Blo 864565 1301147 := bstep (se 1 (by rfl) ⟨975860, by rfl⟩ : syracuseStep 1301147 = 1951721) B1951721
theorem B5003963 : Blo 864565 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1465067 : Blo 864565 1465067 := bstep (se 1 (by rfl) ⟨1098800, by rfl⟩ : syracuseStep 1465067 = 2197601) B2197601
theorem B1301471 : Blo 864565 1301471 := bstep (se 1 (by rfl) ⟨976103, by rfl⟩ : syracuseStep 1301471 = 1952207) B1952207
theorem B1301531 : Blo 864565 1301531 := bstep (se 1 (by rfl) ⟨976148, by rfl⟩ : syracuseStep 1301531 = 1952297) B1952297
theorem B2776123 : Blo 864565 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B4054121 : Blo 864565 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B1465499 : Blo 864565 1465499 := bstep (se 1 (by rfl) ⟨1099124, by rfl⟩ : syracuseStep 1465499 = 2198249) B2198249
theorem B1465607 : Blo 864565 1465607 := bstep (se 1 (by rfl) ⟨1099205, by rfl⟩ : syracuseStep 1465607 = 2198411) B2198411
theorem B1302119 : Blo 864565 1302119 := bstep (se 1 (by rfl) ⟨976589, by rfl⟩ : syracuseStep 1302119 = 1953179) B1953179
theorem B4382585 : Blo 864565 4382585 := bstep (se 2 (by rfl) ⟨1643469, by rfl⟩ : syracuseStep 4382585 = 3286939) B3286939
theorem B6250891 : Blo 864565 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B1565087 : Blo 864565 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B27812555 : Blo 864565 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B4940615 : Blo 864565 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B4678481 : Blo 864565 4678481 := bstep (se 2 (by rfl) ⟨1754430, by rfl⟩ : syracuseStep 4678481 = 3508861) B3508861
theorem B9856079 : Blo 864565 9856079 := bstep (se 1 (by rfl) ⟨7392059, by rfl⟩ : syracuseStep 9856079 = 14784119) B14784119
theorem B976027 : Blo 864565 976027 := bstep (se 1 (by rfl) ⟨732020, by rfl⟩ : syracuseStep 976027 = 1464041) B1464041
theorem B3696425 : Blo 864565 3696425 := bstep (se 2 (by rfl) ⟨1386159, by rfl⟩ : syracuseStep 3696425 = 2772319) B2772319
theorem B2189227 : Blo 864565 2189227 := bstep (se 1 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 2189227 = 3283841) B3283841
theorem B4221355 : Blo 864565 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B4680301 : Blo 864565 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B2190665 : Blo 864565 2190665 := bstep (se 2 (by rfl) ⟨821499, by rfl⟩ : syracuseStep 2190665 = 1642999) B1642999
theorem B3698081 : Blo 864565 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B3698423 : Blo 864565 3698423 := bstep (se 1 (by rfl) ⟨2773817, by rfl⟩ : syracuseStep 3698423 = 5547635) B5547635
theorem B4157419 : Blo 864565 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B11104289 : Blo 864565 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B6254813 : Blo 864565 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B4387607 : Blo 864565 4387607 := bstep (se 1 (by rfl) ⟨3290705, by rfl⟩ : syracuseStep 4387607 = 6581411) B6581411
theorem B3470161 : Blo 864565 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B12809711 : Blo 864565 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B1112167 : Blo 864565 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B2193743 : Blo 864565 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B10681247 : Blo 864565 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1408559 : Blo 864565 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B4686007 : Blo 864565 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B18744367 : Blo 864565 18744367 := bstep (se 1 (by rfl) ⟨14058275, by rfl⟩ : syracuseStep 18744367 = 28116551) B28116551
theorem B2197439 : Blo 864565 2197439 := bstep (se 1 (by rfl) ⟨1648079, by rfl⟩ : syracuseStep 2197439 = 3296159) B3296159
theorem B2918969 : Blo 864565 2918969 := bstep (se 2 (by rfl) ⟨1094613, by rfl⟩ : syracuseStep 2918969 = 2189227) B2189227
theorem B2919131 : Blo 864565 2919131 := bstep (se 1 (by rfl) ⟨2189348, by rfl⟩ : syracuseStep 2919131 = 4378697) B4378697
theorem B3509675 : Blo 864565 3509675 := bstep (se 1 (by rfl) ⟨2632256, by rfl⟩ : syracuseStep 3509675 = 5264513) B5264513
theorem B11275949 : Blo 864565 11275949 := bstep (se 3 (by rfl) ⟨2114240, by rfl⟩ : syracuseStep 11275949 = 4228481) B4228481
theorem B3116855 : Blo 864565 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B17764271 : Blo 864565 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B50073551 : Blo 864565 50073551 := bstep (se 1 (by rfl) ⟨37555163, by rfl⟩ : syracuseStep 50073551 = 75110327) B75110327
theorem B4166569 : Blo 864565 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B2921723 : Blo 864565 2921723 := bstep (se 1 (by rfl) ⟨2191292, by rfl⟩ : syracuseStep 2921723 = 4382585) B4382585
theorem B5543225 : Blo 864565 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B4069007 : Blo 864565 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B2463497 : Blo 864565 2463497 := bstep (se 2 (by rfl) ⟨923811, by rfl⟩ : syracuseStep 2463497 = 1847623) B1847623
theorem B3118987 : Blo 864565 3118987 := bstep (se 1 (by rfl) ⟨2339240, by rfl⟩ : syracuseStep 3118987 = 4678481) B4678481
theorem B2464157 : Blo 864565 2464157 := bstep (se 3 (by rfl) ⟨462029, by rfl⟩ : syracuseStep 2464157 = 924059) B924059
theorem B4626881 : Blo 864565 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B2464283 : Blo 864565 2464283 := bstep (se 1 (by rfl) ⟨1848212, by rfl⟩ : syracuseStep 2464283 = 3696425) B3696425
theorem B2465387 : Blo 864565 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B2465615 : Blo 864565 2465615 := bstep (se 1 (by rfl) ⟨1849211, by rfl⟩ : syracuseStep 2465615 = 3698423) B3698423
theorem B6234029 : Blo 864565 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B1482889 : Blo 864565 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B4169875 : Blo 864565 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B1646887 : Blo 864565 1646887 := bstep (se 1 (by rfl) ⟨1235165, by rfl⟩ : syracuseStep 1646887 = 2470331) B2470331
theorem B2925071 : Blo 864565 2925071 := bstep (se 1 (by rfl) ⟨2193803, by rfl⟩ : syracuseStep 2925071 = 4387607) B4387607
theorem B7120831 : Blo 864565 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B2468713 : Blo 864565 2468713 := bstep (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) B1851535
theorem B2468873 : Blo 864565 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B25308227 : Blo 864565 25308227 := bstep (se 1 (by rfl) ⟨18981170, by rfl⟩ : syracuseStep 25308227 = 37962341) B37962341
theorem B8334521 : Blo 864565 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B9875033 : Blo 864565 9875033 := bstep (se 2 (by rfl) ⟨3703137, by rfl⟩ : syracuseStep 9875033 = 7406275) B7406275
theorem B2928257 : Blo 864565 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B12463955 : Blo 864565 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1945655 : Blo 864565 1945655 := bstep (se 1 (by rfl) ⟨1459241, by rfl⟩ : syracuseStep 1945655 = 2918483) B2918483
theorem B2469943 : Blo 864565 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B2470171 : Blo 864565 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B3289673 : Blo 864565 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B865051 : Blo 864565 865051 := bstep (se 1 (by rfl) ⟨648788, by rfl⟩ : syracuseStep 865051 = 1297577) B1297577
theorem B3158855 : Blo 864565 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B865127 : Blo 864565 865127 := bstep (se 1 (by rfl) ⟨648845, by rfl⟩ : syracuseStep 865127 = 1297691) B1297691
theorem B3519371 : Blo 864565 3519371 := bstep (se 1 (by rfl) ⟨2639528, by rfl⟩ : syracuseStep 3519371 = 5279057) B5279057
theorem B2635055 : Blo 864565 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B76101419 : Blo 864565 76101419 := bstep (se 1 (by rfl) ⟨57076064, by rfl⟩ : syracuseStep 76101419 = 114152129) B114152129
theorem B866151 : Blo 864565 866151 := bstep (se 1 (by rfl) ⟨649613, by rfl⟩ : syracuseStep 866151 = 1299227) B1299227
theorem B4929407 : Blo 864565 4929407 := bstep (se 1 (by rfl) ⟨3697055, by rfl⟩ : syracuseStep 4929407 = 7394111) B7394111
theorem B2471903 : Blo 864565 2471903 := bstep (se 1 (by rfl) ⟨1853927, by rfl⟩ : syracuseStep 2471903 = 3707855) B3707855
theorem B1980443 : Blo 864565 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B4929659 : Blo 864565 4929659 := bstep (se 1 (by rfl) ⟨3697244, by rfl⟩ : syracuseStep 4929659 = 7394489) B7394489
theorem B6240401 : Blo 864565 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B866587 : Blo 864565 866587 := bstep (se 1 (by rfl) ⟨649940, by rfl⟩ : syracuseStep 866587 = 1299881) B1299881
theorem B866623 : Blo 864565 866623 := bstep (se 1 (by rfl) ⟨649967, by rfl⟩ : syracuseStep 866623 = 1299935) B1299935
theorem B3127855 : Blo 864565 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B34159229 : Blo 864565 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B34224905 : Blo 864565 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B2505583 : Blo 864565 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B3292073 : Blo 864565 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B16694261 : Blo 864565 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B867355 : Blo 864565 867355 := bstep (se 1 (by rfl) ⟨650516, by rfl⟩ : syracuseStep 867355 = 1301033) B1301033
theorem B1096735 : Blo 864565 1096735 := bstep (se 1 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 1096735 = 1645103) B1645103
theorem B867431 : Blo 864565 867431 := bstep (se 1 (by rfl) ⟨650573, by rfl⟩ : syracuseStep 867431 = 1301147) B1301147
theorem B867647 : Blo 864565 867647 := bstep (se 1 (by rfl) ⟨650735, by rfl⟩ : syracuseStep 867647 = 1301471) B1301471
theorem B867687 : Blo 864565 867687 := bstep (se 1 (by rfl) ⟨650765, by rfl⟩ : syracuseStep 867687 = 1301531) B1301531
theorem B12500345 : Blo 864565 12500345 := bstep (se 2 (by rfl) ⟨4687629, by rfl⟩ : syracuseStep 12500345 = 9375259) B9375259
theorem B2702747 : Blo 864565 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B868079 : Blo 864565 868079 := bstep (se 1 (by rfl) ⟨651059, by rfl⟩ : syracuseStep 868079 = 1302119) B1302119
theorem B6570233 : Blo 864565 6570233 := bstep (se 2 (by rfl) ⟨2463837, by rfl⟩ : syracuseStep 6570233 = 4927675) B4927675
theorem B15024629 : Blo 864565 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B3293743 : Blo 864565 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B6570719 : Blo 864565 6570719 := bstep (se 1 (by rfl) ⟨4928039, by rfl⟩ : syracuseStep 6570719 = 9856079) B9856079
theorem B2081785 : Blo 864565 2081785 := bstep (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) B1561339
theorem B2344423 : Blo 864565 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B1460443 : Blo 864565 1460443 := bstep (se 1 (by rfl) ⟨1095332, by rfl⟩ : syracuseStep 1460443 = 2190665) B2190665
theorem B1558759 : Blo 864565 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B1952063 : Blo 864565 1952063 := bstep (se 1 (by rfl) ⟨1464047, by rfl⟩ : syracuseStep 1952063 = 2928095) B2928095
theorem B1297055 : Blo 864565 1297055 := bstep (se 1 (by rfl) ⟨972791, by rfl⟩ : syracuseStep 1297055 = 1945583) B1945583
theorem B9358091 : Blo 864565 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B1952873 : Blo 864565 1952873 := bstep (se 2 (by rfl) ⟨732327, by rfl⟩ : syracuseStep 1952873 = 1464655) B1464655
theorem B77122685 : Blo 864565 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B1297967 : Blo 864565 1297967 := bstep (se 1 (by rfl) ⟨973475, by rfl⟩ : syracuseStep 1297967 = 1946951) B1946951
theorem B1461881 : Blo 864565 1461881 := bstep (se 2 (by rfl) ⟨548205, by rfl⟩ : syracuseStep 1461881 = 1096411) B1096411
theorem B1953647 : Blo 864565 1953647 := bstep (se 1 (by rfl) ⟨1465235, by rfl⟩ : syracuseStep 1953647 = 2930471) B2930471
theorem B1953935 : Blo 864565 1953935 := bstep (se 1 (by rfl) ⟨1465451, by rfl⟩ : syracuseStep 1953935 = 2930903) B2930903
theorem B1462495 : Blo 864565 1462495 := bstep (se 1 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 1462495 = 2193743) B2193743
theorem B1299035 : Blo 864565 1299035 := bstep (se 1 (by rfl) ⟨974276, by rfl⟩ : syracuseStep 1299035 = 1948553) B1948553
theorem B1299071 : Blo 864565 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B1299239 : Blo 864565 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B9851705 : Blo 864565 9851705 := bstep (se 2 (by rfl) ⟨3694389, by rfl⟩ : syracuseStep 9851705 = 7388779) B7388779
theorem B1463177 : Blo 864565 1463177 := bstep (se 2 (by rfl) ⟨548691, by rfl⟩ : syracuseStep 1463177 = 1097383) B1097383
theorem B9885239 : Blo 864565 9885239 := bstep (se 1 (by rfl) ⟨7413929, by rfl⟩ : syracuseStep 9885239 = 14827859) B14827859
theorem B1300535 : Blo 864565 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B973039 : Blo 864565 973039 := bstep (se 1 (by rfl) ⟨729779, by rfl⟩ : syracuseStep 973039 = 1459559) B1459559
theorem B1300943 : Blo 864565 1300943 := bstep (se 1 (by rfl) ⟨975707, by rfl⟩ : syracuseStep 1300943 = 1951415) B1951415
theorem B4381451 : Blo 864565 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1301369 : Blo 864565 1301369 := bstep (se 2 (by rfl) ⟨488013, by rfl⟩ : syracuseStep 1301369 = 976027) B976027
theorem B1465519 : Blo 864565 1465519 := bstep (se 1 (by rfl) ⟨1099139, by rfl⟩ : syracuseStep 1465519 = 2198279) B2198279
theorem B3693775 : Blo 864565 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B1302335 : Blo 864565 1302335 := bstep (se 1 (by rfl) ⟨976751, by rfl⟩ : syracuseStep 1302335 = 1953503) B1953503
theorem B1302503 : Blo 864565 1302503 := bstep (se 1 (by rfl) ⟨976877, by rfl⟩ : syracuseStep 1302503 = 1953755) B1953755
theorem B1302575 : Blo 864565 1302575 := bstep (se 1 (by rfl) ⟨976931, by rfl⟩ : syracuseStep 1302575 = 1953863) B1953863
theorem B3694663 : Blo 864565 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B32432339 : Blo 864565 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B1302779 : Blo 864565 1302779 := bstep (se 1 (by rfl) ⟨977084, by rfl⟩ : syracuseStep 1302779 = 1954169) B1954169
theorem B1171783 : Blo 864565 1171783 := bstep (se 1 (by rfl) ⟨878837, by rfl⟩ : syracuseStep 1171783 = 1757675) B1757675
theorem B13525451 : Blo 864565 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B975343 : Blo 864565 975343 := bstep (se 1 (by rfl) ⟨731507, by rfl⟩ : syracuseStep 975343 = 1463015) B1463015
theorem B5628473 : Blo 864565 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B9364187 : Blo 864565 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B4744423 : Blo 864565 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B3335975 : Blo 864565 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B5269303 : Blo 864565 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B976711 : Blo 864565 976711 := bstep (se 1 (by rfl) ⟨732533, by rfl⟩ : syracuseStep 976711 = 1465067) B1465067
theorem B3696475 : Blo 864565 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B3696509 : Blo 864565 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B976999 : Blo 864565 976999 := bstep (se 1 (by rfl) ⟨732749, by rfl⟩ : syracuseStep 976999 = 1465499) B1465499
theorem B977071 : Blo 864565 977071 := bstep (se 1 (by rfl) ⟨732803, by rfl⟩ : syracuseStep 977071 = 1465607) B1465607
theorem B1337575 : Blo 864565 1337575 := bstep (se 1 (by rfl) ⟨1003181, by rfl⟩ : syracuseStep 1337575 = 2006363) B2006363
theorem B14805989 : Blo 864565 14805989 := bstep (se 4 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 14805989 = 2776123) B2776123
theorem B4385825 : Blo 864565 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B18541703 : Blo 864565 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B2192609 : Blo 864565 2192609 := bstep (se 2 (by rfl) ⟨822228, by rfl⟩ : syracuseStep 2192609 = 1644457) B1644457
theorem B7402859 : Blo 864565 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B19036241 : Blo 864565 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B4389713 : Blo 864565 4389713 := bstep (se 2 (by rfl) ⟨1646142, by rfl⟩ : syracuseStep 4389713 = 3292285) B3292285
theorem B2195849 : Blo 864565 2195849 := bstep (se 2 (by rfl) ⟨823443, by rfl⟩ : syracuseStep 2195849 = 1646887) B1646887
theorem B4391657 : Blo 864565 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B6325897 : Blo 864565 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B24971165 : Blo 864565 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B51415123 : Blo 864565 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B6590159 : Blo 864565 6590159 := bstep (se 1 (by rfl) ⟨4942619, by rfl⟩ : syracuseStep 6590159 = 9885239) B9885239
theorem B1642331 : Blo 864565 1642331 := bstep (se 1 (by rfl) ⟨1231748, by rfl⟩ : syracuseStep 1642331 = 2463497) B2463497
theorem B1642771 : Blo 864565 1642771 := bstep (se 1 (by rfl) ⟨1232078, by rfl⟩ : syracuseStep 1642771 = 2464157) B2464157
theorem B3084587 : Blo 864565 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B1642855 : Blo 864565 1642855 := bstep (se 1 (by rfl) ⟨1232141, by rfl⟩ : syracuseStep 1642855 = 2464283) B2464283
theorem B2920967 : Blo 864565 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1643591 : Blo 864565 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B1643743 : Blo 864565 1643743 := bstep (se 1 (by rfl) ⟨1232807, by rfl⟩ : syracuseStep 1643743 = 2465615) B2465615
theorem B9016967 : Blo 864565 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B2464339 : Blo 864565 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B9870659 : Blo 864565 9870659 := bstep (se 1 (by rfl) ⟨7402994, by rfl⟩ : syracuseStep 9870659 = 14805989) B14805989
theorem B1645915 : Blo 864565 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B2923883 : Blo 864565 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B12361135 : Blo 864565 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B2105903 : Blo 864565 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B4170473 : Blo 864565 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B50734279 : Blo 864565 50734279 := bstep (se 1 (by rfl) ⟨38050709, by rfl⟩ : syracuseStep 50734279 = 76101419) B76101419
theorem B3286271 : Blo 864565 3286271 := bstep (se 1 (by rfl) ⟨2464703, by rfl⟩ : syracuseStep 3286271 = 4929407) B4929407
theorem B1647935 : Blo 864565 1647935 := bstep (se 1 (by rfl) ⟨1235951, by rfl⟩ : syracuseStep 1647935 = 2471903) B2471903
theorem B1320295 : Blo 864565 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B12690827 : Blo 864565 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B3286439 : Blo 864565 3286439 := bstep (se 1 (by rfl) ⟨2464829, by rfl⟩ : syracuseStep 3286439 = 4929659) B4929659
theorem B4925033 : Blo 864565 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B22816603 : Blo 864565 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B2926475 : Blo 864565 2926475 := bstep (se 1 (by rfl) ⟨2194856, by rfl⟩ : syracuseStep 2926475 = 4389713) B4389713
theorem B8333563 : Blo 864565 8333563 := bstep (se 1 (by rfl) ⟨6250172, by rfl⟩ : syracuseStep 8333563 = 12500345) B12500345
theorem B4926217 : Blo 864565 4926217 := bstep (se 2 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 4926217 = 3694663) B3694663
theorem B1977185 : Blo 864565 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B86486237 : Blo 864565 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B1945979 : Blo 864565 1945979 := bstep (se 1 (by rfl) ⟨1459484, by rfl⟩ : syracuseStep 1945979 = 2918969) B2918969
theorem B864703 : Blo 864565 864703 := bstep (se 1 (by rfl) ⟨648527, by rfl⟩ : syracuseStep 864703 = 1297055) B1297055
theorem B1946087 : Blo 864565 1946087 := bstep (se 1 (by rfl) ⟨1459565, by rfl⟩ : syracuseStep 1946087 = 2919131) B2919131
theorem B6238727 : Blo 864565 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B3125897 : Blo 864565 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B2339783 : Blo 864565 2339783 := bstep (se 1 (by rfl) ⟨1754837, by rfl⟩ : syracuseStep 2339783 = 3509675) B3509675
theorem B865311 : Blo 864565 865311 := bstep (se 1 (by rfl) ⟨648983, by rfl⟩ : syracuseStep 865311 = 1297967) B1297967
theorem B7517299 : Blo 864565 7517299 := bstep (se 1 (by rfl) ⟨5637974, by rfl⟩ : syracuseStep 7517299 = 11275949) B11275949
theorem B4928633 : Blo 864565 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B2077903 : Blo 864565 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B11842847 : Blo 864565 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B1947257 : Blo 864565 1947257 := bstep (se 2 (by rfl) ⟨730221, by rfl⟩ : syracuseStep 1947257 = 1460443) B1460443
theorem B2078345 : Blo 864565 2078345 := bstep (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) B1558759
theorem B1783433 : Blo 864565 1783433 := bstep (se 2 (by rfl) ⟨668787, by rfl⟩ : syracuseStep 1783433 = 1337575) B1337575
theorem B866023 : Blo 864565 866023 := bstep (se 1 (by rfl) ⟨649517, by rfl⟩ : syracuseStep 866023 = 1299035) B1299035
theorem B866047 : Blo 864565 866047 := bstep (se 1 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 866047 = 1299071) B1299071
theorem B866159 : Blo 864565 866159 := bstep (se 1 (by rfl) ⟨649619, by rfl⟩ : syracuseStep 866159 = 1299239) B1299239
theorem B6567803 : Blo 864565 6567803 := bstep (se 1 (by rfl) ⟨4925852, by rfl⟩ : syracuseStep 6567803 = 9851705) B9851705
theorem B1947815 : Blo 864565 1947815 := bstep (se 1 (by rfl) ⟨1460861, by rfl⟩ : syracuseStep 1947815 = 2921723) B2921723
theorem B3291617 : Blo 864565 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B867023 : Blo 864565 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B867295 : Blo 864565 867295 := bstep (se 1 (by rfl) ⟨650471, by rfl⟩ : syracuseStep 867295 = 1300943) B1300943
theorem B867579 : Blo 864565 867579 := bstep (se 1 (by rfl) ⟨650684, by rfl⟩ : syracuseStep 867579 = 1301369) B1301369
theorem B868223 : Blo 864565 868223 := bstep (se 1 (by rfl) ⟨651167, by rfl⟩ : syracuseStep 868223 = 1302335) B1302335
theorem B868335 : Blo 864565 868335 := bstep (se 1 (by rfl) ⟨651251, by rfl⟩ : syracuseStep 868335 = 1302503) B1302503
theorem B868383 : Blo 864565 868383 := bstep (se 1 (by rfl) ⟨651287, by rfl⟩ : syracuseStep 868383 = 1302575) B1302575
theorem B3293257 : Blo 864565 3293257 := bstep (se 2 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 3293257 = 2469943) B2469943
theorem B868519 : Blo 864565 868519 := bstep (se 1 (by rfl) ⟨651389, by rfl⟩ : syracuseStep 868519 = 1302779) B1302779
theorem B1949993 : Blo 864565 1949993 := bstep (se 2 (by rfl) ⟨731247, by rfl⟩ : syracuseStep 1949993 = 1462495) B1462495
theorem B1950047 : Blo 864565 1950047 := bstep (se 1 (by rfl) ⟨1462535, by rfl⟩ : syracuseStep 1950047 = 2925071) B2925071
theorem B3293561 : Blo 864565 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B3752315 : Blo 864565 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B5555425 : Blo 864565 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B5556347 : Blo 864565 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1952171 : Blo 864565 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B8309303 : Blo 864565 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B1297103 : Blo 864565 1297103 := bstep (se 1 (by rfl) ⟨972827, by rfl⟩ : syracuseStep 1297103 = 1945655) B1945655
theorem B1297385 : Blo 864565 1297385 := bstep (se 2 (by rfl) ⟨486519, by rfl⟩ : syracuseStep 1297385 = 973039) B973039
theorem B2346247 : Blo 864565 2346247 := bstep (se 1 (by rfl) ⟨1759685, by rfl⟩ : syracuseStep 2346247 = 3519371) B3519371
theorem B1461739 : Blo 864565 1461739 := bstep (se 1 (by rfl) ⟨1096304, by rfl⟩ : syracuseStep 1461739 = 2192609) B2192609
theorem B1756703 : Blo 864565 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B4935239 : Blo 864565 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B1462313 : Blo 864565 1462313 := bstep (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) B1096735
theorem B1954025 : Blo 864565 1954025 := bstep (se 2 (by rfl) ⟨732759, by rfl⟩ : syracuseStep 1954025 = 1465519) B1465519
theorem B28102949 : Blo 864565 28102949 := bstep (se 4 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 28102949 = 5269303) B5269303
theorem B11129507 : Blo 864565 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B4380155 : Blo 864565 4380155 := bstep (se 1 (by rfl) ⟨3285116, by rfl⟩ : syracuseStep 4380155 = 6570233) B6570233
theorem B5559833 : Blo 864565 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B6248009 : Blo 864565 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B10016419 : Blo 864565 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B1562377 : Blo 864565 1562377 := bstep (se 2 (by rfl) ⟨585891, by rfl⟩ : syracuseStep 1562377 = 1171783) B1171783
theorem B4380479 : Blo 864565 4380479 := bstep (se 1 (by rfl) ⟨3285359, by rfl⟩ : syracuseStep 4380479 = 6570719) B6570719
theorem B1300457 : Blo 864565 1300457 := bstep (se 2 (by rfl) ⟨487671, by rfl⟩ : syracuseStep 1300457 = 975343) B975343
theorem B1464959 : Blo 864565 1464959 := bstep (se 1 (by rfl) ⟨1098719, by rfl⟩ : syracuseStep 1464959 = 2197439) B2197439
theorem B2775713 : Blo 864565 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B24992489 : Blo 864565 24992489 := bstep (se 2 (by rfl) ⟨9372183, by rfl⟩ : syracuseStep 24992489 = 18744367) B18744367
theorem B1301375 : Blo 864565 1301375 := bstep (se 1 (by rfl) ⟨976031, by rfl⟩ : syracuseStep 1301375 = 1952063) B1952063
theorem B1301915 : Blo 864565 1301915 := bstep (se 1 (by rfl) ⟨976436, by rfl⟩ : syracuseStep 1301915 = 1952873) B1952873
theorem B974587 : Blo 864565 974587 := bstep (se 1 (by rfl) ⟨730940, by rfl⟩ : syracuseStep 974587 = 1461881) B1461881
theorem B1302281 : Blo 864565 1302281 := bstep (se 2 (by rfl) ⟨488355, by rfl⟩ : syracuseStep 1302281 = 976711) B976711
theorem B1302431 : Blo 864565 1302431 := bstep (se 1 (by rfl) ⟨976823, by rfl⟩ : syracuseStep 1302431 = 1953647) B1953647
theorem B9494441 : Blo 864565 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B33382367 : Blo 864565 33382367 := bstep (se 1 (by rfl) ⟨25036775, by rfl⟩ : syracuseStep 33382367 = 50073551) B50073551
theorem B1302623 : Blo 864565 1302623 := bstep (se 1 (by rfl) ⟨976967, by rfl⟩ : syracuseStep 1302623 = 1953935) B1953935
theorem B1302665 : Blo 864565 1302665 := bstep (se 2 (by rfl) ⟨488499, by rfl⟩ : syracuseStep 1302665 = 976999) B976999
theorem B1302761 : Blo 864565 1302761 := bstep (se 2 (by rfl) ⟨488535, by rfl⟩ : syracuseStep 1302761 = 977071) B977071
theorem B975451 : Blo 864565 975451 := bstep (se 1 (by rfl) ⟨731588, by rfl⟩ : syracuseStep 975451 = 1463177) B1463177
theorem B3695483 : Blo 864565 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B2712671 : Blo 864565 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B4156019 : Blo 864565 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B2223983 : Blo 864565 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B16872151 : Blo 864565 16872151 := bstep (se 1 (by rfl) ⟨12654113, by rfl⟩ : syracuseStep 16872151 = 25308227) B25308227
theorem B6583355 : Blo 864565 6583355 := bstep (se 1 (by rfl) ⟨4937516, by rfl⟩ : syracuseStep 6583355 = 9875033) B9875033
theorem B4158649 : Blo 864565 4158649 := bstep (se 2 (by rfl) ⟨1559493, by rfl⟩ : syracuseStep 4158649 = 3118987) B3118987
theorem B2193115 : Blo 864565 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B3340777 : Blo 864565 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B4160267 : Blo 864565 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B22772819 : Blo 864565 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B2194715 : Blo 864565 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B1801831 : Blo 864565 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B4391009 : Blo 864565 4391009 := bstep (se 2 (by rfl) ⟨1646628, by rfl⟩ : syracuseStep 4391009 = 3293257) B3293257
theorem B2195707 : Blo 864565 2195707 := bstep (se 1 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 2195707 = 3293561) B3293561
theorem B16647443 : Blo 864565 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B3704231 : Blo 864565 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B7407233 : Blo 864565 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B5539535 : Blo 864565 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B4393439 : Blo 864565 4393439 := bstep (se 1 (by rfl) ⟨3295079, by rfl⟩ : syracuseStep 4393439 = 6590159) B6590159
theorem B68553497 : Blo 864565 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B11111417 : Blo 864565 11111417 := bstep (se 2 (by rfl) ⟨4166781, by rfl⟩ : syracuseStep 11111417 = 8333563) B8333563
theorem B2920103 : Blo 864565 2920103 := bstep (se 1 (by rfl) ⟨2190077, by rfl⟩ : syracuseStep 2920103 = 4380155) B4380155
theorem B3706555 : Blo 864565 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B4165339 : Blo 864565 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B2920319 : Blo 864565 2920319 := bstep (se 1 (by rfl) ⟨2190239, by rfl⟩ : syracuseStep 2920319 = 4380479) B4380479
theorem B5542253 : Blo 864565 5542253 := bstep (se 3 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 5542253 = 2078345) B2078345
theorem B6329627 : Blo 864565 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B22254911 : Blo 864565 22254911 := bstep (se 1 (by rfl) ⟨16691183, by rfl⟩ : syracuseStep 22254911 = 33382367) B33382367
theorem B1808447 : Blo 864565 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B8460551 : Blo 864565 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B3283355 : Blo 864565 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B5544865 : Blo 864565 5544865 := bstep (se 2 (by rfl) ⟨2079324, by rfl⟩ : syracuseStep 5544865 = 4158649) B4158649
theorem B1318123 : Blo 864565 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B2924153 : Blo 864565 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B3285755 : Blo 864565 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B3285785 : Blo 864565 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B1188955 : Blo 864565 1188955 := bstep (se 1 (by rfl) ⟨891716, by rfl⟩ : syracuseStep 1188955 = 1783433) B1783433
theorem B15181879 : Blo 864565 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2402441 : Blo 864565 2402441 := bstep (se 2 (by rfl) ⟨900915, by rfl⟩ : syracuseStep 2402441 = 1801831) B1801831
theorem B2501543 : Blo 864565 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B2927771 : Blo 864565 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B67645705 : Blo 864565 67645705 := bstep (se 2 (by rfl) ⟨25367139, by rfl⟩ : syracuseStep 67645705 = 50734279) B50734279
theorem B864735 : Blo 864565 864735 := bstep (se 1 (by rfl) ⟨648551, by rfl⟩ : syracuseStep 864735 = 1297103) B1297103
theorem B864923 : Blo 864565 864923 := bstep (se 1 (by rfl) ⟨648692, by rfl⟩ : syracuseStep 864923 = 1297385) B1297385
theorem B8434529 : Blo 864565 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B3290159 : Blo 864565 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B30422137 : Blo 864565 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B1094887 : Blo 864565 1094887 := bstep (se 1 (by rfl) ⟨821165, by rfl⟩ : syracuseStep 1094887 = 1642331) B1642331
theorem B1947311 : Blo 864565 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B7419671 : Blo 864565 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B6568289 : Blo 864565 6568289 := bstep (se 2 (by rfl) ⟨2463108, by rfl⟩ : syracuseStep 6568289 = 4926217) B4926217
theorem B866971 : Blo 864565 866971 := bstep (se 1 (by rfl) ⟨650228, by rfl⟩ : syracuseStep 866971 = 1300457) B1300457
theorem B3128329 : Blo 864565 3128329 := bstep (se 2 (by rfl) ⟨1173123, by rfl⟩ : syracuseStep 3128329 = 2346247) B2346247
theorem B16661659 : Blo 864565 16661659 := bstep (se 1 (by rfl) ⟨12496244, by rfl⟩ : syracuseStep 16661659 = 24992489) B24992489
theorem B867583 : Blo 864565 867583 := bstep (se 1 (by rfl) ⟨650687, by rfl⟩ : syracuseStep 867583 = 1301375) B1301375
theorem B1948985 : Blo 864565 1948985 := bstep (se 2 (by rfl) ⟨730869, by rfl⟩ : syracuseStep 1948985 = 1461739) B1461739
theorem B1949255 : Blo 864565 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B867943 : Blo 864565 867943 := bstep (se 1 (by rfl) ⟨650957, by rfl⟩ : syracuseStep 867943 = 1301915) B1301915
theorem B868187 : Blo 864565 868187 := bstep (se 1 (by rfl) ⟨651140, by rfl⟩ : syracuseStep 868187 = 1302281) B1302281
theorem B868287 : Blo 864565 868287 := bstep (se 1 (by rfl) ⟨651215, by rfl⟩ : syracuseStep 868287 = 1302431) B1302431
theorem B868415 : Blo 864565 868415 := bstep (se 1 (by rfl) ⟨651311, by rfl⟩ : syracuseStep 868415 = 1302623) B1302623
theorem B868443 : Blo 864565 868443 := bstep (se 1 (by rfl) ⟨651332, by rfl⟩ : syracuseStep 868443 = 1302665) B1302665
theorem B868507 : Blo 864565 868507 := bstep (se 1 (by rfl) ⟨651380, by rfl⟩ : syracuseStep 868507 = 1302761) B1302761
theorem B1098623 : Blo 864565 1098623 := bstep (se 1 (by rfl) ⟨823967, by rfl⟩ : syracuseStep 1098623 = 1647935) B1647935
theorem B22496201 : Blo 864565 22496201 := bstep (se 2 (by rfl) ⟨8436075, by rfl⟩ : syracuseStep 22496201 = 16872151) B16872151
theorem B1950983 : Blo 864565 1950983 := bstep (se 1 (by rfl) ⟨1463237, by rfl⟩ : syracuseStep 1950983 = 2926475) B2926475
theorem B2770537 : Blo 864565 2770537 := bstep (se 2 (by rfl) ⟨1038951, by rfl⟩ : syracuseStep 2770537 = 2077903) B2077903
theorem B2770679 : Blo 864565 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B57657491 : Blo 864565 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B13355225 : Blo 864565 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B2083169 : Blo 864565 2083169 := bstep (se 2 (by rfl) ⟨781188, by rfl⟩ : syracuseStep 2083169 = 1562377) B1562377
theorem B1297319 : Blo 864565 1297319 := bstep (se 1 (by rfl) ⟨972989, by rfl⟩ : syracuseStep 1297319 = 1945979) B1945979
theorem B1297391 : Blo 864565 1297391 := bstep (se 1 (by rfl) ⟨973043, by rfl⟩ : syracuseStep 1297391 = 1946087) B1946087
theorem B2083931 : Blo 864565 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B1559855 : Blo 864565 1559855 := bstep (se 1 (by rfl) ⟨1169891, by rfl⟩ : syracuseStep 1559855 = 2339783) B2339783
theorem B1298171 : Blo 864565 1298171 := bstep (se 1 (by rfl) ⟨973628, by rfl⟩ : syracuseStep 1298171 = 1947257) B1947257
theorem B4378535 : Blo 864565 4378535 := bstep (se 1 (by rfl) ⟨3283901, by rfl⟩ : syracuseStep 4378535 = 6567803) B6567803
theorem B1298543 : Blo 864565 1298543 := bstep (se 1 (by rfl) ⟨973907, by rfl⟩ : syracuseStep 1298543 = 1947815) B1947815
theorem B2773511 : Blo 864565 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B1463143 : Blo 864565 1463143 := bstep (se 1 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 1463143 = 2194715) B2194715
theorem B1299449 : Blo 864565 1299449 := bstep (se 2 (by rfl) ⟨487293, by rfl⟩ : syracuseStep 1299449 = 974587) B974587
theorem B1299995 : Blo 864565 1299995 := bstep (se 1 (by rfl) ⟨974996, by rfl⟩ : syracuseStep 1299995 = 1949993) B1949993
theorem B1300031 : Blo 864565 1300031 := bstep (se 1 (by rfl) ⟨975023, by rfl⟩ : syracuseStep 1300031 = 1950047) B1950047
theorem B1463899 : Blo 864565 1463899 := bstep (se 1 (by rfl) ⟨1097924, by rfl⟩ : syracuseStep 1463899 = 2195849) B2195849
theorem B1300601 : Blo 864565 1300601 := bstep (se 2 (by rfl) ⟨487725, by rfl⟩ : syracuseStep 1300601 = 975451) B975451
theorem B1301447 : Blo 864565 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B1760393 : Blo 864565 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B9854621 : Blo 864565 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B1171135 : Blo 864565 1171135 := bstep (se 1 (by rfl) ⟨878351, by rfl⟩ : syracuseStep 1171135 = 1756703) B1756703
theorem B974875 : Blo 864565 974875 := bstep (se 1 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 974875 = 1462313) B1462313
theorem B1302683 : Blo 864565 1302683 := bstep (se 1 (by rfl) ⟨977012, by rfl⟩ : syracuseStep 1302683 = 1954025) B1954025
theorem B4382909 : Blo 864565 4382909 := bstep (se 3 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 4382909 = 1643591) B1643591
theorem B18735299 : Blo 864565 18735299 := bstep (se 1 (by rfl) ⟨14051474, by rfl⟩ : syracuseStep 18735299 = 28102949) B28102949
theorem B2056391 : Blo 864565 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B24045245 : Blo 864565 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B976639 : Blo 864565 976639 := bstep (se 1 (by rfl) ⟨732479, by rfl⟩ : syracuseStep 976639 = 1464959) B1464959
theorem B6580439 : Blo 864565 6580439 := bstep (se 1 (by rfl) ⟨4935329, by rfl⟩ : syracuseStep 6580439 = 9870659) B9870659
theorem B2190361 : Blo 864565 2190361 := bstep (se 2 (by rfl) ⟨821385, by rfl⟩ : syracuseStep 2190361 = 1642771) B1642771
theorem B1403935 : Blo 864565 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B2190473 : Blo 864565 2190473 := bstep (se 2 (by rfl) ⟨821427, by rfl⟩ : syracuseStep 2190473 = 1642855) B1642855
theorem B2780315 : Blo 864565 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B2190847 : Blo 864565 2190847 := bstep (se 1 (by rfl) ⟨1643135, by rfl⟩ : syracuseStep 2190847 = 3286271) B3286271
theorem B2190959 : Blo 864565 2190959 := bstep (se 1 (by rfl) ⟨1643219, by rfl⟩ : syracuseStep 2190959 = 3286439) B3286439
theorem B10023065 : Blo 864565 10023065 := bstep (se 2 (by rfl) ⟨3758649, by rfl⟩ : syracuseStep 10023065 = 7517299) B7517299
theorem B2191657 : Blo 864565 2191657 := bstep (se 2 (by rfl) ⟨821871, by rfl⟩ : syracuseStep 2191657 = 1643743) B1643743
theorem B7401901 : Blo 864565 7401901 := bstep (se 3 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 7401901 = 2775713) B2775713
theorem B4159151 : Blo 864565 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B4454369 : Blo 864565 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B4388903 : Blo 864565 4388903 := bstep (se 1 (by rfl) ⟨3291677, by rfl⟩ : syracuseStep 4388903 = 6583355) B6583355
theorem B7895231 : Blo 864565 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B2194411 : Blo 864565 2194411 := bstep (se 1 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 2194411 = 3291617) B3291617
theorem B2194553 : Blo 864565 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B16481513 : Blo 864565 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B5930621 : Blo 864565 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B38438327 : Blo 864565 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B7407611 : Blo 864565 7407611 := bstep (se 1 (by rfl) ⟨5555708, by rfl⟩ : syracuseStep 7407611 = 11111417) B11111417
theorem B2919023 : Blo 864565 2919023 := bstep (se 1 (by rfl) ⟨2189267, by rfl⟩ : syracuseStep 2919023 = 4378535) B4378535
theorem B2920481 : Blo 864565 2920481 := bstep (se 2 (by rfl) ⟨1095180, by rfl⟩ : syracuseStep 2920481 = 2190361) B2190361
theorem B5640367 : Blo 864565 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B2921129 : Blo 864565 2921129 := bstep (se 2 (by rfl) ⟨1095423, by rfl⟩ : syracuseStep 2921129 = 2190847) B2190847
theorem B2921939 : Blo 864565 2921939 := bstep (se 1 (by rfl) ⟨2191454, by rfl⟩ : syracuseStep 2921939 = 4382909) B4382909
theorem B12490199 : Blo 864565 12490199 := bstep (se 1 (by rfl) ⟨9367649, by rfl⟩ : syracuseStep 12490199 = 18735299) B18735299
theorem B4822525 : Blo 864565 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B2922209 : Blo 864565 2922209 := bstep (se 2 (by rfl) ⟨1095828, by rfl⟩ : syracuseStep 2922209 = 2191657) B2191657
theorem B9869201 : Blo 864565 9869201 := bstep (se 2 (by rfl) ⟨3700950, by rfl⟩ : syracuseStep 9869201 = 7401901) B7401901
theorem B16030163 : Blo 864565 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B4694381 : Blo 864565 4694381 := bstep (se 3 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 4694381 = 1760393) B1760393
theorem B43950701 : Blo 864565 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B2925881 : Blo 864565 2925881 := bstep (se 2 (by rfl) ⟨1097205, by rfl⟩ : syracuseStep 2925881 = 2194411) B2194411
theorem B4171105 : Blo 864565 4171105 := bstep (se 2 (by rfl) ⟨1564164, by rfl⟩ : syracuseStep 4171105 = 3128329) B3128329
theorem B2925935 : Blo 864565 2925935 := bstep (se 1 (by rfl) ⟨2194451, by rfl⟩ : syracuseStep 2925935 = 4388903) B4388903
theorem B2927339 : Blo 864565 2927339 := bstep (se 1 (by rfl) ⟨2195504, by rfl⟩ : syracuseStep 2927339 = 4391009) B4391009
theorem B2927609 : Blo 864565 2927609 := bstep (se 2 (by rfl) ⟨1097853, by rfl⟩ : syracuseStep 2927609 = 2195707) B2195707
theorem B1847119 : Blo 864565 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B1585273 : Blo 864565 1585273 := bstep (se 2 (by rfl) ⟨594477, by rfl⟩ : syracuseStep 1585273 = 1188955) B1188955
theorem B2928959 : Blo 864565 2928959 := bstep (se 1 (by rfl) ⟨2196719, by rfl⟩ : syracuseStep 2928959 = 4393439) B4393439
theorem B864879 : Blo 864565 864879 := bstep (se 1 (by rfl) ⟨648659, by rfl⟩ : syracuseStep 864879 = 1297319) B1297319
theorem B864927 : Blo 864565 864927 := bstep (se 1 (by rfl) ⟨648695, by rfl⟩ : syracuseStep 864927 = 1297391) B1297391
theorem B1389287 : Blo 864565 1389287 := bstep (se 1 (by rfl) ⟨1041965, by rfl⟩ : syracuseStep 1389287 = 2083931) B2083931
theorem B2929661 : Blo 864565 2929661 := bstep (se 3 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 2929661 = 1098623) B1098623
theorem B1946735 : Blo 864565 1946735 := bstep (se 1 (by rfl) ⟨1460051, by rfl⟩ : syracuseStep 1946735 = 2920103) B2920103
theorem B865447 : Blo 864565 865447 := bstep (se 1 (by rfl) ⟨649085, by rfl⟩ : syracuseStep 865447 = 1298171) B1298171
theorem B1946879 : Blo 864565 1946879 := bstep (se 1 (by rfl) ⟨1460159, by rfl⟩ : syracuseStep 1946879 = 2920319) B2920319
theorem B865695 : Blo 864565 865695 := bstep (se 1 (by rfl) ⟨649271, by rfl⟩ : syracuseStep 865695 = 1298543) B1298543
theorem B1849007 : Blo 864565 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B866299 : Blo 864565 866299 := bstep (se 1 (by rfl) ⟨649724, by rfl⟩ : syracuseStep 866299 = 1299449) B1299449
theorem B866663 : Blo 864565 866663 := bstep (se 1 (by rfl) ⟨649997, by rfl⟩ : syracuseStep 866663 = 1299995) B1299995
theorem B866687 : Blo 864565 866687 := bstep (se 1 (by rfl) ⟨650015, by rfl⟩ : syracuseStep 866687 = 1300031) B1300031
theorem B9877949 : Blo 864565 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B867067 : Blo 864565 867067 := bstep (se 1 (by rfl) ⟨650300, by rfl⟩ : syracuseStep 867067 = 1300601) B1300601
theorem B867631 : Blo 864565 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B5553785 : Blo 864565 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B1949435 : Blo 864565 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B6569747 : Blo 864565 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B868455 : Blo 864565 868455 := bstep (se 1 (by rfl) ⟨651341, by rfl⟩ : syracuseStep 868455 = 1302683) B1302683
theorem B7487653 : Blo 864565 7487653 := bstep (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) B1403935
theorem B90194273 : Blo 864565 90194273 := bstep (se 2 (by rfl) ⟨33822852, by rfl⟩ : syracuseStep 90194273 = 67645705) B67645705
theorem B5555117 : Blo 864565 5555117 := bstep (se 3 (by rfl) ⟨1041584, by rfl⟩ : syracuseStep 5555117 = 2083169) B2083169
theorem B1950857 : Blo 864565 1950857 := bstep (se 2 (by rfl) ⟨731571, by rfl⟩ : syracuseStep 1950857 = 1463143) B1463143
theorem B7029989 : Blo 864565 7029989 := bstep (se 4 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 7029989 = 1318123) B1318123
theorem B1459849 : Blo 864565 1459849 := bstep (se 2 (by rfl) ⟨547443, by rfl⟩ : syracuseStep 1459849 = 1094887) B1094887
theorem B1460315 : Blo 864565 1460315 := bstep (se 1 (by rfl) ⟨1095236, by rfl⟩ : syracuseStep 1460315 = 2190473) B2190473
theorem B1951847 : Blo 864565 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B1853543 : Blo 864565 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B1951865 : Blo 864565 1951865 := bstep (se 2 (by rfl) ⟨731949, by rfl⟩ : syracuseStep 1951865 = 1463899) B1463899
theorem B1460639 : Blo 864565 1460639 := bstep (se 1 (by rfl) ⟨1095479, by rfl⟩ : syracuseStep 1460639 = 2190959) B2190959
theorem B6670781 : Blo 864565 6670781 := bstep (se 3 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 6670781 = 2501543) B2501543
theorem B5623019 : Blo 864565 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B1298207 : Blo 864565 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B2772767 : Blo 864565 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B7393153 : Blo 864565 7393153 := bstep (se 2 (by rfl) ⟨2772432, by rfl⟩ : syracuseStep 7393153 = 5544865) B5544865
theorem B2969579 : Blo 864565 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B5263487 : Blo 864565 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B4378859 : Blo 864565 4378859 := bstep (se 1 (by rfl) ⟨3284144, by rfl⟩ : syracuseStep 4378859 = 6568289) B6568289
theorem B1463035 : Blo 864565 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B1299323 : Blo 864565 1299323 := bstep (se 1 (by rfl) ⟨974492, by rfl⟩ : syracuseStep 1299323 = 1948985) B1948985
theorem B1561513 : Blo 864565 1561513 := bstep (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) B1171135
theorem B1299503 : Blo 864565 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B3953747 : Blo 864565 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B1299833 : Blo 864565 1299833 := bstep (se 2 (by rfl) ⟨487437, by rfl⟩ : syracuseStep 1299833 = 974875) B974875
theorem B14997467 : Blo 864565 14997467 := bstep (se 1 (by rfl) ⟨11248100, by rfl⟩ : syracuseStep 14997467 = 22496201) B22496201
theorem B1300655 : Blo 864565 1300655 := bstep (se 1 (by rfl) ⟨975491, by rfl⟩ : syracuseStep 1300655 = 1950983) B1950983
theorem B11098295 : Blo 864565 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B4938155 : Blo 864565 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B3693023 : Blo 864565 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B8903483 : Blo 864565 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B3694049 : Blo 864565 3694049 := bstep (se 2 (by rfl) ⟨1385268, by rfl⟩ : syracuseStep 3694049 = 2770537) B2770537
theorem B1302185 : Blo 864565 1302185 := bstep (se 2 (by rfl) ⟨488319, by rfl⟩ : syracuseStep 1302185 = 976639) B976639
theorem B20242505 : Blo 864565 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B3694835 : Blo 864565 3694835 := bstep (se 1 (by rfl) ⟨2771126, by rfl⟩ : syracuseStep 3694835 = 5542253) B5542253
theorem B4219751 : Blo 864565 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B14836607 : Blo 864565 14836607 := bstep (se 1 (by rfl) ⟨11127455, by rfl⟩ : syracuseStep 14836607 = 22254911) B22254911
theorem B2188903 : Blo 864565 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B4942073 : Blo 864565 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B1370927 : Blo 864565 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B2190503 : Blo 864565 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B2190523 : Blo 864565 2190523 := bstep (se 1 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 2190523 = 3285785) B3285785
theorem B1601627 : Blo 864565 1601627 := bstep (se 1 (by rfl) ⟨1201220, by rfl⟩ : syracuseStep 1601627 = 2402441) B2402441
theorem B4386959 : Blo 864565 4386959 := bstep (se 1 (by rfl) ⟨3290219, by rfl⟩ : syracuseStep 4386959 = 6580439) B6580439
theorem B40562849 : Blo 864565 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B182809325 : Blo 864565 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B6682043 : Blo 864565 6682043 := bstep (se 1 (by rfl) ⟨5011532, by rfl⟩ : syracuseStep 6682043 = 10023065) B10023065
theorem B2193439 : Blo 864565 2193439 := bstep (se 1 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 2193439 = 3290159) B3290159
theorem B4159613 : Blo 864565 4159613 := bstep (se 3 (by rfl) ⟨779927, by rfl⟩ : syracuseStep 4159613 = 1559855) B1559855
theorem B4946447 : Blo 864565 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B22215545 : Blo 864565 22215545 := bstep (se 2 (by rfl) ⟨8330829, by rfl⟩ : syracuseStep 22215545 = 16661659) B16661659
theorem B60129515 : Blo 864565 60129515 := bstep (se 1 (by rfl) ⟨45097136, by rfl⟩ : syracuseStep 60129515 = 90194273) B90194273
theorem B3703411 : Blo 864565 3703411 := bstep (se 1 (by rfl) ⟨2777558, by rfl⟩ : syracuseStep 3703411 = 5555117) B5555117
theorem B4686659 : Blo 864565 4686659 := bstep (se 1 (by rfl) ⟨3514994, by rfl⟩ : syracuseStep 4686659 = 7029989) B7029989
theorem B2918537 : Blo 864565 2918537 := bstep (se 2 (by rfl) ⟨1094451, by rfl⟩ : syracuseStep 2918537 = 2188903) B2188903
theorem B3508991 : Blo 864565 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B2919239 : Blo 864565 2919239 := bstep (se 1 (by rfl) ⟨2189429, by rfl⟩ : syracuseStep 2919239 = 4378859) B4378859
theorem B8326799 : Blo 864565 8326799 := bstep (se 1 (by rfl) ⟨6245099, by rfl⟩ : syracuseStep 8326799 = 12490199) B12490199
theorem B102502205 : Blo 864565 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B9998311 : Blo 864565 9998311 := bstep (se 1 (by rfl) ⟨7498733, by rfl⟩ : syracuseStep 9998311 = 14997467) B14997467
theorem B2920697 : Blo 864565 2920697 := bstep (se 2 (by rfl) ⟨1095261, by rfl⟩ : syracuseStep 2920697 = 2190523) B2190523
theorem B2462015 : Blo 864565 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B5935655 : Blo 864565 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B2462699 : Blo 864565 2462699 := bstep (se 1 (by rfl) ⟨1847024, by rfl⟩ : syracuseStep 2462699 = 3694049) B3694049
theorem B2462825 : Blo 864565 2462825 := bstep (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) B1847119
theorem B2463223 : Blo 864565 2463223 := bstep (se 1 (by rfl) ⟨1847417, by rfl⟩ : syracuseStep 2463223 = 3694835) B3694835
theorem B29300467 : Blo 864565 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B6430033 : Blo 864565 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B2924585 : Blo 864565 2924585 := bstep (se 2 (by rfl) ⟨1096719, by rfl⟩ : syracuseStep 2924585 = 2193439) B2193439
theorem B2924639 : Blo 864565 2924639 := bstep (se 1 (by rfl) ⟨2193479, by rfl⟩ : syracuseStep 2924639 = 4386959) B4386959
theorem B27041899 : Blo 864565 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B926191 : Blo 864565 926191 := bstep (se 1 (by rfl) ⟨694643, by rfl⟩ : syracuseStep 926191 = 1389287) B1389287
theorem B121872883 : Blo 864565 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B53980013 : Blo 864565 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B4271005 : Blo 864565 4271005 := bstep (se 3 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 4271005 = 1601627) B1601627
theorem B1946015 : Blo 864565 1946015 := bstep (se 1 (by rfl) ⟨1459511, by rfl⟩ : syracuseStep 1946015 = 2919023) B2919023
theorem B3748679 : Blo 864565 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B1946465 : Blo 864565 1946465 := bstep (se 2 (by rfl) ⟨729924, by rfl⟩ : syracuseStep 1946465 = 1459849) B1459849
theorem B865471 : Blo 864565 865471 := bstep (se 1 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 865471 = 1298207) B1298207
theorem B1848511 : Blo 864565 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B1946987 : Blo 864565 1946987 := bstep (se 1 (by rfl) ⟨1460240, by rfl⟩ : syracuseStep 1946987 = 2920481) B2920481
theorem B1947419 : Blo 864565 1947419 := bstep (se 1 (by rfl) ⟨1460564, by rfl⟩ : syracuseStep 1947419 = 2921129) B2921129
theorem B866215 : Blo 864565 866215 := bstep (se 1 (by rfl) ⟨649661, by rfl⟩ : syracuseStep 866215 = 1299323) B1299323
theorem B866335 : Blo 864565 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B2635831 : Blo 864565 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B866555 : Blo 864565 866555 := bstep (se 1 (by rfl) ⟨649916, by rfl⟩ : syracuseStep 866555 = 1299833) B1299833
theorem B1947959 : Blo 864565 1947959 := bstep (se 1 (by rfl) ⟨1460969, by rfl⟩ : syracuseStep 1947959 = 2921939) B2921939
theorem B1948139 : Blo 864565 1948139 := bstep (se 1 (by rfl) ⟨1461104, by rfl⟩ : syracuseStep 1948139 = 2922209) B2922209
theorem B867103 : Blo 864565 867103 := bstep (se 1 (by rfl) ⟨650327, by rfl⟩ : syracuseStep 867103 = 1300655) B1300655
theorem B3292103 : Blo 864565 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B180042709 : Blo 864565 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B868123 : Blo 864565 868123 := bstep (se 1 (by rfl) ⟨651092, by rfl⟩ : syracuseStep 868123 = 1302185) B1302185
theorem B2113697 : Blo 864565 2113697 := bstep (se 2 (by rfl) ⟨792636, by rfl⟩ : syracuseStep 2113697 = 1585273) B1585273
theorem B7520489 : Blo 864565 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B3129587 : Blo 864565 3129587 := bstep (se 1 (by rfl) ⟨2347190, by rfl⟩ : syracuseStep 3129587 = 4694381) B4694381
theorem B1950587 : Blo 864565 1950587 := bstep (se 1 (by rfl) ⟨1462940, by rfl⟩ : syracuseStep 1950587 = 2925881) B2925881
theorem B1950623 : Blo 864565 1950623 := bstep (se 1 (by rfl) ⟨1462967, by rfl⟩ : syracuseStep 1950623 = 2925935) B2925935
theorem B1950713 : Blo 864565 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B42747101 : Blo 864565 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B2082017 : Blo 864565 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B3294715 : Blo 864565 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B1951559 : Blo 864565 1951559 := bstep (se 1 (by rfl) ⟨1463669, by rfl⟩ : syracuseStep 1951559 = 2927339) B2927339
theorem B1951739 : Blo 864565 1951739 := bstep (se 1 (by rfl) ⟨1463804, by rfl⟩ : syracuseStep 1951739 = 2927609) B2927609
theorem B1460335 : Blo 864565 1460335 := bstep (se 1 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 1460335 = 2190503) B2190503
theorem B1952639 : Blo 864565 1952639 := bstep (se 1 (by rfl) ⟨1464479, by rfl⟩ : syracuseStep 1952639 = 2928959) B2928959
theorem B1953107 : Blo 864565 1953107 := bstep (se 1 (by rfl) ⟨1464830, by rfl⟩ : syracuseStep 1953107 = 2929661) B2929661
theorem B1297823 : Blo 864565 1297823 := bstep (se 1 (by rfl) ⟨973367, by rfl⟩ : syracuseStep 1297823 = 1946735) B1946735
theorem B1297919 : Blo 864565 1297919 := bstep (se 1 (by rfl) ⟨973439, by rfl⟩ : syracuseStep 1297919 = 1946879) B1946879
theorem B1232671 : Blo 864565 1232671 := bstep (se 1 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 1232671 = 1849007) B1849007
theorem B2773075 : Blo 864565 2773075 := bstep (se 1 (by rfl) ⟨2079806, by rfl⟩ : syracuseStep 2773075 = 4159613) B4159613
theorem B3297631 : Blo 864565 3297631 := bstep (se 1 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 3297631 = 4946447) B4946447
theorem B1299623 : Blo 864565 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B4379831 : Blo 864565 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B7918877 : Blo 864565 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B9983537 : Blo 864565 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B1300571 : Blo 864565 1300571 := bstep (se 1 (by rfl) ⟨975428, by rfl⟩ : syracuseStep 1300571 = 1950857) B1950857
theorem B4938407 : Blo 864565 4938407 := bstep (se 1 (by rfl) ⟨3703805, by rfl⟩ : syracuseStep 4938407 = 7407611) B7407611
theorem B973543 : Blo 864565 973543 := bstep (se 1 (by rfl) ⟨730157, by rfl⟩ : syracuseStep 973543 = 1460315) B1460315
theorem B1301231 : Blo 864565 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B1301243 : Blo 864565 1301243 := bstep (se 1 (by rfl) ⟨975932, by rfl⟩ : syracuseStep 1301243 = 1951865) B1951865
theorem B973759 : Blo 864565 973759 := bstep (se 1 (by rfl) ⟨730319, by rfl⟩ : syracuseStep 973759 = 1460639) B1460639
theorem B4447187 : Blo 864565 4447187 := bstep (se 1 (by rfl) ⟨3335390, by rfl⟩ : syracuseStep 4447187 = 6670781) B6670781
theorem B5561473 : Blo 864565 5561473 := bstep (se 2 (by rfl) ⟨2085552, by rfl⟩ : syracuseStep 5561473 = 4171105) B4171105
theorem B6579467 : Blo 864565 6579467 := bstep (se 1 (by rfl) ⟨4934600, by rfl⟩ : syracuseStep 6579467 = 9869201) B9869201
theorem B7398863 : Blo 864565 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B9857537 : Blo 864565 9857537 := bstep (se 2 (by rfl) ⟨3696576, by rfl⟩ : syracuseStep 9857537 = 7393153) B7393153
theorem B4942781 : Blo 864565 4942781 := bstep (se 3 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 4942781 = 1853543) B1853543
theorem B9891071 : Blo 864565 9891071 := bstep (se 1 (by rfl) ⟨7418303, by rfl⟩ : syracuseStep 9891071 = 14836607) B14836607
theorem B913951 : Blo 864565 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B4454695 : Blo 864565 4454695 := bstep (se 1 (by rfl) ⟨3341021, by rfl⟩ : syracuseStep 4454695 = 6682043) B6682043
theorem B6585299 : Blo 864565 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B14810363 : Blo 864565 14810363 := bstep (se 1 (by rfl) ⟨11107772, by rfl⟩ : syracuseStep 14810363 = 22215545) B22215545
theorem B3702523 : Blo 864565 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B1409131 : Blo 864565 1409131 := bstep (se 1 (by rfl) ⟨1056848, by rfl⟩ : syracuseStep 1409131 = 2113697) B2113697
theorem B5013659 : Blo 864565 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B162497177 : Blo 864565 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B23758373 : Blo 864565 23758373 := bstep (se 4 (by rfl) ⟨2227347, by rfl⟩ : syracuseStep 23758373 = 4454695) B4454695
theorem B4392953 : Blo 864565 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B1641799 : Blo 864565 1641799 := bstep (se 1 (by rfl) ⟨1231349, by rfl⟩ : syracuseStep 1641799 = 2462699) B2462699
theorem B1641883 : Blo 864565 1641883 := bstep (se 1 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 1641883 = 2462825) B2462825
theorem B2919887 : Blo 864565 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B5279251 : Blo 864565 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B6655691 : Blo 864565 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B1643561 : Blo 864565 1643561 := bstep (se 2 (by rfl) ⟨616335, by rfl⟩ : syracuseStep 1643561 = 1232671) B1232671
theorem B4396841 : Blo 864565 4396841 := bstep (se 2 (by rfl) ⟨1648815, by rfl⟩ : syracuseStep 4396841 = 3297631) B3297631
theorem B1218601 : Blo 864565 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B2464681 : Blo 864565 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B35986675 : Blo 864565 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B3284297 : Blo 864565 3284297 := bstep (se 2 (by rfl) ⟨1231611, by rfl⟩ : syracuseStep 3284297 = 2463223) B2463223
theorem B6594047 : Blo 864565 6594047 := bstep (se 1 (by rfl) ⟨4945535, by rfl⟩ : syracuseStep 6594047 = 9891071) B9891071
theorem B39067289 : Blo 864565 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B3514441 : Blo 864565 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B2499119 : Blo 864565 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B7415297 : Blo 864565 7415297 := bstep (se 2 (by rfl) ⟨2780736, by rfl⟩ : syracuseStep 7415297 = 5561473) B5561473
theorem B9873575 : Blo 864565 9873575 := bstep (se 1 (by rfl) ⟨7405181, by rfl⟩ : syracuseStep 9873575 = 14810363) B14810363
theorem B36055865 : Blo 864565 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B40086343 : Blo 864565 40086343 := bstep (se 1 (by rfl) ⟨30064757, by rfl⟩ : syracuseStep 40086343 = 60129515) B60129515
theorem B3124439 : Blo 864565 3124439 := bstep (se 1 (by rfl) ⟨2343329, by rfl⟩ : syracuseStep 3124439 = 4686659) B4686659
theorem B1388011 : Blo 864565 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B6565373 : Blo 864565 6565373 := bstep (se 3 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 6565373 = 2462015) B2462015
theorem B1945691 : Blo 864565 1945691 := bstep (se 1 (by rfl) ⟨1459268, by rfl⟩ : syracuseStep 1945691 = 2918537) B2918537
theorem B2339327 : Blo 864565 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B1946159 : Blo 864565 1946159 := bstep (se 1 (by rfl) ⟨1459619, by rfl⟩ : syracuseStep 1946159 = 2919239) B2919239
theorem B865215 : Blo 864565 865215 := bstep (se 1 (by rfl) ⟨648911, by rfl⟩ : syracuseStep 865215 = 1297823) B1297823
theorem B865279 : Blo 864565 865279 := bstep (se 1 (by rfl) ⟨648959, by rfl⟩ : syracuseStep 865279 = 1297919) B1297919
theorem B5551199 : Blo 864565 5551199 := bstep (se 1 (by rfl) ⟨4163399, by rfl⟩ : syracuseStep 5551199 = 8326799) B8326799
theorem B68334803 : Blo 864565 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B1947113 : Blo 864565 1947113 := bstep (se 2 (by rfl) ⟨730167, by rfl⟩ : syracuseStep 1947113 = 1460335) B1460335
theorem B1947131 : Blo 864565 1947131 := bstep (se 1 (by rfl) ⟨1460348, by rfl⟩ : syracuseStep 1947131 = 2920697) B2920697
theorem B866415 : Blo 864565 866415 := bstep (se 1 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 866415 = 1299623) B1299623
theorem B867047 : Blo 864565 867047 := bstep (se 1 (by rfl) ⟨650285, by rfl⟩ : syracuseStep 867047 = 1300571) B1300571
theorem B3292271 : Blo 864565 3292271 := bstep (se 1 (by rfl) ⟨2469203, by rfl⟩ : syracuseStep 3292271 = 4938407) B4938407
theorem B867487 : Blo 864565 867487 := bstep (se 1 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 867487 = 1301231) B1301231
theorem B867495 : Blo 864565 867495 := bstep (se 1 (by rfl) ⟨650621, by rfl⟩ : syracuseStep 867495 = 1301243) B1301243
theorem B2964791 : Blo 864565 2964791 := bstep (se 1 (by rfl) ⟨2223593, by rfl⟩ : syracuseStep 2964791 = 4447187) B4447187
theorem B1949723 : Blo 864565 1949723 := bstep (se 1 (by rfl) ⟨1462292, by rfl⟩ : syracuseStep 1949723 = 2924585) B2924585
theorem B1949759 : Blo 864565 1949759 := bstep (se 1 (by rfl) ⟨1462319, by rfl⟩ : syracuseStep 1949759 = 2924639) B2924639
theorem B4932575 : Blo 864565 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B6571691 : Blo 864565 6571691 := bstep (se 1 (by rfl) ⟨4928768, by rfl⟩ : syracuseStep 6571691 = 9857537) B9857537
theorem B3295187 : Blo 864565 3295187 := bstep (se 1 (by rfl) ⟨2471390, by rfl⟩ : syracuseStep 3295187 = 4942781) B4942781
theorem B1297343 : Blo 864565 1297343 := bstep (se 1 (by rfl) ⟨973007, by rfl⟩ : syracuseStep 1297343 = 1946015) B1946015
theorem B1297643 : Blo 864565 1297643 := bstep (se 1 (by rfl) ⟨973232, by rfl⟩ : syracuseStep 1297643 = 1946465) B1946465
theorem B1297991 : Blo 864565 1297991 := bstep (se 1 (by rfl) ⟨973493, by rfl⟩ : syracuseStep 1297991 = 1946987) B1946987
theorem B1298057 : Blo 864565 1298057 := bstep (se 2 (by rfl) ⟨486771, by rfl⟩ : syracuseStep 1298057 = 973543) B973543
theorem B1298279 : Blo 864565 1298279 := bstep (se 1 (by rfl) ⟨973709, by rfl⟩ : syracuseStep 1298279 = 1947419) B1947419
theorem B1298345 : Blo 864565 1298345 := bstep (se 2 (by rfl) ⟨486879, by rfl⟩ : syracuseStep 1298345 = 973759) B973759
theorem B1298639 : Blo 864565 1298639 := bstep (se 1 (by rfl) ⟨973979, by rfl⟩ : syracuseStep 1298639 = 1947959) B1947959
theorem B1298759 : Blo 864565 1298759 := bstep (se 1 (by rfl) ⟨974069, by rfl⟩ : syracuseStep 1298759 = 1948139) B1948139
theorem B8573377 : Blo 864565 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B4936697 : Blo 864565 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B2086391 : Blo 864565 2086391 := bstep (se 1 (by rfl) ⟨1564793, by rfl⟩ : syracuseStep 2086391 = 3129587) B3129587
theorem B1300391 : Blo 864565 1300391 := bstep (se 1 (by rfl) ⟨975293, by rfl⟩ : syracuseStep 1300391 = 1950587) B1950587
theorem B1300415 : Blo 864565 1300415 := bstep (se 1 (by rfl) ⟨975311, by rfl⟩ : syracuseStep 1300415 = 1950623) B1950623
theorem B1234921 : Blo 864565 1234921 := bstep (se 2 (by rfl) ⟨463095, by rfl⟩ : syracuseStep 1234921 = 926191) B926191
theorem B1300475 : Blo 864565 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B28498067 : Blo 864565 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B4937881 : Blo 864565 4937881 := bstep (se 2 (by rfl) ⟨1851705, by rfl⟩ : syracuseStep 4937881 = 3703411) B3703411
theorem B1301039 : Blo 864565 1301039 := bstep (se 1 (by rfl) ⟨975779, by rfl⟩ : syracuseStep 1301039 = 1951559) B1951559
theorem B1301159 : Blo 864565 1301159 := bstep (se 1 (by rfl) ⟨975869, by rfl⟩ : syracuseStep 1301159 = 1951739) B1951739
theorem B1301759 : Blo 864565 1301759 := bstep (se 1 (by rfl) ⟨976319, by rfl⟩ : syracuseStep 1301759 = 1952639) B1952639
theorem B1302071 : Blo 864565 1302071 := bstep (se 1 (by rfl) ⟨976553, by rfl⟩ : syracuseStep 1302071 = 1953107) B1953107
theorem B3957103 : Blo 864565 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B5694673 : Blo 864565 5694673 := bstep (se 2 (by rfl) ⟨2135502, by rfl⟩ : syracuseStep 5694673 = 4271005) B4271005
theorem B13331081 : Blo 864565 13331081 := bstep (se 2 (by rfl) ⟨4999155, by rfl⟩ : syracuseStep 13331081 = 9998311) B9998311
theorem B3697433 : Blo 864565 3697433 := bstep (se 2 (by rfl) ⟨1386537, by rfl⟩ : syracuseStep 3697433 = 2773075) B2773075
theorem B4386311 : Blo 864565 4386311 := bstep (se 1 (by rfl) ⟨3289733, by rfl⟩ : syracuseStep 4386311 = 6579467) B6579467
theorem B240056945 : Blo 864565 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2194735 : Blo 864565 2194735 := bstep (se 1 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 2194735 = 3292103) B3292103
theorem B4390199 : Blo 864565 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B4685921 : Blo 864565 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B3342439 : Blo 864565 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B108331451 : Blo 864565 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B2196791 : Blo 864565 2196791 := bstep (se 1 (by rfl) ⟨1647593, by rfl⟩ : syracuseStep 2196791 = 3295187) B3295187
theorem B21104549 : Blo 864565 21104549 := bstep (se 4 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 21104549 = 3957103) B3957103
theorem B4396031 : Blo 864565 4396031 := bstep (se 1 (by rfl) ⟨3297023, by rfl⟩ : syracuseStep 4396031 = 6594047) B6594047
theorem B2464955 : Blo 864565 2464955 := bstep (se 1 (by rfl) ⟨1848716, by rfl⟩ : syracuseStep 2464955 = 3697433) B3697433
theorem B2924207 : Blo 864565 2924207 := bstep (se 1 (by rfl) ⟨2193155, by rfl⟩ : syracuseStep 2924207 = 4386311) B4386311
theorem B1646561 : Blo 864565 1646561 := bstep (se 2 (by rfl) ⟨617460, by rfl⟩ : syracuseStep 1646561 = 1234921) B1234921
theorem B45556535 : Blo 864565 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B3286241 : Blo 864565 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B47982233 : Blo 864565 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B2926313 : Blo 864565 2926313 := bstep (se 2 (by rfl) ⟨1097367, by rfl⟩ : syracuseStep 2926313 = 2194735) B2194735
theorem B1976527 : Blo 864565 1976527 := bstep (se 1 (by rfl) ⟨1482395, by rfl⟩ : syracuseStep 1976527 = 2964791) B2964791
theorem B2926799 : Blo 864565 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B1878841 : Blo 864565 1878841 := bstep (se 2 (by rfl) ⟨704565, by rfl⟩ : syracuseStep 1878841 = 1409131) B1409131
theorem B3288383 : Blo 864565 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B15838915 : Blo 864565 15838915 := bstep (se 1 (by rfl) ⟨11879186, by rfl⟩ : syracuseStep 15838915 = 23758373) B23758373
theorem B2928635 : Blo 864565 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B6238205 : Blo 864565 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B864895 : Blo 864565 864895 := bstep (se 1 (by rfl) ⟨648671, by rfl⟩ : syracuseStep 864895 = 1297343) B1297343
theorem B865095 : Blo 864565 865095 := bstep (se 1 (by rfl) ⟨648821, by rfl⟩ : syracuseStep 865095 = 1297643) B1297643
theorem B1946591 : Blo 864565 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B865327 : Blo 864565 865327 := bstep (se 1 (by rfl) ⟨648995, by rfl⟩ : syracuseStep 865327 = 1297991) B1297991
theorem B865371 : Blo 864565 865371 := bstep (se 1 (by rfl) ⟨649028, by rfl⟩ : syracuseStep 865371 = 1298057) B1298057
theorem B4437127 : Blo 864565 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B865519 : Blo 864565 865519 := bstep (se 1 (by rfl) ⟨649139, by rfl⟩ : syracuseStep 865519 = 1298279) B1298279
theorem B865563 : Blo 864565 865563 := bstep (se 1 (by rfl) ⟨649172, by rfl⟩ : syracuseStep 865563 = 1298345) B1298345
theorem B865759 : Blo 864565 865759 := bstep (se 1 (by rfl) ⟨649319, by rfl⟩ : syracuseStep 865759 = 1298639) B1298639
theorem B865839 : Blo 864565 865839 := bstep (se 1 (by rfl) ⟨649379, by rfl⟩ : syracuseStep 865839 = 1298759) B1298759
theorem B3291131 : Blo 864565 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B1095707 : Blo 864565 1095707 := bstep (se 1 (by rfl) ⟨821780, by rfl⟩ : syracuseStep 1095707 = 1643561) B1643561
theorem B1390927 : Blo 864565 1390927 := bstep (se 1 (by rfl) ⟨1043195, by rfl⟩ : syracuseStep 1390927 = 2086391) B2086391
theorem B2931227 : Blo 864565 2931227 := bstep (se 1 (by rfl) ⟨2198420, by rfl⟩ : syracuseStep 2931227 = 4396841) B4396841
theorem B866927 : Blo 864565 866927 := bstep (se 1 (by rfl) ⟨650195, by rfl⟩ : syracuseStep 866927 = 1300391) B1300391
theorem B866943 : Blo 864565 866943 := bstep (se 1 (by rfl) ⟨650207, by rfl⟩ : syracuseStep 866943 = 1300415) B1300415
theorem B866983 : Blo 864565 866983 := bstep (se 1 (by rfl) ⟨650237, by rfl⟩ : syracuseStep 866983 = 1300475) B1300475
theorem B867359 : Blo 864565 867359 := bstep (se 1 (by rfl) ⟨650519, by rfl⟩ : syracuseStep 867359 = 1301039) B1301039
theorem B213793829 : Blo 864565 213793829 := bstep (se 4 (by rfl) ⟨20043171, by rfl⟩ : syracuseStep 213793829 = 40086343) B40086343
theorem B867439 : Blo 864565 867439 := bstep (se 1 (by rfl) ⟨650579, by rfl⟩ : syracuseStep 867439 = 1301159) B1301159
theorem B1850681 : Blo 864565 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B867839 : Blo 864565 867839 := bstep (se 1 (by rfl) ⟨650879, by rfl⟩ : syracuseStep 867839 = 1301759) B1301759
theorem B868047 : Blo 864565 868047 := bstep (se 1 (by rfl) ⟨651035, by rfl⟩ : syracuseStep 868047 = 1302071) B1302071
theorem B24037243 : Blo 864565 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B2082959 : Blo 864565 2082959 := bstep (se 1 (by rfl) ⟨1562219, by rfl⟩ : syracuseStep 2082959 = 3124439) B3124439
theorem B4376915 : Blo 864565 4376915 := bstep (se 1 (by rfl) ⟨3282686, by rfl⟩ : syracuseStep 4376915 = 6565373) B6565373
theorem B1624801 : Blo 864565 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B1297127 : Blo 864565 1297127 := bstep (se 1 (by rfl) ⟨972845, by rfl⟩ : syracuseStep 1297127 = 1945691) B1945691
theorem B1297439 : Blo 864565 1297439 := bstep (se 1 (by rfl) ⟨973079, by rfl⟩ : syracuseStep 1297439 = 1946159) B1946159
theorem B1298075 : Blo 864565 1298075 := bstep (se 1 (by rfl) ⟨973556, by rfl⟩ : syracuseStep 1298075 = 1947113) B1947113
theorem B1298087 : Blo 864565 1298087 := bstep (se 1 (by rfl) ⟨973565, by rfl⟩ : syracuseStep 1298087 = 1947131) B1947131
theorem B1299815 : Blo 864565 1299815 := bstep (se 1 (by rfl) ⟨974861, by rfl⟩ : syracuseStep 1299815 = 1949723) B1949723
theorem B1299839 : Blo 864565 1299839 := bstep (se 1 (by rfl) ⟨974879, by rfl⟩ : syracuseStep 1299839 = 1949759) B1949759
theorem B4381127 : Blo 864565 4381127 := bstep (se 1 (by rfl) ⟨3285845, by rfl⟩ : syracuseStep 4381127 = 6571691) B6571691
theorem B7592897 : Blo 864565 7592897 := bstep (se 2 (by rfl) ⟨2847336, by rfl⟩ : syracuseStep 7592897 = 5694673) B5694673
theorem B18998711 : Blo 864565 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B2189065 : Blo 864565 2189065 := bstep (se 2 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 2189065 = 1641799) B1641799
theorem B2189177 : Blo 864565 2189177 := bstep (se 2 (by rfl) ⟨820941, by rfl⟩ : syracuseStep 2189177 = 1641883) B1641883
theorem B7039001 : Blo 864565 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B2189531 : Blo 864565 2189531 := bstep (se 1 (by rfl) ⟨1642148, by rfl⟩ : syracuseStep 2189531 = 3284297) B3284297
theorem B26044859 : Blo 864565 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B1666079 : Blo 864565 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B11431169 : Blo 864565 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B4943531 : Blo 864565 4943531 := bstep (se 1 (by rfl) ⟨3707648, by rfl⟩ : syracuseStep 4943531 = 7415297) B7415297
theorem B6582383 : Blo 864565 6582383 := bstep (se 1 (by rfl) ⟨4936787, by rfl⟩ : syracuseStep 6582383 = 9873575) B9873575
theorem B35549549 : Blo 864565 35549549 := bstep (se 3 (by rfl) ⟨6665540, by rfl⟩ : syracuseStep 35549549 = 13331081) B13331081
theorem B6583841 : Blo 864565 6583841 := bstep (se 2 (by rfl) ⟨2468940, by rfl⟩ : syracuseStep 6583841 = 4937881) B4937881
theorem B3700799 : Blo 864565 3700799 := bstep (se 1 (by rfl) ⟨2775599, by rfl⟩ : syracuseStep 3700799 = 5551199) B5551199
theorem B160037963 : Blo 864565 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B2194847 : Blo 864565 2194847 := bstep (se 1 (by rfl) ⟨1646135, by rfl⟩ : syracuseStep 2194847 = 3292271) B3292271
theorem B4456585 : Blo 864565 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B72220967 : Blo 864565 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B2917943 : Blo 864565 2917943 := bstep (se 1 (by rfl) ⟨2188457, by rfl⟩ : syracuseStep 2917943 = 4376915) B4376915
theorem B2918753 : Blo 864565 2918753 := bstep (se 2 (by rfl) ⟨1094532, by rfl⟩ : syracuseStep 2918753 = 2189065) B2189065
theorem B2166401 : Blo 864565 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B2920751 : Blo 864565 2920751 := bstep (se 1 (by rfl) ⟨2190563, by rfl⟩ : syracuseStep 2920751 = 4381127) B4381127
theorem B1643303 : Blo 864565 1643303 := bstep (se 1 (by rfl) ⟨1232477, by rfl⟩ : syracuseStep 1643303 = 2464955) B2464955
theorem B2921885 : Blo 864565 2921885 := bstep (se 3 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 2921885 = 1095707) B1095707
theorem B4692667 : Blo 864565 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B23699699 : Blo 864565 23699699 := bstep (se 1 (by rfl) ⟨17774774, by rfl⟩ : syracuseStep 23699699 = 35549549) B35549549
theorem B2467199 : Blo 864565 2467199 := bstep (se 1 (by rfl) ⟨1850399, by rfl⟩ : syracuseStep 2467199 = 3700799) B3700799
theorem B128198629 : Blo 864565 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B3123947 : Blo 864565 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B14069699 : Blo 864565 14069699 := bstep (se 1 (by rfl) ⟨10552274, by rfl⟩ : syracuseStep 14069699 = 21104549) B21104549
theorem B1388639 : Blo 864565 1388639 := bstep (se 1 (by rfl) ⟨1041479, by rfl⟩ : syracuseStep 1388639 = 2082959) B2082959
theorem B864751 : Blo 864565 864751 := bstep (se 1 (by rfl) ⟨648563, by rfl⟩ : syracuseStep 864751 = 1297127) B1297127
theorem B864959 : Blo 864565 864959 := bstep (se 1 (by rfl) ⟨648719, by rfl⟩ : syracuseStep 864959 = 1297439) B1297439
theorem B865383 : Blo 864565 865383 := bstep (se 1 (by rfl) ⟨649037, by rfl⟩ : syracuseStep 865383 = 1298075) B1298075
theorem B865391 : Blo 864565 865391 := bstep (se 1 (by rfl) ⟨649043, by rfl⟩ : syracuseStep 865391 = 1298087) B1298087
theorem B2930687 : Blo 864565 2930687 := bstep (se 1 (by rfl) ⟨2198015, by rfl⟩ : syracuseStep 2930687 = 4396031) B4396031
theorem B866543 : Blo 864565 866543 := bstep (se 1 (by rfl) ⟨649907, by rfl⟩ : syracuseStep 866543 = 1299815) B1299815
theorem B866559 : Blo 864565 866559 := bstep (se 1 (by rfl) ⟨649919, by rfl⟩ : syracuseStep 866559 = 1299839) B1299839
theorem B21118553 : Blo 864565 21118553 := bstep (se 2 (by rfl) ⟨7919457, by rfl⟩ : syracuseStep 21118553 = 15838915) B15838915
theorem B1949471 : Blo 864565 1949471 := bstep (se 1 (by rfl) ⟨1462103, by rfl⟩ : syracuseStep 1949471 = 2924207) B2924207
theorem B1097707 : Blo 864565 1097707 := bstep (se 1 (by rfl) ⟨823280, by rfl⟩ : syracuseStep 1097707 = 1646561) B1646561
theorem B12665807 : Blo 864565 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B1950875 : Blo 864565 1950875 := bstep (se 1 (by rfl) ⟨1463156, by rfl⟩ : syracuseStep 1950875 = 2926313) B2926313
theorem B69452957 : Blo 864565 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B1459451 : Blo 864565 1459451 := bstep (se 1 (by rfl) ⟨1094588, by rfl⟩ : syracuseStep 1459451 = 2189177) B2189177
theorem B1951199 : Blo 864565 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B1459687 : Blo 864565 1459687 := bstep (se 1 (by rfl) ⟨1094765, by rfl⟩ : syracuseStep 1459687 = 2189531) B2189531
theorem B5916169 : Blo 864565 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B7620779 : Blo 864565 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B3295687 : Blo 864565 3295687 := bstep (se 1 (by rfl) ⟨2471765, by rfl⟩ : syracuseStep 3295687 = 4943531) B4943531
theorem B1952423 : Blo 864565 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B1854569 : Blo 864565 1854569 := bstep (se 2 (by rfl) ⟨695463, by rfl⟩ : syracuseStep 1854569 = 1390927) B1390927
theorem B1297727 : Blo 864565 1297727 := bstep (se 1 (by rfl) ⟨973295, by rfl⟩ : syracuseStep 1297727 = 1946591) B1946591
theorem B1954151 : Blo 864565 1954151 := bstep (se 1 (by rfl) ⟨1465613, by rfl⟩ : syracuseStep 1954151 = 2931227) B2931227
theorem B142529219 : Blo 864565 142529219 := bstep (se 1 (by rfl) ⟨106896914, by rfl⟩ : syracuseStep 142529219 = 213793829) B213793829
theorem B1233787 : Blo 864565 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B1463231 : Blo 864565 1463231 := bstep (se 1 (by rfl) ⟨1097423, by rfl⟩ : syracuseStep 1463231 = 2194847) B2194847
theorem B1464527 : Blo 864565 1464527 := bstep (se 1 (by rfl) ⟨1098395, by rfl⟩ : syracuseStep 1464527 = 2196791) B2196791
theorem B10541477 : Blo 864565 10541477 := bstep (se 4 (by rfl) ⟨988263, by rfl⟩ : syracuseStep 10541477 = 1976527) B1976527
theorem B10020485 : Blo 864565 10020485 := bstep (se 4 (by rfl) ⟨939420, by rfl⟩ : syracuseStep 10020485 = 1878841) B1878841
theorem B127952621 : Blo 864565 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B30371023 : Blo 864565 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B2190827 : Blo 864565 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B1110719 : Blo 864565 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2192255 : Blo 864565 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B20247725 : Blo 864565 20247725 := bstep (se 3 (by rfl) ⟨3796448, by rfl⟩ : syracuseStep 20247725 = 7592897) B7592897
theorem B4158803 : Blo 864565 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B4388255 : Blo 864565 4388255 := bstep (se 1 (by rfl) ⟨3291191, by rfl⟩ : syracuseStep 4388255 = 6582383) B6582383
theorem B4389227 : Blo 864565 4389227 := bstep (se 1 (by rfl) ⟨3291920, by rfl⟩ : syracuseStep 4389227 = 6583841) B6583841
theorem B2194087 : Blo 864565 2194087 := bstep (se 1 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 2194087 = 3291131) B3291131
theorem B106691975 : Blo 864565 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B46301971 : Blo 864565 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B5080519 : Blo 864565 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B1444267 : Blo 864565 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B4394249 : Blo 864565 4394249 := bstep (se 2 (by rfl) ⟨1647843, by rfl⟩ : syracuseStep 4394249 = 3295687) B3295687
theorem B15799799 : Blo 864565 15799799 := bstep (se 1 (by rfl) ⟨11849849, by rfl⟩ : syracuseStep 15799799 = 23699699) B23699699
theorem B1644799 : Blo 864565 1644799 := bstep (se 1 (by rfl) ⟨1233599, by rfl⟩ : syracuseStep 1644799 = 2467199) B2467199
theorem B85301747 : Blo 864565 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B1645049 : Blo 864565 1645049 := bstep (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) B1233787
theorem B8330525 : Blo 864565 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B9379799 : Blo 864565 9379799 := bstep (se 1 (by rfl) ⟨7034849, by rfl⟩ : syracuseStep 9379799 = 14069699) B14069699
theorem B925759 : Blo 864565 925759 := bstep (se 1 (by rfl) ⟨694319, by rfl⟩ : syracuseStep 925759 = 1388639) B1388639
theorem B2925449 : Blo 864565 2925449 := bstep (se 2 (by rfl) ⟨1097043, by rfl⟩ : syracuseStep 2925449 = 2194087) B2194087
theorem B2925503 : Blo 864565 2925503 := bstep (se 1 (by rfl) ⟨2194127, by rfl⟩ : syracuseStep 2925503 = 4388255) B4388255
theorem B2926151 : Blo 864565 2926151 := bstep (se 1 (by rfl) ⟨2194613, by rfl⟩ : syracuseStep 2926151 = 4389227) B4389227
theorem B48147311 : Blo 864565 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B23768453 : Blo 864565 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B1945295 : Blo 864565 1945295 := bstep (se 1 (by rfl) ⟨1458971, by rfl⟩ : syracuseStep 1945295 = 2917943) B2917943
theorem B1945835 : Blo 864565 1945835 := bstep (se 1 (by rfl) ⟨1459376, by rfl⟩ : syracuseStep 1945835 = 2918753) B2918753
theorem B2961917 : Blo 864565 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B1946249 : Blo 864565 1946249 := bstep (se 2 (by rfl) ⟨729843, by rfl⟩ : syracuseStep 1946249 = 1459687) B1459687
theorem B865151 : Blo 864565 865151 := bstep (se 1 (by rfl) ⟨648863, by rfl⟩ : syracuseStep 865151 = 1297727) B1297727
theorem B170931505 : Blo 864565 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B1947167 : Blo 864565 1947167 := bstep (se 1 (by rfl) ⟨1460375, by rfl⟩ : syracuseStep 1947167 = 2920751) B2920751
theorem B1095535 : Blo 864565 1095535 := bstep (se 1 (by rfl) ⟨821651, by rfl⟩ : syracuseStep 1095535 = 1643303) B1643303
theorem B11090141 : Blo 864565 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B1947923 : Blo 864565 1947923 := bstep (se 1 (by rfl) ⟨1460942, by rfl⟩ : syracuseStep 1947923 = 2921885) B2921885
theorem B7027651 : Blo 864565 7027651 := bstep (se 1 (by rfl) ⟨5270738, by rfl⟩ : syracuseStep 7027651 = 10541477) B10541477
theorem B1460551 : Blo 864565 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B1461503 : Blo 864565 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B1953791 : Blo 864565 1953791 := bstep (se 1 (by rfl) ⟨1465343, by rfl⟩ : syracuseStep 1953791 = 2930687) B2930687
theorem B71127983 : Blo 864565 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B14079035 : Blo 864565 14079035 := bstep (se 1 (by rfl) ⟨10559276, by rfl⟩ : syracuseStep 14079035 = 21118553) B21118553
theorem B1299647 : Blo 864565 1299647 := bstep (se 1 (by rfl) ⟨974735, by rfl⟩ : syracuseStep 1299647 = 1949471) B1949471
theorem B1463609 : Blo 864565 1463609 := bstep (se 2 (by rfl) ⟨548853, by rfl⟩ : syracuseStep 1463609 = 1097707) B1097707
theorem B8443871 : Blo 864565 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B1300583 : Blo 864565 1300583 := bstep (se 1 (by rfl) ⟨975437, by rfl⟩ : syracuseStep 1300583 = 1950875) B1950875
theorem B972967 : Blo 864565 972967 := bstep (se 1 (by rfl) ⟨729725, by rfl⟩ : syracuseStep 972967 = 1459451) B1459451
theorem B1300799 : Blo 864565 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B1301615 : Blo 864565 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B7888225 : Blo 864565 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B1236379 : Blo 864565 1236379 := bstep (se 1 (by rfl) ⟨927284, by rfl⟩ : syracuseStep 1236379 = 1854569) B1854569
theorem B1302767 : Blo 864565 1302767 := bstep (se 1 (by rfl) ⟨977075, by rfl⟩ : syracuseStep 1302767 = 1954151) B1954151
theorem B95019479 : Blo 864565 95019479 := bstep (se 1 (by rfl) ⟨71264609, by rfl⟩ : syracuseStep 95019479 = 142529219) B142529219
theorem B975487 : Blo 864565 975487 := bstep (se 1 (by rfl) ⟨731615, by rfl⟩ : syracuseStep 975487 = 1463231) B1463231
theorem B976351 : Blo 864565 976351 := bstep (se 1 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 976351 = 1464527) B1464527
theorem B40494697 : Blo 864565 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B6680323 : Blo 864565 6680323 := bstep (se 1 (by rfl) ⟨5010242, by rfl⟩ : syracuseStep 6680323 = 10020485) B10020485
theorem B13498483 : Blo 864565 13498483 := bstep (se 1 (by rfl) ⟨10123862, by rfl⟩ : syracuseStep 13498483 = 20247725) B20247725
theorem B6256889 : Blo 864565 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B61735961 : Blo 864565 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B47418655 : Blo 864565 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B63346319 : Blo 864565 63346319 := bstep (se 1 (by rfl) ⟨47509739, by rfl⟩ : syracuseStep 63346319 = 95019479) B95019479
theorem B227908673 : Blo 864565 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B17997977 : Blo 864565 17997977 := bstep (se 2 (by rfl) ⟨6749241, by rfl⟩ : syracuseStep 17997977 = 13498483) B13498483
theorem B1974611 : Blo 864565 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B4171259 : Blo 864565 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B1648505 : Blo 864565 1648505 := bstep (se 2 (by rfl) ⟨618189, by rfl⟩ : syracuseStep 1648505 = 1236379) B1236379
theorem B2929499 : Blo 864565 2929499 := bstep (se 1 (by rfl) ⟨2197124, by rfl⟩ : syracuseStep 2929499 = 4394249) B4394249
theorem B1947401 : Blo 864565 1947401 := bstep (se 2 (by rfl) ⟨730275, by rfl⟩ : syracuseStep 1947401 = 1460551) B1460551
theorem B866431 : Blo 864565 866431 := bstep (se 1 (by rfl) ⟨649823, by rfl⟩ : syracuseStep 866431 = 1299647) B1299647
theorem B867055 : Blo 864565 867055 := bstep (se 1 (by rfl) ⟨650291, by rfl⟩ : syracuseStep 867055 = 1300583) B1300583
theorem B867199 : Blo 864565 867199 := bstep (se 1 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 867199 = 1300799) B1300799
theorem B56867831 : Blo 864565 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B867743 : Blo 864565 867743 := bstep (se 1 (by rfl) ⟨650807, by rfl⟩ : syracuseStep 867743 = 1301615) B1301615
theorem B5553683 : Blo 864565 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B868511 : Blo 864565 868511 := bstep (se 1 (by rfl) ⟨651383, by rfl⟩ : syracuseStep 868511 = 1302767) B1302767
theorem B1950299 : Blo 864565 1950299 := bstep (se 1 (by rfl) ⟨1462724, by rfl⟩ : syracuseStep 1950299 = 2925449) B2925449
theorem B1950335 : Blo 864565 1950335 := bstep (se 1 (by rfl) ⟨1462751, by rfl⟩ : syracuseStep 1950335 = 2925503) B2925503
theorem B1950767 : Blo 864565 1950767 := bstep (se 1 (by rfl) ⟨1463075, by rfl⟩ : syracuseStep 1950767 = 2926151) B2926151
theorem B32098207 : Blo 864565 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B15845635 : Blo 864565 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B1296863 : Blo 864565 1296863 := bstep (se 1 (by rfl) ⟨972647, by rfl⟩ : syracuseStep 1296863 = 1945295) B1945295
theorem B1460713 : Blo 864565 1460713 := bstep (se 2 (by rfl) ⟨547767, by rfl⟩ : syracuseStep 1460713 = 1095535) B1095535
theorem B1297223 : Blo 864565 1297223 := bstep (se 1 (by rfl) ⟨972917, by rfl⟩ : syracuseStep 1297223 = 1945835) B1945835
theorem B1297289 : Blo 864565 1297289 := bstep (se 2 (by rfl) ⟨486483, by rfl⟩ : syracuseStep 1297289 = 972967) B972967
theorem B1297499 : Blo 864565 1297499 := bstep (se 1 (by rfl) ⟨973124, by rfl⟩ : syracuseStep 1297499 = 1946249) B1946249
theorem B1298111 : Blo 864565 1298111 := bstep (se 1 (by rfl) ⟨973583, by rfl⟩ : syracuseStep 1298111 = 1947167) B1947167
theorem B7393427 : Blo 864565 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B1298615 : Blo 864565 1298615 := bstep (se 1 (by rfl) ⟨973961, by rfl⟩ : syracuseStep 1298615 = 1947923) B1947923
theorem B4937381 : Blo 864565 4937381 := bstep (se 4 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 4937381 = 925759) B925759
theorem B1300649 : Blo 864565 1300649 := bstep (se 2 (by rfl) ⟨487743, by rfl⟩ : syracuseStep 1300649 = 975487) B975487
theorem B6774025 : Blo 864565 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B1301801 : Blo 864565 1301801 := bstep (se 2 (by rfl) ⟨488175, by rfl⟩ : syracuseStep 1301801 = 976351) B976351
theorem B974335 : Blo 864565 974335 := bstep (se 1 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 974335 = 1461503) B1461503
theorem B1302527 : Blo 864565 1302527 := bstep (se 1 (by rfl) ⟨976895, by rfl⟩ : syracuseStep 1302527 = 1953791) B1953791
theorem B37544093 : Blo 864565 37544093 := bstep (se 3 (by rfl) ⟨7039517, by rfl⟩ : syracuseStep 37544093 = 14079035) B14079035
theorem B1925689 : Blo 864565 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B975739 : Blo 864565 975739 := bstep (se 1 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 975739 = 1463609) B1463609
theorem B42132797 : Blo 864565 42132797 := bstep (se 3 (by rfl) ⟨7899899, by rfl⟩ : syracuseStep 42132797 = 15799799) B15799799
theorem B5629247 : Blo 864565 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B8907097 : Blo 864565 8907097 := bstep (se 2 (by rfl) ⟨3340161, by rfl⟩ : syracuseStep 8907097 = 6680323) B6680323
theorem B6253199 : Blo 864565 6253199 := bstep (se 1 (by rfl) ⟨4689899, by rfl⟩ : syracuseStep 6253199 = 9379799) B9379799
theorem B4386797 : Blo 864565 4386797 := bstep (se 3 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 4386797 = 1645049) B1645049
theorem B2193065 : Blo 864565 2193065 := bstep (se 2 (by rfl) ⟨822399, by rfl⟩ : syracuseStep 2193065 = 1644799) B1644799
theorem B215971717 : Blo 864565 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B9370201 : Blo 864565 9370201 := bstep (se 2 (by rfl) ⟨3513825, by rfl⟩ : syracuseStep 9370201 = 7027651) B7027651
theorem B10517633 : Blo 864565 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B41157307 : Blo 864565 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B42797609 : Blo 864565 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B1316407 : Blo 864565 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B28088531 : Blo 864565 28088531 := bstep (se 1 (by rfl) ⟨21066398, by rfl⟩ : syracuseStep 28088531 = 42132797) B42132797
theorem B4168799 : Blo 864565 4168799 := bstep (se 1 (by rfl) ⟨3126599, by rfl⟩ : syracuseStep 4168799 = 6253199) B6253199
theorem B2924531 : Blo 864565 2924531 := bstep (se 1 (by rfl) ⟨2193398, by rfl⟩ : syracuseStep 2924531 = 4386797) B4386797
theorem B12493601 : Blo 864565 12493601 := bstep (se 2 (by rfl) ⟨4685100, by rfl⟩ : syracuseStep 12493601 = 9370201) B9370201
theorem B2567585 : Blo 864565 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B864575 : Blo 864565 864575 := bstep (se 1 (by rfl) ⟨648431, by rfl⟩ : syracuseStep 864575 = 1296863) B1296863
theorem B864815 : Blo 864565 864815 := bstep (se 1 (by rfl) ⟨648611, by rfl⟩ : syracuseStep 864815 = 1297223) B1297223
theorem B864859 : Blo 864565 864859 := bstep (se 1 (by rfl) ⟨648644, by rfl⟩ : syracuseStep 864859 = 1297289) B1297289
theorem B864999 : Blo 864565 864999 := bstep (se 1 (by rfl) ⟨648749, by rfl⟩ : syracuseStep 864999 = 1297499) B1297499
theorem B865407 : Blo 864565 865407 := bstep (se 1 (by rfl) ⟨649055, by rfl⟩ : syracuseStep 865407 = 1298111) B1298111
theorem B4928951 : Blo 864565 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B865743 : Blo 864565 865743 := bstep (se 1 (by rfl) ⟨649307, by rfl⟩ : syracuseStep 865743 = 1298615) B1298615
theorem B11876129 : Blo 864565 11876129 := bstep (se 2 (by rfl) ⟨4453548, by rfl⟩ : syracuseStep 11876129 = 8907097) B8907097
theorem B1947617 : Blo 864565 1947617 := bstep (se 2 (by rfl) ⟨730356, by rfl⟩ : syracuseStep 1947617 = 1460713) B1460713
theorem B3291587 : Blo 864565 3291587 := bstep (se 1 (by rfl) ⟨2468690, by rfl⟩ : syracuseStep 3291587 = 4937381) B4937381
theorem B867099 : Blo 864565 867099 := bstep (se 1 (by rfl) ⟨650324, by rfl⟩ : syracuseStep 867099 = 1300649) B1300649
theorem B63224873 : Blo 864565 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B867867 : Blo 864565 867867 := bstep (se 1 (by rfl) ⟨650900, by rfl⟩ : syracuseStep 867867 = 1301801) B1301801
theorem B868351 : Blo 864565 868351 := bstep (se 1 (by rfl) ⟨651263, by rfl⟩ : syracuseStep 868351 = 1302527) B1302527
theorem B3752831 : Blo 864565 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B1099003 : Blo 864565 1099003 := bstep (se 1 (by rfl) ⟨824252, by rfl⟩ : syracuseStep 1099003 = 1648505) B1648505
theorem B1952999 : Blo 864565 1952999 := bstep (se 1 (by rfl) ⟨1464749, by rfl⟩ : syracuseStep 1952999 = 2929499) B2929499
theorem B1462043 : Blo 864565 1462043 := bstep (se 1 (by rfl) ⟨1096532, by rfl⟩ : syracuseStep 1462043 = 2193065) B2193065
theorem B1298267 : Blo 864565 1298267 := bstep (se 1 (by rfl) ⟨973700, by rfl⟩ : syracuseStep 1298267 = 1947401) B1947401
theorem B9032033 : Blo 864565 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B1299113 : Blo 864565 1299113 := bstep (se 2 (by rfl) ⟨487167, by rfl⟩ : syracuseStep 1299113 = 974335) B974335
theorem B1300199 : Blo 864565 1300199 := bstep (se 1 (by rfl) ⟨975149, by rfl⟩ : syracuseStep 1300199 = 1950299) B1950299
theorem B47994605 : Blo 864565 47994605 := bstep (se 3 (by rfl) ⟨8998988, by rfl⟩ : syracuseStep 47994605 = 17997977) B17997977
theorem B1300223 : Blo 864565 1300223 := bstep (se 1 (by rfl) ⟨975167, by rfl⟩ : syracuseStep 1300223 = 1950335) B1950335
theorem B1300511 : Blo 864565 1300511 := bstep (se 1 (by rfl) ⟨975383, by rfl⟩ : syracuseStep 1300511 = 1950767) B1950767
theorem B1300985 : Blo 864565 1300985 := bstep (se 2 (by rfl) ⟨487869, by rfl⟩ : syracuseStep 1300985 = 975739) B975739
theorem B21127513 : Blo 864565 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B42230879 : Blo 864565 42230879 := bstep (se 1 (by rfl) ⟨31673159, by rfl⟩ : syracuseStep 42230879 = 63346319) B63346319
theorem B151939115 : Blo 864565 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B25029395 : Blo 864565 25029395 := bstep (se 1 (by rfl) ⟨18772046, by rfl⟩ : syracuseStep 25029395 = 37544093) B37544093
theorem B2780839 : Blo 864565 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B287962289 : Blo 864565 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B37911887 : Blo 864565 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B7011755 : Blo 864565 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B3702455 : Blo 864565 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B24085421 : Blo 864565 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B3707785 : Blo 864565 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B8329067 : Blo 864565 8329067 := bstep (se 1 (by rfl) ⟨6246800, by rfl⟩ : syracuseStep 8329067 = 12493601) B12493601
theorem B28153919 : Blo 864565 28153919 := bstep (se 1 (by rfl) ⟨21115439, by rfl⟩ : syracuseStep 28153919 = 42230879) B42230879
theorem B101292743 : Blo 864565 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B16686263 : Blo 864565 16686263 := bstep (se 1 (by rfl) ⟨12514697, by rfl⟩ : syracuseStep 16686263 = 25029395) B25029395
theorem B3285967 : Blo 864565 3285967 := bstep (se 1 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 3285967 = 4928951) B4928951
theorem B42149915 : Blo 864565 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B25274591 : Blo 864565 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B2468303 : Blo 864565 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B10007549 : Blo 864565 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B865511 : Blo 864565 865511 := bstep (se 1 (by rfl) ⟨649133, by rfl⟩ : syracuseStep 865511 = 1298267) B1298267
theorem B866075 : Blo 864565 866075 := bstep (se 1 (by rfl) ⟨649556, by rfl⟩ : syracuseStep 866075 = 1299113) B1299113
theorem B866799 : Blo 864565 866799 := bstep (se 1 (by rfl) ⟨650099, by rfl⟩ : syracuseStep 866799 = 1300199) B1300199
theorem B31996403 : Blo 864565 31996403 := bstep (se 1 (by rfl) ⟨23997302, by rfl⟩ : syracuseStep 31996403 = 47994605) B47994605
theorem B866815 : Blo 864565 866815 := bstep (se 1 (by rfl) ⟨650111, by rfl⟩ : syracuseStep 866815 = 1300223) B1300223
theorem B867007 : Blo 864565 867007 := bstep (se 1 (by rfl) ⟨650255, by rfl⟩ : syracuseStep 867007 = 1300511) B1300511
theorem B18725687 : Blo 864565 18725687 := bstep (se 1 (by rfl) ⟨14044265, by rfl⟩ : syracuseStep 18725687 = 28088531) B28088531
theorem B867323 : Blo 864565 867323 := bstep (se 1 (by rfl) ⟨650492, by rfl⟩ : syracuseStep 867323 = 1300985) B1300985
theorem B1949687 : Blo 864565 1949687 := bstep (se 1 (by rfl) ⟨1462265, by rfl⟩ : syracuseStep 1949687 = 2924531) B2924531
theorem B1755209 : Blo 864565 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B191974859 : Blo 864565 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B7917419 : Blo 864565 7917419 := bstep (se 1 (by rfl) ⟨5938064, by rfl⟩ : syracuseStep 7917419 = 11876129) B11876129
theorem B1298411 : Blo 864565 1298411 := bstep (se 1 (by rfl) ⟨973808, by rfl⟩ : syracuseStep 1298411 = 1947617) B1947617
theorem B4674503 : Blo 864565 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B28170017 : Blo 864565 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B54876409 : Blo 864565 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B1465337 : Blo 864565 1465337 := bstep (se 2 (by rfl) ⟨549501, by rfl⟩ : syracuseStep 1465337 = 1099003) B1099003
theorem B28531739 : Blo 864565 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B1301999 : Blo 864565 1301999 := bstep (se 1 (by rfl) ⟨976499, by rfl⟩ : syracuseStep 1301999 = 1952999) B1952999
theorem B974695 : Blo 864565 974695 := bstep (se 1 (by rfl) ⟨731021, by rfl⟩ : syracuseStep 974695 = 1462043) B1462043
theorem B2779199 : Blo 864565 2779199 := bstep (se 1 (by rfl) ⟨2084399, by rfl⟩ : syracuseStep 2779199 = 4168799) B4168799
theorem B6846893 : Blo 864565 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B2194391 : Blo 864565 2194391 := bstep (se 1 (by rfl) ⟨1645793, by rfl⟩ : syracuseStep 2194391 = 3291587) B3291587
theorem B16056947 : Blo 864565 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B5278279 : Blo 864565 5278279 := bstep (se 1 (by rfl) ⟨3958709, by rfl⟩ : syracuseStep 5278279 = 7917419) B7917419
theorem B3116335 : Blo 864565 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B18780011 : Blo 864565 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B16849727 : Blo 864565 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B1645535 : Blo 864565 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B4564595 : Blo 864565 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B865607 : Blo 864565 865607 := bstep (se 1 (by rfl) ⟨649205, by rfl⟩ : syracuseStep 865607 = 1298411) B1298411
theorem B5552711 : Blo 864565 5552711 := bstep (se 1 (by rfl) ⟨4164533, by rfl⟩ : syracuseStep 5552711 = 8329067) B8329067
theorem B19021159 : Blo 864565 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B11124175 : Blo 864565 11124175 := bstep (se 1 (by rfl) ⟨8343131, by rfl⟩ : syracuseStep 11124175 = 16686263) B16686263
theorem B867999 : Blo 864565 867999 := bstep (se 1 (by rfl) ⟨650999, by rfl⟩ : syracuseStep 867999 = 1301999) B1301999
theorem B28099943 : Blo 864565 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B1852799 : Blo 864565 1852799 := bstep (se 1 (by rfl) ⟨1389599, by rfl⟩ : syracuseStep 1852799 = 2779199) B2779199
theorem B6671699 : Blo 864565 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B1462927 : Blo 864565 1462927 := bstep (se 1 (by rfl) ⟨1097195, by rfl⟩ : syracuseStep 1462927 = 2194391) B2194391
theorem B1299593 : Blo 864565 1299593 := bstep (se 2 (by rfl) ⟨487347, by rfl⟩ : syracuseStep 1299593 = 974695) B974695
theorem B1299791 : Blo 864565 1299791 := bstep (se 1 (by rfl) ⟨974843, by rfl⟩ : syracuseStep 1299791 = 1949687) B1949687
theorem B4381289 : Blo 864565 4381289 := bstep (se 2 (by rfl) ⟨1642983, by rfl⟩ : syracuseStep 4381289 = 3285967) B3285967
theorem B292674181 : Blo 864565 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B127983239 : Blo 864565 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B18769279 : Blo 864565 18769279 := bstep (se 1 (by rfl) ⟨14076959, by rfl⟩ : syracuseStep 18769279 = 28153919) B28153919
theorem B67528495 : Blo 864565 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B976891 : Blo 864565 976891 := bstep (se 1 (by rfl) ⟨732668, by rfl⟩ : syracuseStep 976891 = 1465337) B1465337
theorem B4680557 : Blo 864565 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B4943713 : Blo 864565 4943713 := bstep (se 2 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 4943713 = 3707785) B3707785
theorem B21330935 : Blo 864565 21330935 := bstep (se 1 (by rfl) ⟨15998201, by rfl⟩ : syracuseStep 21330935 = 31996403) B31996403
theorem B12483791 : Blo 864565 12483791 := bstep (se 1 (by rfl) ⟨9362843, by rfl⟩ : syracuseStep 12483791 = 18725687) B18725687
theorem B12520007 : Blo 864565 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B2920859 : Blo 864565 2920859 := bstep (se 1 (by rfl) ⟨2190644, by rfl⟩ : syracuseStep 2920859 = 4381289) B4381289
theorem B6591617 : Blo 864565 6591617 := bstep (se 2 (by rfl) ⟨2471856, by rfl⟩ : syracuseStep 6591617 = 4943713) B4943713
theorem B3120371 : Blo 864565 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B866395 : Blo 864565 866395 := bstep (se 1 (by rfl) ⟨649796, by rfl⟩ : syracuseStep 866395 = 1299593) B1299593
theorem B866527 : Blo 864565 866527 := bstep (se 1 (by rfl) ⟨649895, by rfl⟩ : syracuseStep 866527 = 1299791) B1299791
theorem B1950569 : Blo 864565 1950569 := bstep (se 2 (by rfl) ⟨731463, by rfl⟩ : syracuseStep 1950569 = 1462927) B1462927
theorem B14832233 : Blo 864565 14832233 := bstep (se 2 (by rfl) ⟨5562087, by rfl⟩ : syracuseStep 14832233 = 11124175) B11124175
theorem B10704631 : Blo 864565 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B18733295 : Blo 864565 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B25025705 : Blo 864565 25025705 := bstep (se 2 (by rfl) ⟨9384639, by rfl⟩ : syracuseStep 25025705 = 18769279) B18769279
theorem B4447799 : Blo 864565 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B90037993 : Blo 864565 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B1302521 : Blo 864565 1302521 := bstep (se 2 (by rfl) ⟨488445, by rfl⟩ : syracuseStep 1302521 = 976891) B976891
theorem B7037705 : Blo 864565 7037705 := bstep (se 2 (by rfl) ⟨2639139, by rfl⟩ : syracuseStep 7037705 = 5278279) B5278279
theorem B4940797 : Blo 864565 4940797 := bstep (se 3 (by rfl) ⟨926399, by rfl⟩ : syracuseStep 4940797 = 1852799) B1852799
theorem B4155113 : Blo 864565 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B11233151 : Blo 864565 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B85322159 : Blo 864565 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B3043063 : Blo 864565 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B101446181 : Blo 864565 101446181 := bstep (se 4 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 101446181 = 19021159) B19021159
theorem B4388093 : Blo 864565 4388093 := bstep (se 3 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 4388093 = 1645535) B1645535
theorem B390232241 : Blo 864565 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B3701807 : Blo 864565 3701807 := bstep (se 1 (by rfl) ⟨2776355, by rfl⟩ : syracuseStep 3701807 = 5552711) B5552711
theorem B14220623 : Blo 864565 14220623 := bstep (se 1 (by rfl) ⟨10665467, by rfl⟩ : syracuseStep 14220623 = 21330935) B21330935
theorem B8322527 : Blo 864565 8322527 := bstep (se 1 (by rfl) ⟨6241895, by rfl⟩ : syracuseStep 8322527 = 12483791) B12483791
theorem B6587729 : Blo 864565 6587729 := bstep (se 2 (by rfl) ⟨2470398, by rfl⟩ : syracuseStep 6587729 = 4940797) B4940797
theorem B4394411 : Blo 864565 4394411 := bstep (se 1 (by rfl) ⟨3295808, by rfl⟩ : syracuseStep 4394411 = 6591617) B6591617
theorem B16683803 : Blo 864565 16683803 := bstep (se 1 (by rfl) ⟨12512852, by rfl⟩ : syracuseStep 16683803 = 25025705) B25025705
theorem B4691803 : Blo 864565 4691803 := bstep (se 1 (by rfl) ⟨3518852, by rfl⟩ : syracuseStep 4691803 = 7037705) B7037705
theorem B2925395 : Blo 864565 2925395 := bstep (se 1 (by rfl) ⟨2194046, by rfl⟩ : syracuseStep 2925395 = 4388093) B4388093
theorem B260154827 : Blo 864565 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B2467871 : Blo 864565 2467871 := bstep (se 1 (by rfl) ⟨1850903, by rfl⟩ : syracuseStep 2467871 = 3701807) B3701807
theorem B9480415 : Blo 864565 9480415 := bstep (se 1 (by rfl) ⟨7110311, by rfl⟩ : syracuseStep 9480415 = 14220623) B14220623
theorem B5548351 : Blo 864565 5548351 := bstep (se 1 (by rfl) ⟨4161263, by rfl⟩ : syracuseStep 5548351 = 8322527) B8322527
theorem B1947239 : Blo 864565 1947239 := bstep (se 1 (by rfl) ⟨1460429, by rfl⟩ : syracuseStep 1947239 = 2920859) B2920859
theorem B2080247 : Blo 864565 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B2965199 : Blo 864565 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B868347 : Blo 864565 868347 := bstep (se 1 (by rfl) ⟨651260, by rfl⟩ : syracuseStep 868347 = 1302521) B1302521
theorem B49955453 : Blo 864565 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B2770075 : Blo 864565 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B7488767 : Blo 864565 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B14272841 : Blo 864565 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B120050657 : Blo 864565 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B1300379 : Blo 864565 1300379 := bstep (se 1 (by rfl) ⟨975284, by rfl⟩ : syracuseStep 1300379 = 1950569) B1950569
theorem B8346671 : Blo 864565 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B9888155 : Blo 864565 9888155 := bstep (se 1 (by rfl) ⟨7416116, by rfl⟩ : syracuseStep 9888155 = 14832233) B14832233
theorem B4057417 : Blo 864565 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B56881439 : Blo 864565 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B67630787 : Blo 864565 67630787 := bstep (se 1 (by rfl) ⟨50723090, by rfl⟩ : syracuseStep 67630787 = 101446181) B101446181
theorem B4391819 : Blo 864565 4391819 := bstep (se 1 (by rfl) ⟨3293864, by rfl⟩ : syracuseStep 4391819 = 6587729) B6587729
theorem B22189301 : Blo 864565 22189301 := bstep (se 5 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 22189301 = 2080247) B2080247
theorem B6592103 : Blo 864565 6592103 := bstep (se 1 (by rfl) ⟨4944077, by rfl⟩ : syracuseStep 6592103 = 9888155) B9888155
theorem B1645247 : Blo 864565 1645247 := bstep (se 1 (by rfl) ⟨1233935, by rfl⟩ : syracuseStep 1645247 = 2467871) B2467871
theorem B31628789 : Blo 864565 31628789 := bstep (se 5 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 31628789 = 2965199) B2965199
theorem B37920959 : Blo 864565 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B33303635 : Blo 864565 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B4992511 : Blo 864565 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B9515227 : Blo 864565 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B21639557 : Blo 864565 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B2929607 : Blo 864565 2929607 := bstep (se 1 (by rfl) ⟨2197205, by rfl⟩ : syracuseStep 2929607 = 4394411) B4394411
theorem B11122535 : Blo 864565 11122535 := bstep (se 1 (by rfl) ⟨8341901, by rfl⟩ : syracuseStep 11122535 = 16683803) B16683803
theorem B80033771 : Blo 864565 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B866919 : Blo 864565 866919 := bstep (se 1 (by rfl) ⟨650189, by rfl⟩ : syracuseStep 866919 = 1300379) B1300379
theorem B1950263 : Blo 864565 1950263 := bstep (se 1 (by rfl) ⟨1462697, by rfl⟩ : syracuseStep 1950263 = 2925395) B2925395
theorem B1298159 : Blo 864565 1298159 := bstep (se 1 (by rfl) ⟨973619, by rfl⟩ : syracuseStep 1298159 = 1947239) B1947239
theorem B3693433 : Blo 864565 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B12640553 : Blo 864565 12640553 := bstep (se 2 (by rfl) ⟨4740207, by rfl⟩ : syracuseStep 12640553 = 9480415) B9480415
theorem B7397801 : Blo 864565 7397801 := bstep (se 2 (by rfl) ⟨2774175, by rfl⟩ : syracuseStep 7397801 = 5548351) B5548351
theorem B5564447 : Blo 864565 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B173436551 : Blo 864565 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B6255737 : Blo 864565 6255737 := bstep (se 2 (by rfl) ⟨2345901, by rfl⟩ : syracuseStep 6255737 = 4691803) B4691803
theorem B45087191 : Blo 864565 45087191 := bstep (se 1 (by rfl) ⟨33815393, by rfl⟩ : syracuseStep 45087191 = 67630787) B67630787
theorem B4394735 : Blo 864565 4394735 := bstep (se 1 (by rfl) ⟨3296051, by rfl⟩ : syracuseStep 4394735 = 6592103) B6592103
theorem B6656681 : Blo 864565 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B8427035 : Blo 864565 8427035 := bstep (se 1 (by rfl) ⟨6320276, by rfl⟩ : syracuseStep 8427035 = 12640553) B12640553
theorem B12686969 : Blo 864565 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B3709631 : Blo 864565 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B14426371 : Blo 864565 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B4170491 : Blo 864565 4170491 := bstep (se 1 (by rfl) ⟨3127868, by rfl⟩ : syracuseStep 4170491 = 6255737) B6255737
theorem B4924577 : Blo 864565 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B7415023 : Blo 864565 7415023 := bstep (se 1 (by rfl) ⟨5561267, by rfl⟩ : syracuseStep 7415023 = 11122535) B11122535
theorem B53355847 : Blo 864565 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B30058127 : Blo 864565 30058127 := bstep (se 1 (by rfl) ⟨22543595, by rfl⟩ : syracuseStep 30058127 = 45087191) B45087191
theorem B2927879 : Blo 864565 2927879 := bstep (se 1 (by rfl) ⟨2195909, by rfl⟩ : syracuseStep 2927879 = 4391819) B4391819
theorem B865439 : Blo 864565 865439 := bstep (se 1 (by rfl) ⟨649079, by rfl⟩ : syracuseStep 865439 = 1298159) B1298159
theorem B14792867 : Blo 864565 14792867 := bstep (se 1 (by rfl) ⟨11094650, by rfl⟩ : syracuseStep 14792867 = 22189301) B22189301
theorem B1096831 : Blo 864565 1096831 := bstep (se 1 (by rfl) ⟨822623, by rfl⟩ : syracuseStep 1096831 = 1645247) B1645247
theorem B21085859 : Blo 864565 21085859 := bstep (se 1 (by rfl) ⟨15814394, by rfl⟩ : syracuseStep 21085859 = 31628789) B31628789
theorem B25280639 : Blo 864565 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B4931867 : Blo 864565 4931867 := bstep (se 1 (by rfl) ⟨3698900, by rfl⟩ : syracuseStep 4931867 = 7397801) B7397801
theorem B22202423 : Blo 864565 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B115624367 : Blo 864565 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1953071 : Blo 864565 1953071 := bstep (se 1 (by rfl) ⟨1464803, by rfl⟩ : syracuseStep 1953071 = 2929607) B2929607
theorem B1300175 : Blo 864565 1300175 := bstep (se 1 (by rfl) ⟨975131, by rfl⟩ : syracuseStep 1300175 = 1950263) B1950263
theorem B19235161 : Blo 864565 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B71141129 : Blo 864565 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B8457979 : Blo 864565 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B3283051 : Blo 864565 3283051 := bstep (se 1 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 3283051 = 4924577) B4924577
theorem B16853759 : Blo 864565 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B3287911 : Blo 864565 3287911 := bstep (se 1 (by rfl) ⟨2465933, by rfl⟩ : syracuseStep 3287911 = 4931867) B4931867
theorem B77082911 : Blo 864565 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B2929823 : Blo 864565 2929823 := bstep (se 1 (by rfl) ⟨2197367, by rfl⟩ : syracuseStep 2929823 = 4394735) B4394735
theorem B866783 : Blo 864565 866783 := bstep (se 1 (by rfl) ⟨650087, by rfl⟩ : syracuseStep 866783 = 1300175) B1300175
theorem B2473087 : Blo 864565 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B20038751 : Blo 864565 20038751 := bstep (se 1 (by rfl) ⟨15029063, by rfl⟩ : syracuseStep 20038751 = 30058127) B30058127
theorem B1951919 : Blo 864565 1951919 := bstep (se 1 (by rfl) ⟨1463939, by rfl⟩ : syracuseStep 1951919 = 2927879) B2927879
theorem B1462441 : Blo 864565 1462441 := bstep (se 2 (by rfl) ⟨548415, by rfl⟩ : syracuseStep 1462441 = 1096831) B1096831
theorem B14801615 : Blo 864565 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B9886697 : Blo 864565 9886697 := bstep (se 2 (by rfl) ⟨3707511, by rfl⟩ : syracuseStep 9886697 = 7415023) B7415023
theorem B17751149 : Blo 864565 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B1302047 : Blo 864565 1302047 := bstep (se 1 (by rfl) ⟨976535, by rfl⟩ : syracuseStep 1302047 = 1953071) B1953071
theorem B22472093 : Blo 864565 22472093 := bstep (se 3 (by rfl) ⟨4213517, by rfl⟩ : syracuseStep 22472093 = 8427035) B8427035
theorem B2780327 : Blo 864565 2780327 := bstep (se 1 (by rfl) ⟨2085245, by rfl⟩ : syracuseStep 2780327 = 4170491) B4170491
theorem B9861911 : Blo 864565 9861911 := bstep (se 1 (by rfl) ⟨7396433, by rfl⟩ : syracuseStep 9861911 = 14792867) B14792867
theorem B14057239 : Blo 864565 14057239 := bstep (se 1 (by rfl) ⟨10542929, by rfl⟩ : syracuseStep 14057239 = 21085859) B21085859
theorem B9867743 : Blo 864565 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B6591131 : Blo 864565 6591131 := bstep (se 1 (by rfl) ⟨4943348, by rfl⟩ : syracuseStep 6591131 = 9886697) B9886697
theorem B11834099 : Blo 864565 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B11277305 : Blo 864565 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B14981395 : Blo 864565 14981395 := bstep (se 1 (by rfl) ⟨11236046, by rfl⟩ : syracuseStep 14981395 = 22472093) B22472093
theorem B51388607 : Blo 864565 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B47427419 : Blo 864565 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B868031 : Blo 864565 868031 := bstep (se 1 (by rfl) ⟨651023, by rfl⟩ : syracuseStep 868031 = 1302047) B1302047
theorem B1949921 : Blo 864565 1949921 := bstep (se 2 (by rfl) ⟨731220, by rfl⟩ : syracuseStep 1949921 = 1462441) B1462441
theorem B1853551 : Blo 864565 1853551 := bstep (se 1 (by rfl) ⟨1390163, by rfl⟩ : syracuseStep 1853551 = 2780327) B2780327
theorem B4377401 : Blo 864565 4377401 := bstep (se 2 (by rfl) ⟨1641525, by rfl⟩ : syracuseStep 4377401 = 3283051) B3283051
theorem B1953215 : Blo 864565 1953215 := bstep (se 1 (by rfl) ⟨1464911, by rfl⟩ : syracuseStep 1953215 = 2929823) B2929823
theorem B3297449 : Blo 864565 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B6574607 : Blo 864565 6574607 := bstep (se 1 (by rfl) ⟨4930955, by rfl⟩ : syracuseStep 6574607 = 9861911) B9861911
theorem B25646881 : Blo 864565 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B13359167 : Blo 864565 13359167 := bstep (se 1 (by rfl) ⟨10019375, by rfl⟩ : syracuseStep 13359167 = 20038751) B20038751
theorem B1301279 : Blo 864565 1301279 := bstep (se 1 (by rfl) ⟨975959, by rfl⟩ : syracuseStep 1301279 = 1951919) B1951919
theorem B4383881 : Blo 864565 4383881 := bstep (se 2 (by rfl) ⟨1643955, by rfl⟩ : syracuseStep 4383881 = 3287911) B3287911
theorem B11235839 : Blo 864565 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B18742985 : Blo 864565 18742985 := bstep (se 2 (by rfl) ⟨7028619, by rfl⟩ : syracuseStep 18742985 = 14057239) B14057239
theorem B2918267 : Blo 864565 2918267 := bstep (se 1 (by rfl) ⟨2188700, by rfl⟩ : syracuseStep 2918267 = 4377401) B4377401
theorem B2198299 : Blo 864565 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B4394087 : Blo 864565 4394087 := bstep (se 1 (by rfl) ⟨3295565, by rfl⟩ : syracuseStep 4394087 = 6591131) B6591131
theorem B2922587 : Blo 864565 2922587 := bstep (se 1 (by rfl) ⟨2191940, by rfl⟩ : syracuseStep 2922587 = 4383881) B4383881
theorem B12495323 : Blo 864565 12495323 := bstep (se 1 (by rfl) ⟨9371492, by rfl⟩ : syracuseStep 12495323 = 18742985) B18742985
theorem B29962237 : Blo 864565 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B2471401 : Blo 864565 2471401 := bstep (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) B1853551
theorem B7518203 : Blo 864565 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B867519 : Blo 864565 867519 := bstep (se 1 (by rfl) ⟨650639, by rfl⟩ : syracuseStep 867519 = 1301279) B1301279
theorem B34259071 : Blo 864565 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B34195841 : Blo 864565 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B19975193 : Blo 864565 19975193 := bstep (se 2 (by rfl) ⟨7490697, by rfl⟩ : syracuseStep 19975193 = 14981395) B14981395
theorem B1299947 : Blo 864565 1299947 := bstep (se 1 (by rfl) ⟨974960, by rfl⟩ : syracuseStep 1299947 = 1949921) B1949921
theorem B1302143 : Blo 864565 1302143 := bstep (se 1 (by rfl) ⟨976607, by rfl⟩ : syracuseStep 1302143 = 1953215) B1953215
theorem B6578495 : Blo 864565 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B4383071 : Blo 864565 4383071 := bstep (se 1 (by rfl) ⟨3287303, by rfl⟩ : syracuseStep 4383071 = 6574607) B6574607
theorem B7889399 : Blo 864565 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B8906111 : Blo 864565 8906111 := bstep (se 1 (by rfl) ⟨6679583, by rfl⟩ : syracuseStep 8906111 = 13359167) B13359167
theorem B31618279 : Blo 864565 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B45678761 : Blo 864565 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B39949649 : Blo 864565 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B2922047 : Blo 864565 2922047 := bstep (se 1 (by rfl) ⟨2191535, by rfl⟩ : syracuseStep 2922047 = 4383071) B4383071
theorem B5937407 : Blo 864565 5937407 := bstep (se 1 (by rfl) ⟨4453055, by rfl⟩ : syracuseStep 5937407 = 8906111) B8906111
theorem B8330215 : Blo 864565 8330215 := bstep (se 1 (by rfl) ⟨6247661, by rfl⟩ : syracuseStep 8330215 = 12495323) B12495323
theorem B1945511 : Blo 864565 1945511 := bstep (se 1 (by rfl) ⟨1459133, by rfl⟩ : syracuseStep 1945511 = 2918267) B2918267
theorem B13316795 : Blo 864565 13316795 := bstep (se 1 (by rfl) ⟨9987596, by rfl⟩ : syracuseStep 13316795 = 19975193) B19975193
theorem B2929391 : Blo 864565 2929391 := bstep (se 1 (by rfl) ⟨2197043, by rfl⟩ : syracuseStep 2929391 = 4394087) B4394087
theorem B866631 : Blo 864565 866631 := bstep (se 1 (by rfl) ⟨649973, by rfl⟩ : syracuseStep 866631 = 1299947) B1299947
theorem B2931065 : Blo 864565 2931065 := bstep (se 2 (by rfl) ⟨1099149, by rfl⟩ : syracuseStep 2931065 = 2198299) B2198299
theorem B1948391 : Blo 864565 1948391 := bstep (se 1 (by rfl) ⟨1461293, by rfl⟩ : syracuseStep 1948391 = 2922587) B2922587
theorem B868095 : Blo 864565 868095 := bstep (se 1 (by rfl) ⟨651071, by rfl⟩ : syracuseStep 868095 = 1302143) B1302143
theorem B5259599 : Blo 864565 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B42157705 : Blo 864565 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B3295201 : Blo 864565 3295201 := bstep (se 2 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 3295201 = 2471401) B2471401
theorem B22797227 : Blo 864565 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B4385663 : Blo 864565 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B5012135 : Blo 864565 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B3506399 : Blo 864565 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B4393601 : Blo 864565 4393601 := bstep (se 2 (by rfl) ⟨1647600, by rfl⟩ : syracuseStep 4393601 = 3295201) B3295201
theorem B2923775 : Blo 864565 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B30452507 : Blo 864565 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B56210273 : Blo 864565 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B1948031 : Blo 864565 1948031 := bstep (se 1 (by rfl) ⟨1461023, by rfl⟩ : syracuseStep 1948031 = 2922047) B2922047
theorem B1297007 : Blo 864565 1297007 := bstep (se 1 (by rfl) ⟨972755, by rfl⟩ : syracuseStep 1297007 = 1945511) B1945511
theorem B1952927 : Blo 864565 1952927 := bstep (se 1 (by rfl) ⟨1464695, by rfl⟩ : syracuseStep 1952927 = 2929391) B2929391
theorem B1954043 : Blo 864565 1954043 := bstep (se 1 (by rfl) ⟨1465532, by rfl⟩ : syracuseStep 1954043 = 2931065) B2931065
theorem B1298927 : Blo 864565 1298927 := bstep (se 1 (by rfl) ⟨974195, by rfl⟩ : syracuseStep 1298927 = 1948391) B1948391
theorem B26633099 : Blo 864565 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B3958271 : Blo 864565 3958271 := bstep (se 1 (by rfl) ⟨2968703, by rfl⟩ : syracuseStep 3958271 = 5937407) B5937407
theorem B15198151 : Blo 864565 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B8877863 : Blo 864565 8877863 := bstep (se 1 (by rfl) ⟨6658397, by rfl⟩ : syracuseStep 8877863 = 13316795) B13316795
theorem B11106953 : Blo 864565 11106953 := bstep (se 2 (by rfl) ⟨4165107, by rfl⟩ : syracuseStep 11106953 = 8330215) B8330215
theorem B3341423 : Blo 864565 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B2337599 : Blo 864565 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B864671 : Blo 864565 864671 := bstep (se 1 (by rfl) ⟨648503, by rfl⟩ : syracuseStep 864671 = 1297007) B1297007
theorem B2929067 : Blo 864565 2929067 := bstep (se 1 (by rfl) ⟨2196800, by rfl⟩ : syracuseStep 2929067 = 4393601) B4393601
theorem B20264201 : Blo 864565 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B865951 : Blo 864565 865951 := bstep (se 1 (by rfl) ⟨649463, by rfl⟩ : syracuseStep 865951 = 1298927) B1298927
theorem B1949183 : Blo 864565 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B2638847 : Blo 864565 2638847 := bstep (se 1 (by rfl) ⟨1979135, by rfl⟩ : syracuseStep 2638847 = 3958271) B3958271
theorem B20301671 : Blo 864565 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B37473515 : Blo 864565 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B5918575 : Blo 864565 5918575 := bstep (se 1 (by rfl) ⟨4438931, by rfl⟩ : syracuseStep 5918575 = 8877863) B8877863
theorem B1298687 : Blo 864565 1298687 := bstep (se 1 (by rfl) ⟨974015, by rfl⟩ : syracuseStep 1298687 = 1948031) B1948031
theorem B1301951 : Blo 864565 1301951 := bstep (se 1 (by rfl) ⟨976463, by rfl⟩ : syracuseStep 1301951 = 1952927) B1952927
theorem B1302695 : Blo 864565 1302695 := bstep (se 1 (by rfl) ⟨977021, by rfl⟩ : syracuseStep 1302695 = 1954043) B1954043
theorem B17755399 : Blo 864565 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B8910461 : Blo 864565 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B7404635 : Blo 864565 7404635 := bstep (se 1 (by rfl) ⟨5553476, by rfl⟩ : syracuseStep 7404635 = 11106953) B11106953
theorem B13534447 : Blo 864565 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B13509467 : Blo 864565 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B5940307 : Blo 864565 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B24982343 : Blo 864565 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B865791 : Blo 864565 865791 := bstep (se 1 (by rfl) ⟨649343, by rfl⟩ : syracuseStep 865791 = 1298687) B1298687
theorem B23673865 : Blo 864565 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B867967 : Blo 864565 867967 := bstep (se 1 (by rfl) ⟨650975, by rfl⟩ : syracuseStep 867967 = 1301951) B1301951
theorem B868463 : Blo 864565 868463 := bstep (se 1 (by rfl) ⟨651347, by rfl⟩ : syracuseStep 868463 = 1302695) B1302695
theorem B1558399 : Blo 864565 1558399 := bstep (se 1 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 1558399 = 2337599) B2337599
theorem B1952711 : Blo 864565 1952711 := bstep (se 1 (by rfl) ⟨1464533, by rfl⟩ : syracuseStep 1952711 = 2929067) B2929067
theorem B4936423 : Blo 864565 4936423 := bstep (se 1 (by rfl) ⟨3702317, by rfl⟩ : syracuseStep 4936423 = 7404635) B7404635
theorem B1299455 : Blo 864565 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B1759231 : Blo 864565 1759231 := bstep (se 1 (by rfl) ⟨1319423, by rfl⟩ : syracuseStep 1759231 = 2638847) B2638847
theorem B7891433 : Blo 864565 7891433 := bstep (se 2 (by rfl) ⟨2959287, by rfl⟩ : syracuseStep 7891433 = 5918575) B5918575
theorem B16654895 : Blo 864565 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B31565153 : Blo 864565 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B2077865 : Blo 864565 2077865 := bstep (se 2 (by rfl) ⟨779199, by rfl⟩ : syracuseStep 2077865 = 1558399) B1558399
theorem B866303 : Blo 864565 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B5260955 : Blo 864565 5260955 := bstep (se 1 (by rfl) ⟨3945716, by rfl⟩ : syracuseStep 5260955 = 7891433) B7891433
theorem B2345641 : Blo 864565 2345641 := bstep (se 2 (by rfl) ⟨879615, by rfl⟩ : syracuseStep 2345641 = 1759231) B1759231
theorem B7920409 : Blo 864565 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B18045929 : Blo 864565 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B1301807 : Blo 864565 1301807 := bstep (se 1 (by rfl) ⟨976355, by rfl⟩ : syracuseStep 1301807 = 1952711) B1952711
theorem B9006311 : Blo 864565 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B6581897 : Blo 864565 6581897 := bstep (se 2 (by rfl) ⟨2468211, by rfl⟩ : syracuseStep 6581897 = 4936423) B4936423
theorem B14029213 : Blo 864565 14029213 := bstep (se 3 (by rfl) ⟨2630477, by rfl⟩ : syracuseStep 14029213 = 5260955) B5260955
theorem B12030619 : Blo 864565 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B21043435 : Blo 864565 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B6004207 : Blo 864565 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B1385243 : Blo 864565 1385243 := bstep (se 1 (by rfl) ⟨1038932, by rfl⟩ : syracuseStep 1385243 = 2077865) B2077865
theorem B10560545 : Blo 864565 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B867871 : Blo 864565 867871 := bstep (se 1 (by rfl) ⟨650903, by rfl⟩ : syracuseStep 867871 = 1301807) B1301807
theorem B12510085 : Blo 864565 12510085 := bstep (se 4 (by rfl) ⟨1172820, by rfl⟩ : syracuseStep 12510085 = 2345641) B2345641
theorem B11103263 : Blo 864565 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B4387931 : Blo 864565 4387931 := bstep (se 1 (by rfl) ⟨3290948, by rfl⟩ : syracuseStep 4387931 = 6581897) B6581897
theorem B16680113 : Blo 864565 16680113 := bstep (se 2 (by rfl) ⟨6255042, by rfl⟩ : syracuseStep 16680113 = 12510085) B12510085
theorem B923495 : Blo 864565 923495 := bstep (se 1 (by rfl) ⟨692621, by rfl⟩ : syracuseStep 923495 = 1385243) B1385243
theorem B28057913 : Blo 864565 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B2925287 : Blo 864565 2925287 := bstep (se 1 (by rfl) ⟨2193965, by rfl⟩ : syracuseStep 2925287 = 4387931) B4387931
theorem B8005609 : Blo 864565 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B16040825 : Blo 864565 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B18705617 : Blo 864565 18705617 := bstep (se 2 (by rfl) ⟨7014606, by rfl⟩ : syracuseStep 18705617 = 14029213) B14029213
theorem B7040363 : Blo 864565 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B7402175 : Blo 864565 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B2462653 : Blo 864565 2462653 := bstep (se 3 (by rfl) ⟨461747, by rfl⟩ : syracuseStep 2462653 = 923495) B923495
theorem B10693883 : Blo 864565 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B11120075 : Blo 864565 11120075 := bstep (se 1 (by rfl) ⟨8340056, by rfl⟩ : syracuseStep 11120075 = 16680113) B16680113
theorem B1950191 : Blo 864565 1950191 := bstep (se 1 (by rfl) ⟨1462643, by rfl⟩ : syracuseStep 1950191 = 2925287) B2925287
theorem B12470411 : Blo 864565 12470411 := bstep (se 1 (by rfl) ⟨9352808, by rfl⟩ : syracuseStep 12470411 = 18705617) B18705617
theorem B4934783 : Blo 864565 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B10674145 : Blo 864565 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B18705275 : Blo 864565 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B18774301 : Blo 864565 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B3283537 : Blo 864565 3283537 := bstep (se 2 (by rfl) ⟨1231326, by rfl⟩ : syracuseStep 3283537 = 2462653) B2462653
theorem B7413383 : Blo 864565 7413383 := bstep (se 1 (by rfl) ⟨5560037, by rfl⟩ : syracuseStep 7413383 = 11120075) B11120075
theorem B14232193 : Blo 864565 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B3289855 : Blo 864565 3289855 := bstep (se 1 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 3289855 = 4934783) B4934783
theorem B12470183 : Blo 864565 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B7129255 : Blo 864565 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B1300127 : Blo 864565 1300127 := bstep (se 1 (by rfl) ⟨975095, by rfl⟩ : syracuseStep 1300127 = 1950191) B1950191
theorem B8313607 : Blo 864565 8313607 := bstep (se 1 (by rfl) ⟨6235205, by rfl⟩ : syracuseStep 8313607 = 12470411) B12470411
theorem B25032401 : Blo 864565 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B9505673 : Blo 864565 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B11084809 : Blo 864565 11084809 := bstep (se 2 (by rfl) ⟨4156803, by rfl⟩ : syracuseStep 11084809 = 8313607) B8313607
theorem B16688267 : Blo 864565 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B75905029 : Blo 864565 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B866751 : Blo 864565 866751 := bstep (se 1 (by rfl) ⟨650063, by rfl⟩ : syracuseStep 866751 = 1300127) B1300127
theorem B4378049 : Blo 864565 4378049 := bstep (se 2 (by rfl) ⟨1641768, by rfl⟩ : syracuseStep 4378049 = 3283537) B3283537
theorem B8313455 : Blo 864565 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B4942255 : Blo 864565 4942255 := bstep (se 1 (by rfl) ⟨3706691, by rfl⟩ : syracuseStep 4942255 = 7413383) B7413383
theorem B4386473 : Blo 864565 4386473 := bstep (se 2 (by rfl) ⟨1644927, by rfl⟩ : syracuseStep 4386473 = 3289855) B3289855
theorem B14779745 : Blo 864565 14779745 := bstep (se 2 (by rfl) ⟨5542404, by rfl⟩ : syracuseStep 14779745 = 11084809) B11084809
theorem B2918699 : Blo 864565 2918699 := bstep (se 1 (by rfl) ⟨2189024, by rfl⟩ : syracuseStep 2918699 = 4378049) B4378049
theorem B6589673 : Blo 864565 6589673 := bstep (se 2 (by rfl) ⟨2471127, by rfl⟩ : syracuseStep 6589673 = 4942255) B4942255
theorem B5542303 : Blo 864565 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B2924315 : Blo 864565 2924315 := bstep (se 1 (by rfl) ⟨2193236, by rfl⟩ : syracuseStep 2924315 = 4386473) B4386473
theorem B6337115 : Blo 864565 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B11125511 : Blo 864565 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B101206705 : Blo 864565 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B4393115 : Blo 864565 4393115 := bstep (se 1 (by rfl) ⟨3294836, by rfl⟩ : syracuseStep 4393115 = 6589673) B6589673
theorem B134942273 : Blo 864565 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B7417007 : Blo 864565 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B1945799 : Blo 864565 1945799 := bstep (se 1 (by rfl) ⟨1459349, by rfl⟩ : syracuseStep 1945799 = 2918699) B2918699
theorem B1949543 : Blo 864565 1949543 := bstep (se 1 (by rfl) ⟨1462157, by rfl⟩ : syracuseStep 1949543 = 2924315) B2924315
theorem B7389737 : Blo 864565 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B9853163 : Blo 864565 9853163 := bstep (se 1 (by rfl) ⟨7389872, by rfl⟩ : syracuseStep 9853163 = 14779745) B14779745
theorem B4224743 : Blo 864565 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B4926491 : Blo 864565 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B2928743 : Blo 864565 2928743 := bstep (se 1 (by rfl) ⟨2196557, by rfl⟩ : syracuseStep 2928743 = 4393115) B4393115
theorem B89961515 : Blo 864565 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B6568775 : Blo 864565 6568775 := bstep (se 1 (by rfl) ⟨4926581, by rfl⟩ : syracuseStep 6568775 = 9853163) B9853163
theorem B1297199 : Blo 864565 1297199 := bstep (se 1 (by rfl) ⟨972899, by rfl⟩ : syracuseStep 1297199 = 1945799) B1945799
theorem B1299695 : Blo 864565 1299695 := bstep (se 1 (by rfl) ⟨974771, by rfl⟩ : syracuseStep 1299695 = 1949543) B1949543
theorem B4944671 : Blo 864565 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B2816495 : Blo 864565 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B3284327 : Blo 864565 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B59974343 : Blo 864565 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B1877663 : Blo 864565 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B864799 : Blo 864565 864799 := bstep (se 1 (by rfl) ⟨648599, by rfl⟩ : syracuseStep 864799 = 1297199) B1297199
theorem B866463 : Blo 864565 866463 := bstep (se 1 (by rfl) ⟨649847, by rfl⟩ : syracuseStep 866463 = 1299695) B1299695
theorem B1952495 : Blo 864565 1952495 := bstep (se 1 (by rfl) ⟨1464371, by rfl⟩ : syracuseStep 1952495 = 2928743) B2928743
theorem B3296447 : Blo 864565 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B4379183 : Blo 864565 4379183 := bstep (se 1 (by rfl) ⟨3284387, by rfl⟩ : syracuseStep 4379183 = 6568775) B6568775
theorem B2197631 : Blo 864565 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B2919455 : Blo 864565 2919455 := bstep (se 1 (by rfl) ⟨2189591, by rfl⟩ : syracuseStep 2919455 = 4379183) B4379183
theorem B39982895 : Blo 864565 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B1251775 : Blo 864565 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B1301663 : Blo 864565 1301663 := bstep (se 1 (by rfl) ⟨976247, by rfl⟩ : syracuseStep 1301663 = 1952495) B1952495
theorem B2189551 : Blo 864565 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B2919401 : Blo 864565 2919401 := bstep (se 2 (by rfl) ⟨1094775, by rfl⟩ : syracuseStep 2919401 = 2189551) B2189551
theorem B1946303 : Blo 864565 1946303 := bstep (se 1 (by rfl) ⟨1459727, by rfl⟩ : syracuseStep 1946303 = 2919455) B2919455
theorem B26655263 : Blo 864565 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B867775 : Blo 864565 867775 := bstep (se 1 (by rfl) ⟨650831, by rfl⟩ : syracuseStep 867775 = 1301663) B1301663
theorem B1465087 : Blo 864565 1465087 := bstep (se 1 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 1465087 = 2197631) B2197631
theorem B1669033 : Blo 864565 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B17770175 : Blo 864565 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B1946267 : Blo 864565 1946267 := bstep (se 1 (by rfl) ⟨1459700, by rfl⟩ : syracuseStep 1946267 = 2919401) B2919401
theorem B1297535 : Blo 864565 1297535 := bstep (se 1 (by rfl) ⟨973151, by rfl⟩ : syracuseStep 1297535 = 1946303) B1946303
theorem B1953449 : Blo 864565 1953449 := bstep (se 2 (by rfl) ⟨732543, by rfl⟩ : syracuseStep 1953449 = 1465087) B1465087
theorem B2225377 : Blo 864565 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B11868677 : Blo 864565 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B865023 : Blo 864565 865023 := bstep (se 1 (by rfl) ⟨648767, by rfl⟩ : syracuseStep 865023 = 1297535) B1297535
theorem B11846783 : Blo 864565 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B1297511 : Blo 864565 1297511 := bstep (se 1 (by rfl) ⟨973133, by rfl⟩ : syracuseStep 1297511 = 1946267) B1946267
theorem B1302299 : Blo 864565 1302299 := bstep (se 1 (by rfl) ⟨976724, by rfl⟩ : syracuseStep 1302299 = 1953449) B1953449
theorem B31591421 : Blo 864565 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B865007 : Blo 864565 865007 := bstep (se 1 (by rfl) ⟨648755, by rfl⟩ : syracuseStep 865007 = 1297511) B1297511
theorem B7912451 : Blo 864565 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B868199 : Blo 864565 868199 := bstep (se 1 (by rfl) ⟨651149, by rfl⟩ : syracuseStep 868199 = 1302299) B1302299
theorem B21060947 : Blo 864565 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B21099869 : Blo 864565 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 864565 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B14040631 : Blo 864565 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B18720841 : Blo 864565 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B37510877 : Blo 864565 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B25007251 : Blo 864565 25007251 := bstep (se 1 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 25007251 = 37510877) B37510877
theorem B24961121 : Blo 864565 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B33343001 : Blo 864565 33343001 := bstep (se 2 (by rfl) ⟨12503625, by rfl⟩ : syracuseStep 33343001 = 25007251) B25007251
theorem B16640747 : Blo 864565 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B22228667 : Blo 864565 22228667 := bstep (se 1 (by rfl) ⟨16671500, by rfl⟩ : syracuseStep 22228667 = 33343001) B33343001
theorem B11093831 : Blo 864565 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B14819111 : Blo 864565 14819111 := bstep (se 1 (by rfl) ⟨11114333, by rfl⟩ : syracuseStep 14819111 = 22228667) B22228667
theorem B7395887 : Blo 864565 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B4930591 : Blo 864565 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B9879407 : Blo 864565 9879407 := bstep (se 1 (by rfl) ⟨7409555, by rfl⟩ : syracuseStep 9879407 = 14819111) B14819111
theorem B6574121 : Blo 864565 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B6586271 : Blo 864565 6586271 := bstep (se 1 (by rfl) ⟨4939703, by rfl⟩ : syracuseStep 6586271 = 9879407) B9879407
theorem B4382747 : Blo 864565 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B4390847 : Blo 864565 4390847 := bstep (se 1 (by rfl) ⟨3293135, by rfl⟩ : syracuseStep 4390847 = 6586271) B6586271
theorem B2921831 : Blo 864565 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B2927231 : Blo 864565 2927231 := bstep (se 1 (by rfl) ⟨2195423, by rfl⟩ : syracuseStep 2927231 = 4390847) B4390847
theorem B1947887 : Blo 864565 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B1951487 : Blo 864565 1951487 := bstep (se 1 (by rfl) ⟨1463615, by rfl⟩ : syracuseStep 1951487 = 2927231) B2927231
theorem B1298591 : Blo 864565 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B1300991 : Blo 864565 1300991 := bstep (se 1 (by rfl) ⟨975743, by rfl⟩ : syracuseStep 1300991 = 1951487) B1951487
theorem B865727 : Blo 864565 865727 := bstep (se 1 (by rfl) ⟨649295, by rfl⟩ : syracuseStep 865727 = 1298591) B1298591
theorem B867327 : Blo 864565 867327 := bstep (se 1 (by rfl) ⟨650495, by rfl⟩ : syracuseStep 867327 = 1300991) B1300991

theorem C0 (j : ℕ) (h1 : 216141 ≤ j) (h2 : j ≤ 216840) : Blo 864565 (4 * j + 3) := by
  interval_cases j
  · exact B864567
  · exact B864571
  · exact B864575
  · exact B864579
  · exact B864583
  · exact B864587
  · exact B864591
  · exact B864595
  · exact B864599
  · exact B864603
  · exact B864607
  · exact B864611
  · exact B864615
  · exact B864619
  · exact B864623
  · exact B864627
  · exact B864631
  · exact B864635
  · exact B864639
  · exact B864643
  · exact B864647
  · exact B864651
  · exact B864655
  · exact B864659
  · exact B864663
  · exact B864667
  · exact B864671
  · exact B864675
  · exact B864679
  · exact B864683
  · exact B864687
  · exact B864691
  · exact B864695
  · exact B864699
  · exact B864703
  · exact B864707
  · exact B864711
  · exact B864715
  · exact B864719
  · exact B864723
  · exact B864727
  · exact B864731
  · exact B864735
  · exact B864739
  · exact B864743
  · exact B864747
  · exact B864751
  · exact B864755
  · exact B864759
  · exact B864763
  · exact B864767
  · exact B864771
  · exact B864775
  · exact B864779
  · exact B864783
  · exact B864787
  · exact B864791
  · exact B864795
  · exact B864799
  · exact B864803
  · exact B864807
  · exact B864811
  · exact B864815
  · exact B864819
  · exact B864823
  · exact B864827
  · exact B864831
  · exact B864835
  · exact B864839
  · exact B864843
  · exact B864847
  · exact B864851
  · exact B864855
  · exact B864859
  · exact B864863
  · exact B864867
  · exact B864871
  · exact B864875
  · exact B864879
  · exact B864883
  · exact B864887
  · exact B864891
  · exact B864895
  · exact B864899
  · exact B864903
  · exact B864907
  · exact B864911
  · exact B864915
  · exact B864919
  · exact B864923
  · exact B864927
  · exact B864931
  · exact B864935
  · exact B864939
  · exact B864943
  · exact B864947
  · exact B864951
  · exact B864955
  · exact B864959
  · exact B864963
  · exact B864967
  · exact B864971
  · exact B864975
  · exact B864979
  · exact B864983
  · exact B864987
  · exact B864991
  · exact B864995
  · exact B864999
  · exact B865003
  · exact B865007
  · exact B865011
  · exact B865015
  · exact B865019
  · exact B865023
  · exact B865027
  · exact B865031
  · exact B865035
  · exact B865039
  · exact B865043
  · exact B865047
  · exact B865051
  · exact B865055
  · exact B865059
  · exact B865063
  · exact B865067
  · exact B865071
  · exact B865075
  · exact B865079
  · exact B865083
  · exact B865087
  · exact B865091
  · exact B865095
  · exact B865099
  · exact B865103
  · exact B865107
  · exact B865111
  · exact B865115
  · exact B865119
  · exact B865123
  · exact B865127
  · exact B865131
  · exact B865135
  · exact B865139
  · exact B865143
  · exact B865147
  · exact B865151
  · exact B865155
  · exact B865159
  · exact B865163
  · exact B865167
  · exact B865171
  · exact B865175
  · exact B865179
  · exact B865183
  · exact B865187
  · exact B865191
  · exact B865195
  · exact B865199
  · exact B865203
  · exact B865207
  · exact B865211
  · exact B865215
  · exact B865219
  · exact B865223
  · exact B865227
  · exact B865231
  · exact B865235
  · exact B865239
  · exact B865243
  · exact B865247
  · exact B865251
  · exact B865255
  · exact B865259
  · exact B865263
  · exact B865267
  · exact B865271
  · exact B865275
  · exact B865279
  · exact B865283
  · exact B865287
  · exact B865291
  · exact B865295
  · exact B865299
  · exact B865303
  · exact B865307
  · exact B865311
  · exact B865315
  · exact B865319
  · exact B865323
  · exact B865327
  · exact B865331
  · exact B865335
  · exact B865339
  · exact B865343
  · exact B865347
  · exact B865351
  · exact B865355
  · exact B865359
  · exact B865363
  · exact B865367
  · exact B865371
  · exact B865375
  · exact B865379
  · exact B865383
  · exact B865387
  · exact B865391
  · exact B865395
  · exact B865399
  · exact B865403
  · exact B865407
  · exact B865411
  · exact B865415
  · exact B865419
  · exact B865423
  · exact B865427
  · exact B865431
  · exact B865435
  · exact B865439
  · exact B865443
  · exact B865447
  · exact B865451
  · exact B865455
  · exact B865459
  · exact B865463
  · exact B865467
  · exact B865471
  · exact B865475
  · exact B865479
  · exact B865483
  · exact B865487
  · exact B865491
  · exact B865495
  · exact B865499
  · exact B865503
  · exact B865507
  · exact B865511
  · exact B865515
  · exact B865519
  · exact B865523
  · exact B865527
  · exact B865531
  · exact B865535
  · exact B865539
  · exact B865543
  · exact B865547
  · exact B865551
  · exact B865555
  · exact B865559
  · exact B865563
  · exact B865567
  · exact B865571
  · exact B865575
  · exact B865579
  · exact B865583
  · exact B865587
  · exact B865591
  · exact B865595
  · exact B865599
  · exact B865603
  · exact B865607
  · exact B865611
  · exact B865615
  · exact B865619
  · exact B865623
  · exact B865627
  · exact B865631
  · exact B865635
  · exact B865639
  · exact B865643
  · exact B865647
  · exact B865651
  · exact B865655
  · exact B865659
  · exact B865663
  · exact B865667
  · exact B865671
  · exact B865675
  · exact B865679
  · exact B865683
  · exact B865687
  · exact B865691
  · exact B865695
  · exact B865699
  · exact B865703
  · exact B865707
  · exact B865711
  · exact B865715
  · exact B865719
  · exact B865723
  · exact B865727
  · exact B865731
  · exact B865735
  · exact B865739
  · exact B865743
  · exact B865747
  · exact B865751
  · exact B865755
  · exact B865759
  · exact B865763
  · exact B865767
  · exact B865771
  · exact B865775
  · exact B865779
  · exact B865783
  · exact B865787
  · exact B865791
  · exact B865795
  · exact B865799
  · exact B865803
  · exact B865807
  · exact B865811
  · exact B865815
  · exact B865819
  · exact B865823
  · exact B865827
  · exact B865831
  · exact B865835
  · exact B865839
  · exact B865843
  · exact B865847
  · exact B865851
  · exact B865855
  · exact B865859
  · exact B865863
  · exact B865867
  · exact B865871
  · exact B865875
  · exact B865879
  · exact B865883
  · exact B865887
  · exact B865891
  · exact B865895
  · exact B865899
  · exact B865903
  · exact B865907
  · exact B865911
  · exact B865915
  · exact B865919
  · exact B865923
  · exact B865927
  · exact B865931
  · exact B865935
  · exact B865939
  · exact B865943
  · exact B865947
  · exact B865951
  · exact B865955
  · exact B865959
  · exact B865963
  · exact B865967
  · exact B865971
  · exact B865975
  · exact B865979
  · exact B865983
  · exact B865987
  · exact B865991
  · exact B865995
  · exact B865999
  · exact B866003
  · exact B866007
  · exact B866011
  · exact B866015
  · exact B866019
  · exact B866023
  · exact B866027
  · exact B866031
  · exact B866035
  · exact B866039
  · exact B866043
  · exact B866047
  · exact B866051
  · exact B866055
  · exact B866059
  · exact B866063
  · exact B866067
  · exact B866071
  · exact B866075
  · exact B866079
  · exact B866083
  · exact B866087
  · exact B866091
  · exact B866095
  · exact B866099
  · exact B866103
  · exact B866107
  · exact B866111
  · exact B866115
  · exact B866119
  · exact B866123
  · exact B866127
  · exact B866131
  · exact B866135
  · exact B866139
  · exact B866143
  · exact B866147
  · exact B866151
  · exact B866155
  · exact B866159
  · exact B866163
  · exact B866167
  · exact B866171
  · exact B866175
  · exact B866179
  · exact B866183
  · exact B866187
  · exact B866191
  · exact B866195
  · exact B866199
  · exact B866203
  · exact B866207
  · exact B866211
  · exact B866215
  · exact B866219
  · exact B866223
  · exact B866227
  · exact B866231
  · exact B866235
  · exact B866239
  · exact B866243
  · exact B866247
  · exact B866251
  · exact B866255
  · exact B866259
  · exact B866263
  · exact B866267
  · exact B866271
  · exact B866275
  · exact B866279
  · exact B866283
  · exact B866287
  · exact B866291
  · exact B866295
  · exact B866299
  · exact B866303
  · exact B866307
  · exact B866311
  · exact B866315
  · exact B866319
  · exact B866323
  · exact B866327
  · exact B866331
  · exact B866335
  · exact B866339
  · exact B866343
  · exact B866347
  · exact B866351
  · exact B866355
  · exact B866359
  · exact B866363
  · exact B866367
  · exact B866371
  · exact B866375
  · exact B866379
  · exact B866383
  · exact B866387
  · exact B866391
  · exact B866395
  · exact B866399
  · exact B866403
  · exact B866407
  · exact B866411
  · exact B866415
  · exact B866419
  · exact B866423
  · exact B866427
  · exact B866431
  · exact B866435
  · exact B866439
  · exact B866443
  · exact B866447
  · exact B866451
  · exact B866455
  · exact B866459
  · exact B866463
  · exact B866467
  · exact B866471
  · exact B866475
  · exact B866479
  · exact B866483
  · exact B866487
  · exact B866491
  · exact B866495
  · exact B866499
  · exact B866503
  · exact B866507
  · exact B866511
  · exact B866515
  · exact B866519
  · exact B866523
  · exact B866527
  · exact B866531
  · exact B866535
  · exact B866539
  · exact B866543
  · exact B866547
  · exact B866551
  · exact B866555
  · exact B866559
  · exact B866563
  · exact B866567
  · exact B866571
  · exact B866575
  · exact B866579
  · exact B866583
  · exact B866587
  · exact B866591
  · exact B866595
  · exact B866599
  · exact B866603
  · exact B866607
  · exact B866611
  · exact B866615
  · exact B866619
  · exact B866623
  · exact B866627
  · exact B866631
  · exact B866635
  · exact B866639
  · exact B866643
  · exact B866647
  · exact B866651
  · exact B866655
  · exact B866659
  · exact B866663
  · exact B866667
  · exact B866671
  · exact B866675
  · exact B866679
  · exact B866683
  · exact B866687
  · exact B866691
  · exact B866695
  · exact B866699
  · exact B866703
  · exact B866707
  · exact B866711
  · exact B866715
  · exact B866719
  · exact B866723
  · exact B866727
  · exact B866731
  · exact B866735
  · exact B866739
  · exact B866743
  · exact B866747
  · exact B866751
  · exact B866755
  · exact B866759
  · exact B866763
  · exact B866767
  · exact B866771
  · exact B866775
  · exact B866779
  · exact B866783
  · exact B866787
  · exact B866791
  · exact B866795
  · exact B866799
  · exact B866803
  · exact B866807
  · exact B866811
  · exact B866815
  · exact B866819
  · exact B866823
  · exact B866827
  · exact B866831
  · exact B866835
  · exact B866839
  · exact B866843
  · exact B866847
  · exact B866851
  · exact B866855
  · exact B866859
  · exact B866863
  · exact B866867
  · exact B866871
  · exact B866875
  · exact B866879
  · exact B866883
  · exact B866887
  · exact B866891
  · exact B866895
  · exact B866899
  · exact B866903
  · exact B866907
  · exact B866911
  · exact B866915
  · exact B866919
  · exact B866923
  · exact B866927
  · exact B866931
  · exact B866935
  · exact B866939
  · exact B866943
  · exact B866947
  · exact B866951
  · exact B866955
  · exact B866959
  · exact B866963
  · exact B866967
  · exact B866971
  · exact B866975
  · exact B866979
  · exact B866983
  · exact B866987
  · exact B866991
  · exact B866995
  · exact B866999
  · exact B867003
  · exact B867007
  · exact B867011
  · exact B867015
  · exact B867019
  · exact B867023
  · exact B867027
  · exact B867031
  · exact B867035
  · exact B867039
  · exact B867043
  · exact B867047
  · exact B867051
  · exact B867055
  · exact B867059
  · exact B867063
  · exact B867067
  · exact B867071
  · exact B867075
  · exact B867079
  · exact B867083
  · exact B867087
  · exact B867091
  · exact B867095
  · exact B867099
  · exact B867103
  · exact B867107
  · exact B867111
  · exact B867115
  · exact B867119
  · exact B867123
  · exact B867127
  · exact B867131
  · exact B867135
  · exact B867139
  · exact B867143
  · exact B867147
  · exact B867151
  · exact B867155
  · exact B867159
  · exact B867163
  · exact B867167
  · exact B867171
  · exact B867175
  · exact B867179
  · exact B867183
  · exact B867187
  · exact B867191
  · exact B867195
  · exact B867199
  · exact B867203
  · exact B867207
  · exact B867211
  · exact B867215
  · exact B867219
  · exact B867223
  · exact B867227
  · exact B867231
  · exact B867235
  · exact B867239
  · exact B867243
  · exact B867247
  · exact B867251
  · exact B867255
  · exact B867259
  · exact B867263
  · exact B867267
  · exact B867271
  · exact B867275
  · exact B867279
  · exact B867283
  · exact B867287
  · exact B867291
  · exact B867295
  · exact B867299
  · exact B867303
  · exact B867307
  · exact B867311
  · exact B867315
  · exact B867319
  · exact B867323
  · exact B867327
  · exact B867331
  · exact B867335
  · exact B867339
  · exact B867343
  · exact B867347
  · exact B867351
  · exact B867355
  · exact B867359
  · exact B867363

theorem C1 (j : ℕ) (h1 : 216841 ≤ j) (h2 : j ≤ 217140) : Blo 864565 (4 * j + 3) := by
  interval_cases j
  · exact B867367
  · exact B867371
  · exact B867375
  · exact B867379
  · exact B867383
  · exact B867387
  · exact B867391
  · exact B867395
  · exact B867399
  · exact B867403
  · exact B867407
  · exact B867411
  · exact B867415
  · exact B867419
  · exact B867423
  · exact B867427
  · exact B867431
  · exact B867435
  · exact B867439
  · exact B867443
  · exact B867447
  · exact B867451
  · exact B867455
  · exact B867459
  · exact B867463
  · exact B867467
  · exact B867471
  · exact B867475
  · exact B867479
  · exact B867483
  · exact B867487
  · exact B867491
  · exact B867495
  · exact B867499
  · exact B867503
  · exact B867507
  · exact B867511
  · exact B867515
  · exact B867519
  · exact B867523
  · exact B867527
  · exact B867531
  · exact B867535
  · exact B867539
  · exact B867543
  · exact B867547
  · exact B867551
  · exact B867555
  · exact B867559
  · exact B867563
  · exact B867567
  · exact B867571
  · exact B867575
  · exact B867579
  · exact B867583
  · exact B867587
  · exact B867591
  · exact B867595
  · exact B867599
  · exact B867603
  · exact B867607
  · exact B867611
  · exact B867615
  · exact B867619
  · exact B867623
  · exact B867627
  · exact B867631
  · exact B867635
  · exact B867639
  · exact B867643
  · exact B867647
  · exact B867651
  · exact B867655
  · exact B867659
  · exact B867663
  · exact B867667
  · exact B867671
  · exact B867675
  · exact B867679
  · exact B867683
  · exact B867687
  · exact B867691
  · exact B867695
  · exact B867699
  · exact B867703
  · exact B867707
  · exact B867711
  · exact B867715
  · exact B867719
  · exact B867723
  · exact B867727
  · exact B867731
  · exact B867735
  · exact B867739
  · exact B867743
  · exact B867747
  · exact B867751
  · exact B867755
  · exact B867759
  · exact B867763
  · exact B867767
  · exact B867771
  · exact B867775
  · exact B867779
  · exact B867783
  · exact B867787
  · exact B867791
  · exact B867795
  · exact B867799
  · exact B867803
  · exact B867807
  · exact B867811
  · exact B867815
  · exact B867819
  · exact B867823
  · exact B867827
  · exact B867831
  · exact B867835
  · exact B867839
  · exact B867843
  · exact B867847
  · exact B867851
  · exact B867855
  · exact B867859
  · exact B867863
  · exact B867867
  · exact B867871
  · exact B867875
  · exact B867879
  · exact B867883
  · exact B867887
  · exact B867891
  · exact B867895
  · exact B867899
  · exact B867903
  · exact B867907
  · exact B867911
  · exact B867915
  · exact B867919
  · exact B867923
  · exact B867927
  · exact B867931
  · exact B867935
  · exact B867939
  · exact B867943
  · exact B867947
  · exact B867951
  · exact B867955
  · exact B867959
  · exact B867963
  · exact B867967
  · exact B867971
  · exact B867975
  · exact B867979
  · exact B867983
  · exact B867987
  · exact B867991
  · exact B867995
  · exact B867999
  · exact B868003
  · exact B868007
  · exact B868011
  · exact B868015
  · exact B868019
  · exact B868023
  · exact B868027
  · exact B868031
  · exact B868035
  · exact B868039
  · exact B868043
  · exact B868047
  · exact B868051
  · exact B868055
  · exact B868059
  · exact B868063
  · exact B868067
  · exact B868071
  · exact B868075
  · exact B868079
  · exact B868083
  · exact B868087
  · exact B868091
  · exact B868095
  · exact B868099
  · exact B868103
  · exact B868107
  · exact B868111
  · exact B868115
  · exact B868119
  · exact B868123
  · exact B868127
  · exact B868131
  · exact B868135
  · exact B868139
  · exact B868143
  · exact B868147
  · exact B868151
  · exact B868155
  · exact B868159
  · exact B868163
  · exact B868167
  · exact B868171
  · exact B868175
  · exact B868179
  · exact B868183
  · exact B868187
  · exact B868191
  · exact B868195
  · exact B868199
  · exact B868203
  · exact B868207
  · exact B868211
  · exact B868215
  · exact B868219
  · exact B868223
  · exact B868227
  · exact B868231
  · exact B868235
  · exact B868239
  · exact B868243
  · exact B868247
  · exact B868251
  · exact B868255
  · exact B868259
  · exact B868263
  · exact B868267
  · exact B868271
  · exact B868275
  · exact B868279
  · exact B868283
  · exact B868287
  · exact B868291
  · exact B868295
  · exact B868299
  · exact B868303
  · exact B868307
  · exact B868311
  · exact B868315
  · exact B868319
  · exact B868323
  · exact B868327
  · exact B868331
  · exact B868335
  · exact B868339
  · exact B868343
  · exact B868347
  · exact B868351
  · exact B868355
  · exact B868359
  · exact B868363
  · exact B868367
  · exact B868371
  · exact B868375
  · exact B868379
  · exact B868383
  · exact B868387
  · exact B868391
  · exact B868395
  · exact B868399
  · exact B868403
  · exact B868407
  · exact B868411
  · exact B868415
  · exact B868419
  · exact B868423
  · exact B868427
  · exact B868431
  · exact B868435
  · exact B868439
  · exact B868443
  · exact B868447
  · exact B868451
  · exact B868455
  · exact B868459
  · exact B868463
  · exact B868467
  · exact B868471
  · exact B868475
  · exact B868479
  · exact B868483
  · exact B868487
  · exact B868491
  · exact B868495
  · exact B868499
  · exact B868503
  · exact B868507
  · exact B868511
  · exact B868515
  · exact B868519
  · exact B868523
  · exact B868527
  · exact B868531
  · exact B868535
  · exact B868539
  · exact B868543
  · exact B868547
  · exact B868551
  · exact B868555
  · exact B868559
  · exact B868563

theorem solution (m : ℕ) (hlo : 864565 ≤ m) (hhi : m ≤ 868565) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 216141 ≤ j := by omega
    have hj2 : j ≤ 217140 := by omega
    have hb : Blo 864565 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 216841 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
