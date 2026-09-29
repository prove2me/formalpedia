-- Prove2me | solution 1 for syracuse_descends_range_1230433_1232433
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:02.793234+00:00
-- url     : https://prove2.me/submissions/d3e83d78-536c-435c-91ca-d6e8d626f704

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


theorem B1384465 : Blo 1230433 1384465 := bbase (se 2 (by rfl) ⟨519174, by rfl⟩ : syracuseStep 1384465 = 1038349) (by norm_num)
theorem B1384501 : Blo 1230433 1384501 := bbase (se 5 (by rfl) ⟨64898, by rfl⟩ : syracuseStep 1384501 = 129797) (by norm_num)
theorem B2768957 : Blo 1230433 2768957 := bbase (se 3 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 2768957 = 1038359) (by norm_num)
theorem B1384537 : Blo 1230433 1384537 := bbase (se 2 (by rfl) ⟨519201, by rfl⟩ : syracuseStep 1384537 = 1038403) (by norm_num)
theorem B1384573 : Blo 1230433 1384573 := bbase (se 3 (by rfl) ⟨259607, by rfl⟩ : syracuseStep 1384573 = 519215) (by norm_num)
theorem B2769029 : Blo 1230433 2769029 := bbase (se 4 (by rfl) ⟨259596, by rfl⟩ : syracuseStep 2769029 = 519193) (by norm_num)
theorem B6234245 : Blo 1230433 6234245 := bbase (se 4 (by rfl) ⟨584460, by rfl⟩ : syracuseStep 6234245 = 1168921) (by norm_num)
theorem B1384609 : Blo 1230433 1384609 := bbase (se 2 (by rfl) ⟨519228, by rfl⟩ : syracuseStep 1384609 = 1038457) (by norm_num)
theorem B1384645 : Blo 1230433 1384645 := bbase (se 4 (by rfl) ⟨129810, by rfl⟩ : syracuseStep 1384645 = 259621) (by norm_num)
theorem B2769101 : Blo 1230433 2769101 := bbase (se 3 (by rfl) ⟨519206, by rfl⟩ : syracuseStep 2769101 = 1038413) (by norm_num)
theorem B2105573 : Blo 1230433 2105573 := bbase (se 4 (by rfl) ⟨197397, by rfl⟩ : syracuseStep 2105573 = 394795) (by norm_num)
theorem B1384681 : Blo 1230433 1384681 := bbase (se 2 (by rfl) ⟨519255, by rfl⟩ : syracuseStep 1384681 = 1038511) (by norm_num)
theorem B2220293 : Blo 1230433 2220293 := bbase (se 4 (by rfl) ⟨208152, by rfl⟩ : syracuseStep 2220293 = 416305) (by norm_num)
theorem B1384717 : Blo 1230433 1384717 := bbase (se 3 (by rfl) ⟨259634, by rfl⟩ : syracuseStep 1384717 = 519269) (by norm_num)
theorem B2769173 : Blo 1230433 2769173 := bbase (se 6 (by rfl) ⟨64902, by rfl⟩ : syracuseStep 2769173 = 129805) (by norm_num)
theorem B1384753 : Blo 1230433 1384753 := bbase (se 2 (by rfl) ⟨519282, by rfl⟩ : syracuseStep 1384753 = 1038565) (by norm_num)
theorem B1663301 : Blo 1230433 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1384789 : Blo 1230433 1384789 := bbase (se 10 (by rfl) ⟨2028, by rfl⟩ : syracuseStep 1384789 = 4057) (by norm_num)
theorem B2769245 : Blo 1230433 2769245 := bbase (se 3 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 2769245 = 1038467) (by norm_num)
theorem B3326309 : Blo 1230433 3326309 := bbase (se 4 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 3326309 = 623683) (by norm_num)
theorem B1384825 : Blo 1230433 1384825 := bbase (se 2 (by rfl) ⟨519309, by rfl⟩ : syracuseStep 1384825 = 1038619) (by norm_num)
theorem B4153733 : Blo 1230433 4153733 := bbase (se 4 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 4153733 = 778825) (by norm_num)
theorem B3506581 : Blo 1230433 3506581 := bbase (se 6 (by rfl) ⟨82185, by rfl⟩ : syracuseStep 3506581 = 164371) (by norm_num)
theorem B1384861 : Blo 1230433 1384861 := bbase (se 3 (by rfl) ⟨259661, by rfl⟩ : syracuseStep 1384861 = 519323) (by norm_num)
theorem B2769317 : Blo 1230433 2769317 := bbase (se 4 (by rfl) ⟨259623, by rfl⟩ : syracuseStep 2769317 = 519247) (by norm_num)
theorem B1384897 : Blo 1230433 1384897 := bbase (se 2 (by rfl) ⟨519336, by rfl⟩ : syracuseStep 1384897 = 1038673) (by norm_num)
theorem B1384933 : Blo 1230433 1384933 := bbase (se 4 (by rfl) ⟨129837, by rfl⟩ : syracuseStep 1384933 = 259675) (by norm_num)
theorem B2769389 : Blo 1230433 2769389 := bbase (se 3 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 2769389 = 1038521) (by norm_num)
theorem B1384969 : Blo 1230433 1384969 := bbase (se 2 (by rfl) ⟨519363, by rfl⟩ : syracuseStep 1384969 = 1038727) (by norm_num)
theorem B1385005 : Blo 1230433 1385005 := bbase (se 3 (by rfl) ⟨259688, by rfl⟩ : syracuseStep 1385005 = 519377) (by norm_num)
theorem B2769461 : Blo 1230433 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B1385041 : Blo 1230433 1385041 := bbase (se 2 (by rfl) ⟨519390, by rfl⟩ : syracuseStep 1385041 = 1038781) (by norm_num)
theorem B1385077 : Blo 1230433 1385077 := bbase (se 5 (by rfl) ⟨64925, by rfl⟩ : syracuseStep 1385077 = 129851) (by norm_num)
theorem B2769533 : Blo 1230433 2769533 := bbase (se 3 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 2769533 = 1038575) (by norm_num)
theorem B1753741 : Blo 1230433 1753741 := bbase (se 3 (by rfl) ⟨328826, by rfl⟩ : syracuseStep 1753741 = 657653) (by norm_num)
theorem B1385113 : Blo 1230433 1385113 := bbase (se 2 (by rfl) ⟨519417, by rfl⟩ : syracuseStep 1385113 = 1038835) (by norm_num)
theorem B5259941 : Blo 1230433 5259941 := bbase (se 4 (by rfl) ⟨493119, by rfl⟩ : syracuseStep 5259941 = 986239) (by norm_num)
theorem B1385149 : Blo 1230433 1385149 := bbase (se 3 (by rfl) ⟨259715, by rfl⟩ : syracuseStep 1385149 = 519431) (by norm_num)
theorem B2769605 : Blo 1230433 2769605 := bbase (se 4 (by rfl) ⟨259650, by rfl⟩ : syracuseStep 2769605 = 519301) (by norm_num)
theorem B4678357 : Blo 1230433 4678357 := bbase (se 7 (by rfl) ⟨54824, by rfl⟩ : syracuseStep 4678357 = 109649) (by norm_num)
theorem B1385185 : Blo 1230433 1385185 := bbase (se 2 (by rfl) ⟨519444, by rfl⟩ : syracuseStep 1385185 = 1038889) (by norm_num)
theorem B1385221 : Blo 1230433 1385221 := bbase (se 4 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 1385221 = 259729) (by norm_num)
theorem B2769677 : Blo 1230433 2769677 := bbase (se 3 (by rfl) ⟨519314, by rfl⟩ : syracuseStep 2769677 = 1038629) (by norm_num)
theorem B7013141 : Blo 1230433 7013141 := bbase (se 6 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 7013141 = 328741) (by norm_num)
theorem B1385257 : Blo 1230433 1385257 := bbase (se 2 (by rfl) ⟨519471, by rfl⟩ : syracuseStep 1385257 = 1038943) (by norm_num)
theorem B1557301 : Blo 1230433 1557301 := bbase (se 5 (by rfl) ⟨72998, by rfl⟩ : syracuseStep 1557301 = 145997) (by norm_num)
theorem B4154165 : Blo 1230433 4154165 := bbase (se 5 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 4154165 = 389453) (by norm_num)
theorem B4440901 : Blo 1230433 4440901 := bbase (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) (by norm_num)
theorem B1385293 : Blo 1230433 1385293 := bbase (se 3 (by rfl) ⟨259742, by rfl⟩ : syracuseStep 1385293 = 519485) (by norm_num)
theorem B2769749 : Blo 1230433 2769749 := bbase (se 9 (by rfl) ⟨8114, by rfl⟩ : syracuseStep 2769749 = 16229) (by norm_num)
theorem B1385329 : Blo 1230433 1385329 := bbase (se 2 (by rfl) ⟨519498, by rfl⟩ : syracuseStep 1385329 = 1038997) (by norm_num)
theorem B1557397 : Blo 1230433 1557397 := bbase (se 6 (by rfl) ⟨36501, by rfl⟩ : syracuseStep 1557397 = 73003) (by norm_num)
theorem B1385365 : Blo 1230433 1385365 := bbase (se 6 (by rfl) ⟨32469, by rfl⟩ : syracuseStep 1385365 = 64939) (by norm_num)
theorem B2769821 : Blo 1230433 2769821 := bbase (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) (by norm_num)
theorem B1385401 : Blo 1230433 1385401 := bbase (se 2 (by rfl) ⟨519525, by rfl⟩ : syracuseStep 1385401 = 1039051) (by norm_num)
theorem B1385437 : Blo 1230433 1385437 := bbase (se 3 (by rfl) ⟨259769, by rfl⟩ : syracuseStep 1385437 = 519539) (by norm_num)
theorem B1754077 : Blo 1230433 1754077 := bbase (se 3 (by rfl) ⟨328889, by rfl⟩ : syracuseStep 1754077 = 657779) (by norm_num)
theorem B2769893 : Blo 1230433 2769893 := bbase (se 4 (by rfl) ⟨259677, by rfl⟩ : syracuseStep 2769893 = 519355) (by norm_num)
theorem B1385473 : Blo 1230433 1385473 := bbase (se 2 (by rfl) ⟨519552, by rfl⟩ : syracuseStep 1385473 = 1039105) (by norm_num)
theorem B4678661 : Blo 1230433 4678661 := bbase (se 4 (by rfl) ⟨438624, by rfl⟩ : syracuseStep 4678661 = 877249) (by norm_num)
theorem B1385509 : Blo 1230433 1385509 := bbase (se 4 (by rfl) ⟨129891, by rfl⟩ : syracuseStep 1385509 = 259783) (by norm_num)
theorem B2769965 : Blo 1230433 2769965 := bbase (se 3 (by rfl) ⟨519368, by rfl⟩ : syracuseStep 2769965 = 1038737) (by norm_num)
theorem B1557569 : Blo 1230433 1557569 := bbase (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) (by norm_num)
theorem B1385545 : Blo 1230433 1385545 := bbase (se 2 (by rfl) ⟨519579, by rfl⟩ : syracuseStep 1385545 = 1039159) (by norm_num)
theorem B1385581 : Blo 1230433 1385581 := bbase (se 3 (by rfl) ⟨259796, by rfl⟩ : syracuseStep 1385581 = 519593) (by norm_num)
theorem B2770037 : Blo 1230433 2770037 := bbase (se 5 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 2770037 = 259691) (by norm_num)
theorem B1557625 : Blo 1230433 1557625 := bbase (se 2 (by rfl) ⟨584109, by rfl⟩ : syracuseStep 1557625 = 1168219) (by norm_num)
theorem B1385617 : Blo 1230433 1385617 := bbase (se 2 (by rfl) ⟨519606, by rfl⟩ : syracuseStep 1385617 = 1039213) (by norm_num)
theorem B2368693 : Blo 1230433 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B2999477 : Blo 1230433 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1385653 : Blo 1230433 1385653 := bbase (se 5 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 1385653 = 129905) (by norm_num)
theorem B1754293 : Blo 1230433 1754293 := bbase (se 5 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 1754293 = 164465) (by norm_num)
theorem B2770109 : Blo 1230433 2770109 := bbase (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) (by norm_num)
theorem B1557721 : Blo 1230433 1557721 := bbase (se 2 (by rfl) ⟨584145, by rfl⟩ : syracuseStep 1557721 = 1168291) (by norm_num)
theorem B1385689 : Blo 1230433 1385689 := bbase (se 2 (by rfl) ⟨519633, by rfl⟩ : syracuseStep 1385689 = 1039267) (by norm_num)
theorem B4154597 : Blo 1230433 4154597 := bbase (se 4 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 4154597 = 778987) (by norm_num)
theorem B1369325 : Blo 1230433 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B2630893 : Blo 1230433 2630893 := bbase (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) (by norm_num)
theorem B1385725 : Blo 1230433 1385725 := bbase (se 3 (by rfl) ⟨259823, by rfl⟩ : syracuseStep 1385725 = 519647) (by norm_num)
theorem B2770181 : Blo 1230433 2770181 := bbase (se 4 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 2770181 = 519409) (by norm_num)
theorem B1385761 : Blo 1230433 1385761 := bbase (se 2 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 1385761 = 1039321) (by norm_num)
theorem B1385797 : Blo 1230433 1385797 := bbase (se 4 (by rfl) ⟨129918, by rfl⟩ : syracuseStep 1385797 = 259837) (by norm_num)
theorem B2770253 : Blo 1230433 2770253 := bbase (se 3 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 2770253 = 1038845) (by norm_num)
theorem B1385833 : Blo 1230433 1385833 := bbase (se 2 (by rfl) ⟨519687, by rfl⟩ : syracuseStep 1385833 = 1039375) (by norm_num)
theorem B1557893 : Blo 1230433 1557893 := bbase (se 4 (by rfl) ⟨146052, by rfl⟩ : syracuseStep 1557893 = 292105) (by norm_num)
theorem B2106757 : Blo 1230433 2106757 := bbase (se 4 (by rfl) ⟨197508, by rfl⟩ : syracuseStep 2106757 = 395017) (by norm_num)
theorem B2336141 : Blo 1230433 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B1385869 : Blo 1230433 1385869 := bbase (se 3 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 1385869 = 519701) (by norm_num)
theorem B2770325 : Blo 1230433 2770325 := bbase (se 6 (by rfl) ⟨64929, by rfl⟩ : syracuseStep 2770325 = 129859) (by norm_num)
theorem B6235541 : Blo 1230433 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B1385905 : Blo 1230433 1385905 := bbase (se 2 (by rfl) ⟨519714, by rfl⟩ : syracuseStep 1385905 = 1039429) (by norm_num)
theorem B1557949 : Blo 1230433 1557949 := bbase (se 3 (by rfl) ⟨292115, by rfl⟩ : syracuseStep 1557949 = 584231) (by norm_num)
theorem B1385941 : Blo 1230433 1385941 := bbase (se 7 (by rfl) ⟨16241, by rfl⟩ : syracuseStep 1385941 = 32483) (by norm_num)
theorem B2770397 : Blo 1230433 2770397 := bbase (se 3 (by rfl) ⟨519449, by rfl⟩ : syracuseStep 2770397 = 1038899) (by norm_num)
theorem B1385977 : Blo 1230433 1385977 := bbase (se 2 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 1385977 = 1039483) (by norm_num)
theorem B1558045 : Blo 1230433 1558045 := bbase (se 3 (by rfl) ⟨292133, by rfl⟩ : syracuseStep 1558045 = 584267) (by norm_num)
theorem B1386013 : Blo 1230433 1386013 := bbase (se 3 (by rfl) ⟨259877, by rfl⟩ : syracuseStep 1386013 = 519755) (by norm_num)
theorem B2336293 : Blo 1230433 2336293 := bbase (se 4 (by rfl) ⟨219027, by rfl⟩ : syracuseStep 2336293 = 438055) (by norm_num)
theorem B2770469 : Blo 1230433 2770469 := bbase (se 4 (by rfl) ⟨259731, by rfl⟩ : syracuseStep 2770469 = 519463) (by norm_num)
theorem B1754669 : Blo 1230433 1754669 := bbase (se 3 (by rfl) ⟨329000, by rfl⟩ : syracuseStep 1754669 = 658001) (by norm_num)
theorem B1386049 : Blo 1230433 1386049 := bbase (se 2 (by rfl) ⟨519768, by rfl⟩ : syracuseStep 1386049 = 1039537) (by norm_num)
theorem B1386085 : Blo 1230433 1386085 := bbase (se 4 (by rfl) ⟨129945, by rfl⟩ : syracuseStep 1386085 = 259891) (by norm_num)
theorem B2770541 : Blo 1230433 2770541 := bbase (se 3 (by rfl) ⟨519476, by rfl⟩ : syracuseStep 2770541 = 1038953) (by norm_num)
theorem B1386121 : Blo 1230433 1386121 := bbase (se 2 (by rfl) ⟨519795, by rfl⟩ : syracuseStep 1386121 = 1039591) (by norm_num)
theorem B4155029 : Blo 1230433 4155029 := bbase (se 6 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 4155029 = 194767) (by norm_num)
theorem B2000533 : Blo 1230433 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B2107037 : Blo 1230433 2107037 := bbase (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) (by norm_num)
theorem B1386157 : Blo 1230433 1386157 := bbase (se 3 (by rfl) ⟨259904, by rfl⟩ : syracuseStep 1386157 = 519809) (by norm_num)
theorem B2770613 : Blo 1230433 2770613 := bbase (se 5 (by rfl) ⟨129872, by rfl⟩ : syracuseStep 2770613 = 259745) (by norm_num)
theorem B1558217 : Blo 1230433 1558217 := bbase (se 2 (by rfl) ⟨584331, by rfl⟩ : syracuseStep 1558217 = 1168663) (by norm_num)
theorem B1386193 : Blo 1230433 1386193 := bbase (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) (by norm_num)
theorem B3114733 : Blo 1230433 3114733 := bbase (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) (by norm_num)
theorem B1386229 : Blo 1230433 1386229 := bbase (se 5 (by rfl) ⟨64979, by rfl⟩ : syracuseStep 1386229 = 129959) (by norm_num)
theorem B2770685 : Blo 1230433 2770685 := bbase (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) (by norm_num)
theorem B1558273 : Blo 1230433 1558273 := bbase (se 2 (by rfl) ⟨584352, by rfl⟩ : syracuseStep 1558273 = 1168705) (by norm_num)
theorem B1386265 : Blo 1230433 1386265 := bbase (se 2 (by rfl) ⟨519849, by rfl⟩ : syracuseStep 1386265 = 1039699) (by norm_num)
theorem B1386301 : Blo 1230433 1386301 := bbase (se 3 (by rfl) ⟨259931, by rfl⟩ : syracuseStep 1386301 = 519863) (by norm_num)
theorem B2770757 : Blo 1230433 2770757 := bbase (se 4 (by rfl) ⟨259758, by rfl⟩ : syracuseStep 2770757 = 519517) (by norm_num)
theorem B2336597 : Blo 1230433 2336597 := bbase (se 9 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 2336597 = 13691) (by norm_num)
theorem B3114845 : Blo 1230433 3114845 := bbase (se 3 (by rfl) ⟨584033, by rfl⟩ : syracuseStep 3114845 = 1168067) (by norm_num)
theorem B1558369 : Blo 1230433 1558369 := bbase (se 2 (by rfl) ⟨584388, by rfl⟩ : syracuseStep 1558369 = 1168777) (by norm_num)
theorem B1386337 : Blo 1230433 1386337 := bbase (se 2 (by rfl) ⟨519876, by rfl⟩ : syracuseStep 1386337 = 1039753) (by norm_num)
theorem B3508085 : Blo 1230433 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B1386373 : Blo 1230433 1386373 := bbase (se 4 (by rfl) ⟨129972, by rfl⟩ : syracuseStep 1386373 = 259945) (by norm_num)
theorem B2770829 : Blo 1230433 2770829 := bbase (se 3 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 2770829 = 1039061) (by norm_num)
theorem B1386409 : Blo 1230433 1386409 := bbase (se 2 (by rfl) ⟨519903, by rfl⟩ : syracuseStep 1386409 = 1039807) (by norm_num)
theorem B1386445 : Blo 1230433 1386445 := bbase (se 3 (by rfl) ⟨259958, by rfl⟩ : syracuseStep 1386445 = 519917) (by norm_num)
theorem B2770901 : Blo 1230433 2770901 := bbase (se 7 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 2770901 = 64943) (by norm_num)
theorem B1386481 : Blo 1230433 1386481 := bbase (se 2 (by rfl) ⟨519930, by rfl⟩ : syracuseStep 1386481 = 1039861) (by norm_num)
theorem B1558541 : Blo 1230433 1558541 := bbase (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) (by norm_num)
theorem B3115037 : Blo 1230433 3115037 := bbase (se 3 (by rfl) ⟨584069, by rfl⟩ : syracuseStep 3115037 = 1168139) (by norm_num)
theorem B2770973 : Blo 1230433 2770973 := bbase (se 3 (by rfl) ⟨519557, by rfl⟩ : syracuseStep 2770973 = 1039115) (by norm_num)
theorem B5916725 : Blo 1230433 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B4499509 : Blo 1230433 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B3557429 : Blo 1230433 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B4155461 : Blo 1230433 4155461 := bbase (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) (by norm_num)
theorem B1558597 : Blo 1230433 1558597 := bbase (se 4 (by rfl) ⟨146118, by rfl⟩ : syracuseStep 1558597 = 292237) (by norm_num)
theorem B2771045 : Blo 1230433 2771045 := bbase (se 4 (by rfl) ⟨259785, by rfl⟩ : syracuseStep 2771045 = 519571) (by norm_num)
theorem B2631781 : Blo 1230433 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B1558693 : Blo 1230433 1558693 := bbase (se 4 (by rfl) ⟨146127, by rfl⟩ : syracuseStep 1558693 = 292255) (by norm_num)
theorem B2771117 : Blo 1230433 2771117 := bbase (se 3 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 2771117 = 1039169) (by norm_num)
theorem B2771189 : Blo 1230433 2771189 := bbase (se 5 (by rfl) ⟨129899, by rfl⟩ : syracuseStep 2771189 = 259799) (by norm_num)
theorem B1665317 : Blo 1230433 1665317 := bbase (se 4 (by rfl) ⟨156123, by rfl⟩ : syracuseStep 1665317 = 312247) (by norm_num)
theorem B2771261 : Blo 1230433 2771261 := bbase (se 3 (by rfl) ⟨519611, by rfl⟩ : syracuseStep 2771261 = 1039223) (by norm_num)
theorem B1558865 : Blo 1230433 1558865 := bbase (se 2 (by rfl) ⟨584574, by rfl⟩ : syracuseStep 1558865 = 1169149) (by norm_num)
theorem B3115381 : Blo 1230433 3115381 := bbase (se 5 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 3115381 = 292067) (by norm_num)
theorem B2771333 : Blo 1230433 2771333 := bbase (se 4 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 2771333 = 519625) (by norm_num)
theorem B1558921 : Blo 1230433 1558921 := bbase (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) (by norm_num)
theorem B1845653 : Blo 1230433 1845653 := bbase (se 6 (by rfl) ⟨43257, by rfl⟩ : syracuseStep 1845653 = 86515) (by norm_num)
theorem B1845677 : Blo 1230433 1845677 := bbase (se 3 (by rfl) ⟨346064, by rfl⟩ : syracuseStep 1845677 = 692129) (by norm_num)
theorem B1845701 : Blo 1230433 1845701 := bbase (se 4 (by rfl) ⟨173034, by rfl⟩ : syracuseStep 1845701 = 346069) (by norm_num)
theorem B2771405 : Blo 1230433 2771405 := bbase (se 3 (by rfl) ⟨519638, by rfl⟩ : syracuseStep 2771405 = 1039277) (by norm_num)
theorem B1845725 : Blo 1230433 1845725 := bbase (se 3 (by rfl) ⟨346073, by rfl⟩ : syracuseStep 1845725 = 692147) (by norm_num)
theorem B3115493 : Blo 1230433 3115493 := bbase (se 4 (by rfl) ⟨292077, by rfl⟩ : syracuseStep 3115493 = 584155) (by norm_num)
theorem B1559017 : Blo 1230433 1559017 := bbase (se 2 (by rfl) ⟨584631, by rfl⟩ : syracuseStep 1559017 = 1169263) (by norm_num)
theorem B1845749 : Blo 1230433 1845749 := bbase (se 5 (by rfl) ⟨86519, by rfl⟩ : syracuseStep 1845749 = 173039) (by norm_num)
theorem B4155893 : Blo 1230433 4155893 := bbase (se 5 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 4155893 = 389615) (by norm_num)
theorem B1845773 : Blo 1230433 1845773 := bbase (se 3 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 1845773 = 692165) (by norm_num)
theorem B2771477 : Blo 1230433 2771477 := bbase (se 6 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 2771477 = 129913) (by norm_num)
theorem B1845797 : Blo 1230433 1845797 := bbase (se 4 (by rfl) ⟨173043, by rfl⟩ : syracuseStep 1845797 = 346087) (by norm_num)
theorem B1845821 : Blo 1230433 1845821 := bbase (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) (by norm_num)
theorem B2337349 : Blo 1230433 2337349 := bbase (se 4 (by rfl) ⟨219126, by rfl⟩ : syracuseStep 2337349 = 438253) (by norm_num)
theorem B1845845 : Blo 1230433 1845845 := bbase (se 8 (by rfl) ⟨10815, by rfl⟩ : syracuseStep 1845845 = 21631) (by norm_num)
theorem B2771549 : Blo 1230433 2771549 := bbase (se 3 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 2771549 = 1039331) (by norm_num)
theorem B1403497 : Blo 1230433 1403497 := bbase (se 2 (by rfl) ⟨526311, by rfl⟩ : syracuseStep 1403497 = 1052623) (by norm_num)
theorem B1845869 : Blo 1230433 1845869 := bbase (se 3 (by rfl) ⟨346100, by rfl⟩ : syracuseStep 1845869 = 692201) (by norm_num)
theorem B1845893 : Blo 1230433 1845893 := bbase (se 4 (by rfl) ⟨173052, by rfl⟩ : syracuseStep 1845893 = 346105) (by norm_num)
theorem B1559189 : Blo 1230433 1559189 := bbase (se 6 (by rfl) ⟨36543, by rfl⟩ : syracuseStep 1559189 = 73087) (by norm_num)
theorem B1845917 : Blo 1230433 1845917 := bbase (se 3 (by rfl) ⟨346109, by rfl⟩ : syracuseStep 1845917 = 692219) (by norm_num)
theorem B3115685 : Blo 1230433 3115685 := bbase (se 4 (by rfl) ⟨292095, by rfl⟩ : syracuseStep 3115685 = 584191) (by norm_num)
theorem B2771621 : Blo 1230433 2771621 := bbase (se 4 (by rfl) ⟨259839, by rfl⟩ : syracuseStep 2771621 = 519679) (by norm_num)
theorem B6236837 : Blo 1230433 6236837 := bbase (se 4 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 6236837 = 1169407) (by norm_num)
theorem B1845941 : Blo 1230433 1845941 := bbase (se 5 (by rfl) ⟨86528, by rfl⟩ : syracuseStep 1845941 = 173057) (by norm_num)
theorem B1845965 : Blo 1230433 1845965 := bbase (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) (by norm_num)
theorem B1559245 : Blo 1230433 1559245 := bbase (se 3 (by rfl) ⟨292358, by rfl⟩ : syracuseStep 1559245 = 584717) (by norm_num)
theorem B2337493 : Blo 1230433 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B1845989 : Blo 1230433 1845989 := bbase (se 4 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 1845989 = 346123) (by norm_num)
theorem B2960101 : Blo 1230433 2960101 := bbase (se 4 (by rfl) ⟨277509, by rfl⟩ : syracuseStep 2960101 = 555019) (by norm_num)
theorem B2771693 : Blo 1230433 2771693 := bbase (se 3 (by rfl) ⟨519692, by rfl⟩ : syracuseStep 2771693 = 1039385) (by norm_num)
theorem B1846013 : Blo 1230433 1846013 := bbase (se 3 (by rfl) ⟨346127, by rfl⟩ : syracuseStep 1846013 = 692255) (by norm_num)
theorem B1846037 : Blo 1230433 1846037 := bbase (se 6 (by rfl) ⟨43266, by rfl⟩ : syracuseStep 1846037 = 86533) (by norm_num)
theorem B1846061 : Blo 1230433 1846061 := bbase (se 3 (by rfl) ⟨346136, by rfl⟩ : syracuseStep 1846061 = 692273) (by norm_num)
theorem B1559341 : Blo 1230433 1559341 := bbase (se 3 (by rfl) ⟨292376, by rfl⟩ : syracuseStep 1559341 = 584753) (by norm_num)
theorem B2771765 : Blo 1230433 2771765 := bbase (se 5 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 2771765 = 259853) (by norm_num)
theorem B1846085 : Blo 1230433 1846085 := bbase (se 4 (by rfl) ⟨173070, by rfl⟩ : syracuseStep 1846085 = 346141) (by norm_num)
theorem B1403725 : Blo 1230433 1403725 := bbase (se 3 (by rfl) ⟨263198, by rfl⟩ : syracuseStep 1403725 = 526397) (by norm_num)
theorem B1846109 : Blo 1230433 1846109 := bbase (se 3 (by rfl) ⟨346145, by rfl⟩ : syracuseStep 1846109 = 692291) (by norm_num)
theorem B1846133 : Blo 1230433 1846133 := bbase (se 5 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 1846133 = 173075) (by norm_num)
theorem B2337653 : Blo 1230433 2337653 := bbase (se 5 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 2337653 = 219155) (by norm_num)
theorem B2771837 : Blo 1230433 2771837 := bbase (se 3 (by rfl) ⟨519719, by rfl⟩ : syracuseStep 2771837 = 1039439) (by norm_num)
theorem B1846157 : Blo 1230433 1846157 := bbase (se 3 (by rfl) ⟨346154, by rfl⟩ : syracuseStep 1846157 = 692309) (by norm_num)
theorem B1846181 : Blo 1230433 1846181 := bbase (se 4 (by rfl) ⟨173079, by rfl⟩ : syracuseStep 1846181 = 346159) (by norm_num)
theorem B4156325 : Blo 1230433 4156325 := bbase (se 4 (by rfl) ⟨389655, by rfl⟩ : syracuseStep 4156325 = 779311) (by norm_num)
theorem B2960293 : Blo 1230433 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B7015349 : Blo 1230433 7015349 := bbase (se 5 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 7015349 = 657689) (by norm_num)
theorem B1846205 : Blo 1230433 1846205 := bbase (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) (by norm_num)
theorem B2771909 : Blo 1230433 2771909 := bbase (se 4 (by rfl) ⟨259866, by rfl⟩ : syracuseStep 2771909 = 519733) (by norm_num)
theorem B2960333 : Blo 1230433 2960333 := bbase (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) (by norm_num)
theorem B1846229 : Blo 1230433 1846229 := bbase (se 7 (by rfl) ⟨21635, by rfl⟩ : syracuseStep 1846229 = 43271) (by norm_num)
theorem B1559513 : Blo 1230433 1559513 := bbase (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) (by norm_num)
theorem B1846253 : Blo 1230433 1846253 := bbase (se 3 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 1846253 = 692345) (by norm_num)
theorem B2370541 : Blo 1230433 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B3116029 : Blo 1230433 3116029 := bbase (se 3 (by rfl) ⟨584255, by rfl⟩ : syracuseStep 3116029 = 1168511) (by norm_num)
theorem B1846277 : Blo 1230433 1846277 := bbase (se 4 (by rfl) ⟨173088, by rfl⟩ : syracuseStep 1846277 = 346177) (by norm_num)
theorem B2337797 : Blo 1230433 2337797 := bbase (se 4 (by rfl) ⟨219168, by rfl⟩ : syracuseStep 2337797 = 438337) (by norm_num)
theorem B2771981 : Blo 1230433 2771981 := bbase (se 3 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 2771981 = 1039493) (by norm_num)
theorem B1559569 : Blo 1230433 1559569 := bbase (se 2 (by rfl) ⟨584838, by rfl⟩ : syracuseStep 1559569 = 1169677) (by norm_num)
theorem B1846301 : Blo 1230433 1846301 := bbase (se 3 (by rfl) ⟨346181, by rfl⟩ : syracuseStep 1846301 = 692363) (by norm_num)
theorem B1846325 : Blo 1230433 1846325 := bbase (se 5 (by rfl) ⟨86546, by rfl⟩ : syracuseStep 1846325 = 173093) (by norm_num)
theorem B9612341 : Blo 1230433 9612341 := bbase (se 5 (by rfl) ⟨450578, by rfl⟩ : syracuseStep 9612341 = 901157) (by norm_num)
theorem B1846349 : Blo 1230433 1846349 := bbase (se 3 (by rfl) ⟨346190, by rfl⟩ : syracuseStep 1846349 = 692381) (by norm_num)
theorem B2772053 : Blo 1230433 2772053 := bbase (se 8 (by rfl) ⟨16242, by rfl⟩ : syracuseStep 2772053 = 32485) (by norm_num)
theorem B1846373 : Blo 1230433 1846373 := bbase (se 4 (by rfl) ⟨173097, by rfl⟩ : syracuseStep 1846373 = 346195) (by norm_num)
theorem B3116141 : Blo 1230433 3116141 := bbase (se 3 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 3116141 = 1168553) (by norm_num)
theorem B1559665 : Blo 1230433 1559665 := bbase (se 2 (by rfl) ⟨584874, by rfl⟩ : syracuseStep 1559665 = 1169749) (by norm_num)
theorem B1846397 : Blo 1230433 1846397 := bbase (se 3 (by rfl) ⟨346199, by rfl⟩ : syracuseStep 1846397 = 692399) (by norm_num)
theorem B1846421 : Blo 1230433 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B3124373 : Blo 1230433 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B2772125 : Blo 1230433 2772125 := bbase (se 3 (by rfl) ⟨519773, by rfl⟩ : syracuseStep 2772125 = 1039547) (by norm_num)
theorem B1846445 : Blo 1230433 1846445 := bbase (se 3 (by rfl) ⟨346208, by rfl⟩ : syracuseStep 1846445 = 692417) (by norm_num)
theorem B1846469 : Blo 1230433 1846469 := bbase (se 4 (by rfl) ⟨173106, by rfl⟩ : syracuseStep 1846469 = 346213) (by norm_num)
theorem B1846493 : Blo 1230433 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B2772197 : Blo 1230433 2772197 := bbase (se 4 (by rfl) ⟨259893, by rfl⟩ : syracuseStep 2772197 = 519787) (by norm_num)
theorem B2960621 : Blo 1230433 2960621 := bbase (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) (by norm_num)
theorem B1846517 : Blo 1230433 1846517 := bbase (se 5 (by rfl) ⟨86555, by rfl⟩ : syracuseStep 1846517 = 173111) (by norm_num)
theorem B1846541 : Blo 1230433 1846541 := bbase (se 3 (by rfl) ⟨346226, by rfl⟩ : syracuseStep 1846541 = 692453) (by norm_num)
theorem B1846565 : Blo 1230433 1846565 := bbase (se 4 (by rfl) ⟨173115, by rfl⟩ : syracuseStep 1846565 = 346231) (by norm_num)
theorem B2338085 : Blo 1230433 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B3116333 : Blo 1230433 3116333 := bbase (se 3 (by rfl) ⟨584312, by rfl⟩ : syracuseStep 3116333 = 1168625) (by norm_num)
theorem B2772269 : Blo 1230433 2772269 := bbase (se 3 (by rfl) ⟨519800, by rfl⟩ : syracuseStep 2772269 = 1039601) (by norm_num)
theorem B1846589 : Blo 1230433 1846589 := bbase (se 3 (by rfl) ⟨346235, by rfl⟩ : syracuseStep 1846589 = 692471) (by norm_num)
theorem B1846613 : Blo 1230433 1846613 := bbase (se 11 (by rfl) ⟨1352, by rfl⟩ : syracuseStep 1846613 = 2705) (by norm_num)
theorem B4156757 : Blo 1230433 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B1846637 : Blo 1230433 1846637 := bbase (se 3 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 1846637 = 692489) (by norm_num)
theorem B2772341 : Blo 1230433 2772341 := bbase (se 5 (by rfl) ⟨129953, by rfl⟩ : syracuseStep 2772341 = 259907) (by norm_num)
theorem B1846661 : Blo 1230433 1846661 := bbase (se 4 (by rfl) ⟨173124, by rfl⟩ : syracuseStep 1846661 = 346249) (by norm_num)
theorem B2436493 : Blo 1230433 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B3943829 : Blo 1230433 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B1846685 : Blo 1230433 1846685 := bbase (se 3 (by rfl) ⟨346253, by rfl⟩ : syracuseStep 1846685 = 692507) (by norm_num)
theorem B5328293 : Blo 1230433 5328293 := bbase (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) (by norm_num)
theorem B1846709 : Blo 1230433 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B2338237 : Blo 1230433 2338237 := bbase (se 3 (by rfl) ⟨438419, by rfl⟩ : syracuseStep 2338237 = 876839) (by norm_num)
theorem B2772413 : Blo 1230433 2772413 := bbase (se 3 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 2772413 = 1039655) (by norm_num)
theorem B4435397 : Blo 1230433 4435397 := bbase (se 4 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 4435397 = 831637) (by norm_num)
theorem B1846733 : Blo 1230433 1846733 := bbase (se 3 (by rfl) ⟨346262, by rfl⟩ : syracuseStep 1846733 = 692525) (by norm_num)
theorem B1404373 : Blo 1230433 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B4672997 : Blo 1230433 4672997 := bbase (se 4 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 4672997 = 876187) (by norm_num)
theorem B1846757 : Blo 1230433 1846757 := bbase (se 4 (by rfl) ⟨173133, by rfl⟩ : syracuseStep 1846757 = 346267) (by norm_num)
theorem B1846781 : Blo 1230433 1846781 := bbase (se 3 (by rfl) ⟨346271, by rfl⟩ : syracuseStep 1846781 = 692543) (by norm_num)
theorem B2772485 : Blo 1230433 2772485 := bbase (se 4 (by rfl) ⟨259920, by rfl⟩ : syracuseStep 2772485 = 519841) (by norm_num)
theorem B1846805 : Blo 1230433 1846805 := bbase (se 6 (by rfl) ⟨43284, by rfl⟩ : syracuseStep 1846805 = 86569) (by norm_num)
theorem B1265189 : Blo 1230433 1265189 := bbase (se 4 (by rfl) ⟨118611, by rfl⟩ : syracuseStep 1265189 = 237223) (by norm_num)
theorem B1846829 : Blo 1230433 1846829 := bbase (se 3 (by rfl) ⟨346280, by rfl⟩ : syracuseStep 1846829 = 692561) (by norm_num)
theorem B1314353 : Blo 1230433 1314353 := bbase (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) (by norm_num)
theorem B1404469 : Blo 1230433 1404469 := bbase (se 5 (by rfl) ⟨65834, by rfl⟩ : syracuseStep 1404469 = 131669) (by norm_num)
theorem B1846853 : Blo 1230433 1846853 := bbase (se 4 (by rfl) ⟨173142, by rfl⟩ : syracuseStep 1846853 = 346285) (by norm_num)
theorem B2772557 : Blo 1230433 2772557 := bbase (se 3 (by rfl) ⟨519854, by rfl⟩ : syracuseStep 2772557 = 1039709) (by norm_num)
theorem B2248285 : Blo 1230433 2248285 := bbase (se 3 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 2248285 = 843107) (by norm_num)
theorem B1846877 : Blo 1230433 1846877 := bbase (se 3 (by rfl) ⟨346289, by rfl⟩ : syracuseStep 1846877 = 692579) (by norm_num)
theorem B1846901 : Blo 1230433 1846901 := bbase (se 5 (by rfl) ⟨86573, by rfl⟩ : syracuseStep 1846901 = 173147) (by norm_num)
theorem B3116677 : Blo 1230433 3116677 := bbase (se 4 (by rfl) ⟨292188, by rfl⟩ : syracuseStep 3116677 = 584377) (by norm_num)
theorem B1846925 : Blo 1230433 1846925 := bbase (se 3 (by rfl) ⟨346298, by rfl⟩ : syracuseStep 1846925 = 692597) (by norm_num)
theorem B2772629 : Blo 1230433 2772629 := bbase (se 6 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 2772629 = 129967) (by norm_num)
theorem B1846949 : Blo 1230433 1846949 := bbase (se 4 (by rfl) ⟨173151, by rfl⟩ : syracuseStep 1846949 = 346303) (by norm_num)
theorem B1846973 : Blo 1230433 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B1846997 : Blo 1230433 1846997 := bbase (se 7 (by rfl) ⟨21644, by rfl⟩ : syracuseStep 1846997 = 43289) (by norm_num)
theorem B2772701 : Blo 1230433 2772701 := bbase (se 3 (by rfl) ⟨519881, by rfl⟩ : syracuseStep 2772701 = 1039763) (by norm_num)
theorem B1847021 : Blo 1230433 1847021 := bbase (se 3 (by rfl) ⟨346316, by rfl⟩ : syracuseStep 1847021 = 692633) (by norm_num)
theorem B2338541 : Blo 1230433 2338541 := bbase (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) (by norm_num)
theorem B3116789 : Blo 1230433 3116789 := bbase (se 5 (by rfl) ⟨146099, by rfl⟩ : syracuseStep 3116789 = 292199) (by norm_num)
theorem B2076421 : Blo 1230433 2076421 := bbase (se 4 (by rfl) ⟨194664, by rfl⟩ : syracuseStep 2076421 = 389329) (by norm_num)
theorem B4673285 : Blo 1230433 4673285 := bbase (se 4 (by rfl) ⟨438120, by rfl⟩ : syracuseStep 4673285 = 876241) (by norm_num)
theorem B1847045 : Blo 1230433 1847045 := bbase (se 4 (by rfl) ⟨173160, by rfl⟩ : syracuseStep 1847045 = 346321) (by norm_num)
theorem B4157189 : Blo 1230433 4157189 := bbase (se 4 (by rfl) ⟨389736, by rfl⟩ : syracuseStep 4157189 = 779473) (by norm_num)
theorem B1847069 : Blo 1230433 1847069 := bbase (se 3 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 1847069 = 692651) (by norm_num)
theorem B2772773 : Blo 1230433 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B1847093 : Blo 1230433 1847093 := bbase (se 5 (by rfl) ⟨86582, by rfl⟩ : syracuseStep 1847093 = 173165) (by norm_num)
theorem B1847117 : Blo 1230433 1847117 := bbase (se 3 (by rfl) ⟨346334, by rfl⟩ : syracuseStep 1847117 = 692669) (by norm_num)
theorem B17764181 : Blo 1230433 17764181 := bbase (se 9 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 17764181 = 104087) (by norm_num)
theorem B2076509 : Blo 1230433 2076509 := bbase (se 3 (by rfl) ⟨389345, by rfl⟩ : syracuseStep 2076509 = 778691) (by norm_num)
theorem B1847141 : Blo 1230433 1847141 := bbase (se 4 (by rfl) ⟨173169, by rfl⟩ : syracuseStep 1847141 = 346339) (by norm_num)
theorem B1249133 : Blo 1230433 1249133 := bbase (se 3 (by rfl) ⟨234212, by rfl⟩ : syracuseStep 1249133 = 468425) (by norm_num)
theorem B2772845 : Blo 1230433 2772845 := bbase (se 3 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 2772845 = 1039817) (by norm_num)
theorem B1478513 : Blo 1230433 1478513 := bbase (se 2 (by rfl) ⟨554442, by rfl⟩ : syracuseStep 1478513 = 1108885) (by norm_num)
theorem B6655861 : Blo 1230433 6655861 := bbase (se 5 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 6655861 = 623987) (by norm_num)
theorem B1847165 : Blo 1230433 1847165 := bbase (se 3 (by rfl) ⟨346343, by rfl⟩ : syracuseStep 1847165 = 692687) (by norm_num)
theorem B7106453 : Blo 1230433 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B1847189 : Blo 1230433 1847189 := bbase (se 6 (by rfl) ⟨43293, by rfl⟩ : syracuseStep 1847189 = 86587) (by norm_num)
theorem B1847213 : Blo 1230433 1847213 := bbase (se 3 (by rfl) ⟨346352, by rfl⟩ : syracuseStep 1847213 = 692705) (by norm_num)
theorem B3116981 : Blo 1230433 3116981 := bbase (se 5 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 3116981 = 292217) (by norm_num)
theorem B6238133 : Blo 1230433 6238133 := bbase (se 5 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 6238133 = 584825) (by norm_num)
theorem B2772917 : Blo 1230433 2772917 := bbase (se 5 (by rfl) ⟨129980, by rfl⟩ : syracuseStep 2772917 = 259961) (by norm_num)
theorem B1847237 : Blo 1230433 1847237 := bbase (se 4 (by rfl) ⟨173178, by rfl⟩ : syracuseStep 1847237 = 346357) (by norm_num)
theorem B9351125 : Blo 1230433 9351125 := bbase (se 7 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 9351125 = 219167) (by norm_num)
theorem B2076637 : Blo 1230433 2076637 := bbase (se 3 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 2076637 = 778739) (by norm_num)
theorem B1847261 : Blo 1230433 1847261 := bbase (se 3 (by rfl) ⟨346361, by rfl⟩ : syracuseStep 1847261 = 692723) (by norm_num)
theorem B2666461 : Blo 1230433 2666461 := bbase (se 3 (by rfl) ⟨499961, by rfl⟩ : syracuseStep 2666461 = 999923) (by norm_num)
theorem B1314797 : Blo 1230433 1314797 := bbase (se 3 (by rfl) ⟨246524, by rfl⟩ : syracuseStep 1314797 = 493049) (by norm_num)
theorem B1847285 : Blo 1230433 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B2371589 : Blo 1230433 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B1847309 : Blo 1230433 1847309 := bbase (se 3 (by rfl) ⟨346370, by rfl⟩ : syracuseStep 1847309 = 692741) (by norm_num)
theorem B5918741 : Blo 1230433 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B1847333 : Blo 1230433 1847333 := bbase (se 4 (by rfl) ⟨173187, by rfl⟩ : syracuseStep 1847333 = 346375) (by norm_num)
theorem B2076725 : Blo 1230433 2076725 := bbase (se 5 (by rfl) ⟨97346, by rfl⟩ : syracuseStep 2076725 = 194693) (by norm_num)
theorem B1847357 : Blo 1230433 1847357 := bbase (se 3 (by rfl) ⟨346379, by rfl⟩ : syracuseStep 1847357 = 692759) (by norm_num)
theorem B1847381 : Blo 1230433 1847381 := bbase (se 8 (by rfl) ⟨10824, by rfl⟩ : syracuseStep 1847381 = 21649) (by norm_num)
theorem B1847405 : Blo 1230433 1847405 := bbase (se 3 (by rfl) ⟨346388, by rfl⟩ : syracuseStep 1847405 = 692777) (by norm_num)
theorem B1896565 : Blo 1230433 1896565 := bbase (se 5 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 1896565 = 177803) (by norm_num)
theorem B10514549 : Blo 1230433 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B1478773 : Blo 1230433 1478773 := bbase (se 5 (by rfl) ⟨69317, by rfl⟩ : syracuseStep 1478773 = 138635) (by norm_num)
theorem B1847429 : Blo 1230433 1847429 := bbase (se 4 (by rfl) ⟨173196, by rfl⟩ : syracuseStep 1847429 = 346393) (by norm_num)
theorem B1847453 : Blo 1230433 1847453 := bbase (se 3 (by rfl) ⟨346397, by rfl⟩ : syracuseStep 1847453 = 692795) (by norm_num)
theorem B2076853 : Blo 1230433 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B1847477 : Blo 1230433 1847477 := bbase (se 5 (by rfl) ⟨86600, by rfl⟩ : syracuseStep 1847477 = 173201) (by norm_num)
theorem B4157621 : Blo 1230433 4157621 := bbase (se 5 (by rfl) ⟨194888, by rfl⟩ : syracuseStep 4157621 = 389777) (by norm_num)
theorem B2887877 : Blo 1230433 2887877 := bbase (se 4 (by rfl) ⟨270738, by rfl⟩ : syracuseStep 2887877 = 541477) (by norm_num)
theorem B1847501 : Blo 1230433 1847501 := bbase (se 3 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 1847501 = 692813) (by norm_num)
theorem B5918933 : Blo 1230433 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B1315045 : Blo 1230433 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B1847525 : Blo 1230433 1847525 := bbase (se 4 (by rfl) ⟨173205, by rfl⟩ : syracuseStep 1847525 = 346411) (by norm_num)
theorem B1847549 : Blo 1230433 1847549 := bbase (se 3 (by rfl) ⟨346415, by rfl⟩ : syracuseStep 1847549 = 692831) (by norm_num)
theorem B2076941 : Blo 1230433 2076941 := bbase (se 3 (by rfl) ⟨389426, by rfl⟩ : syracuseStep 2076941 = 778853) (by norm_num)
theorem B3117325 : Blo 1230433 3117325 := bbase (se 3 (by rfl) ⟨584498, by rfl⟩ : syracuseStep 3117325 = 1168997) (by norm_num)
theorem B15175957 : Blo 1230433 15175957 := bbase (se 6 (by rfl) ⟨355686, by rfl⟩ : syracuseStep 15175957 = 711373) (by norm_num)
theorem B1847573 : Blo 1230433 1847573 := bbase (se 6 (by rfl) ⟨43302, by rfl⟩ : syracuseStep 1847573 = 86605) (by norm_num)
theorem B1847597 : Blo 1230433 1847597 := bbase (se 3 (by rfl) ⟨346424, by rfl⟩ : syracuseStep 1847597 = 692849) (by norm_num)
theorem B1478965 : Blo 1230433 1478965 := bbase (se 5 (by rfl) ⟨69326, by rfl⟩ : syracuseStep 1478965 = 138653) (by norm_num)
theorem B1265977 : Blo 1230433 1265977 := bbase (se 2 (by rfl) ⟨474741, by rfl⟩ : syracuseStep 1265977 = 949483) (by norm_num)
theorem B1847621 : Blo 1230433 1847621 := bbase (se 4 (by rfl) ⟨173214, by rfl⟩ : syracuseStep 1847621 = 346429) (by norm_num)
theorem B1478989 : Blo 1230433 1478989 := bbase (se 3 (by rfl) ⟨277310, by rfl⟩ : syracuseStep 1478989 = 554621) (by norm_num)
theorem B1478993 : Blo 1230433 1478993 := bbase (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) (by norm_num)
theorem B6230357 : Blo 1230433 6230357 := bbase (se 10 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 6230357 = 18253) (by norm_num)
theorem B1847645 : Blo 1230433 1847645 := bbase (se 3 (by rfl) ⟨346433, by rfl⟩ : syracuseStep 1847645 = 692867) (by norm_num)
theorem B1847669 : Blo 1230433 1847669 := bbase (se 5 (by rfl) ⟨86609, by rfl⟩ : syracuseStep 1847669 = 173219) (by norm_num)
theorem B3117437 : Blo 1230433 3117437 := bbase (se 3 (by rfl) ⟨584519, by rfl⟩ : syracuseStep 3117437 = 1169039) (by norm_num)
theorem B2077069 : Blo 1230433 2077069 := bbase (se 3 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 2077069 = 778901) (by norm_num)
theorem B1847693 : Blo 1230433 1847693 := bbase (se 3 (by rfl) ⟨346442, by rfl⟩ : syracuseStep 1847693 = 692885) (by norm_num)
theorem B1847717 : Blo 1230433 1847717 := bbase (se 4 (by rfl) ⟨173223, by rfl⟩ : syracuseStep 1847717 = 346447) (by norm_num)
theorem B1847741 : Blo 1230433 1847741 := bbase (se 3 (by rfl) ⟨346451, by rfl⟩ : syracuseStep 1847741 = 692903) (by norm_num)
theorem B1847765 : Blo 1230433 1847765 := bbase (se 7 (by rfl) ⟨21653, by rfl⟩ : syracuseStep 1847765 = 43307) (by norm_num)
theorem B2339293 : Blo 1230433 2339293 := bbase (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) (by norm_num)
theorem B2077157 : Blo 1230433 2077157 := bbase (se 4 (by rfl) ⟨194733, by rfl⟩ : syracuseStep 2077157 = 389467) (by norm_num)
theorem B1847789 : Blo 1230433 1847789 := bbase (se 3 (by rfl) ⟨346460, by rfl⟩ : syracuseStep 1847789 = 692921) (by norm_num)
theorem B1847813 : Blo 1230433 1847813 := bbase (se 4 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 1847813 = 346465) (by norm_num)
theorem B1847837 : Blo 1230433 1847837 := bbase (se 3 (by rfl) ⟨346469, by rfl⟩ : syracuseStep 1847837 = 692939) (by norm_num)
theorem B1847861 : Blo 1230433 1847861 := bbase (se 5 (by rfl) ⟨86618, by rfl⟩ : syracuseStep 1847861 = 173237) (by norm_num)
theorem B3117629 : Blo 1230433 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B1847885 : Blo 1230433 1847885 := bbase (se 3 (by rfl) ⟨346478, by rfl⟩ : syracuseStep 1847885 = 692957) (by norm_num)
theorem B15782485 : Blo 1230433 15782485 := bbase (se 8 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 15782485 = 184951) (by norm_num)
theorem B2077285 : Blo 1230433 2077285 := bbase (se 4 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 2077285 = 389491) (by norm_num)
theorem B1847909 : Blo 1230433 1847909 := bbase (se 4 (by rfl) ⟨173241, by rfl⟩ : syracuseStep 1847909 = 346483) (by norm_num)
theorem B4158053 : Blo 1230433 4158053 := bbase (se 4 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 4158053 = 779635) (by norm_num)
theorem B5263973 : Blo 1230433 5263973 := bbase (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) (by norm_num)
theorem B2339437 : Blo 1230433 2339437 := bbase (se 3 (by rfl) ⟨438644, by rfl⟩ : syracuseStep 2339437 = 877289) (by norm_num)
theorem B1847933 : Blo 1230433 1847933 := bbase (se 3 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 1847933 = 692975) (by norm_num)
theorem B1872533 : Blo 1230433 1872533 := bbase (se 6 (by rfl) ⟨43887, by rfl⟩ : syracuseStep 1872533 = 87775) (by norm_num)
theorem B1315477 : Blo 1230433 1315477 := bbase (se 6 (by rfl) ⟨30831, by rfl⟩ : syracuseStep 1315477 = 61663) (by norm_num)
theorem B1847957 : Blo 1230433 1847957 := bbase (se 6 (by rfl) ⟨43311, by rfl⟩ : syracuseStep 1847957 = 86623) (by norm_num)
theorem B1847981 : Blo 1230433 1847981 := bbase (se 3 (by rfl) ⟨346496, by rfl⟩ : syracuseStep 1847981 = 692993) (by norm_num)
theorem B2077373 : Blo 1230433 2077373 := bbase (se 3 (by rfl) ⟨389507, by rfl⟩ : syracuseStep 2077373 = 779015) (by norm_num)
theorem B1848005 : Blo 1230433 1848005 := bbase (se 4 (by rfl) ⟨173250, by rfl⟩ : syracuseStep 1848005 = 346501) (by norm_num)
theorem B1315549 : Blo 1230433 1315549 := bbase (se 3 (by rfl) ⟨246665, by rfl⟩ : syracuseStep 1315549 = 493331) (by norm_num)
theorem B1848029 : Blo 1230433 1848029 := bbase (se 3 (by rfl) ⟨346505, by rfl⟩ : syracuseStep 1848029 = 693011) (by norm_num)
theorem B2806501 : Blo 1230433 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B2249461 : Blo 1230433 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B1848053 : Blo 1230433 1848053 := bbase (se 5 (by rfl) ⟨86627, by rfl⟩ : syracuseStep 1848053 = 173255) (by norm_num)
theorem B1848077 : Blo 1230433 1848077 := bbase (se 3 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 1848077 = 693029) (by norm_num)
theorem B2339597 : Blo 1230433 2339597 := bbase (se 3 (by rfl) ⟨438674, by rfl⟩ : syracuseStep 2339597 = 877349) (by norm_num)
theorem B1848101 : Blo 1230433 1848101 := bbase (se 4 (by rfl) ⟨173259, by rfl⟩ : syracuseStep 1848101 = 346519) (by norm_num)
theorem B2077501 : Blo 1230433 2077501 := bbase (se 3 (by rfl) ⟨389531, by rfl⟩ : syracuseStep 2077501 = 779063) (by norm_num)
theorem B1848125 : Blo 1230433 1848125 := bbase (se 3 (by rfl) ⟨346523, by rfl⟩ : syracuseStep 1848125 = 693047) (by norm_num)
theorem B2700101 : Blo 1230433 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B1479493 : Blo 1230433 1479493 := bbase (se 4 (by rfl) ⟨138702, by rfl⟩ : syracuseStep 1479493 = 277405) (by norm_num)
theorem B1848149 : Blo 1230433 1848149 := bbase (se 9 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 1848149 = 10829) (by norm_num)
theorem B1848173 : Blo 1230433 1848173 := bbase (se 3 (by rfl) ⟨346532, by rfl⟩ : syracuseStep 1848173 = 693065) (by norm_num)
theorem B1848197 : Blo 1230433 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B2077589 : Blo 1230433 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B3117973 : Blo 1230433 3117973 := bbase (se 6 (by rfl) ⟨73077, by rfl⟩ : syracuseStep 3117973 = 146155) (by norm_num)
theorem B1848221 : Blo 1230433 1848221 := bbase (se 3 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 1848221 = 693083) (by norm_num)
theorem B4674469 : Blo 1230433 4674469 := bbase (se 4 (by rfl) ⟨438231, by rfl⟩ : syracuseStep 4674469 = 876463) (by norm_num)
theorem B1479589 : Blo 1230433 1479589 := bbase (se 4 (by rfl) ⟨138711, by rfl⟩ : syracuseStep 1479589 = 277423) (by norm_num)
theorem B11826101 : Blo 1230433 11826101 := bbase (se 5 (by rfl) ⟨554348, by rfl⟩ : syracuseStep 11826101 = 1108697) (by norm_num)
theorem B1848245 : Blo 1230433 1848245 := bbase (se 5 (by rfl) ⟨86636, by rfl⟩ : syracuseStep 1848245 = 173273) (by norm_num)
theorem B1848269 : Blo 1230433 1848269 := bbase (se 3 (by rfl) ⟨346550, by rfl⟩ : syracuseStep 1848269 = 693101) (by norm_num)
theorem B1848293 : Blo 1230433 1848293 := bbase (se 4 (by rfl) ⟨173277, by rfl⟩ : syracuseStep 1848293 = 346555) (by norm_num)
theorem B5256181 : Blo 1230433 5256181 := bbase (se 5 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 5256181 = 492767) (by norm_num)
theorem B1848317 : Blo 1230433 1848317 := bbase (se 3 (by rfl) ⟨346559, by rfl⟩ : syracuseStep 1848317 = 693119) (by norm_num)
theorem B3118085 : Blo 1230433 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B2077717 : Blo 1230433 2077717 := bbase (se 6 (by rfl) ⟨48696, by rfl⟩ : syracuseStep 2077717 = 97393) (by norm_num)
theorem B4158485 : Blo 1230433 4158485 := bbase (se 6 (by rfl) ⟨97464, by rfl⟩ : syracuseStep 4158485 = 194929) (by norm_num)
theorem B1848341 : Blo 1230433 1848341 := bbase (se 6 (by rfl) ⟨43320, by rfl⟩ : syracuseStep 1848341 = 86641) (by norm_num)
theorem B1848365 : Blo 1230433 1848365 := bbase (se 3 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 1848365 = 693137) (by norm_num)
theorem B1848389 : Blo 1230433 1848389 := bbase (se 4 (by rfl) ⟨173286, by rfl⟩ : syracuseStep 1848389 = 346573) (by norm_num)
theorem B1315921 : Blo 1230433 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B3847253 : Blo 1230433 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B1848413 : Blo 1230433 1848413 := bbase (se 3 (by rfl) ⟨346577, by rfl⟩ : syracuseStep 1848413 = 693155) (by norm_num)
theorem B2077805 : Blo 1230433 2077805 := bbase (se 3 (by rfl) ⟨389588, by rfl⟩ : syracuseStep 2077805 = 779177) (by norm_num)
theorem B2806901 : Blo 1230433 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1848437 : Blo 1230433 1848437 := bbase (se 5 (by rfl) ⟨86645, by rfl⟩ : syracuseStep 1848437 = 173291) (by norm_num)
theorem B1848461 : Blo 1230433 1848461 := bbase (se 3 (by rfl) ⟨346586, by rfl⟩ : syracuseStep 1848461 = 693173) (by norm_num)
theorem B1848485 : Blo 1230433 1848485 := bbase (se 4 (by rfl) ⟨173295, by rfl⟩ : syracuseStep 1848485 = 346591) (by norm_num)
theorem B1848509 : Blo 1230433 1848509 := bbase (se 3 (by rfl) ⟨346595, by rfl⟩ : syracuseStep 1848509 = 693191) (by norm_num)
theorem B3118277 : Blo 1230433 3118277 := bbase (se 4 (by rfl) ⟨292338, by rfl⟩ : syracuseStep 3118277 = 584677) (by norm_num)
theorem B4674773 : Blo 1230433 4674773 := bbase (se 7 (by rfl) ⟨54782, by rfl⟩ : syracuseStep 4674773 = 109565) (by norm_num)
theorem B1848533 : Blo 1230433 1848533 := bbase (se 7 (by rfl) ⟨21662, by rfl⟩ : syracuseStep 1848533 = 43325) (by norm_num)
theorem B2077933 : Blo 1230433 2077933 := bbase (se 3 (by rfl) ⟨389612, by rfl⟩ : syracuseStep 2077933 = 779225) (by norm_num)
theorem B1848557 : Blo 1230433 1848557 := bbase (se 3 (by rfl) ⟨346604, by rfl⟩ : syracuseStep 1848557 = 693209) (by norm_num)
theorem B1848581 : Blo 1230433 1848581 := bbase (se 4 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 1848581 = 346609) (by norm_num)
theorem B1848605 : Blo 1230433 1848605 := bbase (se 3 (by rfl) ⟨346613, by rfl⟩ : syracuseStep 1848605 = 693227) (by norm_num)
theorem B1848629 : Blo 1230433 1848629 := bbase (se 5 (by rfl) ⟨86654, by rfl⟩ : syracuseStep 1848629 = 173309) (by norm_num)
theorem B1873213 : Blo 1230433 1873213 := bbase (se 3 (by rfl) ⟨351227, by rfl⟩ : syracuseStep 1873213 = 702455) (by norm_num)
theorem B2078021 : Blo 1230433 2078021 := bbase (se 4 (by rfl) ⟨194814, by rfl⟩ : syracuseStep 2078021 = 389629) (by norm_num)
theorem B6657461 : Blo 1230433 6657461 := bbase (se 5 (by rfl) ⟨312068, by rfl⟩ : syracuseStep 6657461 = 624137) (by norm_num)
theorem B2078149 : Blo 1230433 2078149 := bbase (se 4 (by rfl) ⟨194826, by rfl⟩ : syracuseStep 2078149 = 389653) (by norm_num)
theorem B4158917 : Blo 1230433 4158917 := bbase (se 4 (by rfl) ⟨389898, by rfl⟩ : syracuseStep 4158917 = 779797) (by norm_num)
theorem B2078237 : Blo 1230433 2078237 := bbase (se 3 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 2078237 = 779339) (by norm_num)
theorem B3118621 : Blo 1230433 3118621 := bbase (se 3 (by rfl) ⟨584741, by rfl⟩ : syracuseStep 3118621 = 1169483) (by norm_num)
theorem B4437557 : Blo 1230433 4437557 := bbase (se 5 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 4437557 = 416021) (by norm_num)
theorem B6231653 : Blo 1230433 6231653 := bbase (se 4 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 6231653 = 1168435) (by norm_num)
theorem B2807405 : Blo 1230433 2807405 := bbase (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) (by norm_num)
theorem B3118733 : Blo 1230433 3118733 := bbase (se 3 (by rfl) ⟨584762, by rfl⟩ : syracuseStep 3118733 = 1169525) (by norm_num)
theorem B2078365 : Blo 1230433 2078365 := bbase (se 3 (by rfl) ⟨389693, by rfl⟩ : syracuseStep 2078365 = 779387) (by norm_num)
theorem B7009973 : Blo 1230433 7009973 := bbase (se 5 (by rfl) ⟨328592, by rfl⟩ : syracuseStep 7009973 = 657185) (by norm_num)
theorem B2078453 : Blo 1230433 2078453 := bbase (se 5 (by rfl) ⟨97427, by rfl⟩ : syracuseStep 2078453 = 194855) (by norm_num)
theorem B2807557 : Blo 1230433 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B3503893 : Blo 1230433 3503893 := bbase (se 6 (by rfl) ⟨82122, by rfl⟩ : syracuseStep 3503893 = 164245) (by norm_num)
theorem B1333045 : Blo 1230433 1333045 := bbase (se 5 (by rfl) ⟨62486, by rfl⟩ : syracuseStep 1333045 = 124973) (by norm_num)
theorem B3118925 : Blo 1230433 3118925 := bbase (se 3 (by rfl) ⟨584798, by rfl⟩ : syracuseStep 3118925 = 1169597) (by norm_num)
theorem B4437845 : Blo 1230433 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B2078581 : Blo 1230433 2078581 := bbase (se 5 (by rfl) ⟨97433, by rfl⟩ : syracuseStep 2078581 = 194867) (by norm_num)
theorem B4159349 : Blo 1230433 4159349 := bbase (se 5 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 4159349 = 389939) (by norm_num)
theorem B1480565 : Blo 1230433 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B3504053 : Blo 1230433 3504053 := bbase (se 5 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 3504053 = 328505) (by norm_num)
theorem B2078669 : Blo 1230433 2078669 := bbase (se 3 (by rfl) ⟨389750, by rfl⟩ : syracuseStep 2078669 = 779501) (by norm_num)
theorem B3373093 : Blo 1230433 3373093 := bbase (se 4 (by rfl) ⟨316227, by rfl⟩ : syracuseStep 3373093 = 632455) (by norm_num)
theorem B2078797 : Blo 1230433 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B1972325 : Blo 1230433 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B5617781 : Blo 1230433 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B3504293 : Blo 1230433 3504293 := bbase (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) (by norm_num)
theorem B2078885 : Blo 1230433 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B3119269 : Blo 1230433 3119269 := bbase (se 4 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 3119269 = 584863) (by norm_num)
theorem B17742037 : Blo 1230433 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B6314213 : Blo 1230433 6314213 := bbase (se 4 (by rfl) ⟨591957, by rfl⟩ : syracuseStep 6314213 = 1183915) (by norm_num)
theorem B5921029 : Blo 1230433 5921029 := bbase (se 4 (by rfl) ⟨555096, by rfl⟩ : syracuseStep 5921029 = 1110193) (by norm_num)
theorem B5331221 : Blo 1230433 5331221 := bbase (se 6 (by rfl) ⟨124950, by rfl⟩ : syracuseStep 5331221 = 249901) (by norm_num)
theorem B3119381 : Blo 1230433 3119381 := bbase (se 6 (by rfl) ⟨73110, by rfl⟩ : syracuseStep 3119381 = 146221) (by norm_num)
theorem B2079013 : Blo 1230433 2079013 := bbase (se 4 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 2079013 = 389815) (by norm_num)
theorem B1972549 : Blo 1230433 1972549 := bbase (se 4 (by rfl) ⟨184926, by rfl⟩ : syracuseStep 1972549 = 369853) (by norm_num)
theorem B3504485 : Blo 1230433 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B2079101 : Blo 1230433 2079101 := bbase (se 3 (by rfl) ⟨389831, by rfl⟩ : syracuseStep 2079101 = 779663) (by norm_num)
theorem B1423765 : Blo 1230433 1423765 := bbase (se 6 (by rfl) ⟨33369, by rfl⟩ : syracuseStep 1423765 = 66739) (by norm_num)
theorem B5257669 : Blo 1230433 5257669 := bbase (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) (by norm_num)
theorem B5257685 : Blo 1230433 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B16857557 : Blo 1230433 16857557 := bbase (se 7 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 16857557 = 395099) (by norm_num)
theorem B3119573 : Blo 1230433 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B3946981 : Blo 1230433 3946981 := bbase (se 4 (by rfl) ⟨370029, by rfl⟩ : syracuseStep 3946981 = 740059) (by norm_num)
theorem B2079229 : Blo 1230433 2079229 := bbase (se 3 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 2079229 = 779711) (by norm_num)
theorem B2079317 : Blo 1230433 2079317 := bbase (se 8 (by rfl) ⟨12183, by rfl⟩ : syracuseStep 2079317 = 24367) (by norm_num)
theorem B11844245 : Blo 1230433 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B2079445 : Blo 1230433 2079445 := bbase (se 7 (by rfl) ⟨24368, by rfl⟩ : syracuseStep 2079445 = 48737) (by norm_num)
theorem B2079533 : Blo 1230433 2079533 := bbase (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) (by norm_num)
theorem B7011157 : Blo 1230433 7011157 := bbase (se 9 (by rfl) ⟨20540, by rfl⟩ : syracuseStep 7011157 = 41081) (by norm_num)
theorem B9001813 : Blo 1230433 9001813 := bbase (se 9 (by rfl) ⟨26372, by rfl⟩ : syracuseStep 9001813 = 52745) (by norm_num)
theorem B6314869 : Blo 1230433 6314869 := bbase (se 5 (by rfl) ⟨296009, by rfl⟩ : syracuseStep 6314869 = 592019) (by norm_num)
theorem B6232949 : Blo 1230433 6232949 := bbase (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) (by norm_num)
theorem B2218909 : Blo 1230433 2218909 := bbase (se 3 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 2218909 = 832091) (by norm_num)
theorem B2079661 : Blo 1230433 2079661 := bbase (se 3 (by rfl) ⟨389936, by rfl⟩ : syracuseStep 2079661 = 779873) (by norm_num)
theorem B10517525 : Blo 1230433 10517525 := bbase (se 6 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 10517525 = 493009) (by norm_num)
theorem B1752197 : Blo 1230433 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B2956517 : Blo 1230433 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B3849445 : Blo 1230433 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B2628877 : Blo 1230433 2628877 := bbase (se 3 (by rfl) ⟨492914, by rfl⟩ : syracuseStep 2628877 = 985829) (by norm_num)
theorem B4676885 : Blo 1230433 4676885 := bbase (se 6 (by rfl) ⟨109614, by rfl⟩ : syracuseStep 4676885 = 219229) (by norm_num)
theorem B8879381 : Blo 1230433 8879381 := bbase (se 6 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 8879381 = 416221) (by norm_num)
theorem B3505477 : Blo 1230433 3505477 := bbase (se 4 (by rfl) ⟨328638, by rfl⟩ : syracuseStep 3505477 = 657277) (by norm_num)
theorem B1580401 : Blo 1230433 1580401 := bbase (se 2 (by rfl) ⟨592650, by rfl⟩ : syracuseStep 1580401 = 1185301) (by norm_num)
theorem B7888373 : Blo 1230433 7888373 := bbase (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) (by norm_num)
theorem B4152869 : Blo 1230433 4152869 := bbase (se 4 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 4152869 = 778663) (by norm_num)
theorem B4677173 : Blo 1230433 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B2629253 : Blo 1230433 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B2768525 : Blo 1230433 2768525 := bbase (se 3 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 2768525 = 1038197) (by norm_num)
theorem B2219717 : Blo 1230433 2219717 := bbase (se 4 (by rfl) ⟨208098, by rfl⟩ : syracuseStep 2219717 = 416197) (by norm_num)
theorem B1973965 : Blo 1230433 1973965 := bbase (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) (by norm_num)
theorem B2768597 : Blo 1230433 2768597 := bbase (se 7 (by rfl) ⟨32444, by rfl⟩ : syracuseStep 2768597 = 64889) (by norm_num)
theorem B5996261 : Blo 1230433 5996261 := bbase (se 4 (by rfl) ⟨562149, by rfl⟩ : syracuseStep 5996261 = 1124299) (by norm_num)
theorem B1924877 : Blo 1230433 1924877 := bbase (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) (by norm_num)
theorem B2768669 : Blo 1230433 2768669 := bbase (se 3 (by rfl) ⟨519125, by rfl⟩ : syracuseStep 2768669 = 1038251) (by norm_num)
theorem B1384249 : Blo 1230433 1384249 := bbase (se 2 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 1384249 = 1038187) (by norm_num)
theorem B2957141 : Blo 1230433 2957141 := bbase (se 9 (by rfl) ⟨8663, by rfl⟩ : syracuseStep 2957141 = 17327) (by norm_num)
theorem B1384285 : Blo 1230433 1384285 := bbase (se 3 (by rfl) ⟨259553, by rfl⟩ : syracuseStep 1384285 = 519107) (by norm_num)
theorem B2768741 : Blo 1230433 2768741 := bbase (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) (by norm_num)
theorem B1752949 : Blo 1230433 1752949 := bbase (se 5 (by rfl) ⟨82169, by rfl⟩ : syracuseStep 1752949 = 164339) (by norm_num)
theorem B1384321 : Blo 1230433 1384321 := bbase (se 2 (by rfl) ⟨519120, by rfl⟩ : syracuseStep 1384321 = 1038241) (by norm_num)
theorem B2809741 : Blo 1230433 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B1384357 : Blo 1230433 1384357 := bbase (se 4 (by rfl) ⟨129783, by rfl⟩ : syracuseStep 1384357 = 259567) (by norm_num)
theorem B2768813 : Blo 1230433 2768813 := bbase (se 3 (by rfl) ⟨519152, by rfl⟩ : syracuseStep 2768813 = 1038305) (by norm_num)
theorem B1384393 : Blo 1230433 1384393 := bbase (se 2 (by rfl) ⟨519147, by rfl⟩ : syracuseStep 1384393 = 1038295) (by norm_num)
theorem B4153301 : Blo 1230433 4153301 := bbase (se 7 (by rfl) ⟨48671, by rfl⟩ : syracuseStep 4153301 = 97343) (by norm_num)
theorem B1384429 : Blo 1230433 1384429 := bbase (se 3 (by rfl) ⟨259580, by rfl⟩ : syracuseStep 1384429 = 519161) (by norm_num)
theorem B2768885 : Blo 1230433 2768885 := bbase (se 5 (by rfl) ⟨129791, by rfl⟩ : syracuseStep 2768885 = 259583) (by norm_num)
theorem B1581059 : Blo 1230433 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B1384483 : Blo 1230433 1384483 := bstep (se 1 (by rfl) ⟨1038362, by rfl⟩ : syracuseStep 1384483 = 2076725) B2076725
theorem B4497457 : Blo 1230433 4497457 := bstep (se 2 (by rfl) ⟨1686546, by rfl⟩ : syracuseStep 4497457 = 3373093) B3373093
theorem B1925251 : Blo 1230433 1925251 := bstep (se 1 (by rfl) ⟨1443938, by rfl⟩ : syracuseStep 1925251 = 2887877) B2887877
theorem B4153517 : Blo 1230433 4153517 := bstep (se 3 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 4153517 = 1557569) B1557569
theorem B1384627 : Blo 1230433 1384627 := bstep (se 1 (by rfl) ⟨1038470, by rfl⟩ : syracuseStep 1384627 = 2076941) B2076941
theorem B4153571 : Blo 1230433 4153571 := bstep (se 1 (by rfl) ⟨3115178, by rfl⟩ : syracuseStep 4153571 = 6230357) B6230357
theorem B2769137 : Blo 1230433 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B2769155 : Blo 1230433 2769155 := bstep (se 1 (by rfl) ⟨2076866, by rfl⟩ : syracuseStep 2769155 = 4153733) B4153733
theorem B1384771 : Blo 1230433 1384771 := bstep (se 1 (by rfl) ⟨1038578, by rfl⟩ : syracuseStep 1384771 = 2077157) B2077157
theorem B20234609 : Blo 1230433 20234609 := bstep (se 2 (by rfl) ⟨7587978, by rfl⟩ : syracuseStep 20234609 = 15175957) B15175957
theorem B1687969 : Blo 1230433 1687969 := bstep (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) B1265977
theorem B2630065 : Blo 1230433 2630065 := bstep (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) B1972549
theorem B3506627 : Blo 1230433 3506627 := bstep (se 1 (by rfl) ⟨2629970, by rfl⟩ : syracuseStep 3506627 = 5259941) B5259941
theorem B1384915 : Blo 1230433 1384915 := bstep (se 1 (by rfl) ⟨1038686, by rfl⟩ : syracuseStep 1384915 = 2077373) B2077373
theorem B4153841 : Blo 1230433 4153841 := bstep (se 2 (by rfl) ⟨1557690, by rfl⟩ : syracuseStep 4153841 = 3115381) B3115381
theorem B2769425 : Blo 1230433 2769425 := bstep (se 2 (by rfl) ⟨1038534, by rfl⟩ : syracuseStep 2769425 = 2077069) B2077069
theorem B2769443 : Blo 1230433 2769443 := bstep (se 1 (by rfl) ⟨2077082, by rfl⟩ : syracuseStep 2769443 = 4154165) B4154165
theorem B1385059 : Blo 1230433 1385059 := bstep (se 1 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 1385059 = 2077589) B2077589
theorem B1385203 : Blo 1230433 1385203 := bstep (se 1 (by rfl) ⟨1038902, by rfl⟩ : syracuseStep 1385203 = 2077805) B2077805
theorem B6234893 : Blo 1230433 6234893 := bstep (se 3 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 6234893 = 2338085) B2338085
theorem B4440845 : Blo 1230433 4440845 := bstep (se 3 (by rfl) ⟨832658, by rfl⟩ : syracuseStep 4440845 = 1665317) B1665317
theorem B1999651 : Blo 1230433 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B2769713 : Blo 1230433 2769713 := bstep (se 2 (by rfl) ⟨1038642, by rfl⟩ : syracuseStep 2769713 = 2077285) B2077285
theorem B2769731 : Blo 1230433 2769731 := bstep (se 1 (by rfl) ⟨2077298, by rfl⟩ : syracuseStep 2769731 = 4154597) B4154597
theorem B1753969 : Blo 1230433 1753969 := bstep (se 2 (by rfl) ⟨657738, by rfl⟩ : syracuseStep 1753969 = 1315477) B1315477
theorem B1385347 : Blo 1230433 1385347 := bstep (se 1 (by rfl) ⟨1039010, by rfl⟩ : syracuseStep 1385347 = 2078021) B2078021
theorem B12633029 : Blo 1230433 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B1754065 : Blo 1230433 1754065 := bstep (se 2 (by rfl) ⟨657774, by rfl⟩ : syracuseStep 1754065 = 1315549) B1315549
theorem B2999281 : Blo 1230433 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B4154381 : Blo 1230433 4154381 := bstep (se 3 (by rfl) ⟨778946, by rfl⟩ : syracuseStep 4154381 = 1557893) B1557893
theorem B1385491 : Blo 1230433 1385491 := bstep (se 1 (by rfl) ⟨1039118, by rfl⟩ : syracuseStep 1385491 = 2078237) B2078237
theorem B2958371 : Blo 1230433 2958371 := bstep (se 1 (by rfl) ⟨2218778, by rfl⟩ : syracuseStep 2958371 = 4437557) B4437557
theorem B4154435 : Blo 1230433 4154435 := bstep (se 1 (by rfl) ⟨3115826, by rfl⟩ : syracuseStep 4154435 = 6231653) B6231653
theorem B2770001 : Blo 1230433 2770001 := bstep (se 2 (by rfl) ⟨1038750, by rfl⟩ : syracuseStep 2770001 = 2077501) B2077501
theorem B2770019 : Blo 1230433 2770019 := bstep (se 1 (by rfl) ⟨2077514, by rfl⟩ : syracuseStep 2770019 = 4155029) B4155029
theorem B9348209 : Blo 1230433 9348209 := bstep (se 2 (by rfl) ⟨3505578, by rfl⟩ : syracuseStep 9348209 = 7011157) B7011157
theorem B12002417 : Blo 1230433 12002417 := bstep (se 2 (by rfl) ⟨4500906, by rfl⟩ : syracuseStep 12002417 = 9001813) B9001813
theorem B1385635 : Blo 1230433 1385635 := bstep (se 1 (by rfl) ⟨1039226, by rfl⟩ : syracuseStep 1385635 = 2078453) B2078453
theorem B7013573 : Blo 1230433 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B2958545 : Blo 1230433 2958545 := bstep (se 2 (by rfl) ⟨1109454, by rfl⟩ : syracuseStep 2958545 = 2218909) B2218909
theorem B1557731 : Blo 1230433 1557731 := bstep (se 1 (by rfl) ⟨1168298, by rfl⟩ : syracuseStep 1557731 = 2336597) B2336597
theorem B2958563 : Blo 1230433 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B2336035 : Blo 1230433 2336035 := bstep (se 1 (by rfl) ⟨1752026, by rfl⟩ : syracuseStep 2336035 = 3504053) B3504053
theorem B1385779 : Blo 1230433 1385779 := bstep (se 1 (by rfl) ⟨1039334, by rfl⟩ : syracuseStep 1385779 = 2078669) B2078669
theorem B4154705 : Blo 1230433 4154705 := bstep (se 2 (by rfl) ⟨1558014, by rfl⟩ : syracuseStep 4154705 = 3116029) B3116029
theorem B2770289 : Blo 1230433 2770289 := bstep (se 2 (by rfl) ⟨1038858, by rfl⟩ : syracuseStep 2770289 = 2077717) B2077717
theorem B2770307 : Blo 1230433 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B3745187 : Blo 1230433 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B1754561 : Blo 1230433 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B2336195 : Blo 1230433 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B1385923 : Blo 1230433 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B4679117 : Blo 1230433 4679117 := bstep (se 3 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 4679117 = 1754669) B1754669
theorem B33326645 : Blo 1230433 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B1386067 : Blo 1230433 1386067 := bstep (se 1 (by rfl) ⟨1039550, by rfl⟩ : syracuseStep 1386067 = 2079101) B2079101
theorem B1230435 : Blo 1230433 1230435 := bstep (se 1 (by rfl) ⟨922826, by rfl⟩ : syracuseStep 1230435 = 1845653) B1845653
theorem B1230451 : Blo 1230433 1230451 := bstep (se 1 (by rfl) ⟨922838, by rfl⟩ : syracuseStep 1230451 = 1845677) B1845677
theorem B1230467 : Blo 1230433 1230467 := bstep (se 1 (by rfl) ⟨922850, by rfl⟩ : syracuseStep 1230467 = 1845701) B1845701
theorem B2770577 : Blo 1230433 2770577 := bstep (se 2 (by rfl) ⟨1038966, by rfl⟩ : syracuseStep 2770577 = 2077933) B2077933
theorem B1230483 : Blo 1230433 1230483 := bstep (se 1 (by rfl) ⟨922862, by rfl⟩ : syracuseStep 1230483 = 1845725) B1845725
theorem B3507857 : Blo 1230433 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B1230499 : Blo 1230433 1230499 := bstep (se 1 (by rfl) ⟨922874, by rfl⟩ : syracuseStep 1230499 = 1845749) B1845749
theorem B2770595 : Blo 1230433 2770595 := bstep (se 1 (by rfl) ⟨2077946, by rfl⟩ : syracuseStep 2770595 = 4155893) B4155893
theorem B1230515 : Blo 1230433 1230515 := bstep (se 1 (by rfl) ⟨922886, by rfl⟩ : syracuseStep 1230515 = 1845773) B1845773
theorem B1230531 : Blo 1230433 1230531 := bstep (se 1 (by rfl) ⟨922898, by rfl⟩ : syracuseStep 1230531 = 1845797) B1845797
theorem B1230547 : Blo 1230433 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B1230563 : Blo 1230433 1230563 := bstep (se 1 (by rfl) ⟨922922, by rfl⟩ : syracuseStep 1230563 = 1845845) B1845845
theorem B1386211 : Blo 1230433 1386211 := bstep (se 1 (by rfl) ⟨1039658, by rfl⟩ : syracuseStep 1386211 = 2079317) B2079317
theorem B1230579 : Blo 1230433 1230579 := bstep (se 1 (by rfl) ⟨922934, by rfl⟩ : syracuseStep 1230579 = 1845869) B1845869
theorem B1230595 : Blo 1230433 1230595 := bstep (se 1 (by rfl) ⟨922946, by rfl⟩ : syracuseStep 1230595 = 1845893) B1845893
theorem B1230611 : Blo 1230433 1230611 := bstep (se 1 (by rfl) ⟨922958, by rfl⟩ : syracuseStep 1230611 = 1845917) B1845917
theorem B1230627 : Blo 1230433 1230627 := bstep (se 1 (by rfl) ⟨922970, by rfl⟩ : syracuseStep 1230627 = 1845941) B1845941
theorem B1230643 : Blo 1230433 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B1230659 : Blo 1230433 1230659 := bstep (se 1 (by rfl) ⟨922994, by rfl⟩ : syracuseStep 1230659 = 1845989) B1845989
theorem B1230675 : Blo 1230433 1230675 := bstep (se 1 (by rfl) ⟨923006, by rfl⟩ : syracuseStep 1230675 = 1846013) B1846013
theorem B1230691 : Blo 1230433 1230691 := bstep (se 1 (by rfl) ⟨923018, by rfl⟩ : syracuseStep 1230691 = 1846037) B1846037
theorem B4155245 : Blo 1230433 4155245 := bstep (se 3 (by rfl) ⟨779108, by rfl⟩ : syracuseStep 4155245 = 1558217) B1558217
theorem B1230707 : Blo 1230433 1230707 := bstep (se 1 (by rfl) ⟨923030, by rfl⟩ : syracuseStep 1230707 = 1846061) B1846061
theorem B1386355 : Blo 1230433 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B1230723 : Blo 1230433 1230723 := bstep (se 1 (by rfl) ⟨923042, by rfl⟩ : syracuseStep 1230723 = 1846085) B1846085
theorem B1230739 : Blo 1230433 1230739 := bstep (se 1 (by rfl) ⟨923054, by rfl⟩ : syracuseStep 1230739 = 1846109) B1846109
theorem B1230755 : Blo 1230433 1230755 := bstep (se 1 (by rfl) ⟨923066, by rfl⟩ : syracuseStep 1230755 = 1846133) B1846133
theorem B4155299 : Blo 1230433 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B1558435 : Blo 1230433 1558435 := bstep (se 1 (by rfl) ⟨1168826, by rfl⟩ : syracuseStep 1558435 = 2337653) B2337653
theorem B2770865 : Blo 1230433 2770865 := bstep (se 2 (by rfl) ⟨1039074, by rfl⟩ : syracuseStep 2770865 = 2078149) B2078149
theorem B1230771 : Blo 1230433 1230771 := bstep (se 1 (by rfl) ⟨923078, by rfl⟩ : syracuseStep 1230771 = 1846157) B1846157
theorem B1230787 : Blo 1230433 1230787 := bstep (se 1 (by rfl) ⟨923090, by rfl⟩ : syracuseStep 1230787 = 1846181) B1846181
theorem B2770883 : Blo 1230433 2770883 := bstep (se 1 (by rfl) ⟨2078162, by rfl⟩ : syracuseStep 2770883 = 4156325) B4156325
theorem B1230803 : Blo 1230433 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1230819 : Blo 1230433 1230819 := bstep (se 1 (by rfl) ⟨923114, by rfl⟩ : syracuseStep 1230819 = 1846229) B1846229
theorem B1230835 : Blo 1230433 1230835 := bstep (se 1 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 1230835 = 1846253) B1846253
theorem B1230851 : Blo 1230433 1230851 := bstep (se 1 (by rfl) ⟨923138, by rfl⟩ : syracuseStep 1230851 = 1846277) B1846277
theorem B1558531 : Blo 1230433 1558531 := bstep (se 1 (by rfl) ⟨1168898, by rfl⟩ : syracuseStep 1558531 = 2337797) B2337797
theorem B1230867 : Blo 1230433 1230867 := bstep (se 1 (by rfl) ⟨923150, by rfl⟩ : syracuseStep 1230867 = 1846301) B1846301
theorem B1230883 : Blo 1230433 1230883 := bstep (se 1 (by rfl) ⟨923162, by rfl⟩ : syracuseStep 1230883 = 1846325) B1846325
theorem B6408227 : Blo 1230433 6408227 := bstep (se 1 (by rfl) ⟨4806170, by rfl⟩ : syracuseStep 6408227 = 9612341) B9612341
theorem B3115057 : Blo 1230433 3115057 := bstep (se 2 (by rfl) ⟨1168146, by rfl⟩ : syracuseStep 3115057 = 2336293) B2336293
theorem B1230899 : Blo 1230433 1230899 := bstep (se 1 (by rfl) ⟨923174, by rfl⟩ : syracuseStep 1230899 = 1846349) B1846349
theorem B1230915 : Blo 1230433 1230915 := bstep (se 1 (by rfl) ⟨923186, by rfl⟩ : syracuseStep 1230915 = 1846373) B1846373
theorem B1230931 : Blo 1230433 1230931 := bstep (se 1 (by rfl) ⟨923198, by rfl⟩ : syracuseStep 1230931 = 1846397) B1846397
theorem B1230947 : Blo 1230433 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B1230963 : Blo 1230433 1230963 := bstep (se 1 (by rfl) ⟨923222, by rfl⟩ : syracuseStep 1230963 = 1846445) B1846445
theorem B1230979 : Blo 1230433 1230979 := bstep (se 1 (by rfl) ⟨923234, by rfl⟩ : syracuseStep 1230979 = 1846469) B1846469
theorem B1230995 : Blo 1230433 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B1231011 : Blo 1230433 1231011 := bstep (se 1 (by rfl) ⟨923258, by rfl⟩ : syracuseStep 1231011 = 1846517) B1846517
theorem B4155569 : Blo 1230433 4155569 := bstep (se 2 (by rfl) ⟨1558338, by rfl⟩ : syracuseStep 4155569 = 3116677) B3116677
theorem B1231027 : Blo 1230433 1231027 := bstep (se 1 (by rfl) ⟨923270, by rfl⟩ : syracuseStep 1231027 = 1846541) B1846541
theorem B1231043 : Blo 1230433 1231043 := bstep (se 1 (by rfl) ⟨923282, by rfl⟩ : syracuseStep 1231043 = 1846565) B1846565
theorem B7891141 : Blo 1230433 7891141 := bstep (se 4 (by rfl) ⟨739794, by rfl⟩ : syracuseStep 7891141 = 1479589) B1479589
theorem B2771153 : Blo 1230433 2771153 := bstep (se 2 (by rfl) ⟨1039182, by rfl⟩ : syracuseStep 2771153 = 2078365) B2078365
theorem B1231059 : Blo 1230433 1231059 := bstep (se 1 (by rfl) ⟨923294, by rfl⟩ : syracuseStep 1231059 = 1846589) B1846589
theorem B1231075 : Blo 1230433 1231075 := bstep (se 1 (by rfl) ⟨923306, by rfl⟩ : syracuseStep 1231075 = 1846613) B1846613
theorem B2771171 : Blo 1230433 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B1231091 : Blo 1230433 1231091 := bstep (se 1 (by rfl) ⟨923318, by rfl⟩ : syracuseStep 1231091 = 1846637) B1846637
theorem B1231107 : Blo 1230433 1231107 := bstep (se 1 (by rfl) ⟨923330, by rfl⟩ : syracuseStep 1231107 = 1846661) B1846661
theorem B2631953 : Blo 1230433 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B1231123 : Blo 1230433 1231123 := bstep (se 1 (by rfl) ⟨923342, by rfl⟩ : syracuseStep 1231123 = 1846685) B1846685
theorem B1231139 : Blo 1230433 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B3942701 : Blo 1230433 3942701 := bstep (se 3 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 3942701 = 1478513) B1478513
theorem B1231155 : Blo 1230433 1231155 := bstep (se 1 (by rfl) ⟨923366, by rfl⟩ : syracuseStep 1231155 = 1846733) B1846733
theorem B3115331 : Blo 1230433 3115331 := bstep (se 1 (by rfl) ⟨2336498, by rfl⟩ : syracuseStep 3115331 = 4672997) B4672997
theorem B1231171 : Blo 1230433 1231171 := bstep (se 1 (by rfl) ⟨923378, by rfl⟩ : syracuseStep 1231171 = 1846757) B1846757
theorem B1231187 : Blo 1230433 1231187 := bstep (se 1 (by rfl) ⟨923390, by rfl⟩ : syracuseStep 1231187 = 1846781) B1846781
theorem B1231203 : Blo 1230433 1231203 := bstep (se 1 (by rfl) ⟨923402, by rfl⟩ : syracuseStep 1231203 = 1846805) B1846805
theorem B4671857 : Blo 1230433 4671857 := bstep (se 2 (by rfl) ⟨1751946, by rfl⟩ : syracuseStep 4671857 = 3503893) B3503893
theorem B1231219 : Blo 1230433 1231219 := bstep (se 1 (by rfl) ⟨923414, by rfl⟩ : syracuseStep 1231219 = 1846829) B1846829
theorem B1231235 : Blo 1230433 1231235 := bstep (se 1 (by rfl) ⟨923426, by rfl⟩ : syracuseStep 1231235 = 1846853) B1846853
theorem B1231251 : Blo 1230433 1231251 := bstep (se 1 (by rfl) ⟨923438, by rfl⟩ : syracuseStep 1231251 = 1846877) B1846877
theorem B1845665 : Blo 1230433 1845665 := bstep (se 2 (by rfl) ⟨692124, by rfl⟩ : syracuseStep 1845665 = 1384249) B1384249
theorem B1231267 : Blo 1230433 1231267 := bstep (se 1 (by rfl) ⟨923450, by rfl⟩ : syracuseStep 1231267 = 1846901) B1846901
theorem B1845683 : Blo 1230433 1845683 := bstep (se 1 (by rfl) ⟨1384262, by rfl⟩ : syracuseStep 1845683 = 2768525) B2768525
theorem B1231283 : Blo 1230433 1231283 := bstep (se 1 (by rfl) ⟨923462, by rfl⟩ : syracuseStep 1231283 = 1846925) B1846925
theorem B1231299 : Blo 1230433 1231299 := bstep (se 1 (by rfl) ⟨923474, by rfl⟩ : syracuseStep 1231299 = 1846949) B1846949
theorem B1845713 : Blo 1230433 1845713 := bstep (se 2 (by rfl) ⟨692142, by rfl⟩ : syracuseStep 1845713 = 1384285) B1384285
theorem B1231315 : Blo 1230433 1231315 := bstep (se 1 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 1231315 = 1846973) B1846973
theorem B1845731 : Blo 1230433 1845731 := bstep (se 1 (by rfl) ⟨1384298, by rfl⟩ : syracuseStep 1845731 = 2768597) B2768597
theorem B1231331 : Blo 1230433 1231331 := bstep (se 1 (by rfl) ⟨923498, by rfl⟩ : syracuseStep 1231331 = 1846997) B1846997
theorem B2337265 : Blo 1230433 2337265 := bstep (se 2 (by rfl) ⟨876474, by rfl⟩ : syracuseStep 2337265 = 1752949) B1752949
theorem B8874481 : Blo 1230433 8874481 := bstep (se 2 (by rfl) ⟨3327930, by rfl⟩ : syracuseStep 8874481 = 6655861) B6655861
theorem B1231347 : Blo 1230433 1231347 := bstep (se 1 (by rfl) ⟨923510, by rfl⟩ : syracuseStep 1231347 = 1847021) B1847021
theorem B2771441 : Blo 1230433 2771441 := bstep (se 2 (by rfl) ⟨1039290, by rfl⟩ : syracuseStep 2771441 = 2078581) B2078581
theorem B1845761 : Blo 1230433 1845761 := bstep (se 2 (by rfl) ⟨692160, by rfl⟩ : syracuseStep 1845761 = 1384321) B1384321
theorem B3115523 : Blo 1230433 3115523 := bstep (se 1 (by rfl) ⟨2336642, by rfl⟩ : syracuseStep 3115523 = 4673285) B4673285
theorem B1231363 : Blo 1230433 1231363 := bstep (se 1 (by rfl) ⟨923522, by rfl⟩ : syracuseStep 1231363 = 1847045) B1847045
theorem B2771459 : Blo 1230433 2771459 := bstep (se 1 (by rfl) ⟨2078594, by rfl⟩ : syracuseStep 2771459 = 4157189) B4157189
theorem B3746321 : Blo 1230433 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B1845779 : Blo 1230433 1845779 := bstep (se 1 (by rfl) ⟨1384334, by rfl⟩ : syracuseStep 1845779 = 2768669) B2768669
theorem B1231379 : Blo 1230433 1231379 := bstep (se 1 (by rfl) ⟨923534, by rfl⟩ : syracuseStep 1231379 = 1847069) B1847069
theorem B1231395 : Blo 1230433 1231395 := bstep (se 1 (by rfl) ⟨923546, by rfl⟩ : syracuseStep 1231395 = 1847093) B1847093
theorem B1845809 : Blo 1230433 1845809 := bstep (se 2 (by rfl) ⟨692178, by rfl⟩ : syracuseStep 1845809 = 1384357) B1384357
theorem B1231411 : Blo 1230433 1231411 := bstep (se 1 (by rfl) ⟨923558, by rfl⟩ : syracuseStep 1231411 = 1847117) B1847117
theorem B1845827 : Blo 1230433 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B1231427 : Blo 1230433 1231427 := bstep (se 1 (by rfl) ⟨923570, by rfl⟩ : syracuseStep 1231427 = 1847141) B1847141
theorem B1231443 : Blo 1230433 1231443 := bstep (se 1 (by rfl) ⟨923582, by rfl⟩ : syracuseStep 1231443 = 1847165) B1847165
theorem B1845857 : Blo 1230433 1845857 := bstep (se 2 (by rfl) ⟨692196, by rfl⟩ : syracuseStep 1845857 = 1384393) B1384393
theorem B4737635 : Blo 1230433 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B1231459 : Blo 1230433 1231459 := bstep (se 1 (by rfl) ⟨923594, by rfl⟩ : syracuseStep 1231459 = 1847189) B1847189
theorem B1845875 : Blo 1230433 1845875 := bstep (se 1 (by rfl) ⟨1384406, by rfl⟩ : syracuseStep 1845875 = 2768813) B2768813
theorem B1231475 : Blo 1230433 1231475 := bstep (se 1 (by rfl) ⟨923606, by rfl⟩ : syracuseStep 1231475 = 1847213) B1847213
theorem B1231491 : Blo 1230433 1231491 := bstep (se 1 (by rfl) ⟨923618, by rfl⟩ : syracuseStep 1231491 = 1847237) B1847237
theorem B1845905 : Blo 1230433 1845905 := bstep (se 2 (by rfl) ⟨692214, by rfl⟩ : syracuseStep 1845905 = 1384429) B1384429
theorem B1231507 : Blo 1230433 1231507 := bstep (se 1 (by rfl) ⟨923630, by rfl⟩ : syracuseStep 1231507 = 1847261) B1847261
theorem B1845923 : Blo 1230433 1845923 := bstep (se 1 (by rfl) ⟨1384442, by rfl⟩ : syracuseStep 1845923 = 2768885) B2768885
theorem B1231523 : Blo 1230433 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B1231539 : Blo 1230433 1231539 := bstep (se 1 (by rfl) ⟨923654, by rfl⟩ : syracuseStep 1231539 = 1847309) B1847309
theorem B1845953 : Blo 1230433 1845953 := bstep (se 2 (by rfl) ⟨692232, by rfl⟩ : syracuseStep 1845953 = 1384465) B1384465
theorem B1231555 : Blo 1230433 1231555 := bstep (se 1 (by rfl) ⟨923666, by rfl⟩ : syracuseStep 1231555 = 1847333) B1847333
theorem B4156109 : Blo 1230433 4156109 := bstep (se 3 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 4156109 = 1558541) B1558541
theorem B1845971 : Blo 1230433 1845971 := bstep (se 1 (by rfl) ⟨1384478, by rfl⟩ : syracuseStep 1845971 = 2768957) B2768957
theorem B1231571 : Blo 1230433 1231571 := bstep (se 1 (by rfl) ⟨923678, by rfl⟩ : syracuseStep 1231571 = 1847357) B1847357
theorem B1231587 : Blo 1230433 1231587 := bstep (se 1 (by rfl) ⟨923690, by rfl⟩ : syracuseStep 1231587 = 1847381) B1847381
theorem B1846001 : Blo 1230433 1846001 := bstep (se 2 (by rfl) ⟨692250, by rfl⟩ : syracuseStep 1846001 = 1384501) B1384501
theorem B5999345 : Blo 1230433 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B1231603 : Blo 1230433 1231603 := bstep (se 1 (by rfl) ⟨923702, by rfl⟩ : syracuseStep 1231603 = 1847405) B1847405
theorem B1846019 : Blo 1230433 1846019 := bstep (se 1 (by rfl) ⟨1384514, by rfl⟩ : syracuseStep 1846019 = 2769029) B2769029
theorem B4156163 : Blo 1230433 4156163 := bstep (se 1 (by rfl) ⟨3117122, by rfl⟩ : syracuseStep 4156163 = 6234245) B6234245
theorem B1231619 : Blo 1230433 1231619 := bstep (se 1 (by rfl) ⟨923714, by rfl⟩ : syracuseStep 1231619 = 1847429) B1847429
theorem B2771729 : Blo 1230433 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B1231635 : Blo 1230433 1231635 := bstep (se 1 (by rfl) ⟨923726, by rfl⟩ : syracuseStep 1231635 = 1847453) B1847453
theorem B59894549 : Blo 1230433 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B1846049 : Blo 1230433 1846049 := bstep (se 2 (by rfl) ⟨692268, by rfl⟩ : syracuseStep 1846049 = 1384537) B1384537
theorem B1231651 : Blo 1230433 1231651 := bstep (se 1 (by rfl) ⟨923738, by rfl⟩ : syracuseStep 1231651 = 1847477) B1847477
theorem B2771747 : Blo 1230433 2771747 := bstep (se 1 (by rfl) ⟨2078810, by rfl⟩ : syracuseStep 2771747 = 4157621) B4157621
theorem B1846067 : Blo 1230433 1846067 := bstep (se 1 (by rfl) ⟨1384550, by rfl⟩ : syracuseStep 1846067 = 2769101) B2769101
theorem B1231667 : Blo 1230433 1231667 := bstep (se 1 (by rfl) ⟨923750, by rfl⟩ : syracuseStep 1231667 = 1847501) B1847501
theorem B1231683 : Blo 1230433 1231683 := bstep (se 1 (by rfl) ⟨923762, by rfl⟩ : syracuseStep 1231683 = 1847525) B1847525
theorem B1846097 : Blo 1230433 1846097 := bstep (se 2 (by rfl) ⟨692286, by rfl⟩ : syracuseStep 1846097 = 1384573) B1384573
theorem B1231699 : Blo 1230433 1231699 := bstep (se 1 (by rfl) ⟨923774, by rfl⟩ : syracuseStep 1231699 = 1847549) B1847549
theorem B1846115 : Blo 1230433 1846115 := bstep (se 1 (by rfl) ⟨1384586, by rfl⟩ : syracuseStep 1846115 = 2769173) B2769173
theorem B1231715 : Blo 1230433 1231715 := bstep (se 1 (by rfl) ⟨923786, by rfl⟩ : syracuseStep 1231715 = 1847573) B1847573
theorem B1231731 : Blo 1230433 1231731 := bstep (se 1 (by rfl) ⟨923798, by rfl⟩ : syracuseStep 1231731 = 1847597) B1847597
theorem B1846145 : Blo 1230433 1846145 := bstep (se 2 (by rfl) ⟨692304, by rfl⟩ : syracuseStep 1846145 = 1384609) B1384609
theorem B1231747 : Blo 1230433 1231747 := bstep (se 1 (by rfl) ⟨923810, by rfl⟩ : syracuseStep 1231747 = 1847621) B1847621
theorem B10259341 : Blo 1230433 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B1846163 : Blo 1230433 1846163 := bstep (se 1 (by rfl) ⟨1384622, by rfl⟩ : syracuseStep 1846163 = 2769245) B2769245
theorem B1231763 : Blo 1230433 1231763 := bstep (se 1 (by rfl) ⟨923822, by rfl⟩ : syracuseStep 1231763 = 1847645) B1847645
theorem B1231779 : Blo 1230433 1231779 := bstep (se 1 (by rfl) ⟨923834, by rfl⟩ : syracuseStep 1231779 = 1847669) B1847669
theorem B1846193 : Blo 1230433 1846193 := bstep (se 2 (by rfl) ⟨692322, by rfl⟩ : syracuseStep 1846193 = 1384645) B1384645
theorem B1231795 : Blo 1230433 1231795 := bstep (se 1 (by rfl) ⟨923846, by rfl⟩ : syracuseStep 1231795 = 1847693) B1847693
theorem B1846211 : Blo 1230433 1846211 := bstep (se 1 (by rfl) ⟨1384658, by rfl⟩ : syracuseStep 1846211 = 2769317) B2769317
theorem B1231811 : Blo 1230433 1231811 := bstep (se 1 (by rfl) ⟨923858, by rfl⟩ : syracuseStep 1231811 = 1847717) B1847717
theorem B1231827 : Blo 1230433 1231827 := bstep (se 1 (by rfl) ⟨923870, by rfl⟩ : syracuseStep 1231827 = 1847741) B1847741
theorem B1846241 : Blo 1230433 1846241 := bstep (se 2 (by rfl) ⟨692340, by rfl⟩ : syracuseStep 1846241 = 1384681) B1384681
theorem B1231843 : Blo 1230433 1231843 := bstep (se 1 (by rfl) ⟨923882, by rfl⟩ : syracuseStep 1231843 = 1847765) B1847765
theorem B1846259 : Blo 1230433 1846259 := bstep (se 1 (by rfl) ⟨1384694, by rfl⟩ : syracuseStep 1846259 = 2769389) B2769389
theorem B1231859 : Blo 1230433 1231859 := bstep (se 1 (by rfl) ⟨923894, by rfl⟩ : syracuseStep 1231859 = 1847789) B1847789
theorem B1231875 : Blo 1230433 1231875 := bstep (se 1 (by rfl) ⟨923906, by rfl⟩ : syracuseStep 1231875 = 1847813) B1847813
theorem B4672525 : Blo 1230433 4672525 := bstep (se 3 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 4672525 = 1752197) B1752197
theorem B1846289 : Blo 1230433 1846289 := bstep (se 2 (by rfl) ⟨692358, by rfl⟩ : syracuseStep 1846289 = 1384717) B1384717
theorem B4156433 : Blo 1230433 4156433 := bstep (se 2 (by rfl) ⟨1558662, by rfl⟩ : syracuseStep 4156433 = 3117325) B3117325
theorem B1231891 : Blo 1230433 1231891 := bstep (se 1 (by rfl) ⟨923918, by rfl⟩ : syracuseStep 1231891 = 1847837) B1847837
theorem B1846307 : Blo 1230433 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B1231907 : Blo 1230433 1231907 := bstep (se 1 (by rfl) ⟨923930, by rfl⟩ : syracuseStep 1231907 = 1847861) B1847861
theorem B2772017 : Blo 1230433 2772017 := bstep (se 2 (by rfl) ⟨1039506, by rfl⟩ : syracuseStep 2772017 = 2079013) B2079013
theorem B1231923 : Blo 1230433 1231923 := bstep (se 1 (by rfl) ⟨923942, by rfl⟩ : syracuseStep 1231923 = 1847885) B1847885
theorem B13495349 : Blo 1230433 13495349 := bstep (se 5 (by rfl) ⟨632594, by rfl⟩ : syracuseStep 13495349 = 1265189) B1265189
theorem B1846337 : Blo 1230433 1846337 := bstep (se 2 (by rfl) ⟨692376, by rfl⟩ : syracuseStep 1846337 = 1384753) B1384753
theorem B1231939 : Blo 1230433 1231939 := bstep (se 1 (by rfl) ⟨923954, by rfl⟩ : syracuseStep 1231939 = 1847909) B1847909
theorem B2772035 : Blo 1230433 2772035 := bstep (se 1 (by rfl) ⟨2079026, by rfl⟩ : syracuseStep 2772035 = 4158053) B4158053
theorem B3509315 : Blo 1230433 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B1846355 : Blo 1230433 1846355 := bstep (se 1 (by rfl) ⟨1384766, by rfl⟩ : syracuseStep 1846355 = 2769533) B2769533
theorem B1231955 : Blo 1230433 1231955 := bstep (se 1 (by rfl) ⟨923966, by rfl⟩ : syracuseStep 1231955 = 1847933) B1847933
theorem B1248355 : Blo 1230433 1248355 := bstep (se 1 (by rfl) ⟨936266, by rfl⟩ : syracuseStep 1248355 = 1872533) B1872533
theorem B1231971 : Blo 1230433 1231971 := bstep (se 1 (by rfl) ⟨923978, by rfl⟩ : syracuseStep 1231971 = 1847957) B1847957
theorem B1846385 : Blo 1230433 1846385 := bstep (se 2 (by rfl) ⟨692394, by rfl⟩ : syracuseStep 1846385 = 1384789) B1384789
theorem B1231987 : Blo 1230433 1231987 := bstep (se 1 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 1231987 = 1847981) B1847981
theorem B1846403 : Blo 1230433 1846403 := bstep (se 1 (by rfl) ⟨1384802, by rfl⟩ : syracuseStep 1846403 = 2769605) B2769605
theorem B1232003 : Blo 1230433 1232003 := bstep (se 1 (by rfl) ⟨924002, by rfl⟩ : syracuseStep 1232003 = 1848005) B1848005
theorem B1232019 : Blo 1230433 1232019 := bstep (se 1 (by rfl) ⟨924014, by rfl⟩ : syracuseStep 1232019 = 1848029) B1848029
theorem B1846433 : Blo 1230433 1846433 := bstep (se 2 (by rfl) ⟨692412, by rfl⟩ : syracuseStep 1846433 = 1384825) B1384825
theorem B1232035 : Blo 1230433 1232035 := bstep (se 1 (by rfl) ⟨924026, by rfl⟩ : syracuseStep 1232035 = 1848053) B1848053
theorem B1846451 : Blo 1230433 1846451 := bstep (se 1 (by rfl) ⟨1384838, by rfl⟩ : syracuseStep 1846451 = 2769677) B2769677
theorem B1232051 : Blo 1230433 1232051 := bstep (se 1 (by rfl) ⟨924038, by rfl⟩ : syracuseStep 1232051 = 1848077) B1848077
theorem B1559731 : Blo 1230433 1559731 := bstep (se 1 (by rfl) ⟨1169798, by rfl⟩ : syracuseStep 1559731 = 2339597) B2339597
theorem B1232067 : Blo 1230433 1232067 := bstep (se 1 (by rfl) ⟨924050, by rfl⟩ : syracuseStep 1232067 = 1848101) B1848101
theorem B14036165 : Blo 1230433 14036165 := bstep (se 4 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 14036165 = 2631781) B2631781
theorem B1846481 : Blo 1230433 1846481 := bstep (se 2 (by rfl) ⟨692430, by rfl⟩ : syracuseStep 1846481 = 1384861) B1384861
theorem B1232083 : Blo 1230433 1232083 := bstep (se 1 (by rfl) ⟨924062, by rfl⟩ : syracuseStep 1232083 = 1848125) B1848125
theorem B1846499 : Blo 1230433 1846499 := bstep (se 1 (by rfl) ⟨1384874, by rfl⟩ : syracuseStep 1846499 = 2769749) B2769749
theorem B1232099 : Blo 1230433 1232099 := bstep (se 1 (by rfl) ⟨924074, by rfl⟩ : syracuseStep 1232099 = 1848149) B1848149
theorem B1232115 : Blo 1230433 1232115 := bstep (se 1 (by rfl) ⟨924086, by rfl⟩ : syracuseStep 1232115 = 1848173) B1848173
theorem B1846529 : Blo 1230433 1846529 := bstep (se 2 (by rfl) ⟨692448, by rfl⟩ : syracuseStep 1846529 = 1384897) B1384897
theorem B1232131 : Blo 1230433 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B5614861 : Blo 1230433 5614861 := bstep (se 3 (by rfl) ⟨1052786, by rfl⟩ : syracuseStep 5614861 = 2105573) B2105573
theorem B1846547 : Blo 1230433 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B1232147 : Blo 1230433 1232147 := bstep (se 1 (by rfl) ⟨924110, by rfl⟩ : syracuseStep 1232147 = 1848221) B1848221
theorem B7884067 : Blo 1230433 7884067 := bstep (se 1 (by rfl) ⟨5913050, by rfl⟩ : syracuseStep 7884067 = 11826101) B11826101
theorem B1232163 : Blo 1230433 1232163 := bstep (se 1 (by rfl) ⟨924122, by rfl⟩ : syracuseStep 1232163 = 1848245) B1848245
theorem B1846577 : Blo 1230433 1846577 := bstep (se 2 (by rfl) ⟨692466, by rfl⟩ : syracuseStep 1846577 = 1384933) B1384933
theorem B5262641 : Blo 1230433 5262641 := bstep (se 2 (by rfl) ⟨1973490, by rfl⟩ : syracuseStep 5262641 = 3946981) B3946981
theorem B1232179 : Blo 1230433 1232179 := bstep (se 1 (by rfl) ⟨924134, by rfl⟩ : syracuseStep 1232179 = 1848269) B1848269
theorem B1846595 : Blo 1230433 1846595 := bstep (se 1 (by rfl) ⟨1384946, by rfl⟩ : syracuseStep 1846595 = 2769893) B2769893
theorem B1232195 : Blo 1230433 1232195 := bstep (se 1 (by rfl) ⟨924146, by rfl⟩ : syracuseStep 1232195 = 1848293) B1848293
theorem B2772305 : Blo 1230433 2772305 := bstep (se 2 (by rfl) ⟨1039614, by rfl⟩ : syracuseStep 2772305 = 2079229) B2079229
theorem B1232211 : Blo 1230433 1232211 := bstep (se 1 (by rfl) ⟨924158, by rfl⟩ : syracuseStep 1232211 = 1848317) B1848317
theorem B1846625 : Blo 1230433 1846625 := bstep (se 2 (by rfl) ⟨692484, by rfl⟩ : syracuseStep 1846625 = 1384969) B1384969
theorem B2772323 : Blo 1230433 2772323 := bstep (se 1 (by rfl) ⟨2079242, by rfl⟩ : syracuseStep 2772323 = 4158485) B4158485
theorem B1232227 : Blo 1230433 1232227 := bstep (se 1 (by rfl) ⟨924170, by rfl⟩ : syracuseStep 1232227 = 1848341) B1848341
theorem B1846643 : Blo 1230433 1846643 := bstep (se 1 (by rfl) ⟨1384982, by rfl⟩ : syracuseStep 1846643 = 2769965) B2769965
theorem B1232243 : Blo 1230433 1232243 := bstep (se 1 (by rfl) ⟨924182, by rfl⟩ : syracuseStep 1232243 = 1848365) B1848365
theorem B1232259 : Blo 1230433 1232259 := bstep (se 1 (by rfl) ⟨924194, by rfl⟩ : syracuseStep 1232259 = 1848389) B1848389
theorem B1846673 : Blo 1230433 1846673 := bstep (se 2 (by rfl) ⟨692502, by rfl⟩ : syracuseStep 1846673 = 1385005) B1385005
theorem B1232275 : Blo 1230433 1232275 := bstep (se 1 (by rfl) ⟨924206, by rfl⟩ : syracuseStep 1232275 = 1848413) B1848413
theorem B1871267 : Blo 1230433 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B1846691 : Blo 1230433 1846691 := bstep (se 1 (by rfl) ⟨1385018, by rfl⟩ : syracuseStep 1846691 = 2770037) B2770037
theorem B1232291 : Blo 1230433 1232291 := bstep (se 1 (by rfl) ⟨924218, by rfl⟩ : syracuseStep 1232291 = 1848437) B1848437
theorem B3116465 : Blo 1230433 3116465 := bstep (se 2 (by rfl) ⟨1168674, by rfl⟩ : syracuseStep 3116465 = 2337349) B2337349
theorem B1232307 : Blo 1230433 1232307 := bstep (se 1 (by rfl) ⟨924230, by rfl⟩ : syracuseStep 1232307 = 1848461) B1848461
theorem B1846721 : Blo 1230433 1846721 := bstep (se 2 (by rfl) ⟨692520, by rfl⟩ : syracuseStep 1846721 = 1385041) B1385041
theorem B1232323 : Blo 1230433 1232323 := bstep (se 1 (by rfl) ⟨924242, by rfl⟩ : syracuseStep 1232323 = 1848485) B1848485
theorem B1846739 : Blo 1230433 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1232339 : Blo 1230433 1232339 := bstep (se 1 (by rfl) ⟨924254, by rfl⟩ : syracuseStep 1232339 = 1848509) B1848509
theorem B3116515 : Blo 1230433 3116515 := bstep (se 1 (by rfl) ⟨2337386, by rfl⟩ : syracuseStep 3116515 = 4674773) B4674773
theorem B1232355 : Blo 1230433 1232355 := bstep (se 1 (by rfl) ⟨924266, by rfl⟩ : syracuseStep 1232355 = 1848533) B1848533
theorem B1846769 : Blo 1230433 1846769 := bstep (se 2 (by rfl) ⟨692538, by rfl⟩ : syracuseStep 1846769 = 1385077) B1385077
theorem B1232371 : Blo 1230433 1232371 := bstep (se 1 (by rfl) ⟨924278, by rfl⟩ : syracuseStep 1232371 = 1848557) B1848557
theorem B1846787 : Blo 1230433 1846787 := bstep (se 1 (by rfl) ⟨1385090, by rfl⟩ : syracuseStep 1846787 = 2770181) B2770181
theorem B1232387 : Blo 1230433 1232387 := bstep (se 1 (by rfl) ⟨924290, by rfl⟩ : syracuseStep 1232387 = 1848581) B1848581
theorem B4435469 : Blo 1230433 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B2338321 : Blo 1230433 2338321 := bstep (se 2 (by rfl) ⟨876870, by rfl⟩ : syracuseStep 2338321 = 1753741) B1753741
theorem B1232403 : Blo 1230433 1232403 := bstep (se 1 (by rfl) ⟨924302, by rfl⟩ : syracuseStep 1232403 = 1848605) B1848605
theorem B1846817 : Blo 1230433 1846817 := bstep (se 2 (by rfl) ⟨692556, by rfl⟩ : syracuseStep 1846817 = 1385113) B1385113
theorem B1232419 : Blo 1230433 1232419 := bstep (se 1 (by rfl) ⟨924314, by rfl⟩ : syracuseStep 1232419 = 1848629) B1848629
theorem B3943981 : Blo 1230433 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B4156973 : Blo 1230433 4156973 := bstep (se 3 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 4156973 = 1558865) B1558865
theorem B1846835 : Blo 1230433 1846835 := bstep (se 1 (by rfl) ⟨1385126, by rfl⟩ : syracuseStep 1846835 = 2770253) B2770253
theorem B1846865 : Blo 1230433 1846865 := bstep (se 2 (by rfl) ⟨692574, by rfl⟩ : syracuseStep 1846865 = 1385149) B1385149
theorem B1846883 : Blo 1230433 1846883 := bstep (se 1 (by rfl) ⟨1385162, by rfl⟩ : syracuseStep 1846883 = 2770325) B2770325
theorem B4157027 : Blo 1230433 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B3116657 : Blo 1230433 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B6237809 : Blo 1230433 6237809 := bstep (se 2 (by rfl) ⟨2339178, by rfl⟩ : syracuseStep 6237809 = 4678357) B4678357
theorem B2772593 : Blo 1230433 2772593 := bstep (se 2 (by rfl) ⟨1039722, by rfl⟩ : syracuseStep 2772593 = 2079445) B2079445
theorem B1846913 : Blo 1230433 1846913 := bstep (se 2 (by rfl) ⟨692592, by rfl⟩ : syracuseStep 1846913 = 1385185) B1385185
theorem B2772611 : Blo 1230433 2772611 := bstep (se 1 (by rfl) ⟨2079458, by rfl⟩ : syracuseStep 2772611 = 4158917) B4158917
theorem B1846931 : Blo 1230433 1846931 := bstep (se 1 (by rfl) ⟨1385198, by rfl⟩ : syracuseStep 1846931 = 2770397) B2770397
theorem B1846961 : Blo 1230433 1846961 := bstep (se 2 (by rfl) ⟨692610, by rfl⟩ : syracuseStep 1846961 = 1385221) B1385221
theorem B1846979 : Blo 1230433 1846979 := bstep (se 1 (by rfl) ⟨1385234, by rfl⟩ : syracuseStep 1846979 = 2770469) B2770469
theorem B6229709 : Blo 1230433 6229709 := bstep (se 3 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 6229709 = 2336141) B2336141
theorem B1847009 : Blo 1230433 1847009 := bstep (se 2 (by rfl) ⟨692628, by rfl⟩ : syracuseStep 1847009 = 1385257) B1385257
theorem B2076401 : Blo 1230433 2076401 := bstep (se 2 (by rfl) ⟨778650, by rfl⟩ : syracuseStep 2076401 = 1557301) B1557301
theorem B1871603 : Blo 1230433 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B1847027 : Blo 1230433 1847027 := bstep (se 1 (by rfl) ⟨1385270, by rfl⟩ : syracuseStep 1847027 = 2770541) B2770541
theorem B1871633 : Blo 1230433 1871633 := bstep (se 2 (by rfl) ⟨701862, by rfl⟩ : syracuseStep 1871633 = 1403725) B1403725
theorem B1847057 : Blo 1230433 1847057 := bstep (se 2 (by rfl) ⟨692646, by rfl⟩ : syracuseStep 1847057 = 1385293) B1385293
theorem B1404691 : Blo 1230433 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B4673315 : Blo 1230433 4673315 := bstep (se 1 (by rfl) ⟨3504986, by rfl⟩ : syracuseStep 4673315 = 7009973) B7009973
theorem B1847075 : Blo 1230433 1847075 := bstep (se 1 (by rfl) ⟨1385306, by rfl⟩ : syracuseStep 1847075 = 2770613) B2770613
theorem B13324085 : Blo 1230433 13324085 := bstep (se 5 (by rfl) ⟨624566, by rfl⟩ : syracuseStep 13324085 = 1249133) B1249133
theorem B1847105 : Blo 1230433 1847105 := bstep (se 2 (by rfl) ⟨692664, by rfl⟩ : syracuseStep 1847105 = 1385329) B1385329
theorem B1847123 : Blo 1230433 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B2076529 : Blo 1230433 2076529 := bstep (se 2 (by rfl) ⟨778698, by rfl⟩ : syracuseStep 2076529 = 1557397) B1557397
theorem B1847153 : Blo 1230433 1847153 := bstep (se 2 (by rfl) ⟨692682, by rfl⟩ : syracuseStep 1847153 = 1385365) B1385365
theorem B4157297 : Blo 1230433 4157297 := bstep (se 2 (by rfl) ⟨1558986, by rfl⟩ : syracuseStep 4157297 = 3117973) B3117973
theorem B1847171 : Blo 1230433 1847171 := bstep (se 1 (by rfl) ⟨1385378, by rfl⟩ : syracuseStep 1847171 = 2770757) B2770757
theorem B2772881 : Blo 1230433 2772881 := bstep (se 2 (by rfl) ⟨1039830, by rfl⟩ : syracuseStep 2772881 = 2079661) B2079661
theorem B2076563 : Blo 1230433 2076563 := bstep (se 1 (by rfl) ⟨1557422, by rfl⟩ : syracuseStep 2076563 = 3114845) B3114845
theorem B1847201 : Blo 1230433 1847201 := bstep (se 2 (by rfl) ⟨692700, by rfl⟩ : syracuseStep 1847201 = 1385401) B1385401
theorem B2338723 : Blo 1230433 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B2772899 : Blo 1230433 2772899 := bstep (se 1 (by rfl) ⟨2079674, by rfl⟩ : syracuseStep 2772899 = 4159349) B4159349
theorem B1847219 : Blo 1230433 1847219 := bstep (se 1 (by rfl) ⟨1385414, by rfl⟩ : syracuseStep 1847219 = 2770829) B2770829
theorem B1847249 : Blo 1230433 1847249 := bstep (se 2 (by rfl) ⟨692718, by rfl⟩ : syracuseStep 1847249 = 1385437) B1385437
theorem B2338769 : Blo 1230433 2338769 := bstep (se 2 (by rfl) ⟨877038, by rfl⟩ : syracuseStep 2338769 = 1754077) B1754077
theorem B1847267 : Blo 1230433 1847267 := bstep (se 1 (by rfl) ⟨1385450, by rfl⟩ : syracuseStep 1847267 = 2770901) B2770901
theorem B7008241 : Blo 1230433 7008241 := bstep (se 2 (by rfl) ⟨2628090, by rfl⟩ : syracuseStep 7008241 = 5256181) B5256181
theorem B1847297 : Blo 1230433 1847297 := bstep (se 2 (by rfl) ⟨692736, by rfl⟩ : syracuseStep 1847297 = 1385473) B1385473
theorem B1559027 : Blo 1230433 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B2076691 : Blo 1230433 2076691 := bstep (se 1 (by rfl) ⟨1557518, by rfl⟩ : syracuseStep 2076691 = 3115037) B3115037
theorem B1847315 : Blo 1230433 1847315 := bstep (se 1 (by rfl) ⟨1385486, by rfl⟩ : syracuseStep 1847315 = 2770973) B2770973
theorem B3944483 : Blo 1230433 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B2371619 : Blo 1230433 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B1847345 : Blo 1230433 1847345 := bstep (se 2 (by rfl) ⟨692754, by rfl⟩ : syracuseStep 1847345 = 1385509) B1385509
theorem B1314883 : Blo 1230433 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B1847363 : Blo 1230433 1847363 := bstep (se 1 (by rfl) ⟨1385522, by rfl⟩ : syracuseStep 1847363 = 2771045) B2771045
theorem B1847393 : Blo 1230433 1847393 := bstep (se 2 (by rfl) ⟨692772, by rfl⟩ : syracuseStep 1847393 = 1385545) B1385545
theorem B1847411 : Blo 1230433 1847411 := bstep (se 1 (by rfl) ⟨1385558, by rfl⟩ : syracuseStep 1847411 = 2771117) B2771117
theorem B1847441 : Blo 1230433 1847441 := bstep (se 2 (by rfl) ⟨692790, by rfl⟩ : syracuseStep 1847441 = 1385581) B1385581
theorem B2076833 : Blo 1230433 2076833 := bstep (se 2 (by rfl) ⟨778812, by rfl⟩ : syracuseStep 2076833 = 1557625) B1557625
theorem B1847459 : Blo 1230433 1847459 := bstep (se 1 (by rfl) ⟨1385594, by rfl⟩ : syracuseStep 1847459 = 2771189) B2771189
theorem B1847489 : Blo 1230433 1847489 := bstep (se 2 (by rfl) ⟨692808, by rfl⟩ : syracuseStep 1847489 = 1385617) B1385617
theorem B1847507 : Blo 1230433 1847507 := bstep (se 1 (by rfl) ⟨1385630, by rfl⟩ : syracuseStep 1847507 = 2771261) B2771261
theorem B1847537 : Blo 1230433 1847537 := bstep (se 2 (by rfl) ⟨692826, by rfl⟩ : syracuseStep 1847537 = 1385653) B1385653
theorem B2339057 : Blo 1230433 2339057 := bstep (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) B1754293
theorem B1847555 : Blo 1230433 1847555 := bstep (se 1 (by rfl) ⟨1385666, by rfl⟩ : syracuseStep 1847555 = 2771333) B2771333
theorem B2076961 : Blo 1230433 2076961 := bstep (se 2 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 2076961 = 1557721) B1557721
theorem B1847585 : Blo 1230433 1847585 := bstep (se 2 (by rfl) ⟨692844, by rfl⟩ : syracuseStep 1847585 = 1385689) B1385689
theorem B5132593 : Blo 1230433 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1847603 : Blo 1230433 1847603 := bstep (se 1 (by rfl) ⟨1385702, by rfl⟩ : syracuseStep 1847603 = 2771405) B2771405
theorem B2076995 : Blo 1230433 2076995 := bstep (se 1 (by rfl) ⟨1557746, by rfl⟩ : syracuseStep 2076995 = 3115493) B3115493
theorem B9990469 : Blo 1230433 9990469 := bstep (se 4 (by rfl) ⟨936606, by rfl⟩ : syracuseStep 9990469 = 1873213) B1873213
theorem B1847633 : Blo 1230433 1847633 := bstep (se 2 (by rfl) ⟨692862, by rfl⟩ : syracuseStep 1847633 = 1385725) B1385725
theorem B1847651 : Blo 1230433 1847651 := bstep (se 1 (by rfl) ⟨1385738, by rfl⟩ : syracuseStep 1847651 = 2771477) B2771477
theorem B1847681 : Blo 1230433 1847681 := bstep (se 2 (by rfl) ⟨692880, by rfl⟩ : syracuseStep 1847681 = 1385761) B1385761
theorem B4157837 : Blo 1230433 4157837 := bstep (se 3 (by rfl) ⟨779594, by rfl⟩ : syracuseStep 4157837 = 1559189) B1559189
theorem B31584653 : Blo 1230433 31584653 := bstep (se 3 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 31584653 = 11844245) B11844245
theorem B1847699 : Blo 1230433 1847699 := bstep (se 1 (by rfl) ⟨1385774, by rfl⟩ : syracuseStep 1847699 = 2771549) B2771549
theorem B4673969 : Blo 1230433 4673969 := bstep (se 2 (by rfl) ⟨1752738, by rfl⟩ : syracuseStep 4673969 = 3505477) B3505477
theorem B1847729 : Blo 1230433 1847729 := bstep (se 2 (by rfl) ⟨692898, by rfl⟩ : syracuseStep 1847729 = 1385797) B1385797
theorem B2077123 : Blo 1230433 2077123 := bstep (se 1 (by rfl) ⟨1557842, by rfl⟩ : syracuseStep 2077123 = 3115685) B3115685
theorem B1847747 : Blo 1230433 1847747 := bstep (se 1 (by rfl) ⟨1385810, by rfl⟩ : syracuseStep 1847747 = 2771621) B2771621
theorem B4157891 : Blo 1230433 4157891 := bstep (se 1 (by rfl) ⟨3118418, by rfl⟩ : syracuseStep 4157891 = 6236837) B6236837
theorem B1847777 : Blo 1230433 1847777 := bstep (se 2 (by rfl) ⟨692916, by rfl⟩ : syracuseStep 1847777 = 1385833) B1385833
theorem B1847795 : Blo 1230433 1847795 := bstep (se 1 (by rfl) ⟨1385846, by rfl⟩ : syracuseStep 1847795 = 2771693) B2771693
theorem B1847825 : Blo 1230433 1847825 := bstep (se 2 (by rfl) ⟨692934, by rfl⟩ : syracuseStep 1847825 = 1385869) B1385869
theorem B3248657 : Blo 1230433 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B1847843 : Blo 1230433 1847843 := bstep (se 1 (by rfl) ⟨1385882, by rfl⟩ : syracuseStep 1847843 = 2771765) B2771765
theorem B1847873 : Blo 1230433 1847873 := bstep (se 2 (by rfl) ⟨692952, by rfl⟩ : syracuseStep 1847873 = 1385905) B1385905
theorem B2077265 : Blo 1230433 2077265 := bstep (se 2 (by rfl) ⟨778974, by rfl⟩ : syracuseStep 2077265 = 1557949) B1557949
theorem B3117649 : Blo 1230433 3117649 := bstep (se 2 (by rfl) ⟨1169118, by rfl⟩ : syracuseStep 3117649 = 2338237) B2338237
theorem B1847891 : Blo 1230433 1847891 := bstep (se 1 (by rfl) ⟨1385918, by rfl⟩ : syracuseStep 1847891 = 2771837) B2771837
theorem B1872497 : Blo 1230433 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B1847921 : Blo 1230433 1847921 := bstep (se 2 (by rfl) ⟨692970, by rfl⟩ : syracuseStep 1847921 = 1385941) B1385941
theorem B1847939 : Blo 1230433 1847939 := bstep (se 1 (by rfl) ⟨1385954, by rfl⟩ : syracuseStep 1847939 = 2771909) B2771909
theorem B1847969 : Blo 1230433 1847969 := bstep (se 2 (by rfl) ⟨692988, by rfl⟩ : syracuseStep 1847969 = 1385977) B1385977
theorem B1847987 : Blo 1230433 1847987 := bstep (se 1 (by rfl) ⟨1385990, by rfl⟩ : syracuseStep 1847987 = 2771981) B2771981
theorem B2077393 : Blo 1230433 2077393 := bstep (se 2 (by rfl) ⟨779022, by rfl⟩ : syracuseStep 2077393 = 1558045) B1558045
theorem B1848017 : Blo 1230433 1848017 := bstep (se 2 (by rfl) ⟨693006, by rfl⟩ : syracuseStep 1848017 = 1386013) B1386013
theorem B4158161 : Blo 1230433 4158161 := bstep (se 2 (by rfl) ⟨1559310, by rfl⟩ : syracuseStep 4158161 = 3118621) B3118621
theorem B1848035 : Blo 1230433 1848035 := bstep (se 1 (by rfl) ⟨1386026, by rfl⟩ : syracuseStep 1848035 = 2772053) B2772053
theorem B1872625 : Blo 1230433 1872625 := bstep (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) B1404469
theorem B2077427 : Blo 1230433 2077427 := bstep (se 1 (by rfl) ⟨1558070, by rfl⟩ : syracuseStep 2077427 = 3116141) B3116141
theorem B1848065 : Blo 1230433 1848065 := bstep (se 2 (by rfl) ⟨693024, by rfl⟩ : syracuseStep 1848065 = 1386049) B1386049
theorem B1848083 : Blo 1230433 1848083 := bstep (se 1 (by rfl) ⟨1386062, by rfl⟩ : syracuseStep 1848083 = 2772125) B2772125
theorem B1848113 : Blo 1230433 1848113 := bstep (se 2 (by rfl) ⟨693042, by rfl⟩ : syracuseStep 1848113 = 1386085) B1386085
theorem B1971011 : Blo 1230433 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B1848131 : Blo 1230433 1848131 := bstep (se 1 (by rfl) ⟨1386098, by rfl⟩ : syracuseStep 1848131 = 2772197) B2772197
theorem B1848161 : Blo 1230433 1848161 := bstep (se 2 (by rfl) ⟨693060, by rfl⟩ : syracuseStep 1848161 = 1386121) B1386121
theorem B3117923 : Blo 1230433 3117923 := bstep (se 1 (by rfl) ⟨2338442, by rfl⟩ : syracuseStep 3117923 = 4676885) B4676885
theorem B5919587 : Blo 1230433 5919587 := bstep (se 1 (by rfl) ⟨4439690, by rfl⟩ : syracuseStep 5919587 = 8879381) B8879381
theorem B2667377 : Blo 1230433 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B2077555 : Blo 1230433 2077555 := bstep (se 1 (by rfl) ⟨1558166, by rfl⟩ : syracuseStep 2077555 = 3116333) B3116333
theorem B1848179 : Blo 1230433 1848179 := bstep (se 1 (by rfl) ⟨1386134, by rfl⟩ : syracuseStep 1848179 = 2772269) B2772269
theorem B1848209 : Blo 1230433 1848209 := bstep (se 2 (by rfl) ⟨693078, by rfl⟩ : syracuseStep 1848209 = 1386157) B1386157
theorem B1848227 : Blo 1230433 1848227 := bstep (se 1 (by rfl) ⟨1386170, by rfl⟩ : syracuseStep 1848227 = 2772341) B2772341
theorem B1848257 : Blo 1230433 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B1848275 : Blo 1230433 1848275 := bstep (se 1 (by rfl) ⟨1386206, by rfl⟩ : syracuseStep 1848275 = 2772413) B2772413
theorem B1848305 : Blo 1230433 1848305 := bstep (se 2 (by rfl) ⟨693114, by rfl⟩ : syracuseStep 1848305 = 1386229) B1386229
theorem B2077697 : Blo 1230433 2077697 := bstep (se 2 (by rfl) ⟨779136, by rfl⟩ : syracuseStep 2077697 = 1558273) B1558273
theorem B1848323 : Blo 1230433 1848323 := bstep (se 1 (by rfl) ⟨1386242, by rfl⟩ : syracuseStep 1848323 = 2772485) B2772485
theorem B1848353 : Blo 1230433 1848353 := bstep (se 2 (by rfl) ⟨693132, by rfl⟩ : syracuseStep 1848353 = 1386265) B1386265
theorem B3118115 : Blo 1230433 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B1848371 : Blo 1230433 1848371 := bstep (se 1 (by rfl) ⟨1386278, by rfl⟩ : syracuseStep 1848371 = 2772557) B2772557
theorem B1848401 : Blo 1230433 1848401 := bstep (se 2 (by rfl) ⟨693150, by rfl⟩ : syracuseStep 1848401 = 1386301) B1386301
theorem B1848419 : Blo 1230433 1848419 := bstep (se 1 (by rfl) ⟨1386314, by rfl⟩ : syracuseStep 1848419 = 2772629) B2772629
theorem B2077825 : Blo 1230433 2077825 := bstep (se 2 (by rfl) ⟨779184, by rfl⟩ : syracuseStep 2077825 = 1558369) B1558369
theorem B1479811 : Blo 1230433 1479811 := bstep (se 1 (by rfl) ⟨1109858, by rfl⟩ : syracuseStep 1479811 = 2219717) B2219717
theorem B1848449 : Blo 1230433 1848449 := bstep (se 2 (by rfl) ⟨693168, by rfl⟩ : syracuseStep 1848449 = 1386337) B1386337
theorem B1848467 : Blo 1230433 1848467 := bstep (se 1 (by rfl) ⟨1386350, by rfl⟩ : syracuseStep 1848467 = 2772701) B2772701
theorem B2077859 : Blo 1230433 2077859 := bstep (se 1 (by rfl) ⟨1558394, by rfl⟩ : syracuseStep 2077859 = 3116789) B3116789
theorem B1848497 : Blo 1230433 1848497 := bstep (se 2 (by rfl) ⟨693186, by rfl⟩ : syracuseStep 1848497 = 1386373) B1386373
theorem B1283251 : Blo 1230433 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B1848515 : Blo 1230433 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B1848545 : Blo 1230433 1848545 := bstep (se 2 (by rfl) ⟨693204, by rfl⟩ : syracuseStep 1848545 = 1386409) B1386409
theorem B1971427 : Blo 1230433 1971427 := bstep (se 1 (by rfl) ⟨1478570, by rfl⟩ : syracuseStep 1971427 = 2957141) B2957141
theorem B11842787 : Blo 1230433 11842787 := bstep (se 1 (by rfl) ⟨8882090, by rfl⟩ : syracuseStep 11842787 = 17764181) B17764181
theorem B4158701 : Blo 1230433 4158701 := bstep (se 3 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 4158701 = 1559513) B1559513
theorem B1848563 : Blo 1230433 1848563 := bstep (se 1 (by rfl) ⟨1386422, by rfl⟩ : syracuseStep 1848563 = 2772845) B2772845
theorem B1848593 : Blo 1230433 1848593 := bstep (se 2 (by rfl) ⟨693222, by rfl⟩ : syracuseStep 1848593 = 1386445) B1386445
theorem B2077987 : Blo 1230433 2077987 := bstep (se 1 (by rfl) ⟨1558490, by rfl⟩ : syracuseStep 2077987 = 3116981) B3116981
theorem B4158755 : Blo 1230433 4158755 := bstep (se 1 (by rfl) ⟨3119066, by rfl⟩ : syracuseStep 4158755 = 6238133) B6238133
theorem B1848611 : Blo 1230433 1848611 := bstep (se 1 (by rfl) ⟨1386458, by rfl⟩ : syracuseStep 1848611 = 2772917) B2772917
theorem B1848641 : Blo 1230433 1848641 := bstep (se 2 (by rfl) ⟨693240, by rfl⟩ : syracuseStep 1848641 = 1386481) B1386481
theorem B3945827 : Blo 1230433 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B7009699 : Blo 1230433 7009699 := bstep (se 1 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 7009699 = 10514549) B10514549
theorem B2078129 : Blo 1230433 2078129 := bstep (se 2 (by rfl) ⟨779298, by rfl⟩ : syracuseStep 2078129 = 1558597) B1558597
theorem B2528753 : Blo 1230433 2528753 := bstep (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) B1896565
theorem B1971697 : Blo 1230433 1971697 := bstep (se 2 (by rfl) ⟨739386, by rfl⟩ : syracuseStep 1971697 = 1478773) B1478773
theorem B1480195 : Blo 1230433 1480195 := bstep (se 1 (by rfl) ⟨1110146, by rfl⟩ : syracuseStep 1480195 = 2220293) B2220293
theorem B2078257 : Blo 1230433 2078257 := bstep (se 2 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 2078257 = 1558693) B1558693
theorem B4159025 : Blo 1230433 4159025 := bstep (se 2 (by rfl) ⟨1559634, by rfl⟩ : syracuseStep 4159025 = 3119269) B3119269
theorem B2217539 : Blo 1230433 2217539 := bstep (se 1 (by rfl) ⟨1663154, by rfl⟩ : syracuseStep 2217539 = 3326309) B3326309
theorem B2078291 : Blo 1230433 2078291 := bstep (se 1 (by rfl) ⟨1558718, by rfl⟩ : syracuseStep 2078291 = 3117437) B3117437
theorem B23656049 : Blo 1230433 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B7894705 : Blo 1230433 7894705 := bstep (se 2 (by rfl) ⟨2960514, by rfl⟩ : syracuseStep 7894705 = 5921029) B5921029
theorem B2078419 : Blo 1230433 2078419 := bstep (se 1 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 2078419 = 3117629) B3117629
theorem B1971953 : Blo 1230433 1971953 := bstep (se 2 (by rfl) ⟨739482, by rfl⟩ : syracuseStep 1971953 = 1478965) B1478965
theorem B2078561 : Blo 1230433 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B4675427 : Blo 1230433 4675427 := bstep (se 1 (by rfl) ⟨3506570, by rfl⟩ : syracuseStep 4675427 = 7013141) B7013141
theorem B4675441 : Blo 1230433 4675441 := bstep (se 2 (by rfl) ⟨1753290, by rfl⟩ : syracuseStep 4675441 = 3506581) B3506581
theorem B1898353 : Blo 1230433 1898353 := bstep (se 2 (by rfl) ⟨711882, by rfl⟩ : syracuseStep 1898353 = 1423765) B1423765
theorem B7485317 : Blo 1230433 7485317 := bstep (se 4 (by rfl) ⟨701748, by rfl⟩ : syracuseStep 7485317 = 1403497) B1403497
theorem B15783821 : Blo 1230433 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B7010225 : Blo 1230433 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B3651533 : Blo 1230433 3651533 := bstep (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) B1369325
theorem B3119057 : Blo 1230433 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B2078689 : Blo 1230433 2078689 := bstep (se 2 (by rfl) ⟨779508, by rfl⟩ : syracuseStep 2078689 = 1559017) B1559017
theorem B2078723 : Blo 1230433 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B3119107 : Blo 1230433 3119107 := bstep (se 1 (by rfl) ⟨2339330, by rfl⟩ : syracuseStep 3119107 = 4678661) B4678661
theorem B21043313 : Blo 1230433 21043313 := bstep (se 2 (by rfl) ⟨7891242, by rfl⟩ : syracuseStep 21043313 = 15782485) B15782485
theorem B2078851 : Blo 1230433 2078851 := bstep (se 1 (by rfl) ⟨1559138, by rfl⟩ : syracuseStep 2078851 = 3118277) B3118277
theorem B3119249 : Blo 1230433 3119249 := bstep (se 2 (by rfl) ⟨1169718, by rfl⟩ : syracuseStep 3119249 = 2339437) B2339437
theorem B9345293 : Blo 1230433 9345293 := bstep (se 3 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 9345293 = 3504485) B3504485
theorem B2078993 : Blo 1230433 2078993 := bstep (se 2 (by rfl) ⟨779622, by rfl⟩ : syracuseStep 2078993 = 1559245) B1559245
theorem B4438307 : Blo 1230433 4438307 := bstep (se 1 (by rfl) ⟨3328730, by rfl⟩ : syracuseStep 4438307 = 6657461) B6657461
theorem B3742001 : Blo 1230433 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B3946801 : Blo 1230433 3946801 := bstep (se 2 (by rfl) ⟨1480050, by rfl⟩ : syracuseStep 3946801 = 2960101) B2960101
theorem B2079121 : Blo 1230433 2079121 := bstep (se 2 (by rfl) ⟨779670, by rfl⟩ : syracuseStep 2079121 = 1559341) B1559341
theorem B1972657 : Blo 1230433 1972657 := bstep (se 2 (by rfl) ⟨739746, by rfl⟩ : syracuseStep 1972657 = 1479493) B1479493
theorem B5921201 : Blo 1230433 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B2079155 : Blo 1230433 2079155 := bstep (se 1 (by rfl) ⟨1559366, by rfl⟩ : syracuseStep 2079155 = 3118733) B3118733
theorem B8419825 : Blo 1230433 8419825 := bstep (se 2 (by rfl) ⟨3157434, by rfl⟩ : syracuseStep 8419825 = 6314869) B6314869
theorem B6232625 : Blo 1230433 6232625 := bstep (se 2 (by rfl) ⟨2337234, by rfl⟩ : syracuseStep 6232625 = 4674469) B4674469
theorem B3947057 : Blo 1230433 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B2079283 : Blo 1230433 2079283 := bstep (se 1 (by rfl) ⟨1559462, by rfl⟩ : syracuseStep 2079283 = 3118925) B3118925
theorem B3160721 : Blo 1230433 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2079425 : Blo 1230433 2079425 := bstep (se 2 (by rfl) ⟨779784, by rfl⟩ : syracuseStep 2079425 = 1559569) B1559569
theorem B3504941 : Blo 1230433 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B2079553 : Blo 1230433 2079553 := bstep (se 2 (by rfl) ⟨779832, by rfl⟩ : syracuseStep 2079553 = 1559665) B1559665
theorem B4209475 : Blo 1230433 4209475 := bstep (se 1 (by rfl) ⟨3157106, by rfl⟩ : syracuseStep 4209475 = 6314213) B6314213
theorem B3554147 : Blo 1230433 3554147 := bstep (se 1 (by rfl) ⟨2665610, by rfl⟩ : syracuseStep 3554147 = 5331221) B5331221
theorem B2079587 : Blo 1230433 2079587 := bstep (se 1 (by rfl) ⟨1559690, by rfl⟩ : syracuseStep 2079587 = 3119381) B3119381
theorem B3505123 : Blo 1230433 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B11238371 : Blo 1230433 11238371 := bstep (se 1 (by rfl) ⟨8428778, by rfl⟩ : syracuseStep 11238371 = 16857557) B16857557
theorem B2079715 : Blo 1230433 2079715 := bstep (se 1 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 2079715 = 3119573) B3119573
theorem B3505169 : Blo 1230433 3505169 := bstep (se 2 (by rfl) ⟨1314438, by rfl⟩ : syracuseStep 3505169 = 2628877) B2628877
theorem B56835125 : Blo 1230433 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B7887941 : Blo 1230433 7887941 := bstep (se 4 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 7887941 = 1478989) B1478989
theorem B2809009 : Blo 1230433 2809009 := bstep (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) B2106757
theorem B8428805 : Blo 1230433 8428805 := bstep (se 4 (by rfl) ⟨790200, by rfl⟩ : syracuseStep 8428805 = 1580401) B1580401
theorem B4676899 : Blo 1230433 4676899 := bstep (se 1 (by rfl) ⟨3507674, by rfl⟩ : syracuseStep 4676899 = 7015349) B7015349
theorem B1973555 : Blo 1230433 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B7011683 : Blo 1230433 7011683 := bstep (se 1 (by rfl) ⟨5258762, by rfl⟩ : syracuseStep 7011683 = 10517525) B10517525
theorem B2997713 : Blo 1230433 2997713 := bstep (se 2 (by rfl) ⟨1124142, by rfl⟩ : syracuseStep 2997713 = 2248285) B2248285
theorem B1973747 : Blo 1230433 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B7200269 : Blo 1230433 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B2629219 : Blo 1230433 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B2956931 : Blo 1230433 2956931 := bstep (se 1 (by rfl) ⟨2217698, by rfl⟩ : syracuseStep 2956931 = 4435397) B4435397
theorem B3948173 : Blo 1230433 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B4152977 : Blo 1230433 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B5258915 : Blo 1230433 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B2768561 : Blo 1230433 2768561 := bstep (se 2 (by rfl) ⟨1038210, by rfl⟩ : syracuseStep 2768561 = 2076421) B2076421
theorem B2768579 : Blo 1230433 2768579 := bstep (se 1 (by rfl) ⟨2076434, by rfl⟩ : syracuseStep 2768579 = 4152869) B4152869
theorem B1777393 : Blo 1230433 1777393 := bstep (se 2 (by rfl) ⟨666522, by rfl⟩ : syracuseStep 1777393 = 1333045) B1333045
theorem B1752835 : Blo 1230433 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B14024501 : Blo 1230433 14024501 := bstep (se 5 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 14024501 = 1314797) B1314797
theorem B3997507 : Blo 1230433 3997507 := bstep (se 1 (by rfl) ⟨2998130, by rfl⟩ : syracuseStep 3997507 = 5996261) B5996261
theorem B1384339 : Blo 1230433 1384339 := bstep (se 1 (by rfl) ⟨1038254, by rfl⟩ : syracuseStep 1384339 = 2076509) B2076509
theorem B2768849 : Blo 1230433 2768849 := bstep (se 2 (by rfl) ⟨1038318, by rfl⟩ : syracuseStep 2768849 = 2076637) B2076637
theorem B3555281 : Blo 1230433 3555281 := bstep (se 2 (by rfl) ⟨1333230, by rfl⟩ : syracuseStep 3555281 = 2666461) B2666461
theorem B2768867 : Blo 1230433 2768867 := bstep (se 1 (by rfl) ⟨2076650, by rfl⟩ : syracuseStep 2768867 = 4153301) B4153301
theorem B6234083 : Blo 1230433 6234083 := bstep (se 1 (by rfl) ⟨4675562, by rfl⟩ : syracuseStep 6234083 = 9351125) B9351125
theorem B2629655 : Blo 1230433 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B2768921 : Blo 1230433 2768921 := bstep (se 2 (by rfl) ⟨1038345, by rfl⟩ : syracuseStep 2768921 = 2076691) B2076691
theorem B4153409 : Blo 1230433 4153409 := bstep (se 2 (by rfl) ⟨1557528, by rfl⟩ : syracuseStep 4153409 = 3115057) B3115057
theorem B5996609 : Blo 1230433 5996609 := bstep (se 2 (by rfl) ⟨2248728, by rfl⟩ : syracuseStep 5996609 = 4497457) B4497457
theorem B1753177 : Blo 1230433 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B6324317 : Blo 1230433 6324317 := bstep (se 3 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 6324317 = 2371619) B2371619
theorem B1384555 : Blo 1230433 1384555 := bstep (se 1 (by rfl) ⟨1038416, by rfl⟩ : syracuseStep 1384555 = 2076833) B2076833
theorem B2769011 : Blo 1230433 2769011 := bstep (se 1 (by rfl) ⟨2076758, by rfl⟩ : syracuseStep 2769011 = 4153517) B4153517
theorem B2769047 : Blo 1230433 2769047 := bstep (se 1 (by rfl) ⟨2076785, by rfl⟩ : syracuseStep 2769047 = 4153571) B4153571
theorem B1384663 : Blo 1230433 1384663 := bstep (se 1 (by rfl) ⟨1038497, by rfl⟩ : syracuseStep 1384663 = 2076995) B2076995
theorem B2769227 : Blo 1230433 2769227 := bstep (se 1 (by rfl) ⟨2076920, by rfl⟩ : syracuseStep 2769227 = 4153841) B4153841
theorem B2769281 : Blo 1230433 2769281 := bstep (se 2 (by rfl) ⟨1038480, by rfl⟩ : syracuseStep 2769281 = 2076961) B2076961
theorem B1384843 : Blo 1230433 1384843 := bstep (se 1 (by rfl) ⟨1038632, by rfl⟩ : syracuseStep 1384843 = 2077265) B2077265
theorem B13320625 : Blo 1230433 13320625 := bstep (se 2 (by rfl) ⟨4995234, by rfl⟩ : syracuseStep 13320625 = 9990469) B9990469
theorem B1384951 : Blo 1230433 1384951 := bstep (se 1 (by rfl) ⟨1038713, by rfl⟩ : syracuseStep 1384951 = 2077427) B2077427
theorem B3506753 : Blo 1230433 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B2769497 : Blo 1230433 2769497 := bstep (se 2 (by rfl) ⟨1038561, by rfl⟩ : syracuseStep 2769497 = 2077123) B2077123
theorem B4153949 : Blo 1230433 4153949 := bstep (se 3 (by rfl) ⟨778865, by rfl⟩ : syracuseStep 4153949 = 1557731) B1557731
theorem B7889501 : Blo 1230433 7889501 := bstep (se 3 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 7889501 = 2958563) B2958563
theorem B8422019 : Blo 1230433 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B1385131 : Blo 1230433 1385131 := bstep (se 1 (by rfl) ⟨1038848, by rfl⟩ : syracuseStep 1385131 = 2077697) B2077697
theorem B2769587 : Blo 1230433 2769587 := bstep (se 1 (by rfl) ⟨2077190, by rfl⟩ : syracuseStep 2769587 = 4154381) B4154381
theorem B2769623 : Blo 1230433 2769623 := bstep (se 1 (by rfl) ⟨2077217, by rfl⟩ : syracuseStep 2769623 = 4154435) B4154435
theorem B1385239 : Blo 1230433 1385239 := bstep (se 1 (by rfl) ⟨1038929, by rfl⟩ : syracuseStep 1385239 = 2077859) B2077859
theorem B2769803 : Blo 1230433 2769803 := bstep (se 1 (by rfl) ⟨2077352, by rfl⟩ : syracuseStep 2769803 = 4154705) B4154705
theorem B2630551 : Blo 1230433 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B2769857 : Blo 1230433 2769857 := bstep (se 2 (by rfl) ⟨1038696, by rfl⟩ : syracuseStep 2769857 = 2077393) B2077393
theorem B1385419 : Blo 1230433 1385419 := bstep (se 1 (by rfl) ⟨1039064, by rfl⟩ : syracuseStep 1385419 = 2078129) B2078129
theorem B1557463 : Blo 1230433 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B1385527 : Blo 1230433 1385527 := bstep (se 1 (by rfl) ⟨1039145, by rfl⟩ : syracuseStep 1385527 = 2078291) B2078291
theorem B15770699 : Blo 1230433 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B5612633 : Blo 1230433 5612633 := bstep (se 2 (by rfl) ⟨2104737, by rfl⟩ : syracuseStep 5612633 = 4209475) B4209475
theorem B2770073 : Blo 1230433 2770073 := bstep (se 2 (by rfl) ⟨1038777, by rfl⟩ : syracuseStep 2770073 = 2077555) B2077555
theorem B4678829 : Blo 1230433 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1385707 : Blo 1230433 1385707 := bstep (se 1 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 1385707 = 2078561) B2078561
theorem B2770163 : Blo 1230433 2770163 := bstep (se 1 (by rfl) ⟨2077622, by rfl⟩ : syracuseStep 2770163 = 4155245) B4155245
theorem B4990211 : Blo 1230433 4990211 := bstep (se 1 (by rfl) ⟨3742658, by rfl⟩ : syracuseStep 4990211 = 7485317) B7485317
theorem B9479429 : Blo 1230433 9479429 := bstep (se 4 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 9479429 = 1777393) B1777393
theorem B2770199 : Blo 1230433 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B6743341 : Blo 1230433 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B2434355 : Blo 1230433 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B3999041 : Blo 1230433 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B1385815 : Blo 1230433 1385815 := bstep (se 1 (by rfl) ⟨1039361, by rfl⟩ : syracuseStep 1385815 = 2078723) B2078723
theorem B2770379 : Blo 1230433 2770379 := bstep (se 1 (by rfl) ⟨2077784, by rfl⟩ : syracuseStep 2770379 = 4155569) B4155569
theorem B1664473 : Blo 1230433 1664473 := bstep (se 2 (by rfl) ⟨624177, by rfl⟩ : syracuseStep 1664473 = 1248355) B1248355
theorem B2770433 : Blo 1230433 2770433 := bstep (se 2 (by rfl) ⟨1038912, by rfl⟩ : syracuseStep 2770433 = 2077825) B2077825
theorem B1385995 : Blo 1230433 1385995 := bstep (se 1 (by rfl) ⟨1039496, by rfl⟩ : syracuseStep 1385995 = 2078993) B2078993
theorem B1754635 : Blo 1230433 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B2958871 : Blo 1230433 2958871 := bstep (se 1 (by rfl) ⟨2219153, by rfl⟩ : syracuseStep 2958871 = 4438307) B4438307
theorem B3745345 : Blo 1230433 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B3114571 : Blo 1230433 3114571 := bstep (se 1 (by rfl) ⟨2335928, by rfl⟩ : syracuseStep 3114571 = 4671857) B4671857
theorem B1230443 : Blo 1230433 1230443 := bstep (se 1 (by rfl) ⟨922832, by rfl⟩ : syracuseStep 1230443 = 1845665) B1845665
theorem B1230455 : Blo 1230433 1230455 := bstep (se 1 (by rfl) ⟨922841, by rfl⟩ : syracuseStep 1230455 = 1845683) B1845683
theorem B1386103 : Blo 1230433 1386103 := bstep (se 1 (by rfl) ⟨1039577, by rfl⟩ : syracuseStep 1386103 = 2079155) B2079155
theorem B1230475 : Blo 1230433 1230475 := bstep (se 1 (by rfl) ⟨922856, by rfl⟩ : syracuseStep 1230475 = 1845713) B1845713
theorem B1230487 : Blo 1230433 1230487 := bstep (se 1 (by rfl) ⟨922865, by rfl⟩ : syracuseStep 1230487 = 1845731) B1845731
theorem B1230507 : Blo 1230433 1230507 := bstep (se 1 (by rfl) ⟨922880, by rfl⟩ : syracuseStep 1230507 = 1845761) B1845761
theorem B1230519 : Blo 1230433 1230519 := bstep (se 1 (by rfl) ⟨922889, by rfl⟩ : syracuseStep 1230519 = 1845779) B1845779
theorem B1230539 : Blo 1230433 1230539 := bstep (se 1 (by rfl) ⟨922904, by rfl⟩ : syracuseStep 1230539 = 1845809) B1845809
theorem B4155083 : Blo 1230433 4155083 := bstep (se 1 (by rfl) ⟨3116312, by rfl⟩ : syracuseStep 4155083 = 6232625) B6232625
theorem B2631371 : Blo 1230433 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B1230551 : Blo 1230433 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B10512089 : Blo 1230433 10512089 := bstep (se 2 (by rfl) ⟨3942033, by rfl⟩ : syracuseStep 10512089 = 7884067) B7884067
theorem B3114713 : Blo 1230433 3114713 := bstep (se 2 (by rfl) ⟨1168017, by rfl⟩ : syracuseStep 3114713 = 2336035) B2336035
theorem B2770649 : Blo 1230433 2770649 := bstep (se 2 (by rfl) ⟨1038993, by rfl⟩ : syracuseStep 2770649 = 2077987) B2077987
theorem B6235865 : Blo 1230433 6235865 := bstep (se 2 (by rfl) ⟨2338449, by rfl⟩ : syracuseStep 6235865 = 4676899) B4676899
theorem B1230571 : Blo 1230433 1230571 := bstep (se 1 (by rfl) ⟨922928, by rfl⟩ : syracuseStep 1230571 = 1845857) B1845857
theorem B1230583 : Blo 1230433 1230583 := bstep (se 1 (by rfl) ⟨922937, by rfl⟩ : syracuseStep 1230583 = 1845875) B1845875
theorem B1230603 : Blo 1230433 1230603 := bstep (se 1 (by rfl) ⟨922952, by rfl⟩ : syracuseStep 1230603 = 1845905) B1845905
theorem B2107147 : Blo 1230433 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B1230615 : Blo 1230433 1230615 := bstep (se 1 (by rfl) ⟨922961, by rfl⟩ : syracuseStep 1230615 = 1845923) B1845923
theorem B1230635 : Blo 1230433 1230635 := bstep (se 1 (by rfl) ⟨922976, by rfl⟩ : syracuseStep 1230635 = 1845953) B1845953
theorem B1386283 : Blo 1230433 1386283 := bstep (se 1 (by rfl) ⟨1039712, by rfl⟩ : syracuseStep 1386283 = 2079425) B2079425
theorem B2770739 : Blo 1230433 2770739 := bstep (se 1 (by rfl) ⟨2078054, by rfl⟩ : syracuseStep 2770739 = 4156109) B4156109
theorem B1230647 : Blo 1230433 1230647 := bstep (se 1 (by rfl) ⟨922985, by rfl⟩ : syracuseStep 1230647 = 1845971) B1845971
theorem B1230667 : Blo 1230433 1230667 := bstep (se 1 (by rfl) ⟨923000, by rfl⟩ : syracuseStep 1230667 = 1846001) B1846001
theorem B3999563 : Blo 1230433 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B1230679 : Blo 1230433 1230679 := bstep (se 1 (by rfl) ⟨923009, by rfl⟩ : syracuseStep 1230679 = 1846019) B1846019
theorem B2770775 : Blo 1230433 2770775 := bstep (se 1 (by rfl) ⟨2078081, by rfl⟩ : syracuseStep 2770775 = 4156163) B4156163
theorem B39929699 : Blo 1230433 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B1230699 : Blo 1230433 1230699 := bstep (se 1 (by rfl) ⟨923024, by rfl⟩ : syracuseStep 1230699 = 1846049) B1846049
theorem B2336627 : Blo 1230433 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1230711 : Blo 1230433 1230711 := bstep (se 1 (by rfl) ⟨923033, by rfl⟩ : syracuseStep 1230711 = 1846067) B1846067
theorem B1230731 : Blo 1230433 1230731 := bstep (se 1 (by rfl) ⟨923048, by rfl⟩ : syracuseStep 1230731 = 1846097) B1846097
theorem B1230743 : Blo 1230433 1230743 := bstep (se 1 (by rfl) ⟨923057, by rfl⟩ : syracuseStep 1230743 = 1846115) B1846115
theorem B2369431 : Blo 1230433 2369431 := bstep (se 1 (by rfl) ⟨1777073, by rfl⟩ : syracuseStep 2369431 = 3554147) B3554147
theorem B1386391 : Blo 1230433 1386391 := bstep (se 1 (by rfl) ⟨1039793, by rfl⟩ : syracuseStep 1386391 = 2079587) B2079587
theorem B1230763 : Blo 1230433 1230763 := bstep (se 1 (by rfl) ⟨923072, by rfl⟩ : syracuseStep 1230763 = 1846145) B1846145
theorem B1230775 : Blo 1230433 1230775 := bstep (se 1 (by rfl) ⟨923081, by rfl⟩ : syracuseStep 1230775 = 1846163) B1846163
theorem B1230795 : Blo 1230433 1230795 := bstep (se 1 (by rfl) ⟨923096, by rfl⟩ : syracuseStep 1230795 = 1846193) B1846193
theorem B1230807 : Blo 1230433 1230807 := bstep (se 1 (by rfl) ⟨923105, by rfl⟩ : syracuseStep 1230807 = 1846211) B1846211
theorem B4155353 : Blo 1230433 4155353 := bstep (se 2 (by rfl) ⟨1558257, by rfl⟩ : syracuseStep 4155353 = 3116515) B3116515
theorem B1230827 : Blo 1230433 1230827 := bstep (se 1 (by rfl) ⟨923120, by rfl⟩ : syracuseStep 1230827 = 1846241) B1846241
theorem B1230839 : Blo 1230433 1230839 := bstep (se 1 (by rfl) ⟨923129, by rfl⟩ : syracuseStep 1230839 = 1846259) B1846259
theorem B1230859 : Blo 1230433 1230859 := bstep (se 1 (by rfl) ⟨923144, by rfl⟩ : syracuseStep 1230859 = 1846289) B1846289
theorem B2336779 : Blo 1230433 2336779 := bstep (se 1 (by rfl) ⟨1752584, by rfl⟩ : syracuseStep 2336779 = 3505169) B3505169
theorem B2770955 : Blo 1230433 2770955 := bstep (se 1 (by rfl) ⟨2078216, by rfl⟩ : syracuseStep 2770955 = 4156433) B4156433
theorem B1230871 : Blo 1230433 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B37890083 : Blo 1230433 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B8996899 : Blo 1230433 8996899 := bstep (se 1 (by rfl) ⟨6747674, by rfl⟩ : syracuseStep 8996899 = 13495349) B13495349
theorem B1230891 : Blo 1230433 1230891 := bstep (se 1 (by rfl) ⟨923168, by rfl⟩ : syracuseStep 1230891 = 1846337) B1846337
theorem B1230903 : Blo 1230433 1230903 := bstep (se 1 (by rfl) ⟨923177, by rfl⟩ : syracuseStep 1230903 = 1846355) B1846355
theorem B2771009 : Blo 1230433 2771009 := bstep (se 2 (by rfl) ⟨1039128, by rfl⟩ : syracuseStep 2771009 = 2078257) B2078257
theorem B54716485 : Blo 1230433 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B1230923 : Blo 1230433 1230923 := bstep (se 1 (by rfl) ⟨923192, by rfl⟩ : syracuseStep 1230923 = 1846385) B1846385
theorem B1230935 : Blo 1230433 1230935 := bstep (se 1 (by rfl) ⟨923201, by rfl⟩ : syracuseStep 1230935 = 1846403) B1846403
theorem B1230955 : Blo 1230433 1230955 := bstep (se 1 (by rfl) ⟨923216, by rfl⟩ : syracuseStep 1230955 = 1846433) B1846433
theorem B1230967 : Blo 1230433 1230967 := bstep (se 1 (by rfl) ⟨923225, by rfl⟩ : syracuseStep 1230967 = 1846451) B1846451
theorem B9357443 : Blo 1230433 9357443 := bstep (se 1 (by rfl) ⟨7018082, by rfl⟩ : syracuseStep 9357443 = 14036165) B14036165
theorem B1230987 : Blo 1230433 1230987 := bstep (se 1 (by rfl) ⟨923240, by rfl⟩ : syracuseStep 1230987 = 1846481) B1846481
theorem B1230999 : Blo 1230433 1230999 := bstep (se 1 (by rfl) ⟨923249, by rfl⟩ : syracuseStep 1230999 = 1846499) B1846499
theorem B1231019 : Blo 1230433 1231019 := bstep (se 1 (by rfl) ⟨923264, by rfl⟩ : syracuseStep 1231019 = 1846529) B1846529
theorem B1231031 : Blo 1230433 1231031 := bstep (se 1 (by rfl) ⟨923273, by rfl⟩ : syracuseStep 1231031 = 1846547) B1846547
theorem B1231051 : Blo 1230433 1231051 := bstep (se 1 (by rfl) ⟨923288, by rfl⟩ : syracuseStep 1231051 = 1846577) B1846577
theorem B3508427 : Blo 1230433 3508427 := bstep (se 1 (by rfl) ⟨2631320, by rfl⟩ : syracuseStep 3508427 = 5262641) B5262641
theorem B1231063 : Blo 1230433 1231063 := bstep (se 1 (by rfl) ⟨923297, by rfl⟩ : syracuseStep 1231063 = 1846595) B1846595
theorem B1231083 : Blo 1230433 1231083 := bstep (se 1 (by rfl) ⟨923312, by rfl⟩ : syracuseStep 1231083 = 1846625) B1846625
theorem B1231095 : Blo 1230433 1231095 := bstep (se 1 (by rfl) ⟨923321, by rfl⟩ : syracuseStep 1231095 = 1846643) B1846643
theorem B10520837 : Blo 1230433 10520837 := bstep (se 4 (by rfl) ⟨986328, by rfl⟩ : syracuseStep 10520837 = 1972657) B1972657
theorem B1231115 : Blo 1230433 1231115 := bstep (se 1 (by rfl) ⟨923336, by rfl⟩ : syracuseStep 1231115 = 1846673) B1846673
theorem B1231127 : Blo 1230433 1231127 := bstep (se 1 (by rfl) ⟨923345, by rfl⟩ : syracuseStep 1231127 = 1846691) B1846691
theorem B2771225 : Blo 1230433 2771225 := bstep (se 2 (by rfl) ⟨1039209, by rfl⟩ : syracuseStep 2771225 = 2078419) B2078419
theorem B1231147 : Blo 1230433 1231147 := bstep (se 1 (by rfl) ⟨923360, by rfl⟩ : syracuseStep 1231147 = 1846721) B1846721
theorem B7113005 : Blo 1230433 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B1231159 : Blo 1230433 1231159 := bstep (se 1 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 1231159 = 1846739) B1846739
theorem B1231179 : Blo 1230433 1231179 := bstep (se 1 (by rfl) ⟨923384, by rfl⟩ : syracuseStep 1231179 = 1846769) B1846769
theorem B1231191 : Blo 1230433 1231191 := bstep (se 1 (by rfl) ⟨923393, by rfl⟩ : syracuseStep 1231191 = 1846787) B1846787
theorem B2337113 : Blo 1230433 2337113 := bstep (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) B1752835
theorem B1231211 : Blo 1230433 1231211 := bstep (se 1 (by rfl) ⟨923408, by rfl⟩ : syracuseStep 1231211 = 1846817) B1846817
theorem B2771315 : Blo 1230433 2771315 := bstep (se 1 (by rfl) ⟨2078486, by rfl⟩ : syracuseStep 2771315 = 4156973) B4156973
theorem B1231223 : Blo 1230433 1231223 := bstep (se 1 (by rfl) ⟨923417, by rfl⟩ : syracuseStep 1231223 = 1846835) B1846835
theorem B1231243 : Blo 1230433 1231243 := bstep (se 1 (by rfl) ⟨923432, by rfl⟩ : syracuseStep 1231243 = 1846865) B1846865
theorem B1231255 : Blo 1230433 1231255 := bstep (se 1 (by rfl) ⟨923441, by rfl⟩ : syracuseStep 1231255 = 1846883) B1846883
theorem B2771351 : Blo 1230433 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B1231275 : Blo 1230433 1231275 := bstep (se 1 (by rfl) ⟨923456, by rfl⟩ : syracuseStep 1231275 = 1846913) B1846913
theorem B2632115 : Blo 1230433 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1231287 : Blo 1230433 1231287 := bstep (se 1 (by rfl) ⟨923465, by rfl⟩ : syracuseStep 1231287 = 1846931) B1846931
theorem B1845707 : Blo 1230433 1845707 := bstep (se 1 (by rfl) ⟨1384280, by rfl⟩ : syracuseStep 1845707 = 2768561) B2768561
theorem B1231307 : Blo 1230433 1231307 := bstep (se 1 (by rfl) ⟨923480, by rfl⟩ : syracuseStep 1231307 = 1846961) B1846961
theorem B1845719 : Blo 1230433 1845719 := bstep (se 1 (by rfl) ⟨1384289, by rfl⟩ : syracuseStep 1845719 = 2768579) B2768579
theorem B1231319 : Blo 1230433 1231319 := bstep (se 1 (by rfl) ⟨923489, by rfl⟩ : syracuseStep 1231319 = 1846979) B1846979
theorem B1231339 : Blo 1230433 1231339 := bstep (se 1 (by rfl) ⟨923504, by rfl⟩ : syracuseStep 1231339 = 1847009) B1847009
theorem B1247735 : Blo 1230433 1247735 := bstep (se 1 (by rfl) ⟨935801, by rfl⟩ : syracuseStep 1247735 = 1871603) B1871603
theorem B1231351 : Blo 1230433 1231351 := bstep (se 1 (by rfl) ⟨923513, by rfl⟩ : syracuseStep 1231351 = 1847027) B1847027
theorem B1247755 : Blo 1230433 1247755 := bstep (se 1 (by rfl) ⟨935816, by rfl⟩ : syracuseStep 1247755 = 1871633) B1871633
theorem B1231371 : Blo 1230433 1231371 := bstep (se 1 (by rfl) ⟨923528, by rfl⟩ : syracuseStep 1231371 = 1847057) B1847057
theorem B3115543 : Blo 1230433 3115543 := bstep (se 1 (by rfl) ⟨2336657, by rfl⟩ : syracuseStep 3115543 = 4673315) B4673315
theorem B1231383 : Blo 1230433 1231383 := bstep (se 1 (by rfl) ⟨923537, by rfl⟩ : syracuseStep 1231383 = 1847075) B1847075
theorem B1845785 : Blo 1230433 1845785 := bstep (se 2 (by rfl) ⟨692169, by rfl⟩ : syracuseStep 1845785 = 1384339) B1384339
theorem B9349667 : Blo 1230433 9349667 := bstep (se 1 (by rfl) ⟨7012250, by rfl⟩ : syracuseStep 9349667 = 14024501) B14024501
theorem B8882723 : Blo 1230433 8882723 := bstep (se 1 (by rfl) ⟨6662042, by rfl⟩ : syracuseStep 8882723 = 13324085) B13324085
theorem B1231403 : Blo 1230433 1231403 := bstep (se 1 (by rfl) ⟨923552, by rfl⟩ : syracuseStep 1231403 = 1847105) B1847105
theorem B1231415 : Blo 1230433 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B1231435 : Blo 1230433 1231435 := bstep (se 1 (by rfl) ⟨923576, by rfl⟩ : syracuseStep 1231435 = 1847153) B1847153
theorem B2771531 : Blo 1230433 2771531 := bstep (se 1 (by rfl) ⟨2078648, by rfl⟩ : syracuseStep 2771531 = 4157297) B4157297
theorem B1231447 : Blo 1230433 1231447 := bstep (se 1 (by rfl) ⟨923585, by rfl⟩ : syracuseStep 1231447 = 1847171) B1847171
theorem B1231467 : Blo 1230433 1231467 := bstep (se 1 (by rfl) ⟨923600, by rfl⟩ : syracuseStep 1231467 = 1847201) B1847201
theorem B1231479 : Blo 1230433 1231479 := bstep (se 1 (by rfl) ⟨923609, by rfl⟩ : syracuseStep 1231479 = 1847219) B1847219
theorem B2771585 : Blo 1230433 2771585 := bstep (se 2 (by rfl) ⟨1039344, by rfl⟩ : syracuseStep 2771585 = 2078689) B2078689
theorem B1845899 : Blo 1230433 1845899 := bstep (se 1 (by rfl) ⟨1384424, by rfl⟩ : syracuseStep 1845899 = 2768849) B2768849
theorem B1231499 : Blo 1230433 1231499 := bstep (se 1 (by rfl) ⟨923624, by rfl⟩ : syracuseStep 1231499 = 1847249) B1847249
theorem B2370187 : Blo 1230433 2370187 := bstep (se 1 (by rfl) ⟨1777640, by rfl⟩ : syracuseStep 2370187 = 3555281) B3555281
theorem B1559179 : Blo 1230433 1559179 := bstep (se 1 (by rfl) ⟨1169384, by rfl⟩ : syracuseStep 1559179 = 2338769) B2338769
theorem B1845911 : Blo 1230433 1845911 := bstep (se 1 (by rfl) ⟨1384433, by rfl⟩ : syracuseStep 1845911 = 2768867) B2768867
theorem B4156055 : Blo 1230433 4156055 := bstep (se 1 (by rfl) ⟨3117041, by rfl⟩ : syracuseStep 4156055 = 6234083) B6234083
theorem B1231511 : Blo 1230433 1231511 := bstep (se 1 (by rfl) ⟨923633, by rfl⟩ : syracuseStep 1231511 = 1847267) B1847267
theorem B1231531 : Blo 1230433 1231531 := bstep (se 1 (by rfl) ⟨923648, by rfl⟩ : syracuseStep 1231531 = 1847297) B1847297
theorem B1231543 : Blo 1230433 1231543 := bstep (se 1 (by rfl) ⟨923657, by rfl⟩ : syracuseStep 1231543 = 1847315) B1847315
theorem B1231563 : Blo 1230433 1231563 := bstep (se 1 (by rfl) ⟨923672, by rfl⟩ : syracuseStep 1231563 = 1847345) B1847345
theorem B1231575 : Blo 1230433 1231575 := bstep (se 1 (by rfl) ⟨923681, by rfl⟩ : syracuseStep 1231575 = 1847363) B1847363
theorem B1845977 : Blo 1230433 1845977 := bstep (se 2 (by rfl) ⟨692241, by rfl⟩ : syracuseStep 1845977 = 1384483) B1384483
theorem B1231595 : Blo 1230433 1231595 := bstep (se 1 (by rfl) ⟨923696, by rfl⟩ : syracuseStep 1231595 = 1847393) B1847393
theorem B1231607 : Blo 1230433 1231607 := bstep (se 1 (by rfl) ⟨923705, by rfl⟩ : syracuseStep 1231607 = 1847411) B1847411
theorem B1231627 : Blo 1230433 1231627 := bstep (se 1 (by rfl) ⟨923720, by rfl⟩ : syracuseStep 1231627 = 1847441) B1847441
theorem B1231639 : Blo 1230433 1231639 := bstep (se 1 (by rfl) ⟨923729, by rfl⟩ : syracuseStep 1231639 = 1847459) B1847459
theorem B1231659 : Blo 1230433 1231659 := bstep (se 1 (by rfl) ⟨923744, by rfl⟩ : syracuseStep 1231659 = 1847489) B1847489
theorem B1231671 : Blo 1230433 1231671 := bstep (se 1 (by rfl) ⟨923753, by rfl⟩ : syracuseStep 1231671 = 1847507) B1847507
theorem B1846091 : Blo 1230433 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B1231691 : Blo 1230433 1231691 := bstep (se 1 (by rfl) ⟨923768, by rfl⟩ : syracuseStep 1231691 = 1847537) B1847537
theorem B1846103 : Blo 1230433 1846103 := bstep (se 1 (by rfl) ⟨1384577, by rfl⟩ : syracuseStep 1846103 = 2769155) B2769155
theorem B1231703 : Blo 1230433 1231703 := bstep (se 1 (by rfl) ⟨923777, by rfl⟩ : syracuseStep 1231703 = 1847555) B1847555
theorem B2771801 : Blo 1230433 2771801 := bstep (se 2 (by rfl) ⟨1039425, by rfl⟩ : syracuseStep 2771801 = 2078851) B2078851
theorem B1231723 : Blo 1230433 1231723 := bstep (se 1 (by rfl) ⟨923792, by rfl⟩ : syracuseStep 1231723 = 1847585) B1847585
theorem B1231735 : Blo 1230433 1231735 := bstep (se 1 (by rfl) ⟨923801, by rfl⟩ : syracuseStep 1231735 = 1847603) B1847603
theorem B1231755 : Blo 1230433 1231755 := bstep (se 1 (by rfl) ⟨923816, by rfl⟩ : syracuseStep 1231755 = 1847633) B1847633
theorem B1231767 : Blo 1230433 1231767 := bstep (se 1 (by rfl) ⟨923825, by rfl⟩ : syracuseStep 1231767 = 1847651) B1847651
theorem B1846169 : Blo 1230433 1846169 := bstep (se 2 (by rfl) ⟨692313, by rfl⟩ : syracuseStep 1846169 = 1384627) B1384627
theorem B1231787 : Blo 1230433 1231787 := bstep (se 1 (by rfl) ⟨923840, by rfl⟩ : syracuseStep 1231787 = 1847681) B1847681
theorem B10521521 : Blo 1230433 10521521 := bstep (se 2 (by rfl) ⟨3945570, by rfl⟩ : syracuseStep 10521521 = 7891141) B7891141
theorem B2771891 : Blo 1230433 2771891 := bstep (se 1 (by rfl) ⟨2078918, by rfl⟩ : syracuseStep 2771891 = 4157837) B4157837
theorem B21056435 : Blo 1230433 21056435 := bstep (se 1 (by rfl) ⟨15792326, by rfl⟩ : syracuseStep 21056435 = 31584653) B31584653
theorem B1231799 : Blo 1230433 1231799 := bstep (se 1 (by rfl) ⟨923849, by rfl⟩ : syracuseStep 1231799 = 1847699) B1847699
theorem B3115979 : Blo 1230433 3115979 := bstep (se 1 (by rfl) ⟨2336984, by rfl⟩ : syracuseStep 3115979 = 4673969) B4673969
theorem B1231819 : Blo 1230433 1231819 := bstep (se 1 (by rfl) ⟨923864, by rfl⟩ : syracuseStep 1231819 = 1847729) B1847729
theorem B2337751 : Blo 1230433 2337751 := bstep (se 1 (by rfl) ⟨1753313, by rfl⟩ : syracuseStep 2337751 = 3506627) B3506627
theorem B1231831 : Blo 1230433 1231831 := bstep (se 1 (by rfl) ⟨923873, by rfl⟩ : syracuseStep 1231831 = 1847747) B1847747
theorem B2771927 : Blo 1230433 2771927 := bstep (se 1 (by rfl) ⟨2078945, by rfl⟩ : syracuseStep 2771927 = 4157891) B4157891
theorem B1231851 : Blo 1230433 1231851 := bstep (se 1 (by rfl) ⟨923888, by rfl⟩ : syracuseStep 1231851 = 1847777) B1847777
theorem B1231863 : Blo 1230433 1231863 := bstep (se 1 (by rfl) ⟨923897, by rfl⟩ : syracuseStep 1231863 = 1847795) B1847795
theorem B1846283 : Blo 1230433 1846283 := bstep (se 1 (by rfl) ⟨1384712, by rfl⟩ : syracuseStep 1846283 = 2769425) B2769425
theorem B1231883 : Blo 1230433 1231883 := bstep (se 1 (by rfl) ⟨923912, by rfl⟩ : syracuseStep 1231883 = 1847825) B1847825
theorem B2165771 : Blo 1230433 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B1846295 : Blo 1230433 1846295 := bstep (se 1 (by rfl) ⟨1384721, by rfl⟩ : syracuseStep 1846295 = 2769443) B2769443
theorem B1231895 : Blo 1230433 1231895 := bstep (se 1 (by rfl) ⟨923921, by rfl⟩ : syracuseStep 1231895 = 1847843) B1847843
theorem B1231915 : Blo 1230433 1231915 := bstep (se 1 (by rfl) ⟨923936, by rfl⟩ : syracuseStep 1231915 = 1847873) B1847873
theorem B1231927 : Blo 1230433 1231927 := bstep (se 1 (by rfl) ⟨923945, by rfl⟩ : syracuseStep 1231927 = 1847891) B1847891
theorem B5262401 : Blo 1230433 5262401 := bstep (se 2 (by rfl) ⟨1973400, by rfl⟩ : syracuseStep 5262401 = 3946801) B3946801
theorem B6843457 : Blo 1230433 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B1231947 : Blo 1230433 1231947 := bstep (se 1 (by rfl) ⟨923960, by rfl⟩ : syracuseStep 1231947 = 1847921) B1847921
theorem B1231959 : Blo 1230433 1231959 := bstep (se 1 (by rfl) ⟨923969, by rfl⟩ : syracuseStep 1231959 = 1847939) B1847939
theorem B1846361 : Blo 1230433 1846361 := bstep (se 2 (by rfl) ⟨692385, by rfl⟩ : syracuseStep 1846361 = 1384771) B1384771
theorem B1231979 : Blo 1230433 1231979 := bstep (se 1 (by rfl) ⟨923984, by rfl⟩ : syracuseStep 1231979 = 1847969) B1847969
theorem B1231991 : Blo 1230433 1231991 := bstep (se 1 (by rfl) ⟨923993, by rfl⟩ : syracuseStep 1231991 = 1847987) B1847987
theorem B1232011 : Blo 1230433 1232011 := bstep (se 1 (by rfl) ⟨924008, by rfl⟩ : syracuseStep 1232011 = 1848017) B1848017
theorem B2772107 : Blo 1230433 2772107 := bstep (se 1 (by rfl) ⟨2079080, by rfl⟩ : syracuseStep 2772107 = 4158161) B4158161
theorem B1232023 : Blo 1230433 1232023 := bstep (se 1 (by rfl) ⟨924017, by rfl⟩ : syracuseStep 1232023 = 1848035) B1848035
theorem B1232043 : Blo 1230433 1232043 := bstep (se 1 (by rfl) ⟨924032, by rfl⟩ : syracuseStep 1232043 = 1848065) B1848065
theorem B4156595 : Blo 1230433 4156595 := bstep (se 1 (by rfl) ⟨3117446, by rfl⟩ : syracuseStep 4156595 = 6234893) B6234893
theorem B2960563 : Blo 1230433 2960563 := bstep (se 1 (by rfl) ⟨2220422, by rfl⟩ : syracuseStep 2960563 = 4440845) B4440845
theorem B1232055 : Blo 1230433 1232055 := bstep (se 1 (by rfl) ⟨924041, by rfl⟩ : syracuseStep 1232055 = 1848083) B1848083
theorem B2772161 : Blo 1230433 2772161 := bstep (se 2 (by rfl) ⟨1039560, by rfl⟩ : syracuseStep 2772161 = 2079121) B2079121
theorem B1846475 : Blo 1230433 1846475 := bstep (se 1 (by rfl) ⟨1384856, by rfl⟩ : syracuseStep 1846475 = 2769713) B2769713
theorem B1232075 : Blo 1230433 1232075 := bstep (se 1 (by rfl) ⟨924056, by rfl⟩ : syracuseStep 1232075 = 1848113) B1848113
theorem B1846487 : Blo 1230433 1846487 := bstep (se 1 (by rfl) ⟨1384865, by rfl⟩ : syracuseStep 1846487 = 2769731) B2769731
theorem B1232087 : Blo 1230433 1232087 := bstep (se 1 (by rfl) ⟨924065, by rfl⟩ : syracuseStep 1232087 = 1848131) B1848131
theorem B1232107 : Blo 1230433 1232107 := bstep (se 1 (by rfl) ⟨924080, by rfl⟩ : syracuseStep 1232107 = 1848161) B1848161
theorem B1232119 : Blo 1230433 1232119 := bstep (se 1 (by rfl) ⟨924089, by rfl⟩ : syracuseStep 1232119 = 1848179) B1848179
theorem B1232139 : Blo 1230433 1232139 := bstep (se 1 (by rfl) ⟨924104, by rfl⟩ : syracuseStep 1232139 = 1848209) B1848209
theorem B1232151 : Blo 1230433 1232151 := bstep (se 1 (by rfl) ⟨924113, by rfl⟩ : syracuseStep 1232151 = 1848227) B1848227
theorem B1846553 : Blo 1230433 1846553 := bstep (se 2 (by rfl) ⟨692457, by rfl⟩ : syracuseStep 1846553 = 1384915) B1384915
theorem B6237485 : Blo 1230433 6237485 := bstep (se 3 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 6237485 = 2339057) B2339057
theorem B1232171 : Blo 1230433 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B1232183 : Blo 1230433 1232183 := bstep (se 1 (by rfl) ⟨924137, by rfl⟩ : syracuseStep 1232183 = 1848275) B1848275
theorem B11226433 : Blo 1230433 11226433 := bstep (se 2 (by rfl) ⟨4209912, by rfl⟩ : syracuseStep 11226433 = 8419825) B8419825
theorem B3116353 : Blo 1230433 3116353 := bstep (se 2 (by rfl) ⟨1168632, by rfl⟩ : syracuseStep 3116353 = 2337265) B2337265
theorem B11832641 : Blo 1230433 11832641 := bstep (se 2 (by rfl) ⟨4437240, by rfl⟩ : syracuseStep 11832641 = 8874481) B8874481
theorem B1232203 : Blo 1230433 1232203 := bstep (se 1 (by rfl) ⟨924152, by rfl⟩ : syracuseStep 1232203 = 1848305) B1848305
theorem B1232215 : Blo 1230433 1232215 := bstep (se 1 (by rfl) ⟨924161, by rfl⟩ : syracuseStep 1232215 = 1848323) B1848323
theorem B10268005 : Blo 1230433 10268005 := bstep (se 4 (by rfl) ⟨962625, by rfl⟩ : syracuseStep 10268005 = 1925251) B1925251
theorem B1232235 : Blo 1230433 1232235 := bstep (se 1 (by rfl) ⟨924176, by rfl⟩ : syracuseStep 1232235 = 1848353) B1848353
theorem B1232247 : Blo 1230433 1232247 := bstep (se 1 (by rfl) ⟨924185, by rfl⟩ : syracuseStep 1232247 = 1848371) B1848371
theorem B1846667 : Blo 1230433 1846667 := bstep (se 1 (by rfl) ⟨1385000, by rfl⟩ : syracuseStep 1846667 = 2770001) B2770001
theorem B1232267 : Blo 1230433 1232267 := bstep (se 1 (by rfl) ⟨924200, by rfl⟩ : syracuseStep 1232267 = 1848401) B1848401
theorem B1846679 : Blo 1230433 1846679 := bstep (se 1 (by rfl) ⟨1385009, by rfl⟩ : syracuseStep 1846679 = 2770019) B2770019
theorem B1232279 : Blo 1230433 1232279 := bstep (se 1 (by rfl) ⟨924209, by rfl⟩ : syracuseStep 1232279 = 1848419) B1848419
theorem B2772377 : Blo 1230433 2772377 := bstep (se 2 (by rfl) ⟨1039641, by rfl⟩ : syracuseStep 2772377 = 2079283) B2079283
theorem B1232299 : Blo 1230433 1232299 := bstep (se 1 (by rfl) ⟨924224, by rfl⟩ : syracuseStep 1232299 = 1848449) B1848449
theorem B1232311 : Blo 1230433 1232311 := bstep (se 1 (by rfl) ⟨924233, by rfl⟩ : syracuseStep 1232311 = 1848467) B1848467
theorem B4156865 : Blo 1230433 4156865 := bstep (se 2 (by rfl) ⟨1558824, by rfl⟩ : syracuseStep 4156865 = 3117649) B3117649
theorem B1232331 : Blo 1230433 1232331 := bstep (se 1 (by rfl) ⟨924248, by rfl⟩ : syracuseStep 1232331 = 1848497) B1848497
theorem B1232343 : Blo 1230433 1232343 := bstep (se 1 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 1232343 = 1848515) B1848515
theorem B1846745 : Blo 1230433 1846745 := bstep (se 2 (by rfl) ⟨692529, by rfl⟩ : syracuseStep 1846745 = 1385059) B1385059
theorem B1232363 : Blo 1230433 1232363 := bstep (se 1 (by rfl) ⟨924272, by rfl⟩ : syracuseStep 1232363 = 1848545) B1848545
theorem B2772467 : Blo 1230433 2772467 := bstep (se 1 (by rfl) ⟨2079350, by rfl⟩ : syracuseStep 2772467 = 4158701) B4158701
theorem B1232375 : Blo 1230433 1232375 := bstep (se 1 (by rfl) ⟨924281, by rfl⟩ : syracuseStep 1232375 = 1848563) B1848563
theorem B1232395 : Blo 1230433 1232395 := bstep (se 1 (by rfl) ⟨924296, by rfl⟩ : syracuseStep 1232395 = 1848593) B1848593
theorem B2772503 : Blo 1230433 2772503 := bstep (se 1 (by rfl) ⟨2079377, by rfl⟩ : syracuseStep 2772503 = 4158755) B4158755
theorem B1232407 : Blo 1230433 1232407 := bstep (se 1 (by rfl) ⟨924305, by rfl⟩ : syracuseStep 1232407 = 1848611) B1848611
theorem B1232427 : Blo 1230433 1232427 := bstep (se 1 (by rfl) ⟨924320, by rfl⟩ : syracuseStep 1232427 = 1848641) B1848641
theorem B1846859 : Blo 1230433 1846859 := bstep (se 1 (by rfl) ⟨1385144, by rfl⟩ : syracuseStep 1846859 = 2770289) B2770289
theorem B1846871 : Blo 1230433 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B1846937 : Blo 1230433 1846937 := bstep (se 2 (by rfl) ⟨692601, by rfl⟩ : syracuseStep 1846937 = 1385203) B1385203
theorem B2772683 : Blo 1230433 2772683 := bstep (se 1 (by rfl) ⟨2079512, by rfl⟩ : syracuseStep 2772683 = 4159025) B4159025
theorem B1478359 : Blo 1230433 1478359 := bstep (se 1 (by rfl) ⟨1108769, by rfl⟩ : syracuseStep 1478359 = 2217539) B2217539
theorem B2666201 : Blo 1230433 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B2772737 : Blo 1230433 2772737 := bstep (se 2 (by rfl) ⟨1039776, by rfl⟩ : syracuseStep 2772737 = 2079553) B2079553
theorem B1847051 : Blo 1230433 1847051 := bstep (se 1 (by rfl) ⟨1385288, by rfl⟩ : syracuseStep 1847051 = 2770577) B2770577
theorem B2338571 : Blo 1230433 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B1847063 : Blo 1230433 1847063 := bstep (se 1 (by rfl) ⟨1385297, by rfl⟩ : syracuseStep 1847063 = 2770595) B2770595
theorem B2338625 : Blo 1230433 2338625 := bstep (se 2 (by rfl) ⟨876984, by rfl⟩ : syracuseStep 2338625 = 1753969) B1753969
theorem B1314635 : Blo 1230433 1314635 := bstep (se 1 (by rfl) ⟨985976, by rfl⟩ : syracuseStep 1314635 = 1971953) B1971953
theorem B1847129 : Blo 1230433 1847129 := bstep (se 2 (by rfl) ⟨692673, by rfl⟩ : syracuseStep 1847129 = 1385347) B1385347
theorem B3116951 : Blo 1230433 3116951 := bstep (se 1 (by rfl) ⟨2337713, by rfl⟩ : syracuseStep 3116951 = 4675427) B4675427
theorem B10522547 : Blo 1230433 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B4673483 : Blo 1230433 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B1847243 : Blo 1230433 1847243 := bstep (se 1 (by rfl) ⟨1385432, by rfl⟩ : syracuseStep 1847243 = 2770865) B2770865
theorem B1847255 : Blo 1230433 1847255 := bstep (se 1 (by rfl) ⟨1385441, by rfl⟩ : syracuseStep 1847255 = 2770883) B2770883
theorem B4673497 : Blo 1230433 4673497 := bstep (se 2 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 4673497 = 3505123) B3505123
theorem B2772953 : Blo 1230433 2772953 := bstep (se 2 (by rfl) ⟨1039857, by rfl⟩ : syracuseStep 2772953 = 2079715) B2079715
theorem B4157405 : Blo 1230433 4157405 := bstep (se 3 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 4157405 = 1559027) B1559027
theorem B5263325 : Blo 1230433 5263325 := bstep (se 3 (by rfl) ⟨986873, by rfl⟩ : syracuseStep 5263325 = 1973747) B1973747
theorem B6230033 : Blo 1230433 6230033 := bstep (se 2 (by rfl) ⟨2336262, by rfl⟩ : syracuseStep 6230033 = 4672525) B4672525
theorem B1847321 : Blo 1230433 1847321 := bstep (se 2 (by rfl) ⟨692745, by rfl⟩ : syracuseStep 1847321 = 1385491) B1385491
theorem B4272151 : Blo 1230433 4272151 := bstep (se 1 (by rfl) ⟨3204113, by rfl⟩ : syracuseStep 4272151 = 6408227) B6408227
theorem B14028875 : Blo 1230433 14028875 := bstep (se 1 (by rfl) ⟨10521656, by rfl⟩ : syracuseStep 14028875 = 21043313) B21043313
theorem B7491685 : Blo 1230433 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B1847435 : Blo 1230433 1847435 := bstep (se 1 (by rfl) ⟨1385576, by rfl⟩ : syracuseStep 1847435 = 2771153) B2771153
theorem B88871053 : Blo 1230433 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B1847447 : Blo 1230433 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B6230195 : Blo 1230433 6230195 := bstep (se 1 (by rfl) ⟨4672646, by rfl⟩ : syracuseStep 6230195 = 9345293) B9345293
theorem B2494667 : Blo 1230433 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B2076887 : Blo 1230433 2076887 := bstep (se 1 (by rfl) ⟨1557665, by rfl⟩ : syracuseStep 2076887 = 3115331) B3115331
theorem B1847513 : Blo 1230433 1847513 := bstep (se 2 (by rfl) ⟨692817, by rfl⟩ : syracuseStep 1847513 = 1385635) B1385635
theorem B4993325 : Blo 1230433 4993325 := bstep (se 3 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 4993325 = 1872497) B1872497
theorem B1847627 : Blo 1230433 1847627 := bstep (se 1 (by rfl) ⟨1385720, by rfl⟩ : syracuseStep 1847627 = 2771441) B2771441
theorem B2077015 : Blo 1230433 2077015 := bstep (se 1 (by rfl) ⟨1557761, by rfl⟩ : syracuseStep 2077015 = 3115523) B3115523
theorem B1847639 : Blo 1230433 1847639 := bstep (se 1 (by rfl) ⟨1385729, by rfl⟩ : syracuseStep 1847639 = 2771459) B2771459
theorem B19960181 : Blo 1230433 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B3158423 : Blo 1230433 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B1847705 : Blo 1230433 1847705 := bstep (se 2 (by rfl) ⟨692889, by rfl⟩ : syracuseStep 1847705 = 1385779) B1385779
theorem B1847819 : Blo 1230433 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B1847831 : Blo 1230433 1847831 := bstep (se 1 (by rfl) ⟨1385873, by rfl⟩ : syracuseStep 1847831 = 2771747) B2771747
theorem B1847897 : Blo 1230433 1847897 := bstep (se 2 (by rfl) ⟨692961, by rfl⟩ : syracuseStep 1847897 = 1385923) B1385923
theorem B7492247 : Blo 1230433 7492247 := bstep (se 1 (by rfl) ⟨5619185, by rfl⟩ : syracuseStep 7492247 = 11238371) B11238371
theorem B3117761 : Blo 1230433 3117761 := bstep (se 2 (by rfl) ⟨1169160, by rfl⟩ : syracuseStep 3117761 = 2338321) B2338321
theorem B1848011 : Blo 1230433 1848011 := bstep (se 1 (by rfl) ⟨1386008, by rfl⟩ : syracuseStep 1848011 = 2772017) B2772017
theorem B1848023 : Blo 1230433 1848023 := bstep (se 1 (by rfl) ⟨1386017, by rfl⟩ : syracuseStep 1848023 = 2772035) B2772035
theorem B2339543 : Blo 1230433 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B1848089 : Blo 1230433 1848089 := bstep (se 2 (by rfl) ⟨693033, by rfl⟩ : syracuseStep 1848089 = 1386067) B1386067
theorem B5256029 : Blo 1230433 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B1315703 : Blo 1230433 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1848203 : Blo 1230433 1848203 := bstep (se 1 (by rfl) ⟨1386152, by rfl⟩ : syracuseStep 1848203 = 2772305) B2772305
theorem B4674455 : Blo 1230433 4674455 := bstep (se 1 (by rfl) ⟨3505841, by rfl⟩ : syracuseStep 4674455 = 7011683) B7011683
theorem B1848215 : Blo 1230433 1848215 := bstep (se 1 (by rfl) ⟨1386161, by rfl⟩ : syracuseStep 1848215 = 2772323) B2772323
theorem B2077643 : Blo 1230433 2077643 := bstep (se 1 (by rfl) ⟨1558232, by rfl⟩ : syracuseStep 2077643 = 3116465) B3116465
theorem B1848281 : Blo 1230433 1848281 := bstep (se 2 (by rfl) ⟨693105, by rfl⟩ : syracuseStep 1848281 = 1386211) B1386211
theorem B2077771 : Blo 1230433 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B4158539 : Blo 1230433 4158539 := bstep (se 1 (by rfl) ⟨3118904, by rfl⟩ : syracuseStep 4158539 = 6237809) B6237809
theorem B1848395 : Blo 1230433 1848395 := bstep (se 1 (by rfl) ⟨1386296, by rfl⟩ : syracuseStep 1848395 = 2772593) B2772593
theorem B1971287 : Blo 1230433 1971287 := bstep (se 1 (by rfl) ⟨1478465, by rfl⟩ : syracuseStep 1971287 = 2956931) B2956931
theorem B1848407 : Blo 1230433 1848407 := bstep (se 1 (by rfl) ⟨1386305, by rfl⟩ : syracuseStep 1848407 = 2772611) B2772611
theorem B5330009 : Blo 1230433 5330009 := bstep (se 2 (by rfl) ⟨1998753, by rfl⟩ : syracuseStep 5330009 = 3997507) B3997507
theorem B1848473 : Blo 1230433 1848473 := bstep (se 2 (by rfl) ⟨693177, by rfl⟩ : syracuseStep 1848473 = 1386355) B1386355
theorem B2077913 : Blo 1230433 2077913 := bstep (se 2 (by rfl) ⟨779217, by rfl⟩ : syracuseStep 2077913 = 1558435) B1558435
theorem B3118297 : Blo 1230433 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B1848587 : Blo 1230433 1848587 := bstep (se 1 (by rfl) ⟨1386440, by rfl⟩ : syracuseStep 1848587 = 2772881) B2772881
theorem B1848599 : Blo 1230433 1848599 := bstep (se 1 (by rfl) ⟨1386449, by rfl⟩ : syracuseStep 1848599 = 2772899) B2772899
theorem B9344321 : Blo 1230433 9344321 := bstep (se 2 (by rfl) ⟨3504120, by rfl⟩ : syracuseStep 9344321 = 7008241) B7008241
theorem B2078041 : Blo 1230433 2078041 := bstep (se 2 (by rfl) ⟨779265, by rfl⟩ : syracuseStep 2078041 = 1558531) B1558531
theorem B4158809 : Blo 1230433 4158809 := bstep (se 2 (by rfl) ⟨1559553, by rfl⟩ : syracuseStep 4158809 = 3119107) B3119107
theorem B4216157 : Blo 1230433 4216157 := bstep (se 3 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 4216157 = 1581059) B1581059
theorem B21034565 : Blo 1230433 21034565 := bstep (se 4 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 21034565 = 3943981) B3943981
theorem B13489739 : Blo 1230433 13489739 := bstep (se 1 (by rfl) ⟨10117304, by rfl⟩ : syracuseStep 13489739 = 20234609) B20234609
theorem B2250625 : Blo 1230433 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B2078615 : Blo 1230433 2078615 := bstep (se 1 (by rfl) ⟨1558961, by rfl⟩ : syracuseStep 2078615 = 3117923) B3117923
theorem B3946391 : Blo 1230433 3946391 := bstep (se 1 (by rfl) ⟨2959793, by rfl⟩ : syracuseStep 3946391 = 5919587) B5919587
theorem B1972247 : Blo 1230433 1972247 := bstep (se 1 (by rfl) ⟨1479185, by rfl⟩ : syracuseStep 1972247 = 2958371) B2958371
theorem B2078743 : Blo 1230433 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B6232139 : Blo 1230433 6232139 := bstep (se 1 (by rfl) ⟨4674104, by rfl⟩ : syracuseStep 6232139 = 9348209) B9348209
theorem B8001611 : Blo 1230433 8001611 := bstep (se 1 (by rfl) ⟨6001208, by rfl⟩ : syracuseStep 8001611 = 12002417) B12002417
theorem B4675715 : Blo 1230433 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B1972363 : Blo 1230433 1972363 := bstep (se 1 (by rfl) ⟨1479272, by rfl⟩ : syracuseStep 1972363 = 2958545) B2958545
theorem B7895191 : Blo 1230433 7895191 := bstep (se 1 (by rfl) ⟨5921393, by rfl⟩ : syracuseStep 7895191 = 11842787) B11842787
theorem B2496791 : Blo 1230433 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B3119411 : Blo 1230433 3119411 := bstep (se 1 (by rfl) ⟨2339558, by rfl⟩ : syracuseStep 3119411 = 4679117) B4679117
theorem B2496833 : Blo 1230433 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B2079371 : Blo 1230433 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B2079499 : Blo 1230433 2079499 := bstep (se 1 (by rfl) ⟨1559624, by rfl⟩ : syracuseStep 2079499 = 3119249) B3119249
theorem B1973081 : Blo 1230433 1973081 := bstep (se 2 (by rfl) ⟨739905, by rfl⟩ : syracuseStep 1973081 = 1479811) B1479811
theorem B2628467 : Blo 1230433 2628467 := bstep (se 1 (by rfl) ⟨1971350, by rfl⟩ : syracuseStep 2628467 = 3942701) B3942701
theorem B1711001 : Blo 1230433 1711001 := bstep (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) B1283251
theorem B2079641 : Blo 1230433 2079641 := bstep (se 2 (by rfl) ⟨779865, by rfl⟩ : syracuseStep 2079641 = 1559731) B1559731
theorem B3947467 : Blo 1230433 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B2628569 : Blo 1230433 2628569 := bstep (se 2 (by rfl) ⟨985713, by rfl⟩ : syracuseStep 2628569 = 1971427) B1971427
theorem B2497547 : Blo 1230433 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B7486481 : Blo 1230433 7486481 := bstep (se 2 (by rfl) ⟨2807430, by rfl⟩ : syracuseStep 7486481 = 5614861) B5614861
theorem B9346265 : Blo 1230433 9346265 := bstep (se 2 (by rfl) ⟨3504849, by rfl⟩ : syracuseStep 9346265 = 7009699) B7009699
theorem B2628929 : Blo 1230433 2628929 := bstep (se 2 (by rfl) ⟨985848, by rfl⟩ : syracuseStep 2628929 = 1971697) B1971697
theorem B1973593 : Blo 1230433 1973593 := bstep (se 2 (by rfl) ⟨740097, by rfl⟩ : syracuseStep 1973593 = 1480195) B1480195
theorem B5258627 : Blo 1230433 5258627 := bstep (se 1 (by rfl) ⟨3943970, by rfl⟩ : syracuseStep 5258627 = 7887941) B7887941
theorem B3505625 : Blo 1230433 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B5619203 : Blo 1230433 5619203 := bstep (se 1 (by rfl) ⟨4214402, by rfl⟩ : syracuseStep 5619203 = 8428805) B8428805
theorem B10526273 : Blo 1230433 10526273 := bstep (se 2 (by rfl) ⟨3947352, by rfl⟩ : syracuseStep 10526273 = 7894705) B7894705
theorem B1998475 : Blo 1230433 1998475 := bstep (se 1 (by rfl) ⟨1498856, by rfl⟩ : syracuseStep 1998475 = 2997713) B2997713
theorem B4800179 : Blo 1230433 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B2956979 : Blo 1230433 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B9355013 : Blo 1230433 9355013 := bstep (se 4 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 9355013 = 1754065) B1754065
theorem B2768651 : Blo 1230433 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B3505943 : Blo 1230433 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B4153139 : Blo 1230433 4153139 := bstep (se 1 (by rfl) ⟨3114854, by rfl⟩ : syracuseStep 4153139 = 6229709) B6229709
theorem B2768705 : Blo 1230433 2768705 := bstep (se 2 (by rfl) ⟨1038264, by rfl⟩ : syracuseStep 2768705 = 2076529) B2076529
theorem B6233921 : Blo 1230433 6233921 := bstep (se 2 (by rfl) ⟨2337720, by rfl⟩ : syracuseStep 6233921 = 4675441) B4675441
theorem B2531137 : Blo 1230433 2531137 := bstep (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) B1898353
theorem B1384267 : Blo 1230433 1384267 := bstep (se 1 (by rfl) ⟨1038200, by rfl⟩ : syracuseStep 1384267 = 2076401) B2076401
theorem B1384375 : Blo 1230433 1384375 := bstep (se 1 (by rfl) ⟨1038281, by rfl⟩ : syracuseStep 1384375 = 2076563) B2076563
theorem B4153355 : Blo 1230433 4153355 := bstep (se 1 (by rfl) ⟨3115016, by rfl⟩ : syracuseStep 4153355 = 6230033) B6230033
theorem B1753103 : Blo 1230433 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B2768939 : Blo 1230433 2768939 := bstep (se 1 (by rfl) ⟨2076704, by rfl⟩ : syracuseStep 2768939 = 4153409) B4153409
theorem B3997739 : Blo 1230433 3997739 := bstep (se 1 (by rfl) ⟨2998304, by rfl⟩ : syracuseStep 3997739 = 5996609) B5996609
theorem B5259325 : Blo 1230433 5259325 := bstep (se 3 (by rfl) ⟨986123, by rfl⟩ : syracuseStep 5259325 = 1972247) B1972247
theorem B4153463 : Blo 1230433 4153463 := bstep (se 1 (by rfl) ⟨3115097, by rfl⟩ : syracuseStep 4153463 = 6230195) B6230195
theorem B1663111 : Blo 1230433 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1384591 : Blo 1230433 1384591 := bstep (se 1 (by rfl) ⟨1038443, by rfl⟩ : syracuseStep 1384591 = 2076887) B2076887
theorem B2629817 : Blo 1230433 2629817 := bstep (se 2 (by rfl) ⟨986181, by rfl⟩ : syracuseStep 2629817 = 1972363) B1972363
theorem B10526921 : Blo 1230433 10526921 := bstep (se 2 (by rfl) ⟨3947595, by rfl⟩ : syracuseStep 10526921 = 7895191) B7895191
theorem B14213357 : Blo 1230433 14213357 := bstep (se 3 (by rfl) ⟨2665004, by rfl⟩ : syracuseStep 14213357 = 5330009) B5330009
theorem B2105615 : Blo 1230433 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B2769299 : Blo 1230433 2769299 := bstep (se 1 (by rfl) ⟨2076974, by rfl⟩ : syracuseStep 2769299 = 4153949) B4153949
theorem B5259667 : Blo 1230433 5259667 := bstep (se 1 (by rfl) ⟨3944750, by rfl⟩ : syracuseStep 5259667 = 7889501) B7889501
theorem B2769353 : Blo 1230433 2769353 := bstep (se 2 (by rfl) ⟨1038507, by rfl⟩ : syracuseStep 2769353 = 2077015) B2077015
theorem B17760833 : Blo 1230433 17760833 := bstep (se 2 (by rfl) ⟨6660312, by rfl⟩ : syracuseStep 17760833 = 13320625) B13320625
theorem B1385095 : Blo 1230433 1385095 := bstep (se 1 (by rfl) ⟨1038821, by rfl⟩ : syracuseStep 1385095 = 2077643) B2077643
theorem B1663673 : Blo 1230433 1663673 := bstep (se 2 (by rfl) ⟨623877, by rfl⟩ : syracuseStep 1663673 = 1247755) B1247755
theorem B4154057 : Blo 1230433 4154057 := bstep (se 2 (by rfl) ⟨1557771, by rfl⟩ : syracuseStep 4154057 = 3115543) B3115543
theorem B10658533 : Blo 1230433 10658533 := bstep (se 4 (by rfl) ⟨999237, by rfl⟩ : syracuseStep 10658533 = 1998475) B1998475
theorem B12640997 : Blo 1230433 12640997 := bstep (se 4 (by rfl) ⟨1185093, by rfl⟩ : syracuseStep 12640997 = 2370187) B2370187
theorem B1385275 : Blo 1230433 1385275 := bstep (se 1 (by rfl) ⟨1038956, by rfl⟩ : syracuseStep 1385275 = 2077913) B2077913
theorem B3326807 : Blo 1230433 3326807 := bstep (se 1 (by rfl) ⟨2495105, by rfl⟩ : syracuseStep 3326807 = 4990211) B4990211
theorem B2810771 : Blo 1230433 2810771 := bstep (se 1 (by rfl) ⟨2108078, by rfl⟩ : syracuseStep 2810771 = 4216157) B4216157
theorem B2770055 : Blo 1230433 2770055 := bstep (se 1 (by rfl) ⟨2077541, by rfl⟩ : syracuseStep 2770055 = 4155083) B4155083
theorem B3507401 : Blo 1230433 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B1385743 : Blo 1230433 1385743 := bstep (se 1 (by rfl) ⟨1039307, by rfl⟩ : syracuseStep 1385743 = 2078615) B2078615
theorem B2630927 : Blo 1230433 2630927 := bstep (se 1 (by rfl) ⟨1973195, by rfl⟩ : syracuseStep 2630927 = 3946391) B3946391
theorem B2770235 : Blo 1230433 2770235 := bstep (se 1 (by rfl) ⟨2077676, by rfl⟩ : syracuseStep 2770235 = 4155353) B4155353
theorem B3327293 : Blo 1230433 3327293 := bstep (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) B1247735
theorem B4154759 : Blo 1230433 4154759 := bstep (se 1 (by rfl) ⟨3116069, by rfl⟩ : syracuseStep 4154759 = 6232139) B6232139
theorem B5334407 : Blo 1230433 5334407 := bstep (se 1 (by rfl) ⟨4000805, by rfl⟩ : syracuseStep 5334407 = 8001611) B8001611
theorem B2770361 : Blo 1230433 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B7013891 : Blo 1230433 7013891 := bstep (se 1 (by rfl) ⟨5260418, by rfl⟩ : syracuseStep 7013891 = 10520837) B10520837
theorem B1664555 : Blo 1230433 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B35964485 : Blo 1230433 35964485 := bstep (se 4 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 35964485 = 6743341) B6743341
theorem B1230471 : Blo 1230433 1230471 := bstep (se 1 (by rfl) ⟨922853, by rfl⟩ : syracuseStep 1230471 = 1845707) B1845707
theorem B1230479 : Blo 1230433 1230479 := bstep (se 1 (by rfl) ⟨922859, by rfl⟩ : syracuseStep 1230479 = 1845719) B1845719
theorem B1230523 : Blo 1230433 1230523 := bstep (se 1 (by rfl) ⟨922892, by rfl⟩ : syracuseStep 1230523 = 1845785) B1845785
theorem B14968577 : Blo 1230433 14968577 := bstep (se 2 (by rfl) ⟨5613216, by rfl⟩ : syracuseStep 14968577 = 11226433) B11226433
theorem B4155137 : Blo 1230433 4155137 := bstep (se 2 (by rfl) ⟨1558176, by rfl⟩ : syracuseStep 4155137 = 3116353) B3116353
theorem B1230599 : Blo 1230433 1230599 := bstep (se 1 (by rfl) ⟨922949, by rfl⟩ : syracuseStep 1230599 = 1845899) B1845899
theorem B1386247 : Blo 1230433 1386247 := bstep (se 1 (by rfl) ⟨1039685, by rfl⟩ : syracuseStep 1386247 = 2079371) B2079371
theorem B1230607 : Blo 1230433 1230607 := bstep (se 1 (by rfl) ⟨922955, by rfl⟩ : syracuseStep 1230607 = 1845911) B1845911
theorem B2770703 : Blo 1230433 2770703 := bstep (se 1 (by rfl) ⟨2078027, by rfl⟩ : syracuseStep 2770703 = 4156055) B4156055
theorem B2770721 : Blo 1230433 2770721 := bstep (se 2 (by rfl) ⟨1039020, by rfl⟩ : syracuseStep 2770721 = 2078041) B2078041
theorem B2631457 : Blo 1230433 2631457 := bstep (se 2 (by rfl) ⟨986796, by rfl⟩ : syracuseStep 2631457 = 1973593) B1973593
theorem B13690673 : Blo 1230433 13690673 := bstep (se 2 (by rfl) ⟨5134002, by rfl⟩ : syracuseStep 13690673 = 10268005) B10268005
theorem B1230651 : Blo 1230433 1230651 := bstep (se 1 (by rfl) ⟨922988, by rfl⟩ : syracuseStep 1230651 = 1845977) B1845977
theorem B1230727 : Blo 1230433 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B1230735 : Blo 1230433 1230735 := bstep (se 1 (by rfl) ⟨923051, by rfl⟩ : syracuseStep 1230735 = 1846103) B1846103
theorem B1230779 : Blo 1230433 1230779 := bstep (se 1 (by rfl) ⟨923084, by rfl⟩ : syracuseStep 1230779 = 1846169) B1846169
theorem B1386427 : Blo 1230433 1386427 := bstep (se 1 (by rfl) ⟨1039820, by rfl⟩ : syracuseStep 1386427 = 2079641) B2079641
theorem B7014347 : Blo 1230433 7014347 := bstep (se 1 (by rfl) ⟨5260760, by rfl⟩ : syracuseStep 7014347 = 10521521) B10521521
theorem B1230855 : Blo 1230433 1230855 := bstep (se 1 (by rfl) ⟨923141, by rfl⟩ : syracuseStep 1230855 = 1846283) B1846283
theorem B1665031 : Blo 1230433 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B1443847 : Blo 1230433 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B4990987 : Blo 1230433 4990987 := bstep (se 1 (by rfl) ⟨3743240, by rfl⟩ : syracuseStep 4990987 = 7486481) B7486481
theorem B1230863 : Blo 1230433 1230863 := bstep (se 1 (by rfl) ⟨923147, by rfl⟩ : syracuseStep 1230863 = 1846295) B1846295
theorem B6236189 : Blo 1230433 6236189 := bstep (se 3 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 6236189 = 2338571) B2338571
theorem B3508267 : Blo 1230433 3508267 := bstep (se 1 (by rfl) ⟨2631200, by rfl⟩ : syracuseStep 3508267 = 5262401) B5262401
theorem B1230907 : Blo 1230433 1230907 := bstep (se 1 (by rfl) ⟨923180, by rfl⟩ : syracuseStep 1230907 = 1846361) B1846361
theorem B9349181 : Blo 1230433 9349181 := bstep (se 3 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 9349181 = 3505943) B3505943
theorem B2771063 : Blo 1230433 2771063 := bstep (se 1 (by rfl) ⟨2078297, by rfl⟩ : syracuseStep 2771063 = 4156595) B4156595
theorem B1230983 : Blo 1230433 1230983 := bstep (se 1 (by rfl) ⟨923237, by rfl⟩ : syracuseStep 1230983 = 1846475) B1846475
theorem B1230991 : Blo 1230433 1230991 := bstep (se 1 (by rfl) ⟨923243, by rfl⟩ : syracuseStep 1230991 = 1846487) B1846487
theorem B1231035 : Blo 1230433 1231035 := bstep (se 1 (by rfl) ⟨923276, by rfl⟩ : syracuseStep 1231035 = 1846553) B1846553
theorem B1231111 : Blo 1230433 1231111 := bstep (se 1 (by rfl) ⟨923333, by rfl⟩ : syracuseStep 1231111 = 1846667) B1846667
theorem B1231119 : Blo 1230433 1231119 := bstep (se 1 (by rfl) ⟨923339, by rfl⟩ : syracuseStep 1231119 = 1846679) B1846679
theorem B2771243 : Blo 1230433 2771243 := bstep (se 1 (by rfl) ⟨2078432, by rfl⟩ : syracuseStep 2771243 = 4156865) B4156865
theorem B2337083 : Blo 1230433 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B1231163 : Blo 1230433 1231163 := bstep (se 1 (by rfl) ⟨923372, by rfl⟩ : syracuseStep 1231163 = 1846745) B1846745
theorem B3508541 : Blo 1230433 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B3746135 : Blo 1230433 3746135 := bstep (se 1 (by rfl) ⟨2809601, by rfl⟩ : syracuseStep 3746135 = 5619203) B5619203
theorem B1231239 : Blo 1230433 1231239 := bstep (se 1 (by rfl) ⟨923429, by rfl⟩ : syracuseStep 1231239 = 1846859) B1846859
theorem B1231247 : Blo 1230433 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B1845689 : Blo 1230433 1845689 := bstep (se 2 (by rfl) ⟨692133, by rfl⟩ : syracuseStep 1845689 = 1384267) B1384267
theorem B1231291 : Blo 1230433 1231291 := bstep (se 1 (by rfl) ⟨923468, by rfl⟩ : syracuseStep 1231291 = 1846937) B1846937
theorem B3000833 : Blo 1230433 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B6236675 : Blo 1230433 6236675 := bstep (se 1 (by rfl) ⟨4677506, by rfl⟩ : syracuseStep 6236675 = 9355013) B9355013
theorem B1845767 : Blo 1230433 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B1231367 : Blo 1230433 1231367 := bstep (se 1 (by rfl) ⟨923525, by rfl⟩ : syracuseStep 1231367 = 1847051) B1847051
theorem B1231375 : Blo 1230433 1231375 := bstep (se 1 (by rfl) ⟨923531, by rfl⟩ : syracuseStep 1231375 = 1847063) B1847063
theorem B1845803 : Blo 1230433 1845803 := bstep (se 1 (by rfl) ⟨1384352, by rfl⟩ : syracuseStep 1845803 = 2768705) B2768705
theorem B4155947 : Blo 1230433 4155947 := bstep (se 1 (by rfl) ⟨3116960, by rfl⟩ : syracuseStep 4155947 = 6233921) B6233921
theorem B1559083 : Blo 1230433 1559083 := bstep (se 1 (by rfl) ⟨1169312, by rfl⟩ : syracuseStep 1559083 = 2338625) B2338625
theorem B1231419 : Blo 1230433 1231419 := bstep (se 1 (by rfl) ⟨923564, by rfl⟩ : syracuseStep 1231419 = 1847129) B1847129
theorem B1845833 : Blo 1230433 1845833 := bstep (se 2 (by rfl) ⟨692187, by rfl⟩ : syracuseStep 1845833 = 1384375) B1384375
theorem B7015031 : Blo 1230433 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B3115655 : Blo 1230433 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B1231495 : Blo 1230433 1231495 := bstep (se 1 (by rfl) ⟨923621, by rfl⟩ : syracuseStep 1231495 = 1847243) B1847243
theorem B1231503 : Blo 1230433 1231503 := bstep (se 1 (by rfl) ⟨923627, by rfl⟩ : syracuseStep 1231503 = 1847255) B1847255
theorem B2771603 : Blo 1230433 2771603 := bstep (se 1 (by rfl) ⟨2078702, by rfl⟩ : syracuseStep 2771603 = 4157405) B4157405
theorem B3508883 : Blo 1230433 3508883 := bstep (se 1 (by rfl) ⟨2631662, by rfl⟩ : syracuseStep 3508883 = 5263325) B5263325
theorem B3115705 : Blo 1230433 3115705 := bstep (se 2 (by rfl) ⟨1168389, by rfl⟩ : syracuseStep 3115705 = 2336779) B2336779
theorem B1845947 : Blo 1230433 1845947 := bstep (se 1 (by rfl) ⟨1384460, by rfl⟩ : syracuseStep 1845947 = 2768921) B2768921
theorem B1231547 : Blo 1230433 1231547 := bstep (se 1 (by rfl) ⟨923660, by rfl⟩ : syracuseStep 1231547 = 1847321) B1847321
theorem B2771657 : Blo 1230433 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B5696201 : Blo 1230433 5696201 := bstep (se 2 (by rfl) ⟨2136075, by rfl⟩ : syracuseStep 5696201 = 4272151) B4272151
theorem B11995865 : Blo 1230433 11995865 := bstep (se 2 (by rfl) ⟨4498449, by rfl⟩ : syracuseStep 11995865 = 8996899) B8996899
theorem B1846007 : Blo 1230433 1846007 := bstep (se 1 (by rfl) ⟨1384505, by rfl⟩ : syracuseStep 1846007 = 2769011) B2769011
theorem B1231623 : Blo 1230433 1231623 := bstep (se 1 (by rfl) ⟨923717, by rfl⟩ : syracuseStep 1231623 = 1847435) B1847435
theorem B1846031 : Blo 1230433 1846031 := bstep (se 1 (by rfl) ⟨1384523, by rfl⟩ : syracuseStep 1846031 = 2769047) B2769047
theorem B1231631 : Blo 1230433 1231631 := bstep (se 1 (by rfl) ⟨923723, by rfl⟩ : syracuseStep 1231631 = 1847447) B1847447
theorem B2337569 : Blo 1230433 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B9988913 : Blo 1230433 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B1846073 : Blo 1230433 1846073 := bstep (se 2 (by rfl) ⟨692277, by rfl⟩ : syracuseStep 1846073 = 1384555) B1384555
theorem B1231675 : Blo 1230433 1231675 := bstep (se 1 (by rfl) ⟨923756, by rfl⟩ : syracuseStep 1231675 = 1847513) B1847513
theorem B3328883 : Blo 1230433 3328883 := bstep (se 1 (by rfl) ⟨2496662, by rfl⟩ : syracuseStep 3328883 = 4993325) B4993325
theorem B1846151 : Blo 1230433 1846151 := bstep (se 1 (by rfl) ⟨1384613, by rfl⟩ : syracuseStep 1846151 = 2769227) B2769227
theorem B1231751 : Blo 1230433 1231751 := bstep (se 1 (by rfl) ⟨923813, by rfl⟩ : syracuseStep 1231751 = 1847627) B1847627
theorem B1231759 : Blo 1230433 1231759 := bstep (se 1 (by rfl) ⟨923819, by rfl⟩ : syracuseStep 1231759 = 1847639) B1847639
theorem B13306787 : Blo 1230433 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B1846187 : Blo 1230433 1846187 := bstep (se 1 (by rfl) ⟨1384640, by rfl⟩ : syracuseStep 1846187 = 2769281) B2769281
theorem B1231803 : Blo 1230433 1231803 := bstep (se 1 (by rfl) ⟨923852, by rfl⟩ : syracuseStep 1231803 = 1847705) B1847705
theorem B1846217 : Blo 1230433 1846217 := bstep (se 2 (by rfl) ⟨692331, by rfl⟩ : syracuseStep 1846217 = 1384663) B1384663
theorem B1231879 : Blo 1230433 1231879 := bstep (se 1 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 1231879 = 1847819) B1847819
theorem B1231887 : Blo 1230433 1231887 := bstep (se 1 (by rfl) ⟨923915, by rfl⟩ : syracuseStep 1231887 = 1847831) B1847831
theorem B2337835 : Blo 1230433 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B1846331 : Blo 1230433 1846331 := bstep (se 1 (by rfl) ⟨1384748, by rfl⟩ : syracuseStep 1846331 = 2769497) B2769497
theorem B1231931 : Blo 1230433 1231931 := bstep (se 1 (by rfl) ⟨923948, by rfl⟩ : syracuseStep 1231931 = 1847897) B1847897
theorem B5614679 : Blo 1230433 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B1846391 : Blo 1230433 1846391 := bstep (se 1 (by rfl) ⟨1384793, by rfl⟩ : syracuseStep 1846391 = 2769587) B2769587
theorem B1232007 : Blo 1230433 1232007 := bstep (se 1 (by rfl) ⟨924005, by rfl⟩ : syracuseStep 1232007 = 1848011) B1848011
theorem B1846415 : Blo 1230433 1846415 := bstep (se 1 (by rfl) ⟨1384811, by rfl⟩ : syracuseStep 1846415 = 2769623) B2769623
theorem B1232015 : Blo 1230433 1232015 := bstep (se 1 (by rfl) ⟨924011, by rfl⟩ : syracuseStep 1232015 = 1848023) B1848023
theorem B1846457 : Blo 1230433 1846457 := bstep (se 2 (by rfl) ⟨692421, by rfl⟩ : syracuseStep 1846457 = 1384843) B1384843
theorem B1232059 : Blo 1230433 1232059 := bstep (se 1 (by rfl) ⟨924044, by rfl⟩ : syracuseStep 1232059 = 1848089) B1848089
theorem B1846535 : Blo 1230433 1846535 := bstep (se 1 (by rfl) ⟨1384901, by rfl⟩ : syracuseStep 1846535 = 2769803) B2769803
theorem B1232135 : Blo 1230433 1232135 := bstep (se 1 (by rfl) ⟨924101, by rfl⟩ : syracuseStep 1232135 = 1848203) B1848203
theorem B3116303 : Blo 1230433 3116303 := bstep (se 1 (by rfl) ⟨2337227, by rfl⟩ : syracuseStep 3116303 = 4674455) B4674455
theorem B1232143 : Blo 1230433 1232143 := bstep (se 1 (by rfl) ⟨924107, by rfl⟩ : syracuseStep 1232143 = 1848215) B1848215
theorem B1846571 : Blo 1230433 1846571 := bstep (se 1 (by rfl) ⟨1384928, by rfl⟩ : syracuseStep 1846571 = 2769857) B2769857
theorem B1232187 : Blo 1230433 1232187 := bstep (se 1 (by rfl) ⟨924140, by rfl⟩ : syracuseStep 1232187 = 1848281) B1848281
theorem B1846601 : Blo 1230433 1846601 := bstep (se 2 (by rfl) ⟨692475, by rfl⟩ : syracuseStep 1846601 = 1384951) B1384951
theorem B10513799 : Blo 1230433 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B2772359 : Blo 1230433 2772359 := bstep (se 1 (by rfl) ⟨2079269, by rfl⟩ : syracuseStep 2772359 = 4158539) B4158539
theorem B1232263 : Blo 1230433 1232263 := bstep (se 1 (by rfl) ⟨924197, by rfl⟩ : syracuseStep 1232263 = 1848395) B1848395
theorem B1314191 : Blo 1230433 1314191 := bstep (se 1 (by rfl) ⟨985643, by rfl⟩ : syracuseStep 1314191 = 1971287) B1971287
theorem B1232271 : Blo 1230433 1232271 := bstep (se 1 (by rfl) ⟨924203, by rfl⟩ : syracuseStep 1232271 = 1848407) B1848407
theorem B1846715 : Blo 1230433 1846715 := bstep (se 1 (by rfl) ⟨1385036, by rfl⟩ : syracuseStep 1846715 = 2770073) B2770073
theorem B1232315 : Blo 1230433 1232315 := bstep (se 1 (by rfl) ⟨924236, by rfl⟩ : syracuseStep 1232315 = 1848473) B1848473
theorem B1846775 : Blo 1230433 1846775 := bstep (se 1 (by rfl) ⟨1385081, by rfl⟩ : syracuseStep 1846775 = 2770163) B2770163
theorem B6319619 : Blo 1230433 6319619 := bstep (se 1 (by rfl) ⟨4739714, by rfl⟩ : syracuseStep 6319619 = 9479429) B9479429
theorem B1232391 : Blo 1230433 1232391 := bstep (se 1 (by rfl) ⟨924293, by rfl⟩ : syracuseStep 1232391 = 1848587) B1848587
theorem B1846799 : Blo 1230433 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B1232399 : Blo 1230433 1232399 := bstep (se 1 (by rfl) ⟨924299, by rfl⟩ : syracuseStep 1232399 = 1848599) B1848599
theorem B6229547 : Blo 1230433 6229547 := bstep (se 1 (by rfl) ⟨4672160, by rfl⟩ : syracuseStep 6229547 = 9344321) B9344321
theorem B2666027 : Blo 1230433 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B1846841 : Blo 1230433 1846841 := bstep (se 2 (by rfl) ⟨692565, by rfl⟩ : syracuseStep 1846841 = 1385131) B1385131
theorem B2772539 : Blo 1230433 2772539 := bstep (se 1 (by rfl) ⟨2079404, by rfl⟩ : syracuseStep 2772539 = 4158809) B4158809
theorem B1846919 : Blo 1230433 1846919 := bstep (se 1 (by rfl) ⟨1385189, by rfl⟩ : syracuseStep 1846919 = 2770379) B2770379
theorem B1846955 : Blo 1230433 1846955 := bstep (se 1 (by rfl) ⟨1385216, by rfl⟩ : syracuseStep 1846955 = 2770433) B2770433
theorem B2772665 : Blo 1230433 2772665 := bstep (se 2 (by rfl) ⟨1039749, by rfl⟩ : syracuseStep 2772665 = 2079499) B2079499
theorem B1846985 : Blo 1230433 1846985 := bstep (se 2 (by rfl) ⟨692619, by rfl⟩ : syracuseStep 1846985 = 1385239) B1385239
theorem B7008059 : Blo 1230433 7008059 := bstep (se 1 (by rfl) ⟨5256044, by rfl⟩ : syracuseStep 7008059 = 10512089) B10512089
theorem B2076475 : Blo 1230433 2076475 := bstep (se 1 (by rfl) ⟨1557356, by rfl⟩ : syracuseStep 2076475 = 3114713) B3114713
theorem B1847099 : Blo 1230433 1847099 := bstep (se 1 (by rfl) ⟨1385324, by rfl⟩ : syracuseStep 1847099 = 2770649) B2770649
theorem B4157243 : Blo 1230433 4157243 := bstep (se 1 (by rfl) ⟨3117932, by rfl⟩ : syracuseStep 4157243 = 6235865) B6235865
theorem B1847159 : Blo 1230433 1847159 := bstep (se 1 (by rfl) ⟨1385369, by rfl⟩ : syracuseStep 1847159 = 2770739) B2770739
theorem B2666375 : Blo 1230433 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B1847183 : Blo 1230433 1847183 := bstep (se 1 (by rfl) ⟨1385387, by rfl⟩ : syracuseStep 1847183 = 2770775) B2770775
theorem B26619799 : Blo 1230433 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1847225 : Blo 1230433 1847225 := bstep (se 2 (by rfl) ⟨692709, by rfl⟩ : syracuseStep 1847225 = 1385419) B1385419
theorem B5263289 : Blo 1230433 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B2076617 : Blo 1230433 2076617 := bstep (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) B1557463
theorem B3117001 : Blo 1230433 3117001 := bstep (se 2 (by rfl) ⟨1168875, by rfl⟩ : syracuseStep 3117001 = 2337751) B2337751
theorem B1847303 : Blo 1230433 1847303 := bstep (se 1 (by rfl) ⟨1385477, by rfl⟩ : syracuseStep 1847303 = 2770955) B2770955
theorem B25260055 : Blo 1230433 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B1847339 : Blo 1230433 1847339 := bstep (se 1 (by rfl) ⟨1385504, by rfl⟩ : syracuseStep 1847339 = 2771009) B2771009
theorem B1847369 : Blo 1230433 1847369 := bstep (se 2 (by rfl) ⟨692763, by rfl⟩ : syracuseStep 1847369 = 1385527) B1385527
theorem B3117143 : Blo 1230433 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B6238295 : Blo 1230433 6238295 := bstep (se 1 (by rfl) ⟨4678721, by rfl⟩ : syracuseStep 6238295 = 9357443) B9357443
theorem B23687261 : Blo 1230433 23687261 := bstep (se 3 (by rfl) ⟨4441361, by rfl⟩ : syracuseStep 23687261 = 8882723) B8882723
theorem B2338951 : Blo 1230433 2338951 := bstep (se 1 (by rfl) ⟨1754213, by rfl⟩ : syracuseStep 2338951 = 3508427) B3508427
theorem B1847483 : Blo 1230433 1847483 := bstep (se 1 (by rfl) ⟨1385612, by rfl⟩ : syracuseStep 1847483 = 2771225) B2771225
theorem B1847543 : Blo 1230433 1847543 := bstep (se 1 (by rfl) ⟨1385657, by rfl⟩ : syracuseStep 1847543 = 2771315) B2771315
theorem B1847567 : Blo 1230433 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B4157729 : Blo 1230433 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B1847609 : Blo 1230433 1847609 := bstep (se 2 (by rfl) ⟨692853, by rfl⟩ : syracuseStep 1847609 = 1385707) B1385707
theorem B1847687 : Blo 1230433 1847687 := bstep (se 1 (by rfl) ⟨1385765, by rfl⟩ : syracuseStep 1847687 = 2771531) B2771531
theorem B1847723 : Blo 1230433 1847723 := bstep (se 1 (by rfl) ⟨1385792, by rfl⟩ : syracuseStep 1847723 = 2771585) B2771585
theorem B1847753 : Blo 1230433 1847753 := bstep (se 2 (by rfl) ⟨692907, by rfl⟩ : syracuseStep 1847753 = 1385815) B1385815
theorem B12800477 : Blo 1230433 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B7016989 : Blo 1230433 7016989 := bstep (se 3 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 7016989 = 2631371) B2631371
theorem B1315387 : Blo 1230433 1315387 := bstep (se 1 (by rfl) ⟨986540, by rfl⟩ : syracuseStep 1315387 = 1973081) B1973081
theorem B1847867 : Blo 1230433 1847867 := bstep (se 1 (by rfl) ⟨1385900, by rfl⟩ : syracuseStep 1847867 = 2771801) B2771801
theorem B6238781 : Blo 1230433 6238781 := bstep (se 3 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 6238781 = 2339543) B2339543
theorem B1847927 : Blo 1230433 1847927 := bstep (se 1 (by rfl) ⟨1385945, by rfl⟩ : syracuseStep 1847927 = 2771891) B2771891
theorem B14037623 : Blo 1230433 14037623 := bstep (se 1 (by rfl) ⟨10528217, by rfl⟩ : syracuseStep 14037623 = 21056435) B21056435
theorem B2077319 : Blo 1230433 2077319 := bstep (se 1 (by rfl) ⟨1557989, by rfl⟩ : syracuseStep 2077319 = 3115979) B3115979
theorem B1847951 : Blo 1230433 1847951 := bstep (se 1 (by rfl) ⟨1385963, by rfl⟩ : syracuseStep 1847951 = 2771927) B2771927
theorem B1847993 : Blo 1230433 1847993 := bstep (se 2 (by rfl) ⟨692997, by rfl⟩ : syracuseStep 1847993 = 1385995) B1385995
theorem B2339513 : Blo 1230433 2339513 := bstep (se 2 (by rfl) ⟨877317, by rfl⟩ : syracuseStep 2339513 = 1754635) B1754635
theorem B3945161 : Blo 1230433 3945161 := bstep (se 2 (by rfl) ⟨1479435, by rfl⟩ : syracuseStep 3945161 = 2958871) B2958871
theorem B4993793 : Blo 1230433 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B1848071 : Blo 1230433 1848071 := bstep (se 1 (by rfl) ⟨1386053, by rfl⟩ : syracuseStep 1848071 = 2772107) B2772107
theorem B12636965 : Blo 1230433 12636965 := bstep (se 4 (by rfl) ⟨1184715, by rfl⟩ : syracuseStep 12636965 = 2369431) B2369431
theorem B1848107 : Blo 1230433 1848107 := bstep (se 1 (by rfl) ⟨1386080, by rfl⟩ : syracuseStep 1848107 = 2772161) B2772161
theorem B6230843 : Blo 1230433 6230843 := bstep (se 1 (by rfl) ⟨4673132, by rfl⟩ : syracuseStep 6230843 = 9346265) B9346265
theorem B1848137 : Blo 1230433 1848137 := bstep (se 2 (by rfl) ⟨693051, by rfl⟩ : syracuseStep 1848137 = 1386103) B1386103
theorem B4158323 : Blo 1230433 4158323 := bstep (se 1 (by rfl) ⟨3118742, by rfl⟩ : syracuseStep 4158323 = 6237485) B6237485
theorem B1848251 : Blo 1230433 1848251 := bstep (se 1 (by rfl) ⟨1386188, by rfl⟩ : syracuseStep 1848251 = 2772377) B2772377
theorem B1971145 : Blo 1230433 1971145 := bstep (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) B1478359
theorem B6231005 : Blo 1230433 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B1848311 : Blo 1230433 1848311 := bstep (se 1 (by rfl) ⟨1386233, by rfl⟩ : syracuseStep 1848311 = 2772467) B2772467
theorem B1848335 : Blo 1230433 1848335 := bstep (se 1 (by rfl) ⟨1386251, by rfl⟩ : syracuseStep 1848335 = 2772503) B2772503
theorem B7017515 : Blo 1230433 7017515 := bstep (se 1 (by rfl) ⟨5263136, by rfl⟩ : syracuseStep 7017515 = 10526273) B10526273
theorem B1848377 : Blo 1230433 1848377 := bstep (se 2 (by rfl) ⟨693141, by rfl⟩ : syracuseStep 1848377 = 1386283) B1386283
theorem B1971319 : Blo 1230433 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B1848455 : Blo 1230433 1848455 := bstep (se 1 (by rfl) ⟨1386341, by rfl⟩ : syracuseStep 1848455 = 2772683) B2772683
theorem B1848491 : Blo 1230433 1848491 := bstep (se 1 (by rfl) ⟨1386368, by rfl⟩ : syracuseStep 1848491 = 2772737) B2772737
theorem B1848521 : Blo 1230433 1848521 := bstep (se 2 (by rfl) ⟨693195, by rfl⟩ : syracuseStep 1848521 = 1386391) B1386391
theorem B7009517 : Blo 1230433 7009517 := bstep (se 3 (by rfl) ⟨1314284, by rfl⟩ : syracuseStep 7009517 = 2628569) B2628569
theorem B2077967 : Blo 1230433 2077967 := bstep (se 1 (by rfl) ⟨1558475, by rfl⟩ : syracuseStep 2077967 = 3116951) B3116951
theorem B6231329 : Blo 1230433 6231329 := bstep (se 2 (by rfl) ⟨2336748, by rfl⟩ : syracuseStep 6231329 = 4673497) B4673497
theorem B1848635 : Blo 1230433 1848635 := bstep (se 1 (by rfl) ⟨1386476, by rfl⟩ : syracuseStep 1848635 = 2772953) B2772953
theorem B9352583 : Blo 1230433 9352583 := bstep (se 1 (by rfl) ⟨7014437, by rfl⟩ : syracuseStep 9352583 = 14028875) B14028875
theorem B4216211 : Blo 1230433 4216211 := bstep (se 1 (by rfl) ⟨3162158, by rfl⟩ : syracuseStep 4216211 = 6324317) B6324317
theorem B72955313 : Blo 1230433 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B118494737 : Blo 1230433 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B4994831 : Blo 1230433 4994831 := bstep (se 1 (by rfl) ⟨3746123, by rfl⟩ : syracuseStep 4994831 = 7492247) B7492247
theorem B2078507 : Blo 1230433 2078507 := bstep (se 1 (by rfl) ⟨1558880, by rfl⟩ : syracuseStep 2078507 = 3117761) B3117761
theorem B25966453 : Blo 1230433 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B3504019 : Blo 1230433 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B3741755 : Blo 1230433 3741755 := bstep (se 1 (by rfl) ⟨2806316, by rfl⟩ : syracuseStep 3741755 = 5612633) B5612633
theorem B6658109 : Blo 1230433 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B3119219 : Blo 1230433 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2078905 : Blo 1230433 2078905 := bstep (se 2 (by rfl) ⟨779589, by rfl⟩ : syracuseStep 2078905 = 1559179) B1559179
theorem B6232301 : Blo 1230433 6232301 := bstep (se 3 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 6232301 = 2337113) B2337113
theorem B14023043 : Blo 1230433 14023043 := bstep (se 1 (by rfl) ⟨10517282, by rfl⟩ : syracuseStep 14023043 = 21034565) B21034565
theorem B8993159 : Blo 1230433 8993159 := bstep (se 1 (by rfl) ⟨6744869, by rfl⟩ : syracuseStep 8993159 = 13489739) B13489739
theorem B7018973 : Blo 1230433 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B9124609 : Blo 1230433 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B4742003 : Blo 1230433 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B2079607 : Blo 1230433 2079607 := bstep (se 1 (by rfl) ⟨1559705, by rfl⟩ : syracuseStep 2079607 = 3119411) B3119411
theorem B3947417 : Blo 1230433 3947417 := bstep (se 2 (by rfl) ⟨1480281, by rfl⟩ : syracuseStep 3947417 = 2960563) B2960563
theorem B6233111 : Blo 1230433 6233111 := bstep (se 1 (by rfl) ⟨4674833, by rfl⟩ : syracuseStep 6233111 = 9349667) B9349667
theorem B7109869 : Blo 1230433 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B1752311 : Blo 1230433 1752311 := bstep (se 1 (by rfl) ⟨1314233, by rfl⟩ : syracuseStep 1752311 = 2628467) B2628467
theorem B2219297 : Blo 1230433 2219297 := bstep (se 2 (by rfl) ⟨832236, by rfl⟩ : syracuseStep 2219297 = 1664473) B1664473
theorem B4152761 : Blo 1230433 4152761 := bstep (se 2 (by rfl) ⟨1557285, by rfl⟩ : syracuseStep 4152761 = 3114571) B3114571
theorem B3505693 : Blo 1230433 3505693 := bstep (se 3 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 3505693 = 1314635) B1314635
theorem B1752619 : Blo 1230433 1752619 := bstep (se 1 (by rfl) ⟨1314464, by rfl⟩ : syracuseStep 1752619 = 2628929) B2628929
theorem B7888427 : Blo 1230433 7888427 := bstep (se 1 (by rfl) ⟨5916320, by rfl⟩ : syracuseStep 7888427 = 11832641) B11832641
theorem B3505751 : Blo 1230433 3505751 := bstep (se 1 (by rfl) ⟨2629313, by rfl⟩ : syracuseStep 3505751 = 5258627) B5258627
theorem B2809529 : Blo 1230433 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B4562669 : Blo 1230433 4562669 := bstep (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) B1711001
theorem B3374849 : Blo 1230433 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B2768759 : Blo 1230433 2768759 := bstep (se 1 (by rfl) ⟨2076569, by rfl⟩ : syracuseStep 2768759 = 4153139) B4153139
theorem B2768903 : Blo 1230433 2768903 := bstep (se 1 (by rfl) ⟨2076677, by rfl⟩ : syracuseStep 2768903 = 4153355) B4153355
theorem B2220041 : Blo 1230433 2220041 := bstep (se 2 (by rfl) ⟨832515, by rfl⟩ : syracuseStep 2220041 = 1665031) B1665031
theorem B1925129 : Blo 1230433 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B4677689 : Blo 1230433 4677689 := bstep (se 2 (by rfl) ⟨1754133, by rfl⟩ : syracuseStep 4677689 = 3508267) B3508267
theorem B2768975 : Blo 1230433 2768975 := bstep (se 1 (by rfl) ⟨2076731, by rfl⟩ : syracuseStep 2768975 = 4153463) B4153463
theorem B7012433 : Blo 1230433 7012433 := bstep (se 2 (by rfl) ⟨2629662, by rfl⟩ : syracuseStep 7012433 = 5259325) B5259325
theorem B1753211 : Blo 1230433 1753211 := bstep (se 1 (by rfl) ⟨1314908, by rfl⟩ : syracuseStep 1753211 = 2629817) B2629817
theorem B9978013 : Blo 1230433 9978013 := bstep (se 3 (by rfl) ⟨1870877, by rfl⟩ : syracuseStep 9978013 = 3741755) B3741755
theorem B1384879 : Blo 1230433 1384879 := bstep (se 1 (by rfl) ⟨1038659, by rfl⟩ : syracuseStep 1384879 = 2077319) B2077319
theorem B2769371 : Blo 1230433 2769371 := bstep (se 1 (by rfl) ⟨2077028, by rfl⟩ : syracuseStep 2769371 = 4154057) B4154057
theorem B2630107 : Blo 1230433 2630107 := bstep (se 1 (by rfl) ⟨1972580, by rfl⟩ : syracuseStep 2630107 = 3945161) B3945161
theorem B7012889 : Blo 1230433 7012889 := bstep (se 2 (by rfl) ⟨2629833, by rfl⟩ : syracuseStep 7012889 = 5259667) B5259667
theorem B4153895 : Blo 1230433 4153895 := bstep (se 1 (by rfl) ⟨3115421, by rfl⟩ : syracuseStep 4153895 = 6230843) B6230843
theorem B4154003 : Blo 1230433 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B4678343 : Blo 1230433 4678343 := bstep (se 1 (by rfl) ⟨3508757, by rfl⟩ : syracuseStep 4678343 = 7017515) B7017515
theorem B9355985 : Blo 1230433 9355985 := bstep (se 2 (by rfl) ⟨3508494, by rfl⟩ : syracuseStep 9355985 = 7016989) B7016989
theorem B1753849 : Blo 1230433 1753849 := bstep (se 2 (by rfl) ⟨657693, by rfl⟩ : syracuseStep 1753849 = 1315387) B1315387
theorem B1385311 : Blo 1230433 1385311 := bstep (se 1 (by rfl) ⟨1038983, by rfl⟩ : syracuseStep 1385311 = 2077967) B2077967
theorem B4154219 : Blo 1230433 4154219 := bstep (se 1 (by rfl) ⟨3115664, by rfl⟩ : syracuseStep 4154219 = 6231329) B6231329
theorem B4154273 : Blo 1230433 4154273 := bstep (se 2 (by rfl) ⟨1557852, by rfl⟩ : syracuseStep 4154273 = 3115705) B3115705
theorem B2769839 : Blo 1230433 2769839 := bstep (se 1 (by rfl) ⟨2077379, by rfl⟩ : syracuseStep 2769839 = 4154759) B4154759
theorem B6235055 : Blo 1230433 6235055 := bstep (se 1 (by rfl) ⟨4676291, by rfl⟩ : syracuseStep 6235055 = 9352583) B9352583
theorem B3556271 : Blo 1230433 3556271 := bstep (se 1 (by rfl) ⟨2667203, by rfl⟩ : syracuseStep 3556271 = 5334407) B5334407
theorem B2810807 : Blo 1230433 2810807 := bstep (se 1 (by rfl) ⟨2108105, by rfl⟩ : syracuseStep 2810807 = 4216211) B4216211
theorem B48636875 : Blo 1230433 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B12166145 : Blo 1230433 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B78996491 : Blo 1230433 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B9979051 : Blo 1230433 9979051 := bstep (se 1 (by rfl) ⟨7484288, by rfl⟩ : syracuseStep 9979051 = 14968577) B14968577
theorem B2770091 : Blo 1230433 2770091 := bstep (se 1 (by rfl) ⟨2077568, by rfl⟩ : syracuseStep 2770091 = 4155137) B4155137
theorem B1385671 : Blo 1230433 1385671 := bstep (se 1 (by rfl) ⟨1039253, by rfl⟩ : syracuseStep 1385671 = 2078507) B2078507
theorem B9127115 : Blo 1230433 9127115 := bstep (se 1 (by rfl) ⟨6845336, by rfl⟩ : syracuseStep 9127115 = 13690673) B13690673
theorem B4154867 : Blo 1230433 4154867 := bstep (se 1 (by rfl) ⟨3116150, by rfl⟩ : syracuseStep 4154867 = 6232301) B6232301
theorem B1558055 : Blo 1230433 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B9348695 : Blo 1230433 9348695 := bstep (se 1 (by rfl) ⟨7011521, by rfl⟩ : syracuseStep 9348695 = 14023043) B14023043
theorem B1230459 : Blo 1230433 1230459 := bstep (se 1 (by rfl) ⟨922844, by rfl⟩ : syracuseStep 1230459 = 1845689) B1845689
theorem B9479825 : Blo 1230433 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B4679315 : Blo 1230433 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B2000555 : Blo 1230433 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B1230511 : Blo 1230433 1230511 := bstep (se 1 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 1230511 = 1845767) B1845767
theorem B1230535 : Blo 1230433 1230535 := bstep (se 1 (by rfl) ⟨922901, by rfl⟩ : syracuseStep 1230535 = 1845803) B1845803
theorem B2770631 : Blo 1230433 2770631 := bstep (se 1 (by rfl) ⟨2077973, by rfl⟩ : syracuseStep 2770631 = 4155947) B4155947
theorem B1230555 : Blo 1230433 1230555 := bstep (se 1 (by rfl) ⟨922916, by rfl⟩ : syracuseStep 1230555 = 1845833) B1845833
theorem B1230631 : Blo 1230433 1230631 := bstep (se 1 (by rfl) ⟨922973, by rfl⟩ : syracuseStep 1230631 = 1845947) B1845947
theorem B7997243 : Blo 1230433 7997243 := bstep (se 1 (by rfl) ⟨5997932, by rfl⟩ : syracuseStep 7997243 = 11995865) B11995865
theorem B1230671 : Blo 1230433 1230671 := bstep (se 1 (by rfl) ⟨923003, by rfl⟩ : syracuseStep 1230671 = 1846007) B1846007
theorem B1230687 : Blo 1230433 1230687 := bstep (se 1 (by rfl) ⟨923015, by rfl⟩ : syracuseStep 1230687 = 1846031) B1846031
theorem B1558379 : Blo 1230433 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B15189869 : Blo 1230433 15189869 := bstep (se 3 (by rfl) ⟨2848100, by rfl⟩ : syracuseStep 15189869 = 5696201) B5696201
theorem B1230715 : Blo 1230433 1230715 := bstep (se 1 (by rfl) ⟨923036, by rfl⟩ : syracuseStep 1230715 = 1846073) B1846073
theorem B1230767 : Blo 1230433 1230767 := bstep (se 1 (by rfl) ⟨923075, by rfl⟩ : syracuseStep 1230767 = 1846151) B1846151
theorem B2631611 : Blo 1230433 2631611 := bstep (se 1 (by rfl) ⟨1973708, by rfl⟩ : syracuseStep 2631611 = 3947417) B3947417
theorem B1230791 : Blo 1230433 1230791 := bstep (se 1 (by rfl) ⟨923093, by rfl⟩ : syracuseStep 1230791 = 1846187) B1846187
theorem B12167117 : Blo 1230433 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B1230811 : Blo 1230433 1230811 := bstep (se 1 (by rfl) ⟨923108, by rfl⟩ : syracuseStep 1230811 = 1846217) B1846217
theorem B4155407 : Blo 1230433 4155407 := bstep (se 1 (by rfl) ⟨3116555, by rfl⟩ : syracuseStep 4155407 = 6233111) B6233111
theorem B1230887 : Blo 1230433 1230887 := bstep (se 1 (by rfl) ⟨923165, by rfl⟩ : syracuseStep 1230887 = 1846331) B1846331
theorem B2336825 : Blo 1230433 2336825 := bstep (se 2 (by rfl) ⟨876309, by rfl⟩ : syracuseStep 2336825 = 1752619) B1752619
theorem B1230927 : Blo 1230433 1230927 := bstep (se 1 (by rfl) ⟨923195, by rfl⟩ : syracuseStep 1230927 = 1846391) B1846391
theorem B1230943 : Blo 1230433 1230943 := bstep (se 1 (by rfl) ⟨923207, by rfl⟩ : syracuseStep 1230943 = 1846415) B1846415
theorem B1230971 : Blo 1230433 1230971 := bstep (se 1 (by rfl) ⟨923228, by rfl⟩ : syracuseStep 1230971 = 1846457) B1846457
theorem B1231023 : Blo 1230433 1231023 := bstep (se 1 (by rfl) ⟨923267, by rfl⟩ : syracuseStep 1231023 = 1846535) B1846535
theorem B1231047 : Blo 1230433 1231047 := bstep (se 1 (by rfl) ⟨923285, by rfl⟩ : syracuseStep 1231047 = 1846571) B1846571
theorem B1231067 : Blo 1230433 1231067 := bstep (se 1 (by rfl) ⟨923300, by rfl⟩ : syracuseStep 1231067 = 1846601) B1846601
theorem B1231143 : Blo 1230433 1231143 := bstep (se 1 (by rfl) ⟨923357, by rfl⟩ : syracuseStep 1231143 = 1846715) B1846715
theorem B1231183 : Blo 1230433 1231183 := bstep (se 1 (by rfl) ⟨923387, by rfl⟩ : syracuseStep 1231183 = 1846775) B1846775
theorem B4213079 : Blo 1230433 4213079 := bstep (se 1 (by rfl) ⟨3159809, by rfl⟩ : syracuseStep 4213079 = 6319619) B6319619
theorem B1231199 : Blo 1230433 1231199 := bstep (se 1 (by rfl) ⟨923399, by rfl⟩ : syracuseStep 1231199 = 1846799) B1846799
theorem B1231227 : Blo 1230433 1231227 := bstep (se 1 (by rfl) ⟨923420, by rfl⟩ : syracuseStep 1231227 = 1846841) B1846841
theorem B3508609 : Blo 1230433 3508609 := bstep (se 2 (by rfl) ⟨1315728, by rfl⟩ : syracuseStep 3508609 = 2631457) B2631457
theorem B10512773 : Blo 1230433 10512773 := bstep (se 4 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 10512773 = 1971145) B1971145
theorem B2337167 : Blo 1230433 2337167 := bstep (se 1 (by rfl) ⟨1752875, by rfl⟩ : syracuseStep 2337167 = 3505751) B3505751
theorem B1231279 : Blo 1230433 1231279 := bstep (se 1 (by rfl) ⟨923459, by rfl⟩ : syracuseStep 1231279 = 1846919) B1846919
theorem B1231303 : Blo 1230433 1231303 := bstep (se 1 (by rfl) ⟨923477, by rfl⟩ : syracuseStep 1231303 = 1846955) B1846955
theorem B1231323 : Blo 1230433 1231323 := bstep (se 1 (by rfl) ⟨923492, by rfl⟩ : syracuseStep 1231323 = 1846985) B1846985
theorem B34621937 : Blo 1230433 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B4672025 : Blo 1230433 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B4672039 : Blo 1230433 4672039 := bstep (se 1 (by rfl) ⟨3504029, by rfl⟩ : syracuseStep 4672039 = 7008059) B7008059
theorem B1231399 : Blo 1230433 1231399 := bstep (se 1 (by rfl) ⟨923549, by rfl⟩ : syracuseStep 1231399 = 1847099) B1847099
theorem B2771495 : Blo 1230433 2771495 := bstep (se 1 (by rfl) ⟨2078621, by rfl⟩ : syracuseStep 2771495 = 4157243) B4157243
theorem B1845839 : Blo 1230433 1845839 := bstep (se 1 (by rfl) ⟨1384379, by rfl⟩ : syracuseStep 1845839 = 2768759) B2768759
theorem B1231439 : Blo 1230433 1231439 := bstep (se 1 (by rfl) ⟨923579, by rfl⟩ : syracuseStep 1231439 = 1847159) B1847159
theorem B1231455 : Blo 1230433 1231455 := bstep (se 1 (by rfl) ⟨923591, by rfl⟩ : syracuseStep 1231455 = 1847183) B1847183
theorem B4156001 : Blo 1230433 4156001 := bstep (se 2 (by rfl) ⟨1558500, by rfl⟩ : syracuseStep 4156001 = 3117001) B3117001
theorem B1231483 : Blo 1230433 1231483 := bstep (se 1 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 1231483 = 1847225) B1847225
theorem B3508859 : Blo 1230433 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B1231535 : Blo 1230433 1231535 := bstep (se 1 (by rfl) ⟨923651, by rfl⟩ : syracuseStep 1231535 = 1847303) B1847303
theorem B6654649 : Blo 1230433 6654649 := bstep (se 2 (by rfl) ⟨2495493, by rfl⟩ : syracuseStep 6654649 = 4990987) B4990987
theorem B1845959 : Blo 1230433 1845959 := bstep (se 1 (by rfl) ⟨1384469, by rfl⟩ : syracuseStep 1845959 = 2768939) B2768939
theorem B1231559 : Blo 1230433 1231559 := bstep (se 1 (by rfl) ⟨923669, by rfl⟩ : syracuseStep 1231559 = 1847339) B1847339
theorem B1231579 : Blo 1230433 1231579 := bstep (se 1 (by rfl) ⟨923684, by rfl⟩ : syracuseStep 1231579 = 1847369) B1847369
theorem B10660637 : Blo 1230433 10660637 := bstep (se 3 (by rfl) ⟨1998869, by rfl⟩ : syracuseStep 10660637 = 3997739) B3997739
theorem B134720293 : Blo 1230433 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B1231655 : Blo 1230433 1231655 := bstep (se 1 (by rfl) ⟨923741, by rfl⟩ : syracuseStep 1231655 = 1847483) B1847483
theorem B1231695 : Blo 1230433 1231695 := bstep (se 1 (by rfl) ⟨923771, by rfl⟩ : syracuseStep 1231695 = 1847543) B1847543
theorem B1403743 : Blo 1230433 1403743 := bstep (se 1 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 1403743 = 2105615) B2105615
theorem B1231711 : Blo 1230433 1231711 := bstep (se 1 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 1231711 = 1847567) B1847567
theorem B1846121 : Blo 1230433 1846121 := bstep (se 2 (by rfl) ⟨692295, by rfl⟩ : syracuseStep 1846121 = 1384591) B1384591
theorem B2771819 : Blo 1230433 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B1231739 : Blo 1230433 1231739 := bstep (se 1 (by rfl) ⟨923804, by rfl⟩ : syracuseStep 1231739 = 1847609) B1847609
theorem B2771873 : Blo 1230433 2771873 := bstep (se 2 (by rfl) ⟨1039452, by rfl⟩ : syracuseStep 2771873 = 2078905) B2078905
theorem B1231791 : Blo 1230433 1231791 := bstep (se 1 (by rfl) ⟨923843, by rfl⟩ : syracuseStep 1231791 = 1847687) B1847687
theorem B1846199 : Blo 1230433 1846199 := bstep (se 1 (by rfl) ⟨1384649, by rfl⟩ : syracuseStep 1846199 = 2769299) B2769299
theorem B1231815 : Blo 1230433 1231815 := bstep (se 1 (by rfl) ⟨923861, by rfl⟩ : syracuseStep 1231815 = 1847723) B1847723
theorem B1846235 : Blo 1230433 1846235 := bstep (se 1 (by rfl) ⟨1384676, by rfl⟩ : syracuseStep 1846235 = 2769353) B2769353
theorem B1231835 : Blo 1230433 1231835 := bstep (se 1 (by rfl) ⟨923876, by rfl⟩ : syracuseStep 1231835 = 1847753) B1847753
theorem B1231911 : Blo 1230433 1231911 := bstep (se 1 (by rfl) ⟨923933, by rfl⟩ : syracuseStep 1231911 = 1847867) B1847867
theorem B11840555 : Blo 1230433 11840555 := bstep (se 1 (by rfl) ⟨8880416, by rfl⟩ : syracuseStep 11840555 = 17760833) B17760833
theorem B1231951 : Blo 1230433 1231951 := bstep (se 1 (by rfl) ⟨923963, by rfl⟩ : syracuseStep 1231951 = 1847927) B1847927
theorem B9358415 : Blo 1230433 9358415 := bstep (se 1 (by rfl) ⟨7018811, by rfl⟩ : syracuseStep 9358415 = 14037623) B14037623
theorem B1231967 : Blo 1230433 1231967 := bstep (se 1 (by rfl) ⟨923975, by rfl⟩ : syracuseStep 1231967 = 1847951) B1847951
theorem B1231995 : Blo 1230433 1231995 := bstep (se 1 (by rfl) ⟨923996, by rfl⟩ : syracuseStep 1231995 = 1847993) B1847993
theorem B1559675 : Blo 1230433 1559675 := bstep (se 1 (by rfl) ⟨1169756, by rfl⟩ : syracuseStep 1559675 = 2339513) B2339513
theorem B3329195 : Blo 1230433 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B1232047 : Blo 1230433 1232047 := bstep (se 1 (by rfl) ⟨924035, by rfl⟩ : syracuseStep 1232047 = 1848071) B1848071
theorem B8424643 : Blo 1230433 8424643 := bstep (se 1 (by rfl) ⟨6318482, by rfl⟩ : syracuseStep 8424643 = 12636965) B12636965
theorem B1232071 : Blo 1230433 1232071 := bstep (se 1 (by rfl) ⟨924053, by rfl⟩ : syracuseStep 1232071 = 1848107) B1848107
theorem B1232091 : Blo 1230433 1232091 := bstep (se 1 (by rfl) ⟨924068, by rfl⟩ : syracuseStep 1232091 = 1848137) B1848137
theorem B2772215 : Blo 1230433 2772215 := bstep (se 1 (by rfl) ⟨2079161, by rfl⟩ : syracuseStep 2772215 = 4158323) B4158323
theorem B1232167 : Blo 1230433 1232167 := bstep (se 1 (by rfl) ⟨924125, by rfl⟩ : syracuseStep 1232167 = 1848251) B1848251
theorem B4672829 : Blo 1230433 4672829 := bstep (se 3 (by rfl) ⟨876155, by rfl⟩ : syracuseStep 4672829 = 1752311) B1752311
theorem B1232207 : Blo 1230433 1232207 := bstep (se 1 (by rfl) ⟨924155, by rfl⟩ : syracuseStep 1232207 = 1848311) B1848311
theorem B1232223 : Blo 1230433 1232223 := bstep (se 1 (by rfl) ⟨924167, by rfl⟩ : syracuseStep 1232223 = 1848335) B1848335
theorem B1232251 : Blo 1230433 1232251 := bstep (se 1 (by rfl) ⟨924188, by rfl⟩ : syracuseStep 1232251 = 1848377) B1848377
theorem B7015805 : Blo 1230433 7015805 := bstep (se 3 (by rfl) ⟨1315463, by rfl⟩ : syracuseStep 7015805 = 2630927) B2630927
theorem B5918125 : Blo 1230433 5918125 := bstep (se 3 (by rfl) ⟨1109648, by rfl⟩ : syracuseStep 5918125 = 2219297) B2219297
theorem B1846703 : Blo 1230433 1846703 := bstep (se 1 (by rfl) ⟨1385027, by rfl⟩ : syracuseStep 1846703 = 2770055) B2770055
theorem B1232303 : Blo 1230433 1232303 := bstep (se 1 (by rfl) ⟨924227, by rfl⟩ : syracuseStep 1232303 = 1848455) B1848455
theorem B1232327 : Blo 1230433 1232327 := bstep (se 1 (by rfl) ⟨924245, by rfl⟩ : syracuseStep 1232327 = 1848491) B1848491
theorem B1232347 : Blo 1230433 1232347 := bstep (se 1 (by rfl) ⟨924260, by rfl⟩ : syracuseStep 1232347 = 1848521) B1848521
theorem B4673011 : Blo 1230433 4673011 := bstep (se 1 (by rfl) ⟨3504758, by rfl⟩ : syracuseStep 4673011 = 7009517) B7009517
theorem B1846793 : Blo 1230433 1846793 := bstep (se 2 (by rfl) ⟨692547, by rfl⟩ : syracuseStep 1846793 = 1385095) B1385095
theorem B1846823 : Blo 1230433 1846823 := bstep (se 1 (by rfl) ⟨1385117, by rfl⟩ : syracuseStep 1846823 = 2770235) B2770235
theorem B1232423 : Blo 1230433 1232423 := bstep (se 1 (by rfl) ⟨924317, by rfl⟩ : syracuseStep 1232423 = 1848635) B1848635
theorem B9989693 : Blo 1230433 9989693 := bstep (se 3 (by rfl) ⟨1873067, by rfl⟩ : syracuseStep 9989693 = 3746135) B3746135
theorem B1846907 : Blo 1230433 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B1847033 : Blo 1230433 1847033 := bstep (se 2 (by rfl) ⟨692637, by rfl⟩ : syracuseStep 1847033 = 1385275) B1385275
theorem B2772809 : Blo 1230433 2772809 := bstep (se 2 (by rfl) ⟨1039803, by rfl⟩ : syracuseStep 2772809 = 2079607) B2079607
theorem B1847135 : Blo 1230433 1847135 := bstep (se 1 (by rfl) ⟨1385351, by rfl⟩ : syracuseStep 1847135 = 2770703) B2770703
theorem B1847147 : Blo 1230433 1847147 := bstep (se 1 (by rfl) ⟨1385360, by rfl⟩ : syracuseStep 1847147 = 2770721) B2770721
theorem B4157459 : Blo 1230433 4157459 := bstep (se 1 (by rfl) ⟨3118094, by rfl⟩ : syracuseStep 4157459 = 6236189) B6236189
theorem B3117113 : Blo 1230433 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B1847375 : Blo 1230433 1847375 := bstep (se 1 (by rfl) ⟨1385531, by rfl⟩ : syracuseStep 1847375 = 2771063) B2771063
theorem B1847495 : Blo 1230433 1847495 := bstep (se 1 (by rfl) ⟨1385621, by rfl⟩ : syracuseStep 1847495 = 2771243) B2771243
theorem B2339027 : Blo 1230433 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B4157783 : Blo 1230433 4157783 := bstep (se 1 (by rfl) ⟨3118337, by rfl⟩ : syracuseStep 4157783 = 6236675) B6236675
theorem B1847657 : Blo 1230433 1847657 := bstep (se 2 (by rfl) ⟨692871, by rfl⟩ : syracuseStep 1847657 = 1385743) B1385743
theorem B2077103 : Blo 1230433 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B1847735 : Blo 1230433 1847735 := bstep (se 1 (by rfl) ⟨1385801, by rfl⟩ : syracuseStep 1847735 = 2771603) B2771603
theorem B2339255 : Blo 1230433 2339255 := bstep (se 1 (by rfl) ⟨1754441, by rfl⟩ : syracuseStep 2339255 = 3508883) B3508883
theorem B1847771 : Blo 1230433 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B4436461 : Blo 1230433 4436461 := bstep (se 3 (by rfl) ⟨831836, by rfl⟩ : syracuseStep 4436461 = 1663673) B1663673
theorem B4674257 : Blo 1230433 4674257 := bstep (se 2 (by rfl) ⟨1752846, by rfl⟩ : syracuseStep 4674257 = 3505693) B3505693
theorem B2077535 : Blo 1230433 2077535 := bstep (se 1 (by rfl) ⟨1558151, by rfl⟩ : syracuseStep 2077535 = 3116303) B3116303
theorem B7009199 : Blo 1230433 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B1848239 : Blo 1230433 1848239 := bstep (se 1 (by rfl) ⟨1386179, by rfl⟩ : syracuseStep 1848239 = 2772359) B2772359
theorem B12645341 : Blo 1230433 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B1848329 : Blo 1230433 1848329 := bstep (se 2 (by rfl) ⟨693123, by rfl⟩ : syracuseStep 1848329 = 1386247) B1386247
theorem B1848359 : Blo 1230433 1848359 := bstep (se 1 (by rfl) ⟨1386269, by rfl⟩ : syracuseStep 1848359 = 2772539) B2772539
theorem B1873019 : Blo 1230433 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B1848443 : Blo 1230433 1848443 := bstep (se 1 (by rfl) ⟨1386332, by rfl⟩ : syracuseStep 1848443 = 2772665) B2772665
theorem B2249899 : Blo 1230433 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B35493065 : Blo 1230433 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B1848569 : Blo 1230433 1848569 := bstep (se 2 (by rfl) ⟨693213, by rfl⟩ : syracuseStep 1848569 = 1386427) B1386427
theorem B4674941 : Blo 1230433 4674941 := bstep (se 3 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 4674941 = 1753103) B1753103
theorem B2078095 : Blo 1230433 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B4158863 : Blo 1230433 4158863 := bstep (se 1 (by rfl) ⟨3119147, by rfl⟩ : syracuseStep 4158863 = 6238295) B6238295
theorem B15791507 : Blo 1230433 15791507 := bstep (se 1 (by rfl) ⟨11843630, by rfl⟩ : syracuseStep 15791507 = 23687261) B23687261
theorem B7017947 : Blo 1230433 7017947 := bstep (se 1 (by rfl) ⟨5263460, by rfl⟩ : syracuseStep 7017947 = 10526921) B10526921
theorem B9475571 : Blo 1230433 9475571 := bstep (se 1 (by rfl) ⟨7106678, by rfl⟩ : syracuseStep 9475571 = 14213357) B14213357
theorem B3118601 : Blo 1230433 3118601 := bstep (se 2 (by rfl) ⟨1169475, by rfl⟩ : syracuseStep 3118601 = 2338951) B2338951
theorem B4159187 : Blo 1230433 4159187 := bstep (se 1 (by rfl) ⟨3119390, by rfl⟩ : syracuseStep 4159187 = 6238781) B6238781
theorem B8427331 : Blo 1230433 8427331 := bstep (se 1 (by rfl) ⟨6320498, by rfl⟩ : syracuseStep 8427331 = 12640997) B12640997
theorem B9353069 : Blo 1230433 9353069 := bstep (se 3 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 9353069 = 3507401) B3507401
theorem B2217871 : Blo 1230433 2217871 := bstep (se 1 (by rfl) ⟨1663403, by rfl⟩ : syracuseStep 2217871 = 3326807) B3326807
theorem B1873847 : Blo 1230433 1873847 := bstep (se 1 (by rfl) ⟨1405385, by rfl⟩ : syracuseStep 1873847 = 2810771) B2810771
theorem B8869925 : Blo 1230433 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B2078777 : Blo 1230433 2078777 := bstep (se 2 (by rfl) ⟨779541, by rfl⟩ : syracuseStep 2078777 = 1559083) B1559083
theorem B2218195 : Blo 1230433 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B14211377 : Blo 1230433 14211377 := bstep (se 2 (by rfl) ⟨5329266, by rfl⟩ : syracuseStep 14211377 = 10658533) B10658533
theorem B4675927 : Blo 1230433 4675927 := bstep (se 1 (by rfl) ⟨3506945, by rfl⟩ : syracuseStep 4675927 = 7013891) B7013891
theorem B3504509 : Blo 1230433 3504509 := bstep (se 3 (by rfl) ⟨657095, by rfl⟩ : syracuseStep 3504509 = 1314191) B1314191
theorem B23976323 : Blo 1230433 23976323 := bstep (se 1 (by rfl) ⟨17982242, by rfl⟩ : syracuseStep 23976323 = 35964485) B35964485
theorem B34134605 : Blo 1230433 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B4676231 : Blo 1230433 4676231 := bstep (se 1 (by rfl) ⟨3507173, by rfl⟩ : syracuseStep 4676231 = 7014347) B7014347
theorem B6232787 : Blo 1230433 6232787 := bstep (se 1 (by rfl) ⟨4674590, by rfl⟩ : syracuseStep 6232787 = 9349181) B9349181
theorem B4438739 : Blo 1230433 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B2079479 : Blo 1230433 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B4438813 : Blo 1230433 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B2628425 : Blo 1230433 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B5995439 : Blo 1230433 5995439 := bstep (se 1 (by rfl) ⟨4496579, by rfl⟩ : syracuseStep 5995439 = 8993159) B8993159
theorem B4676687 : Blo 1230433 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B6659275 : Blo 1230433 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B2219255 : Blo 1230433 2219255 := bstep (se 1 (by rfl) ⟨1664441, by rfl⟩ : syracuseStep 2219255 = 3328883) B3328883
theorem B8871191 : Blo 1230433 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B13319549 : Blo 1230433 13319549 := bstep (se 3 (by rfl) ⟨2497415, by rfl⟩ : syracuseStep 13319549 = 4994831) B4994831
theorem B3743119 : Blo 1230433 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B2768507 : Blo 1230433 2768507 := bstep (se 1 (by rfl) ⟨2076380, by rfl⟩ : syracuseStep 2768507 = 4152761) B4152761
theorem B4153031 : Blo 1230433 4153031 := bstep (se 1 (by rfl) ⟨3114773, by rfl⟩ : syracuseStep 4153031 = 6229547) B6229547
theorem B5258951 : Blo 1230433 5258951 := bstep (se 1 (by rfl) ⟨3944213, by rfl⟩ : syracuseStep 5258951 = 7888427) B7888427
theorem B1777351 : Blo 1230433 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B2768633 : Blo 1230433 2768633 := bstep (se 2 (by rfl) ⟨1038237, by rfl⟩ : syracuseStep 2768633 = 2076475) B2076475
theorem B1777583 : Blo 1230433 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1384411 : Blo 1230433 1384411 := bstep (se 1 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 1384411 = 2076617) B2076617
theorem B13304017 : Blo 1230433 13304017 := bstep (se 2 (by rfl) ⟨4989006, by rfl⟩ : syracuseStep 13304017 = 9978013) B9978013
theorem B1384735 : Blo 1230433 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B2769263 : Blo 1230433 2769263 := bstep (se 1 (by rfl) ⟨2076947, by rfl⟩ : syracuseStep 2769263 = 4153895) B4153895
theorem B2769335 : Blo 1230433 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B6234569 : Blo 1230433 6234569 := bstep (se 2 (by rfl) ⟨2337963, by rfl⟩ : syracuseStep 6234569 = 4675927) B4675927
theorem B4678145 : Blo 1230433 4678145 := bstep (se 2 (by rfl) ⟨1754304, by rfl⟩ : syracuseStep 4678145 = 3508609) B3508609
theorem B1385023 : Blo 1230433 1385023 := bstep (se 1 (by rfl) ⟨1038767, by rfl⟩ : syracuseStep 1385023 = 2077535) B2077535
theorem B2769479 : Blo 1230433 2769479 := bstep (se 1 (by rfl) ⟨2077109, by rfl⟩ : syracuseStep 2769479 = 4154219) B4154219
theorem B2769515 : Blo 1230433 2769515 := bstep (se 1 (by rfl) ⟨2077136, by rfl⟩ : syracuseStep 2769515 = 4154273) B4154273
theorem B85303925 : Blo 1230433 85303925 := bstep (se 5 (by rfl) ⟨3998621, by rfl⟩ : syracuseStep 85303925 = 7997243) B7997243
theorem B3506809 : Blo 1230433 3506809 := bstep (se 2 (by rfl) ⟨1315053, by rfl⟩ : syracuseStep 3506809 = 2630107) B2630107
theorem B32424583 : Blo 1230433 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B5915281 : Blo 1230433 5915281 := bstep (se 2 (by rfl) ⟨2218230, by rfl⟩ : syracuseStep 5915281 = 4436461) B4436461
theorem B8430227 : Blo 1230433 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B8110763 : Blo 1230433 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B47997845 : Blo 1230433 47997845 := bstep (se 6 (by rfl) ⟨1124949, by rfl⟩ : syracuseStep 47997845 = 2249899) B2249899
theorem B8872865 : Blo 1230433 8872865 := bstep (se 2 (by rfl) ⟨3327324, by rfl⟩ : syracuseStep 8872865 = 6654649) B6654649
theorem B10527671 : Blo 1230433 10527671 := bstep (se 1 (by rfl) ⟨7895753, by rfl⟩ : syracuseStep 10527671 = 15791507) B15791507
theorem B4678631 : Blo 1230433 4678631 := bstep (se 1 (by rfl) ⟨3508973, by rfl⟩ : syracuseStep 4678631 = 7017947) B7017947
theorem B6317047 : Blo 1230433 6317047 := bstep (se 1 (by rfl) ⟨4737785, by rfl⟩ : syracuseStep 6317047 = 9475571) B9475571
theorem B2769911 : Blo 1230433 2769911 := bstep (se 1 (by rfl) ⟨2077433, by rfl⟩ : syracuseStep 2769911 = 4154867) B4154867
theorem B179627057 : Blo 1230433 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B11830373 : Blo 1230433 11830373 := bstep (se 4 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 11830373 = 2218195) B2218195
theorem B6235379 : Blo 1230433 6235379 := bstep (se 1 (by rfl) ⟨4676534, by rfl⟩ : syracuseStep 6235379 = 9353069) B9353069
theorem B1754407 : Blo 1230433 1754407 := bstep (se 1 (by rfl) ⟨1315805, by rfl⟩ : syracuseStep 1754407 = 2631611) B2631611
theorem B8111411 : Blo 1230433 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B2770271 : Blo 1230433 2770271 := bstep (se 1 (by rfl) ⟨2077703, by rfl⟩ : syracuseStep 2770271 = 4155407) B4155407
theorem B1557883 : Blo 1230433 1557883 := bstep (se 1 (by rfl) ⟨1168412, by rfl⟩ : syracuseStep 1557883 = 2336825) B2336825
theorem B1385851 : Blo 1230433 1385851 := bstep (se 1 (by rfl) ⟨1039388, by rfl⟩ : syracuseStep 1385851 = 2078777) B2078777
theorem B4154813 : Blo 1230433 4154813 := bstep (se 3 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 4154813 = 1558055) B1558055
theorem B13305401 : Blo 1230433 13305401 := bstep (se 2 (by rfl) ⟨4989525, by rfl⟩ : syracuseStep 13305401 = 9979051) B9979051
theorem B2336339 : Blo 1230433 2336339 := bstep (se 1 (by rfl) ⟨1752254, by rfl⟩ : syracuseStep 2336339 = 3504509) B3504509
theorem B15984215 : Blo 1230433 15984215 := bstep (se 1 (by rfl) ⟨11988161, by rfl⟩ : syracuseStep 15984215 = 23976323) B23976323
theorem B11232857 : Blo 1230433 11232857 := bstep (se 2 (by rfl) ⟨4212321, by rfl⟩ : syracuseStep 11232857 = 8424643) B8424643
theorem B1558111 : Blo 1230433 1558111 := bstep (se 1 (by rfl) ⟨1168583, by rfl⟩ : syracuseStep 1558111 = 2337167) B2337167
theorem B9356957 : Blo 1230433 9356957 := bstep (se 3 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 9356957 = 3508859) B3508859
theorem B3114683 : Blo 1230433 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B1230559 : Blo 1230433 1230559 := bstep (se 1 (by rfl) ⟨922919, by rfl⟩ : syracuseStep 1230559 = 1845839) B1845839
theorem B2770667 : Blo 1230433 2770667 := bstep (se 1 (by rfl) ⟨2078000, by rfl⟩ : syracuseStep 2770667 = 4156001) B4156001
theorem B1230639 : Blo 1230433 1230639 := bstep (se 1 (by rfl) ⟨922979, by rfl⟩ : syracuseStep 1230639 = 1845959) B1845959
theorem B4155191 : Blo 1230433 4155191 := bstep (se 1 (by rfl) ⟨3116393, by rfl⟩ : syracuseStep 4155191 = 6232787) B6232787
theorem B1386319 : Blo 1230433 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B4990825 : Blo 1230433 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B2770793 : Blo 1230433 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B7890833 : Blo 1230433 7890833 := bstep (se 2 (by rfl) ⟨2959062, by rfl⟩ : syracuseStep 7890833 = 5918125) B5918125
theorem B1230747 : Blo 1230433 1230747 := bstep (se 1 (by rfl) ⟨923060, by rfl⟩ : syracuseStep 1230747 = 1846121) B1846121
theorem B1230799 : Blo 1230433 1230799 := bstep (se 1 (by rfl) ⟨923099, by rfl⟩ : syracuseStep 1230799 = 1846199) B1846199
theorem B1230823 : Blo 1230433 1230823 := bstep (se 1 (by rfl) ⟨923117, by rfl⟩ : syracuseStep 1230823 = 1846235) B1846235
theorem B28428365 : Blo 1230433 28428365 := bstep (se 3 (by rfl) ⟨5330318, by rfl⟩ : syracuseStep 28428365 = 10660637) B10660637
theorem B3115219 : Blo 1230433 3115219 := bstep (se 1 (by rfl) ⟨2336414, by rfl⟩ : syracuseStep 3115219 = 4672829) B4672829
theorem B2369801 : Blo 1230433 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B4155677 : Blo 1230433 4155677 := bstep (se 3 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 4155677 = 1558379) B1558379
theorem B1231135 : Blo 1230433 1231135 := bstep (se 1 (by rfl) ⟨923351, by rfl⟩ : syracuseStep 1231135 = 1846703) B1846703
theorem B1231195 : Blo 1230433 1231195 := bstep (se 1 (by rfl) ⟨923396, by rfl⟩ : syracuseStep 1231195 = 1846793) B1846793
theorem B1231215 : Blo 1230433 1231215 := bstep (se 1 (by rfl) ⟨923411, by rfl⟩ : syracuseStep 1231215 = 1846823) B1846823
theorem B1845671 : Blo 1230433 1845671 := bstep (se 1 (by rfl) ⟨1384253, by rfl⟩ : syracuseStep 1845671 = 2768507) B2768507
theorem B1231271 : Blo 1230433 1231271 := bstep (se 1 (by rfl) ⟨923453, by rfl⟩ : syracuseStep 1231271 = 1846907) B1846907
theorem B1845755 : Blo 1230433 1845755 := bstep (se 1 (by rfl) ⟨1384316, by rfl⟩ : syracuseStep 1845755 = 2768633) B2768633
theorem B1231355 : Blo 1230433 1231355 := bstep (se 1 (by rfl) ⟨923516, by rfl⟩ : syracuseStep 1231355 = 1847033) B1847033
theorem B1231423 : Blo 1230433 1231423 := bstep (se 1 (by rfl) ⟨923567, by rfl⟩ : syracuseStep 1231423 = 1847135) B1847135
theorem B1231431 : Blo 1230433 1231431 := bstep (se 1 (by rfl) ⟨923573, by rfl⟩ : syracuseStep 1231431 = 1847147) B1847147
theorem B1845881 : Blo 1230433 1845881 := bstep (se 2 (by rfl) ⟨692205, by rfl⟩ : syracuseStep 1845881 = 1384411) B1384411
theorem B1845935 : Blo 1230433 1845935 := bstep (se 1 (by rfl) ⟨1384451, by rfl⟩ : syracuseStep 1845935 = 2768903) B2768903
theorem B2771639 : Blo 1230433 2771639 := bstep (se 1 (by rfl) ⟨2078729, by rfl⟩ : syracuseStep 2771639 = 4157459) B4157459
theorem B1845983 : Blo 1230433 1845983 := bstep (se 1 (by rfl) ⟨1384487, by rfl⟩ : syracuseStep 1845983 = 2768975) B2768975
theorem B1231583 : Blo 1230433 1231583 := bstep (se 1 (by rfl) ⟨923687, by rfl⟩ : syracuseStep 1231583 = 1847375) B1847375
theorem B1231663 : Blo 1230433 1231663 := bstep (se 1 (by rfl) ⟨923747, by rfl⟩ : syracuseStep 1231663 = 1847495) B1847495
theorem B1559351 : Blo 1230433 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B2771855 : Blo 1230433 2771855 := bstep (se 1 (by rfl) ⟨2078891, by rfl⟩ : syracuseStep 2771855 = 4157783) B4157783
theorem B1231771 : Blo 1230433 1231771 := bstep (se 1 (by rfl) ⟨923828, by rfl⟩ : syracuseStep 1231771 = 1847657) B1847657
theorem B1231823 : Blo 1230433 1231823 := bstep (se 1 (by rfl) ⟨923867, by rfl⟩ : syracuseStep 1231823 = 1847735) B1847735
theorem B1559503 : Blo 1230433 1559503 := bstep (se 1 (by rfl) ⟨1169627, by rfl⟩ : syracuseStep 1559503 = 2339255) B2339255
theorem B1846247 : Blo 1230433 1846247 := bstep (se 1 (by rfl) ⟨1384685, by rfl⟩ : syracuseStep 1846247 = 2769371) B2769371
theorem B1231847 : Blo 1230433 1231847 := bstep (se 1 (by rfl) ⟨923885, by rfl⟩ : syracuseStep 1231847 = 1847771) B1847771
theorem B3116171 : Blo 1230433 3116171 := bstep (se 1 (by rfl) ⟨2337128, by rfl⟩ : syracuseStep 3116171 = 4674257) B4674257
theorem B6237323 : Blo 1230433 6237323 := bstep (se 1 (by rfl) ⟨4677992, by rfl⟩ : syracuseStep 6237323 = 9355985) B9355985
theorem B1846505 : Blo 1230433 1846505 := bstep (se 2 (by rfl) ⟨692439, by rfl⟩ : syracuseStep 1846505 = 1384879) B1384879
theorem B4672799 : Blo 1230433 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B1846559 : Blo 1230433 1846559 := bstep (se 1 (by rfl) ⟨1384919, by rfl⟩ : syracuseStep 1846559 = 2769839) B2769839
theorem B4156703 : Blo 1230433 4156703 := bstep (se 1 (by rfl) ⟨3117527, by rfl⟩ : syracuseStep 4156703 = 6235055) B6235055
theorem B1232159 : Blo 1230433 1232159 := bstep (se 1 (by rfl) ⟨924119, by rfl⟩ : syracuseStep 1232159 = 1848239) B1848239
theorem B1232219 : Blo 1230433 1232219 := bstep (se 1 (by rfl) ⟨924164, by rfl⟩ : syracuseStep 1232219 = 1848329) B1848329
theorem B1232239 : Blo 1230433 1232239 := bstep (se 1 (by rfl) ⟨924179, by rfl⟩ : syracuseStep 1232239 = 1848359) B1848359
theorem B6229385 : Blo 1230433 6229385 := bstep (se 2 (by rfl) ⟨2336019, by rfl⟩ : syracuseStep 6229385 = 4672039) B4672039
theorem B1248679 : Blo 1230433 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B1232295 : Blo 1230433 1232295 := bstep (se 1 (by rfl) ⟨924221, by rfl⟩ : syracuseStep 1232295 = 1848443) B1848443
theorem B1846727 : Blo 1230433 1846727 := bstep (se 1 (by rfl) ⟨1385045, by rfl⟩ : syracuseStep 1846727 = 2770091) B2770091
theorem B23662043 : Blo 1230433 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1232379 : Blo 1230433 1232379 := bstep (se 1 (by rfl) ⟨924284, by rfl⟩ : syracuseStep 1232379 = 1848569) B1848569
theorem B3116627 : Blo 1230433 3116627 := bstep (se 1 (by rfl) ⟨2337470, by rfl⟩ : syracuseStep 3116627 = 4674941) B4674941
theorem B2772575 : Blo 1230433 2772575 := bstep (se 1 (by rfl) ⟨2079431, by rfl⟩ : syracuseStep 2772575 = 4158863) B4158863
theorem B2338465 : Blo 1230433 2338465 := bstep (se 2 (by rfl) ⟨876924, by rfl⟩ : syracuseStep 2338465 = 1753849) B1753849
theorem B5918417 : Blo 1230433 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B6319883 : Blo 1230433 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B1871657 : Blo 1230433 1871657 := bstep (se 2 (by rfl) ⟨701871, by rfl⟩ : syracuseStep 1871657 = 1403743) B1403743
theorem B1847081 : Blo 1230433 1847081 := bstep (se 2 (by rfl) ⟨692655, by rfl⟩ : syracuseStep 1847081 = 1385311) B1385311
theorem B1847087 : Blo 1230433 1847087 := bstep (se 1 (by rfl) ⟨1385315, by rfl⟩ : syracuseStep 1847087 = 2770631) B2770631
theorem B2772791 : Blo 1230433 2772791 := bstep (se 1 (by rfl) ⟨2079593, by rfl⟩ : syracuseStep 2772791 = 4159187) B4159187
theorem B1249231 : Blo 1230433 1249231 := bstep (se 1 (by rfl) ⟨936923, by rfl⟩ : syracuseStep 1249231 = 1873847) B1873847
theorem B9474251 : Blo 1230433 9474251 := bstep (se 1 (by rfl) ⟨7105688, by rfl⟩ : syracuseStep 9474251 = 14211377) B14211377
theorem B7008515 : Blo 1230433 7008515 := bstep (se 1 (by rfl) ⟨5256386, by rfl⟩ : syracuseStep 7008515 = 10512773) B10512773
theorem B1847561 : Blo 1230433 1847561 := bstep (se 2 (by rfl) ⟨692835, by rfl⟩ : syracuseStep 1847561 = 1385671) B1385671
theorem B23081291 : Blo 1230433 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B1847663 : Blo 1230433 1847663 := bstep (se 1 (by rfl) ⟨1385747, by rfl⟩ : syracuseStep 1847663 = 2771495) B2771495
theorem B3117487 : Blo 1230433 3117487 := bstep (se 1 (by rfl) ⟨2338115, by rfl⟩ : syracuseStep 3117487 = 4676231) B4676231
theorem B1847879 : Blo 1230433 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1847915 : Blo 1230433 1847915 := bstep (se 1 (by rfl) ⟨1385936, by rfl⟩ : syracuseStep 1847915 = 2771873) B2771873
theorem B6230681 : Blo 1230433 6230681 := bstep (se 2 (by rfl) ⟨2336505, by rfl⟩ : syracuseStep 6230681 = 4673011) B4673011
theorem B7893703 : Blo 1230433 7893703 := bstep (se 1 (by rfl) ⟨5920277, by rfl⟩ : syracuseStep 7893703 = 11840555) B11840555
theorem B3117791 : Blo 1230433 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B6238943 : Blo 1230433 6238943 := bstep (se 1 (by rfl) ⟨4679207, by rfl⟩ : syracuseStep 6238943 = 9358415) B9358415
theorem B1479503 : Blo 1230433 1479503 := bstep (se 1 (by rfl) ⟨1109627, by rfl⟩ : syracuseStep 1479503 = 2219255) B2219255
theorem B1848143 : Blo 1230433 1848143 := bstep (se 1 (by rfl) ⟨1386107, by rfl⟩ : syracuseStep 1848143 = 2772215) B2772215
theorem B40506317 : Blo 1230433 40506317 := bstep (se 3 (by rfl) ⟨7594934, by rfl⟩ : syracuseStep 40506317 = 15189869) B15189869
theorem B11236441 : Blo 1230433 11236441 := bstep (se 2 (by rfl) ⟨4213665, by rfl⟩ : syracuseStep 11236441 = 8427331) B8427331
theorem B4740221 : Blo 1230433 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B9483389 : Blo 1230433 9483389 := bstep (se 3 (by rfl) ⟨1778135, by rfl⟩ : syracuseStep 9483389 = 3556271) B3556271
theorem B1848539 : Blo 1230433 1848539 := bstep (se 1 (by rfl) ⟨1386404, by rfl⟩ : syracuseStep 1848539 = 2772809) B2772809
theorem B1480027 : Blo 1230433 1480027 := bstep (se 1 (by rfl) ⟨1110020, by rfl⟩ : syracuseStep 1480027 = 2220041) B2220041
theorem B1283419 : Blo 1230433 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B2078075 : Blo 1230433 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B3118459 : Blo 1230433 3118459 := bstep (se 1 (by rfl) ⟨2338844, by rfl⟩ : syracuseStep 3118459 = 4677689) B4677689
theorem B4674955 : Blo 1230433 4674955 := bstep (se 1 (by rfl) ⟨3506216, by rfl⟩ : syracuseStep 4674955 = 7012433) B7012433
theorem B4675229 : Blo 1230433 4675229 := bstep (se 3 (by rfl) ⟨876605, by rfl⟩ : syracuseStep 4675229 = 1753211) B1753211
theorem B4159133 : Blo 1230433 4159133 := bstep (se 3 (by rfl) ⟨779837, by rfl⟩ : syracuseStep 4159133 = 1559675) B1559675
theorem B4675259 : Blo 1230433 4675259 := bstep (se 1 (by rfl) ⟨3506444, by rfl⟩ : syracuseStep 4675259 = 7012889) B7012889
theorem B8877853 : Blo 1230433 8877853 := bstep (se 3 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 8877853 = 3329195) B3329195
theorem B3118895 : Blo 1230433 3118895 := bstep (se 1 (by rfl) ⟨2339171, by rfl⟩ : syracuseStep 3118895 = 4678343) B4678343
theorem B1873871 : Blo 1230433 1873871 := bstep (se 1 (by rfl) ⟨1405403, by rfl⟩ : syracuseStep 1873871 = 2810807) B2810807
theorem B52664327 : Blo 1230433 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B6084743 : Blo 1230433 6084743 := bstep (se 1 (by rfl) ⟨4563557, by rfl⟩ : syracuseStep 6084743 = 9127115) B9127115
theorem B2079067 : Blo 1230433 2079067 := bstep (se 1 (by rfl) ⟨1559300, by rfl⟩ : syracuseStep 2079067 = 3118601) B3118601
theorem B6232463 : Blo 1230433 6232463 := bstep (se 1 (by rfl) ⟨4674347, by rfl⟩ : syracuseStep 6232463 = 9348695) B9348695
theorem B3119543 : Blo 1230433 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B1333703 : Blo 1230433 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B5913283 : Blo 1230433 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B2808719 : Blo 1230433 2808719 := bstep (se 1 (by rfl) ⟨2106539, by rfl⟩ : syracuseStep 2808719 = 4213079) B4213079
theorem B8879033 : Blo 1230433 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B22756403 : Blo 1230433 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B1752283 : Blo 1230433 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B11836637 : Blo 1230433 11836637 := bstep (se 3 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 11836637 = 4438739) B4438739
theorem B3996959 : Blo 1230433 3996959 := bstep (se 1 (by rfl) ⟨2997719, by rfl⟩ : syracuseStep 3996959 = 5995439) B5995439
theorem B5914127 : Blo 1230433 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B4677203 : Blo 1230433 4677203 := bstep (se 1 (by rfl) ⟨3507902, by rfl⟩ : syracuseStep 4677203 = 7015805) B7015805
theorem B8879699 : Blo 1230433 8879699 := bstep (se 1 (by rfl) ⟨6659774, by rfl⟩ : syracuseStep 8879699 = 13319549) B13319549
theorem B6659795 : Blo 1230433 6659795 := bstep (se 1 (by rfl) ⟨4994846, by rfl⟩ : syracuseStep 6659795 = 9989693) B9989693
theorem B2768687 : Blo 1230433 2768687 := bstep (se 1 (by rfl) ⟨2076515, by rfl⟩ : syracuseStep 2768687 = 4153031) B4153031
theorem B3505967 : Blo 1230433 3505967 := bstep (se 1 (by rfl) ⟨2629475, by rfl⟩ : syracuseStep 3505967 = 5258951) B5258951
theorem B2957161 : Blo 1230433 2957161 := bstep (se 2 (by rfl) ⟨1108935, by rfl⟩ : syracuseStep 2957161 = 2217871) B2217871
theorem B75808973 : Blo 1230433 75808973 := bstep (se 3 (by rfl) ⟨14214182, by rfl⟩ : syracuseStep 75808973 = 28428365) B28428365
theorem B4153625 : Blo 1230433 4153625 := bstep (se 2 (by rfl) ⟨1557609, by rfl⟩ : syracuseStep 4153625 = 3115219) B3115219
theorem B56869283 : Blo 1230433 56869283 := bstep (se 1 (by rfl) ⟨42651962, by rfl⟩ : syracuseStep 56869283 = 85303925) B85303925
theorem B5620151 : Blo 1230433 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B4153787 : Blo 1230433 4153787 := bstep (se 1 (by rfl) ⟨3115340, by rfl⟩ : syracuseStep 4153787 = 6230681) B6230681
theorem B5407175 : Blo 1230433 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B25264669 : Blo 1230433 25264669 := bstep (se 3 (by rfl) ⟨4737125, by rfl⟩ : syracuseStep 25264669 = 9474251) B9474251
theorem B31998563 : Blo 1230433 31998563 := bstep (se 1 (by rfl) ⟨23998922, by rfl⟩ : syracuseStep 31998563 = 47997845) B47997845
theorem B5915243 : Blo 1230433 5915243 := bstep (se 1 (by rfl) ⟨4436432, by rfl⟩ : syracuseStep 5915243 = 8872865) B8872865
theorem B119751371 : Blo 1230433 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B10658557 : Blo 1230433 10658557 := bstep (se 3 (by rfl) ⟨1998479, by rfl⟩ : syracuseStep 10658557 = 3996959) B3996959
theorem B5407607 : Blo 1230433 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B1385383 : Blo 1230433 1385383 := bstep (se 1 (by rfl) ⟨1039037, by rfl⟩ : syracuseStep 1385383 = 2078075) B2078075
theorem B2769875 : Blo 1230433 2769875 := bstep (se 1 (by rfl) ⟨2077406, by rfl⟩ : syracuseStep 2769875 = 4154813) B4154813
theorem B1557559 : Blo 1230433 1557559 := bstep (se 1 (by rfl) ⟨1168169, by rfl⟩ : syracuseStep 1557559 = 2336339) B2336339
theorem B7488571 : Blo 1230433 7488571 := bstep (se 1 (by rfl) ⟨5616428, by rfl⟩ : syracuseStep 7488571 = 11232857) B11232857
theorem B3556541 : Blo 1230433 3556541 := bstep (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) B1333703
theorem B2770127 : Blo 1230433 2770127 := bstep (se 1 (by rfl) ⟨2077595, by rfl⟩ : syracuseStep 2770127 = 4155191) B4155191
theorem B5260555 : Blo 1230433 5260555 := bstep (se 1 (by rfl) ⟨3945416, by rfl⟩ : syracuseStep 5260555 = 7890833) B7890833
theorem B2770451 : Blo 1230433 2770451 := bstep (se 1 (by rfl) ⟨2077838, by rfl⟩ : syracuseStep 2770451 = 4155677) B4155677
theorem B4154975 : Blo 1230433 4154975 := bstep (se 1 (by rfl) ⟨3116231, by rfl⟩ : syracuseStep 4154975 = 6232463) B6232463
theorem B1230447 : Blo 1230433 1230447 := bstep (se 1 (by rfl) ⟨922835, by rfl⟩ : syracuseStep 1230447 = 1845671) B1845671
theorem B2336377 : Blo 1230433 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B1230503 : Blo 1230433 1230503 := bstep (se 1 (by rfl) ⟨922877, by rfl⟩ : syracuseStep 1230503 = 1845755) B1845755
theorem B1230587 : Blo 1230433 1230587 := bstep (se 1 (by rfl) ⟨922940, by rfl⟩ : syracuseStep 1230587 = 1845881) B1845881
theorem B1230623 : Blo 1230433 1230623 := bstep (se 1 (by rfl) ⟨922967, by rfl⟩ : syracuseStep 1230623 = 1845935) B1845935
theorem B1230655 : Blo 1230433 1230655 := bstep (se 1 (by rfl) ⟨922991, by rfl⟩ : syracuseStep 1230655 = 1845983) B1845983
theorem B1664905 : Blo 1230433 1664905 := bstep (se 2 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 1664905 = 1248679) B1248679
theorem B1230831 : Blo 1230433 1230831 := bstep (se 1 (by rfl) ⟨923123, by rfl⟩ : syracuseStep 1230831 = 1846247) B1846247
theorem B16853021 : Blo 1230433 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B7891091 : Blo 1230433 7891091 := bstep (se 1 (by rfl) ⟨5918318, by rfl⟩ : syracuseStep 7891091 = 11836637) B11836637
theorem B1231003 : Blo 1230433 1231003 := bstep (se 1 (by rfl) ⟨923252, by rfl⟩ : syracuseStep 1231003 = 1846505) B1846505
theorem B3115199 : Blo 1230433 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B1231039 : Blo 1230433 1231039 := bstep (se 1 (by rfl) ⟨923279, by rfl⟩ : syracuseStep 1231039 = 1846559) B1846559
theorem B2771135 : Blo 1230433 2771135 := bstep (se 1 (by rfl) ⟨2078351, by rfl⟩ : syracuseStep 2771135 = 4156703) B4156703
theorem B1231151 : Blo 1230433 1231151 := bstep (se 1 (by rfl) ⟨923363, by rfl⟩ : syracuseStep 1231151 = 1846727) B1846727
theorem B3942751 : Blo 1230433 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B3942881 : Blo 1230433 3942881 := bstep (se 2 (by rfl) ⟨1478580, by rfl⟩ : syracuseStep 3942881 = 2957161) B2957161
theorem B6654433 : Blo 1230433 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B1247771 : Blo 1230433 1247771 := bstep (se 1 (by rfl) ⟨935828, by rfl⟩ : syracuseStep 1247771 = 1871657) B1871657
theorem B1231387 : Blo 1230433 1231387 := bstep (se 1 (by rfl) ⟨923540, by rfl⟩ : syracuseStep 1231387 = 1847081) B1847081
theorem B1845791 : Blo 1230433 1845791 := bstep (se 1 (by rfl) ⟨1384343, by rfl⟩ : syracuseStep 1845791 = 2768687) B2768687
theorem B2337311 : Blo 1230433 2337311 := bstep (se 1 (by rfl) ⟨1752983, by rfl⟩ : syracuseStep 2337311 = 3505967) B3505967
theorem B1231391 : Blo 1230433 1231391 := bstep (se 1 (by rfl) ⟨923543, by rfl⟩ : syracuseStep 1231391 = 1847087) B1847087
theorem B1665641 : Blo 1230433 1665641 := bstep (se 2 (by rfl) ⟨624615, by rfl⟩ : syracuseStep 1665641 = 1249231) B1249231
theorem B4672343 : Blo 1230433 4672343 := bstep (se 1 (by rfl) ⟨3504257, by rfl⟩ : syracuseStep 4672343 = 7008515) B7008515
theorem B1231707 : Blo 1230433 1231707 := bstep (se 1 (by rfl) ⟨923780, by rfl⟩ : syracuseStep 1231707 = 1847561) B1847561
theorem B15387527 : Blo 1230433 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B1846175 : Blo 1230433 1846175 := bstep (se 1 (by rfl) ⟨1384631, by rfl⟩ : syracuseStep 1846175 = 2769263) B2769263
theorem B1231775 : Blo 1230433 1231775 := bstep (se 1 (by rfl) ⟨923831, by rfl⟩ : syracuseStep 1231775 = 1847663) B1847663
theorem B17738689 : Blo 1230433 17738689 := bstep (se 2 (by rfl) ⟨6652008, by rfl⟩ : syracuseStep 17738689 = 13304017) B13304017
theorem B1846223 : Blo 1230433 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B4156379 : Blo 1230433 4156379 := bstep (se 1 (by rfl) ⟨3117284, by rfl⟩ : syracuseStep 4156379 = 6234569) B6234569
theorem B1846313 : Blo 1230433 1846313 := bstep (se 2 (by rfl) ⟨692367, by rfl⟩ : syracuseStep 1846313 = 1384735) B1384735
theorem B1846319 : Blo 1230433 1846319 := bstep (se 1 (by rfl) ⟨1384739, by rfl⟩ : syracuseStep 1846319 = 2769479) B2769479
theorem B1231919 : Blo 1230433 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B1846343 : Blo 1230433 1846343 := bstep (se 1 (by rfl) ⟨1384757, by rfl⟩ : syracuseStep 1846343 = 2769515) B2769515
theorem B1231943 : Blo 1230433 1231943 := bstep (se 1 (by rfl) ⟨923957, by rfl⟩ : syracuseStep 1231943 = 1847915) B1847915
theorem B2772089 : Blo 1230433 2772089 := bstep (se 2 (by rfl) ⟨1039533, by rfl⟩ : syracuseStep 2772089 = 2079067) B2079067
theorem B1232095 : Blo 1230433 1232095 := bstep (se 1 (by rfl) ⟨924071, by rfl⟩ : syracuseStep 1232095 = 1848143) B1848143
theorem B4156649 : Blo 1230433 4156649 := bstep (se 2 (by rfl) ⟨1558743, by rfl⟩ : syracuseStep 4156649 = 3117487) B3117487
theorem B27004211 : Blo 1230433 27004211 := bstep (se 1 (by rfl) ⟨20253158, by rfl⟩ : syracuseStep 27004211 = 40506317) B40506317
theorem B1846607 : Blo 1230433 1846607 := bstep (se 1 (by rfl) ⟨1384955, by rfl⟩ : syracuseStep 1846607 = 2769911) B2769911
theorem B1846697 : Blo 1230433 1846697 := bstep (se 2 (by rfl) ⟨692511, by rfl⟩ : syracuseStep 1846697 = 1385023) B1385023
theorem B1232359 : Blo 1230433 1232359 := bstep (se 1 (by rfl) ⟨924269, by rfl⟩ : syracuseStep 1232359 = 1848539) B1848539
theorem B4156919 : Blo 1230433 4156919 := bstep (se 1 (by rfl) ⟨3117689, by rfl⟩ : syracuseStep 4156919 = 6235379) B6235379
theorem B43232777 : Blo 1230433 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B1846847 : Blo 1230433 1846847 := bstep (se 1 (by rfl) ⟨1385135, by rfl⟩ : syracuseStep 1846847 = 2770271) B2770271
theorem B7884377 : Blo 1230433 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B3116819 : Blo 1230433 3116819 := bstep (se 1 (by rfl) ⟨2337614, by rfl⟩ : syracuseStep 3116819 = 4675229) B4675229
theorem B6237971 : Blo 1230433 6237971 := bstep (se 1 (by rfl) ⟨4678478, by rfl⟩ : syracuseStep 6237971 = 9356957) B9356957
theorem B2772755 : Blo 1230433 2772755 := bstep (se 1 (by rfl) ⟨2079566, by rfl⟩ : syracuseStep 2772755 = 4159133) B4159133
theorem B2076455 : Blo 1230433 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B3116839 : Blo 1230433 3116839 := bstep (se 1 (by rfl) ⟨2337629, by rfl⟩ : syracuseStep 3116839 = 4675259) B4675259
theorem B1847111 : Blo 1230433 1847111 := bstep (se 1 (by rfl) ⟨1385333, by rfl⟩ : syracuseStep 1847111 = 2770667) B2770667
theorem B1847195 : Blo 1230433 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B1249247 : Blo 1230433 1249247 := bstep (se 1 (by rfl) ⟨936935, by rfl⟩ : syracuseStep 1249247 = 1873871) B1873871
theorem B2339209 : Blo 1230433 2339209 := bstep (se 2 (by rfl) ⟨877203, by rfl⟩ : syracuseStep 2339209 = 1754407) B1754407
theorem B1847759 : Blo 1230433 1847759 := bstep (se 1 (by rfl) ⟨1385819, by rfl⟩ : syracuseStep 1847759 = 2771639) B2771639
theorem B2077177 : Blo 1230433 2077177 := bstep (se 2 (by rfl) ⟨778941, by rfl⟩ : syracuseStep 2077177 = 1557883) B1557883
theorem B1847801 : Blo 1230433 1847801 := bstep (se 2 (by rfl) ⟨692925, by rfl⟩ : syracuseStep 1847801 = 1385851) B1385851
theorem B4157945 : Blo 1230433 4157945 := bstep (se 2 (by rfl) ⟨1559229, by rfl⟩ : syracuseStep 4157945 = 3118459) B3118459
theorem B1872479 : Blo 1230433 1872479 := bstep (se 1 (by rfl) ⟨1404359, by rfl⟩ : syracuseStep 1872479 = 2808719) B2808719
theorem B1847903 : Blo 1230433 1847903 := bstep (se 1 (by rfl) ⟨1385927, by rfl⟩ : syracuseStep 1847903 = 2771855) B2771855
theorem B5919355 : Blo 1230433 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B2077447 : Blo 1230433 2077447 := bstep (se 1 (by rfl) ⟨1558085, by rfl⟩ : syracuseStep 2077447 = 3116171) B3116171
theorem B4158215 : Blo 1230433 4158215 := bstep (se 1 (by rfl) ⟨3118661, by rfl⟩ : syracuseStep 4158215 = 6237323) B6237323
theorem B2077481 : Blo 1230433 2077481 := bstep (se 2 (by rfl) ⟨779055, by rfl⟩ : syracuseStep 2077481 = 1558111) B1558111
theorem B4158269 : Blo 1230433 4158269 := bstep (se 3 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 4158269 = 1559351) B1559351
theorem B3945341 : Blo 1230433 3945341 := bstep (se 3 (by rfl) ⟨739751, by rfl⟩ : syracuseStep 3945341 = 1479503) B1479503
theorem B3117953 : Blo 1230433 3117953 := bstep (se 2 (by rfl) ⟨1169232, by rfl⟩ : syracuseStep 3117953 = 2338465) B2338465
theorem B15774695 : Blo 1230433 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B2077751 : Blo 1230433 2077751 := bstep (se 1 (by rfl) ⟨1558313, by rfl⟩ : syracuseStep 2077751 = 3116627) B3116627
theorem B3118135 : Blo 1230433 3118135 := bstep (se 1 (by rfl) ⟨2338601, by rfl⟩ : syracuseStep 3118135 = 4677203) B4677203
theorem B5919799 : Blo 1230433 5919799 := bstep (se 1 (by rfl) ⟨4439849, by rfl⟩ : syracuseStep 5919799 = 8879699) B8879699
theorem B1848383 : Blo 1230433 1848383 := bstep (se 1 (by rfl) ⟨1386287, by rfl⟩ : syracuseStep 1848383 = 2772575) B2772575
theorem B1848425 : Blo 1230433 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B3945611 : Blo 1230433 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B1848527 : Blo 1230433 1848527 := bstep (se 1 (by rfl) ⟨1386395, by rfl⟩ : syracuseStep 1848527 = 2772791) B2772791
theorem B33690917 : Blo 1230433 33690917 := bstep (se 4 (by rfl) ⟨3158523, by rfl⟩ : syracuseStep 33690917 = 6317047) B6317047
theorem B3118763 : Blo 1230433 3118763 := bstep (se 1 (by rfl) ⟨2339072, by rfl⟩ : syracuseStep 3118763 = 4678145) B4678145
theorem B16225981 : Blo 1230433 16225981 := bstep (se 3 (by rfl) ⟨3042371, by rfl⟩ : syracuseStep 16225981 = 6084743) B6084743
theorem B2078527 : Blo 1230433 2078527 := bstep (se 1 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 2078527 = 3117791) B3117791
theorem B4159295 : Blo 1230433 4159295 := bstep (se 1 (by rfl) ⟨3119471, by rfl⟩ : syracuseStep 4159295 = 6238943) B6238943
theorem B7018447 : Blo 1230433 7018447 := bstep (se 1 (by rfl) ⟨5263835, by rfl⟩ : syracuseStep 7018447 = 10527671) B10527671
theorem B3119087 : Blo 1230433 3119087 := bstep (se 1 (by rfl) ⟨2339315, by rfl⟩ : syracuseStep 3119087 = 4678631) B4678631
theorem B7886915 : Blo 1230433 7886915 := bstep (se 1 (by rfl) ⟨5915186, by rfl⟩ : syracuseStep 7886915 = 11830373) B11830373
theorem B3160147 : Blo 1230433 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B6322259 : Blo 1230433 6322259 := bstep (se 1 (by rfl) ⟨4741694, by rfl⟩ : syracuseStep 6322259 = 9483389) B9483389
theorem B4675745 : Blo 1230433 4675745 := bstep (se 2 (by rfl) ⟨1753404, by rfl⟩ : syracuseStep 4675745 = 3506809) B3506809
theorem B7887041 : Blo 1230433 7887041 := bstep (se 2 (by rfl) ⟨2957640, by rfl⟩ : syracuseStep 7887041 = 5915281) B5915281
theorem B10524937 : Blo 1230433 10524937 := bstep (se 2 (by rfl) ⟨3946851, by rfl⟩ : syracuseStep 10524937 = 7893703) B7893703
theorem B8870267 : Blo 1230433 8870267 := bstep (se 1 (by rfl) ⟨6652700, by rfl⟩ : syracuseStep 8870267 = 13305401) B13305401
theorem B10656143 : Blo 1230433 10656143 := bstep (se 1 (by rfl) ⟨7992107, by rfl⟩ : syracuseStep 10656143 = 15984215) B15984215
theorem B2079263 : Blo 1230433 2079263 := bstep (se 1 (by rfl) ⟨1559447, by rfl⟩ : syracuseStep 2079263 = 3118895) B3118895
theorem B2079337 : Blo 1230433 2079337 := bstep (se 2 (by rfl) ⟨779751, by rfl⟩ : syracuseStep 2079337 = 1559503) B1559503
theorem B35109551 : Blo 1230433 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B14981921 : Blo 1230433 14981921 := bstep (se 2 (by rfl) ⟨5618220, by rfl⟩ : syracuseStep 14981921 = 11236441) B11236441
theorem B1579867 : Blo 1230433 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B2079695 : Blo 1230433 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B1973369 : Blo 1230433 1973369 := bstep (se 2 (by rfl) ⟨740013, by rfl⟩ : syracuseStep 1973369 = 1480027) B1480027
theorem B1711225 : Blo 1230433 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B6233273 : Blo 1230433 6233273 := bstep (se 2 (by rfl) ⟨2337477, by rfl⟩ : syracuseStep 6233273 = 4674955) B4674955
theorem B15170935 : Blo 1230433 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B4152923 : Blo 1230433 4152923 := bstep (se 1 (by rfl) ⟨3114692, by rfl⟩ : syracuseStep 4152923 = 6229385) B6229385
theorem B11837137 : Blo 1230433 11837137 := bstep (se 2 (by rfl) ⟨4438926, by rfl⟩ : syracuseStep 11837137 = 8877853) B8877853
theorem B4439863 : Blo 1230433 4439863 := bstep (se 1 (by rfl) ⟨3329897, by rfl⟩ : syracuseStep 4439863 = 6659795) B6659795
theorem B2769083 : Blo 1230433 2769083 := bstep (se 1 (by rfl) ⟨2076812, by rfl⟩ : syracuseStep 2769083 = 4153625) B4153625
theorem B37912855 : Blo 1230433 37912855 := bstep (se 1 (by rfl) ⟨28434641, by rfl⟩ : syracuseStep 37912855 = 56869283) B56869283
theorem B2769191 : Blo 1230433 2769191 := bstep (se 1 (by rfl) ⟨2076893, by rfl⟩ : syracuseStep 2769191 = 4153787) B4153787
theorem B14033249 : Blo 1230433 14033249 := bstep (se 2 (by rfl) ⟨5262468, by rfl⟩ : syracuseStep 14033249 = 10524937) B10524937
theorem B21332375 : Blo 1230433 21332375 := bstep (se 1 (by rfl) ⟨15999281, by rfl⟩ : syracuseStep 21332375 = 31998563) B31998563
theorem B1384987 : Blo 1230433 1384987 := bstep (se 1 (by rfl) ⟨1038740, by rfl⟩ : syracuseStep 1384987 = 2077481) B2077481
theorem B2630227 : Blo 1230433 2630227 := bstep (se 1 (by rfl) ⟨1972670, by rfl⟩ : syracuseStep 2630227 = 3945341) B3945341
theorem B8872577 : Blo 1230433 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B9126533 : Blo 1230433 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B2769569 : Blo 1230433 2769569 := bstep (se 2 (by rfl) ⟨1038588, by rfl⟩ : syracuseStep 2769569 = 2077177) B2077177
theorem B1385167 : Blo 1230433 1385167 := bstep (se 1 (by rfl) ⟨1038875, by rfl⟩ : syracuseStep 1385167 = 2077751) B2077751
theorem B33686225 : Blo 1230433 33686225 := bstep (se 2 (by rfl) ⟨12632334, by rfl⟩ : syracuseStep 33686225 = 25264669) B25264669
theorem B2630407 : Blo 1230433 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B2769929 : Blo 1230433 2769929 := bstep (se 2 (by rfl) ⟨1038723, by rfl⟩ : syracuseStep 2769929 = 2077447) B2077447
theorem B2769983 : Blo 1230433 2769983 := bstep (se 1 (by rfl) ⟨2077487, by rfl⟩ : syracuseStep 2769983 = 4154975) B4154975
theorem B14419133 : Blo 1230433 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B23651585 : Blo 1230433 23651585 := bstep (se 2 (by rfl) ⟨8869344, by rfl⟩ : syracuseStep 23651585 = 17738689) B17738689
theorem B56845637 : Blo 1230433 56845637 := bstep (se 4 (by rfl) ⟨5329278, by rfl⟩ : syracuseStep 56845637 = 10658557) B10658557
theorem B3327389 : Blo 1230433 3327389 := bstep (se 3 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 3327389 = 1247771) B1247771
theorem B5260727 : Blo 1230433 5260727 := bstep (se 1 (by rfl) ⟨3945545, by rfl⟩ : syracuseStep 5260727 = 7891091) B7891091
theorem B7104095 : Blo 1230433 7104095 := bstep (se 1 (by rfl) ⟨5328071, by rfl⟩ : syracuseStep 7104095 = 10656143) B10656143
theorem B4441709 : Blo 1230433 4441709 := bstep (se 3 (by rfl) ⟨832820, by rfl⟩ : syracuseStep 4441709 = 1665641) B1665641
theorem B7014073 : Blo 1230433 7014073 := bstep (se 2 (by rfl) ⟨2630277, by rfl⟩ : syracuseStep 7014073 = 5260555) B5260555
theorem B1230527 : Blo 1230433 1230527 := bstep (se 1 (by rfl) ⟨922895, by rfl⟩ : syracuseStep 1230527 = 1845791) B1845791
theorem B1558207 : Blo 1230433 1558207 := bstep (se 1 (by rfl) ⟨1168655, by rfl⟩ : syracuseStep 1558207 = 2337311) B2337311
theorem B1386175 : Blo 1230433 1386175 := bstep (se 1 (by rfl) ⟨1039631, by rfl⟩ : syracuseStep 1386175 = 2079263) B2079263
theorem B23406367 : Blo 1230433 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B20227913 : Blo 1230433 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B9987947 : Blo 1230433 9987947 := bstep (se 1 (by rfl) ⟨7490960, by rfl⟩ : syracuseStep 9987947 = 14981921) B14981921
theorem B3114895 : Blo 1230433 3114895 := bstep (se 1 (by rfl) ⟨2336171, by rfl⟩ : syracuseStep 3114895 = 4672343) B4672343
theorem B1230783 : Blo 1230433 1230783 := bstep (se 1 (by rfl) ⟨923087, by rfl⟩ : syracuseStep 1230783 = 1846175) B1846175
theorem B1230815 : Blo 1230433 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B1386463 : Blo 1230433 1386463 := bstep (se 1 (by rfl) ⟨1039847, by rfl⟩ : syracuseStep 1386463 = 2079695) B2079695
theorem B2770919 : Blo 1230433 2770919 := bstep (se 1 (by rfl) ⟨2078189, by rfl⟩ : syracuseStep 2770919 = 4156379) B4156379
theorem B1230875 : Blo 1230433 1230875 := bstep (se 1 (by rfl) ⟨923156, by rfl⟩ : syracuseStep 1230875 = 1846313) B1846313
theorem B1230879 : Blo 1230433 1230879 := bstep (se 1 (by rfl) ⟨923159, by rfl⟩ : syracuseStep 1230879 = 1846319) B1846319
theorem B1230895 : Blo 1230433 1230895 := bstep (se 1 (by rfl) ⟨923171, by rfl⟩ : syracuseStep 1230895 = 1846343) B1846343
theorem B4155515 : Blo 1230433 4155515 := bstep (se 1 (by rfl) ⟨3116636, by rfl⟩ : syracuseStep 4155515 = 6233273) B6233273
theorem B2771099 : Blo 1230433 2771099 := bstep (se 1 (by rfl) ⟨2078324, by rfl⟩ : syracuseStep 2771099 = 4156649) B4156649
theorem B3115169 : Blo 1230433 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B1231071 : Blo 1230433 1231071 := bstep (se 1 (by rfl) ⟨923303, by rfl⟩ : syracuseStep 1231071 = 1846607) B1846607
theorem B1231131 : Blo 1230433 1231131 := bstep (se 1 (by rfl) ⟨923348, by rfl⟩ : syracuseStep 1231131 = 1846697) B1846697
theorem B14420285 : Blo 1230433 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B2771279 : Blo 1230433 2771279 := bstep (se 1 (by rfl) ⟨2078459, by rfl⟩ : syracuseStep 2771279 = 4156919) B4156919
theorem B28821851 : Blo 1230433 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B1231231 : Blo 1230433 1231231 := bstep (se 1 (by rfl) ⟨923423, by rfl⟩ : syracuseStep 1231231 = 1846847) B1846847
theorem B4155785 : Blo 1230433 4155785 := bstep (se 2 (by rfl) ⟨1558419, by rfl⟩ : syracuseStep 4155785 = 3116839) B3116839
theorem B2771369 : Blo 1230433 2771369 := bstep (se 2 (by rfl) ⟨1039263, by rfl⟩ : syracuseStep 2771369 = 2078527) B2078527
theorem B1231407 : Blo 1230433 1231407 := bstep (se 1 (by rfl) ⟨923555, by rfl⟩ : syracuseStep 1231407 = 1847111) B1847111
theorem B1231463 : Blo 1230433 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B9357929 : Blo 1230433 9357929 := bstep (se 2 (by rfl) ⟨3509223, by rfl⟩ : syracuseStep 9357929 = 7018447) B7018447
theorem B4213529 : Blo 1230433 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B50539315 : Blo 1230433 50539315 := bstep (se 1 (by rfl) ⟨37904486, by rfl⟩ : syracuseStep 50539315 = 75808973) B75808973
theorem B3746767 : Blo 1230433 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B1231839 : Blo 1230433 1231839 := bstep (se 1 (by rfl) ⟨923879, by rfl⟩ : syracuseStep 1231839 = 1847759) B1847759
theorem B5262317 : Blo 1230433 5262317 := bstep (se 3 (by rfl) ⟨986684, by rfl⟩ : syracuseStep 5262317 = 1973369) B1973369
theorem B1231867 : Blo 1230433 1231867 := bstep (se 1 (by rfl) ⟨923900, by rfl⟩ : syracuseStep 1231867 = 1847801) B1847801
theorem B2771963 : Blo 1230433 2771963 := bstep (se 1 (by rfl) ⟨2078972, by rfl⟩ : syracuseStep 2771963 = 4157945) B4157945
theorem B1248319 : Blo 1230433 1248319 := bstep (se 1 (by rfl) ⟨936239, by rfl⟩ : syracuseStep 1248319 = 1872479) B1872479
theorem B1231935 : Blo 1230433 1231935 := bstep (se 1 (by rfl) ⟨923951, by rfl⟩ : syracuseStep 1231935 = 1847903) B1847903
theorem B3943495 : Blo 1230433 3943495 := bstep (se 1 (by rfl) ⟨2957621, by rfl⟩ : syracuseStep 3943495 = 5915243) B5915243
theorem B79834247 : Blo 1230433 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B2772143 : Blo 1230433 2772143 := bstep (se 1 (by rfl) ⟨2079107, by rfl⟩ : syracuseStep 2772143 = 4158215) B4158215
theorem B2772179 : Blo 1230433 2772179 := bstep (se 1 (by rfl) ⟨2079134, by rfl⟩ : syracuseStep 2772179 = 4158269) B4158269
theorem B1846583 : Blo 1230433 1846583 := bstep (se 1 (by rfl) ⟨1384937, by rfl⟩ : syracuseStep 1846583 = 2769875) B2769875
theorem B1232255 : Blo 1230433 1232255 := bstep (se 1 (by rfl) ⟨924191, by rfl⟩ : syracuseStep 1232255 = 1848383) B1848383
theorem B1232283 : Blo 1230433 1232283 := bstep (se 1 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 1232283 = 1848425) B1848425
theorem B2371027 : Blo 1230433 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1846751 : Blo 1230433 1846751 := bstep (se 1 (by rfl) ⟨1385063, by rfl⟩ : syracuseStep 1846751 = 2770127) B2770127
theorem B1232351 : Blo 1230433 1232351 := bstep (se 1 (by rfl) ⟨924263, by rfl⟩ : syracuseStep 1232351 = 1848527) B1848527
theorem B2772449 : Blo 1230433 2772449 := bstep (se 2 (by rfl) ⟨1039668, by rfl⟩ : syracuseStep 2772449 = 2079337) B2079337
theorem B7892473 : Blo 1230433 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B23654045 : Blo 1230433 23654045 := bstep (se 3 (by rfl) ⟨4435133, by rfl⟩ : syracuseStep 23654045 = 8870267) B8870267
theorem B1846967 : Blo 1230433 1846967 := bstep (se 1 (by rfl) ⟨1385225, by rfl⟩ : syracuseStep 1846967 = 2770451) B2770451
theorem B2772863 : Blo 1230433 2772863 := bstep (se 1 (by rfl) ⟨2079647, by rfl⟩ : syracuseStep 2772863 = 4159295) B4159295
theorem B1847177 : Blo 1230433 1847177 := bstep (se 2 (by rfl) ⟨692691, by rfl⟩ : syracuseStep 1847177 = 1385383) B1385383
theorem B11235347 : Blo 1230433 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B4214839 : Blo 1230433 4214839 := bstep (se 1 (by rfl) ⟨3161129, by rfl⟩ : syracuseStep 4214839 = 6322259) B6322259
theorem B2076745 : Blo 1230433 2076745 := bstep (se 2 (by rfl) ⟨778779, by rfl⟩ : syracuseStep 2076745 = 1557559) B1557559
theorem B4157513 : Blo 1230433 4157513 := bstep (se 2 (by rfl) ⟨1559067, by rfl⟩ : syracuseStep 4157513 = 3118135) B3118135
theorem B7893065 : Blo 1230433 7893065 := bstep (se 2 (by rfl) ⟨2959899, by rfl⟩ : syracuseStep 7893065 = 5919799) B5919799
theorem B3117163 : Blo 1230433 3117163 := bstep (se 1 (by rfl) ⟨2337872, by rfl⟩ : syracuseStep 3117163 = 4675745) B4675745
theorem B2076799 : Blo 1230433 2076799 := bstep (se 1 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 2076799 = 3115199) B3115199
theorem B1847423 : Blo 1230433 1847423 := bstep (se 1 (by rfl) ⟨1385567, by rfl⟩ : syracuseStep 1847423 = 2771135) B2771135
theorem B8425957 : Blo 1230433 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B1848059 : Blo 1230433 1848059 := bstep (se 1 (by rfl) ⟨1386044, by rfl⟩ : syracuseStep 1848059 = 2772089) B2772089
theorem B18002807 : Blo 1230433 18002807 := bstep (se 1 (by rfl) ⟨13502105, by rfl⟩ : syracuseStep 18002807 = 27004211) B27004211
theorem B15782849 : Blo 1230433 15782849 := bstep (se 2 (by rfl) ⟨5918568, by rfl⟩ : syracuseStep 15782849 = 11837137) B11837137
theorem B5256251 : Blo 1230433 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B5919817 : Blo 1230433 5919817 := bstep (se 2 (by rfl) ⟨2219931, by rfl⟩ : syracuseStep 5919817 = 4439863) B4439863
theorem B2077879 : Blo 1230433 2077879 := bstep (se 1 (by rfl) ⟨1558409, by rfl⟩ : syracuseStep 2077879 = 3116819) B3116819
theorem B4158647 : Blo 1230433 4158647 := bstep (se 1 (by rfl) ⟨3118985, by rfl⟩ : syracuseStep 4158647 = 6237971) B6237971
theorem B1848503 : Blo 1230433 1848503 := bstep (se 1 (by rfl) ⟨1386377, by rfl⟩ : syracuseStep 1848503 = 2772755) B2772755
theorem B3331325 : Blo 1230433 3331325 := bstep (se 3 (by rfl) ⟨624623, by rfl⟩ : syracuseStep 3331325 = 1249247) B1249247
theorem B35517973 : Blo 1230433 35517973 := bstep (se 6 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 35517973 = 1664905) B1664905
theorem B5257001 : Blo 1230433 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B3118945 : Blo 1230433 3118945 := bstep (se 2 (by rfl) ⟨1169604, by rfl⟩ : syracuseStep 3118945 = 2339209) B2339209
theorem B2078635 : Blo 1230433 2078635 := bstep (se 1 (by rfl) ⟨1558976, by rfl⟩ : syracuseStep 2078635 = 3117953) B3117953
theorem B10516463 : Blo 1230433 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B22460611 : Blo 1230433 22460611 := bstep (se 1 (by rfl) ⟨16845458, by rfl⟩ : syracuseStep 22460611 = 33690917) B33690917
theorem B86538565 : Blo 1230433 86538565 := bstep (se 4 (by rfl) ⟨8112990, by rfl⟩ : syracuseStep 86538565 = 16225981) B16225981
theorem B2079175 : Blo 1230433 2079175 := bstep (se 1 (by rfl) ⟨1559381, by rfl⟩ : syracuseStep 2079175 = 3118763) B3118763
theorem B2079391 : Blo 1230433 2079391 := bstep (se 1 (by rfl) ⟨1559543, by rfl⟩ : syracuseStep 2079391 = 3119087) B3119087
theorem B5257943 : Blo 1230433 5257943 := bstep (se 1 (by rfl) ⟨3943457, by rfl⟩ : syracuseStep 5257943 = 7886915) B7886915
theorem B9984761 : Blo 1230433 9984761 := bstep (se 2 (by rfl) ⟨3744285, by rfl⟩ : syracuseStep 9984761 = 7488571) B7488571
theorem B5258027 : Blo 1230433 5258027 := bstep (se 1 (by rfl) ⟨3943520, by rfl⟩ : syracuseStep 5258027 = 7887041) B7887041
theorem B2628587 : Blo 1230433 2628587 := bstep (se 1 (by rfl) ⟨1971440, by rfl⟩ : syracuseStep 2628587 = 3942881) B3942881
theorem B41033405 : Blo 1230433 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B2768615 : Blo 1230433 2768615 := bstep (se 1 (by rfl) ⟨2076461, by rfl⟩ : syracuseStep 2768615 = 4152923) B4152923
theorem B1384303 : Blo 1230433 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B5619785 : Blo 1230433 5619785 := bstep (se 2 (by rfl) ⟨2107419, by rfl⟩ : syracuseStep 5619785 = 4214839) B4214839
theorem B2768993 : Blo 1230433 2768993 := bstep (se 2 (by rfl) ⟨1038372, by rfl⟩ : syracuseStep 2768993 = 2076745) B2076745
theorem B2769065 : Blo 1230433 2769065 := bstep (se 2 (by rfl) ⟨1038399, by rfl⟩ : syracuseStep 2769065 = 2076799) B2076799
theorem B9355499 : Blo 1230433 9355499 := bstep (se 1 (by rfl) ⟨7016624, by rfl⟩ : syracuseStep 9355499 = 14033249) B14033249
theorem B14221583 : Blo 1230433 14221583 := bstep (se 1 (by rfl) ⟨10666187, by rfl⟩ : syracuseStep 14221583 = 21332375) B21332375
theorem B5915051 : Blo 1230433 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B115384753 : Blo 1230433 115384753 := bstep (se 2 (by rfl) ⟨43269282, by rfl⟩ : syracuseStep 115384753 = 86538565) B86538565
theorem B12001871 : Blo 1230433 12001871 := bstep (se 1 (by rfl) ⟨9001403, by rfl⟩ : syracuseStep 12001871 = 18002807) B18002807
theorem B3506969 : Blo 1230433 3506969 := bstep (se 2 (by rfl) ⟨1315113, by rfl⟩ : syracuseStep 3506969 = 2630227) B2630227
theorem B37897091 : Blo 1230433 37897091 := bstep (se 1 (by rfl) ⟨28422818, by rfl⟩ : syracuseStep 37897091 = 56845637) B56845637
theorem B3507151 : Blo 1230433 3507151 := bstep (se 1 (by rfl) ⟨2630363, by rfl⟩ : syracuseStep 3507151 = 5260727) B5260727
theorem B3507209 : Blo 1230433 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B4736063 : Blo 1230433 4736063 := bstep (se 1 (by rfl) ⟨3552047, by rfl⟩ : syracuseStep 4736063 = 7104095) B7104095
theorem B13485275 : Blo 1230433 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B2770343 : Blo 1230433 2770343 := bstep (se 1 (by rfl) ⟨2077757, by rfl⟩ : syracuseStep 2770343 = 4155515) B4155515
theorem B1664425 : Blo 1230433 1664425 := bstep (se 2 (by rfl) ⟨624159, by rfl⟩ : syracuseStep 1664425 = 1248319) B1248319
theorem B2770505 : Blo 1230433 2770505 := bstep (se 2 (by rfl) ⟨1038939, by rfl⟩ : syracuseStep 2770505 = 2077879) B2077879
theorem B2770523 : Blo 1230433 2770523 := bstep (se 1 (by rfl) ⟨2077892, by rfl⟩ : syracuseStep 2770523 = 4155785) B4155785
theorem B109422413 : Blo 1230433 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B3508211 : Blo 1230433 3508211 := bstep (se 1 (by rfl) ⟨2631158, by rfl⟩ : syracuseStep 3508211 = 5262317) B5262317
theorem B14018669 : Blo 1230433 14018669 := bstep (se 3 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 14018669 = 5257001) B5257001
theorem B1231055 : Blo 1230433 1231055 := bstep (se 1 (by rfl) ⟨923291, by rfl⟩ : syracuseStep 1231055 = 1846583) B1846583
theorem B1231167 : Blo 1230433 1231167 := bstep (se 1 (by rfl) ⟨923375, by rfl⟩ : syracuseStep 1231167 = 1846751) B1846751
theorem B1231311 : Blo 1230433 1231311 := bstep (se 1 (by rfl) ⟨923483, by rfl⟩ : syracuseStep 1231311 = 1846967) B1846967
theorem B1845737 : Blo 1230433 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B1845743 : Blo 1230433 1845743 := bstep (se 1 (by rfl) ⟨1384307, by rfl⟩ : syracuseStep 1845743 = 2768615) B2768615
theorem B2771513 : Blo 1230433 2771513 := bstep (se 2 (by rfl) ⟨1039317, by rfl⟩ : syracuseStep 2771513 = 2078635) B2078635
theorem B1231451 : Blo 1230433 1231451 := bstep (se 1 (by rfl) ⟨923588, by rfl⟩ : syracuseStep 1231451 = 1847177) B1847177
theorem B7490231 : Blo 1230433 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B2771675 : Blo 1230433 2771675 := bstep (se 1 (by rfl) ⟨2078756, by rfl⟩ : syracuseStep 2771675 = 4157513) B4157513
theorem B5262043 : Blo 1230433 5262043 := bstep (se 1 (by rfl) ⟨3946532, by rfl⟩ : syracuseStep 5262043 = 7893065) B7893065
theorem B1231615 : Blo 1230433 1231615 := bstep (se 1 (by rfl) ⟨923711, by rfl⟩ : syracuseStep 1231615 = 1847423) B1847423
theorem B1846055 : Blo 1230433 1846055 := bstep (se 1 (by rfl) ⟨1384541, by rfl⟩ : syracuseStep 1846055 = 2769083) B2769083
theorem B4156217 : Blo 1230433 4156217 := bstep (se 2 (by rfl) ⟨1558581, by rfl⟩ : syracuseStep 4156217 = 3117163) B3117163
theorem B1846127 : Blo 1230433 1846127 := bstep (se 1 (by rfl) ⟨1384595, by rfl⟩ : syracuseStep 1846127 = 2769191) B2769191
theorem B1846379 : Blo 1230433 1846379 := bstep (se 1 (by rfl) ⟨1384784, by rfl⟩ : syracuseStep 1846379 = 2769569) B2769569
theorem B22457483 : Blo 1230433 22457483 := bstep (se 1 (by rfl) ⟨16843112, by rfl⟩ : syracuseStep 22457483 = 33686225) B33686225
theorem B1232039 : Blo 1230433 1232039 := bstep (se 1 (by rfl) ⟨924029, by rfl⟩ : syracuseStep 1232039 = 1848059) B1848059
theorem B2772233 : Blo 1230433 2772233 := bstep (se 2 (by rfl) ⟨1039587, by rfl⟩ : syracuseStep 2772233 = 2079175) B2079175
theorem B10521899 : Blo 1230433 10521899 := bstep (se 1 (by rfl) ⟨7891424, by rfl⟩ : syracuseStep 10521899 = 15782849) B15782849
theorem B11234609 : Blo 1230433 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B8883533 : Blo 1230433 8883533 := bstep (se 3 (by rfl) ⟨1665662, by rfl⟩ : syracuseStep 8883533 = 3331325) B3331325
theorem B1846619 : Blo 1230433 1846619 := bstep (se 1 (by rfl) ⟨1384964, by rfl⟩ : syracuseStep 1846619 = 2769929) B2769929
theorem B1846649 : Blo 1230433 1846649 := bstep (se 2 (by rfl) ⟨692493, by rfl⟩ : syracuseStep 1846649 = 1384987) B1384987
theorem B1846655 : Blo 1230433 1846655 := bstep (se 1 (by rfl) ⟨1384991, by rfl⟩ : syracuseStep 1846655 = 2769983) B2769983
theorem B2772431 : Blo 1230433 2772431 := bstep (se 1 (by rfl) ⟨2079323, by rfl⟩ : syracuseStep 2772431 = 4158647) B4158647
theorem B1232335 : Blo 1230433 1232335 := bstep (se 1 (by rfl) ⟨924251, by rfl⟩ : syracuseStep 1232335 = 1848503) B1848503
theorem B9612755 : Blo 1230433 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B2772521 : Blo 1230433 2772521 := bstep (se 2 (by rfl) ⟨1039695, by rfl⟩ : syracuseStep 2772521 = 2079391) B2079391
theorem B1846889 : Blo 1230433 1846889 := bstep (se 2 (by rfl) ⟨692583, by rfl⟩ : syracuseStep 1846889 = 1385167) B1385167
theorem B2961139 : Blo 1230433 2961139 := bstep (se 1 (by rfl) ⟨2220854, by rfl⟩ : syracuseStep 2961139 = 4441709) B4441709
theorem B1847279 : Blo 1230433 1847279 := bstep (se 1 (by rfl) ⟨1385459, by rfl⟩ : syracuseStep 1847279 = 2770919) B2770919
theorem B7893089 : Blo 1230433 7893089 := bstep (se 2 (by rfl) ⟨2959908, by rfl⟩ : syracuseStep 7893089 = 5919817) B5919817
theorem B1847399 : Blo 1230433 1847399 := bstep (se 1 (by rfl) ⟨1385549, by rfl⟩ : syracuseStep 1847399 = 2771099) B2771099
theorem B2076779 : Blo 1230433 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B9613523 : Blo 1230433 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B1847519 : Blo 1230433 1847519 := bstep (se 1 (by rfl) ⟨1385639, by rfl⟩ : syracuseStep 1847519 = 2771279) B2771279
theorem B19214567 : Blo 1230433 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B1847579 : Blo 1230433 1847579 := bstep (se 1 (by rfl) ⟨1385684, by rfl⟩ : syracuseStep 1847579 = 2771369) B2771369
theorem B6238619 : Blo 1230433 6238619 := bstep (se 1 (by rfl) ⟨4678964, by rfl⟩ : syracuseStep 6238619 = 9357929) B9357929
theorem B6656507 : Blo 1230433 6656507 := bstep (se 1 (by rfl) ⟨4992380, by rfl⟩ : syracuseStep 6656507 = 9984761) B9984761
theorem B10523297 : Blo 1230433 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B1847975 : Blo 1230433 1847975 := bstep (se 1 (by rfl) ⟨1385981, by rfl⟩ : syracuseStep 1847975 = 2771963) B2771963
theorem B1848095 : Blo 1230433 1848095 := bstep (se 1 (by rfl) ⟨1386071, by rfl⟩ : syracuseStep 1848095 = 2772143) B2772143
theorem B1848119 : Blo 1230433 1848119 := bstep (se 1 (by rfl) ⟨1386089, by rfl⟩ : syracuseStep 1848119 = 2772179) B2772179
theorem B9352097 : Blo 1230433 9352097 := bstep (se 2 (by rfl) ⟨3507036, by rfl⟩ : syracuseStep 9352097 = 7014073) B7014073
theorem B2077609 : Blo 1230433 2077609 := bstep (se 2 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 2077609 = 1558207) B1558207
theorem B1848233 : Blo 1230433 1848233 := bstep (se 2 (by rfl) ⟨693087, by rfl⟩ : syracuseStep 1848233 = 1386175) B1386175
theorem B1848299 : Blo 1230433 1848299 := bstep (se 1 (by rfl) ⟨1386224, by rfl⟩ : syracuseStep 1848299 = 2772449) B2772449
theorem B31208489 : Blo 1230433 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B4158593 : Blo 1230433 4158593 := bstep (se 2 (by rfl) ⟨1559472, by rfl⟩ : syracuseStep 4158593 = 3118945) B3118945
theorem B1848575 : Blo 1230433 1848575 := bstep (se 1 (by rfl) ⟨1386431, by rfl⟩ : syracuseStep 1848575 = 2772863) B2772863
theorem B1848617 : Blo 1230433 1848617 := bstep (se 2 (by rfl) ⟨693231, by rfl⟩ : syracuseStep 1848617 = 1386463) B1386463
theorem B29947481 : Blo 1230433 29947481 := bstep (se 2 (by rfl) ⟨11230305, by rfl⟩ : syracuseStep 29947481 = 22460611) B22460611
theorem B50550473 : Blo 1230433 50550473 := bstep (se 2 (by rfl) ⟨18956427, by rfl⟩ : syracuseStep 50550473 = 37912855) B37912855
theorem B6084355 : Blo 1230433 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B3504167 : Blo 1230433 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B15767723 : Blo 1230433 15767723 := bstep (se 1 (by rfl) ⟨11825792, by rfl⟩ : syracuseStep 15767723 = 23651585) B23651585
theorem B2218259 : Blo 1230433 2218259 := bstep (se 1 (by rfl) ⟨1663694, by rfl⟩ : syracuseStep 2218259 = 3327389) B3327389
theorem B67385753 : Blo 1230433 67385753 := bstep (se 2 (by rfl) ⟨25269657, by rfl⟩ : syracuseStep 67385753 = 50539315) B50539315
theorem B6658631 : Blo 1230433 6658631 := bstep (se 1 (by rfl) ⟨4993973, by rfl⟩ : syracuseStep 6658631 = 9987947) B9987947
theorem B4995689 : Blo 1230433 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B7010975 : Blo 1230433 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B5257993 : Blo 1230433 5257993 := bstep (se 2 (by rfl) ⟨1971747, by rfl⟩ : syracuseStep 5257993 = 3943495) B3943495
theorem B3505295 : Blo 1230433 3505295 := bstep (se 1 (by rfl) ⟨2628971, by rfl⟩ : syracuseStep 3505295 = 5257943) B5257943
theorem B2809019 : Blo 1230433 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B3505351 : Blo 1230433 3505351 := bstep (se 1 (by rfl) ⟨2629013, by rfl⟩ : syracuseStep 3505351 = 5258027) B5258027
theorem B3161369 : Blo 1230433 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B1752391 : Blo 1230433 1752391 := bstep (se 1 (by rfl) ⟨1314293, by rfl⟩ : syracuseStep 1752391 = 2628587) B2628587
theorem B47357297 : Blo 1230433 47357297 := bstep (se 2 (by rfl) ⟨17758986, by rfl⟩ : syracuseStep 47357297 = 35517973) B35517973
theorem B53222831 : Blo 1230433 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B15769363 : Blo 1230433 15769363 := bstep (se 1 (by rfl) ⟨11827022, by rfl⟩ : syracuseStep 15769363 = 23654045) B23654045
theorem B4153193 : Blo 1230433 4153193 := bstep (se 2 (by rfl) ⟨1557447, by rfl⟩ : syracuseStep 4153193 = 3114895) B3114895
theorem B1384519 : Blo 1230433 1384519 := bstep (se 1 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 1384519 = 2076779) B2076779
theorem B153846337 : Blo 1230433 153846337 := bstep (se 2 (by rfl) ⟨57692376, by rfl⟩ : syracuseStep 153846337 = 115384753) B115384753
theorem B25264727 : Blo 1230433 25264727 := bstep (se 1 (by rfl) ⟨18948545, by rfl⟩ : syracuseStep 25264727 = 37897091) B37897091
theorem B6234731 : Blo 1230433 6234731 := bstep (se 1 (by rfl) ⟨4676048, by rfl⟩ : syracuseStep 6234731 = 9352097) B9352097
theorem B5915357 : Blo 1230433 5915357 := bstep (se 3 (by rfl) ⟨1109129, by rfl⟩ : syracuseStep 5915357 = 2218259) B2218259
theorem B8430317 : Blo 1230433 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B19964987 : Blo 1230433 19964987 := bstep (se 1 (by rfl) ⟨14973740, by rfl⟩ : syracuseStep 19964987 = 29947481) B29947481
theorem B2770145 : Blo 1230433 2770145 := bstep (se 2 (by rfl) ⟨1038804, by rfl⟩ : syracuseStep 2770145 = 2077609) B2077609
theorem B2336111 : Blo 1230433 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B10511815 : Blo 1230433 10511815 := bstep (se 1 (by rfl) ⟨7883861, by rfl⟩ : syracuseStep 10511815 = 15767723) B15767723
theorem B13321837 : Blo 1230433 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B1230491 : Blo 1230433 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B1230495 : Blo 1230433 1230495 := bstep (se 1 (by rfl) ⟨922871, by rfl⟩ : syracuseStep 1230495 = 1845743) B1845743
theorem B2336521 : Blo 1230433 2336521 := bstep (se 2 (by rfl) ⟨876195, by rfl⟩ : syracuseStep 2336521 = 1752391) B1752391
theorem B1230703 : Blo 1230433 1230703 := bstep (se 1 (by rfl) ⟨923027, by rfl⟩ : syracuseStep 1230703 = 1846055) B1846055
theorem B2770811 : Blo 1230433 2770811 := bstep (se 1 (by rfl) ⟨2078108, by rfl⟩ : syracuseStep 2770811 = 4156217) B4156217
theorem B1230751 : Blo 1230433 1230751 := bstep (se 1 (by rfl) ⟨923063, by rfl⟩ : syracuseStep 1230751 = 1846127) B1846127
theorem B1230919 : Blo 1230433 1230919 := bstep (se 1 (by rfl) ⟨923189, by rfl⟩ : syracuseStep 1230919 = 1846379) B1846379
theorem B2336863 : Blo 1230433 2336863 := bstep (se 1 (by rfl) ⟨1752647, by rfl⟩ : syracuseStep 2336863 = 3505295) B3505295
theorem B7014599 : Blo 1230433 7014599 := bstep (se 1 (by rfl) ⟨5260949, by rfl⟩ : syracuseStep 7014599 = 10521899) B10521899
theorem B7489739 : Blo 1230433 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B1231079 : Blo 1230433 1231079 := bstep (se 1 (by rfl) ⟨923309, by rfl⟩ : syracuseStep 1231079 = 1846619) B1846619
theorem B1231099 : Blo 1230433 1231099 := bstep (se 1 (by rfl) ⟨923324, by rfl⟩ : syracuseStep 1231099 = 1846649) B1846649
theorem B1231103 : Blo 1230433 1231103 := bstep (se 1 (by rfl) ⟨923327, by rfl⟩ : syracuseStep 1231103 = 1846655) B1846655
theorem B35481887 : Blo 1230433 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B6408503 : Blo 1230433 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B8112473 : Blo 1230433 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B1231259 : Blo 1230433 1231259 := bstep (se 1 (by rfl) ⟨923444, by rfl⟩ : syracuseStep 1231259 = 1846889) B1846889
theorem B1231519 : Blo 1230433 1231519 := bstep (se 1 (by rfl) ⟨923639, by rfl⟩ : syracuseStep 1231519 = 1847279) B1847279
theorem B1845995 : Blo 1230433 1845995 := bstep (se 1 (by rfl) ⟨1384496, by rfl⟩ : syracuseStep 1845995 = 2768993) B2768993
theorem B5262059 : Blo 1230433 5262059 := bstep (se 1 (by rfl) ⟨3946544, by rfl⟩ : syracuseStep 5262059 = 7893089) B7893089
theorem B1231599 : Blo 1230433 1231599 := bstep (se 1 (by rfl) ⟨923699, by rfl⟩ : syracuseStep 1231599 = 1847399) B1847399
theorem B1846043 : Blo 1230433 1846043 := bstep (se 1 (by rfl) ⟨1384532, by rfl⟩ : syracuseStep 1846043 = 2769065) B2769065
theorem B1231679 : Blo 1230433 1231679 := bstep (se 1 (by rfl) ⟨923759, by rfl⟩ : syracuseStep 1231679 = 1847519) B1847519
theorem B6236999 : Blo 1230433 6236999 := bstep (se 1 (by rfl) ⟨4677749, by rfl⟩ : syracuseStep 6236999 = 9355499) B9355499
theorem B9481055 : Blo 1230433 9481055 := bstep (se 1 (by rfl) ⟨7110791, by rfl⟩ : syracuseStep 9481055 = 14221583) B14221583
theorem B1231719 : Blo 1230433 1231719 := bstep (se 1 (by rfl) ⟨923789, by rfl⟩ : syracuseStep 1231719 = 1847579) B1847579
theorem B3943367 : Blo 1230433 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B7015531 : Blo 1230433 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B1231983 : Blo 1230433 1231983 := bstep (se 1 (by rfl) ⟨923987, by rfl⟩ : syracuseStep 1231983 = 1847975) B1847975
theorem B7490717 : Blo 1230433 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B2337979 : Blo 1230433 2337979 := bstep (se 1 (by rfl) ⟨1753484, by rfl⟩ : syracuseStep 2337979 = 3506969) B3506969
theorem B1232063 : Blo 1230433 1232063 := bstep (se 1 (by rfl) ⟨924047, by rfl⟩ : syracuseStep 1232063 = 1848095) B1848095
theorem B1232079 : Blo 1230433 1232079 := bstep (se 1 (by rfl) ⟨924059, by rfl⟩ : syracuseStep 1232079 = 1848119) B1848119
theorem B25636061 : Blo 1230433 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B1232155 : Blo 1230433 1232155 := bstep (se 1 (by rfl) ⟨924116, by rfl⟩ : syracuseStep 1232155 = 1848233) B1848233
theorem B1232199 : Blo 1230433 1232199 := bstep (se 1 (by rfl) ⟨924149, by rfl⟩ : syracuseStep 1232199 = 1848299) B1848299
theorem B2338139 : Blo 1230433 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B3157375 : Blo 1230433 3157375 := bstep (se 1 (by rfl) ⟨2368031, by rfl⟩ : syracuseStep 3157375 = 4736063) B4736063
theorem B2772395 : Blo 1230433 2772395 := bstep (se 1 (by rfl) ⟨2079296, by rfl⟩ : syracuseStep 2772395 = 4158593) B4158593
theorem B59944373 : Blo 1230433 59944373 := bstep (se 5 (by rfl) ⟨2809892, by rfl⟩ : syracuseStep 59944373 = 5619785) B5619785
theorem B8990183 : Blo 1230433 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B1232383 : Blo 1230433 1232383 := bstep (se 1 (by rfl) ⟨924287, by rfl⟩ : syracuseStep 1232383 = 1848575) B1848575
theorem B1232411 : Blo 1230433 1232411 := bstep (se 1 (by rfl) ⟨924308, by rfl⟩ : syracuseStep 1232411 = 1848617) B1848617
theorem B1846895 : Blo 1230433 1846895 := bstep (se 1 (by rfl) ⟨1385171, by rfl⟩ : syracuseStep 1846895 = 2770343) B2770343
theorem B7016057 : Blo 1230433 7016057 := bstep (se 2 (by rfl) ⟨2631021, by rfl⟩ : syracuseStep 7016057 = 5262043) B5262043
theorem B1847003 : Blo 1230433 1847003 := bstep (se 1 (by rfl) ⟨1385252, by rfl⟩ : syracuseStep 1847003 = 2770505) B2770505
theorem B1847015 : Blo 1230433 1847015 := bstep (se 1 (by rfl) ⟨1385261, by rfl⟩ : syracuseStep 1847015 = 2770523) B2770523
theorem B2338807 : Blo 1230433 2338807 := bstep (se 1 (by rfl) ⟨1754105, by rfl⟩ : syracuseStep 2338807 = 3508211) B3508211
theorem B4673801 : Blo 1230433 4673801 := bstep (se 2 (by rfl) ⟨1752675, by rfl⟩ : syracuseStep 4673801 = 3505351) B3505351
theorem B1847675 : Blo 1230433 1847675 := bstep (se 1 (by rfl) ⟨1385756, by rfl⟩ : syracuseStep 1847675 = 2771513) B2771513
theorem B4673983 : Blo 1230433 4673983 := bstep (se 1 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 4673983 = 7010975) B7010975
theorem B4993487 : Blo 1230433 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B1847783 : Blo 1230433 1847783 := bstep (se 1 (by rfl) ⟨1385837, by rfl⟩ : syracuseStep 1847783 = 2771675) B2771675
theorem B14971655 : Blo 1230433 14971655 := bstep (se 1 (by rfl) ⟨11228741, by rfl⟩ : syracuseStep 14971655 = 22457483) B22457483
theorem B1848155 : Blo 1230433 1848155 := bstep (se 1 (by rfl) ⟨1386116, by rfl⟩ : syracuseStep 1848155 = 2772233) B2772233
theorem B1848287 : Blo 1230433 1848287 := bstep (se 1 (by rfl) ⟨1386215, by rfl⟩ : syracuseStep 1848287 = 2772431) B2772431
theorem B21025817 : Blo 1230433 21025817 := bstep (se 2 (by rfl) ⟨7884681, by rfl⟩ : syracuseStep 21025817 = 15769363) B15769363
theorem B1848347 : Blo 1230433 1848347 := bstep (se 1 (by rfl) ⟨1386260, by rfl⟩ : syracuseStep 1848347 = 2772521) B2772521
theorem B12809711 : Blo 1230433 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B4159079 : Blo 1230433 4159079 := bstep (se 1 (by rfl) ⟨3119309, by rfl⟩ : syracuseStep 4159079 = 6238619) B6238619
theorem B4437671 : Blo 1230433 4437671 := bstep (se 1 (by rfl) ⟨3328253, by rfl⟩ : syracuseStep 4437671 = 6656507) B6656507
theorem B8001247 : Blo 1230433 8001247 := bstep (se 1 (by rfl) ⟨6000935, by rfl⟩ : syracuseStep 8001247 = 12001871) B12001871
theorem B20805659 : Blo 1230433 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B7010657 : Blo 1230433 7010657 := bstep (se 2 (by rfl) ⟨2628996, by rfl⟩ : syracuseStep 7010657 = 5257993) B5257993
theorem B33700315 : Blo 1230433 33700315 := bstep (se 1 (by rfl) ⟨25275236, by rfl⟩ : syracuseStep 33700315 = 50550473) B50550473
theorem B72948275 : Blo 1230433 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B4676201 : Blo 1230433 4676201 := bstep (se 2 (by rfl) ⟨1753575, by rfl⟩ : syracuseStep 4676201 = 3507151) B3507151
theorem B9345779 : Blo 1230433 9345779 := bstep (se 1 (by rfl) ⟨7009334, by rfl⟩ : syracuseStep 9345779 = 14018669) B14018669
theorem B44923835 : Blo 1230433 44923835 := bstep (se 1 (by rfl) ⟨33692876, by rfl⟩ : syracuseStep 44923835 = 67385753) B67385753
theorem B4439087 : Blo 1230433 4439087 := bstep (se 1 (by rfl) ⟨3329315, by rfl⟩ : syracuseStep 4439087 = 6658631) B6658631
theorem B2219233 : Blo 1230433 2219233 := bstep (se 2 (by rfl) ⟨832212, by rfl⟩ : syracuseStep 2219233 = 1664425) B1664425
theorem B5922355 : Blo 1230433 5922355 := bstep (se 1 (by rfl) ⟨4441766, by rfl⟩ : syracuseStep 5922355 = 8883533) B8883533
theorem B31571531 : Blo 1230433 31571531 := bstep (se 1 (by rfl) ⟨23678648, by rfl⟩ : syracuseStep 31571531 = 47357297) B47357297
theorem B3948185 : Blo 1230433 3948185 := bstep (se 2 (by rfl) ⟨1480569, by rfl⟩ : syracuseStep 3948185 = 2961139) B2961139
theorem B2768795 : Blo 1230433 2768795 := bstep (se 1 (by rfl) ⟨2076596, by rfl⟩ : syracuseStep 2768795 = 4153193) B4153193
theorem B16843151 : Blo 1230433 16843151 := bstep (se 1 (by rfl) ⟨12632363, by rfl⟩ : syracuseStep 16843151 = 25264727) B25264727
theorem B5620211 : Blo 1230433 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B44933753 : Blo 1230433 44933753 := bstep (se 2 (by rfl) ⟨16850157, by rfl⟩ : syracuseStep 44933753 = 33700315) B33700315
theorem B14017211 : Blo 1230433 14017211 := bstep (se 1 (by rfl) ⟨10512908, by rfl⟩ : syracuseStep 14017211 = 21025817) B21025817
theorem B205128449 : Blo 1230433 205128449 := bstep (se 2 (by rfl) ⟨76923168, by rfl⟩ : syracuseStep 205128449 = 153846337) B153846337
theorem B1557407 : Blo 1230433 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B13870439 : Blo 1230433 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B5408315 : Blo 1230433 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B2958977 : Blo 1230433 2958977 := bstep (se 2 (by rfl) ⟨1109616, by rfl⟩ : syracuseStep 2958977 = 2219233) B2219233
theorem B1230663 : Blo 1230433 1230663 := bstep (se 1 (by rfl) ⟨922997, by rfl⟩ : syracuseStep 1230663 = 1845995) B1845995
theorem B3508039 : Blo 1230433 3508039 := bstep (se 1 (by rfl) ⟨2631029, by rfl⟩ : syracuseStep 3508039 = 5262059) B5262059
theorem B1230695 : Blo 1230433 1230695 := bstep (se 1 (by rfl) ⟨923021, by rfl⟩ : syracuseStep 1230695 = 1846043) B1846043
theorem B2959391 : Blo 1230433 2959391 := bstep (se 1 (by rfl) ⟨2219543, by rfl⟩ : syracuseStep 2959391 = 4439087) B4439087
theorem B17762449 : Blo 1230433 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B17090707 : Blo 1230433 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B1558759 : Blo 1230433 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B25282813 : Blo 1230433 25282813 := bstep (se 3 (by rfl) ⟨4740527, by rfl⟩ : syracuseStep 25282813 = 9481055) B9481055
theorem B39962915 : Blo 1230433 39962915 := bstep (se 1 (by rfl) ⟨29972186, by rfl⟩ : syracuseStep 39962915 = 59944373) B59944373
theorem B10668329 : Blo 1230433 10668329 := bstep (se 2 (by rfl) ⟨4000623, by rfl⟩ : syracuseStep 10668329 = 8001247) B8001247
theorem B3115361 : Blo 1230433 3115361 := bstep (se 2 (by rfl) ⟨1168260, by rfl⟩ : syracuseStep 3115361 = 2336521) B2336521
theorem B21047687 : Blo 1230433 21047687 := bstep (se 1 (by rfl) ⟨15785765, by rfl⟩ : syracuseStep 21047687 = 31571531) B31571531
theorem B1231263 : Blo 1230433 1231263 := bstep (se 1 (by rfl) ⟨923447, by rfl⟩ : syracuseStep 1231263 = 1846895) B1846895
theorem B2632123 : Blo 1230433 2632123 := bstep (se 1 (by rfl) ⟨1974092, by rfl⟩ : syracuseStep 2632123 = 3948185) B3948185
theorem B1231335 : Blo 1230433 1231335 := bstep (se 1 (by rfl) ⟨923501, by rfl⟩ : syracuseStep 1231335 = 1847003) B1847003
theorem B1231343 : Blo 1230433 1231343 := bstep (se 1 (by rfl) ⟨923507, by rfl⟩ : syracuseStep 1231343 = 1847015) B1847015
theorem B1845863 : Blo 1230433 1845863 := bstep (se 1 (by rfl) ⟨1384397, by rfl⟩ : syracuseStep 1845863 = 2768795) B2768795
theorem B1846025 : Blo 1230433 1846025 := bstep (se 2 (by rfl) ⟨692259, by rfl⟩ : syracuseStep 1846025 = 1384519) B1384519
theorem B3115817 : Blo 1230433 3115817 := bstep (se 2 (by rfl) ⟨1168431, by rfl⟩ : syracuseStep 3115817 = 2336863) B2336863
theorem B3115867 : Blo 1230433 3115867 := bstep (se 1 (by rfl) ⟨2336900, by rfl⟩ : syracuseStep 3115867 = 4673801) B4673801
theorem B1231783 : Blo 1230433 1231783 := bstep (se 1 (by rfl) ⟨923837, by rfl⟩ : syracuseStep 1231783 = 1847675) B1847675
theorem B3328991 : Blo 1230433 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B1231855 : Blo 1230433 1231855 := bstep (se 1 (by rfl) ⟨923891, by rfl⟩ : syracuseStep 1231855 = 1847783) B1847783
theorem B4156487 : Blo 1230433 4156487 := bstep (se 1 (by rfl) ⟨3117365, by rfl⟩ : syracuseStep 4156487 = 6234731) B6234731
theorem B3943571 : Blo 1230433 3943571 := bstep (se 1 (by rfl) ⟨2957678, by rfl⟩ : syracuseStep 3943571 = 5915357) B5915357
theorem B9981103 : Blo 1230433 9981103 := bstep (se 1 (by rfl) ⟨7485827, by rfl⟩ : syracuseStep 9981103 = 14971655) B14971655
theorem B1232103 : Blo 1230433 1232103 := bstep (se 1 (by rfl) ⟨924077, by rfl⟩ : syracuseStep 1232103 = 1848155) B1848155
theorem B1232191 : Blo 1230433 1232191 := bstep (se 1 (by rfl) ⟨924143, by rfl⟩ : syracuseStep 1232191 = 1848287) B1848287
theorem B1232231 : Blo 1230433 1232231 := bstep (se 1 (by rfl) ⟨924173, by rfl⟩ : syracuseStep 1232231 = 1848347) B1848347
theorem B1846763 : Blo 1230433 1846763 := bstep (se 1 (by rfl) ⟨1385072, by rfl⟩ : syracuseStep 1846763 = 2770145) B2770145
theorem B2772719 : Blo 1230433 2772719 := bstep (se 1 (by rfl) ⟨2079539, by rfl⟩ : syracuseStep 2772719 = 4159079) B4159079
theorem B1847207 : Blo 1230433 1847207 := bstep (se 1 (by rfl) ⟨1385405, by rfl⟩ : syracuseStep 1847207 = 2770811) B2770811
theorem B4993159 : Blo 1230433 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B23654591 : Blo 1230433 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B4272335 : Blo 1230433 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B4673771 : Blo 1230433 4673771 := bstep (se 1 (by rfl) ⟨3505328, by rfl⟩ : syracuseStep 4673771 = 7010657) B7010657
theorem B3117305 : Blo 1230433 3117305 := bstep (se 2 (by rfl) ⟨1168989, by rfl⟩ : syracuseStep 3117305 = 2337979) B2337979
theorem B48632183 : Blo 1230433 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B3117467 : Blo 1230433 3117467 := bstep (se 1 (by rfl) ⟨2338100, by rfl⟩ : syracuseStep 3117467 = 4676201) B4676201
theorem B11833789 : Blo 1230433 11833789 := bstep (se 3 (by rfl) ⟨2218835, by rfl⟩ : syracuseStep 11833789 = 4437671) B4437671
theorem B6230519 : Blo 1230433 6230519 := bstep (se 1 (by rfl) ⟨4672889, by rfl⟩ : syracuseStep 6230519 = 9345779) B9345779
theorem B4157999 : Blo 1230433 4157999 := bstep (se 1 (by rfl) ⟨3118499, by rfl⟩ : syracuseStep 4157999 = 6236999) B6236999
theorem B4993811 : Blo 1230433 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B1848263 : Blo 1230433 1848263 := bstep (se 1 (by rfl) ⟨1386197, by rfl⟩ : syracuseStep 1848263 = 2772395) B2772395
theorem B5993455 : Blo 1230433 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B3118409 : Blo 1230433 3118409 := bstep (se 2 (by rfl) ⟨1169403, by rfl⟩ : syracuseStep 3118409 = 2338807) B2338807
theorem B6231977 : Blo 1230433 6231977 := bstep (se 2 (by rfl) ⟨2336991, by rfl⟩ : syracuseStep 6231977 = 4673983) B4673983
theorem B13309991 : Blo 1230433 13309991 := bstep (se 1 (by rfl) ⟨9982493, by rfl⟩ : syracuseStep 13309991 = 19964987) B19964987
theorem B34159229 : Blo 1230433 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B4676399 : Blo 1230433 4676399 := bstep (se 1 (by rfl) ⟨3507299, by rfl⟩ : syracuseStep 4676399 = 7014599) B7014599
theorem B9354041 : Blo 1230433 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B4209833 : Blo 1230433 4209833 := bstep (se 2 (by rfl) ⟨1578687, by rfl⟩ : syracuseStep 4209833 = 3157375) B3157375
theorem B14015753 : Blo 1230433 14015753 := bstep (se 2 (by rfl) ⟨5255907, by rfl⟩ : syracuseStep 14015753 = 10511815) B10511815
theorem B29949223 : Blo 1230433 29949223 := bstep (se 1 (by rfl) ⟨22461917, by rfl⟩ : syracuseStep 29949223 = 44923835) B44923835
theorem B2628911 : Blo 1230433 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B7896473 : Blo 1230433 7896473 := bstep (se 2 (by rfl) ⟨2961177, by rfl⟩ : syracuseStep 7896473 = 5922355) B5922355
theorem B4677371 : Blo 1230433 4677371 := bstep (se 1 (by rfl) ⟨3508028, by rfl⟩ : syracuseStep 4677371 = 7016057) B7016057
theorem B15769727 : Blo 1230433 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B23683265 : Blo 1230433 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B4153679 : Blo 1230433 4153679 := bstep (se 1 (by rfl) ⟨3115259, by rfl⟩ : syracuseStep 4153679 = 6230519) B6230519
theorem B33710417 : Blo 1230433 33710417 := bstep (se 2 (by rfl) ⟨12641406, by rfl⟩ : syracuseStep 33710417 = 25282813) B25282813
theorem B15778385 : Blo 1230433 15778385 := bstep (se 2 (by rfl) ⟨5916894, by rfl⟩ : syracuseStep 15778385 = 11833789) B11833789
theorem B3605543 : Blo 1230433 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B4154489 : Blo 1230433 4154489 := bstep (se 2 (by rfl) ⟨1557933, by rfl⟩ : syracuseStep 4154489 = 3115867) B3115867
theorem B4154651 : Blo 1230433 4154651 := bstep (se 1 (by rfl) ⟨3115988, by rfl⟩ : syracuseStep 4154651 = 6231977) B6231977
theorem B8873327 : Blo 1230433 8873327 := bstep (se 1 (by rfl) ⟨6654995, by rfl⟩ : syracuseStep 8873327 = 13309991) B13309991
theorem B26641943 : Blo 1230433 26641943 := bstep (se 1 (by rfl) ⟨19981457, by rfl⟩ : syracuseStep 26641943 = 39962915) B39962915
theorem B7112219 : Blo 1230433 7112219 := bstep (se 1 (by rfl) ⟨5334164, by rfl⟩ : syracuseStep 7112219 = 10668329) B10668329
theorem B7890605 : Blo 1230433 7890605 := bstep (se 3 (by rfl) ⟨1479488, by rfl⟩ : syracuseStep 7890605 = 2958977) B2958977
theorem B1230575 : Blo 1230433 1230575 := bstep (se 1 (by rfl) ⟨922931, by rfl⟩ : syracuseStep 1230575 = 1845863) B1845863
theorem B1230683 : Blo 1230433 1230683 := bstep (se 1 (by rfl) ⟨923012, by rfl⟩ : syracuseStep 1230683 = 1846025) B1846025
theorem B6236027 : Blo 1230433 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B2770991 : Blo 1230433 2770991 := bstep (se 1 (by rfl) ⟨2078243, by rfl⟩ : syracuseStep 2770991 = 4156487) B4156487
theorem B1231175 : Blo 1230433 1231175 := bstep (se 1 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 1231175 = 1846763) B1846763
theorem B1231471 : Blo 1230433 1231471 := bstep (se 1 (by rfl) ⟨923603, by rfl⟩ : syracuseStep 1231471 = 1847207) B1847207
theorem B3115847 : Blo 1230433 3115847 := bstep (se 1 (by rfl) ⟨2336885, by rfl⟩ : syracuseStep 3115847 = 4673771) B4673771
theorem B3746807 : Blo 1230433 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B2771999 : Blo 1230433 2771999 := bstep (se 1 (by rfl) ⟨2078999, by rfl⟩ : syracuseStep 2771999 = 4157999) B4157999
theorem B11226221 : Blo 1230433 11226221 := bstep (se 3 (by rfl) ⟨2104916, by rfl⟩ : syracuseStep 11226221 = 4209833) B4209833
theorem B136752299 : Blo 1230433 136752299 := bstep (se 1 (by rfl) ⟨102564224, by rfl⟩ : syracuseStep 136752299 = 205128449) B205128449
theorem B3329207 : Blo 1230433 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B3509497 : Blo 1230433 3509497 := bstep (se 2 (by rfl) ⟨1316061, by rfl⟩ : syracuseStep 3509497 = 2632123) B2632123
theorem B1232175 : Blo 1230433 1232175 := bstep (se 1 (by rfl) ⟨924131, by rfl⟩ : syracuseStep 1232175 = 1848263) B1848263
theorem B7991273 : Blo 1230433 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B13308137 : Blo 1230433 13308137 := bstep (se 2 (by rfl) ⟨4990551, by rfl⟩ : syracuseStep 13308137 = 9981103) B9981103
theorem B2076907 : Blo 1230433 2076907 := bstep (se 1 (by rfl) ⟨1557680, by rfl⟩ : syracuseStep 2076907 = 3115361) B3115361
theorem B39932297 : Blo 1230433 39932297 := bstep (se 2 (by rfl) ⟨14974611, by rfl⟩ : syracuseStep 39932297 = 29949223) B29949223
theorem B2077211 : Blo 1230433 2077211 := bstep (se 1 (by rfl) ⟨1557908, by rfl⟩ : syracuseStep 2077211 = 3115817) B3115817
theorem B3117599 : Blo 1230433 3117599 := bstep (se 1 (by rfl) ⟨2338199, by rfl⟩ : syracuseStep 3117599 = 4676399) B4676399
theorem B9343835 : Blo 1230433 9343835 := bstep (se 1 (by rfl) ⟨7007876, by rfl⟩ : syracuseStep 9343835 = 14015753) B14015753
theorem B5264315 : Blo 1230433 5264315 := bstep (se 1 (by rfl) ⟨3948236, by rfl⟩ : syracuseStep 5264315 = 7896473) B7896473
theorem B1848479 : Blo 1230433 1848479 := bstep (se 1 (by rfl) ⟨1386359, by rfl⟩ : syracuseStep 1848479 = 2772719) B2772719
theorem B3118247 : Blo 1230433 3118247 := bstep (se 1 (by rfl) ⟨2338685, by rfl⟩ : syracuseStep 3118247 = 4677371) B4677371
theorem B2848223 : Blo 1230433 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B2078203 : Blo 1230433 2078203 := bstep (se 1 (by rfl) ⟨1558652, by rfl⟩ : syracuseStep 2078203 = 3117305) B3117305
theorem B6657545 : Blo 1230433 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B22787609 : Blo 1230433 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B32421455 : Blo 1230433 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B2078311 : Blo 1230433 2078311 := bstep (se 1 (by rfl) ⟨1558733, by rfl⟩ : syracuseStep 2078311 = 3117467) B3117467
theorem B2078345 : Blo 1230433 2078345 := bstep (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) B1558759
theorem B10516189 : Blo 1230433 10516189 := bstep (se 3 (by rfl) ⟨1971785, by rfl⟩ : syracuseStep 10516189 = 3943571) B3943571
theorem B29955835 : Blo 1230433 29955835 := bstep (se 1 (by rfl) ⟨22466876, by rfl⟩ : syracuseStep 29955835 = 44933753) B44933753
theorem B9344807 : Blo 1230433 9344807 := bstep (se 1 (by rfl) ⟨7008605, by rfl⟩ : syracuseStep 9344807 = 14017211) B14017211
theorem B2078939 : Blo 1230433 2078939 := bstep (se 1 (by rfl) ⟨1559204, by rfl⟩ : syracuseStep 2078939 = 3118409) B3118409
theorem B9246959 : Blo 1230433 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B44915069 : Blo 1230433 44915069 := bstep (se 3 (by rfl) ⟨8421575, by rfl⟩ : syracuseStep 44915069 = 16843151) B16843151
theorem B1972927 : Blo 1230433 1972927 := bstep (se 1 (by rfl) ⟨1479695, by rfl⟩ : syracuseStep 1972927 = 2959391) B2959391
theorem B14031791 : Blo 1230433 14031791 := bstep (se 1 (by rfl) ⟨10523843, by rfl⟩ : syracuseStep 14031791 = 21047687) B21047687
theorem B22772819 : Blo 1230433 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B2219327 : Blo 1230433 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B1752607 : Blo 1230433 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B4153085 : Blo 1230433 4153085 := bstep (se 3 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 4153085 = 1557407) B1557407
theorem B4677385 : Blo 1230433 4677385 := bstep (se 2 (by rfl) ⟨1754019, by rfl⟩ : syracuseStep 4677385 = 3508039) B3508039
theorem B8872091 : Blo 1230433 8872091 := bstep (se 1 (by rfl) ⟨6654068, by rfl⟩ : syracuseStep 8872091 = 13308137) B13308137
theorem B9347237 : Blo 1230433 9347237 := bstep (se 4 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 9347237 = 1752607) B1752607
theorem B2769119 : Blo 1230433 2769119 := bstep (se 1 (by rfl) ⟨2076839, by rfl⟩ : syracuseStep 2769119 = 4153679) B4153679
theorem B2769209 : Blo 1230433 2769209 := bstep (se 2 (by rfl) ⟨1038453, by rfl⟩ : syracuseStep 2769209 = 2076907) B2076907
theorem B1384807 : Blo 1230433 1384807 := bstep (se 1 (by rfl) ⟨1038605, by rfl⟩ : syracuseStep 1384807 = 2077211) B2077211
theorem B10518923 : Blo 1230433 10518923 := bstep (se 1 (by rfl) ⟨7889192, by rfl⟩ : syracuseStep 10518923 = 15778385) B15778385
theorem B2769659 : Blo 1230433 2769659 := bstep (se 1 (by rfl) ⟨2077244, by rfl⟩ : syracuseStep 2769659 = 4154489) B4154489
theorem B2769767 : Blo 1230433 2769767 := bstep (se 1 (by rfl) ⟨2077325, by rfl⟩ : syracuseStep 2769767 = 4154651) B4154651
theorem B5915551 : Blo 1230433 5915551 := bstep (se 1 (by rfl) ⟨4436663, by rfl⟩ : syracuseStep 5915551 = 8873327) B8873327
theorem B2630569 : Blo 1230433 2630569 := bstep (se 2 (by rfl) ⟨986463, by rfl⟩ : syracuseStep 2630569 = 1972927) B1972927
theorem B17761295 : Blo 1230433 17761295 := bstep (se 1 (by rfl) ⟨13320971, by rfl⟩ : syracuseStep 17761295 = 26641943) B26641943
theorem B1385563 : Blo 1230433 1385563 := bstep (se 1 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 1385563 = 2078345) B2078345
theorem B5260403 : Blo 1230433 5260403 := bstep (se 1 (by rfl) ⟨3945302, by rfl⟩ : syracuseStep 5260403 = 7890605) B7890605
theorem B18965917 : Blo 1230433 18965917 := bstep (se 3 (by rfl) ⟨3556109, by rfl⟩ : syracuseStep 18965917 = 7112219) B7112219
theorem B1385959 : Blo 1230433 1385959 := bstep (se 1 (by rfl) ⟨1039469, by rfl⟩ : syracuseStep 1385959 = 2078939) B2078939
theorem B29943379 : Blo 1230433 29943379 := bstep (se 1 (by rfl) ⟨22457534, by rfl⟩ : syracuseStep 29943379 = 44915069) B44915069
theorem B4679329 : Blo 1230433 4679329 := bstep (se 2 (by rfl) ⟨1754748, by rfl⟩ : syracuseStep 4679329 = 3509497) B3509497
theorem B2770937 : Blo 1230433 2770937 := bstep (se 2 (by rfl) ⟨1039101, by rfl⟩ : syracuseStep 2770937 = 2078203) B2078203
theorem B15181879 : Blo 1230433 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2771081 : Blo 1230433 2771081 := bstep (se 2 (by rfl) ⟨1039155, by rfl⟩ : syracuseStep 2771081 = 2078311) B2078311
theorem B6236513 : Blo 1230433 6236513 := bstep (se 2 (by rfl) ⟨2338692, by rfl⟩ : syracuseStep 6236513 = 4677385) B4677385
theorem B5327515 : Blo 1230433 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B10513151 : Blo 1230433 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B15788843 : Blo 1230433 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B22473611 : Blo 1230433 22473611 := bstep (se 1 (by rfl) ⟨16855208, by rfl⟩ : syracuseStep 22473611 = 33710417) B33710417
theorem B6229223 : Blo 1230433 6229223 := bstep (se 1 (by rfl) ⟨4671917, by rfl⟩ : syracuseStep 6229223 = 9343835) B9343835
theorem B3509543 : Blo 1230433 3509543 := bstep (se 1 (by rfl) ⟨2632157, by rfl⟩ : syracuseStep 3509543 = 5264315) B5264315
theorem B2403695 : Blo 1230433 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B1232319 : Blo 1230433 1232319 := bstep (se 1 (by rfl) ⟨924239, by rfl⟩ : syracuseStep 1232319 = 1848479) B1848479
theorem B21614303 : Blo 1230433 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B6229871 : Blo 1230433 6229871 := bstep (se 1 (by rfl) ⟨4672403, by rfl⟩ : syracuseStep 6229871 = 9344807) B9344807
theorem B4157351 : Blo 1230433 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B1847327 : Blo 1230433 1847327 := bstep (se 1 (by rfl) ⟨1385495, by rfl⟩ : syracuseStep 1847327 = 2770991) B2770991
theorem B6164639 : Blo 1230433 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B2077231 : Blo 1230433 2077231 := bstep (se 1 (by rfl) ⟨1557923, by rfl⟩ : syracuseStep 2077231 = 3115847) B3115847
theorem B1847999 : Blo 1230433 1847999 := bstep (se 1 (by rfl) ⟨1385999, by rfl⟩ : syracuseStep 1847999 = 2771999) B2771999
theorem B7484147 : Blo 1230433 7484147 := bstep (se 1 (by rfl) ⟨5613110, by rfl⟩ : syracuseStep 7484147 = 11226221) B11226221
theorem B1479551 : Blo 1230433 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B14021585 : Blo 1230433 14021585 := bstep (se 2 (by rfl) ⟨5258094, by rfl⟩ : syracuseStep 14021585 = 10516189) B10516189
theorem B39941113 : Blo 1230433 39941113 := bstep (se 2 (by rfl) ⟨14977917, by rfl⟩ : syracuseStep 39941113 = 29955835) B29955835
theorem B26621531 : Blo 1230433 26621531 := bstep (se 1 (by rfl) ⟨19966148, by rfl⟩ : syracuseStep 26621531 = 39932297) B39932297
theorem B2078399 : Blo 1230433 2078399 := bstep (se 1 (by rfl) ⟨1558799, by rfl⟩ : syracuseStep 2078399 = 3117599) B3117599
theorem B2078831 : Blo 1230433 2078831 := bstep (se 1 (by rfl) ⟨1559123, by rfl⟩ : syracuseStep 2078831 = 3118247) B3118247
theorem B1898815 : Blo 1230433 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B4438363 : Blo 1230433 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B60766957 : Blo 1230433 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B9354527 : Blo 1230433 9354527 := bstep (se 1 (by rfl) ⟨7015895, by rfl⟩ : syracuseStep 9354527 = 14031791) B14031791
theorem B2497871 : Blo 1230433 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B91168199 : Blo 1230433 91168199 := bstep (se 1 (by rfl) ⟨68376149, by rfl⟩ : syracuseStep 91168199 = 136752299) B136752299
theorem B2219471 : Blo 1230433 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B2768723 : Blo 1230433 2768723 := bstep (se 1 (by rfl) ⟨2076542, by rfl⟩ : syracuseStep 2768723 = 4153085) B4153085
theorem B20242505 : Blo 1230433 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B5914727 : Blo 1230433 5914727 := bstep (se 1 (by rfl) ⟨4436045, by rfl⟩ : syracuseStep 5914727 = 8872091) B8872091
theorem B7012615 : Blo 1230433 7012615 := bstep (se 1 (by rfl) ⟨5259461, by rfl⟩ : syracuseStep 7012615 = 10518923) B10518923
theorem B2531753 : Blo 1230433 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B4989431 : Blo 1230433 4989431 := bstep (se 1 (by rfl) ⟨3742073, by rfl⟩ : syracuseStep 4989431 = 7484147) B7484147
theorem B9347723 : Blo 1230433 9347723 := bstep (se 1 (by rfl) ⟨7010792, by rfl⟩ : syracuseStep 9347723 = 14021585) B14021585
theorem B2769641 : Blo 1230433 2769641 := bstep (se 2 (by rfl) ⟨1038615, by rfl⟩ : syracuseStep 2769641 = 2077231) B2077231
theorem B3506935 : Blo 1230433 3506935 := bstep (se 1 (by rfl) ⟨2630201, by rfl⟩ : syracuseStep 3506935 = 5260403) B5260403
theorem B1385599 : Blo 1230433 1385599 := bstep (se 1 (by rfl) ⟨1039199, by rfl⟩ : syracuseStep 1385599 = 2078399) B2078399
theorem B3507425 : Blo 1230433 3507425 := bstep (se 2 (by rfl) ⟨1315284, by rfl⟩ : syracuseStep 3507425 = 2630569) B2630569
theorem B1385887 : Blo 1230433 1385887 := bstep (se 1 (by rfl) ⟨1039415, by rfl⟩ : syracuseStep 1385887 = 2078831) B2078831
theorem B6236351 : Blo 1230433 6236351 := bstep (se 1 (by rfl) ⟨4677263, by rfl⟩ : syracuseStep 6236351 = 9354527) B9354527
theorem B1665247 : Blo 1230433 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B60778799 : Blo 1230433 60778799 := bstep (se 1 (by rfl) ⟨45584099, by rfl⟩ : syracuseStep 60778799 = 91168199) B91168199
theorem B1845815 : Blo 1230433 1845815 := bstep (se 1 (by rfl) ⟨1384361, by rfl⟩ : syracuseStep 1845815 = 2768723) B2768723
theorem B2771567 : Blo 1230433 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B1231551 : Blo 1230433 1231551 := bstep (se 1 (by rfl) ⟨923663, by rfl⟩ : syracuseStep 1231551 = 1847327) B1847327
theorem B1846079 : Blo 1230433 1846079 := bstep (se 1 (by rfl) ⟨1384559, by rfl⟩ : syracuseStep 1846079 = 2769119) B2769119
theorem B1846139 : Blo 1230433 1846139 := bstep (se 1 (by rfl) ⟨1384604, by rfl⟩ : syracuseStep 1846139 = 2769209) B2769209
theorem B5917817 : Blo 1230433 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B1231999 : Blo 1230433 1231999 := bstep (se 1 (by rfl) ⟨923999, by rfl⟩ : syracuseStep 1231999 = 1847999) B1847999
theorem B1846409 : Blo 1230433 1846409 := bstep (se 2 (by rfl) ⟨692403, by rfl⟩ : syracuseStep 1846409 = 1384807) B1384807
theorem B1846439 : Blo 1230433 1846439 := bstep (se 1 (by rfl) ⟨1384829, by rfl⟩ : syracuseStep 1846439 = 2769659) B2769659
theorem B1846511 : Blo 1230433 1846511 := bstep (se 1 (by rfl) ⟨1384883, by rfl⟩ : syracuseStep 1846511 = 2769767) B2769767
theorem B11840863 : Blo 1230433 11840863 := bstep (se 1 (by rfl) ⟨8880647, by rfl⟩ : syracuseStep 11840863 = 17761295) B17761295
theorem B28413413 : Blo 1230433 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B6409853 : Blo 1230433 6409853 := bstep (se 3 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 6409853 = 2403695) B2403695
theorem B81022609 : Blo 1230433 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B17747687 : Blo 1230433 17747687 := bstep (se 1 (by rfl) ⟨13310765, by rfl⟩ : syracuseStep 17747687 = 26621531) B26621531
theorem B1847291 : Blo 1230433 1847291 := bstep (se 1 (by rfl) ⟨1385468, by rfl⟩ : syracuseStep 1847291 = 2770937) B2770937
theorem B1847387 : Blo 1230433 1847387 := bstep (se 1 (by rfl) ⟨1385540, by rfl⟩ : syracuseStep 1847387 = 2771081) B2771081
theorem B1847417 : Blo 1230433 1847417 := bstep (se 2 (by rfl) ⟨692781, by rfl⟩ : syracuseStep 1847417 = 1385563) B1385563
theorem B4157675 : Blo 1230433 4157675 := bstep (se 1 (by rfl) ⟨3118256, by rfl⟩ : syracuseStep 4157675 = 6236513) B6236513
theorem B7008767 : Blo 1230433 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B1847945 : Blo 1230433 1847945 := bstep (se 2 (by rfl) ⟨692979, by rfl⟩ : syracuseStep 1847945 = 1385959) B1385959
theorem B39924505 : Blo 1230433 39924505 := bstep (se 2 (by rfl) ⟨14971689, by rfl⟩ : syracuseStep 39924505 = 29943379) B29943379
theorem B2339695 : Blo 1230433 2339695 := bstep (se 1 (by rfl) ⟨1754771, by rfl⟩ : syracuseStep 2339695 = 3509543) B3509543
theorem B6239105 : Blo 1230433 6239105 := bstep (se 2 (by rfl) ⟨2339664, by rfl⟩ : syracuseStep 6239105 = 4679329) B4679329
theorem B1479647 : Blo 1230433 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B3945469 : Blo 1230433 3945469 := bstep (se 3 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 3945469 = 1479551) B1479551
theorem B4109759 : Blo 1230433 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B6231491 : Blo 1230433 6231491 := bstep (se 1 (by rfl) ⟨4673618, by rfl⟩ : syracuseStep 6231491 = 9347237) B9347237
theorem B7887401 : Blo 1230433 7887401 := bstep (se 2 (by rfl) ⟨2957775, by rfl⟩ : syracuseStep 7887401 = 5915551) B5915551
theorem B53254817 : Blo 1230433 53254817 := bstep (se 2 (by rfl) ⟨19970556, by rfl⟩ : syracuseStep 53254817 = 39941113) B39941113
theorem B10525895 : Blo 1230433 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B25287889 : Blo 1230433 25287889 := bstep (se 2 (by rfl) ⟨9482958, by rfl⟩ : syracuseStep 25287889 = 18965917) B18965917
theorem B14982407 : Blo 1230433 14982407 := bstep (se 1 (by rfl) ⟨11236805, by rfl⟩ : syracuseStep 14982407 = 22473611) B22473611
theorem B4152815 : Blo 1230433 4152815 := bstep (se 1 (by rfl) ⟨3114611, by rfl⟩ : syracuseStep 4152815 = 6229223) B6229223
theorem B14409535 : Blo 1230433 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B4153247 : Blo 1230433 4153247 := bstep (se 1 (by rfl) ⟨3114935, by rfl⟩ : syracuseStep 4153247 = 6229871) B6229871
theorem B1687835 : Blo 1230433 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B2220329 : Blo 1230433 2220329 := bstep (se 2 (by rfl) ⟨832623, by rfl⟩ : syracuseStep 2220329 = 1665247) B1665247
theorem B3326287 : Blo 1230433 3326287 := bstep (se 1 (by rfl) ⟨2494715, by rfl⟩ : syracuseStep 3326287 = 4989431) B4989431
theorem B4154327 : Blo 1230433 4154327 := bstep (se 1 (by rfl) ⟨3115745, by rfl⟩ : syracuseStep 4154327 = 6231491) B6231491
theorem B53232673 : Blo 1230433 53232673 := bstep (se 2 (by rfl) ⟨19962252, by rfl⟩ : syracuseStep 53232673 = 39924505) B39924505
theorem B5260625 : Blo 1230433 5260625 := bstep (se 2 (by rfl) ⟨1972734, by rfl⟩ : syracuseStep 5260625 = 3945469) B3945469
theorem B40519199 : Blo 1230433 40519199 := bstep (se 1 (by rfl) ⟨30389399, by rfl⟩ : syracuseStep 40519199 = 60778799) B60778799
theorem B1230543 : Blo 1230433 1230543 := bstep (se 1 (by rfl) ⟨922907, by rfl⟩ : syracuseStep 1230543 = 1845815) B1845815
theorem B15787817 : Blo 1230433 15787817 := bstep (se 2 (by rfl) ⟨5920431, by rfl⟩ : syracuseStep 15787817 = 11840863) B11840863
theorem B1230719 : Blo 1230433 1230719 := bstep (se 1 (by rfl) ⟨923039, by rfl⟩ : syracuseStep 1230719 = 1846079) B1846079
theorem B1230759 : Blo 1230433 1230759 := bstep (se 1 (by rfl) ⟨923069, by rfl⟩ : syracuseStep 1230759 = 1846139) B1846139
theorem B1230939 : Blo 1230433 1230939 := bstep (se 1 (by rfl) ⟨923204, by rfl⟩ : syracuseStep 1230939 = 1846409) B1846409
theorem B1230959 : Blo 1230433 1230959 := bstep (se 1 (by rfl) ⟨923219, by rfl⟩ : syracuseStep 1230959 = 1846439) B1846439
theorem B1231007 : Blo 1230433 1231007 := bstep (se 1 (by rfl) ⟨923255, by rfl⟩ : syracuseStep 1231007 = 1846511) B1846511
theorem B9988271 : Blo 1230433 9988271 := bstep (se 1 (by rfl) ⟨7491203, by rfl⟩ : syracuseStep 9988271 = 14982407) B14982407
theorem B108030145 : Blo 1230433 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B18942275 : Blo 1230433 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B19212713 : Blo 1230433 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B11831791 : Blo 1230433 11831791 := bstep (se 1 (by rfl) ⟨8873843, by rfl⟩ : syracuseStep 11831791 = 17747687) B17747687
theorem B1231527 : Blo 1230433 1231527 := bstep (se 1 (by rfl) ⟨923645, by rfl⟩ : syracuseStep 1231527 = 1847291) B1847291
theorem B1231591 : Blo 1230433 1231591 := bstep (se 1 (by rfl) ⟨923693, by rfl⟩ : syracuseStep 1231591 = 1847387) B1847387
theorem B3943151 : Blo 1230433 3943151 := bstep (se 1 (by rfl) ⟨2957363, by rfl⟩ : syracuseStep 3943151 = 5914727) B5914727
theorem B1231611 : Blo 1230433 1231611 := bstep (se 1 (by rfl) ⟨923708, by rfl⟩ : syracuseStep 1231611 = 1847417) B1847417
theorem B2771783 : Blo 1230433 2771783 := bstep (se 1 (by rfl) ⟨2078837, by rfl⟩ : syracuseStep 2771783 = 4157675) B4157675
theorem B53980013 : Blo 1230433 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B15780845 : Blo 1230433 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B4672511 : Blo 1230433 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B9350153 : Blo 1230433 9350153 := bstep (se 2 (by rfl) ⟨3506307, by rfl⟩ : syracuseStep 9350153 = 7012615) B7012615
theorem B1231963 : Blo 1230433 1231963 := bstep (se 1 (by rfl) ⟨923972, by rfl⟩ : syracuseStep 1231963 = 1847945) B1847945
theorem B1846427 : Blo 1230433 1846427 := bstep (se 1 (by rfl) ⟨1384820, by rfl⟩ : syracuseStep 1846427 = 2769641) B2769641
theorem B2338283 : Blo 1230433 2338283 := bstep (se 1 (by rfl) ⟨1753712, by rfl⟩ : syracuseStep 2338283 = 3507425) B3507425
theorem B2739839 : Blo 1230433 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B4157567 : Blo 1230433 4157567 := bstep (se 1 (by rfl) ⟨3118175, by rfl⟩ : syracuseStep 4157567 = 6236351) B6236351
theorem B1847465 : Blo 1230433 1847465 := bstep (se 2 (by rfl) ⟨692799, by rfl⟩ : syracuseStep 1847465 = 1385599) B1385599
theorem B1847711 : Blo 1230433 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B1847849 : Blo 1230433 1847849 := bstep (se 2 (by rfl) ⟨692943, by rfl⟩ : syracuseStep 1847849 = 1385887) B1385887
theorem B7017263 : Blo 1230433 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B4273235 : Blo 1230433 4273235 := bstep (se 1 (by rfl) ⟨3204926, by rfl⟩ : syracuseStep 4273235 = 6409853) B6409853
theorem B3945725 : Blo 1230433 3945725 := bstep (se 3 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 3945725 = 1479647) B1479647
theorem B6231815 : Blo 1230433 6231815 := bstep (se 1 (by rfl) ⟨4673861, by rfl⟩ : syracuseStep 6231815 = 9347723) B9347723
theorem B4159403 : Blo 1230433 4159403 := bstep (se 1 (by rfl) ⟨3119552, by rfl⟩ : syracuseStep 4159403 = 6239105) B6239105
theorem B4675913 : Blo 1230433 4675913 := bstep (se 2 (by rfl) ⟨1753467, by rfl⟩ : syracuseStep 4675913 = 3506935) B3506935
theorem B3119593 : Blo 1230433 3119593 := bstep (se 2 (by rfl) ⟨1169847, by rfl⟩ : syracuseStep 3119593 = 2339695) B2339695
theorem B33717185 : Blo 1230433 33717185 := bstep (se 2 (by rfl) ⟨12643944, by rfl⟩ : syracuseStep 33717185 = 25287889) B25287889
theorem B5258267 : Blo 1230433 5258267 := bstep (se 1 (by rfl) ⟨3943700, by rfl⟩ : syracuseStep 5258267 = 7887401) B7887401
theorem B35503211 : Blo 1230433 35503211 := bstep (se 1 (by rfl) ⟨26627408, by rfl⟩ : syracuseStep 35503211 = 53254817) B53254817
theorem B2768543 : Blo 1230433 2768543 := bstep (se 1 (by rfl) ⟨2076407, by rfl⟩ : syracuseStep 2768543 = 4152815) B4152815
theorem B2768831 : Blo 1230433 2768831 := bstep (se 1 (by rfl) ⟨2076623, by rfl⟩ : syracuseStep 2768831 = 4153247) B4153247
theorem B144040193 : Blo 1230433 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B4678175 : Blo 1230433 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B2769551 : Blo 1230433 2769551 := bstep (se 1 (by rfl) ⟨2077163, by rfl⟩ : syracuseStep 2769551 = 4154327) B4154327
theorem B2630483 : Blo 1230433 2630483 := bstep (se 1 (by rfl) ⟨1972862, by rfl⟩ : syracuseStep 2630483 = 3945725) B3945725
theorem B3507083 : Blo 1230433 3507083 := bstep (se 1 (by rfl) ⟨2630312, by rfl⟩ : syracuseStep 3507083 = 5260625) B5260625
theorem B4154543 : Blo 1230433 4154543 := bstep (se 1 (by rfl) ⟨3115907, by rfl⟩ : syracuseStep 4154543 = 6231815) B6231815
theorem B70976897 : Blo 1230433 70976897 := bstep (se 2 (by rfl) ⟨26616336, by rfl⟩ : syracuseStep 70976897 = 53232673) B53232673
theorem B10520563 : Blo 1230433 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B3115007 : Blo 1230433 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B23668807 : Blo 1230433 23668807 := bstep (se 1 (by rfl) ⟨17751605, by rfl⟩ : syracuseStep 23668807 = 35503211) B35503211
theorem B1230951 : Blo 1230433 1230951 := bstep (se 1 (by rfl) ⟨923213, by rfl⟩ : syracuseStep 1230951 = 1846427) B1846427
theorem B1558855 : Blo 1230433 1558855 := bstep (se 1 (by rfl) ⟨1169141, by rfl⟩ : syracuseStep 1558855 = 2338283) B2338283
theorem B1845695 : Blo 1230433 1845695 := bstep (se 1 (by rfl) ⟨1384271, by rfl⟩ : syracuseStep 1845695 = 2768543) B2768543
theorem B1845887 : Blo 1230433 1845887 := bstep (se 1 (by rfl) ⟨1384415, by rfl⟩ : syracuseStep 1845887 = 2768831) B2768831
theorem B2771711 : Blo 1230433 2771711 := bstep (se 1 (by rfl) ⟨2078783, by rfl⟩ : syracuseStep 2771711 = 4157567) B4157567
theorem B1231643 : Blo 1230433 1231643 := bstep (se 1 (by rfl) ⟨923732, by rfl⟩ : syracuseStep 1231643 = 1847465) B1847465
theorem B1231807 : Blo 1230433 1231807 := bstep (se 1 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 1231807 = 1847711) B1847711
theorem B1231899 : Blo 1230433 1231899 := bstep (se 1 (by rfl) ⟨923924, by rfl⟩ : syracuseStep 1231899 = 1847849) B1847849
theorem B4435049 : Blo 1230433 4435049 := bstep (se 2 (by rfl) ⟨1663143, by rfl⟩ : syracuseStep 4435049 = 3326287) B3326287
theorem B4500893 : Blo 1230433 4500893 := bstep (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) B1687835
theorem B27012799 : Blo 1230433 27012799 := bstep (se 1 (by rfl) ⟨20259599, by rfl⟩ : syracuseStep 27012799 = 40519199) B40519199
theorem B2772935 : Blo 1230433 2772935 := bstep (se 1 (by rfl) ⟨2079701, by rfl⟩ : syracuseStep 2772935 = 4159403) B4159403
theorem B12628183 : Blo 1230433 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B3117275 : Blo 1230433 3117275 := bstep (se 1 (by rfl) ⟨2337956, by rfl⟩ : syracuseStep 3117275 = 4675913) B4675913
theorem B12808475 : Blo 1230433 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B1847855 : Blo 1230433 1847855 := bstep (se 1 (by rfl) ⟨1385891, by rfl⟩ : syracuseStep 1847855 = 2771783) B2771783
theorem B4159457 : Blo 1230433 4159457 := bstep (se 2 (by rfl) ⟨1559796, by rfl⟩ : syracuseStep 4159457 = 3119593) B3119593
theorem B15775721 : Blo 1230433 15775721 := bstep (se 2 (by rfl) ⟨5915895, by rfl⟩ : syracuseStep 15775721 = 11831791) B11831791
theorem B2848823 : Blo 1230433 2848823 := bstep (se 1 (by rfl) ⟨2136617, by rfl⟩ : syracuseStep 2848823 = 4273235) B4273235
theorem B5920877 : Blo 1230433 5920877 := bstep (se 3 (by rfl) ⟨1110164, by rfl⟩ : syracuseStep 5920877 = 2220329) B2220329
theorem B10525211 : Blo 1230433 10525211 := bstep (se 1 (by rfl) ⟨7893908, by rfl⟩ : syracuseStep 10525211 = 15787817) B15787817
theorem B6658847 : Blo 1230433 6658847 := bstep (se 1 (by rfl) ⟨4994135, by rfl⟩ : syracuseStep 6658847 = 9988271) B9988271
theorem B7306237 : Blo 1230433 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B2628767 : Blo 1230433 2628767 := bstep (se 1 (by rfl) ⟨1971575, by rfl⟩ : syracuseStep 2628767 = 3943151) B3943151
theorem B35986675 : Blo 1230433 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B22478123 : Blo 1230433 22478123 := bstep (se 1 (by rfl) ⟨16858592, by rfl⟩ : syracuseStep 22478123 = 33717185) B33717185
theorem B6233435 : Blo 1230433 6233435 := bstep (se 1 (by rfl) ⟨4675076, by rfl⟩ : syracuseStep 6233435 = 9350153) B9350153
theorem B3505511 : Blo 1230433 3505511 := bstep (se 1 (by rfl) ⟨2629133, by rfl⟩ : syracuseStep 3505511 = 5258267) B5258267
theorem B96026795 : Blo 1230433 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B1753655 : Blo 1230433 1753655 := bstep (se 1 (by rfl) ⟨1315241, by rfl⟩ : syracuseStep 1753655 = 2630483) B2630483
theorem B2769695 : Blo 1230433 2769695 := bstep (se 1 (by rfl) ⟨2077271, by rfl⟩ : syracuseStep 2769695 = 4154543) B4154543
theorem B47317931 : Blo 1230433 47317931 := bstep (se 1 (by rfl) ⟨35488448, by rfl⟩ : syracuseStep 47317931 = 70976897) B70976897
theorem B9741649 : Blo 1230433 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B1230463 : Blo 1230433 1230463 := bstep (se 1 (by rfl) ⟨922847, by rfl⟩ : syracuseStep 1230463 = 1845695) B1845695
theorem B47982233 : Blo 1230433 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B1230591 : Blo 1230433 1230591 := bstep (se 1 (by rfl) ⟨922943, by rfl⟩ : syracuseStep 1230591 = 1845887) B1845887
theorem B14985415 : Blo 1230433 14985415 := bstep (se 1 (by rfl) ⟨11239061, by rfl⟩ : syracuseStep 14985415 = 22478123) B22478123
theorem B4155623 : Blo 1230433 4155623 := bstep (se 1 (by rfl) ⟨3116717, by rfl⟩ : syracuseStep 4155623 = 6233435) B6233435
theorem B2337007 : Blo 1230433 2337007 := bstep (se 1 (by rfl) ⟨1752755, by rfl⟩ : syracuseStep 2337007 = 3505511) B3505511
theorem B3000595 : Blo 1230433 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B14027417 : Blo 1230433 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B31558409 : Blo 1230433 31558409 := bstep (se 2 (by rfl) ⟨11834403, by rfl⟩ : syracuseStep 31558409 = 23668807) B23668807
theorem B8538983 : Blo 1230433 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B16837577 : Blo 1230433 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B1231903 : Blo 1230433 1231903 := bstep (se 1 (by rfl) ⟨923927, by rfl⟩ : syracuseStep 1231903 = 1847855) B1847855
theorem B1846367 : Blo 1230433 1846367 := bstep (se 1 (by rfl) ⟨1384775, by rfl⟩ : syracuseStep 1846367 = 2769551) B2769551
theorem B2338055 : Blo 1230433 2338055 := bstep (se 1 (by rfl) ⟨1753541, by rfl⟩ : syracuseStep 2338055 = 3507083) B3507083
theorem B2772971 : Blo 1230433 2772971 := bstep (se 1 (by rfl) ⟨2079728, by rfl⟩ : syracuseStep 2772971 = 4159457) B4159457
theorem B2076671 : Blo 1230433 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B7016807 : Blo 1230433 7016807 := bstep (se 1 (by rfl) ⟨5262605, by rfl⟩ : syracuseStep 7016807 = 10525211) B10525211
theorem B1847807 : Blo 1230433 1847807 := bstep (se 1 (by rfl) ⟨1385855, by rfl⟩ : syracuseStep 1847807 = 2771711) B2771711
theorem B36017065 : Blo 1230433 36017065 := bstep (se 2 (by rfl) ⟨13506399, by rfl⟩ : syracuseStep 36017065 = 27012799) B27012799
theorem B1848623 : Blo 1230433 1848623 := bstep (se 1 (by rfl) ⟨1386467, by rfl⟩ : syracuseStep 1848623 = 2772935) B2772935
theorem B2078183 : Blo 1230433 2078183 := bstep (se 1 (by rfl) ⟨1558637, by rfl⟩ : syracuseStep 2078183 = 3117275) B3117275
theorem B3118783 : Blo 1230433 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B2078473 : Blo 1230433 2078473 := bstep (se 2 (by rfl) ⟨779427, by rfl⟩ : syracuseStep 2078473 = 1558855) B1558855
theorem B10517147 : Blo 1230433 10517147 := bstep (se 1 (by rfl) ⟨7887860, by rfl⟩ : syracuseStep 10517147 = 15775721) B15775721
theorem B1899215 : Blo 1230433 1899215 := bstep (se 1 (by rfl) ⟨1424411, by rfl⟩ : syracuseStep 1899215 = 2848823) B2848823
theorem B3947251 : Blo 1230433 3947251 := bstep (se 1 (by rfl) ⟨2960438, by rfl⟩ : syracuseStep 3947251 = 5920877) B5920877
theorem B4439231 : Blo 1230433 4439231 := bstep (se 1 (by rfl) ⟨3329423, by rfl⟩ : syracuseStep 4439231 = 6658847) B6658847
theorem B2956699 : Blo 1230433 2956699 := bstep (se 1 (by rfl) ⟨2217524, by rfl⟩ : syracuseStep 2956699 = 4435049) B4435049
theorem B1752511 : Blo 1230433 1752511 := bstep (se 1 (by rfl) ⟨1314383, by rfl⟩ : syracuseStep 1752511 = 2628767) B2628767
theorem B4677871 : Blo 1230433 4677871 := bstep (se 1 (by rfl) ⟨3508403, by rfl⟩ : syracuseStep 4677871 = 7016807) B7016807
theorem B19980553 : Blo 1230433 19980553 := bstep (se 2 (by rfl) ⟨7492707, by rfl⟩ : syracuseStep 19980553 = 14985415) B14985415
theorem B64012693 : Blo 1230433 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B1385455 : Blo 1230433 1385455 := bstep (se 1 (by rfl) ⟨1039091, by rfl⟩ : syracuseStep 1385455 = 2078183) B2078183
theorem B2770415 : Blo 1230433 2770415 := bstep (se 1 (by rfl) ⟨2077811, by rfl⟩ : syracuseStep 2770415 = 4155623) B4155623
theorem B127952621 : Blo 1230433 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B21038939 : Blo 1230433 21038939 := bstep (se 1 (by rfl) ⟨15779204, by rfl⟩ : syracuseStep 21038939 = 31558409) B31558409
theorem B3942265 : Blo 1230433 3942265 := bstep (se 2 (by rfl) ⟨1478349, by rfl⟩ : syracuseStep 3942265 = 2956699) B2956699
theorem B2336681 : Blo 1230433 2336681 := bstep (se 2 (by rfl) ⟨876255, by rfl⟩ : syracuseStep 2336681 = 1752511) B1752511
theorem B11225051 : Blo 1230433 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B1230911 : Blo 1230433 1230911 := bstep (se 1 (by rfl) ⟨923183, by rfl⟩ : syracuseStep 1230911 = 1846367) B1846367
theorem B2959487 : Blo 1230433 2959487 := bstep (se 1 (by rfl) ⟨2219615, by rfl⟩ : syracuseStep 2959487 = 4439231) B4439231
theorem B1558703 : Blo 1230433 1558703 := bstep (se 1 (by rfl) ⟨1169027, by rfl⟩ : syracuseStep 1558703 = 2338055) B2338055
theorem B2771297 : Blo 1230433 2771297 := bstep (se 2 (by rfl) ⟨1039236, by rfl⟩ : syracuseStep 2771297 = 2078473) B2078473
theorem B3116009 : Blo 1230433 3116009 := bstep (se 2 (by rfl) ⟨1168503, by rfl⟩ : syracuseStep 3116009 = 2337007) B2337007
theorem B1231871 : Blo 1230433 1231871 := bstep (se 1 (by rfl) ⟨923903, by rfl⟩ : syracuseStep 1231871 = 1847807) B1847807
theorem B1846463 : Blo 1230433 1846463 := bstep (se 1 (by rfl) ⟨1384847, by rfl⟩ : syracuseStep 1846463 = 2769695) B2769695
theorem B1232415 : Blo 1230433 1232415 := bstep (se 1 (by rfl) ⟨924311, by rfl⟩ : syracuseStep 1232415 = 1848623) B1848623
theorem B5263001 : Blo 1230433 5263001 := bstep (se 2 (by rfl) ⟨1973625, by rfl⟩ : syracuseStep 5263001 = 3947251) B3947251
theorem B9351611 : Blo 1230433 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B12988865 : Blo 1230433 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B1266143 : Blo 1230433 1266143 := bstep (se 1 (by rfl) ⟨949607, by rfl⟩ : syracuseStep 1266143 = 1899215) B1899215
theorem B192091013 : Blo 1230433 192091013 := bstep (se 4 (by rfl) ⟨18008532, by rfl⟩ : syracuseStep 192091013 = 36017065) B36017065
theorem B4158377 : Blo 1230433 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B1848647 : Blo 1230433 1848647 := bstep (se 1 (by rfl) ⟨1386485, by rfl⟩ : syracuseStep 1848647 = 2772971) B2772971
theorem B64017863 : Blo 1230433 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B31545287 : Blo 1230433 31545287 := bstep (se 1 (by rfl) ⟨23658965, by rfl⟩ : syracuseStep 31545287 = 47317931) B47317931
theorem B4676413 : Blo 1230433 4676413 := bstep (se 3 (by rfl) ⟨876827, by rfl⟩ : syracuseStep 4676413 = 1753655) B1753655
theorem B7011431 : Blo 1230433 7011431 := bstep (se 1 (by rfl) ⟨5258573, by rfl⟩ : syracuseStep 7011431 = 10517147) B10517147
theorem B5692655 : Blo 1230433 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B1384447 : Blo 1230433 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B6234407 : Blo 1230433 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B8659243 : Blo 1230433 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B26640737 : Blo 1230433 26640737 := bstep (se 2 (by rfl) ⟨9990276, by rfl⟩ : syracuseStep 26640737 = 19980553) B19980553
theorem B6235217 : Blo 1230433 6235217 := bstep (se 2 (by rfl) ⟨2338206, by rfl⟩ : syracuseStep 6235217 = 4676413) B4676413
theorem B14025959 : Blo 1230433 14025959 := bstep (se 1 (by rfl) ⟨10519469, by rfl⟩ : syracuseStep 14025959 = 21038939) B21038939
theorem B1557787 : Blo 1230433 1557787 := bstep (se 1 (by rfl) ⟨1168340, by rfl⟩ : syracuseStep 1557787 = 2336681) B2336681
theorem B21030191 : Blo 1230433 21030191 := bstep (se 1 (by rfl) ⟨15772643, by rfl⟩ : syracuseStep 21030191 = 31545287) B31545287
theorem B1230975 : Blo 1230433 1230975 := bstep (se 1 (by rfl) ⟨923231, by rfl⟩ : syracuseStep 1230975 = 1846463) B1846463
theorem B3795103 : Blo 1230433 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B3508667 : Blo 1230433 3508667 := bstep (se 1 (by rfl) ⟨2631500, by rfl⟩ : syracuseStep 3508667 = 5263001) B5263001
theorem B1845929 : Blo 1230433 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B6237161 : Blo 1230433 6237161 := bstep (se 2 (by rfl) ⟨2338935, by rfl⟩ : syracuseStep 6237161 = 4677871) B4677871
theorem B4156541 : Blo 1230433 4156541 := bstep (se 3 (by rfl) ⟨779351, by rfl⟩ : syracuseStep 4156541 = 1558703) B1558703
theorem B128060675 : Blo 1230433 128060675 := bstep (se 1 (by rfl) ⟨96045506, by rfl⟩ : syracuseStep 128060675 = 192091013) B192091013
theorem B2772251 : Blo 1230433 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B1232431 : Blo 1230433 1232431 := bstep (se 1 (by rfl) ⟨924323, by rfl⟩ : syracuseStep 1232431 = 1848647) B1848647
theorem B1846943 : Blo 1230433 1846943 := bstep (se 1 (by rfl) ⟨1385207, by rfl⟩ : syracuseStep 1846943 = 2770415) B2770415
theorem B7483367 : Blo 1230433 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B1847273 : Blo 1230433 1847273 := bstep (se 2 (by rfl) ⟨692727, by rfl⟩ : syracuseStep 1847273 = 1385455) B1385455
theorem B1847531 : Blo 1230433 1847531 := bstep (se 1 (by rfl) ⟨1385648, by rfl⟩ : syracuseStep 1847531 = 2771297) B2771297
theorem B2077339 : Blo 1230433 2077339 := bstep (se 1 (by rfl) ⟨1558004, by rfl⟩ : syracuseStep 2077339 = 3116009) B3116009
theorem B4674287 : Blo 1230433 4674287 := bstep (se 1 (by rfl) ⟨3505715, by rfl⟩ : syracuseStep 4674287 = 7011431) B7011431
theorem B13505525 : Blo 1230433 13505525 := bstep (se 5 (by rfl) ⟨633071, by rfl⟩ : syracuseStep 13505525 = 1266143) B1266143
theorem B5256353 : Blo 1230433 5256353 := bstep (se 2 (by rfl) ⟨1971132, by rfl⟩ : syracuseStep 5256353 = 3942265) B3942265
theorem B85350257 : Blo 1230433 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B42678575 : Blo 1230433 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B85301747 : Blo 1230433 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B1972991 : Blo 1230433 1972991 := bstep (se 1 (by rfl) ⟨1479743, by rfl⟩ : syracuseStep 1972991 = 2959487) B2959487
theorem B17760491 : Blo 1230433 17760491 := bstep (se 1 (by rfl) ⟨13320368, by rfl⟩ : syracuseStep 17760491 = 26640737) B26640737
theorem B9003683 : Blo 1230433 9003683 := bstep (se 1 (by rfl) ⟨6752762, by rfl⟩ : syracuseStep 9003683 = 13505525) B13505525
theorem B2769785 : Blo 1230433 2769785 := bstep (se 2 (by rfl) ⟨1038669, by rfl⟩ : syracuseStep 2769785 = 2077339) B2077339
theorem B28452383 : Blo 1230433 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B1230619 : Blo 1230433 1230619 := bstep (se 1 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 1230619 = 1845929) B1845929
theorem B2771027 : Blo 1230433 2771027 := bstep (se 1 (by rfl) ⟨2078270, by rfl⟩ : syracuseStep 2771027 = 4156541) B4156541
theorem B1231295 : Blo 1230433 1231295 := bstep (se 1 (by rfl) ⟨923471, by rfl⟩ : syracuseStep 1231295 = 1846943) B1846943
theorem B1231515 : Blo 1230433 1231515 := bstep (se 1 (by rfl) ⟨923636, by rfl⟩ : syracuseStep 1231515 = 1847273) B1847273
theorem B1231687 : Blo 1230433 1231687 := bstep (se 1 (by rfl) ⟨923765, by rfl⟩ : syracuseStep 1231687 = 1847531) B1847531
theorem B4156271 : Blo 1230433 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B3116191 : Blo 1230433 3116191 := bstep (se 1 (by rfl) ⟨2337143, by rfl⟩ : syracuseStep 3116191 = 4674287) B4674287
theorem B4156811 : Blo 1230433 4156811 := bstep (se 1 (by rfl) ⟨3117608, by rfl⟩ : syracuseStep 4156811 = 6235217) B6235217
theorem B9350639 : Blo 1230433 9350639 := bstep (se 1 (by rfl) ⟨7012979, by rfl⟩ : syracuseStep 9350639 = 14025959) B14025959
theorem B14020127 : Blo 1230433 14020127 := bstep (se 1 (by rfl) ⟨10515095, by rfl⟩ : syracuseStep 14020127 = 21030191) B21030191
theorem B46182629 : Blo 1230433 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B2339111 : Blo 1230433 2339111 := bstep (se 1 (by rfl) ⟨1754333, by rfl⟩ : syracuseStep 2339111 = 3508667) B3508667
theorem B2077049 : Blo 1230433 2077049 := bstep (se 2 (by rfl) ⟨778893, by rfl⟩ : syracuseStep 2077049 = 1557787) B1557787
theorem B1315327 : Blo 1230433 1315327 := bstep (se 1 (by rfl) ⟨986495, by rfl⟩ : syracuseStep 1315327 = 1972991) B1972991
theorem B4158107 : Blo 1230433 4158107 := bstep (se 1 (by rfl) ⟨3118580, by rfl⟩ : syracuseStep 4158107 = 6237161) B6237161
theorem B85373783 : Blo 1230433 85373783 := bstep (se 1 (by rfl) ⟨64030337, by rfl⟩ : syracuseStep 85373783 = 128060675) B128060675
theorem B1848167 : Blo 1230433 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B3504235 : Blo 1230433 3504235 := bstep (se 1 (by rfl) ⟨2628176, by rfl⟩ : syracuseStep 3504235 = 5256353) B5256353
theorem B20240549 : Blo 1230433 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B56900171 : Blo 1230433 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B56867831 : Blo 1230433 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B19955645 : Blo 1230433 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B1384699 : Blo 1230433 1384699 := bstep (se 1 (by rfl) ⟨1038524, by rfl⟩ : syracuseStep 1384699 = 2077049) B2077049
theorem B1753769 : Blo 1230433 1753769 := bstep (se 2 (by rfl) ⟨657663, by rfl⟩ : syracuseStep 1753769 = 1315327) B1315327
theorem B13493699 : Blo 1230433 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B4154921 : Blo 1230433 4154921 := bstep (se 2 (by rfl) ⟨1558095, by rfl⟩ : syracuseStep 4154921 = 3116191) B3116191
theorem B2770847 : Blo 1230433 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B2771207 : Blo 1230433 2771207 := bstep (se 1 (by rfl) ⟨2078405, by rfl⟩ : syracuseStep 2771207 = 4156811) B4156811
theorem B4672313 : Blo 1230433 4672313 := bstep (se 2 (by rfl) ⟨1752117, by rfl⟩ : syracuseStep 4672313 = 3504235) B3504235
theorem B30788419 : Blo 1230433 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B11840327 : Blo 1230433 11840327 := bstep (se 1 (by rfl) ⟨8880245, by rfl⟩ : syracuseStep 11840327 = 17760491) B17760491
theorem B1559407 : Blo 1230433 1559407 := bstep (se 1 (by rfl) ⟨1169555, by rfl⟩ : syracuseStep 1559407 = 2339111) B2339111
theorem B2772071 : Blo 1230433 2772071 := bstep (se 1 (by rfl) ⟨2079053, by rfl⟩ : syracuseStep 2772071 = 4158107) B4158107
theorem B1232111 : Blo 1230433 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B1846523 : Blo 1230433 1846523 := bstep (se 1 (by rfl) ⟨1384892, by rfl⟩ : syracuseStep 1846523 = 2769785) B2769785
theorem B18968255 : Blo 1230433 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B1847351 : Blo 1230433 1847351 := bstep (se 1 (by rfl) ⟨1385513, by rfl⟩ : syracuseStep 1847351 = 2771027) B2771027
theorem B37933447 : Blo 1230433 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B56915855 : Blo 1230433 56915855 := bstep (se 1 (by rfl) ⟨42686891, by rfl⟩ : syracuseStep 56915855 = 85373783) B85373783
theorem B24009821 : Blo 1230433 24009821 := bstep (se 3 (by rfl) ⟨4501841, by rfl⟩ : syracuseStep 24009821 = 9003683) B9003683
theorem B37911887 : Blo 1230433 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B6233759 : Blo 1230433 6233759 := bstep (se 1 (by rfl) ⟨4675319, by rfl⟩ : syracuseStep 6233759 = 9350639) B9350639
theorem B9346751 : Blo 1230433 9346751 := bstep (se 1 (by rfl) ⟨7010063, by rfl⟩ : syracuseStep 9346751 = 14020127) B14020127
theorem B13303763 : Blo 1230433 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B50577929 : Blo 1230433 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B8995799 : Blo 1230433 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B2769947 : Blo 1230433 2769947 := bstep (se 1 (by rfl) ⟨2077460, by rfl⟩ : syracuseStep 2769947 = 4154921) B4154921
theorem B41051225 : Blo 1230433 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B3114875 : Blo 1230433 3114875 := bstep (se 1 (by rfl) ⟨2336156, by rfl⟩ : syracuseStep 3114875 = 4672313) B4672313
theorem B1231015 : Blo 1230433 1231015 := bstep (se 1 (by rfl) ⟨923261, by rfl⟩ : syracuseStep 1231015 = 1846523) B1846523
theorem B25274591 : Blo 1230433 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B4155839 : Blo 1230433 4155839 := bstep (se 1 (by rfl) ⟨3116879, by rfl⟩ : syracuseStep 4155839 = 6233759) B6233759
theorem B1231567 : Blo 1230433 1231567 := bstep (se 1 (by rfl) ⟨923675, by rfl⟩ : syracuseStep 1231567 = 1847351) B1847351
theorem B1846265 : Blo 1230433 1846265 := bstep (se 2 (by rfl) ⟨692349, by rfl⟩ : syracuseStep 1846265 = 1384699) B1384699
theorem B1847231 : Blo 1230433 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B1847471 : Blo 1230433 1847471 := bstep (se 1 (by rfl) ⟨1385603, by rfl⟩ : syracuseStep 1847471 = 2771207) B2771207
theorem B7893551 : Blo 1230433 7893551 := bstep (se 1 (by rfl) ⟨5920163, by rfl⟩ : syracuseStep 7893551 = 11840327) B11840327
theorem B1848047 : Blo 1230433 1848047 := bstep (se 1 (by rfl) ⟨1386035, by rfl⟩ : syracuseStep 1848047 = 2772071) B2772071
theorem B6231167 : Blo 1230433 6231167 := bstep (se 1 (by rfl) ⟨4673375, by rfl⟩ : syracuseStep 6231167 = 9346751) B9346751
theorem B12645503 : Blo 1230433 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B8869175 : Blo 1230433 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B2079209 : Blo 1230433 2079209 := bstep (se 2 (by rfl) ⟨779703, by rfl⟩ : syracuseStep 2079209 = 1559407) B1559407
theorem B37943903 : Blo 1230433 37943903 := bstep (se 1 (by rfl) ⟨28457927, by rfl⟩ : syracuseStep 37943903 = 56915855) B56915855
theorem B4676717 : Blo 1230433 4676717 := bstep (se 3 (by rfl) ⟨876884, by rfl⟩ : syracuseStep 4676717 = 1753769) B1753769
theorem B16006547 : Blo 1230433 16006547 := bstep (se 1 (by rfl) ⟨12004910, by rfl⟩ : syracuseStep 16006547 = 24009821) B24009821
theorem B33718619 : Blo 1230433 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B5997199 : Blo 1230433 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B4154111 : Blo 1230433 4154111 := bstep (se 1 (by rfl) ⟨3115583, by rfl⟩ : syracuseStep 4154111 = 6231167) B6231167
theorem B8430335 : Blo 1230433 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B2770559 : Blo 1230433 2770559 := bstep (se 1 (by rfl) ⟨2077919, by rfl⟩ : syracuseStep 2770559 = 4155839) B4155839
theorem B1386139 : Blo 1230433 1386139 := bstep (se 1 (by rfl) ⟨1039604, by rfl⟩ : syracuseStep 1386139 = 2079209) B2079209
theorem B1230843 : Blo 1230433 1230843 := bstep (se 1 (by rfl) ⟨923132, by rfl⟩ : syracuseStep 1230843 = 1846265) B1846265
theorem B1231487 : Blo 1230433 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B1231647 : Blo 1230433 1231647 := bstep (se 1 (by rfl) ⟨923735, by rfl⟩ : syracuseStep 1231647 = 1847471) B1847471
theorem B5262367 : Blo 1230433 5262367 := bstep (se 1 (by rfl) ⟨3946775, by rfl⟩ : syracuseStep 5262367 = 7893551) B7893551
theorem B1232031 : Blo 1230433 1232031 := bstep (se 1 (by rfl) ⟨924023, by rfl⟩ : syracuseStep 1232031 = 1848047) B1848047
theorem B1846631 : Blo 1230433 1846631 := bstep (se 1 (by rfl) ⟨1384973, by rfl⟩ : syracuseStep 1846631 = 2769947) B2769947
theorem B2076583 : Blo 1230433 2076583 := bstep (se 1 (by rfl) ⟨1557437, by rfl⟩ : syracuseStep 2076583 = 3114875) B3114875
theorem B101183741 : Blo 1230433 101183741 := bstep (se 3 (by rfl) ⟨18971951, by rfl⟩ : syracuseStep 101183741 = 37943903) B37943903
theorem B3117811 : Blo 1230433 3117811 := bstep (se 1 (by rfl) ⟨2338358, by rfl⟩ : syracuseStep 3117811 = 4676717) B4676717
theorem B10671031 : Blo 1230433 10671031 := bstep (se 1 (by rfl) ⟨8003273, by rfl⟩ : syracuseStep 10671031 = 16006547) B16006547
theorem B27367483 : Blo 1230433 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B5912783 : Blo 1230433 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B16849727 : Blo 1230433 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B22479079 : Blo 1230433 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B2769407 : Blo 1230433 2769407 := bstep (se 1 (by rfl) ⟨2077055, by rfl⟩ : syracuseStep 2769407 = 4154111) B4154111
theorem B5620223 : Blo 1230433 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B7996265 : Blo 1230433 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B3941855 : Blo 1230433 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B11233151 : Blo 1230433 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B1231087 : Blo 1230433 1231087 := bstep (se 1 (by rfl) ⟨923315, by rfl⟩ : syracuseStep 1231087 = 1846631) B1846631
theorem B56912165 : Blo 1230433 56912165 := bstep (se 4 (by rfl) ⟨5335515, by rfl⟩ : syracuseStep 56912165 = 10671031) B10671031
theorem B36489977 : Blo 1230433 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B67455827 : Blo 1230433 67455827 := bstep (se 1 (by rfl) ⟨50591870, by rfl⟩ : syracuseStep 67455827 = 101183741) B101183741
theorem B4157081 : Blo 1230433 4157081 := bstep (se 2 (by rfl) ⟨1558905, by rfl⟩ : syracuseStep 4157081 = 3117811) B3117811
theorem B1847039 : Blo 1230433 1847039 := bstep (se 1 (by rfl) ⟨1385279, by rfl⟩ : syracuseStep 1847039 = 2770559) B2770559
theorem B7016489 : Blo 1230433 7016489 := bstep (se 2 (by rfl) ⟨2631183, by rfl⟩ : syracuseStep 7016489 = 5262367) B5262367
theorem B1848185 : Blo 1230433 1848185 := bstep (se 2 (by rfl) ⟨693069, by rfl⟩ : syracuseStep 1848185 = 1386139) B1386139
theorem B2768777 : Blo 1230433 2768777 := bstep (se 2 (by rfl) ⟨1038291, by rfl⟩ : syracuseStep 2768777 = 2076583) B2076583
theorem B4677659 : Blo 1230433 4677659 := bstep (se 1 (by rfl) ⟨3508244, by rfl⟩ : syracuseStep 4677659 = 7016489) B7016489
theorem B7488767 : Blo 1230433 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B2771387 : Blo 1230433 2771387 := bstep (se 1 (by rfl) ⟨2078540, by rfl⟩ : syracuseStep 2771387 = 4157081) B4157081
theorem B1231359 : Blo 1230433 1231359 := bstep (se 1 (by rfl) ⟨923519, by rfl⟩ : syracuseStep 1231359 = 1847039) B1847039
theorem B1845851 : Blo 1230433 1845851 := bstep (se 1 (by rfl) ⟨1384388, by rfl⟩ : syracuseStep 1845851 = 2768777) B2768777
theorem B1846271 : Blo 1230433 1846271 := bstep (se 1 (by rfl) ⟨1384703, by rfl⟩ : syracuseStep 1846271 = 2769407) B2769407
theorem B1232123 : Blo 1230433 1232123 := bstep (se 1 (by rfl) ⟨924092, by rfl⟩ : syracuseStep 1232123 = 1848185) B1848185
theorem B14987261 : Blo 1230433 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B37941443 : Blo 1230433 37941443 := bstep (se 1 (by rfl) ⟨28456082, by rfl⟩ : syracuseStep 37941443 = 56912165) B56912165
theorem B24326651 : Blo 1230433 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B44970551 : Blo 1230433 44970551 := bstep (se 1 (by rfl) ⟨33727913, by rfl⟩ : syracuseStep 44970551 = 67455827) B67455827
theorem B29972105 : Blo 1230433 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B5330843 : Blo 1230433 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B2627903 : Blo 1230433 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B19981403 : Blo 1230433 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B1230567 : Blo 1230433 1230567 := bstep (se 1 (by rfl) ⟨922925, by rfl⟩ : syracuseStep 1230567 = 1845851) B1845851
theorem B1230847 : Blo 1230433 1230847 := bstep (se 1 (by rfl) ⟨923135, by rfl⟩ : syracuseStep 1230847 = 1846271) B1846271
theorem B7007741 : Blo 1230433 7007741 := bstep (se 3 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 7007741 = 2627903) B2627903
theorem B4992511 : Blo 1230433 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B1847591 : Blo 1230433 1847591 := bstep (se 1 (by rfl) ⟨1385693, by rfl⟩ : syracuseStep 1847591 = 2771387) B2771387
theorem B9991507 : Blo 1230433 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B3118439 : Blo 1230433 3118439 := bstep (se 1 (by rfl) ⟨2338829, by rfl⟩ : syracuseStep 3118439 = 4677659) B4677659
theorem B25294295 : Blo 1230433 25294295 := bstep (se 1 (by rfl) ⟨18970721, by rfl⟩ : syracuseStep 25294295 = 37941443) B37941443
theorem B16217767 : Blo 1230433 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B29980367 : Blo 1230433 29980367 := bstep (se 1 (by rfl) ⟨22485275, by rfl⟩ : syracuseStep 29980367 = 44970551) B44970551
theorem B3553895 : Blo 1230433 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B13320935 : Blo 1230433 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B2369263 : Blo 1230433 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B13322009 : Blo 1230433 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B4671827 : Blo 1230433 4671827 := bstep (se 1 (by rfl) ⟨3503870, by rfl⟩ : syracuseStep 4671827 = 7007741) B7007741
theorem B1231727 : Blo 1230433 1231727 := bstep (se 1 (by rfl) ⟨923795, by rfl⟩ : syracuseStep 1231727 = 1847591) B1847591
theorem B16862863 : Blo 1230433 16862863 := bstep (se 1 (by rfl) ⟨12647147, by rfl⟩ : syracuseStep 16862863 = 25294295) B25294295
theorem B6656681 : Blo 1230433 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B21623689 : Blo 1230433 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B2078959 : Blo 1230433 2078959 := bstep (se 1 (by rfl) ⟨1559219, by rfl⟩ : syracuseStep 2078959 = 3118439) B3118439
theorem B19986911 : Blo 1230433 19986911 := bstep (se 1 (by rfl) ⟨14990183, by rfl⟩ : syracuseStep 19986911 = 29980367) B29980367
theorem B8880623 : Blo 1230433 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B8881339 : Blo 1230433 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B3114551 : Blo 1230433 3114551 := bstep (se 1 (by rfl) ⟨2335913, by rfl⟩ : syracuseStep 3114551 = 4671827) B4671827
theorem B2771945 : Blo 1230433 2771945 := bstep (se 2 (by rfl) ⟨1039479, by rfl⟩ : syracuseStep 2771945 = 2078959) B2078959
theorem B13324607 : Blo 1230433 13324607 := bstep (se 1 (by rfl) ⟨9993455, by rfl⟩ : syracuseStep 13324607 = 19986911) B19986911
theorem B22483817 : Blo 1230433 22483817 := bstep (se 2 (by rfl) ⟨8431431, by rfl⟩ : syracuseStep 22483817 = 16862863) B16862863
theorem B3159017 : Blo 1230433 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B17751149 : Blo 1230433 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B115326341 : Blo 1230433 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B2106011 : Blo 1230433 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B76884227 : Blo 1230433 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B8883071 : Blo 1230433 8883071 := bstep (se 1 (by rfl) ⟨6662303, by rfl⟩ : syracuseStep 8883071 = 13324607) B13324607
theorem B2076367 : Blo 1230433 2076367 := bstep (se 1 (by rfl) ⟨1557275, by rfl⟩ : syracuseStep 2076367 = 3114551) B3114551
theorem B11841785 : Blo 1230433 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B1847963 : Blo 1230433 1847963 := bstep (se 1 (by rfl) ⟨1385972, by rfl⟩ : syracuseStep 1847963 = 2771945) B2771945
theorem B11834099 : Blo 1230433 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B5920415 : Blo 1230433 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B14989211 : Blo 1230433 14989211 := bstep (se 1 (by rfl) ⟨11241908, by rfl⟩ : syracuseStep 14989211 = 22483817) B22483817
theorem B7889399 : Blo 1230433 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B1231975 : Blo 1230433 1231975 := bstep (se 1 (by rfl) ⟨923981, by rfl⟩ : syracuseStep 1231975 = 1847963) B1847963
theorem B5616029 : Blo 1230433 5616029 := bstep (se 3 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 5616029 = 2106011) B2106011
theorem B7894523 : Blo 1230433 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B3946943 : Blo 1230433 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B9992807 : Blo 1230433 9992807 := bstep (se 1 (by rfl) ⟨7494605, by rfl⟩ : syracuseStep 9992807 = 14989211) B14989211
theorem B51256151 : Blo 1230433 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B5922047 : Blo 1230433 5922047 := bstep (se 1 (by rfl) ⟨4441535, by rfl⟩ : syracuseStep 5922047 = 8883071) B8883071
theorem B2768489 : Blo 1230433 2768489 := bstep (se 2 (by rfl) ⟨1038183, by rfl⟩ : syracuseStep 2768489 = 2076367) B2076367
theorem B3744019 : Blo 1230433 3744019 := bstep (se 1 (by rfl) ⟨2808014, by rfl⟩ : syracuseStep 3744019 = 5616029) B5616029
theorem B5259599 : Blo 1230433 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B2631295 : Blo 1230433 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B6661871 : Blo 1230433 6661871 := bstep (se 1 (by rfl) ⟨4996403, by rfl⟩ : syracuseStep 6661871 = 9992807) B9992807
theorem B34170767 : Blo 1230433 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B1845659 : Blo 1230433 1845659 := bstep (se 1 (by rfl) ⟨1384244, by rfl⟩ : syracuseStep 1845659 = 2768489) B2768489
theorem B21052061 : Blo 1230433 21052061 := bstep (se 3 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 21052061 = 7894523) B7894523
theorem B3948031 : Blo 1230433 3948031 := bstep (se 1 (by rfl) ⟨2961023, by rfl⟩ : syracuseStep 3948031 = 5922047) B5922047
theorem B3506399 : Blo 1230433 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B4441247 : Blo 1230433 4441247 := bstep (se 1 (by rfl) ⟨3330935, by rfl⟩ : syracuseStep 4441247 = 6661871) B6661871
theorem B1230439 : Blo 1230433 1230439 := bstep (se 1 (by rfl) ⟨922829, by rfl⟩ : syracuseStep 1230439 = 1845659) B1845659
theorem B14034707 : Blo 1230433 14034707 := bstep (se 1 (by rfl) ⟨10526030, by rfl⟩ : syracuseStep 14034707 = 21052061) B21052061
theorem B3508393 : Blo 1230433 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B4992025 : Blo 1230433 4992025 := bstep (se 2 (by rfl) ⟨1872009, by rfl⟩ : syracuseStep 4992025 = 3744019) B3744019
theorem B5264041 : Blo 1230433 5264041 := bstep (se 2 (by rfl) ⟨1974015, by rfl⟩ : syracuseStep 5264041 = 3948031) B3948031
theorem B22780511 : Blo 1230433 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B4677857 : Blo 1230433 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B9356471 : Blo 1230433 9356471 := bstep (se 1 (by rfl) ⟨7017353, by rfl⟩ : syracuseStep 9356471 = 14034707) B14034707
theorem B2337599 : Blo 1230433 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B2960831 : Blo 1230433 2960831 := bstep (se 1 (by rfl) ⟨2220623, by rfl⟩ : syracuseStep 2960831 = 4441247) B4441247
theorem B6656033 : Blo 1230433 6656033 := bstep (se 2 (by rfl) ⟨2496012, by rfl⟩ : syracuseStep 6656033 = 4992025) B4992025
theorem B7018721 : Blo 1230433 7018721 := bstep (se 2 (by rfl) ⟨2632020, by rfl⟩ : syracuseStep 7018721 = 5264041) B5264041
theorem B15187007 : Blo 1230433 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B4679147 : Blo 1230433 4679147 := bstep (se 1 (by rfl) ⟨3509360, by rfl⟩ : syracuseStep 4679147 = 7018721) B7018721
theorem B6237647 : Blo 1230433 6237647 := bstep (se 1 (by rfl) ⟨4678235, by rfl⟩ : syracuseStep 6237647 = 9356471) B9356471
theorem B4437355 : Blo 1230433 4437355 := bstep (se 1 (by rfl) ⟨3328016, by rfl⟩ : syracuseStep 4437355 = 6656033) B6656033
theorem B3118571 : Blo 1230433 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B7895549 : Blo 1230433 7895549 := bstep (se 3 (by rfl) ⟨1480415, by rfl⟩ : syracuseStep 7895549 = 2960831) B2960831
theorem B10124671 : Blo 1230433 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B6233597 : Blo 1230433 6233597 := bstep (se 3 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 6233597 = 2337599) B2337599
theorem B5916473 : Blo 1230433 5916473 := bstep (se 2 (by rfl) ⟨2218677, by rfl⟩ : syracuseStep 5916473 = 4437355) B4437355
theorem B4155731 : Blo 1230433 4155731 := bstep (se 1 (by rfl) ⟨3116798, by rfl⟩ : syracuseStep 4155731 = 6233597) B6233597
theorem B5263699 : Blo 1230433 5263699 := bstep (se 1 (by rfl) ⟨3947774, by rfl⟩ : syracuseStep 5263699 = 7895549) B7895549
theorem B4158431 : Blo 1230433 4158431 := bstep (se 1 (by rfl) ⟨3118823, by rfl⟩ : syracuseStep 4158431 = 6237647) B6237647
theorem B2079047 : Blo 1230433 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B3119431 : Blo 1230433 3119431 := bstep (se 1 (by rfl) ⟨2339573, by rfl⟩ : syracuseStep 3119431 = 4679147) B4679147
theorem B13499561 : Blo 1230433 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B1386031 : Blo 1230433 1386031 := bstep (se 1 (by rfl) ⟨1039523, by rfl⟩ : syracuseStep 1386031 = 2079047) B2079047
theorem B2770487 : Blo 1230433 2770487 := bstep (se 1 (by rfl) ⟨2077865, by rfl⟩ : syracuseStep 2770487 = 4155731) B4155731
theorem B2772287 : Blo 1230433 2772287 := bstep (se 1 (by rfl) ⟨2079215, by rfl⟩ : syracuseStep 2772287 = 4158431) B4158431
theorem B3944315 : Blo 1230433 3944315 := bstep (se 1 (by rfl) ⟨2958236, by rfl⟩ : syracuseStep 3944315 = 5916473) B5916473
theorem B8999707 : Blo 1230433 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B4159241 : Blo 1230433 4159241 := bstep (se 2 (by rfl) ⟨1559715, by rfl⟩ : syracuseStep 4159241 = 3119431) B3119431
theorem B7018265 : Blo 1230433 7018265 := bstep (se 2 (by rfl) ⟨2631849, by rfl⟩ : syracuseStep 7018265 = 5263699) B5263699
theorem B4678843 : Blo 1230433 4678843 := bstep (se 1 (by rfl) ⟨3509132, by rfl⟩ : syracuseStep 4678843 = 7018265) B7018265
theorem B1846991 : Blo 1230433 1846991 := bstep (se 1 (by rfl) ⟨1385243, by rfl⟩ : syracuseStep 1846991 = 2770487) B2770487
theorem B2772827 : Blo 1230433 2772827 := bstep (se 1 (by rfl) ⟨2079620, by rfl⟩ : syracuseStep 2772827 = 4159241) B4159241
theorem B1848041 : Blo 1230433 1848041 := bstep (se 2 (by rfl) ⟨693015, by rfl⟩ : syracuseStep 1848041 = 1386031) B1386031
theorem B1848191 : Blo 1230433 1848191 := bstep (se 1 (by rfl) ⟨1386143, by rfl⟩ : syracuseStep 1848191 = 2772287) B2772287
theorem B11999609 : Blo 1230433 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B10518173 : Blo 1230433 10518173 := bstep (se 3 (by rfl) ⟨1972157, by rfl⟩ : syracuseStep 10518173 = 3944315) B3944315
theorem B1231327 : Blo 1230433 1231327 := bstep (se 1 (by rfl) ⟨923495, by rfl⟩ : syracuseStep 1231327 = 1846991) B1846991
theorem B1232027 : Blo 1230433 1232027 := bstep (se 1 (by rfl) ⟨924020, by rfl⟩ : syracuseStep 1232027 = 1848041) B1848041
theorem B1232127 : Blo 1230433 1232127 := bstep (se 1 (by rfl) ⟨924095, by rfl⟩ : syracuseStep 1232127 = 1848191) B1848191
theorem B7999739 : Blo 1230433 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B6238457 : Blo 1230433 6238457 := bstep (se 2 (by rfl) ⟨2339421, by rfl⟩ : syracuseStep 6238457 = 4678843) B4678843
theorem B1848551 : Blo 1230433 1848551 := bstep (se 1 (by rfl) ⟨1386413, by rfl⟩ : syracuseStep 1848551 = 2772827) B2772827
theorem B7012115 : Blo 1230433 7012115 := bstep (se 1 (by rfl) ⟨5259086, by rfl⟩ : syracuseStep 7012115 = 10518173) B10518173
theorem B5333159 : Blo 1230433 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B1232367 : Blo 1230433 1232367 := bstep (se 1 (by rfl) ⟨924275, by rfl⟩ : syracuseStep 1232367 = 1848551) B1848551
theorem B4674743 : Blo 1230433 4674743 := bstep (se 1 (by rfl) ⟨3506057, by rfl⟩ : syracuseStep 4674743 = 7012115) B7012115
theorem B4158971 : Blo 1230433 4158971 := bstep (se 1 (by rfl) ⟨3119228, by rfl⟩ : syracuseStep 4158971 = 6238457) B6238457
theorem B14221757 : Blo 1230433 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B3116495 : Blo 1230433 3116495 := bstep (se 1 (by rfl) ⟨2337371, by rfl⟩ : syracuseStep 3116495 = 4674743) B4674743
theorem B2772647 : Blo 1230433 2772647 := bstep (se 1 (by rfl) ⟨2079485, by rfl⟩ : syracuseStep 2772647 = 4158971) B4158971
theorem B37924685 : Blo 1230433 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B2077663 : Blo 1230433 2077663 := bstep (se 1 (by rfl) ⟨1558247, by rfl⟩ : syracuseStep 2077663 = 3116495) B3116495
theorem B1848431 : Blo 1230433 1848431 := bstep (se 1 (by rfl) ⟨1386323, by rfl⟩ : syracuseStep 1848431 = 2772647) B2772647
theorem B2770217 : Blo 1230433 2770217 := bstep (se 2 (by rfl) ⟨1038831, by rfl⟩ : syracuseStep 2770217 = 2077663) B2077663
theorem B25283123 : Blo 1230433 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B1232287 : Blo 1230433 1232287 := bstep (se 1 (by rfl) ⟨924215, by rfl⟩ : syracuseStep 1232287 = 1848431) B1848431
theorem B1846811 : Blo 1230433 1846811 := bstep (se 1 (by rfl) ⟨1385108, by rfl⟩ : syracuseStep 1846811 = 2770217) B2770217
theorem B16855415 : Blo 1230433 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B1231207 : Blo 1230433 1231207 := bstep (se 1 (by rfl) ⟨923405, by rfl⟩ : syracuseStep 1231207 = 1846811) B1846811
theorem B11236943 : Blo 1230433 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B7491295 : Blo 1230433 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B39953573 : Blo 1230433 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B26635715 : Blo 1230433 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B17757143 : Blo 1230433 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B11838095 : Blo 1230433 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B7892063 : Blo 1230433 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B5261375 : Blo 1230433 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B14030333 : Blo 1230433 14030333 := bstep (se 3 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 14030333 = 5261375) B5261375
theorem B9353555 : Blo 1230433 9353555 := bstep (se 1 (by rfl) ⟨7015166, by rfl⟩ : syracuseStep 9353555 = 14030333) B14030333
theorem B6235703 : Blo 1230433 6235703 := bstep (se 1 (by rfl) ⟨4676777, by rfl⟩ : syracuseStep 6235703 = 9353555) B9353555
theorem B4157135 : Blo 1230433 4157135 := bstep (se 1 (by rfl) ⟨3117851, by rfl⟩ : syracuseStep 4157135 = 6235703) B6235703
theorem B2771423 : Blo 1230433 2771423 := bstep (se 1 (by rfl) ⟨2078567, by rfl⟩ : syracuseStep 2771423 = 4157135) B4157135
theorem B1847615 : Blo 1230433 1847615 := bstep (se 1 (by rfl) ⟨1385711, by rfl⟩ : syracuseStep 1847615 = 2771423) B2771423
theorem B1231743 : Blo 1230433 1231743 := bstep (se 1 (by rfl) ⟨923807, by rfl⟩ : syracuseStep 1231743 = 1847615) B1847615

theorem C0 (j : ℕ) (h1 : 307608 ≤ j) (h2 : j ≤ 308107) : Blo 1230433 (4 * j + 3) := by
  interval_cases j
  · exact B1230435
  · exact B1230439
  · exact B1230443
  · exact B1230447
  · exact B1230451
  · exact B1230455
  · exact B1230459
  · exact B1230463
  · exact B1230467
  · exact B1230471
  · exact B1230475
  · exact B1230479
  · exact B1230483
  · exact B1230487
  · exact B1230491
  · exact B1230495
  · exact B1230499
  · exact B1230503
  · exact B1230507
  · exact B1230511
  · exact B1230515
  · exact B1230519
  · exact B1230523
  · exact B1230527
  · exact B1230531
  · exact B1230535
  · exact B1230539
  · exact B1230543
  · exact B1230547
  · exact B1230551
  · exact B1230555
  · exact B1230559
  · exact B1230563
  · exact B1230567
  · exact B1230571
  · exact B1230575
  · exact B1230579
  · exact B1230583
  · exact B1230587
  · exact B1230591
  · exact B1230595
  · exact B1230599
  · exact B1230603
  · exact B1230607
  · exact B1230611
  · exact B1230615
  · exact B1230619
  · exact B1230623
  · exact B1230627
  · exact B1230631
  · exact B1230635
  · exact B1230639
  · exact B1230643
  · exact B1230647
  · exact B1230651
  · exact B1230655
  · exact B1230659
  · exact B1230663
  · exact B1230667
  · exact B1230671
  · exact B1230675
  · exact B1230679
  · exact B1230683
  · exact B1230687
  · exact B1230691
  · exact B1230695
  · exact B1230699
  · exact B1230703
  · exact B1230707
  · exact B1230711
  · exact B1230715
  · exact B1230719
  · exact B1230723
  · exact B1230727
  · exact B1230731
  · exact B1230735
  · exact B1230739
  · exact B1230743
  · exact B1230747
  · exact B1230751
  · exact B1230755
  · exact B1230759
  · exact B1230763
  · exact B1230767
  · exact B1230771
  · exact B1230775
  · exact B1230779
  · exact B1230783
  · exact B1230787
  · exact B1230791
  · exact B1230795
  · exact B1230799
  · exact B1230803
  · exact B1230807
  · exact B1230811
  · exact B1230815
  · exact B1230819
  · exact B1230823
  · exact B1230827
  · exact B1230831
  · exact B1230835
  · exact B1230839
  · exact B1230843
  · exact B1230847
  · exact B1230851
  · exact B1230855
  · exact B1230859
  · exact B1230863
  · exact B1230867
  · exact B1230871
  · exact B1230875
  · exact B1230879
  · exact B1230883
  · exact B1230887
  · exact B1230891
  · exact B1230895
  · exact B1230899
  · exact B1230903
  · exact B1230907
  · exact B1230911
  · exact B1230915
  · exact B1230919
  · exact B1230923
  · exact B1230927
  · exact B1230931
  · exact B1230935
  · exact B1230939
  · exact B1230943
  · exact B1230947
  · exact B1230951
  · exact B1230955
  · exact B1230959
  · exact B1230963
  · exact B1230967
  · exact B1230971
  · exact B1230975
  · exact B1230979
  · exact B1230983
  · exact B1230987
  · exact B1230991
  · exact B1230995
  · exact B1230999
  · exact B1231003
  · exact B1231007
  · exact B1231011
  · exact B1231015
  · exact B1231019
  · exact B1231023
  · exact B1231027
  · exact B1231031
  · exact B1231035
  · exact B1231039
  · exact B1231043
  · exact B1231047
  · exact B1231051
  · exact B1231055
  · exact B1231059
  · exact B1231063
  · exact B1231067
  · exact B1231071
  · exact B1231075
  · exact B1231079
  · exact B1231083
  · exact B1231087
  · exact B1231091
  · exact B1231095
  · exact B1231099
  · exact B1231103
  · exact B1231107
  · exact B1231111
  · exact B1231115
  · exact B1231119
  · exact B1231123
  · exact B1231127
  · exact B1231131
  · exact B1231135
  · exact B1231139
  · exact B1231143
  · exact B1231147
  · exact B1231151
  · exact B1231155
  · exact B1231159
  · exact B1231163
  · exact B1231167
  · exact B1231171
  · exact B1231175
  · exact B1231179
  · exact B1231183
  · exact B1231187
  · exact B1231191
  · exact B1231195
  · exact B1231199
  · exact B1231203
  · exact B1231207
  · exact B1231211
  · exact B1231215
  · exact B1231219
  · exact B1231223
  · exact B1231227
  · exact B1231231
  · exact B1231235
  · exact B1231239
  · exact B1231243
  · exact B1231247
  · exact B1231251
  · exact B1231255
  · exact B1231259
  · exact B1231263
  · exact B1231267
  · exact B1231271
  · exact B1231275
  · exact B1231279
  · exact B1231283
  · exact B1231287
  · exact B1231291
  · exact B1231295
  · exact B1231299
  · exact B1231303
  · exact B1231307
  · exact B1231311
  · exact B1231315
  · exact B1231319
  · exact B1231323
  · exact B1231327
  · exact B1231331
  · exact B1231335
  · exact B1231339
  · exact B1231343
  · exact B1231347
  · exact B1231351
  · exact B1231355
  · exact B1231359
  · exact B1231363
  · exact B1231367
  · exact B1231371
  · exact B1231375
  · exact B1231379
  · exact B1231383
  · exact B1231387
  · exact B1231391
  · exact B1231395
  · exact B1231399
  · exact B1231403
  · exact B1231407
  · exact B1231411
  · exact B1231415
  · exact B1231419
  · exact B1231423
  · exact B1231427
  · exact B1231431
  · exact B1231435
  · exact B1231439
  · exact B1231443
  · exact B1231447
  · exact B1231451
  · exact B1231455
  · exact B1231459
  · exact B1231463
  · exact B1231467
  · exact B1231471
  · exact B1231475
  · exact B1231479
  · exact B1231483
  · exact B1231487
  · exact B1231491
  · exact B1231495
  · exact B1231499
  · exact B1231503
  · exact B1231507
  · exact B1231511
  · exact B1231515
  · exact B1231519
  · exact B1231523
  · exact B1231527
  · exact B1231531
  · exact B1231535
  · exact B1231539
  · exact B1231543
  · exact B1231547
  · exact B1231551
  · exact B1231555
  · exact B1231559
  · exact B1231563
  · exact B1231567
  · exact B1231571
  · exact B1231575
  · exact B1231579
  · exact B1231583
  · exact B1231587
  · exact B1231591
  · exact B1231595
  · exact B1231599
  · exact B1231603
  · exact B1231607
  · exact B1231611
  · exact B1231615
  · exact B1231619
  · exact B1231623
  · exact B1231627
  · exact B1231631
  · exact B1231635
  · exact B1231639
  · exact B1231643
  · exact B1231647
  · exact B1231651
  · exact B1231655
  · exact B1231659
  · exact B1231663
  · exact B1231667
  · exact B1231671
  · exact B1231675
  · exact B1231679
  · exact B1231683
  · exact B1231687
  · exact B1231691
  · exact B1231695
  · exact B1231699
  · exact B1231703
  · exact B1231707
  · exact B1231711
  · exact B1231715
  · exact B1231719
  · exact B1231723
  · exact B1231727
  · exact B1231731
  · exact B1231735
  · exact B1231739
  · exact B1231743
  · exact B1231747
  · exact B1231751
  · exact B1231755
  · exact B1231759
  · exact B1231763
  · exact B1231767
  · exact B1231771
  · exact B1231775
  · exact B1231779
  · exact B1231783
  · exact B1231787
  · exact B1231791
  · exact B1231795
  · exact B1231799
  · exact B1231803
  · exact B1231807
  · exact B1231811
  · exact B1231815
  · exact B1231819
  · exact B1231823
  · exact B1231827
  · exact B1231831
  · exact B1231835
  · exact B1231839
  · exact B1231843
  · exact B1231847
  · exact B1231851
  · exact B1231855
  · exact B1231859
  · exact B1231863
  · exact B1231867
  · exact B1231871
  · exact B1231875
  · exact B1231879
  · exact B1231883
  · exact B1231887
  · exact B1231891
  · exact B1231895
  · exact B1231899
  · exact B1231903
  · exact B1231907
  · exact B1231911
  · exact B1231915
  · exact B1231919
  · exact B1231923
  · exact B1231927
  · exact B1231931
  · exact B1231935
  · exact B1231939
  · exact B1231943
  · exact B1231947
  · exact B1231951
  · exact B1231955
  · exact B1231959
  · exact B1231963
  · exact B1231967
  · exact B1231971
  · exact B1231975
  · exact B1231979
  · exact B1231983
  · exact B1231987
  · exact B1231991
  · exact B1231995
  · exact B1231999
  · exact B1232003
  · exact B1232007
  · exact B1232011
  · exact B1232015
  · exact B1232019
  · exact B1232023
  · exact B1232027
  · exact B1232031
  · exact B1232035
  · exact B1232039
  · exact B1232043
  · exact B1232047
  · exact B1232051
  · exact B1232055
  · exact B1232059
  · exact B1232063
  · exact B1232067
  · exact B1232071
  · exact B1232075
  · exact B1232079
  · exact B1232083
  · exact B1232087
  · exact B1232091
  · exact B1232095
  · exact B1232099
  · exact B1232103
  · exact B1232107
  · exact B1232111
  · exact B1232115
  · exact B1232119
  · exact B1232123
  · exact B1232127
  · exact B1232131
  · exact B1232135
  · exact B1232139
  · exact B1232143
  · exact B1232147
  · exact B1232151
  · exact B1232155
  · exact B1232159
  · exact B1232163
  · exact B1232167
  · exact B1232171
  · exact B1232175
  · exact B1232179
  · exact B1232183
  · exact B1232187
  · exact B1232191
  · exact B1232195
  · exact B1232199
  · exact B1232203
  · exact B1232207
  · exact B1232211
  · exact B1232215
  · exact B1232219
  · exact B1232223
  · exact B1232227
  · exact B1232231
  · exact B1232235
  · exact B1232239
  · exact B1232243
  · exact B1232247
  · exact B1232251
  · exact B1232255
  · exact B1232259
  · exact B1232263
  · exact B1232267
  · exact B1232271
  · exact B1232275
  · exact B1232279
  · exact B1232283
  · exact B1232287
  · exact B1232291
  · exact B1232295
  · exact B1232299
  · exact B1232303
  · exact B1232307
  · exact B1232311
  · exact B1232315
  · exact B1232319
  · exact B1232323
  · exact B1232327
  · exact B1232331
  · exact B1232335
  · exact B1232339
  · exact B1232343
  · exact B1232347
  · exact B1232351
  · exact B1232355
  · exact B1232359
  · exact B1232363
  · exact B1232367
  · exact B1232371
  · exact B1232375
  · exact B1232379
  · exact B1232383
  · exact B1232387
  · exact B1232391
  · exact B1232395
  · exact B1232399
  · exact B1232403
  · exact B1232407
  · exact B1232411
  · exact B1232415
  · exact B1232419
  · exact B1232423
  · exact B1232427
  · exact B1232431

theorem solution (m : ℕ) (hlo : 1230433 ≤ m) (hhi : m ≤ 1232433) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 307608 ≤ j := by omega
    have hj2 : j ≤ 308107 := by omega
    have hb : Blo 1230433 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
