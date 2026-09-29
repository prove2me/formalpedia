-- Prove2me | solution 1 for syracuse_descends_range_1124630_1128630
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:42.788933+00:00
-- url     : https://prove2.me/submissions/d07b2070-45f5-436a-aa70-51ccedcc922c

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


theorem B1900597 : Blo 1124630 1900597 := bbase (se 5 (by rfl) ⟨89090, by rfl⟩ : syracuseStep 1900597 = 178181) (by norm_num)
theorem B1802341 : Blo 1124630 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B3801221 : Blo 1124630 3801221 := bbase (se 4 (by rfl) ⟨356364, by rfl⟩ : syracuseStep 3801221 = 712729) (by norm_num)
theorem B1900685 : Blo 1124630 1900685 := bbase (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) (by norm_num)
theorem B1802405 : Blo 1124630 1802405 := bbase (se 4 (by rfl) ⟨168975, by rfl⟩ : syracuseStep 1802405 = 337951) (by norm_num)
theorem B10813621 : Blo 1124630 10813621 := bbase (se 5 (by rfl) ⟨506888, by rfl⟩ : syracuseStep 10813621 = 1013777) (by norm_num)
theorem B2850997 : Blo 1124630 2850997 := bbase (se 5 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 2850997 = 267281) (by norm_num)
theorem B1736885 : Blo 1124630 1736885 := bbase (se 5 (by rfl) ⟨81416, by rfl⟩ : syracuseStep 1736885 = 162833) (by norm_num)
theorem B1605845 : Blo 1124630 1605845 := bbase (se 7 (by rfl) ⟨18818, by rfl⟩ : syracuseStep 1605845 = 37637) (by norm_num)
theorem B4817141 : Blo 1124630 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B1900813 : Blo 1124630 1900813 := bbase (se 3 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 1900813 = 712805) (by norm_num)
theorem B2851109 : Blo 1124630 2851109 := bbase (se 4 (by rfl) ⟨267291, by rfl⟩ : syracuseStep 2851109 = 534583) (by norm_num)
theorem B1900901 : Blo 1124630 1900901 := bbase (se 4 (by rfl) ⟨178209, by rfl⟩ : syracuseStep 1900901 = 356419) (by norm_num)
theorem B2851301 : Blo 1124630 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1901029 : Blo 1124630 1901029 := bbase (se 4 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 1901029 = 356443) (by norm_num)
theorem B3801653 : Blo 1124630 3801653 := bbase (se 5 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 3801653 = 356405) (by norm_num)
theorem B1901117 : Blo 1124630 1901117 := bbase (se 3 (by rfl) ⟨356459, by rfl⟩ : syracuseStep 1901117 = 712919) (by norm_num)
theorem B1901245 : Blo 1124630 1901245 := bbase (se 3 (by rfl) ⟨356483, by rfl⟩ : syracuseStep 1901245 = 712967) (by norm_num)
theorem B6095573 : Blo 1124630 6095573 := bbase (se 7 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 6095573 = 142865) (by norm_num)
theorem B1606397 : Blo 1124630 1606397 := bbase (se 3 (by rfl) ⟨301199, by rfl⟩ : syracuseStep 1606397 = 602399) (by norm_num)
theorem B1901333 : Blo 1124630 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B2851645 : Blo 1124630 2851645 := bbase (se 3 (by rfl) ⟨534683, by rfl⟩ : syracuseStep 2851645 = 1069367) (by norm_num)
theorem B1901461 : Blo 1124630 1901461 := bbase (se 6 (by rfl) ⟨44565, by rfl⟩ : syracuseStep 1901461 = 89131) (by norm_num)
theorem B2851757 : Blo 1124630 2851757 := bbase (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) (by norm_num)
theorem B3802085 : Blo 1124630 3802085 := bbase (se 4 (by rfl) ⟨356445, by rfl⟩ : syracuseStep 3802085 = 712891) (by norm_num)
theorem B4817893 : Blo 1124630 4817893 := bbase (se 4 (by rfl) ⟨451677, by rfl⟩ : syracuseStep 4817893 = 903355) (by norm_num)
theorem B1901549 : Blo 1124630 1901549 := bbase (se 3 (by rfl) ⟨356540, by rfl⟩ : syracuseStep 1901549 = 713081) (by norm_num)
theorem B3212293 : Blo 1124630 3212293 := bbase (se 4 (by rfl) ⟨301152, by rfl⟩ : syracuseStep 3212293 = 602305) (by norm_num)
theorem B5407829 : Blo 1124630 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B2851949 : Blo 1124630 2851949 := bbase (se 3 (by rfl) ⟨534740, by rfl⟩ : syracuseStep 2851949 = 1069481) (by norm_num)
theorem B1901677 : Blo 1124630 1901677 := bbase (se 3 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 1901677 = 713129) (by norm_num)
theorem B3212453 : Blo 1124630 3212453 := bbase (se 4 (by rfl) ⟨301167, by rfl⟩ : syracuseStep 3212453 = 602335) (by norm_num)
theorem B1901765 : Blo 1124630 1901765 := bbase (se 4 (by rfl) ⟨178290, by rfl⟩ : syracuseStep 1901765 = 356581) (by norm_num)
theorem B5702885 : Blo 1124630 5702885 := bbase (se 4 (by rfl) ⟨534645, by rfl⟩ : syracuseStep 5702885 = 1069291) (by norm_num)
theorem B1901893 : Blo 1124630 1901893 := bbase (se 4 (by rfl) ⟨178302, by rfl⟩ : syracuseStep 1901893 = 356605) (by norm_num)
theorem B3802517 : Blo 1124630 3802517 := bbase (se 6 (by rfl) ⟨89121, by rfl⟩ : syracuseStep 3802517 = 178243) (by norm_num)
theorem B3212693 : Blo 1124630 3212693 := bbase (se 6 (by rfl) ⟨75297, by rfl⟩ : syracuseStep 3212693 = 150595) (by norm_num)
theorem B1901981 : Blo 1124630 1901981 := bbase (se 3 (by rfl) ⟨356621, by rfl⟩ : syracuseStep 1901981 = 713243) (by norm_num)
theorem B2852293 : Blo 1124630 2852293 := bbase (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) (by norm_num)
theorem B1803725 : Blo 1124630 1803725 := bbase (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) (by norm_num)
theorem B21661141 : Blo 1124630 21661141 := bbase (se 7 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 21661141 = 507683) (by norm_num)
theorem B2721293 : Blo 1124630 2721293 := bbase (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) (by norm_num)
theorem B1902109 : Blo 1124630 1902109 := bbase (se 3 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 1902109 = 713291) (by norm_num)
theorem B3048997 : Blo 1124630 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B2852405 : Blo 1124630 2852405 := bbase (se 5 (by rfl) ⟨133706, by rfl⟩ : syracuseStep 2852405 = 267413) (by norm_num)
theorem B3212885 : Blo 1124630 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B7308917 : Blo 1124630 7308917 := bbase (se 5 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 7308917 = 685211) (by norm_num)
theorem B1902197 : Blo 1124630 1902197 := bbase (se 5 (by rfl) ⟨89165, by rfl⟩ : syracuseStep 1902197 = 178331) (by norm_num)
theorem B1803917 : Blo 1124630 1803917 := bbase (se 3 (by rfl) ⟨338234, by rfl⟩ : syracuseStep 1803917 = 676469) (by norm_num)
theorem B4818629 : Blo 1124630 4818629 := bbase (se 4 (by rfl) ⟨451746, by rfl⟩ : syracuseStep 4818629 = 903493) (by norm_num)
theorem B2164429 : Blo 1124630 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B3606245 : Blo 1124630 3606245 := bbase (se 4 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 3606245 = 676171) (by norm_num)
theorem B2852597 : Blo 1124630 2852597 := bbase (se 5 (by rfl) ⟨133715, by rfl⟩ : syracuseStep 2852597 = 267431) (by norm_num)
theorem B1902325 : Blo 1124630 1902325 := bbase (se 5 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 1902325 = 178343) (by norm_num)
theorem B1804045 : Blo 1124630 1804045 := bbase (se 3 (by rfl) ⟨338258, by rfl⟩ : syracuseStep 1804045 = 676517) (by norm_num)
theorem B1443625 : Blo 1124630 1443625 := bbase (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) (by norm_num)
theorem B3802949 : Blo 1124630 3802949 := bbase (se 4 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 3802949 = 713053) (by norm_num)
theorem B1902413 : Blo 1124630 1902413 := bbase (se 3 (by rfl) ⟨356702, by rfl⟩ : syracuseStep 1902413 = 713405) (by norm_num)
theorem B3475349 : Blo 1124630 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1902541 : Blo 1124630 1902541 := bbase (se 3 (by rfl) ⟨356726, by rfl⟩ : syracuseStep 1902541 = 713453) (by norm_num)
theorem B1902629 : Blo 1124630 1902629 := bbase (se 4 (by rfl) ⟨178371, by rfl⟩ : syracuseStep 1902629 = 356743) (by norm_num)
theorem B1443901 : Blo 1124630 1443901 := bbase (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) (by norm_num)
theorem B2852941 : Blo 1124630 2852941 := bbase (se 3 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 2852941 = 1069853) (by norm_num)
theorem B1902757 : Blo 1124630 1902757 := bbase (se 4 (by rfl) ⟨178383, by rfl⟩ : syracuseStep 1902757 = 356767) (by norm_num)
theorem B2853053 : Blo 1124630 2853053 := bbase (se 3 (by rfl) ⟨534947, by rfl⟩ : syracuseStep 2853053 = 1069895) (by norm_num)
theorem B1444061 : Blo 1124630 1444061 := bbase (se 3 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 1444061 = 541523) (by norm_num)
theorem B3803381 : Blo 1124630 3803381 := bbase (se 5 (by rfl) ⟨178283, by rfl⟩ : syracuseStep 3803381 = 356567) (by norm_num)
theorem B1902845 : Blo 1124630 1902845 := bbase (se 3 (by rfl) ⟨356783, by rfl⟩ : syracuseStep 1902845 = 713567) (by norm_num)
theorem B2853245 : Blo 1124630 2853245 := bbase (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) (by norm_num)
theorem B1902973 : Blo 1124630 1902973 := bbase (se 3 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 1902973 = 713615) (by norm_num)
theorem B1804685 : Blo 1124630 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B1903061 : Blo 1124630 1903061 := bbase (se 7 (by rfl) ⟨22301, by rfl⟩ : syracuseStep 1903061 = 44603) (by norm_num)
theorem B3607013 : Blo 1124630 3607013 := bbase (se 4 (by rfl) ⟨338157, by rfl⟩ : syracuseStep 3607013 = 676315) (by norm_num)
theorem B5704181 : Blo 1124630 5704181 := bbase (se 5 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 5704181 = 534767) (by norm_num)
theorem B3213877 : Blo 1124630 3213877 := bbase (se 5 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 3213877 = 301301) (by norm_num)
theorem B1903189 : Blo 1124630 1903189 := bbase (se 8 (by rfl) ⟨11151, by rfl⟩ : syracuseStep 1903189 = 22303) (by norm_num)
theorem B3803813 : Blo 1124630 3803813 := bbase (se 4 (by rfl) ⟨356607, by rfl⟩ : syracuseStep 3803813 = 713215) (by norm_num)
theorem B1903277 : Blo 1124630 1903277 := bbase (se 3 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 1903277 = 713729) (by norm_num)
theorem B2853589 : Blo 1124630 2853589 := bbase (se 7 (by rfl) ⟨33440, by rfl⟩ : syracuseStep 2853589 = 66881) (by norm_num)
theorem B1903405 : Blo 1124630 1903405 := bbase (se 3 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 1903405 = 713777) (by norm_num)
theorem B2853701 : Blo 1124630 2853701 := bbase (se 4 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 2853701 = 535069) (by norm_num)
theorem B1805141 : Blo 1124630 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B1903493 : Blo 1124630 1903493 := bbase (se 4 (by rfl) ⟨178452, by rfl⟩ : syracuseStep 1903493 = 356905) (by norm_num)
theorem B3607525 : Blo 1124630 3607525 := bbase (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) (by norm_num)
theorem B2853893 : Blo 1124630 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B1903621 : Blo 1124630 1903621 := bbase (se 4 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 1903621 = 356929) (by norm_num)
theorem B1805365 : Blo 1124630 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B3804245 : Blo 1124630 3804245 := bbase (se 8 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 3804245 = 44581) (by norm_num)
theorem B1903709 : Blo 1124630 1903709 := bbase (se 3 (by rfl) ⟨356945, by rfl⟩ : syracuseStep 1903709 = 713891) (by norm_num)
theorem B3050597 : Blo 1124630 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B1444969 : Blo 1124630 1444969 := bbase (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) (by norm_num)
theorem B1805429 : Blo 1124630 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B4066453 : Blo 1124630 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B1903837 : Blo 1124630 1903837 := bbase (se 3 (by rfl) ⟨356969, by rfl⟩ : syracuseStep 1903837 = 713939) (by norm_num)
theorem B1805557 : Blo 1124630 1805557 := bbase (se 5 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 1805557 = 169271) (by norm_num)
theorem B1903925 : Blo 1124630 1903925 := bbase (se 5 (by rfl) ⟨89246, by rfl⟩ : syracuseStep 1903925 = 178493) (by norm_num)
theorem B2854237 : Blo 1124630 2854237 := bbase (se 3 (by rfl) ⟨535169, by rfl⟩ : syracuseStep 2854237 = 1070339) (by norm_num)
theorem B1904053 : Blo 1124630 1904053 := bbase (se 5 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 1904053 = 178505) (by norm_num)
theorem B2854349 : Blo 1124630 2854349 := bbase (se 3 (by rfl) ⟨535190, by rfl⟩ : syracuseStep 2854349 = 1070381) (by norm_num)
theorem B3804677 : Blo 1124630 3804677 := bbase (se 4 (by rfl) ⟨356688, by rfl⟩ : syracuseStep 3804677 = 713377) (by norm_num)
theorem B1904141 : Blo 1124630 1904141 := bbase (se 3 (by rfl) ⟨357026, by rfl⟩ : syracuseStep 1904141 = 714053) (by norm_num)
theorem B2854541 : Blo 1124630 2854541 := bbase (se 3 (by rfl) ⟨535226, by rfl⟩ : syracuseStep 2854541 = 1070453) (by norm_num)
theorem B1904269 : Blo 1124630 1904269 := bbase (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) (by norm_num)
theorem B1904357 : Blo 1124630 1904357 := bbase (se 4 (by rfl) ⟨178533, by rfl⟩ : syracuseStep 1904357 = 357067) (by norm_num)
theorem B5705477 : Blo 1124630 5705477 := bbase (se 4 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 5705477 = 1069777) (by norm_num)
theorem B5410597 : Blo 1124630 5410597 := bbase (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) (by norm_num)
theorem B1904485 : Blo 1124630 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B3805109 : Blo 1124630 3805109 := bbase (se 5 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 3805109 = 356729) (by norm_num)
theorem B2854885 : Blo 1124630 2854885 := bbase (se 4 (by rfl) ⟨267645, by rfl⟩ : syracuseStep 2854885 = 535291) (by norm_num)
theorem B2887741 : Blo 1124630 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B2854997 : Blo 1124630 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B9637973 : Blo 1124630 9637973 := bbase (se 8 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 9637973 = 112945) (by norm_num)
theorem B7213205 : Blo 1124630 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B6426773 : Blo 1124630 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B4329733 : Blo 1124630 4329733 := bbase (se 4 (by rfl) ⟨405912, by rfl⟩ : syracuseStep 4329733 = 811825) (by norm_num)
theorem B2855189 : Blo 1124630 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B3805541 : Blo 1124630 3805541 := bbase (se 4 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 3805541 = 713539) (by norm_num)
theorem B1806781 : Blo 1124630 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B7311829 : Blo 1124630 7311829 := bbase (se 7 (by rfl) ⟨85685, by rfl⟩ : syracuseStep 7311829 = 171371) (by norm_num)
theorem B2855533 : Blo 1124630 2855533 := bbase (se 3 (by rfl) ⟨535412, by rfl⟩ : syracuseStep 2855533 = 1070825) (by norm_num)
theorem B3609269 : Blo 1124630 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B2855645 : Blo 1124630 2855645 := bbase (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) (by norm_num)
theorem B3805973 : Blo 1124630 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B3609461 : Blo 1124630 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B2855837 : Blo 1124630 2855837 := bbase (se 3 (by rfl) ⟨535469, by rfl⟩ : syracuseStep 2855837 = 1070939) (by norm_num)
theorem B5706773 : Blo 1124630 5706773 := bbase (se 6 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 5706773 = 267505) (by norm_num)
theorem B1807453 : Blo 1124630 1807453 := bbase (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) (by norm_num)
theorem B2135173 : Blo 1124630 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B1283249 : Blo 1124630 1283249 := bbase (se 2 (by rfl) ⟨481218, by rfl⟩ : syracuseStep 1283249 = 962437) (by norm_num)
theorem B3806405 : Blo 1124630 3806405 := bbase (se 4 (by rfl) ⟨356850, by rfl⟩ : syracuseStep 3806405 = 713701) (by norm_num)
theorem B4560101 : Blo 1124630 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B2856181 : Blo 1124630 2856181 := bbase (se 5 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 2856181 = 267767) (by norm_num)
theorem B2135317 : Blo 1124630 2135317 := bbase (se 6 (by rfl) ⟨50046, by rfl⟩ : syracuseStep 2135317 = 100093) (by norm_num)
theorem B1217873 : Blo 1124630 1217873 := bbase (se 2 (by rfl) ⟨456702, by rfl⟩ : syracuseStep 1217873 = 913405) (by norm_num)
theorem B4560229 : Blo 1124630 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B2856293 : Blo 1124630 2856293 := bbase (se 4 (by rfl) ⟨267777, by rfl⟩ : syracuseStep 2856293 = 535555) (by norm_num)
theorem B8557973 : Blo 1124630 8557973 := bbase (se 6 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 8557973 = 401155) (by norm_num)
theorem B2135477 : Blo 1124630 2135477 := bbase (se 5 (by rfl) ⟨100100, by rfl⟩ : syracuseStep 2135477 = 200201) (by norm_num)
theorem B2856485 : Blo 1124630 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B2135621 : Blo 1124630 2135621 := bbase (se 4 (by rfl) ⟨200214, by rfl⟩ : syracuseStep 2135621 = 400429) (by norm_num)
theorem B3806837 : Blo 1124630 3806837 := bbase (se 5 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 3806837 = 356891) (by norm_num)
theorem B1447621 : Blo 1124630 1447621 := bbase (se 4 (by rfl) ⟨135714, by rfl⟩ : syracuseStep 1447621 = 271429) (by norm_num)
theorem B2135909 : Blo 1124630 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B2856829 : Blo 1124630 2856829 := bbase (se 3 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 2856829 = 1071311) (by norm_num)
theorem B1218461 : Blo 1124630 1218461 := bbase (se 3 (by rfl) ⟨228461, by rfl⟩ : syracuseStep 1218461 = 456923) (by norm_num)
theorem B2136061 : Blo 1124630 2136061 := bbase (se 3 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 2136061 = 801023) (by norm_num)
theorem B3807269 : Blo 1124630 3807269 := bbase (se 4 (by rfl) ⟨356931, by rfl⟩ : syracuseStep 3807269 = 713863) (by norm_num)
theorem B1284197 : Blo 1124630 1284197 := bbase (se 4 (by rfl) ⟨120393, by rfl⟩ : syracuseStep 1284197 = 240787) (by norm_num)
theorem B5708069 : Blo 1124630 5708069 := bbase (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) (by norm_num)
theorem B2136365 : Blo 1124630 2136365 := bbase (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) (by norm_num)
theorem B7706933 : Blo 1124630 7706933 := bbase (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) (by norm_num)
theorem B1284545 : Blo 1124630 1284545 := bbase (se 2 (by rfl) ⟨481704, by rfl⟩ : syracuseStep 1284545 = 963409) (by norm_num)
theorem B2169301 : Blo 1124630 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B3807701 : Blo 1124630 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B9607733 : Blo 1124630 9607733 := bbase (se 5 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 9607733 = 900725) (by norm_num)
theorem B1284709 : Blo 1124630 1284709 := bbase (se 4 (by rfl) ⟨120441, by rfl⟩ : syracuseStep 1284709 = 240883) (by norm_num)
theorem B4332197 : Blo 1124630 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B3808133 : Blo 1124630 3808133 := bbase (se 4 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 3808133 = 714025) (by norm_num)
theorem B8231861 : Blo 1124630 8231861 := bbase (se 5 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 8231861 = 771737) (by norm_num)
theorem B2137117 : Blo 1124630 2137117 := bbase (se 3 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 2137117 = 801419) (by norm_num)
theorem B2530421 : Blo 1124630 2530421 := bbase (se 5 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 2530421 = 237227) (by norm_num)
theorem B2137261 : Blo 1124630 2137261 := bbase (se 3 (by rfl) ⟨400736, by rfl⟩ : syracuseStep 2137261 = 801473) (by norm_num)
theorem B2530493 : Blo 1124630 2530493 := bbase (se 3 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 2530493 = 948935) (by norm_num)
theorem B2530565 : Blo 1124630 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B3808565 : Blo 1124630 3808565 := bbase (se 5 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 3808565 = 357053) (by norm_num)
theorem B2530637 : Blo 1124630 2530637 := bbase (se 3 (by rfl) ⟨474494, by rfl⟩ : syracuseStep 2530637 = 948989) (by norm_num)
theorem B2137421 : Blo 1124630 2137421 := bbase (se 3 (by rfl) ⟨400766, by rfl⟩ : syracuseStep 2137421 = 801533) (by norm_num)
theorem B2530709 : Blo 1124630 2530709 := bbase (se 6 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 2530709 = 118627) (by norm_num)
theorem B2530781 : Blo 1124630 2530781 := bbase (se 3 (by rfl) ⟨474521, by rfl⟩ : syracuseStep 2530781 = 949043) (by norm_num)
theorem B2137565 : Blo 1124630 2137565 := bbase (se 3 (by rfl) ⟨400793, by rfl⟩ : syracuseStep 2137565 = 801587) (by norm_num)
theorem B2530853 : Blo 1124630 2530853 := bbase (se 4 (by rfl) ⟨237267, by rfl⟩ : syracuseStep 2530853 = 474535) (by norm_num)
theorem B5709365 : Blo 1124630 5709365 := bbase (se 5 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 5709365 = 535253) (by norm_num)
theorem B2530925 : Blo 1124630 2530925 := bbase (se 3 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 2530925 = 949097) (by norm_num)
theorem B1351333 : Blo 1124630 1351333 := bbase (se 4 (by rfl) ⟨126687, by rfl⟩ : syracuseStep 1351333 = 253375) (by norm_num)
theorem B2530997 : Blo 1124630 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B3808997 : Blo 1124630 3808997 := bbase (se 4 (by rfl) ⟨357093, by rfl⟩ : syracuseStep 3808997 = 714187) (by norm_num)
theorem B2531069 : Blo 1124630 2531069 := bbase (se 3 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 2531069 = 949151) (by norm_num)
theorem B2137853 : Blo 1124630 2137853 := bbase (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) (by norm_num)
theorem B2531141 : Blo 1124630 2531141 := bbase (se 4 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 2531141 = 474589) (by norm_num)
theorem B1351549 : Blo 1124630 1351549 := bbase (se 3 (by rfl) ⟨253415, by rfl⟩ : syracuseStep 1351549 = 506831) (by norm_num)
theorem B2531213 : Blo 1124630 2531213 := bbase (se 3 (by rfl) ⟨474602, by rfl⟩ : syracuseStep 2531213 = 949205) (by norm_num)
theorem B2138005 : Blo 1124630 2138005 := bbase (se 6 (by rfl) ⟨50109, by rfl⟩ : syracuseStep 2138005 = 100219) (by norm_num)
theorem B13705109 : Blo 1124630 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B2531285 : Blo 1124630 2531285 := bbase (se 7 (by rfl) ⟨29663, by rfl⟩ : syracuseStep 2531285 = 59327) (by norm_num)
theorem B2531357 : Blo 1124630 2531357 := bbase (se 3 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 2531357 = 949259) (by norm_num)
theorem B2531429 : Blo 1124630 2531429 := bbase (se 4 (by rfl) ⟨237321, by rfl⟩ : syracuseStep 2531429 = 474643) (by norm_num)
theorem B4759717 : Blo 1124630 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B2531501 : Blo 1124630 2531501 := bbase (se 3 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 2531501 = 949313) (by norm_num)
theorem B2138309 : Blo 1124630 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B2531573 : Blo 1124630 2531573 := bbase (se 5 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 2531573 = 237335) (by norm_num)
theorem B5415173 : Blo 1124630 5415173 := bbase (se 4 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 5415173 = 1015345) (by norm_num)
theorem B2531645 : Blo 1124630 2531645 := bbase (se 3 (by rfl) ⟨474683, by rfl⟩ : syracuseStep 2531645 = 949367) (by norm_num)
theorem B33497429 : Blo 1124630 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B2531717 : Blo 1124630 2531717 := bbase (se 4 (by rfl) ⟨237348, by rfl⟩ : syracuseStep 2531717 = 474697) (by norm_num)
theorem B3613061 : Blo 1124630 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B1286533 : Blo 1124630 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B2531789 : Blo 1124630 2531789 := bbase (se 3 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 2531789 = 949421) (by norm_num)
theorem B2531861 : Blo 1124630 2531861 := bbase (se 6 (by rfl) ⟨59340, by rfl⟩ : syracuseStep 2531861 = 118681) (by norm_num)
theorem B2531933 : Blo 1124630 2531933 := bbase (se 3 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 2531933 = 949475) (by norm_num)
theorem B2532005 : Blo 1124630 2532005 := bbase (se 4 (by rfl) ⟨237375, by rfl⟩ : syracuseStep 2532005 = 474751) (by norm_num)
theorem B2532077 : Blo 1124630 2532077 := bbase (se 3 (by rfl) ⟨474764, by rfl⟩ : syracuseStep 2532077 = 949529) (by norm_num)
theorem B4563701 : Blo 1124630 4563701 := bbase (se 5 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 4563701 = 427847) (by norm_num)
theorem B1712909 : Blo 1124630 1712909 := bbase (se 3 (by rfl) ⟨321170, by rfl⟩ : syracuseStep 1712909 = 642341) (by norm_num)
theorem B2532149 : Blo 1124630 2532149 := bbase (se 5 (by rfl) ⟨118694, by rfl⟩ : syracuseStep 2532149 = 237389) (by norm_num)
theorem B5710661 : Blo 1124630 5710661 := bbase (se 4 (by rfl) ⟨535374, by rfl⟩ : syracuseStep 5710661 = 1070749) (by norm_num)
theorem B1155965 : Blo 1124630 1155965 := bbase (se 3 (by rfl) ⟨216743, by rfl⟩ : syracuseStep 1155965 = 433487) (by norm_num)
theorem B2532221 : Blo 1124630 2532221 := bbase (se 3 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 2532221 = 949583) (by norm_num)
theorem B2139061 : Blo 1124630 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B2532293 : Blo 1124630 2532293 := bbase (se 4 (by rfl) ⟨237402, by rfl⟩ : syracuseStep 2532293 = 474805) (by norm_num)
theorem B2532365 : Blo 1124630 2532365 := bbase (se 3 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 2532365 = 949637) (by norm_num)
theorem B2139205 : Blo 1124630 2139205 := bbase (se 4 (by rfl) ⟨200550, by rfl⟩ : syracuseStep 2139205 = 401101) (by norm_num)
theorem B2532437 : Blo 1124630 2532437 := bbase (se 8 (by rfl) ⟨14838, by rfl⟩ : syracuseStep 2532437 = 29677) (by norm_num)
theorem B17572949 : Blo 1124630 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B2532509 : Blo 1124630 2532509 := bbase (se 3 (by rfl) ⟨474845, by rfl⟩ : syracuseStep 2532509 = 949691) (by norm_num)
theorem B2532581 : Blo 1124630 2532581 := bbase (se 4 (by rfl) ⟨237429, by rfl⟩ : syracuseStep 2532581 = 474859) (by norm_num)
theorem B2139365 : Blo 1124630 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B2532653 : Blo 1124630 2532653 := bbase (se 3 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 2532653 = 949745) (by norm_num)
theorem B2532725 : Blo 1124630 2532725 := bbase (se 5 (by rfl) ⟨118721, by rfl⟩ : syracuseStep 2532725 = 237443) (by norm_num)
theorem B2139509 : Blo 1124630 2139509 := bbase (se 5 (by rfl) ⟨100289, by rfl⟩ : syracuseStep 2139509 = 200579) (by norm_num)
theorem B2532797 : Blo 1124630 2532797 := bbase (se 3 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 2532797 = 949799) (by norm_num)
theorem B2532869 : Blo 1124630 2532869 := bbase (se 4 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 2532869 = 474913) (by norm_num)
theorem B1353245 : Blo 1124630 1353245 := bbase (se 3 (by rfl) ⟨253733, by rfl⟩ : syracuseStep 1353245 = 507467) (by norm_num)
theorem B2532941 : Blo 1124630 2532941 := bbase (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) (by norm_num)
theorem B2533013 : Blo 1124630 2533013 := bbase (se 6 (by rfl) ⟨59367, by rfl⟩ : syracuseStep 2533013 = 118735) (by norm_num)
theorem B2139797 : Blo 1124630 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B2533085 : Blo 1124630 2533085 := bbase (se 3 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 2533085 = 949907) (by norm_num)
theorem B1353457 : Blo 1124630 1353457 := bbase (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) (by norm_num)
theorem B2533157 : Blo 1124630 2533157 := bbase (se 4 (by rfl) ⟨237483, by rfl⟩ : syracuseStep 2533157 = 474967) (by norm_num)
theorem B2139949 : Blo 1124630 2139949 := bbase (se 3 (by rfl) ⟨401240, by rfl⟩ : syracuseStep 2139949 = 802481) (by norm_num)
theorem B2533229 : Blo 1124630 2533229 := bbase (se 3 (by rfl) ⟨474980, by rfl⟩ : syracuseStep 2533229 = 949961) (by norm_num)
theorem B1353601 : Blo 1124630 1353601 := bbase (se 2 (by rfl) ⟨507600, by rfl⟩ : syracuseStep 1353601 = 1015201) (by norm_num)
theorem B2533301 : Blo 1124630 2533301 := bbase (se 5 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 2533301 = 237497) (by norm_num)
theorem B2533373 : Blo 1124630 2533373 := bbase (se 3 (by rfl) ⟨475007, by rfl⟩ : syracuseStep 2533373 = 950015) (by norm_num)
theorem B4270117 : Blo 1124630 4270117 := bbase (se 4 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 4270117 = 800647) (by norm_num)
theorem B2533445 : Blo 1124630 2533445 := bbase (se 4 (by rfl) ⟨237510, by rfl⟩ : syracuseStep 2533445 = 475021) (by norm_num)
theorem B5711957 : Blo 1124630 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B2140253 : Blo 1124630 2140253 := bbase (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) (by norm_num)
theorem B1157257 : Blo 1124630 1157257 := bbase (se 2 (by rfl) ⟨433971, by rfl⟩ : syracuseStep 1157257 = 867943) (by norm_num)
theorem B2533517 : Blo 1124630 2533517 := bbase (se 3 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 2533517 = 950069) (by norm_num)
theorem B5777573 : Blo 1124630 5777573 := bbase (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) (by norm_num)
theorem B2533589 : Blo 1124630 2533589 := bbase (se 7 (by rfl) ⟨29690, by rfl⟩ : syracuseStep 2533589 = 59381) (by norm_num)
theorem B2533661 : Blo 1124630 2533661 := bbase (se 3 (by rfl) ⟨475061, by rfl⟩ : syracuseStep 2533661 = 950123) (by norm_num)
theorem B4270421 : Blo 1124630 4270421 := bbase (se 10 (by rfl) ⟨6255, by rfl⟩ : syracuseStep 4270421 = 12511) (by norm_num)
theorem B2533733 : Blo 1124630 2533733 := bbase (se 4 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 2533733 = 475075) (by norm_num)
theorem B2533805 : Blo 1124630 2533805 := bbase (se 3 (by rfl) ⟨475088, by rfl⟩ : syracuseStep 2533805 = 950177) (by norm_num)
theorem B2533877 : Blo 1124630 2533877 := bbase (se 5 (by rfl) ⟨118775, by rfl⟩ : syracuseStep 2533877 = 237551) (by norm_num)
theorem B1714709 : Blo 1124630 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B2533949 : Blo 1124630 2533949 := bbase (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) (by norm_num)
theorem B3615317 : Blo 1124630 3615317 := bbase (se 8 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 3615317 = 42367) (by norm_num)
theorem B2894453 : Blo 1124630 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B2534021 : Blo 1124630 2534021 := bbase (se 4 (by rfl) ⟨237564, by rfl⟩ : syracuseStep 2534021 = 475129) (by norm_num)
theorem B2534093 : Blo 1124630 2534093 := bbase (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) (by norm_num)
theorem B3615445 : Blo 1124630 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B2534165 : Blo 1124630 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B2141005 : Blo 1124630 2141005 := bbase (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) (by norm_num)
theorem B2534237 : Blo 1124630 2534237 := bbase (se 3 (by rfl) ⟨475169, by rfl⟩ : syracuseStep 2534237 = 950339) (by norm_num)
theorem B2534309 : Blo 1124630 2534309 := bbase (se 4 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 2534309 = 475183) (by norm_num)
theorem B2141149 : Blo 1124630 2141149 := bbase (se 3 (by rfl) ⟨401465, by rfl⟩ : syracuseStep 2141149 = 802931) (by norm_num)
theorem B2534381 : Blo 1124630 2534381 := bbase (se 3 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 2534381 = 950393) (by norm_num)
theorem B1649701 : Blo 1124630 1649701 := bbase (se 4 (by rfl) ⟨154659, by rfl⟩ : syracuseStep 1649701 = 309319) (by norm_num)
theorem B2534453 : Blo 1124630 2534453 := bbase (se 5 (by rfl) ⟨118802, by rfl⟩ : syracuseStep 2534453 = 237605) (by norm_num)
theorem B2403445 : Blo 1124630 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B2534525 : Blo 1124630 2534525 := bbase (se 3 (by rfl) ⟨475223, by rfl⟩ : syracuseStep 2534525 = 950447) (by norm_num)
theorem B2141309 : Blo 1124630 2141309 := bbase (se 3 (by rfl) ⟨401495, by rfl⟩ : syracuseStep 2141309 = 802991) (by norm_num)
theorem B4566149 : Blo 1124630 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B1715341 : Blo 1124630 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B2534597 : Blo 1124630 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B2534669 : Blo 1124630 2534669 := bbase (se 3 (by rfl) ⟨475250, by rfl⟩ : syracuseStep 2534669 = 950501) (by norm_num)
theorem B2141453 : Blo 1124630 2141453 := bbase (se 3 (by rfl) ⟨401522, by rfl⟩ : syracuseStep 2141453 = 803045) (by norm_num)
theorem B2534741 : Blo 1124630 2534741 := bbase (se 11 (by rfl) ⟨1856, by rfl⟩ : syracuseStep 2534741 = 3713) (by norm_num)
theorem B5713253 : Blo 1124630 5713253 := bbase (se 4 (by rfl) ⟨535617, by rfl⟩ : syracuseStep 5713253 = 1071235) (by norm_num)
theorem B2534813 : Blo 1124630 2534813 := bbase (se 3 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 2534813 = 950555) (by norm_num)
theorem B1355177 : Blo 1124630 1355177 := bbase (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) (by norm_num)
theorem B2534885 : Blo 1124630 2534885 := bbase (se 4 (by rfl) ⟨237645, by rfl⟩ : syracuseStep 2534885 = 475291) (by norm_num)
theorem B2534957 : Blo 1124630 2534957 := bbase (se 3 (by rfl) ⟨475304, by rfl⟩ : syracuseStep 2534957 = 950609) (by norm_num)
theorem B2141741 : Blo 1124630 2141741 := bbase (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) (by norm_num)
theorem B2535029 : Blo 1124630 2535029 := bbase (se 5 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 2535029 = 237659) (by norm_num)
theorem B2535101 : Blo 1124630 2535101 := bbase (se 3 (by rfl) ⟨475331, by rfl⟩ : syracuseStep 2535101 = 950663) (by norm_num)
theorem B2141893 : Blo 1124630 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B1355513 : Blo 1124630 1355513 := bbase (se 2 (by rfl) ⟨508317, by rfl⟩ : syracuseStep 1355513 = 1016635) (by norm_num)
theorem B2535173 : Blo 1124630 2535173 := bbase (se 4 (by rfl) ⟨237672, by rfl⟩ : syracuseStep 2535173 = 475345) (by norm_num)
theorem B2535245 : Blo 1124630 2535245 := bbase (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) (by norm_num)
theorem B1355629 : Blo 1124630 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B2535317 : Blo 1124630 2535317 := bbase (se 6 (by rfl) ⟨59421, by rfl⟩ : syracuseStep 2535317 = 118843) (by norm_num)
theorem B1355701 : Blo 1124630 1355701 := bbase (se 5 (by rfl) ⟨63548, by rfl⟩ : syracuseStep 1355701 = 127097) (by norm_num)
theorem B1355725 : Blo 1124630 1355725 := bbase (se 3 (by rfl) ⟨254198, by rfl⟩ : syracuseStep 1355725 = 508397) (by norm_num)
theorem B2535389 : Blo 1124630 2535389 := bbase (se 3 (by rfl) ⟨475385, by rfl⟩ : syracuseStep 2535389 = 950771) (by norm_num)
theorem B2404333 : Blo 1124630 2404333 := bbase (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) (by norm_num)
theorem B2142197 : Blo 1124630 2142197 := bbase (se 5 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 2142197 = 200831) (by norm_num)
theorem B2535461 : Blo 1124630 2535461 := bbase (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) (by norm_num)
theorem B1355869 : Blo 1124630 1355869 := bbase (se 3 (by rfl) ⟨254225, by rfl⟩ : syracuseStep 1355869 = 508451) (by norm_num)
theorem B2535533 : Blo 1124630 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B2535605 : Blo 1124630 2535605 := bbase (se 5 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 2535605 = 237713) (by norm_num)
theorem B2535677 : Blo 1124630 2535677 := bbase (se 3 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 2535677 = 950879) (by norm_num)
theorem B2535749 : Blo 1124630 2535749 := bbase (se 4 (by rfl) ⟨237726, by rfl⟩ : syracuseStep 2535749 = 475453) (by norm_num)
theorem B2535821 : Blo 1124630 2535821 := bbase (se 3 (by rfl) ⟨475466, by rfl⟩ : syracuseStep 2535821 = 950933) (by norm_num)
theorem B4272533 : Blo 1124630 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B2535893 : Blo 1124630 2535893 := bbase (se 7 (by rfl) ⟨29717, by rfl⟩ : syracuseStep 2535893 = 59435) (by norm_num)
theorem B5419477 : Blo 1124630 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B2404829 : Blo 1124630 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B2535965 : Blo 1124630 2535965 := bbase (se 3 (by rfl) ⟨475493, by rfl⟩ : syracuseStep 2535965 = 950987) (by norm_num)
theorem B2536037 : Blo 1124630 2536037 := bbase (se 4 (by rfl) ⟨237753, by rfl⟩ : syracuseStep 2536037 = 475507) (by norm_num)
theorem B2536109 : Blo 1124630 2536109 := bbase (se 3 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 2536109 = 951041) (by norm_num)
theorem B4272821 : Blo 1124630 4272821 := bbase (se 5 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 4272821 = 400577) (by norm_num)
theorem B3420917 : Blo 1124630 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B2536181 : Blo 1124630 2536181 := bbase (se 5 (by rfl) ⟨118883, by rfl⟩ : syracuseStep 2536181 = 237767) (by norm_num)
theorem B2536253 : Blo 1124630 2536253 := bbase (se 3 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 2536253 = 951095) (by norm_num)
theorem B2536325 : Blo 1124630 2536325 := bbase (se 4 (by rfl) ⟨237780, by rfl⟩ : syracuseStep 2536325 = 475561) (by norm_num)
theorem B2536397 : Blo 1124630 2536397 := bbase (se 3 (by rfl) ⟨475574, by rfl⟩ : syracuseStep 2536397 = 951149) (by norm_num)
theorem B8565749 : Blo 1124630 8565749 := bbase (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) (by norm_num)
theorem B2536469 : Blo 1124630 2536469 := bbase (se 6 (by rfl) ⟨59448, by rfl⟩ : syracuseStep 2536469 = 118897) (by norm_num)
theorem B2536541 : Blo 1124630 2536541 := bbase (se 3 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 2536541 = 951203) (by norm_num)
theorem B2536613 : Blo 1124630 2536613 := bbase (se 4 (by rfl) ⟨237807, by rfl⟩ : syracuseStep 2536613 = 475615) (by norm_num)
theorem B2536685 : Blo 1124630 2536685 := bbase (se 3 (by rfl) ⟨475628, by rfl⟩ : syracuseStep 2536685 = 951257) (by norm_num)
theorem B4568309 : Blo 1124630 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B2929949 : Blo 1124630 2929949 := bbase (se 3 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 2929949 = 1098731) (by norm_num)
theorem B2536757 : Blo 1124630 2536757 := bbase (se 5 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 2536757 = 237821) (by norm_num)
theorem B2405693 : Blo 1124630 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B2536829 : Blo 1124630 2536829 := bbase (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) (by norm_num)
theorem B2536901 : Blo 1124630 2536901 := bbase (se 4 (by rfl) ⟨237834, by rfl⟩ : syracuseStep 2536901 = 475669) (by norm_num)
theorem B2405837 : Blo 1124630 2405837 := bbase (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) (by norm_num)
theorem B2536973 : Blo 1124630 2536973 := bbase (se 3 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 2536973 = 951365) (by norm_num)
theorem B2537045 : Blo 1124630 2537045 := bbase (se 8 (by rfl) ⟨14865, by rfl⟩ : syracuseStep 2537045 = 29731) (by norm_num)
theorem B2537117 : Blo 1124630 2537117 := bbase (se 3 (by rfl) ⟨475709, by rfl⟩ : syracuseStep 2537117 = 951419) (by norm_num)
theorem B2537189 : Blo 1124630 2537189 := bbase (se 4 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 2537189 = 475723) (by norm_num)
theorem B2537261 : Blo 1124630 2537261 := bbase (se 3 (by rfl) ⟨475736, by rfl⟩ : syracuseStep 2537261 = 951473) (by norm_num)
theorem B4274005 : Blo 1124630 4274005 := bbase (se 9 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 4274005 = 25043) (by norm_num)
theorem B2537333 : Blo 1124630 2537333 := bbase (se 5 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 2537333 = 237875) (by norm_num)
theorem B2537405 : Blo 1124630 2537405 := bbase (se 3 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 2537405 = 951527) (by norm_num)
theorem B2570221 : Blo 1124630 2570221 := bbase (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) (by norm_num)
theorem B2537477 : Blo 1124630 2537477 := bbase (se 4 (by rfl) ⟨237888, by rfl⟩ : syracuseStep 2537477 = 475777) (by norm_num)
theorem B1423433 : Blo 1124630 1423433 := bbase (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) (by norm_num)
theorem B2537549 : Blo 1124630 2537549 := bbase (se 3 (by rfl) ⟨475790, by rfl⟩ : syracuseStep 2537549 = 951581) (by norm_num)
theorem B1423489 : Blo 1124630 1423489 := bbase (se 2 (by rfl) ⟨533808, by rfl⟩ : syracuseStep 1423489 = 1067617) (by norm_num)
theorem B4274309 : Blo 1124630 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B2537621 : Blo 1124630 2537621 := bbase (se 6 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 2537621 = 118951) (by norm_num)
theorem B2406581 : Blo 1124630 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1521877 : Blo 1124630 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B2537693 : Blo 1124630 2537693 := bbase (se 3 (by rfl) ⟨475817, by rfl⟩ : syracuseStep 2537693 = 951635) (by norm_num)
theorem B1423585 : Blo 1124630 1423585 := bbase (se 2 (by rfl) ⟨533844, by rfl⟩ : syracuseStep 1423585 = 1067689) (by norm_num)
theorem B2537765 : Blo 1124630 2537765 := bbase (se 4 (by rfl) ⟨237915, by rfl⟩ : syracuseStep 2537765 = 475831) (by norm_num)
theorem B3422533 : Blo 1124630 3422533 := bbase (se 4 (by rfl) ⟨320862, by rfl⟩ : syracuseStep 3422533 = 641725) (by norm_num)
theorem B2537837 : Blo 1124630 2537837 := bbase (se 3 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 2537837 = 951689) (by norm_num)
theorem B1423757 : Blo 1124630 1423757 := bbase (se 3 (by rfl) ⟨266954, by rfl⟩ : syracuseStep 1423757 = 533909) (by norm_num)
theorem B2537909 : Blo 1124630 2537909 := bbase (se 5 (by rfl) ⟨118964, by rfl⟩ : syracuseStep 2537909 = 237929) (by norm_num)
theorem B1423813 : Blo 1124630 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B3422677 : Blo 1124630 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B2537981 : Blo 1124630 2537981 := bbase (se 3 (by rfl) ⟨475871, by rfl⟩ : syracuseStep 2537981 = 951743) (by norm_num)
theorem B4569605 : Blo 1124630 4569605 := bbase (se 4 (by rfl) ⟨428400, by rfl⟩ : syracuseStep 4569605 = 856801) (by norm_num)
theorem B1423909 : Blo 1124630 1423909 := bbase (se 4 (by rfl) ⟨133491, by rfl⟩ : syracuseStep 1423909 = 266983) (by norm_num)
theorem B2538053 : Blo 1124630 2538053 := bbase (se 4 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 2538053 = 475885) (by norm_num)
theorem B2538125 : Blo 1124630 2538125 := bbase (se 3 (by rfl) ⟨475898, by rfl⟩ : syracuseStep 2538125 = 951797) (by norm_num)
theorem B2603677 : Blo 1124630 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B4569797 : Blo 1124630 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B1424081 : Blo 1124630 1424081 := bbase (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) (by norm_num)
theorem B2538197 : Blo 1124630 2538197 := bbase (se 7 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 2538197 = 59489) (by norm_num)
theorem B1424137 : Blo 1124630 1424137 := bbase (se 2 (by rfl) ⟨534051, by rfl⟩ : syracuseStep 1424137 = 1068103) (by norm_num)
theorem B2538269 : Blo 1124630 2538269 := bbase (se 3 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 2538269 = 951851) (by norm_num)
theorem B2538341 : Blo 1124630 2538341 := bbase (se 4 (by rfl) ⟨237969, by rfl⟩ : syracuseStep 2538341 = 475939) (by norm_num)
theorem B1424233 : Blo 1124630 1424233 := bbase (se 2 (by rfl) ⟨534087, by rfl⟩ : syracuseStep 1424233 = 1068175) (by norm_num)
theorem B2407333 : Blo 1124630 2407333 := bbase (se 4 (by rfl) ⟨225687, by rfl⟩ : syracuseStep 2407333 = 451375) (by norm_num)
theorem B2538413 : Blo 1124630 2538413 := bbase (se 3 (by rfl) ⟨475952, by rfl⟩ : syracuseStep 2538413 = 951905) (by norm_num)
theorem B2702261 : Blo 1124630 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B2538485 : Blo 1124630 2538485 := bbase (se 5 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 2538485 = 237983) (by norm_num)
theorem B1424405 : Blo 1124630 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B2407477 : Blo 1124630 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B2538557 : Blo 1124630 2538557 := bbase (se 3 (by rfl) ⟨475979, by rfl⟩ : syracuseStep 2538557 = 951959) (by norm_num)
theorem B1424461 : Blo 1124630 1424461 := bbase (se 3 (by rfl) ⟨267086, by rfl⟩ : syracuseStep 1424461 = 534173) (by norm_num)
theorem B2538629 : Blo 1124630 2538629 := bbase (se 4 (by rfl) ⟨237996, by rfl⟩ : syracuseStep 2538629 = 475993) (by norm_num)
theorem B2604197 : Blo 1124630 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B1424557 : Blo 1124630 1424557 := bbase (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) (by norm_num)
theorem B2538701 : Blo 1124630 2538701 := bbase (se 3 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 2538701 = 952013) (by norm_num)
theorem B3849445 : Blo 1124630 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B2538773 : Blo 1124630 2538773 := bbase (se 6 (by rfl) ⟨59502, by rfl⟩ : syracuseStep 2538773 = 119005) (by norm_num)
theorem B1424729 : Blo 1124630 1424729 := bbase (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) (by norm_num)
theorem B2538845 : Blo 1124630 2538845 := bbase (se 3 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 2538845 = 952067) (by norm_num)
theorem B1424785 : Blo 1124630 1424785 := bbase (se 2 (by rfl) ⟨534294, by rfl⟩ : syracuseStep 1424785 = 1068589) (by norm_num)
theorem B2538917 : Blo 1124630 2538917 := bbase (se 4 (by rfl) ⟨238023, by rfl⟩ : syracuseStep 2538917 = 476047) (by norm_num)
theorem B2407853 : Blo 1124630 2407853 := bbase (se 3 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 2407853 = 902945) (by norm_num)
theorem B1686965 : Blo 1124630 1686965 := bbase (se 5 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 1686965 = 158153) (by norm_num)
theorem B1686989 : Blo 1124630 1686989 := bbase (se 3 (by rfl) ⟨316310, by rfl⟩ : syracuseStep 1686989 = 632621) (by norm_num)
theorem B1687013 : Blo 1124630 1687013 := bbase (se 4 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 1687013 = 316315) (by norm_num)
theorem B2538989 : Blo 1124630 2538989 := bbase (se 3 (by rfl) ⟨476060, by rfl⟩ : syracuseStep 2538989 = 952121) (by norm_num)
theorem B1424881 : Blo 1124630 1424881 := bbase (se 2 (by rfl) ⟨534330, by rfl⟩ : syracuseStep 1424881 = 1068661) (by norm_num)
theorem B1687037 : Blo 1124630 1687037 := bbase (se 3 (by rfl) ⟨316319, by rfl⟩ : syracuseStep 1687037 = 632639) (by norm_num)
theorem B1687061 : Blo 1124630 1687061 := bbase (se 6 (by rfl) ⟨39540, by rfl⟩ : syracuseStep 1687061 = 79081) (by norm_num)
theorem B1687085 : Blo 1124630 1687085 := bbase (se 3 (by rfl) ⟨316328, by rfl⟩ : syracuseStep 1687085 = 632657) (by norm_num)
theorem B2539061 : Blo 1124630 2539061 := bbase (se 5 (by rfl) ⟨119018, by rfl⟩ : syracuseStep 2539061 = 238037) (by norm_num)
theorem B1687109 : Blo 1124630 1687109 := bbase (se 4 (by rfl) ⟨158166, by rfl⟩ : syracuseStep 1687109 = 316333) (by norm_num)
theorem B1687133 : Blo 1124630 1687133 := bbase (se 3 (by rfl) ⟨316337, by rfl⟩ : syracuseStep 1687133 = 632675) (by norm_num)
theorem B1687157 : Blo 1124630 1687157 := bbase (se 5 (by rfl) ⟨79085, by rfl⟩ : syracuseStep 1687157 = 158171) (by norm_num)
theorem B2539133 : Blo 1124630 2539133 := bbase (se 3 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 2539133 = 952175) (by norm_num)
theorem B1687181 : Blo 1124630 1687181 := bbase (se 3 (by rfl) ⟨316346, by rfl⟩ : syracuseStep 1687181 = 632693) (by norm_num)
theorem B1425053 : Blo 1124630 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B1687205 : Blo 1124630 1687205 := bbase (se 4 (by rfl) ⟨158175, by rfl⟩ : syracuseStep 1687205 = 316351) (by norm_num)
theorem B1687229 : Blo 1124630 1687229 := bbase (se 3 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 1687229 = 632711) (by norm_num)
theorem B2539205 : Blo 1124630 2539205 := bbase (se 4 (by rfl) ⟨238050, by rfl⟩ : syracuseStep 2539205 = 476101) (by norm_num)
theorem B1687253 : Blo 1124630 1687253 := bbase (se 7 (by rfl) ⟨19772, by rfl⟩ : syracuseStep 1687253 = 39545) (by norm_num)
theorem B1425109 : Blo 1124630 1425109 := bbase (se 7 (by rfl) ⟨16700, by rfl⟩ : syracuseStep 1425109 = 33401) (by norm_num)
theorem B1687277 : Blo 1124630 1687277 := bbase (se 3 (by rfl) ⟨316364, by rfl⟩ : syracuseStep 1687277 = 632729) (by norm_num)
theorem B4112117 : Blo 1124630 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B1687301 : Blo 1124630 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B2539277 : Blo 1124630 2539277 := bbase (se 3 (by rfl) ⟨476114, by rfl⟩ : syracuseStep 2539277 = 952229) (by norm_num)
theorem B1687325 : Blo 1124630 1687325 := bbase (se 3 (by rfl) ⟨316373, by rfl⟩ : syracuseStep 1687325 = 632747) (by norm_num)
theorem B2408221 : Blo 1124630 2408221 := bbase (se 3 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 2408221 = 903083) (by norm_num)
theorem B1687349 : Blo 1124630 1687349 := bbase (se 5 (by rfl) ⟨79094, by rfl⟩ : syracuseStep 1687349 = 158189) (by norm_num)
theorem B1425205 : Blo 1124630 1425205 := bbase (se 5 (by rfl) ⟨66806, by rfl⟩ : syracuseStep 1425205 = 133613) (by norm_num)
theorem B1687373 : Blo 1124630 1687373 := bbase (se 3 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 1687373 = 632765) (by norm_num)
theorem B2539349 : Blo 1124630 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B1687397 : Blo 1124630 1687397 := bbase (se 4 (by rfl) ⟨158193, by rfl⟩ : syracuseStep 1687397 = 316387) (by norm_num)
theorem B1687421 : Blo 1124630 1687421 := bbase (se 3 (by rfl) ⟨316391, by rfl⟩ : syracuseStep 1687421 = 632783) (by norm_num)
theorem B2932613 : Blo 1124630 2932613 := bbase (se 4 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 2932613 = 549865) (by norm_num)
theorem B1687445 : Blo 1124630 1687445 := bbase (se 6 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 1687445 = 79099) (by norm_num)
theorem B1687469 : Blo 1124630 1687469 := bbase (se 3 (by rfl) ⟨316400, by rfl⟩ : syracuseStep 1687469 = 632801) (by norm_num)
theorem B1687493 : Blo 1124630 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B7225301 : Blo 1124630 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B1687517 : Blo 1124630 1687517 := bbase (se 3 (by rfl) ⟨316409, by rfl⟩ : syracuseStep 1687517 = 632819) (by norm_num)
theorem B1425377 : Blo 1124630 1425377 := bbase (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) (by norm_num)
theorem B1687541 : Blo 1124630 1687541 := bbase (se 5 (by rfl) ⟨79103, by rfl⟩ : syracuseStep 1687541 = 158207) (by norm_num)
theorem B1687565 : Blo 1124630 1687565 := bbase (se 3 (by rfl) ⟨316418, by rfl⟩ : syracuseStep 1687565 = 632837) (by norm_num)
theorem B1425433 : Blo 1124630 1425433 := bbase (se 2 (by rfl) ⟨534537, by rfl⟩ : syracuseStep 1425433 = 1069075) (by norm_num)
theorem B1523741 : Blo 1124630 1523741 := bbase (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) (by norm_num)
theorem B1687589 : Blo 1124630 1687589 := bbase (se 4 (by rfl) ⟨158211, by rfl⟩ : syracuseStep 1687589 = 316423) (by norm_num)
theorem B1687613 : Blo 1124630 1687613 := bbase (se 3 (by rfl) ⟨316427, by rfl⟩ : syracuseStep 1687613 = 632855) (by norm_num)
theorem B1687637 : Blo 1124630 1687637 := bbase (se 8 (by rfl) ⟨9888, by rfl⟩ : syracuseStep 1687637 = 19777) (by norm_num)
theorem B1687661 : Blo 1124630 1687661 := bbase (se 3 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 1687661 = 632873) (by norm_num)
theorem B1425529 : Blo 1124630 1425529 := bbase (se 2 (by rfl) ⟨534573, by rfl⟩ : syracuseStep 1425529 = 1069147) (by norm_num)
theorem B1687685 : Blo 1124630 1687685 := bbase (se 4 (by rfl) ⟨158220, by rfl⟩ : syracuseStep 1687685 = 316441) (by norm_num)
theorem B1687709 : Blo 1124630 1687709 := bbase (se 3 (by rfl) ⟨316445, by rfl⟩ : syracuseStep 1687709 = 632891) (by norm_num)
theorem B1687733 : Blo 1124630 1687733 := bbase (se 5 (by rfl) ⟨79112, by rfl⟩ : syracuseStep 1687733 = 158225) (by norm_num)
theorem B4276421 : Blo 1124630 4276421 := bbase (se 4 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 4276421 = 801829) (by norm_num)
theorem B1687757 : Blo 1124630 1687757 := bbase (se 3 (by rfl) ⟨316454, by rfl⟩ : syracuseStep 1687757 = 632909) (by norm_num)
theorem B9126101 : Blo 1124630 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B1687781 : Blo 1124630 1687781 := bbase (se 4 (by rfl) ⟨158229, by rfl⟩ : syracuseStep 1687781 = 316459) (by norm_num)
theorem B1687805 : Blo 1124630 1687805 := bbase (se 3 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 1687805 = 632927) (by norm_num)
theorem B1687829 : Blo 1124630 1687829 := bbase (se 6 (by rfl) ⟨39558, by rfl⟩ : syracuseStep 1687829 = 79117) (by norm_num)
theorem B1425701 : Blo 1124630 1425701 := bbase (se 4 (by rfl) ⟨133659, by rfl⟩ : syracuseStep 1425701 = 267319) (by norm_num)
theorem B1687853 : Blo 1124630 1687853 := bbase (se 3 (by rfl) ⟨316472, by rfl⟩ : syracuseStep 1687853 = 632945) (by norm_num)
theorem B1687877 : Blo 1124630 1687877 := bbase (se 4 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 1687877 = 316477) (by norm_num)
theorem B1687901 : Blo 1124630 1687901 := bbase (se 3 (by rfl) ⟨316481, by rfl⟩ : syracuseStep 1687901 = 632963) (by norm_num)
theorem B1425757 : Blo 1124630 1425757 := bbase (se 3 (by rfl) ⟨267329, by rfl⟩ : syracuseStep 1425757 = 534659) (by norm_num)
theorem B1687925 : Blo 1124630 1687925 := bbase (se 5 (by rfl) ⟨79121, by rfl⟩ : syracuseStep 1687925 = 158243) (by norm_num)
theorem B1687949 : Blo 1124630 1687949 := bbase (se 3 (by rfl) ⟨316490, by rfl⟩ : syracuseStep 1687949 = 632981) (by norm_num)
theorem B1687973 : Blo 1124630 1687973 := bbase (se 4 (by rfl) ⟨158247, by rfl⟩ : syracuseStep 1687973 = 316495) (by norm_num)
theorem B1687997 : Blo 1124630 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B1425853 : Blo 1124630 1425853 := bbase (se 3 (by rfl) ⟨267347, by rfl⟩ : syracuseStep 1425853 = 534695) (by norm_num)
theorem B5489093 : Blo 1124630 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B6406613 : Blo 1124630 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B1688021 : Blo 1124630 1688021 := bbase (se 7 (by rfl) ⟨19781, by rfl⟩ : syracuseStep 1688021 = 39563) (by norm_num)
theorem B4276709 : Blo 1124630 4276709 := bbase (se 4 (by rfl) ⟨400941, by rfl⟩ : syracuseStep 4276709 = 801883) (by norm_num)
theorem B1688045 : Blo 1124630 1688045 := bbase (se 3 (by rfl) ⟨316508, by rfl⟩ : syracuseStep 1688045 = 633017) (by norm_num)
theorem B1688069 : Blo 1124630 1688069 := bbase (se 4 (by rfl) ⟨158256, by rfl⟩ : syracuseStep 1688069 = 316513) (by norm_num)
theorem B1688093 : Blo 1124630 1688093 := bbase (se 3 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 1688093 = 633035) (by norm_num)
theorem B1688117 : Blo 1124630 1688117 := bbase (se 5 (by rfl) ⟨79130, by rfl⟩ : syracuseStep 1688117 = 158261) (by norm_num)
theorem B1688141 : Blo 1124630 1688141 := bbase (se 3 (by rfl) ⟨316526, by rfl⟩ : syracuseStep 1688141 = 633053) (by norm_num)
theorem B1688165 : Blo 1124630 1688165 := bbase (se 4 (by rfl) ⟨158265, by rfl⟩ : syracuseStep 1688165 = 316531) (by norm_num)
theorem B1426025 : Blo 1124630 1426025 := bbase (se 2 (by rfl) ⟨534759, by rfl⟩ : syracuseStep 1426025 = 1069519) (by norm_num)
theorem B1688189 : Blo 1124630 1688189 := bbase (se 3 (by rfl) ⟨316535, by rfl⟩ : syracuseStep 1688189 = 633071) (by norm_num)
theorem B1688213 : Blo 1124630 1688213 := bbase (se 6 (by rfl) ⟨39567, by rfl⟩ : syracuseStep 1688213 = 79135) (by norm_num)
theorem B1426081 : Blo 1124630 1426081 := bbase (se 2 (by rfl) ⟨534780, by rfl⟩ : syracuseStep 1426081 = 1069561) (by norm_num)
theorem B1688237 : Blo 1124630 1688237 := bbase (se 3 (by rfl) ⟨316544, by rfl⟩ : syracuseStep 1688237 = 633089) (by norm_num)
theorem B1688261 : Blo 1124630 1688261 := bbase (se 4 (by rfl) ⟨158274, by rfl⟩ : syracuseStep 1688261 = 316549) (by norm_num)
theorem B1688285 : Blo 1124630 1688285 := bbase (se 3 (by rfl) ⟨316553, by rfl⟩ : syracuseStep 1688285 = 633107) (by norm_num)
theorem B1688309 : Blo 1124630 1688309 := bbase (se 5 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 1688309 = 158279) (by norm_num)
theorem B1426177 : Blo 1124630 1426177 := bbase (se 2 (by rfl) ⟨534816, by rfl⟩ : syracuseStep 1426177 = 1069633) (by norm_num)
theorem B4571909 : Blo 1124630 4571909 := bbase (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) (by norm_num)
theorem B1688333 : Blo 1124630 1688333 := bbase (se 3 (by rfl) ⟨316562, by rfl⟩ : syracuseStep 1688333 = 633125) (by norm_num)
theorem B1688357 : Blo 1124630 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1688381 : Blo 1124630 1688381 := bbase (se 3 (by rfl) ⟨316571, by rfl⟩ : syracuseStep 1688381 = 633143) (by norm_num)
theorem B1688405 : Blo 1124630 1688405 := bbase (se 9 (by rfl) ⟨4946, by rfl⟩ : syracuseStep 1688405 = 9893) (by norm_num)
theorem B1688429 : Blo 1124630 1688429 := bbase (se 3 (by rfl) ⟨316580, by rfl⟩ : syracuseStep 1688429 = 633161) (by norm_num)
theorem B1688453 : Blo 1124630 1688453 := bbase (se 4 (by rfl) ⟨158292, by rfl⟩ : syracuseStep 1688453 = 316585) (by norm_num)
theorem B1688477 : Blo 1124630 1688477 := bbase (se 3 (by rfl) ⟨316589, by rfl⟩ : syracuseStep 1688477 = 633179) (by norm_num)
theorem B1426349 : Blo 1124630 1426349 := bbase (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) (by norm_num)
theorem B1688501 : Blo 1124630 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B1688525 : Blo 1124630 1688525 := bbase (se 3 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 1688525 = 633197) (by norm_num)
theorem B2704357 : Blo 1124630 2704357 := bbase (se 4 (by rfl) ⟨253533, by rfl⟩ : syracuseStep 2704357 = 507067) (by norm_num)
theorem B1688549 : Blo 1124630 1688549 := bbase (se 4 (by rfl) ⟨158301, by rfl⟩ : syracuseStep 1688549 = 316603) (by norm_num)
theorem B1426405 : Blo 1124630 1426405 := bbase (se 4 (by rfl) ⟨133725, by rfl⟩ : syracuseStep 1426405 = 267451) (by norm_num)
theorem B1688573 : Blo 1124630 1688573 := bbase (se 3 (by rfl) ⟨316607, by rfl⟩ : syracuseStep 1688573 = 633215) (by norm_num)
theorem B1688597 : Blo 1124630 1688597 := bbase (se 6 (by rfl) ⟨39576, by rfl⟩ : syracuseStep 1688597 = 79153) (by norm_num)
theorem B1688621 : Blo 1124630 1688621 := bbase (se 3 (by rfl) ⟨316616, by rfl⟩ : syracuseStep 1688621 = 633233) (by norm_num)
theorem B1688645 : Blo 1124630 1688645 := bbase (se 4 (by rfl) ⟨158310, by rfl⟩ : syracuseStep 1688645 = 316621) (by norm_num)
theorem B1426501 : Blo 1124630 1426501 := bbase (se 4 (by rfl) ⟨133734, by rfl⟩ : syracuseStep 1426501 = 267469) (by norm_num)
theorem B1688669 : Blo 1124630 1688669 := bbase (se 3 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 1688669 = 633251) (by norm_num)
theorem B1688693 : Blo 1124630 1688693 := bbase (se 5 (by rfl) ⟨79157, by rfl⟩ : syracuseStep 1688693 = 158315) (by norm_num)
theorem B1688717 : Blo 1124630 1688717 := bbase (se 3 (by rfl) ⟨316634, by rfl⟩ : syracuseStep 1688717 = 633269) (by norm_num)
theorem B1688741 : Blo 1124630 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B1688765 : Blo 1124630 1688765 := bbase (se 3 (by rfl) ⟨316643, by rfl⟩ : syracuseStep 1688765 = 633287) (by norm_num)
theorem B1688789 : Blo 1124630 1688789 := bbase (se 7 (by rfl) ⟨19790, by rfl⟩ : syracuseStep 1688789 = 39581) (by norm_num)
theorem B1688813 : Blo 1124630 1688813 := bbase (se 3 (by rfl) ⟨316652, by rfl⟩ : syracuseStep 1688813 = 633305) (by norm_num)
theorem B1426673 : Blo 1124630 1426673 := bbase (se 2 (by rfl) ⟨535002, by rfl⟩ : syracuseStep 1426673 = 1070005) (by norm_num)
theorem B2409725 : Blo 1124630 2409725 := bbase (se 3 (by rfl) ⟨451823, by rfl⟩ : syracuseStep 2409725 = 903647) (by norm_num)
theorem B1688837 : Blo 1124630 1688837 := bbase (se 4 (by rfl) ⟨158328, by rfl⟩ : syracuseStep 1688837 = 316657) (by norm_num)
theorem B1688861 : Blo 1124630 1688861 := bbase (se 3 (by rfl) ⟨316661, by rfl⟩ : syracuseStep 1688861 = 633323) (by norm_num)
theorem B1426729 : Blo 1124630 1426729 := bbase (se 2 (by rfl) ⟨535023, by rfl⟩ : syracuseStep 1426729 = 1070047) (by norm_num)
theorem B1688885 : Blo 1124630 1688885 := bbase (se 5 (by rfl) ⟨79166, by rfl⟩ : syracuseStep 1688885 = 158333) (by norm_num)
theorem B1688909 : Blo 1124630 1688909 := bbase (se 3 (by rfl) ⟨316670, by rfl⟩ : syracuseStep 1688909 = 633341) (by norm_num)
theorem B1688933 : Blo 1124630 1688933 := bbase (se 4 (by rfl) ⟨158337, by rfl⟩ : syracuseStep 1688933 = 316675) (by norm_num)
theorem B1688957 : Blo 1124630 1688957 := bbase (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) (by norm_num)
theorem B1426825 : Blo 1124630 1426825 := bbase (se 2 (by rfl) ⟨535059, by rfl⟩ : syracuseStep 1426825 = 1070119) (by norm_num)
theorem B2409869 : Blo 1124630 2409869 := bbase (se 3 (by rfl) ⟨451850, by rfl⟩ : syracuseStep 2409869 = 903701) (by norm_num)
theorem B1688981 : Blo 1124630 1688981 := bbase (se 6 (by rfl) ⟨39585, by rfl⟩ : syracuseStep 1688981 = 79171) (by norm_num)
theorem B1689005 : Blo 1124630 1689005 := bbase (se 3 (by rfl) ⟨316688, by rfl⟩ : syracuseStep 1689005 = 633377) (by norm_num)
theorem B1689029 : Blo 1124630 1689029 := bbase (se 4 (by rfl) ⟨158346, by rfl⟩ : syracuseStep 1689029 = 316693) (by norm_num)
theorem B1689053 : Blo 1124630 1689053 := bbase (se 3 (by rfl) ⟨316697, by rfl⟩ : syracuseStep 1689053 = 633395) (by norm_num)
theorem B1689077 : Blo 1124630 1689077 := bbase (se 5 (by rfl) ⟨79175, by rfl⟩ : syracuseStep 1689077 = 158351) (by norm_num)
theorem B1689101 : Blo 1124630 1689101 := bbase (se 3 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 1689101 = 633413) (by norm_num)
theorem B1525277 : Blo 1124630 1525277 := bbase (se 3 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 1525277 = 571979) (by norm_num)
theorem B1689125 : Blo 1124630 1689125 := bbase (se 4 (by rfl) ⟨158355, by rfl⟩ : syracuseStep 1689125 = 316711) (by norm_num)
theorem B1426997 : Blo 1124630 1426997 := bbase (se 5 (by rfl) ⟨66890, by rfl⟩ : syracuseStep 1426997 = 133781) (by norm_num)
theorem B1689149 : Blo 1124630 1689149 := bbase (se 3 (by rfl) ⟨316715, by rfl⟩ : syracuseStep 1689149 = 633431) (by norm_num)
theorem B1689173 : Blo 1124630 1689173 := bbase (se 8 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 1689173 = 19795) (by norm_num)
theorem B1689197 : Blo 1124630 1689197 := bbase (se 3 (by rfl) ⟨316724, by rfl⟩ : syracuseStep 1689197 = 633449) (by norm_num)
theorem B1427053 : Blo 1124630 1427053 := bbase (se 3 (by rfl) ⟨267572, by rfl⟩ : syracuseStep 1427053 = 535145) (by norm_num)
theorem B1689221 : Blo 1124630 1689221 := bbase (se 4 (by rfl) ⟨158364, by rfl⟩ : syracuseStep 1689221 = 316729) (by norm_num)
theorem B4277893 : Blo 1124630 4277893 := bbase (se 4 (by rfl) ⟨401052, by rfl⟩ : syracuseStep 4277893 = 802105) (by norm_num)
theorem B1689245 : Blo 1124630 1689245 := bbase (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) (by norm_num)
theorem B2705069 : Blo 1124630 2705069 := bbase (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) (by norm_num)
theorem B1689269 : Blo 1124630 1689269 := bbase (se 5 (by rfl) ⟨79184, by rfl⟩ : syracuseStep 1689269 = 158369) (by norm_num)
theorem B1689293 : Blo 1124630 1689293 := bbase (se 3 (by rfl) ⟨316742, by rfl⟩ : syracuseStep 1689293 = 633485) (by norm_num)
theorem B1427149 : Blo 1124630 1427149 := bbase (se 3 (by rfl) ⟨267590, by rfl⟩ : syracuseStep 1427149 = 535181) (by norm_num)
theorem B1689317 : Blo 1124630 1689317 := bbase (se 4 (by rfl) ⟨158373, by rfl⟩ : syracuseStep 1689317 = 316747) (by norm_num)
theorem B2410229 : Blo 1124630 2410229 := bbase (se 5 (by rfl) ⟨112979, by rfl⟩ : syracuseStep 2410229 = 225959) (by norm_num)
theorem B1689341 : Blo 1124630 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B1689365 : Blo 1124630 1689365 := bbase (se 6 (by rfl) ⟨39594, by rfl⟩ : syracuseStep 1689365 = 79189) (by norm_num)
theorem B15255317 : Blo 1124630 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B1689389 : Blo 1124630 1689389 := bbase (se 3 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 1689389 = 633521) (by norm_num)
theorem B1689413 : Blo 1124630 1689413 := bbase (se 4 (by rfl) ⟨158382, by rfl⟩ : syracuseStep 1689413 = 316765) (by norm_num)
theorem B8898389 : Blo 1124630 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B1689437 : Blo 1124630 1689437 := bbase (se 3 (by rfl) ⟨316769, by rfl⟩ : syracuseStep 1689437 = 633539) (by norm_num)
theorem B1689461 : Blo 1124630 1689461 := bbase (se 5 (by rfl) ⟨79193, by rfl⟩ : syracuseStep 1689461 = 158387) (by norm_num)
theorem B1427321 : Blo 1124630 1427321 := bbase (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) (by norm_num)
theorem B1689485 : Blo 1124630 1689485 := bbase (se 3 (by rfl) ⟨316778, by rfl⟩ : syracuseStep 1689485 = 633557) (by norm_num)
theorem B1689509 : Blo 1124630 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1427377 : Blo 1124630 1427377 := bbase (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) (by norm_num)
theorem B4278197 : Blo 1124630 4278197 := bbase (se 5 (by rfl) ⟨200540, by rfl⟩ : syracuseStep 4278197 = 401081) (by norm_num)
theorem B1689533 : Blo 1124630 1689533 := bbase (se 3 (by rfl) ⟨316787, by rfl⟩ : syracuseStep 1689533 = 633575) (by norm_num)
theorem B1689557 : Blo 1124630 1689557 := bbase (se 7 (by rfl) ⟨19799, by rfl⟩ : syracuseStep 1689557 = 39599) (by norm_num)
theorem B1689581 : Blo 1124630 1689581 := bbase (se 3 (by rfl) ⟨316796, by rfl⟩ : syracuseStep 1689581 = 633593) (by norm_num)
theorem B1689605 : Blo 1124630 1689605 := bbase (se 4 (by rfl) ⟨158400, by rfl⟩ : syracuseStep 1689605 = 316801) (by norm_num)
theorem B1427473 : Blo 1124630 1427473 := bbase (se 2 (by rfl) ⟨535302, by rfl⟩ : syracuseStep 1427473 = 1070605) (by norm_num)
theorem B1689629 : Blo 1124630 1689629 := bbase (se 3 (by rfl) ⟨316805, by rfl⟩ : syracuseStep 1689629 = 633611) (by norm_num)
theorem B2705453 : Blo 1124630 2705453 := bbase (se 3 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 2705453 = 1014545) (by norm_num)
theorem B1689653 : Blo 1124630 1689653 := bbase (se 5 (by rfl) ⟨79202, by rfl⟩ : syracuseStep 1689653 = 158405) (by norm_num)
theorem B1689677 : Blo 1124630 1689677 := bbase (se 3 (by rfl) ⟨316814, by rfl⟩ : syracuseStep 1689677 = 633629) (by norm_num)
theorem B1689701 : Blo 1124630 1689701 := bbase (se 4 (by rfl) ⟨158409, by rfl⟩ : syracuseStep 1689701 = 316819) (by norm_num)
theorem B1689725 : Blo 1124630 1689725 := bbase (se 3 (by rfl) ⟨316823, by rfl⟩ : syracuseStep 1689725 = 633647) (by norm_num)
theorem B1689749 : Blo 1124630 1689749 := bbase (se 6 (by rfl) ⟨39603, by rfl⟩ : syracuseStep 1689749 = 79207) (by norm_num)
theorem B1689773 : Blo 1124630 1689773 := bbase (se 3 (by rfl) ⟨316832, by rfl⟩ : syracuseStep 1689773 = 633665) (by norm_num)
theorem B1427645 : Blo 1124630 1427645 := bbase (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) (by norm_num)
theorem B1689797 : Blo 1124630 1689797 := bbase (se 4 (by rfl) ⟨158418, by rfl⟩ : syracuseStep 1689797 = 316837) (by norm_num)
theorem B1689821 : Blo 1124630 1689821 := bbase (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) (by norm_num)
theorem B1689845 : Blo 1124630 1689845 := bbase (se 5 (by rfl) ⟨79211, by rfl⟩ : syracuseStep 1689845 = 158423) (by norm_num)
theorem B1427701 : Blo 1124630 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B1689869 : Blo 1124630 1689869 := bbase (se 3 (by rfl) ⟨316850, by rfl⟩ : syracuseStep 1689869 = 633701) (by norm_num)
theorem B1689893 : Blo 1124630 1689893 := bbase (se 4 (by rfl) ⟨158427, by rfl⟩ : syracuseStep 1689893 = 316855) (by norm_num)
theorem B1689917 : Blo 1124630 1689917 := bbase (se 3 (by rfl) ⟨316859, by rfl⟩ : syracuseStep 1689917 = 633719) (by norm_num)
theorem B2705741 : Blo 1124630 2705741 := bbase (se 3 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 2705741 = 1014653) (by norm_num)
theorem B1689941 : Blo 1124630 1689941 := bbase (se 10 (by rfl) ⟨2475, by rfl⟩ : syracuseStep 1689941 = 4951) (by norm_num)
theorem B1427797 : Blo 1124630 1427797 := bbase (se 10 (by rfl) ⟨2091, by rfl⟩ : syracuseStep 1427797 = 4183) (by norm_num)
theorem B1689965 : Blo 1124630 1689965 := bbase (se 3 (by rfl) ⟨316868, by rfl⟩ : syracuseStep 1689965 = 633737) (by norm_num)
theorem B1689989 : Blo 1124630 1689989 := bbase (se 4 (by rfl) ⟨158436, by rfl⟩ : syracuseStep 1689989 = 316873) (by norm_num)
theorem B1690013 : Blo 1124630 1690013 := bbase (se 3 (by rfl) ⟨316877, by rfl⟩ : syracuseStep 1690013 = 633755) (by norm_num)
theorem B1690037 : Blo 1124630 1690037 := bbase (se 5 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 1690037 = 158441) (by norm_num)
theorem B1690061 : Blo 1124630 1690061 := bbase (se 3 (by rfl) ⟨316886, by rfl⟩ : syracuseStep 1690061 = 633773) (by norm_num)
theorem B1690085 : Blo 1124630 1690085 := bbase (se 4 (by rfl) ⟨158445, by rfl⟩ : syracuseStep 1690085 = 316891) (by norm_num)
theorem B1690109 : Blo 1124630 1690109 := bbase (se 3 (by rfl) ⟨316895, by rfl⟩ : syracuseStep 1690109 = 633791) (by norm_num)
theorem B1427969 : Blo 1124630 1427969 := bbase (se 2 (by rfl) ⟨535488, by rfl⟩ : syracuseStep 1427969 = 1070977) (by norm_num)
theorem B1690133 : Blo 1124630 1690133 := bbase (se 6 (by rfl) ⟨39612, by rfl⟩ : syracuseStep 1690133 = 79225) (by norm_num)
theorem B1690157 : Blo 1124630 1690157 := bbase (se 3 (by rfl) ⟨316904, by rfl⟩ : syracuseStep 1690157 = 633809) (by norm_num)
theorem B5130805 : Blo 1124630 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B1428025 : Blo 1124630 1428025 := bbase (se 2 (by rfl) ⟨535509, by rfl⟩ : syracuseStep 1428025 = 1071019) (by norm_num)
theorem B1690181 : Blo 1124630 1690181 := bbase (se 4 (by rfl) ⟨158454, by rfl⟩ : syracuseStep 1690181 = 316909) (by norm_num)
theorem B1690205 : Blo 1124630 1690205 := bbase (se 3 (by rfl) ⟨316913, by rfl⟩ : syracuseStep 1690205 = 633827) (by norm_num)
theorem B6408821 : Blo 1124630 6408821 := bbase (se 5 (by rfl) ⟨300413, by rfl⟩ : syracuseStep 6408821 = 600827) (by norm_num)
theorem B1690229 : Blo 1124630 1690229 := bbase (se 5 (by rfl) ⟨79229, by rfl⟩ : syracuseStep 1690229 = 158459) (by norm_num)
theorem B4016773 : Blo 1124630 4016773 := bbase (se 4 (by rfl) ⟨376572, by rfl⟩ : syracuseStep 4016773 = 753145) (by norm_num)
theorem B1690253 : Blo 1124630 1690253 := bbase (se 3 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 1690253 = 633845) (by norm_num)
theorem B1428121 : Blo 1124630 1428121 := bbase (se 2 (by rfl) ⟨535545, by rfl⟩ : syracuseStep 1428121 = 1071091) (by norm_num)
theorem B1690277 : Blo 1124630 1690277 := bbase (se 4 (by rfl) ⟨158463, by rfl⟩ : syracuseStep 1690277 = 316927) (by norm_num)
theorem B1690301 : Blo 1124630 1690301 := bbase (se 3 (by rfl) ⟨316931, by rfl⟩ : syracuseStep 1690301 = 633863) (by norm_num)
theorem B5130949 : Blo 1124630 5130949 := bbase (se 4 (by rfl) ⟨481026, by rfl⟩ : syracuseStep 5130949 = 962053) (by norm_num)
theorem B1690325 : Blo 1124630 1690325 := bbase (se 7 (by rfl) ⟨19808, by rfl⟩ : syracuseStep 1690325 = 39617) (by norm_num)
theorem B13191893 : Blo 1124630 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B1690349 : Blo 1124630 1690349 := bbase (se 3 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 1690349 = 633881) (by norm_num)
theorem B1690373 : Blo 1124630 1690373 := bbase (se 4 (by rfl) ⟨158472, by rfl⟩ : syracuseStep 1690373 = 316945) (by norm_num)
theorem B1690397 : Blo 1124630 1690397 := bbase (se 3 (by rfl) ⟨316949, by rfl⟩ : syracuseStep 1690397 = 633899) (by norm_num)
theorem B1690421 : Blo 1124630 1690421 := bbase (se 5 (by rfl) ⟨79238, by rfl⟩ : syracuseStep 1690421 = 158477) (by norm_num)
theorem B1428293 : Blo 1124630 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1690445 : Blo 1124630 1690445 := bbase (se 3 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 1690445 = 633917) (by norm_num)
theorem B1690469 : Blo 1124630 1690469 := bbase (se 4 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 1690469 = 316963) (by norm_num)
theorem B7228277 : Blo 1124630 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B1690493 : Blo 1124630 1690493 := bbase (se 3 (by rfl) ⟨316967, by rfl⟩ : syracuseStep 1690493 = 633935) (by norm_num)
theorem B1428349 : Blo 1124630 1428349 := bbase (se 3 (by rfl) ⟨267815, by rfl⟩ : syracuseStep 1428349 = 535631) (by norm_num)
theorem B2083733 : Blo 1124630 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B1690517 : Blo 1124630 1690517 := bbase (se 6 (by rfl) ⟨39621, by rfl⟩ : syracuseStep 1690517 = 79243) (by norm_num)
theorem B1690541 : Blo 1124630 1690541 := bbase (se 3 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 1690541 = 633953) (by norm_num)
theorem B1690565 : Blo 1124630 1690565 := bbase (se 4 (by rfl) ⟨158490, by rfl⟩ : syracuseStep 1690565 = 316981) (by norm_num)
theorem B1690589 : Blo 1124630 1690589 := bbase (se 3 (by rfl) ⟨316985, by rfl⟩ : syracuseStep 1690589 = 633971) (by norm_num)
theorem B1690613 : Blo 1124630 1690613 := bbase (se 5 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 1690613 = 158495) (by norm_num)
theorem B1690637 : Blo 1124630 1690637 := bbase (se 3 (by rfl) ⟨316994, by rfl⟩ : syracuseStep 1690637 = 633989) (by norm_num)
theorem B1690661 : Blo 1124630 1690661 := bbase (se 4 (by rfl) ⟨158499, by rfl⟩ : syracuseStep 1690661 = 316999) (by norm_num)
theorem B1690685 : Blo 1124630 1690685 := bbase (se 3 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 1690685 = 634007) (by norm_num)
theorem B1690709 : Blo 1124630 1690709 := bbase (se 8 (by rfl) ⟨9906, by rfl⟩ : syracuseStep 1690709 = 19813) (by norm_num)
theorem B1690733 : Blo 1124630 1690733 := bbase (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) (by norm_num)
theorem B3427445 : Blo 1124630 3427445 := bbase (se 5 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 3427445 = 321323) (by norm_num)
theorem B8244341 : Blo 1124630 8244341 := bbase (se 5 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 8244341 = 772907) (by norm_num)
theorem B1690757 : Blo 1124630 1690757 := bbase (se 4 (by rfl) ⟨158508, by rfl⟩ : syracuseStep 1690757 = 317017) (by norm_num)
theorem B1690781 : Blo 1124630 1690781 := bbase (se 3 (by rfl) ⟨317021, by rfl⟩ : syracuseStep 1690781 = 634043) (by norm_num)
theorem B1690805 : Blo 1124630 1690805 := bbase (se 5 (by rfl) ⟨79256, by rfl⟩ : syracuseStep 1690805 = 158513) (by norm_num)
theorem B1690829 : Blo 1124630 1690829 := bbase (se 3 (by rfl) ⟨317030, by rfl⟩ : syracuseStep 1690829 = 634061) (by norm_num)
theorem B1690853 : Blo 1124630 1690853 := bbase (se 4 (by rfl) ⟨158517, by rfl⟩ : syracuseStep 1690853 = 317035) (by norm_num)
theorem B1690877 : Blo 1124630 1690877 := bbase (se 3 (by rfl) ⟨317039, by rfl⟩ : syracuseStep 1690877 = 634079) (by norm_num)
theorem B1690901 : Blo 1124630 1690901 := bbase (se 6 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 1690901 = 79261) (by norm_num)
theorem B1690925 : Blo 1124630 1690925 := bbase (se 3 (by rfl) ⟨317048, by rfl⟩ : syracuseStep 1690925 = 634097) (by norm_num)
theorem B1690949 : Blo 1124630 1690949 := bbase (se 4 (by rfl) ⟨158526, by rfl⟩ : syracuseStep 1690949 = 317053) (by norm_num)
theorem B1690973 : Blo 1124630 1690973 := bbase (se 3 (by rfl) ⟨317057, by rfl⟩ : syracuseStep 1690973 = 634115) (by norm_num)
theorem B1690997 : Blo 1124630 1690997 := bbase (se 5 (by rfl) ⟨79265, by rfl⟩ : syracuseStep 1690997 = 158531) (by norm_num)
theorem B2280845 : Blo 1124630 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B1691021 : Blo 1124630 1691021 := bbase (se 3 (by rfl) ⟨317066, by rfl⟩ : syracuseStep 1691021 = 634133) (by norm_num)
theorem B1691045 : Blo 1124630 1691045 := bbase (se 4 (by rfl) ⟨158535, by rfl⟩ : syracuseStep 1691045 = 317071) (by norm_num)
theorem B2280893 : Blo 1124630 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B1691069 : Blo 1124630 1691069 := bbase (se 3 (by rfl) ⟨317075, by rfl⟩ : syracuseStep 1691069 = 634151) (by norm_num)
theorem B1691093 : Blo 1124630 1691093 := bbase (se 7 (by rfl) ⟨19817, by rfl⟩ : syracuseStep 1691093 = 39635) (by norm_num)
theorem B1691117 : Blo 1124630 1691117 := bbase (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) (by norm_num)
theorem B6082037 : Blo 1124630 6082037 := bbase (se 5 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 6082037 = 570191) (by norm_num)
theorem B1691141 : Blo 1124630 1691141 := bbase (se 4 (by rfl) ⟨158544, by rfl⟩ : syracuseStep 1691141 = 317089) (by norm_num)
theorem B3427861 : Blo 1124630 3427861 := bbase (se 6 (by rfl) ⟨80340, by rfl⟩ : syracuseStep 3427861 = 160681) (by norm_num)
theorem B1691165 : Blo 1124630 1691165 := bbase (se 3 (by rfl) ⟨317093, by rfl⟩ : syracuseStep 1691165 = 634187) (by norm_num)
theorem B1691189 : Blo 1124630 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1691213 : Blo 1124630 1691213 := bbase (se 3 (by rfl) ⟨317102, by rfl⟩ : syracuseStep 1691213 = 634205) (by norm_num)
theorem B1265233 : Blo 1124630 1265233 := bbase (se 2 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 1265233 = 948925) (by norm_num)
theorem B1691237 : Blo 1124630 1691237 := bbase (se 4 (by rfl) ⟨158553, by rfl⟩ : syracuseStep 1691237 = 317107) (by norm_num)
theorem B1265269 : Blo 1124630 1265269 := bbase (se 5 (by rfl) ⟨59309, by rfl⟩ : syracuseStep 1265269 = 118619) (by norm_num)
theorem B1691261 : Blo 1124630 1691261 := bbase (se 3 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 1691261 = 634223) (by norm_num)
theorem B1691285 : Blo 1124630 1691285 := bbase (se 6 (by rfl) ⟨39639, by rfl⟩ : syracuseStep 1691285 = 79279) (by norm_num)
theorem B1265305 : Blo 1124630 1265305 := bbase (se 2 (by rfl) ⟨474489, by rfl⟩ : syracuseStep 1265305 = 948979) (by norm_num)
theorem B1691309 : Blo 1124630 1691309 := bbase (se 3 (by rfl) ⟨317120, by rfl⟩ : syracuseStep 1691309 = 634241) (by norm_num)
theorem B1265341 : Blo 1124630 1265341 := bbase (se 3 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 1265341 = 474503) (by norm_num)
theorem B1691333 : Blo 1124630 1691333 := bbase (se 4 (by rfl) ⟨158562, by rfl⟩ : syracuseStep 1691333 = 317125) (by norm_num)
theorem B1691357 : Blo 1124630 1691357 := bbase (se 3 (by rfl) ⟨317129, by rfl⟩ : syracuseStep 1691357 = 634259) (by norm_num)
theorem B1265377 : Blo 1124630 1265377 := bbase (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) (by norm_num)
theorem B1691381 : Blo 1124630 1691381 := bbase (se 5 (by rfl) ⟨79283, by rfl⟩ : syracuseStep 1691381 = 158567) (by norm_num)
theorem B1265413 : Blo 1124630 1265413 := bbase (se 4 (by rfl) ⟨118632, by rfl⟩ : syracuseStep 1265413 = 237265) (by norm_num)
theorem B1691405 : Blo 1124630 1691405 := bbase (se 3 (by rfl) ⟨317138, by rfl⟩ : syracuseStep 1691405 = 634277) (by norm_num)
theorem B1691429 : Blo 1124630 1691429 := bbase (se 4 (by rfl) ⟨158571, by rfl⟩ : syracuseStep 1691429 = 317143) (by norm_num)
theorem B1265449 : Blo 1124630 1265449 := bbase (se 2 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 1265449 = 949087) (by norm_num)
theorem B1691453 : Blo 1124630 1691453 := bbase (se 3 (by rfl) ⟨317147, by rfl⟩ : syracuseStep 1691453 = 634295) (by norm_num)
theorem B1265485 : Blo 1124630 1265485 := bbase (se 3 (by rfl) ⟨237278, by rfl⟩ : syracuseStep 1265485 = 474557) (by norm_num)
theorem B1691477 : Blo 1124630 1691477 := bbase (se 9 (by rfl) ⟨4955, by rfl⟩ : syracuseStep 1691477 = 9911) (by norm_num)
theorem B1691501 : Blo 1124630 1691501 := bbase (se 3 (by rfl) ⟨317156, by rfl⟩ : syracuseStep 1691501 = 634313) (by norm_num)
theorem B1265521 : Blo 1124630 1265521 := bbase (se 2 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 1265521 = 949141) (by norm_num)
theorem B1691525 : Blo 1124630 1691525 := bbase (se 4 (by rfl) ⟨158580, by rfl⟩ : syracuseStep 1691525 = 317161) (by norm_num)
theorem B1265557 : Blo 1124630 1265557 := bbase (se 6 (by rfl) ⟨29661, by rfl⟩ : syracuseStep 1265557 = 59323) (by norm_num)
theorem B1691549 : Blo 1124630 1691549 := bbase (se 3 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 1691549 = 634331) (by norm_num)
theorem B1691573 : Blo 1124630 1691573 := bbase (se 5 (by rfl) ⟨79292, by rfl⟩ : syracuseStep 1691573 = 158585) (by norm_num)
theorem B1265593 : Blo 1124630 1265593 := bbase (se 2 (by rfl) ⟨474597, by rfl⟩ : syracuseStep 1265593 = 949195) (by norm_num)
theorem B1691597 : Blo 1124630 1691597 := bbase (se 3 (by rfl) ⟨317174, by rfl⟩ : syracuseStep 1691597 = 634349) (by norm_num)
theorem B1265629 : Blo 1124630 1265629 := bbase (se 3 (by rfl) ⟨237305, by rfl⟩ : syracuseStep 1265629 = 474611) (by norm_num)
theorem B1691621 : Blo 1124630 1691621 := bbase (se 4 (by rfl) ⟨158589, by rfl⟩ : syracuseStep 1691621 = 317179) (by norm_num)
theorem B8114165 : Blo 1124630 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B4280309 : Blo 1124630 4280309 := bbase (se 5 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 4280309 = 401279) (by norm_num)
theorem B1691645 : Blo 1124630 1691645 := bbase (se 3 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 1691645 = 634367) (by norm_num)
theorem B1265665 : Blo 1124630 1265665 := bbase (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) (by norm_num)
theorem B1691669 : Blo 1124630 1691669 := bbase (se 6 (by rfl) ⟨39648, by rfl⟩ : syracuseStep 1691669 = 79297) (by norm_num)
theorem B1265701 : Blo 1124630 1265701 := bbase (se 4 (by rfl) ⟨118659, by rfl⟩ : syracuseStep 1265701 = 237319) (by norm_num)
theorem B1691693 : Blo 1124630 1691693 := bbase (se 3 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 1691693 = 634385) (by norm_num)
theorem B1691717 : Blo 1124630 1691717 := bbase (se 4 (by rfl) ⟨158598, by rfl⟩ : syracuseStep 1691717 = 317197) (by norm_num)
theorem B1265737 : Blo 1124630 1265737 := bbase (se 2 (by rfl) ⟨474651, by rfl⟩ : syracuseStep 1265737 = 949303) (by norm_num)
theorem B1691741 : Blo 1124630 1691741 := bbase (se 3 (by rfl) ⟨317201, by rfl⟩ : syracuseStep 1691741 = 634403) (by norm_num)
theorem B1265773 : Blo 1124630 1265773 := bbase (se 3 (by rfl) ⟨237332, by rfl⟩ : syracuseStep 1265773 = 474665) (by norm_num)
theorem B1691765 : Blo 1124630 1691765 := bbase (se 5 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 1691765 = 158603) (by norm_num)
theorem B4575365 : Blo 1124630 4575365 := bbase (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) (by norm_num)
theorem B1691789 : Blo 1124630 1691789 := bbase (se 3 (by rfl) ⟨317210, by rfl⟩ : syracuseStep 1691789 = 634421) (by norm_num)
theorem B1265809 : Blo 1124630 1265809 := bbase (se 2 (by rfl) ⟨474678, by rfl⟩ : syracuseStep 1265809 = 949357) (by norm_num)
theorem B1691813 : Blo 1124630 1691813 := bbase (se 4 (by rfl) ⟨158607, by rfl⟩ : syracuseStep 1691813 = 317215) (by norm_num)
theorem B1265845 : Blo 1124630 1265845 := bbase (se 5 (by rfl) ⟨59336, by rfl⟩ : syracuseStep 1265845 = 118673) (by norm_num)
theorem B1691837 : Blo 1124630 1691837 := bbase (se 3 (by rfl) ⟨317219, by rfl⟩ : syracuseStep 1691837 = 634439) (by norm_num)
theorem B1691861 : Blo 1124630 1691861 := bbase (se 7 (by rfl) ⟨19826, by rfl⟩ : syracuseStep 1691861 = 39653) (by norm_num)
theorem B1265881 : Blo 1124630 1265881 := bbase (se 2 (by rfl) ⟨474705, by rfl⟩ : syracuseStep 1265881 = 949411) (by norm_num)
theorem B1691885 : Blo 1124630 1691885 := bbase (se 3 (by rfl) ⟨317228, by rfl⟩ : syracuseStep 1691885 = 634457) (by norm_num)
theorem B1265917 : Blo 1124630 1265917 := bbase (se 3 (by rfl) ⟨237359, by rfl⟩ : syracuseStep 1265917 = 474719) (by norm_num)
theorem B1691909 : Blo 1124630 1691909 := bbase (se 4 (by rfl) ⟨158616, by rfl⟩ : syracuseStep 1691909 = 317233) (by norm_num)
theorem B4280597 : Blo 1124630 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B1691933 : Blo 1124630 1691933 := bbase (se 3 (by rfl) ⟨317237, by rfl⟩ : syracuseStep 1691933 = 634475) (by norm_num)
theorem B1265953 : Blo 1124630 1265953 := bbase (se 2 (by rfl) ⟨474732, by rfl⟩ : syracuseStep 1265953 = 949465) (by norm_num)
theorem B1691957 : Blo 1124630 1691957 := bbase (se 5 (by rfl) ⟨79310, by rfl⟩ : syracuseStep 1691957 = 158621) (by norm_num)
theorem B1265989 : Blo 1124630 1265989 := bbase (se 4 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 1265989 = 237373) (by norm_num)
theorem B1691981 : Blo 1124630 1691981 := bbase (se 3 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 1691981 = 634493) (by norm_num)
theorem B1692005 : Blo 1124630 1692005 := bbase (se 4 (by rfl) ⟨158625, by rfl⟩ : syracuseStep 1692005 = 317251) (by norm_num)
theorem B1266025 : Blo 1124630 1266025 := bbase (se 2 (by rfl) ⟨474759, by rfl⟩ : syracuseStep 1266025 = 949519) (by norm_num)
theorem B1692029 : Blo 1124630 1692029 := bbase (se 3 (by rfl) ⟨317255, by rfl⟩ : syracuseStep 1692029 = 634511) (by norm_num)
theorem B1266061 : Blo 1124630 1266061 := bbase (se 3 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 1266061 = 474773) (by norm_num)
theorem B1692053 : Blo 1124630 1692053 := bbase (se 6 (by rfl) ⟨39657, by rfl⟩ : syracuseStep 1692053 = 79315) (by norm_num)
theorem B1692077 : Blo 1124630 1692077 := bbase (se 3 (by rfl) ⟨317264, by rfl⟩ : syracuseStep 1692077 = 634529) (by norm_num)
theorem B1266097 : Blo 1124630 1266097 := bbase (se 2 (by rfl) ⟨474786, by rfl⟩ : syracuseStep 1266097 = 949573) (by norm_num)
theorem B4805045 : Blo 1124630 4805045 := bbase (se 5 (by rfl) ⟨225236, by rfl⟩ : syracuseStep 4805045 = 450473) (by norm_num)
theorem B1692101 : Blo 1124630 1692101 := bbase (se 4 (by rfl) ⟨158634, by rfl⟩ : syracuseStep 1692101 = 317269) (by norm_num)
theorem B1266133 : Blo 1124630 1266133 := bbase (se 7 (by rfl) ⟨14837, by rfl⟩ : syracuseStep 1266133 = 29675) (by norm_num)
theorem B1692125 : Blo 1124630 1692125 := bbase (se 3 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 1692125 = 634547) (by norm_num)
theorem B1692149 : Blo 1124630 1692149 := bbase (se 5 (by rfl) ⟨79319, by rfl⟩ : syracuseStep 1692149 = 158639) (by norm_num)
theorem B1266169 : Blo 1124630 1266169 := bbase (se 2 (by rfl) ⟨474813, by rfl⟩ : syracuseStep 1266169 = 949627) (by norm_num)
theorem B1692173 : Blo 1124630 1692173 := bbase (se 3 (by rfl) ⟨317282, by rfl⟩ : syracuseStep 1692173 = 634565) (by norm_num)
theorem B1954325 : Blo 1124630 1954325 := bbase (se 6 (by rfl) ⟨45804, by rfl⟩ : syracuseStep 1954325 = 91609) (by norm_num)
theorem B1266205 : Blo 1124630 1266205 := bbase (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) (by norm_num)
theorem B1692197 : Blo 1124630 1692197 := bbase (se 4 (by rfl) ⟨158643, by rfl⟩ : syracuseStep 1692197 = 317287) (by norm_num)
theorem B1692221 : Blo 1124630 1692221 := bbase (se 3 (by rfl) ⟨317291, by rfl⟩ : syracuseStep 1692221 = 634583) (by norm_num)
theorem B1266241 : Blo 1124630 1266241 := bbase (se 2 (by rfl) ⟨474840, by rfl⟩ : syracuseStep 1266241 = 949681) (by norm_num)
theorem B1692245 : Blo 1124630 1692245 := bbase (se 8 (by rfl) ⟨9915, by rfl⟩ : syracuseStep 1692245 = 19831) (by norm_num)
theorem B1266277 : Blo 1124630 1266277 := bbase (se 4 (by rfl) ⟨118713, by rfl⟩ : syracuseStep 1266277 = 237427) (by norm_num)
theorem B1692269 : Blo 1124630 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B6509173 : Blo 1124630 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B1692293 : Blo 1124630 1692293 := bbase (se 4 (by rfl) ⟨158652, by rfl⟩ : syracuseStep 1692293 = 317305) (by norm_num)
theorem B1266313 : Blo 1124630 1266313 := bbase (se 2 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 1266313 = 949735) (by norm_num)
theorem B1692317 : Blo 1124630 1692317 := bbase (se 3 (by rfl) ⟨317309, by rfl⟩ : syracuseStep 1692317 = 634619) (by norm_num)
theorem B1266349 : Blo 1124630 1266349 := bbase (se 3 (by rfl) ⟨237440, by rfl⟩ : syracuseStep 1266349 = 474881) (by norm_num)
theorem B1692341 : Blo 1124630 1692341 := bbase (se 5 (by rfl) ⟨79328, by rfl⟩ : syracuseStep 1692341 = 158657) (by norm_num)
theorem B1692365 : Blo 1124630 1692365 := bbase (se 3 (by rfl) ⟨317318, by rfl⟩ : syracuseStep 1692365 = 634637) (by norm_num)
theorem B1266385 : Blo 1124630 1266385 := bbase (se 2 (by rfl) ⟨474894, by rfl⟩ : syracuseStep 1266385 = 949789) (by norm_num)
theorem B1692389 : Blo 1124630 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B1266421 : Blo 1124630 1266421 := bbase (se 5 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 1266421 = 118727) (by norm_num)
theorem B1692413 : Blo 1124630 1692413 := bbase (se 3 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 1692413 = 634655) (by norm_num)
theorem B1692437 : Blo 1124630 1692437 := bbase (se 6 (by rfl) ⟨39666, by rfl⟩ : syracuseStep 1692437 = 79333) (by norm_num)
theorem B1266457 : Blo 1124630 1266457 := bbase (se 2 (by rfl) ⟨474921, by rfl⟩ : syracuseStep 1266457 = 949843) (by norm_num)
theorem B1692461 : Blo 1124630 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B1266493 : Blo 1124630 1266493 := bbase (se 3 (by rfl) ⟨237467, by rfl⟩ : syracuseStep 1266493 = 474935) (by norm_num)
theorem B1692485 : Blo 1124630 1692485 := bbase (se 4 (by rfl) ⟨158670, by rfl⟩ : syracuseStep 1692485 = 317341) (by norm_num)
theorem B1692509 : Blo 1124630 1692509 := bbase (se 3 (by rfl) ⟨317345, by rfl⟩ : syracuseStep 1692509 = 634691) (by norm_num)
theorem B1266529 : Blo 1124630 1266529 := bbase (se 2 (by rfl) ⟨474948, by rfl⟩ : syracuseStep 1266529 = 949897) (by norm_num)
theorem B1692533 : Blo 1124630 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B1266565 : Blo 1124630 1266565 := bbase (se 4 (by rfl) ⟨118740, by rfl⟩ : syracuseStep 1266565 = 237481) (by norm_num)
theorem B1692557 : Blo 1124630 1692557 := bbase (se 3 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 1692557 = 634709) (by norm_num)
theorem B1692581 : Blo 1124630 1692581 := bbase (se 4 (by rfl) ⟨158679, by rfl⟩ : syracuseStep 1692581 = 317359) (by norm_num)
theorem B1266601 : Blo 1124630 1266601 := bbase (se 2 (by rfl) ⟨474975, by rfl⟩ : syracuseStep 1266601 = 949951) (by norm_num)
theorem B1201073 : Blo 1124630 1201073 := bbase (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) (by norm_num)
theorem B1692605 : Blo 1124630 1692605 := bbase (se 3 (by rfl) ⟨317363, by rfl⟩ : syracuseStep 1692605 = 634727) (by norm_num)
theorem B1266637 : Blo 1124630 1266637 := bbase (se 3 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 1266637 = 474989) (by norm_num)
theorem B1692629 : Blo 1124630 1692629 := bbase (se 7 (by rfl) ⟨19835, by rfl⟩ : syracuseStep 1692629 = 39671) (by norm_num)
theorem B1463269 : Blo 1124630 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B1692653 : Blo 1124630 1692653 := bbase (se 3 (by rfl) ⟨317372, by rfl⟩ : syracuseStep 1692653 = 634745) (by norm_num)
theorem B1266673 : Blo 1124630 1266673 := bbase (se 2 (by rfl) ⟨475002, by rfl⟩ : syracuseStep 1266673 = 950005) (by norm_num)
theorem B1692677 : Blo 1124630 1692677 := bbase (se 4 (by rfl) ⟨158688, by rfl⟩ : syracuseStep 1692677 = 317377) (by norm_num)
theorem B1266709 : Blo 1124630 1266709 := bbase (se 6 (by rfl) ⟨29688, by rfl⟩ : syracuseStep 1266709 = 59377) (by norm_num)
theorem B1692701 : Blo 1124630 1692701 := bbase (se 3 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 1692701 = 634763) (by norm_num)
theorem B1692725 : Blo 1124630 1692725 := bbase (se 5 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 1692725 = 158693) (by norm_num)
theorem B1266745 : Blo 1124630 1266745 := bbase (se 2 (by rfl) ⟨475029, by rfl⟩ : syracuseStep 1266745 = 950059) (by norm_num)
theorem B1692749 : Blo 1124630 1692749 := bbase (se 3 (by rfl) ⟨317390, by rfl⟩ : syracuseStep 1692749 = 634781) (by norm_num)
theorem B1266781 : Blo 1124630 1266781 := bbase (se 3 (by rfl) ⟨237521, by rfl⟩ : syracuseStep 1266781 = 475043) (by norm_num)
theorem B1692773 : Blo 1124630 1692773 := bbase (se 4 (by rfl) ⟨158697, by rfl⟩ : syracuseStep 1692773 = 317395) (by norm_num)
theorem B1692797 : Blo 1124630 1692797 := bbase (se 3 (by rfl) ⟨317399, by rfl⟩ : syracuseStep 1692797 = 634799) (by norm_num)
theorem B1266817 : Blo 1124630 1266817 := bbase (se 2 (by rfl) ⟨475056, by rfl⟩ : syracuseStep 1266817 = 950113) (by norm_num)
theorem B1692821 : Blo 1124630 1692821 := bbase (se 6 (by rfl) ⟨39675, by rfl⟩ : syracuseStep 1692821 = 79351) (by norm_num)
theorem B1266853 : Blo 1124630 1266853 := bbase (se 4 (by rfl) ⟨118767, by rfl⟩ : syracuseStep 1266853 = 237535) (by norm_num)
theorem B1201321 : Blo 1124630 1201321 := bbase (se 2 (by rfl) ⟨450495, by rfl⟩ : syracuseStep 1201321 = 900991) (by norm_num)
theorem B1692845 : Blo 1124630 1692845 := bbase (se 3 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 1692845 = 634817) (by norm_num)
theorem B1692869 : Blo 1124630 1692869 := bbase (se 4 (by rfl) ⟨158706, by rfl⟩ : syracuseStep 1692869 = 317413) (by norm_num)
theorem B1266889 : Blo 1124630 1266889 := bbase (se 2 (by rfl) ⟨475083, by rfl⟩ : syracuseStep 1266889 = 950167) (by norm_num)
theorem B1692893 : Blo 1124630 1692893 := bbase (se 3 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 1692893 = 634835) (by norm_num)
theorem B1266925 : Blo 1124630 1266925 := bbase (se 3 (by rfl) ⟨237548, by rfl⟩ : syracuseStep 1266925 = 475097) (by norm_num)
theorem B1692917 : Blo 1124630 1692917 := bbase (se 5 (by rfl) ⟨79355, by rfl⟩ : syracuseStep 1692917 = 158711) (by norm_num)
theorem B1692941 : Blo 1124630 1692941 := bbase (se 3 (by rfl) ⟨317426, by rfl⟩ : syracuseStep 1692941 = 634853) (by norm_num)
theorem B1266961 : Blo 1124630 1266961 := bbase (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) (by norm_num)
theorem B1266997 : Blo 1124630 1266997 := bbase (se 5 (by rfl) ⟨59390, by rfl⟩ : syracuseStep 1266997 = 118781) (by norm_num)
theorem B2708797 : Blo 1124630 2708797 := bbase (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) (by norm_num)
theorem B1267033 : Blo 1124630 1267033 := bbase (se 2 (by rfl) ⟨475137, by rfl⟩ : syracuseStep 1267033 = 950275) (by norm_num)
theorem B1267069 : Blo 1124630 1267069 := bbase (se 3 (by rfl) ⟨237575, by rfl⟩ : syracuseStep 1267069 = 475151) (by norm_num)
theorem B1267105 : Blo 1124630 1267105 := bbase (se 2 (by rfl) ⟨475164, by rfl⟩ : syracuseStep 1267105 = 950329) (by norm_num)
theorem B4281781 : Blo 1124630 4281781 := bbase (se 5 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 4281781 = 401417) (by norm_num)
theorem B1267141 : Blo 1124630 1267141 := bbase (se 4 (by rfl) ⟨118794, by rfl⟩ : syracuseStep 1267141 = 237589) (by norm_num)
theorem B1267177 : Blo 1124630 1267177 := bbase (se 2 (by rfl) ⟨475191, by rfl⟩ : syracuseStep 1267177 = 950383) (by norm_num)
theorem B1267213 : Blo 1124630 1267213 := bbase (se 3 (by rfl) ⟨237602, by rfl⟩ : syracuseStep 1267213 = 475205) (by norm_num)
theorem B1267249 : Blo 1124630 1267249 := bbase (se 2 (by rfl) ⟨475218, by rfl⟩ : syracuseStep 1267249 = 950437) (by norm_num)
theorem B1267285 : Blo 1124630 1267285 := bbase (se 8 (by rfl) ⟨7425, by rfl⟩ : syracuseStep 1267285 = 14851) (by norm_num)
theorem B1201753 : Blo 1124630 1201753 := bbase (se 2 (by rfl) ⟨450657, by rfl⟩ : syracuseStep 1201753 = 901315) (by norm_num)
theorem B1267321 : Blo 1124630 1267321 := bbase (se 2 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 1267321 = 950491) (by norm_num)
theorem B1267357 : Blo 1124630 1267357 := bbase (se 3 (by rfl) ⟨237629, by rfl⟩ : syracuseStep 1267357 = 475259) (by norm_num)
theorem B1201825 : Blo 1124630 1201825 := bbase (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) (by norm_num)
theorem B1267393 : Blo 1124630 1267393 := bbase (se 2 (by rfl) ⟨475272, by rfl⟩ : syracuseStep 1267393 = 950545) (by norm_num)
theorem B1267429 : Blo 1124630 1267429 := bbase (se 4 (by rfl) ⟨118821, by rfl⟩ : syracuseStep 1267429 = 237643) (by norm_num)
theorem B4282085 : Blo 1124630 4282085 := bbase (se 4 (by rfl) ⟨401445, by rfl⟩ : syracuseStep 4282085 = 802891) (by norm_num)
theorem B1267465 : Blo 1124630 1267465 := bbase (se 2 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 1267465 = 950599) (by norm_num)
theorem B1267501 : Blo 1124630 1267501 := bbase (se 3 (by rfl) ⟨237656, by rfl⟩ : syracuseStep 1267501 = 475313) (by norm_num)
theorem B10835765 : Blo 1124630 10835765 := bbase (se 5 (by rfl) ⟨507926, by rfl⟩ : syracuseStep 10835765 = 1015853) (by norm_num)
theorem B1267537 : Blo 1124630 1267537 := bbase (se 2 (by rfl) ⟨475326, by rfl⟩ : syracuseStep 1267537 = 950653) (by norm_num)
theorem B1267573 : Blo 1124630 1267573 := bbase (se 5 (by rfl) ⟨59417, by rfl⟩ : syracuseStep 1267573 = 118835) (by norm_num)
theorem B1267609 : Blo 1124630 1267609 := bbase (se 2 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 1267609 = 950707) (by norm_num)
theorem B2709413 : Blo 1124630 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B1267645 : Blo 1124630 1267645 := bbase (se 3 (by rfl) ⟨237683, by rfl⟩ : syracuseStep 1267645 = 475367) (by norm_num)
theorem B12834773 : Blo 1124630 12834773 := bbase (se 7 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 12834773 = 300815) (by norm_num)
theorem B1267681 : Blo 1124630 1267681 := bbase (se 2 (by rfl) ⟨475380, by rfl⟩ : syracuseStep 1267681 = 950761) (by norm_num)
theorem B1267717 : Blo 1124630 1267717 := bbase (se 4 (by rfl) ⟨118848, by rfl⟩ : syracuseStep 1267717 = 237697) (by norm_num)
theorem B1202197 : Blo 1124630 1202197 := bbase (se 6 (by rfl) ⟨28176, by rfl⟩ : syracuseStep 1202197 = 56353) (by norm_num)
theorem B1267753 : Blo 1124630 1267753 := bbase (se 2 (by rfl) ⟨475407, by rfl⟩ : syracuseStep 1267753 = 950815) (by norm_num)
theorem B1267789 : Blo 1124630 1267789 := bbase (se 3 (by rfl) ⟨237710, by rfl⟩ : syracuseStep 1267789 = 475421) (by norm_num)
theorem B1300573 : Blo 1124630 1300573 := bbase (se 3 (by rfl) ⟨243857, by rfl⟩ : syracuseStep 1300573 = 487715) (by norm_num)
theorem B2709605 : Blo 1124630 2709605 := bbase (se 4 (by rfl) ⟨254025, by rfl⟩ : syracuseStep 2709605 = 508051) (by norm_num)
theorem B1267825 : Blo 1124630 1267825 := bbase (se 2 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 1267825 = 950869) (by norm_num)
theorem B1267861 : Blo 1124630 1267861 := bbase (se 6 (by rfl) ⟨29715, by rfl⟩ : syracuseStep 1267861 = 59431) (by norm_num)
theorem B1628309 : Blo 1124630 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B3659957 : Blo 1124630 3659957 := bbase (se 5 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 3659957 = 343121) (by norm_num)
theorem B1267897 : Blo 1124630 1267897 := bbase (se 2 (by rfl) ⟨475461, by rfl⟩ : syracuseStep 1267897 = 950923) (by norm_num)
theorem B8542421 : Blo 1124630 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B1267933 : Blo 1124630 1267933 := bbase (se 3 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 1267933 = 475475) (by norm_num)
theorem B1267969 : Blo 1124630 1267969 := bbase (se 2 (by rfl) ⟨475488, by rfl⟩ : syracuseStep 1267969 = 950977) (by norm_num)
theorem B1268005 : Blo 1124630 1268005 := bbase (se 4 (by rfl) ⟨118875, by rfl⟩ : syracuseStep 1268005 = 237751) (by norm_num)
theorem B1268041 : Blo 1124630 1268041 := bbase (se 2 (by rfl) ⟨475515, by rfl⟩ : syracuseStep 1268041 = 951031) (by norm_num)
theorem B9623893 : Blo 1124630 9623893 := bbase (se 10 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 9623893 = 28195) (by norm_num)
theorem B1268077 : Blo 1124630 1268077 := bbase (se 3 (by rfl) ⟨237764, by rfl⟩ : syracuseStep 1268077 = 475529) (by norm_num)
theorem B1202573 : Blo 1124630 1202573 := bbase (se 3 (by rfl) ⟨225482, by rfl⟩ : syracuseStep 1202573 = 450965) (by norm_num)
theorem B1268113 : Blo 1124630 1268113 := bbase (se 2 (by rfl) ⟨475542, by rfl⟩ : syracuseStep 1268113 = 951085) (by norm_num)
theorem B1268149 : Blo 1124630 1268149 := bbase (se 5 (by rfl) ⟨59444, by rfl⟩ : syracuseStep 1268149 = 118889) (by norm_num)
theorem B1202645 : Blo 1124630 1202645 := bbase (se 7 (by rfl) ⟨14093, by rfl⟩ : syracuseStep 1202645 = 28187) (by norm_num)
theorem B1268185 : Blo 1124630 1268185 := bbase (se 2 (by rfl) ⟨475569, by rfl⟩ : syracuseStep 1268185 = 951139) (by norm_num)
theorem B1268221 : Blo 1124630 1268221 := bbase (se 3 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 1268221 = 475583) (by norm_num)
theorem B1268257 : Blo 1124630 1268257 := bbase (se 2 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 1268257 = 951193) (by norm_num)
theorem B1268293 : Blo 1124630 1268293 := bbase (se 4 (by rfl) ⟨118902, by rfl⟩ : syracuseStep 1268293 = 237805) (by norm_num)
theorem B1268329 : Blo 1124630 1268329 := bbase (se 2 (by rfl) ⟨475623, by rfl⟩ : syracuseStep 1268329 = 951247) (by norm_num)
theorem B1268365 : Blo 1124630 1268365 := bbase (se 3 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 1268365 = 475637) (by norm_num)
theorem B1202833 : Blo 1124630 1202833 := bbase (se 2 (by rfl) ⟨451062, by rfl⟩ : syracuseStep 1202833 = 902125) (by norm_num)
theorem B2710181 : Blo 1124630 2710181 := bbase (se 4 (by rfl) ⟨254079, by rfl⟩ : syracuseStep 2710181 = 508159) (by norm_num)
theorem B1268401 : Blo 1124630 1268401 := bbase (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) (by norm_num)
theorem B1268437 : Blo 1124630 1268437 := bbase (se 7 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 1268437 = 29729) (by norm_num)
theorem B1268473 : Blo 1124630 1268473 := bbase (se 2 (by rfl) ⟨475677, by rfl⟩ : syracuseStep 1268473 = 951355) (by norm_num)
theorem B2317061 : Blo 1124630 2317061 := bbase (se 4 (by rfl) ⟨217224, by rfl⟩ : syracuseStep 2317061 = 434449) (by norm_num)
theorem B9132821 : Blo 1124630 9132821 := bbase (se 6 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 9132821 = 428101) (by norm_num)
theorem B1268509 : Blo 1124630 1268509 := bbase (se 3 (by rfl) ⟨237845, by rfl⟩ : syracuseStep 1268509 = 475691) (by norm_num)
theorem B1268545 : Blo 1124630 1268545 := bbase (se 2 (by rfl) ⟨475704, by rfl⟩ : syracuseStep 1268545 = 951409) (by norm_num)
theorem B1203017 : Blo 1124630 1203017 := bbase (se 2 (by rfl) ⟨451131, by rfl⟩ : syracuseStep 1203017 = 902263) (by norm_num)
theorem B1268581 : Blo 1124630 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B1268617 : Blo 1124630 1268617 := bbase (se 2 (by rfl) ⟨475731, by rfl⟩ : syracuseStep 1268617 = 951463) (by norm_num)
theorem B1923997 : Blo 1124630 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B2284445 : Blo 1124630 2284445 := bbase (se 3 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 2284445 = 856667) (by norm_num)
theorem B1268653 : Blo 1124630 1268653 := bbase (se 3 (by rfl) ⟨237872, by rfl⟩ : syracuseStep 1268653 = 475745) (by norm_num)
theorem B1268689 : Blo 1124630 1268689 := bbase (se 2 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 1268689 = 951517) (by norm_num)
theorem B1268725 : Blo 1124630 1268725 := bbase (se 5 (by rfl) ⟨59471, by rfl⟩ : syracuseStep 1268725 = 118943) (by norm_num)
theorem B5790709 : Blo 1124630 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B1268761 : Blo 1124630 1268761 := bbase (se 2 (by rfl) ⟨475785, by rfl⟩ : syracuseStep 1268761 = 951571) (by norm_num)
theorem B2710565 : Blo 1124630 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B1465393 : Blo 1124630 1465393 := bbase (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) (by norm_num)
theorem B1268797 : Blo 1124630 1268797 := bbase (se 3 (by rfl) ⟨237899, by rfl⟩ : syracuseStep 1268797 = 475799) (by norm_num)
theorem B21683285 : Blo 1124630 21683285 := bbase (se 8 (by rfl) ⟨127050, by rfl⟩ : syracuseStep 21683285 = 254101) (by norm_num)
theorem B1268833 : Blo 1124630 1268833 := bbase (se 2 (by rfl) ⟨475812, by rfl⟩ : syracuseStep 1268833 = 951625) (by norm_num)
theorem B1268869 : Blo 1124630 1268869 := bbase (se 4 (by rfl) ⟨118956, by rfl⟩ : syracuseStep 1268869 = 237913) (by norm_num)
theorem B1301665 : Blo 1124630 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B1268905 : Blo 1124630 1268905 := bbase (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) (by norm_num)
theorem B1268941 : Blo 1124630 1268941 := bbase (se 3 (by rfl) ⟨237926, by rfl⟩ : syracuseStep 1268941 = 475853) (by norm_num)
theorem B1268977 : Blo 1124630 1268977 := bbase (se 2 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 1268977 = 951733) (by norm_num)
theorem B1269013 : Blo 1124630 1269013 := bbase (se 6 (by rfl) ⟨29742, by rfl⟩ : syracuseStep 1269013 = 59485) (by norm_num)
theorem B1269049 : Blo 1124630 1269049 := bbase (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) (by norm_num)
theorem B1269085 : Blo 1124630 1269085 := bbase (se 3 (by rfl) ⟨237953, by rfl⟩ : syracuseStep 1269085 = 475907) (by norm_num)
theorem B1236353 : Blo 1124630 1236353 := bbase (se 2 (by rfl) ⟨463632, by rfl⟩ : syracuseStep 1236353 = 927265) (by norm_num)
theorem B1269121 : Blo 1124630 1269121 := bbase (se 2 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 1269121 = 951841) (by norm_num)
theorem B3431813 : Blo 1124630 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B1269157 : Blo 1124630 1269157 := bbase (se 4 (by rfl) ⟨118983, by rfl⟩ : syracuseStep 1269157 = 237967) (by norm_num)
theorem B1269193 : Blo 1124630 1269193 := bbase (se 2 (by rfl) ⟨475947, by rfl⟩ : syracuseStep 1269193 = 951895) (by norm_num)
theorem B1269229 : Blo 1124630 1269229 := bbase (se 3 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 1269229 = 475961) (by norm_num)
theorem B1269265 : Blo 1124630 1269265 := bbase (se 2 (by rfl) ⟨475974, by rfl⟩ : syracuseStep 1269265 = 951949) (by norm_num)
theorem B1269301 : Blo 1124630 1269301 := bbase (se 5 (by rfl) ⟨59498, by rfl⟩ : syracuseStep 1269301 = 118997) (by norm_num)
theorem B1203769 : Blo 1124630 1203769 := bbase (se 2 (by rfl) ⟨451413, by rfl⟩ : syracuseStep 1203769 = 902827) (by norm_num)
theorem B1269337 : Blo 1124630 1269337 := bbase (se 2 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 1269337 = 952003) (by norm_num)
theorem B1269373 : Blo 1124630 1269373 := bbase (se 3 (by rfl) ⟨238007, by rfl⟩ : syracuseStep 1269373 = 476015) (by norm_num)
theorem B1203841 : Blo 1124630 1203841 := bbase (se 2 (by rfl) ⟨451440, by rfl⟩ : syracuseStep 1203841 = 902881) (by norm_num)
theorem B4054661 : Blo 1124630 4054661 := bbase (se 4 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 4054661 = 760249) (by norm_num)
theorem B1269409 : Blo 1124630 1269409 := bbase (se 2 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 1269409 = 952057) (by norm_num)
theorem B1269445 : Blo 1124630 1269445 := bbase (se 4 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 1269445 = 238021) (by norm_num)
theorem B1269481 : Blo 1124630 1269481 := bbase (se 2 (by rfl) ⟨476055, by rfl⟩ : syracuseStep 1269481 = 952111) (by norm_num)
theorem B1269517 : Blo 1124630 1269517 := bbase (se 3 (by rfl) ⟨238034, by rfl⟩ : syracuseStep 1269517 = 476069) (by norm_num)
theorem B4284197 : Blo 1124630 4284197 := bbase (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) (by norm_num)
theorem B1269553 : Blo 1124630 1269553 := bbase (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) (by norm_num)
theorem B1204021 : Blo 1124630 1204021 := bbase (se 5 (by rfl) ⟨56438, by rfl⟩ : syracuseStep 1204021 = 112877) (by norm_num)
theorem B1269589 : Blo 1124630 1269589 := bbase (se 9 (by rfl) ⟨3719, by rfl⟩ : syracuseStep 1269589 = 7439) (by norm_num)
theorem B1269625 : Blo 1124630 1269625 := bbase (se 2 (by rfl) ⟨476109, by rfl⟩ : syracuseStep 1269625 = 952219) (by norm_num)
theorem B1269661 : Blo 1124630 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B4054949 : Blo 1124630 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B1269697 : Blo 1124630 1269697 := bbase (se 2 (by rfl) ⟨476136, by rfl⟩ : syracuseStep 1269697 = 952273) (by norm_num)
theorem B1925141 : Blo 1124630 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B4284485 : Blo 1124630 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2285677 : Blo 1124630 2285677 := bbase (se 3 (by rfl) ⟨428564, by rfl⟩ : syracuseStep 2285677 = 857129) (by norm_num)
theorem B1204465 : Blo 1124630 1204465 := bbase (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) (by norm_num)
theorem B3203317 : Blo 1124630 3203317 := bbase (se 5 (by rfl) ⟨150155, by rfl⟩ : syracuseStep 3203317 = 300311) (by norm_num)
theorem B9625877 : Blo 1124630 9625877 := bbase (se 6 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 9625877 = 451213) (by norm_num)
theorem B1204589 : Blo 1124630 1204589 := bbase (se 3 (by rfl) ⟨225860, by rfl⟩ : syracuseStep 1204589 = 451721) (by norm_num)
theorem B5693813 : Blo 1124630 5693813 := bbase (se 5 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 5693813 = 533795) (by norm_num)
theorem B4809077 : Blo 1124630 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B1204841 : Blo 1124630 1204841 := bbase (se 2 (by rfl) ⟨451815, by rfl⟩ : syracuseStep 1204841 = 903631) (by norm_num)
theorem B5695109 : Blo 1124630 5695109 := bbase (se 4 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 5695109 = 1067833) (by norm_num)
theorem B3204821 : Blo 1124630 3204821 := bbase (se 7 (by rfl) ⟨37556, by rfl⟩ : syracuseStep 3204821 = 75113) (by norm_num)
theorem B1173253 : Blo 1124630 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B2287397 : Blo 1124630 2287397 := bbase (se 4 (by rfl) ⟨214443, by rfl⟩ : syracuseStep 2287397 = 428887) (by norm_num)
theorem B1370189 : Blo 1124630 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B4810853 : Blo 1124630 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B1140889 : Blo 1124630 1140889 := bbase (se 2 (by rfl) ⟨427833, by rfl⟩ : syracuseStep 1140889 = 855667) (by norm_num)
theorem B4057717 : Blo 1124630 4057717 := bbase (se 5 (by rfl) ⟨190205, by rfl⟩ : syracuseStep 4057717 = 380411) (by norm_num)
theorem B1927829 : Blo 1124630 1927829 := bbase (se 6 (by rfl) ⟨45183, by rfl⟩ : syracuseStep 1927829 = 90367) (by norm_num)
theorem B4057877 : Blo 1124630 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B5696405 : Blo 1124630 5696405 := bbase (se 6 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 5696405 = 267019) (by norm_num)
theorem B3796037 : Blo 1124630 3796037 := bbase (se 4 (by rfl) ⟨355878, by rfl⟩ : syracuseStep 3796037 = 711757) (by norm_num)
theorem B4811845 : Blo 1124630 4811845 := bbase (se 4 (by rfl) ⟨451110, by rfl⟩ : syracuseStep 4811845 = 902221) (by norm_num)
theorem B1174637 : Blo 1124630 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B3206405 : Blo 1124630 3206405 := bbase (se 4 (by rfl) ⟨300600, by rfl⟩ : syracuseStep 3206405 = 601201) (by norm_num)
theorem B2026957 : Blo 1124630 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B3796469 : Blo 1124630 3796469 := bbase (se 5 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 3796469 = 355919) (by norm_num)
theorem B1142381 : Blo 1124630 1142381 := bbase (se 3 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 1142381 = 428393) (by norm_num)
theorem B4878085 : Blo 1124630 4878085 := bbase (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) (by norm_num)
theorem B1601317 : Blo 1124630 1601317 := bbase (se 4 (by rfl) ⟨150123, by rfl⟩ : syracuseStep 1601317 = 300247) (by norm_num)
theorem B3796901 : Blo 1124630 3796901 := bbase (se 4 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 3796901 = 711919) (by norm_num)
theorem B3207077 : Blo 1124630 3207077 := bbase (se 4 (by rfl) ⟨300663, by rfl⟩ : syracuseStep 3207077 = 601327) (by norm_num)
theorem B2846765 : Blo 1124630 2846765 := bbase (se 3 (by rfl) ⟨533768, by rfl⟩ : syracuseStep 2846765 = 1067537) (by norm_num)
theorem B39055445 : Blo 1124630 39055445 := bbase (se 8 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 39055445 = 457681) (by norm_num)
theorem B5697701 : Blo 1124630 5697701 := bbase (se 4 (by rfl) ⟨534159, by rfl⟩ : syracuseStep 5697701 = 1068319) (by norm_num)
theorem B13693141 : Blo 1124630 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B1143001 : Blo 1124630 1143001 := bbase (se 2 (by rfl) ⟨428625, by rfl⟩ : syracuseStep 1143001 = 857251) (by norm_num)
theorem B6418709 : Blo 1124630 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B3797333 : Blo 1124630 3797333 := bbase (se 10 (by rfl) ⟨5562, by rfl⟩ : syracuseStep 3797333 = 11125) (by norm_num)
theorem B3207509 : Blo 1124630 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B2847109 : Blo 1124630 2847109 := bbase (se 4 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 2847109 = 533833) (by norm_num)
theorem B1143277 : Blo 1124630 1143277 := bbase (se 3 (by rfl) ⟨214364, by rfl⟩ : syracuseStep 1143277 = 428729) (by norm_num)
theorem B2847221 : Blo 1124630 2847221 := bbase (se 5 (by rfl) ⟨133463, by rfl⟩ : syracuseStep 2847221 = 266927) (by norm_num)
theorem B1143293 : Blo 1124630 1143293 := bbase (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) (by norm_num)
theorem B1143325 : Blo 1124630 1143325 := bbase (se 3 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 1143325 = 428747) (by norm_num)
theorem B1602109 : Blo 1124630 1602109 := bbase (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) (by norm_num)
theorem B2847413 : Blo 1124630 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B3797765 : Blo 1124630 3797765 := bbase (se 4 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 3797765 = 712081) (by norm_num)
theorem B2028341 : Blo 1124630 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B1602445 : Blo 1124630 1602445 := bbase (se 3 (by rfl) ⟨300458, by rfl⟩ : syracuseStep 1602445 = 600917) (by norm_num)
theorem B2847757 : Blo 1124630 2847757 := bbase (se 3 (by rfl) ⟨533954, by rfl⟩ : syracuseStep 2847757 = 1067909) (by norm_num)
theorem B2028557 : Blo 1124630 2028557 := bbase (se 3 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 2028557 = 760709) (by norm_num)
theorem B3208261 : Blo 1124630 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B1143877 : Blo 1124630 1143877 := bbase (se 4 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 1143877 = 214477) (by norm_num)
theorem B1602661 : Blo 1124630 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B2847869 : Blo 1124630 2847869 := bbase (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) (by norm_num)
theorem B3798197 : Blo 1124630 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B2848061 : Blo 1124630 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B1897877 : Blo 1124630 1897877 := bbase (se 6 (by rfl) ⟨44481, by rfl⟩ : syracuseStep 1897877 = 88963) (by norm_num)
theorem B5698997 : Blo 1124630 5698997 := bbase (se 5 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 5698997 = 534281) (by norm_num)
theorem B1603037 : Blo 1124630 1603037 := bbase (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) (by norm_num)
theorem B1898005 : Blo 1124630 1898005 := bbase (se 6 (by rfl) ⟨44484, by rfl⟩ : syracuseStep 1898005 = 88969) (by norm_num)
theorem B3798629 : Blo 1124630 3798629 := bbase (se 4 (by rfl) ⟨356121, by rfl⟩ : syracuseStep 3798629 = 712243) (by norm_num)
theorem B3044965 : Blo 1124630 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B1898093 : Blo 1124630 1898093 := bbase (se 3 (by rfl) ⟨355892, by rfl⟩ : syracuseStep 1898093 = 711785) (by norm_num)
theorem B2848405 : Blo 1124630 2848405 := bbase (se 6 (by rfl) ⟨66759, by rfl⟩ : syracuseStep 2848405 = 133519) (by norm_num)
theorem B1898221 : Blo 1124630 1898221 := bbase (se 3 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 1898221 = 711833) (by norm_num)
theorem B2848517 : Blo 1124630 2848517 := bbase (se 4 (by rfl) ⟨267048, by rfl⟩ : syracuseStep 2848517 = 534097) (by norm_num)
theorem B8550197 : Blo 1124630 8550197 := bbase (se 5 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 8550197 = 801581) (by norm_num)
theorem B1898309 : Blo 1124630 1898309 := bbase (se 4 (by rfl) ⟨177966, by rfl⟩ : syracuseStep 1898309 = 355933) (by norm_num)
theorem B1898437 : Blo 1124630 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B2848709 : Blo 1124630 2848709 := bbase (se 4 (by rfl) ⟨267066, by rfl⟩ : syracuseStep 2848709 = 534133) (by norm_num)
theorem B3799061 : Blo 1124630 3799061 := bbase (se 6 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 3799061 = 178081) (by norm_num)
theorem B1898525 : Blo 1124630 1898525 := bbase (se 3 (by rfl) ⟨355973, by rfl⟩ : syracuseStep 1898525 = 711947) (by norm_num)
theorem B2029637 : Blo 1124630 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B1898653 : Blo 1124630 1898653 := bbase (se 3 (by rfl) ⟨355997, by rfl⟩ : syracuseStep 1898653 = 711995) (by norm_num)
theorem B7207157 : Blo 1124630 7207157 := bbase (se 5 (by rfl) ⟨337835, by rfl⟩ : syracuseStep 7207157 = 675671) (by norm_num)
theorem B1898741 : Blo 1124630 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B2849053 : Blo 1124630 2849053 := bbase (se 3 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 2849053 = 1068395) (by norm_num)
theorem B2029861 : Blo 1124630 2029861 := bbase (se 4 (by rfl) ⟨190299, by rfl⟩ : syracuseStep 2029861 = 380599) (by norm_num)
theorem B46332245 : Blo 1124630 46332245 := bbase (se 10 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 46332245 = 135739) (by norm_num)
theorem B1898869 : Blo 1124630 1898869 := bbase (se 5 (by rfl) ⟨89009, by rfl⟩ : syracuseStep 1898869 = 178019) (by norm_num)
theorem B2849165 : Blo 1124630 2849165 := bbase (se 3 (by rfl) ⟨534218, by rfl⟩ : syracuseStep 2849165 = 1068437) (by norm_num)
theorem B3799493 : Blo 1124630 3799493 := bbase (se 4 (by rfl) ⟨356202, by rfl⟩ : syracuseStep 3799493 = 712405) (by norm_num)
theorem B1898957 : Blo 1124630 1898957 := bbase (se 3 (by rfl) ⟨356054, by rfl⟩ : syracuseStep 1898957 = 712109) (by norm_num)
theorem B1899085 : Blo 1124630 1899085 := bbase (se 3 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 1899085 = 712157) (by norm_num)
theorem B2849357 : Blo 1124630 2849357 := bbase (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) (by norm_num)
theorem B24672853 : Blo 1124630 24672853 := bbase (se 8 (by rfl) ⟨144567, by rfl⟩ : syracuseStep 24672853 = 289135) (by norm_num)
theorem B1899173 : Blo 1124630 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B5700293 : Blo 1124630 5700293 := bbase (se 4 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 5700293 = 1068805) (by norm_num)
theorem B1899301 : Blo 1124630 1899301 := bbase (se 4 (by rfl) ⟨178059, by rfl⟩ : syracuseStep 1899301 = 356119) (by norm_num)
theorem B1604461 : Blo 1124630 1604461 := bbase (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) (by norm_num)
theorem B3799925 : Blo 1124630 3799925 := bbase (se 5 (by rfl) ⟨178121, by rfl⟩ : syracuseStep 3799925 = 356243) (by norm_num)
theorem B1899389 : Blo 1124630 1899389 := bbase (se 3 (by rfl) ⟨356135, by rfl⟩ : syracuseStep 1899389 = 712271) (by norm_num)
theorem B2849701 : Blo 1124630 2849701 := bbase (se 4 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 2849701 = 534319) (by norm_num)
theorem B1899517 : Blo 1124630 1899517 := bbase (se 3 (by rfl) ⟨356159, by rfl⟩ : syracuseStep 1899517 = 712319) (by norm_num)
theorem B2849813 : Blo 1124630 2849813 := bbase (se 6 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 2849813 = 133585) (by norm_num)
theorem B1899605 : Blo 1124630 1899605 := bbase (se 8 (by rfl) ⟨11130, by rfl⟩ : syracuseStep 1899605 = 22261) (by norm_num)
theorem B8125525 : Blo 1124630 8125525 := bbase (se 8 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 8125525 = 95221) (by norm_num)
theorem B1899733 : Blo 1124630 1899733 := bbase (se 7 (by rfl) ⟨22262, by rfl⟩ : syracuseStep 1899733 = 44525) (by norm_num)
theorem B2850005 : Blo 1124630 2850005 := bbase (se 7 (by rfl) ⟨33398, by rfl⟩ : syracuseStep 2850005 = 66797) (by norm_num)
theorem B3800357 : Blo 1124630 3800357 := bbase (se 4 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 3800357 = 712567) (by norm_num)
theorem B1899821 : Blo 1124630 1899821 := bbase (se 3 (by rfl) ⟨356216, by rfl⟩ : syracuseStep 1899821 = 712433) (by norm_num)
theorem B5143925 : Blo 1124630 5143925 := bbase (se 5 (by rfl) ⟨241121, by rfl⟩ : syracuseStep 5143925 = 482243) (by norm_num)
theorem B1899949 : Blo 1124630 1899949 := bbase (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) (by norm_num)
theorem B1801661 : Blo 1124630 1801661 := bbase (se 3 (by rfl) ⟨337811, by rfl⟩ : syracuseStep 1801661 = 675623) (by norm_num)
theorem B1605053 : Blo 1124630 1605053 := bbase (se 3 (by rfl) ⟨300947, by rfl⟩ : syracuseStep 1605053 = 601895) (by norm_num)
theorem B1900037 : Blo 1124630 1900037 := bbase (se 4 (by rfl) ⟨178128, by rfl⟩ : syracuseStep 1900037 = 356257) (by norm_num)
theorem B1605133 : Blo 1124630 1605133 := bbase (se 3 (by rfl) ⟨300962, by rfl⟩ : syracuseStep 1605133 = 601925) (by norm_num)
theorem B3603989 : Blo 1124630 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B2850349 : Blo 1124630 2850349 := bbase (se 3 (by rfl) ⟨534440, by rfl⟩ : syracuseStep 2850349 = 1068881) (by norm_num)
theorem B1900165 : Blo 1124630 1900165 := bbase (se 4 (by rfl) ⟨178140, by rfl⟩ : syracuseStep 1900165 = 356281) (by norm_num)
theorem B1605253 : Blo 1124630 1605253 := bbase (se 4 (by rfl) ⟨150492, by rfl⟩ : syracuseStep 1605253 = 300985) (by norm_num)
theorem B2031245 : Blo 1124630 2031245 := bbase (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) (by norm_num)
theorem B2850461 : Blo 1124630 2850461 := bbase (se 3 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 2850461 = 1068923) (by norm_num)
theorem B3800789 : Blo 1124630 3800789 := bbase (se 7 (by rfl) ⟨44540, by rfl⟩ : syracuseStep 3800789 = 89081) (by norm_num)
theorem B1900253 : Blo 1124630 1900253 := bbase (se 3 (by rfl) ⟨356297, by rfl⟩ : syracuseStep 1900253 = 712595) (by norm_num)
theorem B1605349 : Blo 1124630 1605349 := bbase (se 4 (by rfl) ⟨150501, by rfl⟩ : syracuseStep 1605349 = 301003) (by norm_num)
theorem B1900381 : Blo 1124630 1900381 := bbase (se 3 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 1900381 = 712643) (by norm_num)
theorem B2850653 : Blo 1124630 2850653 := bbase (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) (by norm_num)
theorem B3211109 : Blo 1124630 3211109 := bbase (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) (by norm_num)
theorem B1900469 : Blo 1124630 1900469 := bbase (se 5 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 1900469 = 178169) (by norm_num)
theorem B5701589 : Blo 1124630 5701589 := bbase (se 7 (by rfl) ⟨66815, by rfl⟩ : syracuseStep 5701589 = 133631) (by norm_num)
theorem B4816853 : Blo 1124630 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B1900577 : Blo 1124630 1900577 := bstep (se 2 (by rfl) ⟨712716, by rfl⟩ : syracuseStep 1900577 = 1425433) B1425433
theorem B2850947 : Blo 1124630 2850947 := bstep (se 1 (by rfl) ⟨2138210, by rfl⟩ : syracuseStep 2850947 = 4276421) B4276421
theorem B1900705 : Blo 1124630 1900705 := bstep (se 2 (by rfl) ⟨712764, by rfl⟩ : syracuseStep 1900705 = 1425529) B1425529
theorem B3211427 : Blo 1124630 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B1900739 : Blo 1124630 1900739 := bstep (se 1 (by rfl) ⟨1425554, by rfl⟩ : syracuseStep 1900739 = 2851109) B2851109
theorem B14418161 : Blo 1124630 14418161 := bstep (se 2 (by rfl) ⟨5406810, by rfl⟩ : syracuseStep 14418161 = 10813621) B10813621
theorem B3801329 : Blo 1124630 3801329 := bstep (se 2 (by rfl) ⟨1425498, by rfl⟩ : syracuseStep 3801329 = 2850997) B2850997
theorem B16253237 : Blo 1124630 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B1605953 : Blo 1124630 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B2851139 : Blo 1124630 2851139 := bstep (se 1 (by rfl) ⟨2138354, by rfl⟩ : syracuseStep 2851139 = 4276709) B4276709
theorem B1900867 : Blo 1124630 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B1901009 : Blo 1124630 1901009 := bstep (se 2 (by rfl) ⟨712878, by rfl⟩ : syracuseStep 1901009 = 1425757) B1425757
theorem B4063715 : Blo 1124630 4063715 := bstep (se 1 (by rfl) ⟨3047786, by rfl⟩ : syracuseStep 4063715 = 6095573) B6095573
theorem B3047939 : Blo 1124630 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B12190277 : Blo 1124630 12190277 := bstep (se 4 (by rfl) ⟨1142838, by rfl⟩ : syracuseStep 12190277 = 2285677) B2285677
theorem B1901137 : Blo 1124630 1901137 := bstep (se 2 (by rfl) ⟨712926, by rfl⟩ : syracuseStep 1901137 = 1425853) B1425853
theorem B1901171 : Blo 1124630 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B3605219 : Blo 1124630 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B1901299 : Blo 1124630 1901299 := bstep (se 1 (by rfl) ⟨1425974, by rfl⟩ : syracuseStep 1901299 = 2851949) B2851949
theorem B3801869 : Blo 1124630 3801869 := bstep (se 3 (by rfl) ⟨712850, by rfl⟩ : syracuseStep 3801869 = 1425701) B1425701
theorem B3801923 : Blo 1124630 3801923 := bstep (se 1 (by rfl) ⟨2851442, by rfl⟩ : syracuseStep 3801923 = 5702885) B5702885
theorem B1606483 : Blo 1124630 1606483 := bstep (se 1 (by rfl) ⟨1204862, by rfl⟩ : syracuseStep 1606483 = 2409725) B2409725
theorem B1901441 : Blo 1124630 1901441 := bstep (se 2 (by rfl) ⟨713040, by rfl⟩ : syracuseStep 1901441 = 1426081) B1426081
theorem B3212237 : Blo 1124630 3212237 := bstep (se 3 (by rfl) ⟨602294, by rfl⟩ : syracuseStep 3212237 = 1204589) B1204589
theorem B1901569 : Blo 1124630 1901569 := bstep (se 2 (by rfl) ⟨713088, by rfl⟩ : syracuseStep 1901569 = 1426177) B1426177
theorem B1901603 : Blo 1124630 1901603 := bstep (se 1 (by rfl) ⟨1426202, by rfl⟩ : syracuseStep 1901603 = 2852405) B2852405
theorem B3802193 : Blo 1124630 3802193 := bstep (se 2 (by rfl) ⟨1425822, by rfl⟩ : syracuseStep 3802193 = 2851645) B2851645
theorem B1803379 : Blo 1124630 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B3212419 : Blo 1124630 3212419 := bstep (se 1 (by rfl) ⟨2409314, by rfl⟩ : syracuseStep 3212419 = 4818629) B4818629
theorem B6096005 : Blo 1124630 6096005 := bstep (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) B1143001
theorem B1901731 : Blo 1124630 1901731 := bstep (se 1 (by rfl) ⟨1426298, by rfl⟩ : syracuseStep 1901731 = 2852597) B2852597
theorem B1606819 : Blo 1124630 1606819 := bstep (se 1 (by rfl) ⟨1205114, by rfl⟩ : syracuseStep 1606819 = 2410229) B2410229
theorem B5932259 : Blo 1124630 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B2852081 : Blo 1124630 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B2852131 : Blo 1124630 2852131 := bstep (se 1 (by rfl) ⟨2139098, by rfl⟩ : syracuseStep 2852131 = 4278197) B4278197
theorem B3605809 : Blo 1124630 3605809 := bstep (se 2 (by rfl) ⟨1352178, by rfl⟩ : syracuseStep 3605809 = 2704357) B2704357
theorem B1901873 : Blo 1124630 1901873 := bstep (se 2 (by rfl) ⟨713202, by rfl⟩ : syracuseStep 1901873 = 1426405) B1426405
theorem B6423857 : Blo 1124630 6423857 := bstep (se 2 (by rfl) ⟨2408946, by rfl⟩ : syracuseStep 6423857 = 4817893) B4817893
theorem B3048781 : Blo 1124630 3048781 := bstep (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) B1143293
theorem B1803635 : Blo 1124630 1803635 := bstep (se 1 (by rfl) ⟨1352726, by rfl⟩ : syracuseStep 1803635 = 2705453) B2705453
theorem B5211533 : Blo 1124630 5211533 := bstep (se 3 (by rfl) ⟨977162, by rfl⟩ : syracuseStep 5211533 = 1954325) B1954325
theorem B2852273 : Blo 1124630 2852273 := bstep (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) B2139205
theorem B1902001 : Blo 1124630 1902001 := bstep (se 2 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 1902001 = 1426501) B1426501
theorem B1902035 : Blo 1124630 1902035 := bstep (se 1 (by rfl) ⟨1426526, by rfl⟩ : syracuseStep 1902035 = 2853053) B2853053
theorem B1803827 : Blo 1124630 1803827 := bstep (se 1 (by rfl) ⟨1352870, by rfl⟩ : syracuseStep 1803827 = 2705741) B2705741
theorem B1902163 : Blo 1124630 1902163 := bstep (se 1 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 1902163 = 2853245) B2853245
theorem B3802733 : Blo 1124630 3802733 := bstep (se 3 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 3802733 = 1426025) B1426025
theorem B3212909 : Blo 1124630 3212909 := bstep (se 3 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 3212909 = 1204841) B1204841
theorem B3802787 : Blo 1124630 3802787 := bstep (se 1 (by rfl) ⟨2852090, by rfl⟩ : syracuseStep 3802787 = 5704181) B5704181
theorem B1902305 : Blo 1124630 1902305 := bstep (se 2 (by rfl) ⟨713364, by rfl⟩ : syracuseStep 1902305 = 1426729) B1426729
theorem B1902433 : Blo 1124630 1902433 := bstep (se 2 (by rfl) ⟨713412, by rfl⟩ : syracuseStep 1902433 = 1426825) B1426825
theorem B1902467 : Blo 1124630 1902467 := bstep (se 1 (by rfl) ⟨1426850, by rfl⟩ : syracuseStep 1902467 = 2853701) B2853701
theorem B4818851 : Blo 1124630 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B3803057 : Blo 1124630 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B1902595 : Blo 1124630 1902595 := bstep (se 1 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 1902595 = 2853893) B2853893
theorem B4065329 : Blo 1124630 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B2033731 : Blo 1124630 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B1902737 : Blo 1124630 1902737 := bstep (se 2 (by rfl) ⟨713526, by rfl⟩ : syracuseStep 1902737 = 1427053) B1427053
theorem B5703857 : Blo 1124630 5703857 := bstep (se 2 (by rfl) ⟨2138946, by rfl⟩ : syracuseStep 5703857 = 4277893) B4277893
theorem B2885905 : Blo 1124630 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B1902865 : Blo 1124630 1902865 := bstep (se 2 (by rfl) ⟨713574, by rfl⟩ : syracuseStep 1902865 = 1427149) B1427149
theorem B1902899 : Blo 1124630 1902899 := bstep (se 1 (by rfl) ⟨1427174, by rfl⟩ : syracuseStep 1902899 = 2854349) B2854349
theorem B1804609 : Blo 1124630 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B3082573 : Blo 1124630 3082573 := bstep (se 3 (by rfl) ⟨577982, by rfl⟩ : syracuseStep 3082573 = 1155965) B1155965
theorem B2853265 : Blo 1124630 2853265 := bstep (se 2 (by rfl) ⟨1069974, by rfl⟩ : syracuseStep 2853265 = 2139949) B2139949
theorem B1903027 : Blo 1124630 1903027 := bstep (se 1 (by rfl) ⟨1427270, by rfl⟩ : syracuseStep 1903027 = 2854541) B2854541
theorem B3803597 : Blo 1124630 3803597 := bstep (se 3 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 3803597 = 1426349) B1426349
theorem B3803651 : Blo 1124630 3803651 := bstep (se 1 (by rfl) ⟨2852738, by rfl⟩ : syracuseStep 3803651 = 5705477) B5705477
theorem B1903169 : Blo 1124630 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B6097477 : Blo 1124630 6097477 := bstep (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) B1143277
theorem B5409443 : Blo 1124630 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B2853539 : Blo 1124630 2853539 := bstep (se 1 (by rfl) ⟨2140154, by rfl⟩ : syracuseStep 2853539 = 4280309) B4280309
theorem B1903297 : Blo 1124630 1903297 := bstep (se 2 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 1903297 = 1427473) B1427473
theorem B1903331 : Blo 1124630 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B6425315 : Blo 1124630 6425315 := bstep (se 1 (by rfl) ⟨4818986, by rfl⟩ : syracuseStep 6425315 = 9637973) B9637973
theorem B3050243 : Blo 1124630 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B3803921 : Blo 1124630 3803921 := bstep (se 2 (by rfl) ⟨1426470, by rfl⟩ : syracuseStep 3803921 = 2852941) B2852941
theorem B6097733 : Blo 1124630 6097733 := bstep (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) B1143325
theorem B1543009 : Blo 1124630 1543009 := bstep (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) B1157257
theorem B2853731 : Blo 1124630 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B1903459 : Blo 1124630 1903459 := bstep (se 1 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 1903459 = 2855189) B2855189
theorem B1903601 : Blo 1124630 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B1903729 : Blo 1124630 1903729 := bstep (se 2 (by rfl) ⟨713898, by rfl⟩ : syracuseStep 1903729 = 1427797) B1427797
theorem B1903763 : Blo 1124630 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B1903891 : Blo 1124630 1903891 := bstep (se 1 (by rfl) ⟨1427918, by rfl⟩ : syracuseStep 1903891 = 2855837) B2855837
theorem B3804461 : Blo 1124630 3804461 := bstep (se 3 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 3804461 = 1426673) B1426673
theorem B3804515 : Blo 1124630 3804515 := bstep (se 1 (by rfl) ⟨2853386, by rfl⟩ : syracuseStep 3804515 = 5706773) B5706773
theorem B1904033 : Blo 1124630 1904033 := bstep (se 2 (by rfl) ⟨714012, by rfl⟩ : syracuseStep 1904033 = 1428025) B1428025
theorem B5410289 : Blo 1124630 5410289 := bstep (se 2 (by rfl) ⟨2028858, by rfl⟩ : syracuseStep 5410289 = 4057717) B4057717
theorem B1904161 : Blo 1124630 1904161 := bstep (se 2 (by rfl) ⟨714060, by rfl⟩ : syracuseStep 1904161 = 1428121) B1428121
theorem B3247661 : Blo 1124630 3247661 := bstep (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) B1217873
theorem B357305909 : Blo 1124630 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B1904195 : Blo 1124630 1904195 := bstep (se 1 (by rfl) ⟨1428146, by rfl⟩ : syracuseStep 1904195 = 2856293) B2856293
theorem B5705315 : Blo 1124630 5705315 := bstep (se 1 (by rfl) ⟨4278986, by rfl⟩ : syracuseStep 5705315 = 8557973) B8557973
theorem B3804785 : Blo 1124630 3804785 := bstep (se 2 (by rfl) ⟨1426794, by rfl⟩ : syracuseStep 3804785 = 2853589) B2853589
theorem B4820593 : Blo 1124630 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B1904323 : Blo 1124630 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B6426317 : Blo 1124630 6426317 := bstep (se 3 (by rfl) ⟨1204934, by rfl⟩ : syracuseStep 6426317 = 2409869) B2409869
theorem B2854673 : Blo 1124630 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B2854723 : Blo 1124630 2854723 := bstep (se 1 (by rfl) ⟨2141042, by rfl⟩ : syracuseStep 2854723 = 4282085) B4282085
theorem B1904465 : Blo 1124630 1904465 := bstep (se 2 (by rfl) ⟨714174, by rfl⟩ : syracuseStep 1904465 = 1428349) B1428349
theorem B1806275 : Blo 1124630 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B2854865 : Blo 1124630 2854865 := bstep (se 2 (by rfl) ⟨1070574, by rfl⟩ : syracuseStep 2854865 = 2141149) B2141149
theorem B8556515 : Blo 1124630 8556515 := bstep (se 1 (by rfl) ⟨6417386, by rfl⟩ : syracuseStep 8556515 = 12834773) B12834773
theorem B2199601 : Blo 1124630 2199601 := bstep (se 2 (by rfl) ⟨824850, by rfl⟩ : syracuseStep 2199601 = 1649701) B1649701
theorem B36606005 : Blo 1124630 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B1806403 : Blo 1124630 1806403 := bstep (se 1 (by rfl) ⟨1354802, by rfl⟩ : syracuseStep 1806403 = 2709605) B2709605
theorem B3608653 : Blo 1124630 3608653 := bstep (se 3 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 3608653 = 1353245) B1353245
theorem B4067405 : Blo 1124630 4067405 := bstep (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) B1525277
theorem B3805325 : Blo 1124630 3805325 := bstep (se 3 (by rfl) ⟨713498, by rfl⟩ : syracuseStep 3805325 = 1426997) B1426997
theorem B3805379 : Blo 1124630 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B5706125 : Blo 1124630 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B2888131 : Blo 1124630 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B1806787 : Blo 1124630 1806787 := bstep (se 1 (by rfl) ⟨1355090, by rfl⟩ : syracuseStep 1806787 = 2710181) B2710181
theorem B3805649 : Blo 1124630 3805649 := bstep (se 2 (by rfl) ⟨1427118, by rfl⟩ : syracuseStep 3805649 = 2854237) B2854237
theorem B1544707 : Blo 1124630 1544707 := bstep (se 1 (by rfl) ⟨1158530, by rfl⟩ : syracuseStep 1544707 = 2317061) B2317061
theorem B1807043 : Blo 1124630 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B14455523 : Blo 1124630 14455523 := bstep (se 1 (by rfl) ⟨10841642, by rfl⟩ : syracuseStep 14455523 = 21683285) B21683285
theorem B6099725 : Blo 1124630 6099725 := bstep (se 3 (by rfl) ⟨1143698, by rfl⟩ : syracuseStep 6099725 = 2287397) B2287397
theorem B2855857 : Blo 1124630 2855857 := bstep (se 2 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 2855857 = 2141893) B2141893
theorem B3806189 : Blo 1124630 3806189 := bstep (se 3 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 3806189 = 1427321) B1427321
theorem B3806243 : Blo 1124630 3806243 := bstep (se 1 (by rfl) ⟨2854682, by rfl⟩ : syracuseStep 3806243 = 5709365) B5709365
theorem B2135089 : Blo 1124630 2135089 := bstep (se 2 (by rfl) ⟨800658, by rfl⟩ : syracuseStep 2135089 = 1601317) B1601317
theorem B7214129 : Blo 1124630 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B3249229 : Blo 1124630 3249229 := bstep (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) B1218461
theorem B1807505 : Blo 1124630 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B2856131 : Blo 1124630 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B1807601 : Blo 1124630 1807601 := bstep (se 2 (by rfl) ⟨677850, by rfl⟩ : syracuseStep 1807601 = 1355701) B1355701
theorem B1807633 : Blo 1124630 1807633 := bstep (se 2 (by rfl) ⟨677862, by rfl⟩ : syracuseStep 1807633 = 1355725) B1355725
theorem B3806513 : Blo 1124630 3806513 := bstep (se 2 (by rfl) ⟨1427442, by rfl⟩ : syracuseStep 3806513 = 2854885) B2854885
theorem B2856323 : Blo 1124630 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B3610115 : Blo 1124630 3610115 := bstep (se 1 (by rfl) ⟨2707586, by rfl⟩ : syracuseStep 3610115 = 5415173) B5415173
theorem B5412365 : Blo 1124630 5412365 := bstep (se 3 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 5412365 = 2029637) B2029637
theorem B18257521 : Blo 1124630 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B5772977 : Blo 1124630 5772977 := bstep (se 2 (by rfl) ⟨2164866, by rfl⟩ : syracuseStep 5772977 = 4329733) B4329733
theorem B15406861 : Blo 1124630 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B9639749 : Blo 1124630 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B3807053 : Blo 1124630 3807053 := bstep (se 3 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 3807053 = 1427645) B1427645
theorem B3807107 : Blo 1124630 3807107 := bstep (se 1 (by rfl) ⟨2855330, by rfl⟩ : syracuseStep 3807107 = 5710661) B5710661
theorem B7706501 : Blo 1124630 7706501 := bstep (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) B1444969
theorem B2136145 : Blo 1124630 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B3807377 : Blo 1124630 3807377 := bstep (se 2 (by rfl) ⟨1427766, by rfl⟩ : syracuseStep 3807377 = 2855533) B2855533
theorem B2136547 : Blo 1124630 2136547 := bstep (se 1 (by rfl) ⟨1602410, by rfl⟩ : syracuseStep 2136547 = 3204821) B3204821
theorem B2136593 : Blo 1124630 2136593 := bstep (se 2 (by rfl) ⟨801222, by rfl⟩ : syracuseStep 2136593 = 1602445) B1602445
theorem B3807917 : Blo 1124630 3807917 := bstep (se 3 (by rfl) ⟨713984, by rfl⟩ : syracuseStep 3807917 = 1427969) B1427969
theorem B3807971 : Blo 1124630 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B2136881 : Blo 1124630 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B3808241 : Blo 1124630 3808241 := bstep (se 2 (by rfl) ⟨1428090, by rfl⟩ : syracuseStep 3808241 = 2856181) B2856181
theorem B3611729 : Blo 1124630 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B1285219 : Blo 1124630 1285219 := bstep (se 1 (by rfl) ⟨963914, by rfl⟩ : syracuseStep 1285219 = 1927829) B1927829
theorem B5709041 : Blo 1124630 5709041 := bstep (se 2 (by rfl) ⟨2140890, by rfl⟩ : syracuseStep 5709041 = 4281781) B4281781
theorem B2530673 : Blo 1124630 2530673 := bstep (se 2 (by rfl) ⟨949002, by rfl⟩ : syracuseStep 2530673 = 1898005) B1898005
theorem B2530691 : Blo 1124630 2530691 := bstep (se 1 (by rfl) ⟨1898018, by rfl⟩ : syracuseStep 2530691 = 3796037) B3796037
theorem B2137603 : Blo 1124630 2137603 := bstep (se 1 (by rfl) ⟨1603202, by rfl⟩ : syracuseStep 2137603 = 3206405) B3206405
theorem B3808781 : Blo 1124630 3808781 := bstep (se 3 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 3808781 = 1428293) B1428293
theorem B3808835 : Blo 1124630 3808835 := bstep (se 1 (by rfl) ⟨2856626, by rfl⟩ : syracuseStep 3808835 = 5713253) B5713253
theorem B2530961 : Blo 1124630 2530961 := bstep (se 2 (by rfl) ⟨949110, by rfl⟩ : syracuseStep 2530961 = 1898221) B1898221
theorem B2530979 : Blo 1124630 2530979 := bstep (se 1 (by rfl) ⟨1898234, by rfl⟩ : syracuseStep 2530979 = 3796469) B3796469
theorem B3809105 : Blo 1124630 3809105 := bstep (se 2 (by rfl) ⟨1428414, by rfl⟩ : syracuseStep 3809105 = 2856829) B2856829
theorem B2531249 : Blo 1124630 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B2531267 : Blo 1124630 2531267 := bstep (se 1 (by rfl) ⟨1898450, by rfl⟩ : syracuseStep 2531267 = 3796901) B3796901
theorem B2138051 : Blo 1124630 2138051 := bstep (se 1 (by rfl) ⟨1603538, by rfl⟩ : syracuseStep 2138051 = 3207077) B3207077
theorem B2531537 : Blo 1124630 2531537 := bstep (se 2 (by rfl) ⟨949326, by rfl⟩ : syracuseStep 2531537 = 1898653) B1898653
theorem B2531555 : Blo 1124630 2531555 := bstep (se 1 (by rfl) ⟨1898666, by rfl⟩ : syracuseStep 2531555 = 3797333) B3797333
theorem B2138339 : Blo 1124630 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B4563377 : Blo 1124630 4563377 := bstep (se 2 (by rfl) ⟨1711266, by rfl⟩ : syracuseStep 4563377 = 3422533) B3422533
theorem B2531825 : Blo 1124630 2531825 := bstep (se 2 (by rfl) ⟨949434, by rfl⟩ : syracuseStep 2531825 = 1898869) B1898869
theorem B2531843 : Blo 1124630 2531843 := bstep (se 1 (by rfl) ⟨1898882, by rfl⟩ : syracuseStep 2531843 = 3797765) B3797765
theorem B1352227 : Blo 1124630 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B4563569 : Blo 1124630 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B2892401 : Blo 1124630 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B5710499 : Blo 1124630 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B1352371 : Blo 1124630 1352371 := bstep (se 1 (by rfl) ⟨1014278, by rfl⟩ : syracuseStep 1352371 = 2028557) B2028557
theorem B2532113 : Blo 1124630 2532113 := bstep (se 2 (by rfl) ⟨949542, by rfl⟩ : syracuseStep 2532113 = 1899085) B1899085
theorem B2532131 : Blo 1124630 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1712945 : Blo 1124630 1712945 := bstep (se 2 (by rfl) ⟨642354, by rfl⟩ : syracuseStep 1712945 = 1284709) B1284709
theorem B2532401 : Blo 1124630 2532401 := bstep (se 2 (by rfl) ⟨949650, by rfl⟩ : syracuseStep 2532401 = 1899301) B1899301
theorem B2532419 : Blo 1124630 2532419 := bstep (se 1 (by rfl) ⟨1899314, by rfl⟩ : syracuseStep 2532419 = 3798629) B3798629
theorem B3613805 : Blo 1124630 3613805 := bstep (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) B1355177
theorem B2139281 : Blo 1124630 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B8561861 : Blo 1124630 8561861 := bstep (se 4 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 8561861 = 1605349) B1605349
theorem B2565329 : Blo 1124630 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B2532689 : Blo 1124630 2532689 := bstep (se 2 (by rfl) ⟨949758, by rfl⟩ : syracuseStep 2532689 = 1899517) B1899517
theorem B2532707 : Blo 1124630 2532707 := bstep (se 1 (by rfl) ⟨1899530, by rfl⟩ : syracuseStep 2532707 = 3799061) B3799061
theorem B5711309 : Blo 1124630 5711309 := bstep (se 3 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 5711309 = 2141741) B2141741
theorem B2532977 : Blo 1124630 2532977 := bstep (se 2 (by rfl) ⟨949866, by rfl⟩ : syracuseStep 2532977 = 1899733) B1899733
theorem B2532995 : Blo 1124630 2532995 := bstep (se 1 (by rfl) ⟨1899746, by rfl⟩ : syracuseStep 2532995 = 3799493) B3799493
theorem B2533265 : Blo 1124630 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B2533283 : Blo 1124630 2533283 := bstep (se 1 (by rfl) ⟨1899962, by rfl⟩ : syracuseStep 2533283 = 3799925) B3799925
theorem B3614701 : Blo 1124630 3614701 := bstep (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) B1355513
theorem B7219205 : Blo 1124630 7219205 := bstep (se 4 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 7219205 = 1353601) B1353601
theorem B2140177 : Blo 1124630 2140177 := bstep (se 2 (by rfl) ⟨802566, by rfl⟩ : syracuseStep 2140177 = 1605133) B1605133
theorem B2533553 : Blo 1124630 2533553 := bstep (se 2 (by rfl) ⟨950082, by rfl⟩ : syracuseStep 2533553 = 1900165) B1900165
theorem B2140337 : Blo 1124630 2140337 := bstep (se 2 (by rfl) ⟨802626, by rfl⟩ : syracuseStep 2140337 = 1605253) B1605253
theorem B2533571 : Blo 1124630 2533571 := bstep (se 1 (by rfl) ⟨1900178, by rfl⟩ : syracuseStep 2533571 = 3800357) B3800357
theorem B1124643 : Blo 1124630 1124643 := bstep (se 1 (by rfl) ⟨843482, by rfl⟩ : syracuseStep 1124643 = 1686965) B1686965
theorem B1124659 : Blo 1124630 1124659 := bstep (se 1 (by rfl) ⟨843494, by rfl⟩ : syracuseStep 1124659 = 1686989) B1686989
theorem B1124675 : Blo 1124630 1124675 := bstep (se 1 (by rfl) ⟨843506, by rfl⟩ : syracuseStep 1124675 = 1687013) B1687013
theorem B1124691 : Blo 1124630 1124691 := bstep (se 1 (by rfl) ⟨843518, by rfl⟩ : syracuseStep 1124691 = 1687037) B1687037
theorem B1124707 : Blo 1124630 1124707 := bstep (se 1 (by rfl) ⟨843530, by rfl⟩ : syracuseStep 1124707 = 1687061) B1687061
theorem B2402659 : Blo 1124630 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B1124723 : Blo 1124630 1124723 := bstep (se 1 (by rfl) ⟨843542, by rfl⟩ : syracuseStep 1124723 = 1687085) B1687085
theorem B1124739 : Blo 1124630 1124739 := bstep (se 1 (by rfl) ⟨843554, by rfl⟩ : syracuseStep 1124739 = 1687109) B1687109
theorem B1124755 : Blo 1124630 1124755 := bstep (se 1 (by rfl) ⟨843566, by rfl⟩ : syracuseStep 1124755 = 1687133) B1687133
theorem B1124771 : Blo 1124630 1124771 := bstep (se 1 (by rfl) ⟨843578, by rfl⟩ : syracuseStep 1124771 = 1687157) B1687157
theorem B1124787 : Blo 1124630 1124787 := bstep (se 1 (by rfl) ⟨843590, by rfl⟩ : syracuseStep 1124787 = 1687181) B1687181
theorem B1354163 : Blo 1124630 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B1124803 : Blo 1124630 1124803 := bstep (se 1 (by rfl) ⟨843602, by rfl⟩ : syracuseStep 1124803 = 1687205) B1687205
theorem B2533841 : Blo 1124630 2533841 := bstep (se 2 (by rfl) ⟨950190, by rfl⟩ : syracuseStep 2533841 = 1900381) B1900381
theorem B1124819 : Blo 1124630 1124819 := bstep (se 1 (by rfl) ⟨843614, by rfl⟩ : syracuseStep 1124819 = 1687229) B1687229
theorem B1124835 : Blo 1124630 1124835 := bstep (se 1 (by rfl) ⟨843626, by rfl⟩ : syracuseStep 1124835 = 1687253) B1687253
theorem B2533859 : Blo 1124630 2533859 := bstep (se 1 (by rfl) ⟨1900394, by rfl⟩ : syracuseStep 2533859 = 3800789) B3800789
theorem B1124851 : Blo 1124630 1124851 := bstep (se 1 (by rfl) ⟨843638, by rfl⟩ : syracuseStep 1124851 = 1687277) B1687277
theorem B1124867 : Blo 1124630 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B1124883 : Blo 1124630 1124883 := bstep (se 1 (by rfl) ⟨843662, by rfl⟩ : syracuseStep 1124883 = 1687325) B1687325
theorem B1124899 : Blo 1124630 1124899 := bstep (se 1 (by rfl) ⟨843674, by rfl⟩ : syracuseStep 1124899 = 1687349) B1687349
theorem B1124915 : Blo 1124630 1124915 := bstep (se 1 (by rfl) ⟨843686, by rfl⟩ : syracuseStep 1124915 = 1687373) B1687373
theorem B1124931 : Blo 1124630 1124931 := bstep (se 1 (by rfl) ⟨843698, by rfl⟩ : syracuseStep 1124931 = 1687397) B1687397
theorem B2140739 : Blo 1124630 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B12823109 : Blo 1124630 12823109 := bstep (se 4 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 12823109 = 2404333) B2404333
theorem B1124947 : Blo 1124630 1124947 := bstep (se 1 (by rfl) ⟨843710, by rfl⟩ : syracuseStep 1124947 = 1687421) B1687421
theorem B1124963 : Blo 1124630 1124963 := bstep (se 1 (by rfl) ⟨843722, by rfl⟩ : syracuseStep 1124963 = 1687445) B1687445
theorem B1124979 : Blo 1124630 1124979 := bstep (se 1 (by rfl) ⟨843734, by rfl⟩ : syracuseStep 1124979 = 1687469) B1687469
theorem B1124995 : Blo 1124630 1124995 := bstep (se 1 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 1124995 = 1687493) B1687493
theorem B1125011 : Blo 1124630 1125011 := bstep (se 1 (by rfl) ⟨843758, by rfl⟩ : syracuseStep 1125011 = 1687517) B1687517
theorem B1125027 : Blo 1124630 1125027 := bstep (se 1 (by rfl) ⟨843770, by rfl⟩ : syracuseStep 1125027 = 1687541) B1687541
theorem B1125043 : Blo 1124630 1125043 := bstep (se 1 (by rfl) ⟨843782, by rfl⟩ : syracuseStep 1125043 = 1687565) B1687565
theorem B1125059 : Blo 1124630 1125059 := bstep (se 1 (by rfl) ⟨843794, by rfl⟩ : syracuseStep 1125059 = 1687589) B1687589
theorem B1125075 : Blo 1124630 1125075 := bstep (se 1 (by rfl) ⟨843806, by rfl⟩ : syracuseStep 1125075 = 1687613) B1687613
theorem B1125091 : Blo 1124630 1125091 := bstep (se 1 (by rfl) ⟨843818, by rfl⟩ : syracuseStep 1125091 = 1687637) B1687637
theorem B2534129 : Blo 1124630 2534129 := bstep (se 2 (by rfl) ⟨950298, by rfl⟩ : syracuseStep 2534129 = 1900597) B1900597
theorem B1125107 : Blo 1124630 1125107 := bstep (se 1 (by rfl) ⟨843830, by rfl⟩ : syracuseStep 1125107 = 1687661) B1687661
theorem B1125123 : Blo 1124630 1125123 := bstep (se 1 (by rfl) ⟨843842, by rfl⟩ : syracuseStep 1125123 = 1687685) B1687685
theorem B2534147 : Blo 1124630 2534147 := bstep (se 1 (by rfl) ⟨1900610, by rfl⟩ : syracuseStep 2534147 = 3801221) B3801221
theorem B1125139 : Blo 1124630 1125139 := bstep (se 1 (by rfl) ⟨843854, by rfl⟩ : syracuseStep 1125139 = 1687709) B1687709
theorem B1125155 : Blo 1124630 1125155 := bstep (se 1 (by rfl) ⟨843866, by rfl⟩ : syracuseStep 1125155 = 1687733) B1687733
theorem B1157923 : Blo 1124630 1157923 := bstep (se 1 (by rfl) ⟨868442, by rfl⟩ : syracuseStep 1157923 = 1736885) B1736885
theorem B2403121 : Blo 1124630 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B1125171 : Blo 1124630 1125171 := bstep (se 1 (by rfl) ⟨843878, by rfl⟩ : syracuseStep 1125171 = 1687757) B1687757
theorem B1125187 : Blo 1124630 1125187 := bstep (se 1 (by rfl) ⟨843890, by rfl⟩ : syracuseStep 1125187 = 1687781) B1687781
theorem B1125203 : Blo 1124630 1125203 := bstep (se 1 (by rfl) ⟨843902, by rfl⟩ : syracuseStep 1125203 = 1687805) B1687805
theorem B1125219 : Blo 1124630 1125219 := bstep (se 1 (by rfl) ⟨843914, by rfl⟩ : syracuseStep 1125219 = 1687829) B1687829
theorem B1125235 : Blo 1124630 1125235 := bstep (se 1 (by rfl) ⟨843926, by rfl⟩ : syracuseStep 1125235 = 1687853) B1687853
theorem B1125251 : Blo 1124630 1125251 := bstep (se 1 (by rfl) ⟨843938, by rfl⟩ : syracuseStep 1125251 = 1687877) B1687877
theorem B1125267 : Blo 1124630 1125267 := bstep (se 1 (by rfl) ⟨843950, by rfl⟩ : syracuseStep 1125267 = 1687901) B1687901
theorem B1125283 : Blo 1124630 1125283 := bstep (se 1 (by rfl) ⟨843962, by rfl⟩ : syracuseStep 1125283 = 1687925) B1687925
theorem B1125299 : Blo 1124630 1125299 := bstep (se 1 (by rfl) ⟨843974, by rfl⟩ : syracuseStep 1125299 = 1687949) B1687949
theorem B1125315 : Blo 1124630 1125315 := bstep (se 1 (by rfl) ⟨843986, by rfl⟩ : syracuseStep 1125315 = 1687973) B1687973
theorem B1125331 : Blo 1124630 1125331 := bstep (se 1 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 1125331 = 1687997) B1687997
theorem B4271075 : Blo 1124630 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B1125347 : Blo 1124630 1125347 := bstep (se 1 (by rfl) ⟨844010, by rfl⟩ : syracuseStep 1125347 = 1688021) B1688021
theorem B4271089 : Blo 1124630 4271089 := bstep (se 2 (by rfl) ⟨1601658, by rfl⟩ : syracuseStep 4271089 = 3203317) B3203317
theorem B1125363 : Blo 1124630 1125363 := bstep (se 1 (by rfl) ⟨844022, by rfl⟩ : syracuseStep 1125363 = 1688045) B1688045
theorem B1125379 : Blo 1124630 1125379 := bstep (se 1 (by rfl) ⟨844034, by rfl⟩ : syracuseStep 1125379 = 1688069) B1688069
theorem B2534417 : Blo 1124630 2534417 := bstep (se 2 (by rfl) ⟨950406, by rfl⟩ : syracuseStep 2534417 = 1900813) B1900813
theorem B1125395 : Blo 1124630 1125395 := bstep (se 1 (by rfl) ⟨844046, by rfl⟩ : syracuseStep 1125395 = 1688093) B1688093
theorem B1125411 : Blo 1124630 1125411 := bstep (se 1 (by rfl) ⟨844058, by rfl⟩ : syracuseStep 1125411 = 1688117) B1688117
theorem B2534435 : Blo 1124630 2534435 := bstep (se 1 (by rfl) ⟨1900826, by rfl⟩ : syracuseStep 2534435 = 3801653) B3801653
theorem B1125427 : Blo 1124630 1125427 := bstep (se 1 (by rfl) ⟨844070, by rfl⟩ : syracuseStep 1125427 = 1688141) B1688141
theorem B1125443 : Blo 1124630 1125443 := bstep (se 1 (by rfl) ⟨844082, by rfl⟩ : syracuseStep 1125443 = 1688165) B1688165
theorem B1125459 : Blo 1124630 1125459 := bstep (se 1 (by rfl) ⟨844094, by rfl⟩ : syracuseStep 1125459 = 1688189) B1688189
theorem B1125475 : Blo 1124630 1125475 := bstep (se 1 (by rfl) ⟨844106, by rfl⟩ : syracuseStep 1125475 = 1688213) B1688213
theorem B1125491 : Blo 1124630 1125491 := bstep (se 1 (by rfl) ⟨844118, by rfl⟩ : syracuseStep 1125491 = 1688237) B1688237
theorem B1125507 : Blo 1124630 1125507 := bstep (se 1 (by rfl) ⟨844130, by rfl⟩ : syracuseStep 1125507 = 1688261) B1688261
theorem B1125523 : Blo 1124630 1125523 := bstep (se 1 (by rfl) ⟨844142, by rfl⟩ : syracuseStep 1125523 = 1688285) B1688285
theorem B1125539 : Blo 1124630 1125539 := bstep (se 1 (by rfl) ⟨844154, by rfl⟩ : syracuseStep 1125539 = 1688309) B1688309
theorem B1715377 : Blo 1124630 1715377 := bstep (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) B1286533
theorem B1125555 : Blo 1124630 1125555 := bstep (se 1 (by rfl) ⟨844166, by rfl⟩ : syracuseStep 1125555 = 1688333) B1688333
theorem B1125571 : Blo 1124630 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B1125587 : Blo 1124630 1125587 := bstep (se 1 (by rfl) ⟨844190, by rfl⟩ : syracuseStep 1125587 = 1688381) B1688381
theorem B1125603 : Blo 1124630 1125603 := bstep (se 1 (by rfl) ⟨844202, by rfl⟩ : syracuseStep 1125603 = 1688405) B1688405
theorem B1125619 : Blo 1124630 1125619 := bstep (se 1 (by rfl) ⟨844214, by rfl⟩ : syracuseStep 1125619 = 1688429) B1688429
theorem B1125635 : Blo 1124630 1125635 := bstep (se 1 (by rfl) ⟨844226, by rfl⟩ : syracuseStep 1125635 = 1688453) B1688453
theorem B1125651 : Blo 1124630 1125651 := bstep (se 1 (by rfl) ⟨844238, by rfl⟩ : syracuseStep 1125651 = 1688477) B1688477
theorem B1125667 : Blo 1124630 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B2534705 : Blo 1124630 2534705 := bstep (se 2 (by rfl) ⟨950514, by rfl⟩ : syracuseStep 2534705 = 1901029) B1901029
theorem B1125683 : Blo 1124630 1125683 := bstep (se 1 (by rfl) ⟨844262, by rfl⟩ : syracuseStep 1125683 = 1688525) B1688525
theorem B1125699 : Blo 1124630 1125699 := bstep (se 1 (by rfl) ⟨844274, by rfl⟩ : syracuseStep 1125699 = 1688549) B1688549
theorem B2534723 : Blo 1124630 2534723 := bstep (se 1 (by rfl) ⟨1901042, by rfl⟩ : syracuseStep 2534723 = 3802085) B3802085
theorem B1125715 : Blo 1124630 1125715 := bstep (se 1 (by rfl) ⟨844286, by rfl⟩ : syracuseStep 1125715 = 1688573) B1688573
theorem B1125731 : Blo 1124630 1125731 := bstep (se 1 (by rfl) ⟨844298, by rfl⟩ : syracuseStep 1125731 = 1688597) B1688597
theorem B1125747 : Blo 1124630 1125747 := bstep (se 1 (by rfl) ⟨844310, by rfl⟩ : syracuseStep 1125747 = 1688621) B1688621
theorem B1125763 : Blo 1124630 1125763 := bstep (se 1 (by rfl) ⟨844322, by rfl⟩ : syracuseStep 1125763 = 1688645) B1688645
theorem B1125779 : Blo 1124630 1125779 := bstep (se 1 (by rfl) ⟨844334, by rfl⟩ : syracuseStep 1125779 = 1688669) B1688669
theorem B1125795 : Blo 1124630 1125795 := bstep (se 1 (by rfl) ⟨844346, by rfl⟩ : syracuseStep 1125795 = 1688693) B1688693
theorem B1125811 : Blo 1124630 1125811 := bstep (se 1 (by rfl) ⟨844358, by rfl⟩ : syracuseStep 1125811 = 1688717) B1688717
theorem B1125827 : Blo 1124630 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B2141635 : Blo 1124630 2141635 := bstep (se 1 (by rfl) ⟨1606226, by rfl⟩ : syracuseStep 2141635 = 3212453) B3212453
theorem B1125843 : Blo 1124630 1125843 := bstep (se 1 (by rfl) ⟨844382, by rfl⟩ : syracuseStep 1125843 = 1688765) B1688765
theorem B1125859 : Blo 1124630 1125859 := bstep (se 1 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 1125859 = 1688789) B1688789
theorem B1125875 : Blo 1124630 1125875 := bstep (se 1 (by rfl) ⟨844406, by rfl⟩ : syracuseStep 1125875 = 1688813) B1688813
theorem B1125891 : Blo 1124630 1125891 := bstep (se 1 (by rfl) ⟨844418, by rfl⟩ : syracuseStep 1125891 = 1688837) B1688837
theorem B1125907 : Blo 1124630 1125907 := bstep (se 1 (by rfl) ⟨844430, by rfl⟩ : syracuseStep 1125907 = 1688861) B1688861
theorem B1125923 : Blo 1124630 1125923 := bstep (se 1 (by rfl) ⟨844442, by rfl⟩ : syracuseStep 1125923 = 1688885) B1688885
theorem B1125939 : Blo 1124630 1125939 := bstep (se 1 (by rfl) ⟨844454, by rfl⟩ : syracuseStep 1125939 = 1688909) B1688909
theorem B1125955 : Blo 1124630 1125955 := bstep (se 1 (by rfl) ⟨844466, by rfl⟩ : syracuseStep 1125955 = 1688933) B1688933
theorem B2534993 : Blo 1124630 2534993 := bstep (se 2 (by rfl) ⟨950622, by rfl⟩ : syracuseStep 2534993 = 1901245) B1901245
theorem B1125971 : Blo 1124630 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B1125987 : Blo 1124630 1125987 := bstep (se 1 (by rfl) ⟨844490, by rfl⟩ : syracuseStep 1125987 = 1688981) B1688981
theorem B2535011 : Blo 1124630 2535011 := bstep (se 1 (by rfl) ⟨1901258, by rfl⟩ : syracuseStep 2535011 = 3802517) B3802517
theorem B2141795 : Blo 1124630 2141795 := bstep (se 1 (by rfl) ⟨1606346, by rfl⟩ : syracuseStep 2141795 = 3212693) B3212693
theorem B1126003 : Blo 1124630 1126003 := bstep (se 1 (by rfl) ⟨844502, by rfl⟩ : syracuseStep 1126003 = 1689005) B1689005
theorem B1126019 : Blo 1124630 1126019 := bstep (se 1 (by rfl) ⟨844514, by rfl⟩ : syracuseStep 1126019 = 1689029) B1689029
theorem B1126035 : Blo 1124630 1126035 := bstep (se 1 (by rfl) ⟨844526, by rfl⟩ : syracuseStep 1126035 = 1689053) B1689053
theorem B1126051 : Blo 1124630 1126051 := bstep (se 1 (by rfl) ⟨844538, by rfl⟩ : syracuseStep 1126051 = 1689077) B1689077
theorem B1126067 : Blo 1124630 1126067 := bstep (se 1 (by rfl) ⟨844550, by rfl⟩ : syracuseStep 1126067 = 1689101) B1689101
theorem B1814195 : Blo 1124630 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B1126083 : Blo 1124630 1126083 := bstep (se 1 (by rfl) ⟨844562, by rfl⟩ : syracuseStep 1126083 = 1689125) B1689125
theorem B1126099 : Blo 1124630 1126099 := bstep (se 1 (by rfl) ⟨844574, by rfl⟩ : syracuseStep 1126099 = 1689149) B1689149
theorem B1126115 : Blo 1124630 1126115 := bstep (se 1 (by rfl) ⟨844586, by rfl⟩ : syracuseStep 1126115 = 1689173) B1689173
theorem B1126131 : Blo 1124630 1126131 := bstep (se 1 (by rfl) ⟨844598, by rfl⟩ : syracuseStep 1126131 = 1689197) B1689197
theorem B1126147 : Blo 1124630 1126147 := bstep (se 1 (by rfl) ⟨844610, by rfl⟩ : syracuseStep 1126147 = 1689221) B1689221
theorem B1126163 : Blo 1124630 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B1126179 : Blo 1124630 1126179 := bstep (se 1 (by rfl) ⟨844634, by rfl⟩ : syracuseStep 1126179 = 1689269) B1689269
theorem B1126195 : Blo 1124630 1126195 := bstep (se 1 (by rfl) ⟨844646, by rfl⟩ : syracuseStep 1126195 = 1689293) B1689293
theorem B2404163 : Blo 1124630 2404163 := bstep (se 1 (by rfl) ⟨1803122, by rfl⟩ : syracuseStep 2404163 = 3606245) B3606245
theorem B1126211 : Blo 1124630 1126211 := bstep (se 1 (by rfl) ⟨844658, by rfl⟩ : syracuseStep 1126211 = 1689317) B1689317
theorem B1126227 : Blo 1124630 1126227 := bstep (se 1 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 1126227 = 1689341) B1689341
theorem B1126243 : Blo 1124630 1126243 := bstep (se 1 (by rfl) ⟨844682, by rfl⟩ : syracuseStep 1126243 = 1689365) B1689365
theorem B10170211 : Blo 1124630 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B2535281 : Blo 1124630 2535281 := bstep (se 2 (by rfl) ⟨950730, by rfl⟩ : syracuseStep 2535281 = 1901461) B1901461
theorem B1126259 : Blo 1124630 1126259 := bstep (se 1 (by rfl) ⟨844694, by rfl⟩ : syracuseStep 1126259 = 1689389) B1689389
theorem B1126275 : Blo 1124630 1126275 := bstep (se 1 (by rfl) ⟨844706, by rfl⟩ : syracuseStep 1126275 = 1689413) B1689413
theorem B2535299 : Blo 1124630 2535299 := bstep (se 1 (by rfl) ⟨1901474, by rfl⟩ : syracuseStep 2535299 = 3802949) B3802949
theorem B1126291 : Blo 1124630 1126291 := bstep (se 1 (by rfl) ⟨844718, by rfl⟩ : syracuseStep 1126291 = 1689437) B1689437
theorem B1126307 : Blo 1124630 1126307 := bstep (se 1 (by rfl) ⟨844730, by rfl⟩ : syracuseStep 1126307 = 1689461) B1689461
theorem B1126323 : Blo 1124630 1126323 := bstep (se 1 (by rfl) ⟨844742, by rfl⟩ : syracuseStep 1126323 = 1689485) B1689485
theorem B1126339 : Blo 1124630 1126339 := bstep (se 1 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 1126339 = 1689509) B1689509
theorem B1126355 : Blo 1124630 1126355 := bstep (se 1 (by rfl) ⟨844766, by rfl⟩ : syracuseStep 1126355 = 1689533) B1689533
theorem B1126371 : Blo 1124630 1126371 := bstep (se 1 (by rfl) ⟨844778, by rfl⟩ : syracuseStep 1126371 = 1689557) B1689557
theorem B1126387 : Blo 1124630 1126387 := bstep (se 1 (by rfl) ⟨844790, by rfl⟩ : syracuseStep 1126387 = 1689581) B1689581
theorem B1126403 : Blo 1124630 1126403 := bstep (se 1 (by rfl) ⟨844802, by rfl⟩ : syracuseStep 1126403 = 1689605) B1689605
theorem B1126419 : Blo 1124630 1126419 := bstep (se 1 (by rfl) ⟨844814, by rfl⟩ : syracuseStep 1126419 = 1689629) B1689629
theorem B1126435 : Blo 1124630 1126435 := bstep (se 1 (by rfl) ⟨844826, by rfl⟩ : syracuseStep 1126435 = 1689653) B1689653
theorem B1126451 : Blo 1124630 1126451 := bstep (se 1 (by rfl) ⟨844838, by rfl⟩ : syracuseStep 1126451 = 1689677) B1689677
theorem B1126467 : Blo 1124630 1126467 := bstep (se 1 (by rfl) ⟨844850, by rfl⟩ : syracuseStep 1126467 = 1689701) B1689701
theorem B1126483 : Blo 1124630 1126483 := bstep (se 1 (by rfl) ⟨844862, by rfl⟩ : syracuseStep 1126483 = 1689725) B1689725
theorem B1126499 : Blo 1124630 1126499 := bstep (se 1 (by rfl) ⟨844874, by rfl⟩ : syracuseStep 1126499 = 1689749) B1689749
theorem B1126515 : Blo 1124630 1126515 := bstep (se 1 (by rfl) ⟨844886, by rfl⟩ : syracuseStep 1126515 = 1689773) B1689773
theorem B1126531 : Blo 1124630 1126531 := bstep (se 1 (by rfl) ⟨844898, by rfl⟩ : syracuseStep 1126531 = 1689797) B1689797
theorem B2535569 : Blo 1124630 2535569 := bstep (se 2 (by rfl) ⟨950838, by rfl⟩ : syracuseStep 2535569 = 1901677) B1901677
theorem B1126547 : Blo 1124630 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B1126563 : Blo 1124630 1126563 := bstep (se 1 (by rfl) ⟨844922, by rfl⟩ : syracuseStep 1126563 = 1689845) B1689845
theorem B2535587 : Blo 1124630 2535587 := bstep (se 1 (by rfl) ⟨1901690, by rfl⟩ : syracuseStep 2535587 = 3803381) B3803381
theorem B1126579 : Blo 1124630 1126579 := bstep (se 1 (by rfl) ⟨844934, by rfl⟩ : syracuseStep 1126579 = 1689869) B1689869
theorem B1126595 : Blo 1124630 1126595 := bstep (se 1 (by rfl) ⟨844946, by rfl⟩ : syracuseStep 1126595 = 1689893) B1689893
theorem B1126611 : Blo 1124630 1126611 := bstep (se 1 (by rfl) ⟨844958, by rfl⟩ : syracuseStep 1126611 = 1689917) B1689917
theorem B1126627 : Blo 1124630 1126627 := bstep (se 1 (by rfl) ⟨844970, by rfl⟩ : syracuseStep 1126627 = 1689941) B1689941
theorem B1126643 : Blo 1124630 1126643 := bstep (se 1 (by rfl) ⟨844982, by rfl⟩ : syracuseStep 1126643 = 1689965) B1689965
theorem B1126659 : Blo 1124630 1126659 := bstep (se 1 (by rfl) ⟨844994, by rfl⟩ : syracuseStep 1126659 = 1689989) B1689989
theorem B1126675 : Blo 1124630 1126675 := bstep (se 1 (by rfl) ⟨845006, by rfl⟩ : syracuseStep 1126675 = 1690013) B1690013
theorem B1126691 : Blo 1124630 1126691 := bstep (se 1 (by rfl) ⟨845018, by rfl⟩ : syracuseStep 1126691 = 1690037) B1690037
theorem B1126707 : Blo 1124630 1126707 := bstep (se 1 (by rfl) ⟨845030, by rfl⟩ : syracuseStep 1126707 = 1690061) B1690061
theorem B2404675 : Blo 1124630 2404675 := bstep (se 1 (by rfl) ⟨1803506, by rfl⟩ : syracuseStep 2404675 = 3607013) B3607013
theorem B1126723 : Blo 1124630 1126723 := bstep (se 1 (by rfl) ⟨845042, by rfl⟩ : syracuseStep 1126723 = 1690085) B1690085
theorem B1126739 : Blo 1124630 1126739 := bstep (se 1 (by rfl) ⟨845054, by rfl⟩ : syracuseStep 1126739 = 1690109) B1690109
theorem B1126755 : Blo 1124630 1126755 := bstep (se 1 (by rfl) ⟨845066, by rfl⟩ : syracuseStep 1126755 = 1690133) B1690133
theorem B1126771 : Blo 1124630 1126771 := bstep (se 1 (by rfl) ⟨845078, by rfl⟩ : syracuseStep 1126771 = 1690157) B1690157
theorem B1126787 : Blo 1124630 1126787 := bstep (se 1 (by rfl) ⟨845090, by rfl⟩ : syracuseStep 1126787 = 1690181) B1690181
theorem B1126803 : Blo 1124630 1126803 := bstep (se 1 (by rfl) ⟨845102, by rfl⟩ : syracuseStep 1126803 = 1690205) B1690205
theorem B4272547 : Blo 1124630 4272547 := bstep (se 1 (by rfl) ⟨3204410, by rfl⟩ : syracuseStep 4272547 = 6408821) B6408821
theorem B1126819 : Blo 1124630 1126819 := bstep (se 1 (by rfl) ⟨845114, by rfl⟩ : syracuseStep 1126819 = 1690229) B1690229
theorem B2535857 : Blo 1124630 2535857 := bstep (se 2 (by rfl) ⟨950946, by rfl⟩ : syracuseStep 2535857 = 1901893) B1901893
theorem B1126835 : Blo 1124630 1126835 := bstep (se 1 (by rfl) ⟨845126, by rfl⟩ : syracuseStep 1126835 = 1690253) B1690253
theorem B1126851 : Blo 1124630 1126851 := bstep (se 1 (by rfl) ⟨845138, by rfl⟩ : syracuseStep 1126851 = 1690277) B1690277
theorem B2535875 : Blo 1124630 2535875 := bstep (se 1 (by rfl) ⟨1901906, by rfl⟩ : syracuseStep 2535875 = 3803813) B3803813
theorem B1126867 : Blo 1124630 1126867 := bstep (se 1 (by rfl) ⟨845150, by rfl⟩ : syracuseStep 1126867 = 1690301) B1690301
theorem B1126883 : Blo 1124630 1126883 := bstep (se 1 (by rfl) ⟨845162, by rfl⟩ : syracuseStep 1126883 = 1690325) B1690325
theorem B8794595 : Blo 1124630 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B1126899 : Blo 1124630 1126899 := bstep (se 1 (by rfl) ⟨845174, by rfl⟩ : syracuseStep 1126899 = 1690349) B1690349
theorem B1126915 : Blo 1124630 1126915 := bstep (se 1 (by rfl) ⟨845186, by rfl⟩ : syracuseStep 1126915 = 1690373) B1690373
theorem B1126931 : Blo 1124630 1126931 := bstep (se 1 (by rfl) ⟨845198, by rfl⟩ : syracuseStep 1126931 = 1690397) B1690397
theorem B1126947 : Blo 1124630 1126947 := bstep (se 1 (by rfl) ⟨845210, by rfl⟩ : syracuseStep 1126947 = 1690421) B1690421
theorem B1126963 : Blo 1124630 1126963 := bstep (se 1 (by rfl) ⟨845222, by rfl⟩ : syracuseStep 1126963 = 1690445) B1690445
theorem B1126979 : Blo 1124630 1126979 := bstep (se 1 (by rfl) ⟨845234, by rfl⟩ : syracuseStep 1126979 = 1690469) B1690469
theorem B1126995 : Blo 1124630 1126995 := bstep (se 1 (by rfl) ⟨845246, by rfl⟩ : syracuseStep 1126995 = 1690493) B1690493
theorem B1389155 : Blo 1124630 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B1127011 : Blo 1124630 1127011 := bstep (se 1 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 1127011 = 1690517) B1690517
theorem B28881521 : Blo 1124630 28881521 := bstep (se 2 (by rfl) ⟨10830570, by rfl⟩ : syracuseStep 28881521 = 21661141) B21661141
theorem B1127027 : Blo 1124630 1127027 := bstep (se 1 (by rfl) ⟨845270, by rfl⟩ : syracuseStep 1127027 = 1690541) B1690541
theorem B1127043 : Blo 1124630 1127043 := bstep (se 1 (by rfl) ⟨845282, by rfl⟩ : syracuseStep 1127043 = 1690565) B1690565
theorem B1127059 : Blo 1124630 1127059 := bstep (se 1 (by rfl) ⟨845294, by rfl⟩ : syracuseStep 1127059 = 1690589) B1690589
theorem B1127075 : Blo 1124630 1127075 := bstep (se 1 (by rfl) ⟨845306, by rfl⟩ : syracuseStep 1127075 = 1690613) B1690613
theorem B1127091 : Blo 1124630 1127091 := bstep (se 1 (by rfl) ⟨845318, by rfl⟩ : syracuseStep 1127091 = 1690637) B1690637
theorem B1127107 : Blo 1124630 1127107 := bstep (se 1 (by rfl) ⟨845330, by rfl⟩ : syracuseStep 1127107 = 1690661) B1690661
theorem B2536145 : Blo 1124630 2536145 := bstep (se 2 (by rfl) ⟨951054, by rfl⟩ : syracuseStep 2536145 = 1902109) B1902109
theorem B1127123 : Blo 1124630 1127123 := bstep (se 1 (by rfl) ⟨845342, by rfl⟩ : syracuseStep 1127123 = 1690685) B1690685
theorem B1127139 : Blo 1124630 1127139 := bstep (se 1 (by rfl) ⟨845354, by rfl⟩ : syracuseStep 1127139 = 1690709) B1690709
theorem B2536163 : Blo 1124630 2536163 := bstep (se 1 (by rfl) ⟨1902122, by rfl⟩ : syracuseStep 2536163 = 3804245) B3804245
theorem B1127155 : Blo 1124630 1127155 := bstep (se 1 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 1127155 = 1690733) B1690733
theorem B1127171 : Blo 1124630 1127171 := bstep (se 1 (by rfl) ⟨845378, by rfl⟩ : syracuseStep 1127171 = 1690757) B1690757
theorem B1127187 : Blo 1124630 1127187 := bstep (se 1 (by rfl) ⟨845390, by rfl⟩ : syracuseStep 1127187 = 1690781) B1690781
theorem B1127203 : Blo 1124630 1127203 := bstep (se 1 (by rfl) ⟨845402, by rfl⟩ : syracuseStep 1127203 = 1690805) B1690805
theorem B1127219 : Blo 1124630 1127219 := bstep (se 1 (by rfl) ⟨845414, by rfl⟩ : syracuseStep 1127219 = 1690829) B1690829
theorem B1127235 : Blo 1124630 1127235 := bstep (se 1 (by rfl) ⟨845426, by rfl⟩ : syracuseStep 1127235 = 1690853) B1690853
theorem B1127251 : Blo 1124630 1127251 := bstep (se 1 (by rfl) ⟨845438, by rfl⟩ : syracuseStep 1127251 = 1690877) B1690877
theorem B1127267 : Blo 1124630 1127267 := bstep (se 1 (by rfl) ⟨845450, by rfl⟩ : syracuseStep 1127267 = 1690901) B1690901
theorem B1127283 : Blo 1124630 1127283 := bstep (se 1 (by rfl) ⟨845462, by rfl⟩ : syracuseStep 1127283 = 1690925) B1690925
theorem B1127299 : Blo 1124630 1127299 := bstep (se 1 (by rfl) ⟨845474, by rfl⟩ : syracuseStep 1127299 = 1690949) B1690949
theorem B1127315 : Blo 1124630 1127315 := bstep (se 1 (by rfl) ⟨845486, by rfl⟩ : syracuseStep 1127315 = 1690973) B1690973
theorem B1127331 : Blo 1124630 1127331 := bstep (se 1 (by rfl) ⟨845498, by rfl⟩ : syracuseStep 1127331 = 1690997) B1690997
theorem B1127347 : Blo 1124630 1127347 := bstep (se 1 (by rfl) ⟨845510, by rfl⟩ : syracuseStep 1127347 = 1691021) B1691021
theorem B1127363 : Blo 1124630 1127363 := bstep (se 1 (by rfl) ⟨845522, by rfl⟩ : syracuseStep 1127363 = 1691045) B1691045
theorem B1127379 : Blo 1124630 1127379 := bstep (se 1 (by rfl) ⟨845534, by rfl⟩ : syracuseStep 1127379 = 1691069) B1691069
theorem B1127395 : Blo 1124630 1127395 := bstep (se 1 (by rfl) ⟨845546, by rfl⟩ : syracuseStep 1127395 = 1691093) B1691093
theorem B2536433 : Blo 1124630 2536433 := bstep (se 2 (by rfl) ⟨951162, by rfl⟩ : syracuseStep 2536433 = 1902325) B1902325
theorem B1127411 : Blo 1124630 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B2536451 : Blo 1124630 2536451 := bstep (se 1 (by rfl) ⟨1902338, by rfl⟩ : syracuseStep 2536451 = 3804677) B3804677
theorem B1127427 : Blo 1124630 1127427 := bstep (se 1 (by rfl) ⟨845570, by rfl⟩ : syracuseStep 1127427 = 1691141) B1691141
theorem B2405393 : Blo 1124630 2405393 := bstep (se 2 (by rfl) ⟨902022, by rfl⟩ : syracuseStep 2405393 = 1804045) B1804045
theorem B1127443 : Blo 1124630 1127443 := bstep (se 1 (by rfl) ⟨845582, by rfl⟩ : syracuseStep 1127443 = 1691165) B1691165
theorem B1127459 : Blo 1124630 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B1127475 : Blo 1124630 1127475 := bstep (se 1 (by rfl) ⟨845606, by rfl⟩ : syracuseStep 1127475 = 1691213) B1691213
theorem B1127491 : Blo 1124630 1127491 := bstep (se 1 (by rfl) ⟨845618, by rfl⟩ : syracuseStep 1127491 = 1691237) B1691237
theorem B1127507 : Blo 1124630 1127507 := bstep (se 1 (by rfl) ⟨845630, by rfl⟩ : syracuseStep 1127507 = 1691261) B1691261
theorem B1127523 : Blo 1124630 1127523 := bstep (se 1 (by rfl) ⟨845642, by rfl⟩ : syracuseStep 1127523 = 1691285) B1691285
theorem B1127539 : Blo 1124630 1127539 := bstep (se 1 (by rfl) ⟨845654, by rfl⟩ : syracuseStep 1127539 = 1691309) B1691309
theorem B1127555 : Blo 1124630 1127555 := bstep (se 1 (by rfl) ⟨845666, by rfl⟩ : syracuseStep 1127555 = 1691333) B1691333
theorem B1127571 : Blo 1124630 1127571 := bstep (se 1 (by rfl) ⟨845678, by rfl⟩ : syracuseStep 1127571 = 1691357) B1691357
theorem B1127587 : Blo 1124630 1127587 := bstep (se 1 (by rfl) ⟨845690, by rfl⟩ : syracuseStep 1127587 = 1691381) B1691381
theorem B1127603 : Blo 1124630 1127603 := bstep (se 1 (by rfl) ⟨845702, by rfl⟩ : syracuseStep 1127603 = 1691405) B1691405
theorem B1127619 : Blo 1124630 1127619 := bstep (se 1 (by rfl) ⟨845714, by rfl⟩ : syracuseStep 1127619 = 1691429) B1691429
theorem B1127635 : Blo 1124630 1127635 := bstep (se 1 (by rfl) ⟨845726, by rfl⟩ : syracuseStep 1127635 = 1691453) B1691453
theorem B1127651 : Blo 1124630 1127651 := bstep (se 1 (by rfl) ⟨845738, by rfl⟩ : syracuseStep 1127651 = 1691477) B1691477
theorem B1127667 : Blo 1124630 1127667 := bstep (se 1 (by rfl) ⟨845750, by rfl⟩ : syracuseStep 1127667 = 1691501) B1691501
theorem B1127683 : Blo 1124630 1127683 := bstep (se 1 (by rfl) ⟨845762, by rfl⟩ : syracuseStep 1127683 = 1691525) B1691525
theorem B2536721 : Blo 1124630 2536721 := bstep (se 2 (by rfl) ⟨951270, by rfl⟩ : syracuseStep 2536721 = 1902541) B1902541
theorem B1127699 : Blo 1124630 1127699 := bstep (se 1 (by rfl) ⟨845774, by rfl⟩ : syracuseStep 1127699 = 1691549) B1691549
theorem B2536739 : Blo 1124630 2536739 := bstep (se 1 (by rfl) ⟨1902554, by rfl⟩ : syracuseStep 2536739 = 3805109) B3805109
theorem B1127715 : Blo 1124630 1127715 := bstep (se 1 (by rfl) ⟨845786, by rfl⟩ : syracuseStep 1127715 = 1691573) B1691573
theorem B1127731 : Blo 1124630 1127731 := bstep (se 1 (by rfl) ⟨845798, by rfl⟩ : syracuseStep 1127731 = 1691597) B1691597
theorem B1127747 : Blo 1124630 1127747 := bstep (se 1 (by rfl) ⟨845810, by rfl⟩ : syracuseStep 1127747 = 1691621) B1691621
theorem B1127763 : Blo 1124630 1127763 := bstep (se 1 (by rfl) ⟨845822, by rfl⟩ : syracuseStep 1127763 = 1691645) B1691645
theorem B1127779 : Blo 1124630 1127779 := bstep (se 1 (by rfl) ⟨845834, by rfl⟩ : syracuseStep 1127779 = 1691669) B1691669
theorem B1127795 : Blo 1124630 1127795 := bstep (se 1 (by rfl) ⟨845846, by rfl⟩ : syracuseStep 1127795 = 1691693) B1691693
theorem B1127811 : Blo 1124630 1127811 := bstep (se 1 (by rfl) ⟨845858, by rfl⟩ : syracuseStep 1127811 = 1691717) B1691717
theorem B1127827 : Blo 1124630 1127827 := bstep (se 1 (by rfl) ⟨845870, by rfl⟩ : syracuseStep 1127827 = 1691741) B1691741
theorem B1127843 : Blo 1124630 1127843 := bstep (se 1 (by rfl) ⟨845882, by rfl⟩ : syracuseStep 1127843 = 1691765) B1691765
theorem B1127859 : Blo 1124630 1127859 := bstep (se 1 (by rfl) ⟨845894, by rfl⟩ : syracuseStep 1127859 = 1691789) B1691789
theorem B1127875 : Blo 1124630 1127875 := bstep (se 1 (by rfl) ⟨845906, by rfl⟩ : syracuseStep 1127875 = 1691813) B1691813
theorem B1127891 : Blo 1124630 1127891 := bstep (se 1 (by rfl) ⟨845918, by rfl⟩ : syracuseStep 1127891 = 1691837) B1691837
theorem B1127907 : Blo 1124630 1127907 := bstep (se 1 (by rfl) ⟨845930, by rfl⟩ : syracuseStep 1127907 = 1691861) B1691861
theorem B1127923 : Blo 1124630 1127923 := bstep (se 1 (by rfl) ⟨845942, by rfl⟩ : syracuseStep 1127923 = 1691885) B1691885
theorem B1127939 : Blo 1124630 1127939 := bstep (se 1 (by rfl) ⟨845954, by rfl⟩ : syracuseStep 1127939 = 1691909) B1691909
theorem B1127955 : Blo 1124630 1127955 := bstep (se 1 (by rfl) ⟨845966, by rfl⟩ : syracuseStep 1127955 = 1691933) B1691933
theorem B1521185 : Blo 1124630 1521185 := bstep (se 2 (by rfl) ⟨570444, by rfl⟩ : syracuseStep 1521185 = 1140889) B1140889
theorem B1127971 : Blo 1124630 1127971 := bstep (se 1 (by rfl) ⟨845978, by rfl⟩ : syracuseStep 1127971 = 1691957) B1691957
theorem B2537009 : Blo 1124630 2537009 := bstep (se 2 (by rfl) ⟨951378, by rfl⟩ : syracuseStep 2537009 = 1902757) B1902757
theorem B1127987 : Blo 1124630 1127987 := bstep (se 1 (by rfl) ⟨845990, by rfl⟩ : syracuseStep 1127987 = 1691981) B1691981
theorem B2537027 : Blo 1124630 2537027 := bstep (se 1 (by rfl) ⟨1902770, by rfl⟩ : syracuseStep 2537027 = 3805541) B3805541
theorem B1128003 : Blo 1124630 1128003 := bstep (se 1 (by rfl) ⟨846002, by rfl⟩ : syracuseStep 1128003 = 1692005) B1692005
theorem B1128019 : Blo 1124630 1128019 := bstep (se 1 (by rfl) ⟨846014, by rfl⟩ : syracuseStep 1128019 = 1692029) B1692029
theorem B1128035 : Blo 1124630 1128035 := bstep (se 1 (by rfl) ⟨846026, by rfl⟩ : syracuseStep 1128035 = 1692053) B1692053
theorem B1128051 : Blo 1124630 1128051 := bstep (se 1 (by rfl) ⟨846038, by rfl⟩ : syracuseStep 1128051 = 1692077) B1692077
theorem B1128067 : Blo 1124630 1128067 := bstep (se 1 (by rfl) ⟨846050, by rfl⟩ : syracuseStep 1128067 = 1692101) B1692101
theorem B1128083 : Blo 1124630 1128083 := bstep (se 1 (by rfl) ⟨846062, by rfl⟩ : syracuseStep 1128083 = 1692125) B1692125
theorem B1128099 : Blo 1124630 1128099 := bstep (se 1 (by rfl) ⟨846074, by rfl⟩ : syracuseStep 1128099 = 1692149) B1692149
theorem B1128115 : Blo 1124630 1128115 := bstep (se 1 (by rfl) ⟨846086, by rfl⟩ : syracuseStep 1128115 = 1692173) B1692173
theorem B1128131 : Blo 1124630 1128131 := bstep (se 1 (by rfl) ⟨846098, by rfl⟩ : syracuseStep 1128131 = 1692197) B1692197
theorem B1128147 : Blo 1124630 1128147 := bstep (se 1 (by rfl) ⟨846110, by rfl⟩ : syracuseStep 1128147 = 1692221) B1692221
theorem B1128163 : Blo 1124630 1128163 := bstep (se 1 (by rfl) ⟨846122, by rfl⟩ : syracuseStep 1128163 = 1692245) B1692245
theorem B1128179 : Blo 1124630 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B1128195 : Blo 1124630 1128195 := bstep (se 1 (by rfl) ⟨846146, by rfl⟩ : syracuseStep 1128195 = 1692293) B1692293
theorem B1128211 : Blo 1124630 1128211 := bstep (se 1 (by rfl) ⟨846158, by rfl⟩ : syracuseStep 1128211 = 1692317) B1692317
theorem B2406179 : Blo 1124630 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B1128227 : Blo 1124630 1128227 := bstep (se 1 (by rfl) ⟨846170, by rfl⟩ : syracuseStep 1128227 = 1692341) B1692341
theorem B3421997 : Blo 1124630 3421997 := bstep (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) B1283249
theorem B1128243 : Blo 1124630 1128243 := bstep (se 1 (by rfl) ⟨846182, by rfl⟩ : syracuseStep 1128243 = 1692365) B1692365
theorem B1128259 : Blo 1124630 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B2537297 : Blo 1124630 2537297 := bstep (se 2 (by rfl) ⟨951486, by rfl⟩ : syracuseStep 2537297 = 1902973) B1902973
theorem B1128275 : Blo 1124630 1128275 := bstep (se 1 (by rfl) ⟨846206, by rfl⟩ : syracuseStep 1128275 = 1692413) B1692413
theorem B2537315 : Blo 1124630 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B1128291 : Blo 1124630 1128291 := bstep (se 1 (by rfl) ⟨846218, by rfl⟩ : syracuseStep 1128291 = 1692437) B1692437
theorem B1128307 : Blo 1124630 1128307 := bstep (se 1 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 1128307 = 1692461) B1692461
theorem B1128323 : Blo 1124630 1128323 := bstep (se 1 (by rfl) ⟨846242, by rfl⟩ : syracuseStep 1128323 = 1692485) B1692485
theorem B1128339 : Blo 1124630 1128339 := bstep (se 1 (by rfl) ⟨846254, by rfl⟩ : syracuseStep 1128339 = 1692509) B1692509
theorem B1128355 : Blo 1124630 1128355 := bstep (se 1 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 1128355 = 1692533) B1692533
theorem B1128371 : Blo 1124630 1128371 := bstep (se 1 (by rfl) ⟨846278, by rfl⟩ : syracuseStep 1128371 = 1692557) B1692557
theorem B1128387 : Blo 1124630 1128387 := bstep (se 1 (by rfl) ⟨846290, by rfl⟩ : syracuseStep 1128387 = 1692581) B1692581
theorem B1128403 : Blo 1124630 1128403 := bstep (se 1 (by rfl) ⟨846302, by rfl⟩ : syracuseStep 1128403 = 1692605) B1692605
theorem B1128419 : Blo 1124630 1128419 := bstep (se 1 (by rfl) ⟨846314, by rfl⟩ : syracuseStep 1128419 = 1692629) B1692629
theorem B1128435 : Blo 1124630 1128435 := bstep (se 1 (by rfl) ⟨846326, by rfl⟩ : syracuseStep 1128435 = 1692653) B1692653
theorem B1128451 : Blo 1124630 1128451 := bstep (se 1 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 1128451 = 1692677) B1692677
theorem B1128467 : Blo 1124630 1128467 := bstep (se 1 (by rfl) ⟨846350, by rfl⟩ : syracuseStep 1128467 = 1692701) B1692701
theorem B1128483 : Blo 1124630 1128483 := bstep (se 1 (by rfl) ⟨846362, by rfl⟩ : syracuseStep 1128483 = 1692725) B1692725
theorem B1128499 : Blo 1124630 1128499 := bstep (se 1 (by rfl) ⟨846374, by rfl⟩ : syracuseStep 1128499 = 1692749) B1692749
theorem B1128515 : Blo 1124630 1128515 := bstep (se 1 (by rfl) ⟨846386, by rfl⟩ : syracuseStep 1128515 = 1692773) B1692773
theorem B1128531 : Blo 1124630 1128531 := bstep (se 1 (by rfl) ⟨846398, by rfl⟩ : syracuseStep 1128531 = 1692797) B1692797
theorem B1128547 : Blo 1124630 1128547 := bstep (se 1 (by rfl) ⟨846410, by rfl⟩ : syracuseStep 1128547 = 1692821) B1692821
theorem B2537585 : Blo 1124630 2537585 := bstep (se 2 (by rfl) ⟨951594, by rfl⟩ : syracuseStep 2537585 = 1903189) B1903189
theorem B1128563 : Blo 1124630 1128563 := bstep (se 1 (by rfl) ⟨846422, by rfl⟩ : syracuseStep 1128563 = 1692845) B1692845
theorem B2537603 : Blo 1124630 2537603 := bstep (se 1 (by rfl) ⟨1903202, by rfl⟩ : syracuseStep 2537603 = 3806405) B3806405
theorem B1128579 : Blo 1124630 1128579 := bstep (se 1 (by rfl) ⟨846434, by rfl⟩ : syracuseStep 1128579 = 1692869) B1692869
theorem B1128595 : Blo 1124630 1128595 := bstep (se 1 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 1128595 = 1692893) B1692893
theorem B1128611 : Blo 1124630 1128611 := bstep (se 1 (by rfl) ⟨846458, by rfl⟩ : syracuseStep 1128611 = 1692917) B1692917
theorem B1128627 : Blo 1124630 1128627 := bstep (se 1 (by rfl) ⟨846470, by rfl⟩ : syracuseStep 1128627 = 1692941) B1692941
theorem B1423651 : Blo 1124630 1423651 := bstep (se 1 (by rfl) ⟨1067738, by rfl⟩ : syracuseStep 1423651 = 2135477) B2135477
theorem B1423747 : Blo 1124630 1423747 := bstep (se 1 (by rfl) ⟨1067810, by rfl⟩ : syracuseStep 1423747 = 2135621) B2135621
theorem B2537873 : Blo 1124630 2537873 := bstep (se 2 (by rfl) ⟨951702, by rfl⟩ : syracuseStep 2537873 = 1903405) B1903405
theorem B2537891 : Blo 1124630 2537891 := bstep (se 1 (by rfl) ⟨1903418, by rfl⟩ : syracuseStep 2537891 = 3806837) B3806837
theorem B7223843 : Blo 1124630 7223843 := bstep (se 1 (by rfl) ⟨5417882, by rfl⟩ : syracuseStep 7223843 = 10835765) B10835765
theorem B4274765 : Blo 1124630 4274765 := bstep (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) B1603037
theorem B2538161 : Blo 1124630 2538161 := bstep (se 2 (by rfl) ⟨951810, by rfl⟩ : syracuseStep 2538161 = 1903621) B1903621
theorem B2538179 : Blo 1124630 2538179 := bstep (se 1 (by rfl) ⟨1903634, by rfl⟩ : syracuseStep 2538179 = 3807269) B3807269
theorem B2407153 : Blo 1124630 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B2439971 : Blo 1124630 2439971 := bstep (se 1 (by rfl) ⟨1829978, by rfl⟩ : syracuseStep 2439971 = 3659957) B3659957
theorem B19249973 : Blo 1124630 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B1424243 : Blo 1124630 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B8567693 : Blo 1124630 8567693 := bstep (se 3 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 8567693 = 3212885) B3212885
theorem B2538449 : Blo 1124630 2538449 := bstep (se 2 (by rfl) ⟨951918, by rfl⟩ : syracuseStep 2538449 = 1903837) B1903837
theorem B2538467 : Blo 1124630 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B2407409 : Blo 1124630 2407409 := bstep (se 2 (by rfl) ⟨902778, by rfl⟩ : syracuseStep 2407409 = 1805557) B1805557
theorem B6405155 : Blo 1124630 6405155 := bstep (se 1 (by rfl) ⟨4803866, by rfl⟩ : syracuseStep 6405155 = 9607733) B9607733
theorem B2538737 : Blo 1124630 2538737 := bstep (se 2 (by rfl) ⟨952026, by rfl⟩ : syracuseStep 2538737 = 1904053) B1904053
theorem B2538755 : Blo 1124630 2538755 := bstep (se 1 (by rfl) ⟨1904066, by rfl⟩ : syracuseStep 2538755 = 3808133) B3808133
theorem B2702609 : Blo 1124630 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B1522963 : Blo 1124630 1522963 := bstep (se 1 (by rfl) ⟨1142222, by rfl⟩ : syracuseStep 1522963 = 2284445) B2284445
theorem B5487907 : Blo 1124630 5487907 := bstep (se 1 (by rfl) ⟨4115930, by rfl⟩ : syracuseStep 5487907 = 8231861) B8231861
theorem B4570481 : Blo 1124630 4570481 := bstep (se 2 (by rfl) ⟨1713930, by rfl⟩ : syracuseStep 4570481 = 3427861) B3427861
theorem B1686947 : Blo 1124630 1686947 := bstep (se 1 (by rfl) ⟨1265210, by rfl⟩ : syracuseStep 1686947 = 2530421) B2530421
theorem B1686977 : Blo 1124630 1686977 := bstep (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) B1265233
theorem B1686995 : Blo 1124630 1686995 := bstep (se 1 (by rfl) ⟨1265246, by rfl⟩ : syracuseStep 1686995 = 2530493) B2530493
theorem B1687025 : Blo 1124630 1687025 := bstep (se 2 (by rfl) ⟨632634, by rfl⟩ : syracuseStep 1687025 = 1265269) B1265269
theorem B1687043 : Blo 1124630 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B2539025 : Blo 1124630 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B1687073 : Blo 1124630 1687073 := bstep (se 2 (by rfl) ⟨632652, by rfl⟩ : syracuseStep 1687073 = 1265305) B1265305
theorem B2539043 : Blo 1124630 2539043 := bstep (se 1 (by rfl) ⟨1904282, by rfl⟩ : syracuseStep 2539043 = 3808565) B3808565
theorem B1687091 : Blo 1124630 1687091 := bstep (se 1 (by rfl) ⟨1265318, by rfl⟩ : syracuseStep 1687091 = 2530637) B2530637
theorem B1424947 : Blo 1124630 1424947 := bstep (se 1 (by rfl) ⟨1068710, by rfl⟩ : syracuseStep 1424947 = 2137421) B2137421
theorem B1687121 : Blo 1124630 1687121 := bstep (se 2 (by rfl) ⟨632670, by rfl⟩ : syracuseStep 1687121 = 1265341) B1265341
theorem B1687139 : Blo 1124630 1687139 := bstep (se 1 (by rfl) ⟨1265354, by rfl⟩ : syracuseStep 1687139 = 2530709) B2530709
theorem B1687169 : Blo 1124630 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B1687187 : Blo 1124630 1687187 := bstep (se 1 (by rfl) ⟨1265390, by rfl⟩ : syracuseStep 1687187 = 2530781) B2530781
theorem B1425043 : Blo 1124630 1425043 := bstep (se 1 (by rfl) ⟨1068782, by rfl⟩ : syracuseStep 1425043 = 2137565) B2137565
theorem B1687217 : Blo 1124630 1687217 := bstep (se 2 (by rfl) ⟨632706, by rfl⟩ : syracuseStep 1687217 = 1265413) B1265413
theorem B6504113 : Blo 1124630 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B1687235 : Blo 1124630 1687235 := bstep (se 1 (by rfl) ⟨1265426, by rfl⟩ : syracuseStep 1687235 = 2530853) B2530853
theorem B1687265 : Blo 1124630 1687265 := bstep (se 2 (by rfl) ⟨632724, by rfl⟩ : syracuseStep 1687265 = 1265449) B1265449
theorem B1687283 : Blo 1124630 1687283 := bstep (se 1 (by rfl) ⟨1265462, by rfl⟩ : syracuseStep 1687283 = 2530925) B2530925
theorem B2703107 : Blo 1124630 2703107 := bstep (se 1 (by rfl) ⟨2027330, by rfl⟩ : syracuseStep 2703107 = 4054661) B4054661
theorem B1687313 : Blo 1124630 1687313 := bstep (se 2 (by rfl) ⟨632742, by rfl⟩ : syracuseStep 1687313 = 1265485) B1265485
theorem B1687331 : Blo 1124630 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2539313 : Blo 1124630 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B1687361 : Blo 1124630 1687361 := bstep (se 2 (by rfl) ⟨632760, by rfl⟩ : syracuseStep 1687361 = 1265521) B1265521
theorem B2539331 : Blo 1124630 2539331 := bstep (se 1 (by rfl) ⟨1904498, by rfl⟩ : syracuseStep 2539331 = 3808997) B3808997
theorem B1687379 : Blo 1124630 1687379 := bstep (se 1 (by rfl) ⟨1265534, by rfl⟩ : syracuseStep 1687379 = 2531069) B2531069
theorem B1687409 : Blo 1124630 1687409 := bstep (se 2 (by rfl) ⟨632778, by rfl⟩ : syracuseStep 1687409 = 1265557) B1265557
theorem B1687427 : Blo 1124630 1687427 := bstep (se 1 (by rfl) ⟨1265570, by rfl⟩ : syracuseStep 1687427 = 2531141) B2531141
theorem B1687457 : Blo 1124630 1687457 := bstep (se 2 (by rfl) ⟨632796, by rfl⟩ : syracuseStep 1687457 = 1265593) B1265593
theorem B1687475 : Blo 1124630 1687475 := bstep (se 1 (by rfl) ⟨1265606, by rfl⟩ : syracuseStep 1687475 = 2531213) B2531213
theorem B2703299 : Blo 1124630 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B30883781 : Blo 1124630 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1687505 : Blo 1124630 1687505 := bstep (se 2 (by rfl) ⟨632814, by rfl⟩ : syracuseStep 1687505 = 1265629) B1265629
theorem B1687523 : Blo 1124630 1687523 := bstep (se 1 (by rfl) ⟨1265642, by rfl⟩ : syracuseStep 1687523 = 2531285) B2531285
theorem B1687553 : Blo 1124630 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B1687571 : Blo 1124630 1687571 := bstep (se 1 (by rfl) ⟨1265678, by rfl⟩ : syracuseStep 1687571 = 2531357) B2531357
theorem B1687601 : Blo 1124630 1687601 := bstep (se 2 (by rfl) ⟨632850, by rfl⟩ : syracuseStep 1687601 = 1265701) B1265701
theorem B1687619 : Blo 1124630 1687619 := bstep (se 1 (by rfl) ⟨1265714, by rfl⟩ : syracuseStep 1687619 = 2531429) B2531429
theorem B3850321 : Blo 1124630 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B1687649 : Blo 1124630 1687649 := bstep (se 2 (by rfl) ⟨632868, by rfl⟩ : syracuseStep 1687649 = 1265737) B1265737
theorem B1687667 : Blo 1124630 1687667 := bstep (se 1 (by rfl) ⟨1265750, by rfl⟩ : syracuseStep 1687667 = 2531501) B2531501
theorem B1425539 : Blo 1124630 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B1687697 : Blo 1124630 1687697 := bstep (se 2 (by rfl) ⟨632886, by rfl⟩ : syracuseStep 1687697 = 1265773) B1265773
theorem B1687715 : Blo 1124630 1687715 := bstep (se 1 (by rfl) ⟨1265786, by rfl⟩ : syracuseStep 1687715 = 2531573) B2531573
theorem B1687745 : Blo 1124630 1687745 := bstep (se 2 (by rfl) ⟨632904, by rfl⟩ : syracuseStep 1687745 = 1265809) B1265809
theorem B3653837 : Blo 1124630 3653837 := bstep (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) B1370189
theorem B1687763 : Blo 1124630 1687763 := bstep (se 1 (by rfl) ⟨1265822, by rfl⟩ : syracuseStep 1687763 = 2531645) B2531645
theorem B1687793 : Blo 1124630 1687793 := bstep (se 2 (by rfl) ⟨632922, by rfl⟩ : syracuseStep 1687793 = 1265845) B1265845
theorem B1687811 : Blo 1124630 1687811 := bstep (se 1 (by rfl) ⟨1265858, by rfl⟩ : syracuseStep 1687811 = 2531717) B2531717
theorem B2408707 : Blo 1124630 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B3424525 : Blo 1124630 3424525 := bstep (se 3 (by rfl) ⟨642098, by rfl⟩ : syracuseStep 3424525 = 1284197) B1284197
theorem B12828941 : Blo 1124630 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B1687841 : Blo 1124630 1687841 := bstep (se 2 (by rfl) ⟨632940, by rfl⟩ : syracuseStep 1687841 = 1265881) B1265881
theorem B1687859 : Blo 1124630 1687859 := bstep (se 1 (by rfl) ⟨1265894, by rfl⟩ : syracuseStep 1687859 = 2531789) B2531789
theorem B1687889 : Blo 1124630 1687889 := bstep (se 2 (by rfl) ⟨632958, by rfl⟩ : syracuseStep 1687889 = 1265917) B1265917
theorem B1687907 : Blo 1124630 1687907 := bstep (se 1 (by rfl) ⟨1265930, by rfl⟩ : syracuseStep 1687907 = 2531861) B2531861
theorem B1687937 : Blo 1124630 1687937 := bstep (se 2 (by rfl) ⟨632976, by rfl⟩ : syracuseStep 1687937 = 1265953) B1265953
theorem B4342157 : Blo 1124630 4342157 := bstep (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) B1628309
theorem B1687955 : Blo 1124630 1687955 := bstep (se 1 (by rfl) ⟨1265966, by rfl⟩ : syracuseStep 1687955 = 2531933) B2531933
theorem B1687985 : Blo 1124630 1687985 := bstep (se 2 (by rfl) ⟨632994, by rfl⟩ : syracuseStep 1687985 = 1265989) B1265989
theorem B1688003 : Blo 1124630 1688003 := bstep (se 1 (by rfl) ⟨1266002, by rfl⟩ : syracuseStep 1688003 = 2532005) B2532005
theorem B1688033 : Blo 1124630 1688033 := bstep (se 2 (by rfl) ⟨633012, by rfl⟩ : syracuseStep 1688033 = 1266025) B1266025
theorem B1688051 : Blo 1124630 1688051 := bstep (se 1 (by rfl) ⟨1266038, by rfl⟩ : syracuseStep 1688051 = 2532077) B2532077
theorem B1688081 : Blo 1124630 1688081 := bstep (se 2 (by rfl) ⟨633030, by rfl⟩ : syracuseStep 1688081 = 1266061) B1266061
theorem B1688099 : Blo 1124630 1688099 := bstep (se 1 (by rfl) ⟨1266074, by rfl⟩ : syracuseStep 1688099 = 2532149) B2532149
theorem B1688129 : Blo 1124630 1688129 := bstep (se 2 (by rfl) ⟨633048, by rfl⟩ : syracuseStep 1688129 = 1266097) B1266097
theorem B3850829 : Blo 1124630 3850829 := bstep (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) B1444061
theorem B2409041 : Blo 1124630 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1688147 : Blo 1124630 1688147 := bstep (se 1 (by rfl) ⟨1266110, by rfl⟩ : syracuseStep 1688147 = 2532221) B2532221
theorem B1688177 : Blo 1124630 1688177 := bstep (se 2 (by rfl) ⟨633066, by rfl⟩ : syracuseStep 1688177 = 1266133) B1266133
theorem B9749105 : Blo 1124630 9749105 := bstep (se 2 (by rfl) ⟨3655914, by rfl⟩ : syracuseStep 9749105 = 7311829) B7311829
theorem B7225969 : Blo 1124630 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B1688195 : Blo 1124630 1688195 := bstep (se 1 (by rfl) ⟨1266146, by rfl⟩ : syracuseStep 1688195 = 2532293) B2532293
theorem B1688225 : Blo 1124630 1688225 := bstep (se 2 (by rfl) ⟨633084, by rfl⟩ : syracuseStep 1688225 = 1266169) B1266169
theorem B1688243 : Blo 1124630 1688243 := bstep (se 1 (by rfl) ⟨1266182, by rfl⟩ : syracuseStep 1688243 = 2532365) B2532365
theorem B1688273 : Blo 1124630 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1688291 : Blo 1124630 1688291 := bstep (se 1 (by rfl) ⟨1266218, by rfl⟩ : syracuseStep 1688291 = 2532437) B2532437
theorem B11715299 : Blo 1124630 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B1688321 : Blo 1124630 1688321 := bstep (se 2 (by rfl) ⟨633120, by rfl⟩ : syracuseStep 1688321 = 1266241) B1266241
theorem B1688339 : Blo 1124630 1688339 := bstep (se 1 (by rfl) ⟨1266254, by rfl⟩ : syracuseStep 1688339 = 2532509) B2532509
theorem B1688369 : Blo 1124630 1688369 := bstep (se 2 (by rfl) ⟨633138, by rfl⟩ : syracuseStep 1688369 = 1266277) B1266277
theorem B1688387 : Blo 1124630 1688387 := bstep (se 1 (by rfl) ⟨1266290, by rfl⟩ : syracuseStep 1688387 = 2532581) B2532581
theorem B1426243 : Blo 1124630 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B1688417 : Blo 1124630 1688417 := bstep (se 2 (by rfl) ⟨633156, by rfl⟩ : syracuseStep 1688417 = 1266313) B1266313
theorem B1688435 : Blo 1124630 1688435 := bstep (se 1 (by rfl) ⟨1266326, by rfl⟩ : syracuseStep 1688435 = 2532653) B2532653
theorem B6407045 : Blo 1124630 6407045 := bstep (se 4 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 6407045 = 1201321) B1201321
theorem B1688465 : Blo 1124630 1688465 := bstep (se 2 (by rfl) ⟨633174, by rfl⟩ : syracuseStep 1688465 = 1266349) B1266349
theorem B1688483 : Blo 1124630 1688483 := bstep (se 1 (by rfl) ⟨1266362, by rfl⟩ : syracuseStep 1688483 = 2532725) B2532725
theorem B1426339 : Blo 1124630 1426339 := bstep (se 1 (by rfl) ⟨1069754, by rfl⟩ : syracuseStep 1426339 = 2139509) B2139509
theorem B1688513 : Blo 1124630 1688513 := bstep (se 2 (by rfl) ⟨633192, by rfl⟩ : syracuseStep 1688513 = 1266385) B1266385
theorem B1688531 : Blo 1124630 1688531 := bstep (se 1 (by rfl) ⟨1266398, by rfl⟩ : syracuseStep 1688531 = 2532797) B2532797
theorem B1688561 : Blo 1124630 1688561 := bstep (se 2 (by rfl) ⟨633210, by rfl⟩ : syracuseStep 1688561 = 1266421) B1266421
theorem B1688579 : Blo 1124630 1688579 := bstep (se 1 (by rfl) ⟨1266434, by rfl⟩ : syracuseStep 1688579 = 2532869) B2532869
theorem B1688609 : Blo 1124630 1688609 := bstep (se 2 (by rfl) ⟨633228, by rfl⟩ : syracuseStep 1688609 = 1266457) B1266457
theorem B1688627 : Blo 1124630 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B1688657 : Blo 1124630 1688657 := bstep (se 2 (by rfl) ⟨633246, by rfl⟩ : syracuseStep 1688657 = 1266493) B1266493
theorem B1688675 : Blo 1124630 1688675 := bstep (se 1 (by rfl) ⟨1266506, by rfl⟩ : syracuseStep 1688675 = 2533013) B2533013
theorem B1688705 : Blo 1124630 1688705 := bstep (se 2 (by rfl) ⟨633264, by rfl⟩ : syracuseStep 1688705 = 1266529) B1266529
theorem B1688723 : Blo 1124630 1688723 := bstep (se 1 (by rfl) ⟨1266542, by rfl⟩ : syracuseStep 1688723 = 2533085) B2533085
theorem B3425453 : Blo 1124630 3425453 := bstep (se 3 (by rfl) ⟨642272, by rfl⟩ : syracuseStep 3425453 = 1284545) B1284545
theorem B1688753 : Blo 1124630 1688753 := bstep (se 2 (by rfl) ⟨633282, by rfl⟩ : syracuseStep 1688753 = 1266565) B1266565
theorem B1688771 : Blo 1124630 1688771 := bstep (se 1 (by rfl) ⟨1266578, by rfl⟩ : syracuseStep 1688771 = 2533157) B2533157
theorem B1688801 : Blo 1124630 1688801 := bstep (se 2 (by rfl) ⟨633300, by rfl⟩ : syracuseStep 1688801 = 1266601) B1266601
theorem B1688819 : Blo 1124630 1688819 := bstep (se 1 (by rfl) ⟨1266614, by rfl⟩ : syracuseStep 1688819 = 2533229) B2533229
theorem B1688849 : Blo 1124630 1688849 := bstep (se 2 (by rfl) ⟨633318, by rfl⟩ : syracuseStep 1688849 = 1266637) B1266637
theorem B1688867 : Blo 1124630 1688867 := bstep (se 1 (by rfl) ⟨1266650, by rfl⟩ : syracuseStep 1688867 = 2533301) B2533301
theorem B1951025 : Blo 1124630 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1688897 : Blo 1124630 1688897 := bstep (se 2 (by rfl) ⟨633336, by rfl⟩ : syracuseStep 1688897 = 1266673) B1266673
theorem B1688915 : Blo 1124630 1688915 := bstep (se 1 (by rfl) ⟨1266686, by rfl⟩ : syracuseStep 1688915 = 2533373) B2533373
theorem B1688945 : Blo 1124630 1688945 := bstep (se 2 (by rfl) ⟨633354, by rfl⟩ : syracuseStep 1688945 = 1266709) B1266709
theorem B1688963 : Blo 1124630 1688963 := bstep (se 1 (by rfl) ⟨1266722, by rfl⟩ : syracuseStep 1688963 = 2533445) B2533445
theorem B4572557 : Blo 1124630 4572557 := bstep (se 3 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 4572557 = 1714709) B1714709
theorem B1426835 : Blo 1124630 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B1688993 : Blo 1124630 1688993 := bstep (se 2 (by rfl) ⟨633372, by rfl⟩ : syracuseStep 1688993 = 1266745) B1266745
theorem B4277681 : Blo 1124630 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B1525169 : Blo 1124630 1525169 := bstep (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) B1143877
theorem B1689011 : Blo 1124630 1689011 := bstep (se 1 (by rfl) ⟨1266758, by rfl⟩ : syracuseStep 1689011 = 2533517) B2533517
theorem B1689041 : Blo 1124630 1689041 := bstep (se 2 (by rfl) ⟨633390, by rfl⟩ : syracuseStep 1689041 = 1266781) B1266781
theorem B1689059 : Blo 1124630 1689059 := bstep (se 1 (by rfl) ⟨1266794, by rfl⟩ : syracuseStep 1689059 = 2533589) B2533589
theorem B1689089 : Blo 1124630 1689089 := bstep (se 2 (by rfl) ⟨633408, by rfl⟩ : syracuseStep 1689089 = 1266817) B1266817
theorem B1689107 : Blo 1124630 1689107 := bstep (se 1 (by rfl) ⟨1266830, by rfl⟩ : syracuseStep 1689107 = 2533661) B2533661
theorem B1689137 : Blo 1124630 1689137 := bstep (se 2 (by rfl) ⟨633426, by rfl⟩ : syracuseStep 1689137 = 1266853) B1266853
theorem B1689155 : Blo 1124630 1689155 := bstep (se 1 (by rfl) ⟨1266866, by rfl⟩ : syracuseStep 1689155 = 2533733) B2533733
theorem B1689185 : Blo 1124630 1689185 := bstep (se 2 (by rfl) ⟨633444, by rfl⟩ : syracuseStep 1689185 = 1266889) B1266889
theorem B1689203 : Blo 1124630 1689203 := bstep (se 1 (by rfl) ⟨1266902, by rfl⟩ : syracuseStep 1689203 = 2533805) B2533805
theorem B1689233 : Blo 1124630 1689233 := bstep (se 2 (by rfl) ⟨633462, by rfl⟩ : syracuseStep 1689233 = 1266925) B1266925
theorem B1689251 : Blo 1124630 1689251 := bstep (se 1 (by rfl) ⟨1266938, by rfl⟩ : syracuseStep 1689251 = 2533877) B2533877
theorem B1689281 : Blo 1124630 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B1689299 : Blo 1124630 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B2410211 : Blo 1124630 2410211 := bstep (se 1 (by rfl) ⟨1807658, by rfl⟩ : syracuseStep 2410211 = 3615317) B3615317
theorem B1689329 : Blo 1124630 1689329 := bstep (se 2 (by rfl) ⟨633498, by rfl⟩ : syracuseStep 1689329 = 1266997) B1266997
theorem B1689347 : Blo 1124630 1689347 := bstep (se 1 (by rfl) ⟨1267010, by rfl⟩ : syracuseStep 1689347 = 2534021) B2534021
theorem B1689377 : Blo 1124630 1689377 := bstep (se 2 (by rfl) ⟨633516, by rfl⟩ : syracuseStep 1689377 = 1267033) B1267033
theorem B6080305 : Blo 1124630 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B1689395 : Blo 1124630 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B1689425 : Blo 1124630 1689425 := bstep (se 2 (by rfl) ⟨633534, by rfl⟩ : syracuseStep 1689425 = 1267069) B1267069
theorem B2705251 : Blo 1124630 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B1689443 : Blo 1124630 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B1689473 : Blo 1124630 1689473 := bstep (se 2 (by rfl) ⟨633552, by rfl⟩ : syracuseStep 1689473 = 1267105) B1267105
theorem B1689491 : Blo 1124630 1689491 := bstep (se 1 (by rfl) ⟨1267118, by rfl⟩ : syracuseStep 1689491 = 2534237) B2534237
theorem B1689521 : Blo 1124630 1689521 := bstep (se 2 (by rfl) ⟨633570, by rfl⟩ : syracuseStep 1689521 = 1267141) B1267141
theorem B1689539 : Blo 1124630 1689539 := bstep (se 1 (by rfl) ⟨1267154, by rfl⟩ : syracuseStep 1689539 = 2534309) B2534309
theorem B1689569 : Blo 1124630 1689569 := bstep (se 2 (by rfl) ⟨633588, by rfl⟩ : syracuseStep 1689569 = 1267177) B1267177
theorem B1689587 : Blo 1124630 1689587 := bstep (se 1 (by rfl) ⟨1267190, by rfl⟩ : syracuseStep 1689587 = 2534381) B2534381
theorem B1689617 : Blo 1124630 1689617 := bstep (se 2 (by rfl) ⟨633606, by rfl⟩ : syracuseStep 1689617 = 1267213) B1267213
theorem B1689635 : Blo 1124630 1689635 := bstep (se 1 (by rfl) ⟨1267226, by rfl⟩ : syracuseStep 1689635 = 2534453) B2534453
theorem B1689665 : Blo 1124630 1689665 := bstep (se 2 (by rfl) ⟨633624, by rfl⟩ : syracuseStep 1689665 = 1267249) B1267249
theorem B1689683 : Blo 1124630 1689683 := bstep (se 1 (by rfl) ⟨1267262, by rfl⟩ : syracuseStep 1689683 = 2534525) B2534525
theorem B1427539 : Blo 1124630 1427539 := bstep (se 1 (by rfl) ⟨1070654, by rfl⟩ : syracuseStep 1427539 = 2141309) B2141309
theorem B1689713 : Blo 1124630 1689713 := bstep (se 2 (by rfl) ⟨633642, by rfl⟩ : syracuseStep 1689713 = 1267285) B1267285
theorem B1689731 : Blo 1124630 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B1689761 : Blo 1124630 1689761 := bstep (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) B1267321
theorem B1689779 : Blo 1124630 1689779 := bstep (se 1 (by rfl) ⟨1267334, by rfl⟩ : syracuseStep 1689779 = 2534669) B2534669
theorem B1427635 : Blo 1124630 1427635 := bstep (se 1 (by rfl) ⟨1070726, by rfl⟩ : syracuseStep 1427635 = 2141453) B2141453
theorem B1689809 : Blo 1124630 1689809 := bstep (se 2 (by rfl) ⟨633678, by rfl⟩ : syracuseStep 1689809 = 1267357) B1267357
theorem B1689827 : Blo 1124630 1689827 := bstep (se 1 (by rfl) ⟨1267370, by rfl⟩ : syracuseStep 1689827 = 2534741) B2534741
theorem B1689857 : Blo 1124630 1689857 := bstep (se 2 (by rfl) ⟨633696, by rfl⟩ : syracuseStep 1689857 = 1267393) B1267393
theorem B1689875 : Blo 1124630 1689875 := bstep (se 1 (by rfl) ⟨1267406, by rfl⟩ : syracuseStep 1689875 = 2534813) B2534813
theorem B1689905 : Blo 1124630 1689905 := bstep (se 2 (by rfl) ⟨633714, by rfl⟩ : syracuseStep 1689905 = 1267429) B1267429
theorem B1689923 : Blo 1124630 1689923 := bstep (se 1 (by rfl) ⟨1267442, by rfl⟩ : syracuseStep 1689923 = 2534885) B2534885
theorem B1689953 : Blo 1124630 1689953 := bstep (se 2 (by rfl) ⟨633732, by rfl⟩ : syracuseStep 1689953 = 1267465) B1267465
theorem B1689971 : Blo 1124630 1689971 := bstep (se 1 (by rfl) ⟨1267478, by rfl⟩ : syracuseStep 1689971 = 2534957) B2534957
theorem B1690001 : Blo 1124630 1690001 := bstep (se 2 (by rfl) ⟨633750, by rfl⟩ : syracuseStep 1690001 = 1267501) B1267501
theorem B1690019 : Blo 1124630 1690019 := bstep (se 1 (by rfl) ⟨1267514, by rfl⟩ : syracuseStep 1690019 = 2535029) B2535029
theorem B1690049 : Blo 1124630 1690049 := bstep (se 2 (by rfl) ⟨633768, by rfl⟩ : syracuseStep 1690049 = 1267537) B1267537
theorem B1690067 : Blo 1124630 1690067 := bstep (se 1 (by rfl) ⟨1267550, by rfl⟩ : syracuseStep 1690067 = 2535101) B2535101
theorem B1690097 : Blo 1124630 1690097 := bstep (se 2 (by rfl) ⟨633786, by rfl⟩ : syracuseStep 1690097 = 1267573) B1267573
theorem B1690115 : Blo 1124630 1690115 := bstep (se 1 (by rfl) ⟨1267586, by rfl⟩ : syracuseStep 1690115 = 2535173) B2535173
theorem B1690145 : Blo 1124630 1690145 := bstep (se 2 (by rfl) ⟨633804, by rfl⟩ : syracuseStep 1690145 = 1267609) B1267609
theorem B1690163 : Blo 1124630 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B1690193 : Blo 1124630 1690193 := bstep (se 2 (by rfl) ⟨633822, by rfl⟩ : syracuseStep 1690193 = 1267645) B1267645
theorem B1690211 : Blo 1124630 1690211 := bstep (se 1 (by rfl) ⟨1267658, by rfl⟩ : syracuseStep 1690211 = 2535317) B2535317
theorem B1690241 : Blo 1124630 1690241 := bstep (se 2 (by rfl) ⟨633840, by rfl⟩ : syracuseStep 1690241 = 1267681) B1267681
theorem B3426961 : Blo 1124630 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1690259 : Blo 1124630 1690259 := bstep (se 1 (by rfl) ⟨1267694, by rfl⟩ : syracuseStep 1690259 = 2535389) B2535389
theorem B1428131 : Blo 1124630 1428131 := bstep (se 1 (by rfl) ⟨1071098, by rfl⟩ : syracuseStep 1428131 = 2142197) B2142197
theorem B1690289 : Blo 1124630 1690289 := bstep (se 2 (by rfl) ⟨633858, by rfl⟩ : syracuseStep 1690289 = 1267717) B1267717
theorem B1690307 : Blo 1124630 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B1690337 : Blo 1124630 1690337 := bstep (se 2 (by rfl) ⟨633876, by rfl⟩ : syracuseStep 1690337 = 1267753) B1267753
theorem B26036963 : Blo 1124630 26036963 := bstep (se 1 (by rfl) ⟨19527722, by rfl⟩ : syracuseStep 26036963 = 39055445) B39055445
theorem B1690355 : Blo 1124630 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B1690385 : Blo 1124630 1690385 := bstep (se 2 (by rfl) ⟨633894, by rfl⟩ : syracuseStep 1690385 = 1267789) B1267789
theorem B1690403 : Blo 1124630 1690403 := bstep (se 1 (by rfl) ⟨1267802, by rfl⟩ : syracuseStep 1690403 = 2535605) B2535605
theorem B1690433 : Blo 1124630 1690433 := bstep (se 2 (by rfl) ⟨633912, by rfl⟩ : syracuseStep 1690433 = 1267825) B1267825
theorem B1690451 : Blo 1124630 1690451 := bstep (se 1 (by rfl) ⟨1267838, by rfl⟩ : syracuseStep 1690451 = 2535677) B2535677
theorem B4279139 : Blo 1124630 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B1690481 : Blo 1124630 1690481 := bstep (se 2 (by rfl) ⟨633930, by rfl⟩ : syracuseStep 1690481 = 1267861) B1267861
theorem B1690499 : Blo 1124630 1690499 := bstep (se 1 (by rfl) ⟨1267874, by rfl⟩ : syracuseStep 1690499 = 2535749) B2535749
theorem B1690529 : Blo 1124630 1690529 := bstep (se 2 (by rfl) ⟨633948, by rfl⟩ : syracuseStep 1690529 = 1267897) B1267897
theorem B1690547 : Blo 1124630 1690547 := bstep (se 1 (by rfl) ⟨1267910, by rfl⟩ : syracuseStep 1690547 = 2535821) B2535821
theorem B3132365 : Blo 1124630 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B1690577 : Blo 1124630 1690577 := bstep (se 2 (by rfl) ⟨633966, by rfl⟩ : syracuseStep 1690577 = 1267933) B1267933
theorem B1690595 : Blo 1124630 1690595 := bstep (se 1 (by rfl) ⟨1267946, by rfl⟩ : syracuseStep 1690595 = 2535893) B2535893
theorem B1690625 : Blo 1124630 1690625 := bstep (se 2 (by rfl) ⟨633984, by rfl⟩ : syracuseStep 1690625 = 1267969) B1267969
theorem B1690643 : Blo 1124630 1690643 := bstep (se 1 (by rfl) ⟨1267982, by rfl⟩ : syracuseStep 1690643 = 2535965) B2535965
theorem B1690673 : Blo 1124630 1690673 := bstep (se 2 (by rfl) ⟨634002, by rfl⟩ : syracuseStep 1690673 = 1268005) B1268005
theorem B2706481 : Blo 1124630 2706481 := bstep (se 2 (by rfl) ⟨1014930, by rfl⟩ : syracuseStep 2706481 = 2029861) B2029861
theorem B1690691 : Blo 1124630 1690691 := bstep (se 1 (by rfl) ⟨1268018, by rfl⟩ : syracuseStep 1690691 = 2536037) B2536037
theorem B1690721 : Blo 1124630 1690721 := bstep (se 2 (by rfl) ⟨634020, by rfl⟩ : syracuseStep 1690721 = 1268041) B1268041
theorem B12831857 : Blo 1124630 12831857 := bstep (se 2 (by rfl) ⟨4811946, by rfl⟩ : syracuseStep 12831857 = 9623893) B9623893
theorem B1690739 : Blo 1124630 1690739 := bstep (se 1 (by rfl) ⟨1268054, by rfl⟩ : syracuseStep 1690739 = 2536109) B2536109
theorem B1690769 : Blo 1124630 1690769 := bstep (se 2 (by rfl) ⟨634038, by rfl⟩ : syracuseStep 1690769 = 1268077) B1268077
theorem B2280611 : Blo 1124630 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B1690787 : Blo 1124630 1690787 := bstep (se 1 (by rfl) ⟨1268090, by rfl⟩ : syracuseStep 1690787 = 2536181) B2536181
theorem B1690817 : Blo 1124630 1690817 := bstep (se 2 (by rfl) ⟨634056, by rfl⟩ : syracuseStep 1690817 = 1268113) B1268113
theorem B1690835 : Blo 1124630 1690835 := bstep (se 1 (by rfl) ⟨1268126, by rfl⟩ : syracuseStep 1690835 = 2536253) B2536253
theorem B1690865 : Blo 1124630 1690865 := bstep (se 2 (by rfl) ⟨634074, by rfl⟩ : syracuseStep 1690865 = 1268149) B1268149
theorem B1690883 : Blo 1124630 1690883 := bstep (se 1 (by rfl) ⟨1268162, by rfl⟩ : syracuseStep 1690883 = 2536325) B2536325
theorem B1690913 : Blo 1124630 1690913 := bstep (se 2 (by rfl) ⟨634092, by rfl⟩ : syracuseStep 1690913 = 1268185) B1268185
theorem B1690931 : Blo 1124630 1690931 := bstep (se 1 (by rfl) ⟨1268198, by rfl⟩ : syracuseStep 1690931 = 2536397) B2536397
theorem B1690961 : Blo 1124630 1690961 := bstep (se 2 (by rfl) ⟨634110, by rfl⟩ : syracuseStep 1690961 = 1268221) B1268221
theorem B1690979 : Blo 1124630 1690979 := bstep (se 1 (by rfl) ⟨1268234, by rfl⟩ : syracuseStep 1690979 = 2536469) B2536469
theorem B1691009 : Blo 1124630 1691009 := bstep (se 2 (by rfl) ⟨634128, by rfl⟩ : syracuseStep 1691009 = 1268257) B1268257
theorem B1691027 : Blo 1124630 1691027 := bstep (se 1 (by rfl) ⟨1268270, by rfl⟩ : syracuseStep 1691027 = 2536541) B2536541
theorem B1691057 : Blo 1124630 1691057 := bstep (se 2 (by rfl) ⟨634146, by rfl⟩ : syracuseStep 1691057 = 1268293) B1268293
theorem B1691075 : Blo 1124630 1691075 := bstep (se 1 (by rfl) ⟨1268306, by rfl⟩ : syracuseStep 1691075 = 2536613) B2536613
theorem B1691105 : Blo 1124630 1691105 := bstep (se 2 (by rfl) ⟨634164, by rfl⟩ : syracuseStep 1691105 = 1268329) B1268329
theorem B1691123 : Blo 1124630 1691123 := bstep (se 1 (by rfl) ⟨1268342, by rfl⟩ : syracuseStep 1691123 = 2536685) B2536685
theorem B1691153 : Blo 1124630 1691153 := bstep (se 2 (by rfl) ⟨634182, by rfl⟩ : syracuseStep 1691153 = 1268365) B1268365
theorem B1953299 : Blo 1124630 1953299 := bstep (se 1 (by rfl) ⟨1464974, by rfl⟩ : syracuseStep 1953299 = 2929949) B2929949
theorem B1691171 : Blo 1124630 1691171 := bstep (se 1 (by rfl) ⟨1268378, by rfl⟩ : syracuseStep 1691171 = 2536757) B2536757
theorem B1691201 : Blo 1124630 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B1691219 : Blo 1124630 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B1265251 : Blo 1124630 1265251 := bstep (se 1 (by rfl) ⟨948938, by rfl⟩ : syracuseStep 1265251 = 1897877) B1897877
theorem B1691249 : Blo 1124630 1691249 := bstep (se 2 (by rfl) ⟨634218, by rfl⟩ : syracuseStep 1691249 = 1268437) B1268437
theorem B1691267 : Blo 1124630 1691267 := bstep (se 1 (by rfl) ⟨1268450, by rfl⟩ : syracuseStep 1691267 = 2536901) B2536901
theorem B1691297 : Blo 1124630 1691297 := bstep (se 2 (by rfl) ⟨634236, by rfl⟩ : syracuseStep 1691297 = 1268473) B1268473
theorem B3296941 : Blo 1124630 3296941 := bstep (se 3 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 3296941 = 1236353) B1236353
theorem B1691315 : Blo 1124630 1691315 := bstep (se 1 (by rfl) ⟨1268486, by rfl⟩ : syracuseStep 1691315 = 2536973) B2536973
theorem B7720645 : Blo 1124630 7720645 := bstep (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) B1447621
theorem B6082253 : Blo 1124630 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B1691345 : Blo 1124630 1691345 := bstep (se 2 (by rfl) ⟨634254, by rfl⟩ : syracuseStep 1691345 = 1268509) B1268509
theorem B1691363 : Blo 1124630 1691363 := bstep (se 1 (by rfl) ⟨1268522, by rfl⟩ : syracuseStep 1691363 = 2537045) B2537045
theorem B1265395 : Blo 1124630 1265395 := bstep (se 1 (by rfl) ⟨949046, by rfl⟩ : syracuseStep 1265395 = 1898093) B1898093
theorem B1691393 : Blo 1124630 1691393 := bstep (se 2 (by rfl) ⟨634272, by rfl⟩ : syracuseStep 1691393 = 1268545) B1268545
theorem B1691411 : Blo 1124630 1691411 := bstep (se 1 (by rfl) ⟨1268558, by rfl⟩ : syracuseStep 1691411 = 2537117) B2537117
theorem B1691441 : Blo 1124630 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B1691459 : Blo 1124630 1691459 := bstep (se 1 (by rfl) ⟨1268594, by rfl⟩ : syracuseStep 1691459 = 2537189) B2537189
theorem B4804429 : Blo 1124630 4804429 := bstep (se 3 (by rfl) ⟨900830, by rfl⟩ : syracuseStep 4804429 = 1801661) B1801661
theorem B6082381 : Blo 1124630 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B4280141 : Blo 1124630 4280141 := bstep (se 3 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 4280141 = 1605053) B1605053
theorem B1691489 : Blo 1124630 1691489 := bstep (se 2 (by rfl) ⟨634308, by rfl⟩ : syracuseStep 1691489 = 1268617) B1268617
theorem B1691507 : Blo 1124630 1691507 := bstep (se 1 (by rfl) ⟨1268630, by rfl⟩ : syracuseStep 1691507 = 2537261) B2537261
theorem B1265539 : Blo 1124630 1265539 := bstep (se 1 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 1265539 = 1898309) B1898309
theorem B1691537 : Blo 1124630 1691537 := bstep (se 2 (by rfl) ⟨634326, by rfl⟩ : syracuseStep 1691537 = 1268653) B1268653
theorem B1691555 : Blo 1124630 1691555 := bstep (se 1 (by rfl) ⟨1268666, by rfl⟩ : syracuseStep 1691555 = 2537333) B2537333
theorem B1691585 : Blo 1124630 1691585 := bstep (se 2 (by rfl) ⟨634344, by rfl⟩ : syracuseStep 1691585 = 1268689) B1268689
theorem B1691603 : Blo 1124630 1691603 := bstep (se 1 (by rfl) ⟨1268702, by rfl⟩ : syracuseStep 1691603 = 2537405) B2537405
theorem B1691633 : Blo 1124630 1691633 := bstep (se 2 (by rfl) ⟨634362, by rfl⟩ : syracuseStep 1691633 = 1268725) B1268725
theorem B1691651 : Blo 1124630 1691651 := bstep (se 1 (by rfl) ⟨1268738, by rfl⟩ : syracuseStep 1691651 = 2537477) B2537477
theorem B1265683 : Blo 1124630 1265683 := bstep (se 1 (by rfl) ⟨949262, by rfl⟩ : syracuseStep 1265683 = 1898525) B1898525
theorem B1691681 : Blo 1124630 1691681 := bstep (se 2 (by rfl) ⟨634380, by rfl⟩ : syracuseStep 1691681 = 1268761) B1268761
theorem B1691699 : Blo 1124630 1691699 := bstep (se 1 (by rfl) ⟨1268774, by rfl⟩ : syracuseStep 1691699 = 2537549) B2537549
theorem B1953857 : Blo 1124630 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B1691729 : Blo 1124630 1691729 := bstep (se 2 (by rfl) ⟨634398, by rfl⟩ : syracuseStep 1691729 = 1268797) B1268797
theorem B1691747 : Blo 1124630 1691747 := bstep (se 1 (by rfl) ⟨1268810, by rfl⟩ : syracuseStep 1691747 = 2537621) B2537621
theorem B10834033 : Blo 1124630 10834033 := bstep (se 2 (by rfl) ⟨4062762, by rfl⟩ : syracuseStep 10834033 = 8125525) B8125525
theorem B1691777 : Blo 1124630 1691777 := bstep (se 2 (by rfl) ⟨634416, by rfl⟩ : syracuseStep 1691777 = 1268833) B1268833
theorem B1691795 : Blo 1124630 1691795 := bstep (se 1 (by rfl) ⟨1268846, by rfl⟩ : syracuseStep 1691795 = 2537693) B2537693
theorem B4804771 : Blo 1124630 4804771 := bstep (se 1 (by rfl) ⟨3603578, by rfl⟩ : syracuseStep 4804771 = 7207157) B7207157
theorem B1265827 : Blo 1124630 1265827 := bstep (se 1 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 1265827 = 1898741) B1898741
theorem B1691825 : Blo 1124630 1691825 := bstep (se 2 (by rfl) ⟨634434, by rfl⟩ : syracuseStep 1691825 = 1268869) B1268869
theorem B1691843 : Blo 1124630 1691843 := bstep (se 1 (by rfl) ⟨1268882, by rfl⟩ : syracuseStep 1691843 = 2537765) B2537765
theorem B1691873 : Blo 1124630 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B30888163 : Blo 1124630 30888163 := bstep (se 1 (by rfl) ⟨23166122, by rfl⟩ : syracuseStep 30888163 = 46332245) B46332245
theorem B1691891 : Blo 1124630 1691891 := bstep (se 1 (by rfl) ⟨1268918, by rfl⟩ : syracuseStep 1691891 = 2537837) B2537837
theorem B1691921 : Blo 1124630 1691921 := bstep (se 2 (by rfl) ⟨634470, by rfl⟩ : syracuseStep 1691921 = 1268941) B1268941
theorem B1691939 : Blo 1124630 1691939 := bstep (se 1 (by rfl) ⟨1268954, by rfl⟩ : syracuseStep 1691939 = 2537909) B2537909
theorem B5132593 : Blo 1124630 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1265971 : Blo 1124630 1265971 := bstep (se 1 (by rfl) ⟨949478, by rfl⟩ : syracuseStep 1265971 = 1898957) B1898957
theorem B1691969 : Blo 1124630 1691969 := bstep (se 2 (by rfl) ⟨634488, by rfl⟩ : syracuseStep 1691969 = 1268977) B1268977
theorem B1691987 : Blo 1124630 1691987 := bstep (se 1 (by rfl) ⟨1268990, by rfl⟩ : syracuseStep 1691987 = 2537981) B2537981
theorem B1692017 : Blo 1124630 1692017 := bstep (se 2 (by rfl) ⟨634506, by rfl⟩ : syracuseStep 1692017 = 1269013) B1269013
theorem B1692035 : Blo 1124630 1692035 := bstep (se 1 (by rfl) ⟨1269026, by rfl⟩ : syracuseStep 1692035 = 2538053) B2538053
theorem B1692065 : Blo 1124630 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1692083 : Blo 1124630 1692083 := bstep (se 1 (by rfl) ⟨1269062, by rfl⟩ : syracuseStep 1692083 = 2538125) B2538125
theorem B1266115 : Blo 1124630 1266115 := bstep (se 1 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 1266115 = 1899173) B1899173
theorem B1692113 : Blo 1124630 1692113 := bstep (se 2 (by rfl) ⟨634542, by rfl⟩ : syracuseStep 1692113 = 1269085) B1269085
theorem B1692131 : Blo 1124630 1692131 := bstep (se 1 (by rfl) ⟨1269098, by rfl⟩ : syracuseStep 1692131 = 2538197) B2538197
theorem B1692161 : Blo 1124630 1692161 := bstep (se 2 (by rfl) ⟨634560, by rfl⟩ : syracuseStep 1692161 = 1269121) B1269121
theorem B1692179 : Blo 1124630 1692179 := bstep (se 1 (by rfl) ⟨1269134, by rfl⟩ : syracuseStep 1692179 = 2538269) B2538269
theorem B1692209 : Blo 1124630 1692209 := bstep (se 2 (by rfl) ⟨634578, by rfl⟩ : syracuseStep 1692209 = 1269157) B1269157
theorem B1692227 : Blo 1124630 1692227 := bstep (se 1 (by rfl) ⟨1269170, by rfl⟩ : syracuseStep 1692227 = 2538341) B2538341
theorem B1266259 : Blo 1124630 1266259 := bstep (se 1 (by rfl) ⟨949694, by rfl⟩ : syracuseStep 1266259 = 1899389) B1899389
theorem B1692257 : Blo 1124630 1692257 := bstep (se 2 (by rfl) ⟨634596, by rfl⟩ : syracuseStep 1692257 = 1269193) B1269193
theorem B1692275 : Blo 1124630 1692275 := bstep (se 1 (by rfl) ⟨1269206, by rfl⟩ : syracuseStep 1692275 = 2538413) B2538413
theorem B1692305 : Blo 1124630 1692305 := bstep (se 2 (by rfl) ⟨634614, by rfl⟩ : syracuseStep 1692305 = 1269229) B1269229
theorem B1692323 : Blo 1124630 1692323 := bstep (se 1 (by rfl) ⟨1269242, by rfl⟩ : syracuseStep 1692323 = 2538485) B2538485
theorem B1692353 : Blo 1124630 1692353 := bstep (se 2 (by rfl) ⟨634632, by rfl⟩ : syracuseStep 1692353 = 1269265) B1269265
theorem B1692371 : Blo 1124630 1692371 := bstep (se 1 (by rfl) ⟨1269278, by rfl⟩ : syracuseStep 1692371 = 2538557) B2538557
theorem B1266403 : Blo 1124630 1266403 := bstep (se 1 (by rfl) ⟨949802, by rfl⟩ : syracuseStep 1266403 = 1899605) B1899605
theorem B1692401 : Blo 1124630 1692401 := bstep (se 2 (by rfl) ⟨634650, by rfl⟩ : syracuseStep 1692401 = 1269301) B1269301
theorem B1692419 : Blo 1124630 1692419 := bstep (se 1 (by rfl) ⟨1269314, by rfl⟩ : syracuseStep 1692419 = 2538629) B2538629
theorem B1692449 : Blo 1124630 1692449 := bstep (se 2 (by rfl) ⟨634668, by rfl⟩ : syracuseStep 1692449 = 1269337) B1269337
theorem B1692467 : Blo 1124630 1692467 := bstep (se 1 (by rfl) ⟨1269350, by rfl⟩ : syracuseStep 1692467 = 2538701) B2538701
theorem B1692497 : Blo 1124630 1692497 := bstep (se 2 (by rfl) ⟨634686, by rfl⟩ : syracuseStep 1692497 = 1269373) B1269373
theorem B1692515 : Blo 1124630 1692515 := bstep (se 1 (by rfl) ⟨1269386, by rfl⟩ : syracuseStep 1692515 = 2538773) B2538773
theorem B1266547 : Blo 1124630 1266547 := bstep (se 1 (by rfl) ⟨949910, by rfl⟩ : syracuseStep 1266547 = 1899821) B1899821
theorem B1692545 : Blo 1124630 1692545 := bstep (se 2 (by rfl) ⟨634704, by rfl⟩ : syracuseStep 1692545 = 1269409) B1269409
theorem B1692563 : Blo 1124630 1692563 := bstep (se 1 (by rfl) ⟨1269422, by rfl⟩ : syracuseStep 1692563 = 2538845) B2538845
theorem B3429283 : Blo 1124630 3429283 := bstep (se 1 (by rfl) ⟨2571962, by rfl⟩ : syracuseStep 3429283 = 5143925) B5143925
theorem B1692593 : Blo 1124630 1692593 := bstep (se 2 (by rfl) ⟨634722, by rfl⟩ : syracuseStep 1692593 = 1269445) B1269445
theorem B1692611 : Blo 1124630 1692611 := bstep (se 1 (by rfl) ⟨1269458, by rfl⟩ : syracuseStep 1692611 = 2538917) B2538917
theorem B1692641 : Blo 1124630 1692641 := bstep (se 2 (by rfl) ⟨634740, by rfl⟩ : syracuseStep 1692641 = 1269481) B1269481
theorem B1692659 : Blo 1124630 1692659 := bstep (se 1 (by rfl) ⟨1269494, by rfl⟩ : syracuseStep 1692659 = 2538989) B2538989
theorem B1266691 : Blo 1124630 1266691 := bstep (se 1 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 1266691 = 1900037) B1900037
theorem B1692689 : Blo 1124630 1692689 := bstep (se 2 (by rfl) ⟨634758, by rfl⟩ : syracuseStep 1692689 = 1269517) B1269517
theorem B1692707 : Blo 1124630 1692707 := bstep (se 1 (by rfl) ⟨1269530, by rfl⟩ : syracuseStep 1692707 = 2539061) B2539061
theorem B1692737 : Blo 1124630 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B1692755 : Blo 1124630 1692755 := bstep (se 1 (by rfl) ⟨1269566, by rfl⟩ : syracuseStep 1692755 = 2539133) B2539133
theorem B1692785 : Blo 1124630 1692785 := bstep (se 2 (by rfl) ⟨634794, by rfl⟩ : syracuseStep 1692785 = 1269589) B1269589
theorem B1692803 : Blo 1124630 1692803 := bstep (se 1 (by rfl) ⟨1269602, by rfl⟩ : syracuseStep 1692803 = 2539205) B2539205
theorem B1266835 : Blo 1124630 1266835 := bstep (se 1 (by rfl) ⟨950126, by rfl⟩ : syracuseStep 1266835 = 1900253) B1900253
theorem B1692833 : Blo 1124630 1692833 := bstep (se 2 (by rfl) ⟨634812, by rfl⟩ : syracuseStep 1692833 = 1269625) B1269625
theorem B2741411 : Blo 1124630 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B1692851 : Blo 1124630 1692851 := bstep (se 1 (by rfl) ⟨1269638, by rfl⟩ : syracuseStep 1692851 = 2539277) B2539277
theorem B1692881 : Blo 1124630 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B1692899 : Blo 1124630 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B1692929 : Blo 1124630 1692929 := bstep (se 2 (by rfl) ⟨634848, by rfl⟩ : syracuseStep 1692929 = 1269697) B1269697
theorem B1955075 : Blo 1124630 1955075 := bstep (se 1 (by rfl) ⟨1466306, by rfl⟩ : syracuseStep 1955075 = 2932613) B2932613
theorem B1266979 : Blo 1124630 1266979 := bstep (se 1 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 1266979 = 1900469) B1900469
theorem B5133709 : Blo 1124630 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1267123 : Blo 1124630 1267123 := bstep (se 1 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 1267123 = 1900685) B1900685
theorem B1201603 : Blo 1124630 1201603 := bstep (se 1 (by rfl) ⟨901202, by rfl⟩ : syracuseStep 1201603 = 1802405) B1802405
theorem B6084067 : Blo 1124630 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B6346289 : Blo 1124630 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B1267267 : Blo 1124630 1267267 := bstep (se 1 (by rfl) ⟨950450, by rfl⟩ : syracuseStep 1267267 = 1900901) B1900901
theorem B1267411 : Blo 1124630 1267411 := bstep (se 1 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 1267411 = 1901117) B1901117
theorem B7231301 : Blo 1124630 7231301 := bstep (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) B1355869
theorem B1267555 : Blo 1124630 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B4282253 : Blo 1124630 4282253 := bstep (se 3 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 4282253 = 1605845) B1605845
theorem B1267699 : Blo 1124630 1267699 := bstep (se 1 (by rfl) ⟨950774, by rfl⟩ : syracuseStep 1267699 = 1901549) B1901549
theorem B1267843 : Blo 1124630 1267843 := bstep (se 1 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 1267843 = 1901765) B1901765
theorem B1267987 : Blo 1124630 1267987 := bstep (se 1 (by rfl) ⟨950990, by rfl⟩ : syracuseStep 1267987 = 1901981) B1901981
theorem B1202483 : Blo 1124630 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B4872611 : Blo 1124630 4872611 := bstep (se 1 (by rfl) ⟨3654458, by rfl⟩ : syracuseStep 4872611 = 7308917) B7308917
theorem B1268131 : Blo 1124630 1268131 := bstep (se 1 (by rfl) ⟨951098, by rfl⟩ : syracuseStep 1268131 = 1902197) B1902197
theorem B1202611 : Blo 1124630 1202611 := bstep (se 1 (by rfl) ⟨901958, by rfl⟩ : syracuseStep 1202611 = 1803917) B1803917
theorem B14637581 : Blo 1124630 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B1268275 : Blo 1124630 1268275 := bstep (se 1 (by rfl) ⟨951206, by rfl⟩ : syracuseStep 1268275 = 1902413) B1902413
theorem B6412877 : Blo 1124630 6412877 := bstep (se 3 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 6412877 = 2404829) B2404829
theorem B2316899 : Blo 1124630 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B4283057 : Blo 1124630 4283057 := bstep (se 2 (by rfl) ⟨1606146, by rfl⟩ : syracuseStep 4283057 = 3212293) B3212293
theorem B1268419 : Blo 1124630 1268419 := bstep (se 1 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 1268419 = 1902629) B1902629
theorem B1268563 : Blo 1124630 1268563 := bstep (se 1 (by rfl) ⟨951422, by rfl⟩ : syracuseStep 1268563 = 1902845) B1902845
theorem B1268707 : Blo 1124630 1268707 := bstep (se 1 (by rfl) ⟨951530, by rfl⟩ : syracuseStep 1268707 = 1903061) B1903061
theorem B1268851 : Blo 1124630 1268851 := bstep (se 1 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 1268851 = 1903277) B1903277
theorem B1203427 : Blo 1124630 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B1268995 : Blo 1124630 1268995 := bstep (se 1 (by rfl) ⟨951746, by rfl⟩ : syracuseStep 1268995 = 1903493) B1903493
theorem B4283725 : Blo 1124630 4283725 := bstep (se 3 (by rfl) ⟨803198, by rfl⟩ : syracuseStep 4283725 = 1606397) B1606397
theorem B1269139 : Blo 1124630 1269139 := bstep (se 1 (by rfl) ⟨951854, by rfl⟩ : syracuseStep 1269139 = 1903709) B1903709
theorem B5496227 : Blo 1124630 5496227 := bstep (se 1 (by rfl) ⟨4122170, by rfl⟩ : syracuseStep 5496227 = 8244341) B8244341
theorem B1269283 : Blo 1124630 1269283 := bstep (se 1 (by rfl) ⟨951962, by rfl⟩ : syracuseStep 1269283 = 1903925) B1903925
theorem B9625229 : Blo 1124630 9625229 := bstep (se 3 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 9625229 = 3609461) B3609461
theorem B4054691 : Blo 1124630 4054691 := bstep (se 1 (by rfl) ⟨3041018, by rfl⟩ : syracuseStep 4054691 = 6082037) B6082037
theorem B1564337 : Blo 1124630 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B1269427 : Blo 1124630 1269427 := bstep (se 1 (by rfl) ⟨952070, by rfl⟩ : syracuseStep 1269427 = 1904141) B1904141
theorem B1269571 : Blo 1124630 1269571 := bstep (se 1 (by rfl) ⟨952178, by rfl⟩ : syracuseStep 1269571 = 1904357) B1904357
theorem B5693489 : Blo 1124630 5693489 := bstep (se 2 (by rfl) ⟨2135058, by rfl⟩ : syracuseStep 5693489 = 4270117) B4270117
theorem B1925201 : Blo 1124630 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B4808803 : Blo 1124630 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B4284515 : Blo 1124630 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B3203363 : Blo 1124630 3203363 := bstep (se 1 (by rfl) ⟨2402522, by rfl⟩ : syracuseStep 3203363 = 4805045) B4805045
theorem B21422789 : Blo 1124630 21422789 := bstep (se 4 (by rfl) ⟨2008386, by rfl⟩ : syracuseStep 21422789 = 4016773) B4016773
theorem B6841073 : Blo 1124630 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B4285169 : Blo 1124630 4285169 := bstep (se 2 (by rfl) ⟨1606938, by rfl⟩ : syracuseStep 4285169 = 3213877) B3213877
theorem B6415109 : Blo 1124630 6415109 := bstep (se 4 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 6415109 = 1202833) B1202833
theorem B3040067 : Blo 1124630 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B6841265 : Blo 1124630 6841265 := bstep (se 2 (by rfl) ⟨2565474, by rfl⟩ : syracuseStep 6841265 = 5130949) B5130949
theorem B4810033 : Blo 1124630 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B6415793 : Blo 1124630 6415793 := bstep (se 2 (by rfl) ⟨2405922, by rfl⟩ : syracuseStep 6415793 = 4811845) B4811845
theorem B5694947 : Blo 1124630 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B3204593 : Blo 1124630 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B2287121 : Blo 1124630 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B5137955 : Blo 1124630 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B6088547 : Blo 1124630 6088547 := bstep (se 1 (by rfl) ⟨4566410, by rfl⟩ : syracuseStep 6088547 = 9132821) B9132821
theorem B5695757 : Blo 1124630 5695757 := bstep (se 3 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 5695757 = 2135909) B2135909
theorem B9136739 : Blo 1124630 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B6417251 : Blo 1124630 6417251 := bstep (se 1 (by rfl) ⟨4812938, by rfl⟩ : syracuseStep 6417251 = 9625877) B9625877
theorem B3795821 : Blo 1124630 3795821 := bstep (se 3 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 3795821 = 1423433) B1423433
theorem B3795875 : Blo 1124630 3795875 := bstep (se 1 (by rfl) ⟨2846906, by rfl⟩ : syracuseStep 3795875 = 5693813) B5693813
theorem B3206051 : Blo 1124630 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B3042467 : Blo 1124630 3042467 := bstep (se 1 (by rfl) ⟨2281850, by rfl⟩ : syracuseStep 3042467 = 4563701) B4563701
theorem B3796145 : Blo 1124630 3796145 := bstep (se 2 (by rfl) ⟨1423554, by rfl⟩ : syracuseStep 3796145 = 2847109) B2847109
theorem B1141939 : Blo 1124630 1141939 := bstep (se 1 (by rfl) ⟨856454, by rfl⟩ : syracuseStep 1141939 = 1712909) B1712909
theorem B21687749 : Blo 1124630 21687749 := bstep (se 4 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 21687749 = 4066453) B4066453
theorem B8678897 : Blo 1124630 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B30797333 : Blo 1124630 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B3796685 : Blo 1124630 3796685 := bstep (se 3 (by rfl) ⟨711878, by rfl⟩ : syracuseStep 3796685 = 1423757) B1423757
theorem B3206861 : Blo 1124630 3206861 := bstep (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) B1202573
theorem B3796739 : Blo 1124630 3796739 := bstep (se 1 (by rfl) ⟨2847554, by rfl⟩ : syracuseStep 3796739 = 5695109) B5695109
theorem B3207053 : Blo 1124630 3207053 := bstep (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) B1202645
theorem B3797009 : Blo 1124630 3797009 := bstep (se 2 (by rfl) ⟨1423878, by rfl⟩ : syracuseStep 3797009 = 2847757) B2847757
theorem B2846897 : Blo 1124630 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B2846947 : Blo 1124630 2846947 := bstep (se 1 (by rfl) ⟨2135210, by rfl⟩ : syracuseStep 2846947 = 4270421) B4270421
theorem B2847089 : Blo 1124630 2847089 := bstep (se 2 (by rfl) ⟨1067658, by rfl⟩ : syracuseStep 2847089 = 2135317) B2135317
theorem B1929635 : Blo 1124630 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B12186125 : Blo 1124630 12186125 := bstep (se 3 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 12186125 = 4569797) B4569797
theorem B3797549 : Blo 1124630 3797549 := bstep (se 3 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 3797549 = 1424081) B1424081
theorem B3797603 : Blo 1124630 3797603 := bstep (se 1 (by rfl) ⟨2848202, by rfl⟩ : syracuseStep 3797603 = 5696405) B5696405
theorem B3044099 : Blo 1124630 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B1602337 : Blo 1124630 1602337 := bstep (se 2 (by rfl) ⟨600876, by rfl⟩ : syracuseStep 1602337 = 1201753) B1201753
theorem B4059953 : Blo 1124630 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B3208045 : Blo 1124630 3208045 := bstep (se 3 (by rfl) ⟨601508, by rfl⟩ : syracuseStep 3208045 = 1203017) B1203017
theorem B3797873 : Blo 1124630 3797873 := bstep (se 2 (by rfl) ⟨1424202, by rfl⟩ : syracuseStep 3797873 = 2848405) B2848405
theorem B1602433 : Blo 1124630 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B5698673 : Blo 1124630 5698673 := bstep (se 2 (by rfl) ⟨2137002, by rfl⟩ : syracuseStep 5698673 = 4274005) B4274005
theorem B7206029 : Blo 1124630 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B2848081 : Blo 1124630 2848081 := bstep (se 2 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 2848081 = 2136061) B2136061
theorem B1602929 : Blo 1124630 1602929 := bstep (se 2 (by rfl) ⟨601098, by rfl⟩ : syracuseStep 1602929 = 1202197) B1202197
theorem B1897843 : Blo 1124630 1897843 := bstep (se 1 (by rfl) ⟨1423382, by rfl⟩ : syracuseStep 1897843 = 2846765) B2846765
theorem B3798413 : Blo 1124630 3798413 := bstep (se 3 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 3798413 = 1424405) B1424405
theorem B3798467 : Blo 1124630 3798467 := bstep (se 1 (by rfl) ⟨2848850, by rfl⟩ : syracuseStep 3798467 = 5697701) B5697701
theorem B1734097 : Blo 1124630 1734097 := bstep (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) B1300573
theorem B1897985 : Blo 1124630 1897985 := bstep (se 2 (by rfl) ⟨711744, by rfl⟩ : syracuseStep 1897985 = 1423489) B1423489
theorem B2848355 : Blo 1124630 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B2029169 : Blo 1124630 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B1898113 : Blo 1124630 1898113 := bstep (se 2 (by rfl) ⟨711792, by rfl⟩ : syracuseStep 1898113 = 1423585) B1423585
theorem B9139853 : Blo 1124630 9139853 := bstep (se 3 (by rfl) ⟨1713722, by rfl⟩ : syracuseStep 9139853 = 3427445) B3427445
theorem B4814477 : Blo 1124630 4814477 := bstep (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) B1805429
theorem B1898147 : Blo 1124630 1898147 := bstep (se 1 (by rfl) ⟨1423610, by rfl⟩ : syracuseStep 1898147 = 2847221) B2847221
theorem B3798737 : Blo 1124630 3798737 := bstep (se 2 (by rfl) ⟨1424526, by rfl⟩ : syracuseStep 3798737 = 2849053) B2849053
theorem B6944525 : Blo 1124630 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B1898275 : Blo 1124630 1898275 := bstep (se 1 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 1898275 = 2847413) B2847413
theorem B2848547 : Blo 1124630 2848547 := bstep (se 1 (by rfl) ⟨2136410, by rfl⟩ : syracuseStep 2848547 = 4272821) B4272821
theorem B1898417 : Blo 1124630 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B6420485 : Blo 1124630 6420485 := bstep (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) B1203841
theorem B1898545 : Blo 1124630 1898545 := bstep (se 2 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 1898545 = 1423909) B1423909
theorem B1898579 : Blo 1124630 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B32897137 : Blo 1124630 32897137 := bstep (se 2 (by rfl) ⟨12336426, by rfl⟩ : syracuseStep 32897137 = 24672853) B24672853
theorem B3045539 : Blo 1124630 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B3471569 : Blo 1124630 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B1898707 : Blo 1124630 1898707 := bstep (se 1 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 1898707 = 2848061) B2848061
theorem B1603795 : Blo 1124630 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B3799277 : Blo 1124630 3799277 := bstep (se 3 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 3799277 = 1424729) B1424729
theorem B3799331 : Blo 1124630 3799331 := bstep (se 1 (by rfl) ⟨2849498, by rfl⟩ : syracuseStep 3799331 = 5698997) B5698997
theorem B1603891 : Blo 1124630 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B1898849 : Blo 1124630 1898849 := bstep (se 2 (by rfl) ⟨712068, by rfl⟩ : syracuseStep 1898849 = 1424137) B1424137
theorem B6420941 : Blo 1124630 6420941 := bstep (se 3 (by rfl) ⟨1203926, by rfl⟩ : syracuseStep 6420941 = 2407853) B2407853
theorem B1898977 : Blo 1124630 1898977 := bstep (se 2 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 1898977 = 1424233) B1424233
theorem B1899011 : Blo 1124630 1899011 := bstep (se 1 (by rfl) ⟨1424258, by rfl⟩ : syracuseStep 1899011 = 2848517) B2848517
theorem B5700131 : Blo 1124630 5700131 := bstep (se 1 (by rfl) ⟨4275098, by rfl⟩ : syracuseStep 5700131 = 8550197) B8550197
theorem B3799601 : Blo 1124630 3799601 := bstep (se 2 (by rfl) ⟨1424850, by rfl⟩ : syracuseStep 3799601 = 2849701) B2849701
theorem B3209777 : Blo 1124630 3209777 := bstep (se 2 (by rfl) ⟨1203666, by rfl⟩ : syracuseStep 3209777 = 2407333) B2407333
theorem B1899139 : Blo 1124630 1899139 := bstep (se 1 (by rfl) ⟨1424354, by rfl⟩ : syracuseStep 1899139 = 2848709) B2848709
theorem B2849489 : Blo 1124630 2849489 := bstep (se 2 (by rfl) ⟨1068558, by rfl⟩ : syracuseStep 2849489 = 2137117) B2137117
theorem B3209969 : Blo 1124630 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B2849539 : Blo 1124630 2849539 := bstep (se 1 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 2849539 = 4274309) B4274309
theorem B1899281 : Blo 1124630 1899281 := bstep (se 2 (by rfl) ⟨712230, by rfl⟩ : syracuseStep 1899281 = 1424461) B1424461
theorem B1604387 : Blo 1124630 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B1735553 : Blo 1124630 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1899409 : Blo 1124630 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B2849681 : Blo 1124630 2849681 := bstep (se 2 (by rfl) ⟨1068630, by rfl⟩ : syracuseStep 2849681 = 2137261) B2137261
theorem B1899443 : Blo 1124630 1899443 := bstep (se 1 (by rfl) ⟨1424582, by rfl⟩ : syracuseStep 1899443 = 2849165) B2849165
theorem B3046349 : Blo 1124630 3046349 := bstep (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) B1142381
theorem B3046403 : Blo 1124630 3046403 := bstep (se 1 (by rfl) ⟨2284802, by rfl⟩ : syracuseStep 3046403 = 4569605) B4569605
theorem B1899571 : Blo 1124630 1899571 := bstep (se 1 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 1899571 = 2849357) B2849357
theorem B3800141 : Blo 1124630 3800141 := bstep (se 3 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 3800141 = 1425053) B1425053
theorem B3800195 : Blo 1124630 3800195 := bstep (se 1 (by rfl) ⟨2850146, by rfl⟩ : syracuseStep 3800195 = 5700293) B5700293
theorem B12811445 : Blo 1124630 12811445 := bstep (se 5 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 12811445 = 1201073) B1201073
theorem B1899713 : Blo 1124630 1899713 := bstep (se 2 (by rfl) ⟨712392, by rfl⟩ : syracuseStep 1899713 = 1424785) B1424785
theorem B1899841 : Blo 1124630 1899841 := bstep (se 2 (by rfl) ⟨712440, by rfl⟩ : syracuseStep 1899841 = 1424881) B1424881
theorem B7208261 : Blo 1124630 7208261 := bstep (se 4 (by rfl) ⟨675774, by rfl⟩ : syracuseStep 7208261 = 1351549) B1351549
theorem B5700941 : Blo 1124630 5700941 := bstep (se 3 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 5700941 = 2137853) B2137853
theorem B1899875 : Blo 1124630 1899875 := bstep (se 1 (by rfl) ⟨1424906, by rfl⟩ : syracuseStep 1899875 = 2849813) B2849813
theorem B3800465 : Blo 1124630 3800465 := bstep (se 2 (by rfl) ⟨1425174, by rfl⟩ : syracuseStep 3800465 = 2850349) B2850349
theorem B1605025 : Blo 1124630 1605025 := bstep (se 2 (by rfl) ⟨601884, by rfl⟩ : syracuseStep 1605025 = 1203769) B1203769
theorem B1900003 : Blo 1124630 1900003 := bstep (se 1 (by rfl) ⟨1425002, by rfl⟩ : syracuseStep 1900003 = 2850005) B2850005
theorem B1801777 : Blo 1124630 1801777 := bstep (se 2 (by rfl) ⟨675666, by rfl⟩ : syracuseStep 1801777 = 1351333) B1351333
theorem B1900145 : Blo 1124630 1900145 := bstep (se 2 (by rfl) ⟨712554, by rfl⟩ : syracuseStep 1900145 = 1425109) B1425109
theorem B3210961 : Blo 1124630 3210961 := bstep (se 2 (by rfl) ⟨1204110, by rfl⟩ : syracuseStep 3210961 = 2408221) B2408221
theorem B1900273 : Blo 1124630 1900273 := bstep (se 2 (by rfl) ⟨712602, by rfl⟩ : syracuseStep 1900273 = 1425205) B1425205
theorem B1605361 : Blo 1124630 1605361 := bstep (se 2 (by rfl) ⟨602010, by rfl⟩ : syracuseStep 1605361 = 1204021) B1204021
theorem B1900307 : Blo 1124630 1900307 := bstep (se 1 (by rfl) ⟨1425230, by rfl⟩ : syracuseStep 1900307 = 2850461) B2850461
theorem B2850673 : Blo 1124630 2850673 := bstep (se 2 (by rfl) ⟨1069002, by rfl⟩ : syracuseStep 2850673 = 2138005) B2138005
theorem B19267469 : Blo 1124630 19267469 := bstep (se 3 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 19267469 = 7225301) B7225301
theorem B1900435 : Blo 1124630 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B3801005 : Blo 1124630 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B3801059 : Blo 1124630 3801059 := bstep (se 1 (by rfl) ⟨2850794, by rfl⟩ : syracuseStep 3801059 = 5701589) B5701589
theorem B3211235 : Blo 1124630 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B1900631 : Blo 1124630 1900631 := bstep (se 1 (by rfl) ⟨1425473, by rfl⟩ : syracuseStep 1900631 = 2850947) B2850947
theorem B8552627 : Blo 1124630 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B1900759 : Blo 1124630 1900759 := bstep (se 1 (by rfl) ⟨1425569, by rfl⟩ : syracuseStep 1900759 = 2851139) B2851139
theorem B11731205 : Blo 1124630 11731205 := bstep (se 4 (by rfl) ⟨1099800, by rfl⟩ : syracuseStep 11731205 = 2199601) B2199601
theorem B2031959 : Blo 1124630 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B3801437 : Blo 1124630 3801437 := bstep (se 3 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 3801437 = 1425539) B1425539
theorem B8126851 : Blo 1124630 8126851 := bstep (se 1 (by rfl) ⟨6095138, by rfl⟩ : syracuseStep 8126851 = 12190277) B12190277
theorem B5702237 : Blo 1124630 5702237 := bstep (se 3 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 5702237 = 2138339) B2138339
theorem B1802969 : Blo 1124630 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B4064003 : Blo 1124630 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B9634625 : Blo 1124630 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B1901387 : Blo 1124630 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B1803161 : Blo 1124630 1803161 := bstep (se 2 (by rfl) ⟨676185, by rfl⟩ : syracuseStep 1803161 = 1352371) B1352371
theorem B3474355 : Blo 1124630 3474355 := bstep (se 1 (by rfl) ⟨2605766, by rfl⟩ : syracuseStep 3474355 = 5211533) B5211533
theorem B3048371 : Blo 1124630 3048371 := bstep (se 1 (by rfl) ⟨2286278, by rfl⟩ : syracuseStep 3048371 = 4572557) B4572557
theorem B2851787 : Blo 1124630 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B1901515 : Blo 1124630 1901515 := bstep (se 1 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 1901515 = 2852273) B2852273
theorem B1901657 : Blo 1124630 1901657 := bstep (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) B1426243
theorem B1606807 : Blo 1124630 1606807 := bstep (se 1 (by rfl) ⟨1205105, by rfl⟩ : syracuseStep 1606807 = 2410211) B2410211
theorem B1901785 : Blo 1124630 1901785 := bstep (se 2 (by rfl) ⟨713169, by rfl⟩ : syracuseStep 1901785 = 1426339) B1426339
theorem B3212567 : Blo 1124630 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B12846437 : Blo 1124630 12846437 := bstep (se 4 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 12846437 = 2408707) B2408707
theorem B3802571 : Blo 1124630 3802571 := bstep (se 1 (by rfl) ⟨2851928, by rfl⟩ : syracuseStep 3802571 = 5703857) B5703857
theorem B6424109 : Blo 1124630 6424109 := bstep (se 3 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 6424109 = 2409041) B2409041
theorem B8554085 : Blo 1124630 8554085 := bstep (se 4 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 8554085 = 1603891) B1603891
theorem B3802841 : Blo 1124630 3802841 := bstep (se 2 (by rfl) ⟨1426065, by rfl⟩ : syracuseStep 3802841 = 2852131) B2852131
theorem B4065041 : Blo 1124630 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B3606295 : Blo 1124630 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B1902359 : Blo 1124630 1902359 := bstep (se 1 (by rfl) ⟨1426769, by rfl⟩ : syracuseStep 1902359 = 2853539) B2853539
theorem B2033495 : Blo 1124630 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B4818781 : Blo 1124630 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B4065155 : Blo 1124630 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B2852759 : Blo 1124630 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B1902487 : Blo 1124630 1902487 := bstep (se 1 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 1902487 = 2853731) B2853731
theorem B8554571 : Blo 1124630 8554571 := bstep (se 1 (by rfl) ⟨6415928, by rfl⟩ : syracuseStep 8554571 = 12831857) B12831857
theorem B3606859 : Blo 1124630 3606859 := bstep (se 1 (by rfl) ⟨2705144, by rfl⟩ : syracuseStep 3606859 = 5410289) B5410289
theorem B3803543 : Blo 1124630 3803543 := bstep (se 1 (by rfl) ⟨2852657, by rfl⟩ : syracuseStep 3803543 = 5705315) B5705315
theorem B3607001 : Blo 1124630 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B1903115 : Blo 1124630 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B2853427 : Blo 1124630 2853427 := bstep (se 1 (by rfl) ⟨2140070, by rfl⟩ : syracuseStep 2853427 = 4280141) B4280141
theorem B1903243 : Blo 1124630 1903243 := bstep (se 1 (by rfl) ⟨1427432, by rfl⟩ : syracuseStep 1903243 = 2854865) B2854865
theorem B4819601 : Blo 1124630 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B5704343 : Blo 1124630 5704343 := bstep (se 1 (by rfl) ⟨4278257, by rfl⟩ : syracuseStep 5704343 = 8556515) B8556515
theorem B2853569 : Blo 1124630 2853569 := bstep (se 2 (by rfl) ⟨1070088, by rfl⟩ : syracuseStep 2853569 = 2140177) B2140177
theorem B1903385 : Blo 1124630 1903385 := bstep (se 2 (by rfl) ⟨713769, by rfl⟩ : syracuseStep 1903385 = 1427539) B1427539
theorem B1903513 : Blo 1124630 1903513 := bstep (se 2 (by rfl) ⟨713817, by rfl⟩ : syracuseStep 1903513 = 1427635) B1427635
theorem B3804083 : Blo 1124630 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B7310429 : Blo 1124630 7310429 := bstep (se 3 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 7310429 = 2741411) B2741411
theorem B9637015 : Blo 1124630 9637015 := bstep (se 1 (by rfl) ⟨7227761, by rfl⟩ : syracuseStep 9637015 = 14455523) B14455523
theorem B4066483 : Blo 1124630 4066483 := bstep (se 1 (by rfl) ⟨3049862, by rfl⟩ : syracuseStep 4066483 = 6099725) B6099725
theorem B3804353 : Blo 1124630 3804353 := bstep (se 2 (by rfl) ⟨1426632, by rfl⟩ : syracuseStep 3804353 = 2853265) B2853265
theorem B4820269 : Blo 1124630 4820269 := bstep (se 3 (by rfl) ⟨903800, by rfl⟩ : syracuseStep 4820269 = 1807601) B1807601
theorem B5213533 : Blo 1124630 5213533 := bstep (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) B1955075
theorem B8129969 : Blo 1124630 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B1904087 : Blo 1124630 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B1904215 : Blo 1124630 1904215 := bstep (se 1 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 1904215 = 2856323) B2856323
theorem B3608243 : Blo 1124630 3608243 := bstep (se 1 (by rfl) ⟨2706182, by rfl⟩ : syracuseStep 3608243 = 5412365) B5412365
theorem B4230859 : Blo 1124630 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B1543897 : Blo 1124630 1543897 := bstep (se 2 (by rfl) ⟨578961, by rfl⟩ : syracuseStep 1543897 = 1157923) B1157923
theorem B3804893 : Blo 1124630 3804893 := bstep (se 3 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 3804893 = 1426835) B1426835
theorem B4067117 : Blo 1124630 4067117 := bstep (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) B1525169
theorem B6426499 : Blo 1124630 6426499 := bstep (se 1 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 6426499 = 9639749) B9639749
theorem B4820867 : Blo 1124630 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B2854835 : Blo 1124630 2854835 := bstep (se 1 (by rfl) ⟨2141126, by rfl⟩ : syracuseStep 2854835 = 4282253) B4282253
theorem B6098989 : Blo 1124630 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B3608641 : Blo 1124630 3608641 := bstep (se 2 (by rfl) ⟨1353240, by rfl⟩ : syracuseStep 3608641 = 2706481) B2706481
theorem B3248407 : Blo 1124630 3248407 := bstep (se 1 (by rfl) ⟨2436305, by rfl⟩ : syracuseStep 3248407 = 4872611) B4872611
theorem B5411117 : Blo 1124630 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B1544599 : Blo 1124630 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B2855371 : Blo 1124630 2855371 := bstep (se 1 (by rfl) ⟨2141528, by rfl⟩ : syracuseStep 2855371 = 4283057) B4283057
theorem B2855513 : Blo 1124630 2855513 := bstep (se 2 (by rfl) ⟨1070817, by rfl⟩ : syracuseStep 2855513 = 2141635) B2141635
theorem B6427457 : Blo 1124630 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B3806027 : Blo 1124630 3806027 := bstep (se 1 (by rfl) ⟨2854520, by rfl⟩ : syracuseStep 3806027 = 5709041) B5709041
theorem B10294193 : Blo 1124630 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B3806297 : Blo 1124630 3806297 := bstep (se 2 (by rfl) ⟨1427361, by rfl⟩ : syracuseStep 3806297 = 2854723) B2854723
theorem B2856343 : Blo 1124630 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B2135575 : Blo 1124630 2135575 := bstep (se 1 (by rfl) ⟨1601681, by rfl⟩ : syracuseStep 2135575 = 3203363) B3203363
theorem B3806999 : Blo 1124630 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B4560715 : Blo 1124630 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B2856779 : Blo 1124630 2856779 := bstep (se 1 (by rfl) ⟨2142584, by rfl⟩ : syracuseStep 2856779 = 4285169) B4285169
theorem B5707907 : Blo 1124630 5707907 := bstep (se 1 (by rfl) ⟨4280930, by rfl⟩ : syracuseStep 5707907 = 8561861) B8561861
theorem B3807539 : Blo 1124630 3807539 := bstep (se 1 (by rfl) ⟨2855654, by rfl⟩ : syracuseStep 3807539 = 5711309) B5711309
theorem B2136395 : Blo 1124630 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B14817653 : Blo 1124630 14817653 := bstep (se 5 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 14817653 = 1389155) B1389155
theorem B2136449 : Blo 1124630 2136449 := bstep (se 2 (by rfl) ⟨801168, by rfl⟩ : syracuseStep 2136449 = 1602337) B1602337
theorem B3807809 : Blo 1124630 3807809 := bstep (se 2 (by rfl) ⟨1427928, by rfl⟩ : syracuseStep 3807809 = 2855857) B2855857
theorem B4332305 : Blo 1124630 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B3808349 : Blo 1124630 3808349 := bstep (se 3 (by rfl) ⟨714065, by rfl⟩ : syracuseStep 3808349 = 1428131) B1428131
theorem B2530457 : Blo 1124630 2530457 := bstep (se 2 (by rfl) ⟨948921, by rfl⟩ : syracuseStep 2530457 = 1897843) B1897843
theorem B2530547 : Blo 1124630 2530547 := bstep (se 1 (by rfl) ⟨1897910, by rfl⟩ : syracuseStep 2530547 = 3795821) B3795821
theorem B2530583 : Blo 1124630 2530583 := bstep (se 1 (by rfl) ⟨1897937, by rfl⟩ : syracuseStep 2530583 = 3795875) B3795875
theorem B2137367 : Blo 1124630 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B8559917 : Blo 1124630 8559917 := bstep (se 3 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 8559917 = 3209969) B3209969
theorem B2530763 : Blo 1124630 2530763 := bstep (se 1 (by rfl) ⟨1898072, by rfl⟩ : syracuseStep 2530763 = 3796145) B3796145
theorem B2530817 : Blo 1124630 2530817 := bstep (se 2 (by rfl) ⟨949056, by rfl⟩ : syracuseStep 2530817 = 1898113) B1898113
theorem B14458499 : Blo 1124630 14458499 := bstep (se 1 (by rfl) ⟨10843874, by rfl⟩ : syracuseStep 14458499 = 21687749) B21687749
theorem B4628141 : Blo 1124630 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B2531033 : Blo 1124630 2531033 := bstep (se 2 (by rfl) ⟨949137, by rfl⟩ : syracuseStep 2531033 = 1898275) B1898275
theorem B2531123 : Blo 1124630 2531123 := bstep (se 1 (by rfl) ⟨1898342, by rfl⟩ : syracuseStep 2531123 = 3796685) B3796685
theorem B2137907 : Blo 1124630 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B2531159 : Blo 1124630 2531159 := bstep (se 1 (by rfl) ⟨1898369, by rfl⟩ : syracuseStep 2531159 = 3796739) B3796739
theorem B2531339 : Blo 1124630 2531339 := bstep (se 1 (by rfl) ⟨1898504, by rfl⟩ : syracuseStep 2531339 = 3797009) B3797009
theorem B2531393 : Blo 1124630 2531393 := bstep (se 2 (by rfl) ⟨949272, by rfl⟩ : syracuseStep 2531393 = 1898545) B1898545
theorem B1286423 : Blo 1124630 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B2531609 : Blo 1124630 2531609 := bstep (se 2 (by rfl) ⟨949353, by rfl⟩ : syracuseStep 2531609 = 1898707) B1898707
theorem B2138393 : Blo 1124630 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B2531699 : Blo 1124630 2531699 := bstep (se 1 (by rfl) ⟨1898774, by rfl⟩ : syracuseStep 2531699 = 3797549) B3797549
theorem B2531735 : Blo 1124630 2531735 := bstep (se 1 (by rfl) ⟨1898801, by rfl⟩ : syracuseStep 2531735 = 3797603) B3797603
theorem B2531915 : Blo 1124630 2531915 := bstep (se 1 (by rfl) ⟨1898936, by rfl⟩ : syracuseStep 2531915 = 3797873) B3797873
theorem B2531969 : Blo 1124630 2531969 := bstep (se 2 (by rfl) ⟨949488, by rfl⟩ : syracuseStep 2531969 = 1898977) B1898977
theorem B2532185 : Blo 1124630 2532185 := bstep (se 2 (by rfl) ⟨949569, by rfl⟩ : syracuseStep 2532185 = 1899139) B1899139
theorem B2532275 : Blo 1124630 2532275 := bstep (se 1 (by rfl) ⟨1899206, by rfl⟩ : syracuseStep 2532275 = 3798413) B3798413
theorem B2532311 : Blo 1124630 2532311 := bstep (se 1 (by rfl) ⟨1899233, by rfl⟩ : syracuseStep 2532311 = 3798467) B3798467
theorem B2532491 : Blo 1124630 2532491 := bstep (se 1 (by rfl) ⟨1899368, by rfl⟩ : syracuseStep 2532491 = 3798737) B3798737
theorem B4629683 : Blo 1124630 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B2532545 : Blo 1124630 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B2532761 : Blo 1124630 2532761 := bstep (se 2 (by rfl) ⟨949785, by rfl⟩ : syracuseStep 2532761 = 1899571) B1899571
theorem B8660429 : Blo 1124630 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B1713625 : Blo 1124630 1713625 := bstep (se 2 (by rfl) ⟨642609, by rfl⟩ : syracuseStep 1713625 = 1285219) B1285219
theorem B2532851 : Blo 1124630 2532851 := bstep (se 1 (by rfl) ⟨1899638, by rfl⟩ : syracuseStep 2532851 = 3799277) B3799277
theorem B2532887 : Blo 1124630 2532887 := bstep (se 1 (by rfl) ⟨1899665, by rfl⟩ : syracuseStep 2532887 = 3799331) B3799331
theorem B2533067 : Blo 1124630 2533067 := bstep (se 1 (by rfl) ⟨1899800, by rfl⟩ : syracuseStep 2533067 = 3799601) B3799601
theorem B2139851 : Blo 1124630 2139851 := bstep (se 1 (by rfl) ⟨1604888, by rfl⟩ : syracuseStep 2139851 = 3209777) B3209777
theorem B7317209 : Blo 1124630 7317209 := bstep (se 2 (by rfl) ⟨2743953, by rfl⟩ : syracuseStep 7317209 = 5487907) B5487907
theorem B2533121 : Blo 1124630 2533121 := bstep (se 2 (by rfl) ⟨949920, by rfl⟩ : syracuseStep 2533121 = 1899841) B1899841
theorem B5711633 : Blo 1124630 5711633 := bstep (se 2 (by rfl) ⟨2141862, by rfl⟩ : syracuseStep 5711633 = 4283725) B4283725
theorem B4171565 : Blo 1124630 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B2140033 : Blo 1124630 2140033 := bstep (se 2 (by rfl) ⟨802512, by rfl⟩ : syracuseStep 2140033 = 1605025) B1605025
theorem B5711795 : Blo 1124630 5711795 := bstep (se 1 (by rfl) ⟨4283846, by rfl⟩ : syracuseStep 5711795 = 8567693) B8567693
theorem B2533337 : Blo 1124630 2533337 := bstep (se 2 (by rfl) ⟨950001, by rfl⟩ : syracuseStep 2533337 = 1900003) B1900003
theorem B4270103 : Blo 1124630 4270103 := bstep (se 1 (by rfl) ⟨3202577, by rfl⟩ : syracuseStep 4270103 = 6405155) B6405155
theorem B2533427 : Blo 1124630 2533427 := bstep (se 1 (by rfl) ⟨1900070, by rfl⟩ : syracuseStep 2533427 = 3800141) B3800141
theorem B2402369 : Blo 1124630 2402369 := bstep (se 2 (by rfl) ⟨900888, by rfl⟩ : syracuseStep 2402369 = 1801777) B1801777
theorem B2533463 : Blo 1124630 2533463 := bstep (se 1 (by rfl) ⟨1900097, by rfl⟩ : syracuseStep 2533463 = 3800195) B3800195
theorem B2533643 : Blo 1124630 2533643 := bstep (se 1 (by rfl) ⟨1900232, by rfl⟩ : syracuseStep 2533643 = 3800465) B3800465
theorem B1124631 : Blo 1124630 1124631 := bstep (se 1 (by rfl) ⟨843473, by rfl⟩ : syracuseStep 1124631 = 1686947) B1686947
theorem B1124651 : Blo 1124630 1124651 := bstep (se 1 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 1124651 = 1686977) B1686977
theorem B1124663 : Blo 1124630 1124663 := bstep (se 1 (by rfl) ⟨843497, by rfl⟩ : syracuseStep 1124663 = 1686995) B1686995
theorem B2533697 : Blo 1124630 2533697 := bstep (se 2 (by rfl) ⟨950136, by rfl⟩ : syracuseStep 2533697 = 1900273) B1900273
theorem B2140481 : Blo 1124630 2140481 := bstep (se 2 (by rfl) ⟨802680, by rfl⟩ : syracuseStep 2140481 = 1605361) B1605361
theorem B1124683 : Blo 1124630 1124683 := bstep (se 1 (by rfl) ⟨843512, by rfl⟩ : syracuseStep 1124683 = 1687025) B1687025
theorem B1124695 : Blo 1124630 1124695 := bstep (se 1 (by rfl) ⟨843521, by rfl⟩ : syracuseStep 1124695 = 1687043) B1687043
theorem B1124715 : Blo 1124630 1124715 := bstep (se 1 (by rfl) ⟨843536, by rfl⟩ : syracuseStep 1124715 = 1687073) B1687073
theorem B1124727 : Blo 1124630 1124727 := bstep (se 1 (by rfl) ⟨843545, by rfl⟩ : syracuseStep 1124727 = 1687091) B1687091
theorem B1124747 : Blo 1124630 1124747 := bstep (se 1 (by rfl) ⟨843560, by rfl⟩ : syracuseStep 1124747 = 1687121) B1687121
theorem B1124759 : Blo 1124630 1124759 := bstep (se 1 (by rfl) ⟨843569, by rfl⟩ : syracuseStep 1124759 = 1687139) B1687139
theorem B1124779 : Blo 1124630 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B1124791 : Blo 1124630 1124791 := bstep (se 1 (by rfl) ⟨843593, by rfl⟩ : syracuseStep 1124791 = 1687187) B1687187
theorem B1124811 : Blo 1124630 1124811 := bstep (se 1 (by rfl) ⟨843608, by rfl⟩ : syracuseStep 1124811 = 1687217) B1687217
theorem B4336075 : Blo 1124630 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B1124823 : Blo 1124630 1124823 := bstep (se 1 (by rfl) ⟨843617, by rfl⟩ : syracuseStep 1124823 = 1687235) B1687235
theorem B1124843 : Blo 1124630 1124843 := bstep (se 1 (by rfl) ⟨843632, by rfl⟩ : syracuseStep 1124843 = 1687265) B1687265
theorem B1124855 : Blo 1124630 1124855 := bstep (se 1 (by rfl) ⟨843641, by rfl⟩ : syracuseStep 1124855 = 1687283) B1687283
theorem B1124875 : Blo 1124630 1124875 := bstep (se 1 (by rfl) ⟨843656, by rfl⟩ : syracuseStep 1124875 = 1687313) B1687313
theorem B82356749 : Blo 1124630 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B1124887 : Blo 1124630 1124887 := bstep (se 1 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 1124887 = 1687331) B1687331
theorem B2533913 : Blo 1124630 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B1124907 : Blo 1124630 1124907 := bstep (se 1 (by rfl) ⟨843680, by rfl⟩ : syracuseStep 1124907 = 1687361) B1687361
theorem B1124919 : Blo 1124630 1124919 := bstep (se 1 (by rfl) ⟨843689, by rfl⟩ : syracuseStep 1124919 = 1687379) B1687379
theorem B1124939 : Blo 1124630 1124939 := bstep (se 1 (by rfl) ⟨843704, by rfl⟩ : syracuseStep 1124939 = 1687409) B1687409
theorem B1124951 : Blo 1124630 1124951 := bstep (se 1 (by rfl) ⟨843713, by rfl⟩ : syracuseStep 1124951 = 1687427) B1687427
theorem B1124971 : Blo 1124630 1124971 := bstep (se 1 (by rfl) ⟨843728, by rfl⟩ : syracuseStep 1124971 = 1687457) B1687457
theorem B2534003 : Blo 1124630 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B1124983 : Blo 1124630 1124983 := bstep (se 1 (by rfl) ⟨843737, by rfl⟩ : syracuseStep 1124983 = 1687475) B1687475
theorem B1125003 : Blo 1124630 1125003 := bstep (se 1 (by rfl) ⟨843752, by rfl⟩ : syracuseStep 1125003 = 1687505) B1687505
theorem B1125015 : Blo 1124630 1125015 := bstep (se 1 (by rfl) ⟨843761, by rfl⟩ : syracuseStep 1125015 = 1687523) B1687523
theorem B2534039 : Blo 1124630 2534039 := bstep (se 1 (by rfl) ⟨1900529, by rfl⟩ : syracuseStep 2534039 = 3801059) B3801059
theorem B2140823 : Blo 1124630 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B1125035 : Blo 1124630 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B1125047 : Blo 1124630 1125047 := bstep (se 1 (by rfl) ⟨843785, by rfl⟩ : syracuseStep 1125047 = 1687571) B1687571
theorem B1125067 : Blo 1124630 1125067 := bstep (se 1 (by rfl) ⟨843800, by rfl⟩ : syracuseStep 1125067 = 1687601) B1687601
theorem B1125079 : Blo 1124630 1125079 := bstep (se 1 (by rfl) ⟨843809, by rfl⟩ : syracuseStep 1125079 = 1687619) B1687619
theorem B1125099 : Blo 1124630 1125099 := bstep (se 1 (by rfl) ⟨843824, by rfl⟩ : syracuseStep 1125099 = 1687649) B1687649
theorem B1125111 : Blo 1124630 1125111 := bstep (se 1 (by rfl) ⟨843833, by rfl⟩ : syracuseStep 1125111 = 1687667) B1687667
theorem B1125131 : Blo 1124630 1125131 := bstep (se 1 (by rfl) ⟨843848, by rfl⟩ : syracuseStep 1125131 = 1687697) B1687697
theorem B1125143 : Blo 1124630 1125143 := bstep (se 1 (by rfl) ⟨843857, by rfl⟩ : syracuseStep 1125143 = 1687715) B1687715
theorem B1125163 : Blo 1124630 1125163 := bstep (se 1 (by rfl) ⟨843872, by rfl⟩ : syracuseStep 1125163 = 1687745) B1687745
theorem B2435891 : Blo 1124630 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B1125175 : Blo 1124630 1125175 := bstep (se 1 (by rfl) ⟨843881, by rfl⟩ : syracuseStep 1125175 = 1687763) B1687763
theorem B9612107 : Blo 1124630 9612107 := bstep (se 1 (by rfl) ⟨7209080, by rfl⟩ : syracuseStep 9612107 = 14418161) B14418161
theorem B1125195 : Blo 1124630 1125195 := bstep (se 1 (by rfl) ⟨843896, by rfl⟩ : syracuseStep 1125195 = 1687793) B1687793
theorem B2534219 : Blo 1124630 2534219 := bstep (se 1 (by rfl) ⟨1900664, by rfl⟩ : syracuseStep 2534219 = 3801329) B3801329
theorem B1125207 : Blo 1124630 1125207 := bstep (se 1 (by rfl) ⟨843905, by rfl⟩ : syracuseStep 1125207 = 1687811) B1687811
theorem B1125227 : Blo 1124630 1125227 := bstep (se 1 (by rfl) ⟨843920, by rfl⟩ : syracuseStep 1125227 = 1687841) B1687841
theorem B1125239 : Blo 1124630 1125239 := bstep (se 1 (by rfl) ⟨843929, by rfl⟩ : syracuseStep 1125239 = 1687859) B1687859
theorem B2534273 : Blo 1124630 2534273 := bstep (se 2 (by rfl) ⟨950352, by rfl⟩ : syracuseStep 2534273 = 1900705) B1900705
theorem B1125259 : Blo 1124630 1125259 := bstep (se 1 (by rfl) ⟨843944, by rfl⟩ : syracuseStep 1125259 = 1687889) B1687889
theorem B1125271 : Blo 1124630 1125271 := bstep (se 1 (by rfl) ⟨843953, by rfl⟩ : syracuseStep 1125271 = 1687907) B1687907
theorem B1125291 : Blo 1124630 1125291 := bstep (se 1 (by rfl) ⟨843968, by rfl⟩ : syracuseStep 1125291 = 1687937) B1687937
theorem B2894771 : Blo 1124630 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B1125303 : Blo 1124630 1125303 := bstep (se 1 (by rfl) ⟨843977, by rfl⟩ : syracuseStep 1125303 = 1687955) B1687955
theorem B1125323 : Blo 1124630 1125323 := bstep (se 1 (by rfl) ⟨843992, by rfl⟩ : syracuseStep 1125323 = 1687985) B1687985
theorem B1125335 : Blo 1124630 1125335 := bstep (se 1 (by rfl) ⟨844001, by rfl⟩ : syracuseStep 1125335 = 1688003) B1688003
theorem B1125355 : Blo 1124630 1125355 := bstep (se 1 (by rfl) ⟨844016, by rfl⟩ : syracuseStep 1125355 = 1688033) B1688033
theorem B1125367 : Blo 1124630 1125367 := bstep (se 1 (by rfl) ⟨844025, by rfl⟩ : syracuseStep 1125367 = 1688051) B1688051
theorem B1125387 : Blo 1124630 1125387 := bstep (se 1 (by rfl) ⟨844040, by rfl⟩ : syracuseStep 1125387 = 1688081) B1688081
theorem B1125399 : Blo 1124630 1125399 := bstep (se 1 (by rfl) ⟨844049, by rfl⟩ : syracuseStep 1125399 = 1688099) B1688099
theorem B1125419 : Blo 1124630 1125419 := bstep (se 1 (by rfl) ⟨844064, by rfl⟩ : syracuseStep 1125419 = 1688129) B1688129
theorem B2567219 : Blo 1124630 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B1125431 : Blo 1124630 1125431 := bstep (se 1 (by rfl) ⟨844073, by rfl⟩ : syracuseStep 1125431 = 1688147) B1688147
theorem B1125451 : Blo 1124630 1125451 := bstep (se 1 (by rfl) ⟨844088, by rfl⟩ : syracuseStep 1125451 = 1688177) B1688177
theorem B6499403 : Blo 1124630 6499403 := bstep (se 1 (by rfl) ⟨4874552, by rfl⟩ : syracuseStep 6499403 = 9749105) B9749105
theorem B1125463 : Blo 1124630 1125463 := bstep (se 1 (by rfl) ⟨844097, by rfl⟩ : syracuseStep 1125463 = 1688195) B1688195
theorem B2534489 : Blo 1124630 2534489 := bstep (se 2 (by rfl) ⟨950433, by rfl⟩ : syracuseStep 2534489 = 1900867) B1900867
theorem B8563805 : Blo 1124630 8563805 := bstep (se 3 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 8563805 = 3211427) B3211427
theorem B1125483 : Blo 1124630 1125483 := bstep (se 1 (by rfl) ⟨844112, by rfl⟩ : syracuseStep 1125483 = 1688225) B1688225
theorem B1125495 : Blo 1124630 1125495 := bstep (se 1 (by rfl) ⟨844121, by rfl⟩ : syracuseStep 1125495 = 1688243) B1688243
theorem B1125515 : Blo 1124630 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B2403479 : Blo 1124630 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B1125527 : Blo 1124630 1125527 := bstep (se 1 (by rfl) ⟨844145, by rfl⟩ : syracuseStep 1125527 = 1688291) B1688291
theorem B7810199 : Blo 1124630 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B1125547 : Blo 1124630 1125547 := bstep (se 1 (by rfl) ⟨844160, by rfl⟩ : syracuseStep 1125547 = 1688321) B1688321
theorem B2534579 : Blo 1124630 2534579 := bstep (se 1 (by rfl) ⟨1900934, by rfl⟩ : syracuseStep 2534579 = 3801869) B3801869
theorem B1125559 : Blo 1124630 1125559 := bstep (se 1 (by rfl) ⟨844169, by rfl⟩ : syracuseStep 1125559 = 1688339) B1688339
theorem B1125579 : Blo 1124630 1125579 := bstep (se 1 (by rfl) ⟨844184, by rfl⟩ : syracuseStep 1125579 = 1688369) B1688369
theorem B1125591 : Blo 1124630 1125591 := bstep (se 1 (by rfl) ⟨844193, by rfl⟩ : syracuseStep 1125591 = 1688387) B1688387
theorem B2534615 : Blo 1124630 2534615 := bstep (se 1 (by rfl) ⟨1900961, by rfl⟩ : syracuseStep 2534615 = 3801923) B3801923
theorem B1125611 : Blo 1124630 1125611 := bstep (se 1 (by rfl) ⟨844208, by rfl⟩ : syracuseStep 1125611 = 1688417) B1688417
theorem B1125623 : Blo 1124630 1125623 := bstep (se 1 (by rfl) ⟨844217, by rfl⟩ : syracuseStep 1125623 = 1688435) B1688435
theorem B4271363 : Blo 1124630 4271363 := bstep (se 1 (by rfl) ⟨3203522, by rfl⟩ : syracuseStep 4271363 = 6407045) B6407045
theorem B1125643 : Blo 1124630 1125643 := bstep (se 1 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 1125643 = 1688465) B1688465
theorem B1125655 : Blo 1124630 1125655 := bstep (se 1 (by rfl) ⟨844241, by rfl⟩ : syracuseStep 1125655 = 1688483) B1688483
theorem B1125675 : Blo 1124630 1125675 := bstep (se 1 (by rfl) ⟨844256, by rfl⟩ : syracuseStep 1125675 = 1688513) B1688513
theorem B2141491 : Blo 1124630 2141491 := bstep (se 1 (by rfl) ⟨1606118, by rfl⟩ : syracuseStep 2141491 = 3212237) B3212237
theorem B1125687 : Blo 1124630 1125687 := bstep (se 1 (by rfl) ⟨844265, by rfl⟩ : syracuseStep 1125687 = 1688531) B1688531
theorem B1125707 : Blo 1124630 1125707 := bstep (se 1 (by rfl) ⟨844280, by rfl⟩ : syracuseStep 1125707 = 1688561) B1688561
theorem B1125719 : Blo 1124630 1125719 := bstep (se 1 (by rfl) ⟨844289, by rfl⟩ : syracuseStep 1125719 = 1688579) B1688579
theorem B1125739 : Blo 1124630 1125739 := bstep (se 1 (by rfl) ⟨844304, by rfl⟩ : syracuseStep 1125739 = 1688609) B1688609
theorem B1125751 : Blo 1124630 1125751 := bstep (se 1 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 1125751 = 1688627) B1688627
theorem B1125771 : Blo 1124630 1125771 := bstep (se 1 (by rfl) ⟨844328, by rfl⟩ : syracuseStep 1125771 = 1688657) B1688657
theorem B2534795 : Blo 1124630 2534795 := bstep (se 1 (by rfl) ⟨1901096, by rfl⟩ : syracuseStep 2534795 = 3802193) B3802193
theorem B1125783 : Blo 1124630 1125783 := bstep (se 1 (by rfl) ⟨844337, by rfl⟩ : syracuseStep 1125783 = 1688675) B1688675
theorem B1125803 : Blo 1124630 1125803 := bstep (se 1 (by rfl) ⟨844352, by rfl⟩ : syracuseStep 1125803 = 1688705) B1688705
theorem B1125815 : Blo 1124630 1125815 := bstep (se 1 (by rfl) ⟨844361, by rfl⟩ : syracuseStep 1125815 = 1688723) B1688723
theorem B2534849 : Blo 1124630 2534849 := bstep (se 2 (by rfl) ⟨950568, by rfl⟩ : syracuseStep 2534849 = 1901137) B1901137
theorem B1125835 : Blo 1124630 1125835 := bstep (se 1 (by rfl) ⟨844376, by rfl⟩ : syracuseStep 1125835 = 1688753) B1688753
theorem B1125847 : Blo 1124630 1125847 := bstep (se 1 (by rfl) ⟨844385, by rfl⟩ : syracuseStep 1125847 = 1688771) B1688771
theorem B1125867 : Blo 1124630 1125867 := bstep (se 1 (by rfl) ⟨844400, by rfl⟩ : syracuseStep 1125867 = 1688801) B1688801
theorem B1125879 : Blo 1124630 1125879 := bstep (se 1 (by rfl) ⟨844409, by rfl⟩ : syracuseStep 1125879 = 1688819) B1688819
theorem B1125899 : Blo 1124630 1125899 := bstep (se 1 (by rfl) ⟨844424, by rfl⟩ : syracuseStep 1125899 = 1688849) B1688849
theorem B1125911 : Blo 1124630 1125911 := bstep (se 1 (by rfl) ⟨844433, by rfl⟩ : syracuseStep 1125911 = 1688867) B1688867
theorem B1125931 : Blo 1124630 1125931 := bstep (se 1 (by rfl) ⟨844448, by rfl⟩ : syracuseStep 1125931 = 1688897) B1688897
theorem B1125943 : Blo 1124630 1125943 := bstep (se 1 (by rfl) ⟨844457, by rfl⟩ : syracuseStep 1125943 = 1688915) B1688915
theorem B1125963 : Blo 1124630 1125963 := bstep (se 1 (by rfl) ⟨844472, by rfl⟩ : syracuseStep 1125963 = 1688945) B1688945
theorem B1125975 : Blo 1124630 1125975 := bstep (se 1 (by rfl) ⟨844481, by rfl⟩ : syracuseStep 1125975 = 1688963) B1688963
theorem B1125995 : Blo 1124630 1125995 := bstep (se 1 (by rfl) ⟨844496, by rfl⟩ : syracuseStep 1125995 = 1688993) B1688993
theorem B1126007 : Blo 1124630 1126007 := bstep (se 1 (by rfl) ⟨844505, by rfl⟩ : syracuseStep 1126007 = 1689011) B1689011
theorem B1126027 : Blo 1124630 1126027 := bstep (se 1 (by rfl) ⟨844520, by rfl⟩ : syracuseStep 1126027 = 1689041) B1689041
theorem B1126039 : Blo 1124630 1126039 := bstep (se 1 (by rfl) ⟨844529, by rfl⟩ : syracuseStep 1126039 = 1689059) B1689059
theorem B2535065 : Blo 1124630 2535065 := bstep (se 2 (by rfl) ⟨950649, by rfl⟩ : syracuseStep 2535065 = 1901299) B1901299
theorem B1126059 : Blo 1124630 1126059 := bstep (se 1 (by rfl) ⟨844544, by rfl⟩ : syracuseStep 1126059 = 1689089) B1689089
theorem B1126071 : Blo 1124630 1126071 := bstep (se 1 (by rfl) ⟨844553, by rfl⟩ : syracuseStep 1126071 = 1689107) B1689107
theorem B1126091 : Blo 1124630 1126091 := bstep (se 1 (by rfl) ⟨844568, by rfl⟩ : syracuseStep 1126091 = 1689137) B1689137
theorem B1126103 : Blo 1124630 1126103 := bstep (se 1 (by rfl) ⟨844577, by rfl⟩ : syracuseStep 1126103 = 1689155) B1689155
theorem B1126123 : Blo 1124630 1126123 := bstep (se 1 (by rfl) ⟨844592, by rfl⟩ : syracuseStep 1126123 = 1689185) B1689185
theorem B2535155 : Blo 1124630 2535155 := bstep (se 1 (by rfl) ⟨1901366, by rfl⟩ : syracuseStep 2535155 = 3802733) B3802733
theorem B2141939 : Blo 1124630 2141939 := bstep (se 1 (by rfl) ⟨1606454, by rfl⟩ : syracuseStep 2141939 = 3212909) B3212909
theorem B1126135 : Blo 1124630 1126135 := bstep (se 1 (by rfl) ⟨844601, by rfl⟩ : syracuseStep 1126135 = 1689203) B1689203
theorem B1126155 : Blo 1124630 1126155 := bstep (se 1 (by rfl) ⟨844616, by rfl⟩ : syracuseStep 1126155 = 1689233) B1689233
theorem B1126167 : Blo 1124630 1126167 := bstep (se 1 (by rfl) ⟨844625, by rfl⟩ : syracuseStep 1126167 = 1689251) B1689251
theorem B2535191 : Blo 1124630 2535191 := bstep (se 1 (by rfl) ⟨1901393, by rfl⟩ : syracuseStep 2535191 = 3802787) B3802787
theorem B2141977 : Blo 1124630 2141977 := bstep (se 2 (by rfl) ⟨803241, by rfl⟩ : syracuseStep 2141977 = 1606483) B1606483
theorem B1126187 : Blo 1124630 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B1126199 : Blo 1124630 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B1126219 : Blo 1124630 1126219 := bstep (se 1 (by rfl) ⟨844664, by rfl⟩ : syracuseStep 1126219 = 1689329) B1689329
theorem B1126231 : Blo 1124630 1126231 := bstep (se 1 (by rfl) ⟨844673, by rfl⟩ : syracuseStep 1126231 = 1689347) B1689347
theorem B1126251 : Blo 1124630 1126251 := bstep (se 1 (by rfl) ⟨844688, by rfl⟩ : syracuseStep 1126251 = 1689377) B1689377
theorem B1126263 : Blo 1124630 1126263 := bstep (se 1 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 1126263 = 1689395) B1689395
theorem B1126283 : Blo 1124630 1126283 := bstep (se 1 (by rfl) ⟨844712, by rfl⟩ : syracuseStep 1126283 = 1689425) B1689425
theorem B1126295 : Blo 1124630 1126295 := bstep (se 1 (by rfl) ⟨844721, by rfl⟩ : syracuseStep 1126295 = 1689443) B1689443
theorem B1126315 : Blo 1124630 1126315 := bstep (se 1 (by rfl) ⟨844736, by rfl⟩ : syracuseStep 1126315 = 1689473) B1689473
theorem B1126327 : Blo 1124630 1126327 := bstep (se 1 (by rfl) ⟨844745, by rfl⟩ : syracuseStep 1126327 = 1689491) B1689491
theorem B1126347 : Blo 1124630 1126347 := bstep (se 1 (by rfl) ⟨844760, by rfl⟩ : syracuseStep 1126347 = 1689521) B1689521
theorem B2535371 : Blo 1124630 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B1126359 : Blo 1124630 1126359 := bstep (se 1 (by rfl) ⟨844769, by rfl⟩ : syracuseStep 1126359 = 1689539) B1689539
theorem B1126379 : Blo 1124630 1126379 := bstep (se 1 (by rfl) ⟨844784, by rfl⟩ : syracuseStep 1126379 = 1689569) B1689569
theorem B1126391 : Blo 1124630 1126391 := bstep (se 1 (by rfl) ⟨844793, by rfl⟩ : syracuseStep 1126391 = 1689587) B1689587
theorem B2535425 : Blo 1124630 2535425 := bstep (se 2 (by rfl) ⟨950784, by rfl⟩ : syracuseStep 2535425 = 1901569) B1901569
theorem B1126411 : Blo 1124630 1126411 := bstep (se 1 (by rfl) ⟨844808, by rfl⟩ : syracuseStep 1126411 = 1689617) B1689617
theorem B1126423 : Blo 1124630 1126423 := bstep (se 1 (by rfl) ⟨844817, by rfl⟩ : syracuseStep 1126423 = 1689635) B1689635
theorem B1126443 : Blo 1124630 1126443 := bstep (se 1 (by rfl) ⟨844832, by rfl⟩ : syracuseStep 1126443 = 1689665) B1689665
theorem B1126455 : Blo 1124630 1126455 := bstep (se 1 (by rfl) ⟨844841, by rfl⟩ : syracuseStep 1126455 = 1689683) B1689683
theorem B18264133 : Blo 1124630 18264133 := bstep (se 4 (by rfl) ⟨1712262, by rfl⟩ : syracuseStep 18264133 = 3424525) B3424525
theorem B1126475 : Blo 1124630 1126475 := bstep (se 1 (by rfl) ⟨844856, by rfl⟩ : syracuseStep 1126475 = 1689713) B1689713
theorem B1126487 : Blo 1124630 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B1126507 : Blo 1124630 1126507 := bstep (se 1 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 1126507 = 1689761) B1689761
theorem B1126519 : Blo 1124630 1126519 := bstep (se 1 (by rfl) ⟨844889, by rfl⟩ : syracuseStep 1126519 = 1689779) B1689779
theorem B1126539 : Blo 1124630 1126539 := bstep (se 1 (by rfl) ⟨844904, by rfl⟩ : syracuseStep 1126539 = 1689809) B1689809
theorem B1126551 : Blo 1124630 1126551 := bstep (se 1 (by rfl) ⟨844913, by rfl⟩ : syracuseStep 1126551 = 1689827) B1689827
theorem B2404505 : Blo 1124630 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B1126571 : Blo 1124630 1126571 := bstep (se 1 (by rfl) ⟨844928, by rfl⟩ : syracuseStep 1126571 = 1689857) B1689857
theorem B1126583 : Blo 1124630 1126583 := bstep (se 1 (by rfl) ⟨844937, by rfl⟩ : syracuseStep 1126583 = 1689875) B1689875
theorem B1126603 : Blo 1124630 1126603 := bstep (se 1 (by rfl) ⟨844952, by rfl⟩ : syracuseStep 1126603 = 1689905) B1689905
theorem B1126615 : Blo 1124630 1126615 := bstep (se 1 (by rfl) ⟨844961, by rfl⟩ : syracuseStep 1126615 = 1689923) B1689923
theorem B2535641 : Blo 1124630 2535641 := bstep (se 2 (by rfl) ⟨950865, by rfl⟩ : syracuseStep 2535641 = 1901731) B1901731
theorem B2142425 : Blo 1124630 2142425 := bstep (se 2 (by rfl) ⟨803409, by rfl⟩ : syracuseStep 2142425 = 1606819) B1606819
theorem B1126635 : Blo 1124630 1126635 := bstep (se 1 (by rfl) ⟨844976, by rfl⟩ : syracuseStep 1126635 = 1689953) B1689953
theorem B1126647 : Blo 1124630 1126647 := bstep (se 1 (by rfl) ⟨844985, by rfl⟩ : syracuseStep 1126647 = 1689971) B1689971
theorem B1126667 : Blo 1124630 1126667 := bstep (se 1 (by rfl) ⟨845000, by rfl⟩ : syracuseStep 1126667 = 1690001) B1690001
theorem B1126679 : Blo 1124630 1126679 := bstep (se 1 (by rfl) ⟨845009, by rfl⟩ : syracuseStep 1126679 = 1690019) B1690019
theorem B1126699 : Blo 1124630 1126699 := bstep (se 1 (by rfl) ⟨845024, by rfl⟩ : syracuseStep 1126699 = 1690049) B1690049
theorem B2535731 : Blo 1124630 2535731 := bstep (se 1 (by rfl) ⟨1901798, by rfl⟩ : syracuseStep 2535731 = 3803597) B3803597
theorem B1126711 : Blo 1124630 1126711 := bstep (se 1 (by rfl) ⟨845033, by rfl⟩ : syracuseStep 1126711 = 1690067) B1690067
theorem B1126731 : Blo 1124630 1126731 := bstep (se 1 (by rfl) ⟨845048, by rfl⟩ : syracuseStep 1126731 = 1690097) B1690097
theorem B1126743 : Blo 1124630 1126743 := bstep (se 1 (by rfl) ⟨845057, by rfl⟩ : syracuseStep 1126743 = 1690115) B1690115
theorem B2535767 : Blo 1124630 2535767 := bstep (se 1 (by rfl) ⟨1901825, by rfl⟩ : syracuseStep 2535767 = 3803651) B3803651
theorem B1126763 : Blo 1124630 1126763 := bstep (se 1 (by rfl) ⟨845072, by rfl⟩ : syracuseStep 1126763 = 1690145) B1690145
theorem B1126775 : Blo 1124630 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B1126795 : Blo 1124630 1126795 := bstep (se 1 (by rfl) ⟨845096, by rfl⟩ : syracuseStep 1126795 = 1690193) B1690193
theorem B1126807 : Blo 1124630 1126807 := bstep (se 1 (by rfl) ⟨845105, by rfl⟩ : syracuseStep 1126807 = 1690211) B1690211
theorem B1126827 : Blo 1124630 1126827 := bstep (se 1 (by rfl) ⟨845120, by rfl⟩ : syracuseStep 1126827 = 1690241) B1690241
theorem B1126839 : Blo 1124630 1126839 := bstep (se 1 (by rfl) ⟨845129, by rfl⟩ : syracuseStep 1126839 = 1690259) B1690259
theorem B1126859 : Blo 1124630 1126859 := bstep (se 1 (by rfl) ⟨845144, by rfl⟩ : syracuseStep 1126859 = 1690289) B1690289
theorem B1126871 : Blo 1124630 1126871 := bstep (se 1 (by rfl) ⟨845153, by rfl⟩ : syracuseStep 1126871 = 1690307) B1690307
theorem B1126891 : Blo 1124630 1126891 := bstep (se 1 (by rfl) ⟨845168, by rfl⟩ : syracuseStep 1126891 = 1690337) B1690337
theorem B1126903 : Blo 1124630 1126903 := bstep (se 1 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 1126903 = 1690355) B1690355
theorem B1126923 : Blo 1124630 1126923 := bstep (se 1 (by rfl) ⟨845192, by rfl⟩ : syracuseStep 1126923 = 1690385) B1690385
theorem B2535947 : Blo 1124630 2535947 := bstep (se 1 (by rfl) ⟨1901960, by rfl⟩ : syracuseStep 2535947 = 3803921) B3803921
theorem B1126935 : Blo 1124630 1126935 := bstep (se 1 (by rfl) ⟨845201, by rfl⟩ : syracuseStep 1126935 = 1690403) B1690403
theorem B1126955 : Blo 1124630 1126955 := bstep (se 1 (by rfl) ⟨845216, by rfl⟩ : syracuseStep 1126955 = 1690433) B1690433
theorem B1126967 : Blo 1124630 1126967 := bstep (se 1 (by rfl) ⟨845225, by rfl⟩ : syracuseStep 1126967 = 1690451) B1690451
theorem B2536001 : Blo 1124630 2536001 := bstep (se 2 (by rfl) ⟨951000, by rfl⟩ : syracuseStep 2536001 = 1902001) B1902001
theorem B1126987 : Blo 1124630 1126987 := bstep (se 1 (by rfl) ⟨845240, by rfl⟩ : syracuseStep 1126987 = 1690481) B1690481
theorem B1126999 : Blo 1124630 1126999 := bstep (se 1 (by rfl) ⟨845249, by rfl⟩ : syracuseStep 1126999 = 1690499) B1690499
theorem B1127019 : Blo 1124630 1127019 := bstep (se 1 (by rfl) ⟨845264, by rfl⟩ : syracuseStep 1127019 = 1690529) B1690529
theorem B1127031 : Blo 1124630 1127031 := bstep (se 1 (by rfl) ⟨845273, by rfl⟩ : syracuseStep 1127031 = 1690547) B1690547
theorem B1127051 : Blo 1124630 1127051 := bstep (se 1 (by rfl) ⟨845288, by rfl⟩ : syracuseStep 1127051 = 1690577) B1690577
theorem B1127063 : Blo 1124630 1127063 := bstep (se 1 (by rfl) ⟨845297, by rfl⟩ : syracuseStep 1127063 = 1690595) B1690595
theorem B1127083 : Blo 1124630 1127083 := bstep (se 1 (by rfl) ⟨845312, by rfl⟩ : syracuseStep 1127083 = 1690625) B1690625
theorem B1127095 : Blo 1124630 1127095 := bstep (se 1 (by rfl) ⟨845321, by rfl⟩ : syracuseStep 1127095 = 1690643) B1690643
theorem B1127115 : Blo 1124630 1127115 := bstep (se 1 (by rfl) ⟨845336, by rfl⟩ : syracuseStep 1127115 = 1690673) B1690673
theorem B1127127 : Blo 1124630 1127127 := bstep (se 1 (by rfl) ⟨845345, by rfl⟩ : syracuseStep 1127127 = 1690691) B1690691
theorem B1127147 : Blo 1124630 1127147 := bstep (se 1 (by rfl) ⟨845360, by rfl⟩ : syracuseStep 1127147 = 1690721) B1690721
theorem B1127159 : Blo 1124630 1127159 := bstep (se 1 (by rfl) ⟨845369, by rfl⟩ : syracuseStep 1127159 = 1690739) B1690739
theorem B1127179 : Blo 1124630 1127179 := bstep (se 1 (by rfl) ⟨845384, by rfl⟩ : syracuseStep 1127179 = 1690769) B1690769
theorem B1520407 : Blo 1124630 1520407 := bstep (se 1 (by rfl) ⟨1140305, by rfl⟩ : syracuseStep 1520407 = 2280611) B2280611
theorem B1127191 : Blo 1124630 1127191 := bstep (se 1 (by rfl) ⟨845393, by rfl⟩ : syracuseStep 1127191 = 1690787) B1690787
theorem B2536217 : Blo 1124630 2536217 := bstep (se 2 (by rfl) ⟨951081, by rfl⟩ : syracuseStep 2536217 = 1902163) B1902163
theorem B1127211 : Blo 1124630 1127211 := bstep (se 1 (by rfl) ⟨845408, by rfl⟩ : syracuseStep 1127211 = 1690817) B1690817
theorem B4567853 : Blo 1124630 4567853 := bstep (se 3 (by rfl) ⟨856472, by rfl⟩ : syracuseStep 4567853 = 1712945) B1712945
theorem B1127223 : Blo 1124630 1127223 := bstep (se 1 (by rfl) ⟨845417, by rfl⟩ : syracuseStep 1127223 = 1690835) B1690835
theorem B1127243 : Blo 1124630 1127243 := bstep (se 1 (by rfl) ⟨845432, by rfl⟩ : syracuseStep 1127243 = 1690865) B1690865
theorem B1127255 : Blo 1124630 1127255 := bstep (se 1 (by rfl) ⟨845441, by rfl⟩ : syracuseStep 1127255 = 1690883) B1690883
theorem B1127275 : Blo 1124630 1127275 := bstep (se 1 (by rfl) ⟨845456, by rfl⟩ : syracuseStep 1127275 = 1690913) B1690913
theorem B2536307 : Blo 1124630 2536307 := bstep (se 1 (by rfl) ⟨1902230, by rfl⟩ : syracuseStep 2536307 = 3804461) B3804461
theorem B1127287 : Blo 1124630 1127287 := bstep (se 1 (by rfl) ⟨845465, by rfl⟩ : syracuseStep 1127287 = 1690931) B1690931
theorem B1127307 : Blo 1124630 1127307 := bstep (se 1 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 1127307 = 1690961) B1690961
theorem B2536343 : Blo 1124630 2536343 := bstep (se 1 (by rfl) ⟨1902257, by rfl⟩ : syracuseStep 2536343 = 3804515) B3804515
theorem B1127319 : Blo 1124630 1127319 := bstep (se 1 (by rfl) ⟨845489, by rfl⟩ : syracuseStep 1127319 = 1690979) B1690979
theorem B1127339 : Blo 1124630 1127339 := bstep (se 1 (by rfl) ⟨845504, by rfl⟩ : syracuseStep 1127339 = 1691009) B1691009
theorem B1127351 : Blo 1124630 1127351 := bstep (se 1 (by rfl) ⟨845513, by rfl⟩ : syracuseStep 1127351 = 1691027) B1691027
theorem B1127371 : Blo 1124630 1127371 := bstep (se 1 (by rfl) ⟨845528, by rfl⟩ : syracuseStep 1127371 = 1691057) B1691057
theorem B1127383 : Blo 1124630 1127383 := bstep (se 1 (by rfl) ⟨845537, by rfl⟩ : syracuseStep 1127383 = 1691075) B1691075
theorem B1127403 : Blo 1124630 1127403 := bstep (se 1 (by rfl) ⟨845552, by rfl⟩ : syracuseStep 1127403 = 1691105) B1691105
theorem B1127415 : Blo 1124630 1127415 := bstep (se 1 (by rfl) ⟨845561, by rfl⟩ : syracuseStep 1127415 = 1691123) B1691123
theorem B1127435 : Blo 1124630 1127435 := bstep (se 1 (by rfl) ⟨845576, by rfl⟩ : syracuseStep 1127435 = 1691153) B1691153
theorem B1127447 : Blo 1124630 1127447 := bstep (se 1 (by rfl) ⟨845585, by rfl⟩ : syracuseStep 1127447 = 1691171) B1691171
theorem B1127467 : Blo 1124630 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B1127479 : Blo 1124630 1127479 := bstep (se 1 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 1127479 = 1691219) B1691219
theorem B8107073 : Blo 1124630 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B2536523 : Blo 1124630 2536523 := bstep (se 1 (by rfl) ⟨1902392, by rfl⟩ : syracuseStep 2536523 = 3804785) B3804785
theorem B1127499 : Blo 1124630 1127499 := bstep (se 1 (by rfl) ⟨845624, by rfl⟩ : syracuseStep 1127499 = 1691249) B1691249
theorem B1127511 : Blo 1124630 1127511 := bstep (se 1 (by rfl) ⟨845633, by rfl⟩ : syracuseStep 1127511 = 1691267) B1691267
theorem B1127531 : Blo 1124630 1127531 := bstep (se 1 (by rfl) ⟨845648, by rfl⟩ : syracuseStep 1127531 = 1691297) B1691297
theorem B1127543 : Blo 1124630 1127543 := bstep (se 1 (by rfl) ⟨845657, by rfl⟩ : syracuseStep 1127543 = 1691315) B1691315
theorem B2536577 : Blo 1124630 2536577 := bstep (se 2 (by rfl) ⟨951216, by rfl⟩ : syracuseStep 2536577 = 1902433) B1902433
theorem B1127563 : Blo 1124630 1127563 := bstep (se 1 (by rfl) ⟨845672, by rfl⟩ : syracuseStep 1127563 = 1691345) B1691345
theorem B1127575 : Blo 1124630 1127575 := bstep (se 1 (by rfl) ⟨845681, by rfl⟩ : syracuseStep 1127575 = 1691363) B1691363
theorem B1127595 : Blo 1124630 1127595 := bstep (se 1 (by rfl) ⟨845696, by rfl⟩ : syracuseStep 1127595 = 1691393) B1691393
theorem B1127607 : Blo 1124630 1127607 := bstep (se 1 (by rfl) ⟨845705, by rfl⟩ : syracuseStep 1127607 = 1691411) B1691411
theorem B1127627 : Blo 1124630 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B1127639 : Blo 1124630 1127639 := bstep (se 1 (by rfl) ⟨845729, by rfl⟩ : syracuseStep 1127639 = 1691459) B1691459
theorem B1127659 : Blo 1124630 1127659 := bstep (se 1 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 1127659 = 1691489) B1691489
theorem B1127671 : Blo 1124630 1127671 := bstep (se 1 (by rfl) ⟨845753, by rfl⟩ : syracuseStep 1127671 = 1691507) B1691507
theorem B1127691 : Blo 1124630 1127691 := bstep (se 1 (by rfl) ⟨845768, by rfl⟩ : syracuseStep 1127691 = 1691537) B1691537
theorem B1127703 : Blo 1124630 1127703 := bstep (se 1 (by rfl) ⟨845777, by rfl⟩ : syracuseStep 1127703 = 1691555) B1691555
theorem B1127723 : Blo 1124630 1127723 := bstep (se 1 (by rfl) ⟨845792, by rfl⟩ : syracuseStep 1127723 = 1691585) B1691585
theorem B1127735 : Blo 1124630 1127735 := bstep (se 1 (by rfl) ⟨845801, by rfl⟩ : syracuseStep 1127735 = 1691603) B1691603
theorem B1127755 : Blo 1124630 1127755 := bstep (se 1 (by rfl) ⟨845816, by rfl⟩ : syracuseStep 1127755 = 1691633) B1691633
theorem B1127767 : Blo 1124630 1127767 := bstep (se 1 (by rfl) ⟨845825, by rfl⟩ : syracuseStep 1127767 = 1691651) B1691651
theorem B2536793 : Blo 1124630 2536793 := bstep (se 2 (by rfl) ⟨951297, by rfl⟩ : syracuseStep 2536793 = 1902595) B1902595
theorem B1127787 : Blo 1124630 1127787 := bstep (se 1 (by rfl) ⟨845840, by rfl⟩ : syracuseStep 1127787 = 1691681) B1691681
theorem B1127799 : Blo 1124630 1127799 := bstep (se 1 (by rfl) ⟨845849, by rfl⟩ : syracuseStep 1127799 = 1691699) B1691699
theorem B1127819 : Blo 1124630 1127819 := bstep (se 1 (by rfl) ⟨845864, by rfl⟩ : syracuseStep 1127819 = 1691729) B1691729
theorem B1127831 : Blo 1124630 1127831 := bstep (se 1 (by rfl) ⟨845873, by rfl⟩ : syracuseStep 1127831 = 1691747) B1691747
theorem B1127851 : Blo 1124630 1127851 := bstep (se 1 (by rfl) ⟨845888, by rfl⟩ : syracuseStep 1127851 = 1691777) B1691777
theorem B2536883 : Blo 1124630 2536883 := bstep (se 1 (by rfl) ⟨1902662, by rfl⟩ : syracuseStep 2536883 = 3805325) B3805325
theorem B1127863 : Blo 1124630 1127863 := bstep (se 1 (by rfl) ⟨845897, by rfl⟩ : syracuseStep 1127863 = 1691795) B1691795
theorem B1127883 : Blo 1124630 1127883 := bstep (se 1 (by rfl) ⟨845912, by rfl⟩ : syracuseStep 1127883 = 1691825) B1691825
theorem B2536919 : Blo 1124630 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B1127895 : Blo 1124630 1127895 := bstep (se 1 (by rfl) ⟨845921, by rfl⟩ : syracuseStep 1127895 = 1691843) B1691843
theorem B1127915 : Blo 1124630 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B1127927 : Blo 1124630 1127927 := bstep (se 1 (by rfl) ⟨845945, by rfl⟩ : syracuseStep 1127927 = 1691891) B1691891
theorem B1127947 : Blo 1124630 1127947 := bstep (se 1 (by rfl) ⟨845960, by rfl⟩ : syracuseStep 1127947 = 1691921) B1691921
theorem B1127959 : Blo 1124630 1127959 := bstep (se 1 (by rfl) ⟨845969, by rfl⟩ : syracuseStep 1127959 = 1691939) B1691939
theorem B1127979 : Blo 1124630 1127979 := bstep (se 1 (by rfl) ⟨845984, by rfl⟩ : syracuseStep 1127979 = 1691969) B1691969
theorem B1127991 : Blo 1124630 1127991 := bstep (se 1 (by rfl) ⟨845993, by rfl⟩ : syracuseStep 1127991 = 1691987) B1691987
theorem B1128011 : Blo 1124630 1128011 := bstep (se 1 (by rfl) ⟨846008, by rfl⟩ : syracuseStep 1128011 = 1692017) B1692017
theorem B1128023 : Blo 1124630 1128023 := bstep (se 1 (by rfl) ⟨846017, by rfl⟩ : syracuseStep 1128023 = 1692035) B1692035
theorem B1128043 : Blo 1124630 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B1128055 : Blo 1124630 1128055 := bstep (se 1 (by rfl) ⟨846041, by rfl⟩ : syracuseStep 1128055 = 1692083) B1692083
theorem B2537099 : Blo 1124630 2537099 := bstep (se 1 (by rfl) ⟨1902824, by rfl⟩ : syracuseStep 2537099 = 3805649) B3805649
theorem B1128075 : Blo 1124630 1128075 := bstep (se 1 (by rfl) ⟨846056, by rfl⟩ : syracuseStep 1128075 = 1692113) B1692113
theorem B1128087 : Blo 1124630 1128087 := bstep (se 1 (by rfl) ⟨846065, by rfl⟩ : syracuseStep 1128087 = 1692131) B1692131
theorem B1128107 : Blo 1124630 1128107 := bstep (se 1 (by rfl) ⟨846080, by rfl⟩ : syracuseStep 1128107 = 1692161) B1692161
theorem B1128119 : Blo 1124630 1128119 := bstep (se 1 (by rfl) ⟨846089, by rfl⟩ : syracuseStep 1128119 = 1692179) B1692179
theorem B3847873 : Blo 1124630 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2537153 : Blo 1124630 2537153 := bstep (se 2 (by rfl) ⟨951432, by rfl⟩ : syracuseStep 2537153 = 1902865) B1902865
theorem B1128139 : Blo 1124630 1128139 := bstep (se 1 (by rfl) ⟨846104, by rfl⟩ : syracuseStep 1128139 = 1692209) B1692209
theorem B1128151 : Blo 1124630 1128151 := bstep (se 1 (by rfl) ⟨846113, by rfl⟩ : syracuseStep 1128151 = 1692227) B1692227
theorem B1128171 : Blo 1124630 1128171 := bstep (se 1 (by rfl) ⟨846128, by rfl⟩ : syracuseStep 1128171 = 1692257) B1692257
theorem B1128183 : Blo 1124630 1128183 := bstep (se 1 (by rfl) ⟨846137, by rfl⟩ : syracuseStep 1128183 = 1692275) B1692275
theorem B2406145 : Blo 1124630 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B1128203 : Blo 1124630 1128203 := bstep (se 1 (by rfl) ⟨846152, by rfl⟩ : syracuseStep 1128203 = 1692305) B1692305
theorem B4110097 : Blo 1124630 4110097 := bstep (se 2 (by rfl) ⟨1541286, by rfl⟩ : syracuseStep 4110097 = 3082573) B3082573
theorem B1128215 : Blo 1124630 1128215 := bstep (se 1 (by rfl) ⟨846161, by rfl⟩ : syracuseStep 1128215 = 1692323) B1692323
theorem B1128235 : Blo 1124630 1128235 := bstep (se 1 (by rfl) ⟨846176, by rfl⟩ : syracuseStep 1128235 = 1692353) B1692353
theorem B1128247 : Blo 1124630 1128247 := bstep (se 1 (by rfl) ⟨846185, by rfl⟩ : syracuseStep 1128247 = 1692371) B1692371
theorem B1128267 : Blo 1124630 1128267 := bstep (se 1 (by rfl) ⟨846200, by rfl⟩ : syracuseStep 1128267 = 1692401) B1692401
theorem B1128279 : Blo 1124630 1128279 := bstep (se 1 (by rfl) ⟨846209, by rfl⟩ : syracuseStep 1128279 = 1692419) B1692419
theorem B1128299 : Blo 1124630 1128299 := bstep (se 1 (by rfl) ⟨846224, by rfl⟩ : syracuseStep 1128299 = 1692449) B1692449
theorem B1128311 : Blo 1124630 1128311 := bstep (se 1 (by rfl) ⟨846233, by rfl⟩ : syracuseStep 1128311 = 1692467) B1692467
theorem B1128331 : Blo 1124630 1128331 := bstep (se 1 (by rfl) ⟨846248, by rfl⟩ : syracuseStep 1128331 = 1692497) B1692497
theorem B1128343 : Blo 1124630 1128343 := bstep (se 1 (by rfl) ⟨846257, by rfl⟩ : syracuseStep 1128343 = 1692515) B1692515
theorem B2537369 : Blo 1124630 2537369 := bstep (se 2 (by rfl) ⟨951513, by rfl⟩ : syracuseStep 2537369 = 1903027) B1903027
theorem B1128363 : Blo 1124630 1128363 := bstep (se 1 (by rfl) ⟨846272, by rfl⟩ : syracuseStep 1128363 = 1692545) B1692545
theorem B1128375 : Blo 1124630 1128375 := bstep (se 1 (by rfl) ⟨846281, by rfl⟩ : syracuseStep 1128375 = 1692563) B1692563
theorem B1128395 : Blo 1124630 1128395 := bstep (se 1 (by rfl) ⟨846296, by rfl⟩ : syracuseStep 1128395 = 1692593) B1692593
theorem B1128407 : Blo 1124630 1128407 := bstep (se 1 (by rfl) ⟨846305, by rfl⟩ : syracuseStep 1128407 = 1692611) B1692611
theorem B1128427 : Blo 1124630 1128427 := bstep (se 1 (by rfl) ⟨846320, by rfl⟩ : syracuseStep 1128427 = 1692641) B1692641
theorem B2537459 : Blo 1124630 2537459 := bstep (se 1 (by rfl) ⟨1903094, by rfl⟩ : syracuseStep 2537459 = 3806189) B3806189
theorem B1128439 : Blo 1124630 1128439 := bstep (se 1 (by rfl) ⟨846329, by rfl⟩ : syracuseStep 1128439 = 1692659) B1692659
theorem B1128459 : Blo 1124630 1128459 := bstep (se 1 (by rfl) ⟨846344, by rfl⟩ : syracuseStep 1128459 = 1692689) B1692689
theorem B2537495 : Blo 1124630 2537495 := bstep (se 1 (by rfl) ⟨1903121, by rfl⟩ : syracuseStep 2537495 = 3806243) B3806243
theorem B1128471 : Blo 1124630 1128471 := bstep (se 1 (by rfl) ⟨846353, by rfl⟩ : syracuseStep 1128471 = 1692707) B1692707
theorem B1128491 : Blo 1124630 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B1128503 : Blo 1124630 1128503 := bstep (se 1 (by rfl) ⟨846377, by rfl⟩ : syracuseStep 1128503 = 1692755) B1692755
theorem B1128523 : Blo 1124630 1128523 := bstep (se 1 (by rfl) ⟨846392, by rfl⟩ : syracuseStep 1128523 = 1692785) B1692785
theorem B1128535 : Blo 1124630 1128535 := bstep (se 1 (by rfl) ⟨846401, by rfl⟩ : syracuseStep 1128535 = 1692803) B1692803
theorem B1128555 : Blo 1124630 1128555 := bstep (se 1 (by rfl) ⟨846416, by rfl⟩ : syracuseStep 1128555 = 1692833) B1692833
theorem B1128567 : Blo 1124630 1128567 := bstep (se 1 (by rfl) ⟨846425, by rfl⟩ : syracuseStep 1128567 = 1692851) B1692851
theorem B1128587 : Blo 1124630 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B1128599 : Blo 1124630 1128599 := bstep (se 1 (by rfl) ⟨846449, by rfl⟩ : syracuseStep 1128599 = 1692899) B1692899
theorem B1128619 : Blo 1124630 1128619 := bstep (se 1 (by rfl) ⟨846464, by rfl⟩ : syracuseStep 1128619 = 1692929) B1692929
theorem B4569281 : Blo 1124630 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B2537675 : Blo 1124630 2537675 := bstep (se 1 (by rfl) ⟨1903256, by rfl⟩ : syracuseStep 2537675 = 3806513) B3806513
theorem B2537729 : Blo 1124630 2537729 := bstep (se 2 (by rfl) ⟨951648, by rfl⟩ : syracuseStep 2537729 = 1903297) B1903297
theorem B4274477 : Blo 1124630 4274477 := bstep (se 3 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 4274477 = 1602929) B1602929
theorem B2406743 : Blo 1124630 2406743 := bstep (se 1 (by rfl) ⟨1805057, by rfl⟩ : syracuseStep 2406743 = 3610115) B3610115
theorem B3848651 : Blo 1124630 3848651 := bstep (se 1 (by rfl) ⟨2886488, by rfl⟩ : syracuseStep 3848651 = 5772977) B5772977
theorem B2537945 : Blo 1124630 2537945 := bstep (se 2 (by rfl) ⟨951729, by rfl⟩ : syracuseStep 2537945 = 1903459) B1903459
theorem B2538035 : Blo 1124630 2538035 := bstep (se 1 (by rfl) ⟨1903526, by rfl⟩ : syracuseStep 2538035 = 3807053) B3807053
theorem B2538071 : Blo 1124630 2538071 := bstep (se 1 (by rfl) ⟨1903553, by rfl⟩ : syracuseStep 2538071 = 3807107) B3807107
theorem B2538251 : Blo 1124630 2538251 := bstep (se 1 (by rfl) ⟨1903688, by rfl⟩ : syracuseStep 2538251 = 3807377) B3807377
theorem B2538305 : Blo 1124630 2538305 := bstep (se 2 (by rfl) ⟨951864, by rfl⟩ : syracuseStep 2538305 = 1903729) B1903729
theorem B1522585 : Blo 1124630 1522585 := bstep (se 2 (by rfl) ⟨570969, by rfl⟩ : syracuseStep 1522585 = 1141939) B1141939
theorem B1424395 : Blo 1124630 1424395 := bstep (se 1 (by rfl) ⟨1068296, by rfl⟩ : syracuseStep 1424395 = 2136593) B2136593
theorem B2538521 : Blo 1124630 2538521 := bstep (se 2 (by rfl) ⟨951945, by rfl⟩ : syracuseStep 2538521 = 1903891) B1903891
theorem B4275251 : Blo 1124630 4275251 := bstep (se 1 (by rfl) ⟨3206438, by rfl⟩ : syracuseStep 4275251 = 6412877) B6412877
theorem B2538611 : Blo 1124630 2538611 := bstep (se 1 (by rfl) ⟨1903958, by rfl⟩ : syracuseStep 2538611 = 3807917) B3807917
theorem B2538647 : Blo 1124630 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B2538827 : Blo 1124630 2538827 := bstep (se 1 (by rfl) ⟨1904120, by rfl⟩ : syracuseStep 2538827 = 3808241) B3808241
theorem B2538881 : Blo 1124630 2538881 := bstep (se 2 (by rfl) ⟨952080, by rfl⟩ : syracuseStep 2538881 = 1904161) B1904161
theorem B2407819 : Blo 1124630 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B1687001 : Blo 1124630 1687001 := bstep (se 2 (by rfl) ⟨632625, by rfl⟩ : syracuseStep 1687001 = 1265251) B1265251
theorem B1687115 : Blo 1124630 1687115 := bstep (se 1 (by rfl) ⟨1265336, by rfl⟩ : syracuseStep 1687115 = 2530673) B2530673
theorem B1687127 : Blo 1124630 1687127 := bstep (se 1 (by rfl) ⟨1265345, by rfl⟩ : syracuseStep 1687127 = 2530691) B2530691
theorem B2539097 : Blo 1124630 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B1687193 : Blo 1124630 1687193 := bstep (se 2 (by rfl) ⟨632697, by rfl⟩ : syracuseStep 1687193 = 1265395) B1265395
theorem B2539187 : Blo 1124630 2539187 := bstep (se 1 (by rfl) ⟨1904390, by rfl⟩ : syracuseStep 2539187 = 3808781) B3808781
theorem B2539223 : Blo 1124630 2539223 := bstep (se 1 (by rfl) ⟨1904417, by rfl⟩ : syracuseStep 2539223 = 3808835) B3808835
theorem B1687307 : Blo 1124630 1687307 := bstep (se 1 (by rfl) ⟨1265480, by rfl⟩ : syracuseStep 1687307 = 2530961) B2530961
theorem B6405905 : Blo 1124630 6405905 := bstep (se 2 (by rfl) ⟨2402214, by rfl⟩ : syracuseStep 6405905 = 4804429) B4804429
theorem B8109841 : Blo 1124630 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B1687319 : Blo 1124630 1687319 := bstep (se 1 (by rfl) ⟨1265489, by rfl⟩ : syracuseStep 1687319 = 2530979) B2530979
theorem B2703127 : Blo 1124630 2703127 := bstep (se 1 (by rfl) ⟨2027345, by rfl⟩ : syracuseStep 2703127 = 4054691) B4054691
theorem B1687385 : Blo 1124630 1687385 := bstep (se 2 (by rfl) ⟨632769, by rfl⟩ : syracuseStep 1687385 = 1265539) B1265539
theorem B2539403 : Blo 1124630 2539403 := bstep (se 1 (by rfl) ⟨1904552, by rfl⟩ : syracuseStep 2539403 = 3809105) B3809105
theorem B1687499 : Blo 1124630 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B1687511 : Blo 1124630 1687511 := bstep (se 1 (by rfl) ⟨1265633, by rfl⟩ : syracuseStep 1687511 = 2531267) B2531267
theorem B1425367 : Blo 1124630 1425367 := bstep (se 1 (by rfl) ⟨1069025, by rfl⟩ : syracuseStep 1425367 = 2138051) B2138051
theorem B1687577 : Blo 1124630 1687577 := bstep (se 2 (by rfl) ⟨632841, by rfl⟩ : syracuseStep 1687577 = 1265683) B1265683
theorem B2408537 : Blo 1124630 2408537 := bstep (se 2 (by rfl) ⟨903201, by rfl⟩ : syracuseStep 2408537 = 1806403) B1806403
theorem B1687691 : Blo 1124630 1687691 := bstep (se 1 (by rfl) ⟨1265768, by rfl⟩ : syracuseStep 1687691 = 2531537) B2531537
theorem B1687703 : Blo 1124630 1687703 := bstep (se 1 (by rfl) ⟨1265777, by rfl⟩ : syracuseStep 1687703 = 2531555) B2531555
theorem B6406361 : Blo 1124630 6406361 := bstep (se 2 (by rfl) ⟨2402385, by rfl⟩ : syracuseStep 6406361 = 4804771) B4804771
theorem B1687769 : Blo 1124630 1687769 := bstep (se 2 (by rfl) ⟨632913, by rfl⟩ : syracuseStep 1687769 = 1265827) B1265827
theorem B1687883 : Blo 1124630 1687883 := bstep (se 1 (by rfl) ⟨1265912, by rfl⟩ : syracuseStep 1687883 = 2531825) B2531825
theorem B1687895 : Blo 1124630 1687895 := bstep (se 1 (by rfl) ⟨1265921, by rfl⟩ : syracuseStep 1687895 = 2531843) B2531843
theorem B54804853 : Blo 1124630 54804853 := bstep (se 5 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 54804853 = 5137955) B5137955
theorem B1687961 : Blo 1124630 1687961 := bstep (se 2 (by rfl) ⟨632985, by rfl⟩ : syracuseStep 1687961 = 1265971) B1265971
theorem B4276739 : Blo 1124630 4276739 := bstep (se 1 (by rfl) ⟨3207554, by rfl⟩ : syracuseStep 4276739 = 6415109) B6415109
theorem B1688075 : Blo 1124630 1688075 := bstep (se 1 (by rfl) ⟨1266056, by rfl⟩ : syracuseStep 1688075 = 2532113) B2532113
theorem B1688087 : Blo 1124630 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B3811263029 : Blo 1124630 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B1688153 : Blo 1124630 1688153 := bstep (se 2 (by rfl) ⟨633057, by rfl⟩ : syracuseStep 1688153 = 1266115) B1266115
theorem B3850841 : Blo 1124630 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B2409049 : Blo 1124630 2409049 := bstep (se 2 (by rfl) ⟨903393, by rfl⟩ : syracuseStep 2409049 = 1806787) B1806787
theorem B1688267 : Blo 1124630 1688267 := bstep (se 1 (by rfl) ⟨1266200, by rfl⟩ : syracuseStep 1688267 = 2532401) B2532401
theorem B1688279 : Blo 1124630 1688279 := bstep (se 1 (by rfl) ⟨1266209, by rfl⟩ : syracuseStep 1688279 = 2532419) B2532419
theorem B2409203 : Blo 1124630 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B1426187 : Blo 1124630 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B1688345 : Blo 1124630 1688345 := bstep (se 2 (by rfl) ⟨633129, by rfl⟩ : syracuseStep 1688345 = 1266259) B1266259
theorem B1688459 : Blo 1124630 1688459 := bstep (se 1 (by rfl) ⟨1266344, by rfl⟩ : syracuseStep 1688459 = 2532689) B2532689
theorem B1688471 : Blo 1124630 1688471 := bstep (se 1 (by rfl) ⟨1266353, by rfl⟩ : syracuseStep 1688471 = 2532707) B2532707
theorem B4277195 : Blo 1124630 4277195 := bstep (se 1 (by rfl) ⟨3207896, by rfl⟩ : syracuseStep 4277195 = 6415793) B6415793
theorem B1688537 : Blo 1124630 1688537 := bstep (se 2 (by rfl) ⟨633201, by rfl⟩ : syracuseStep 1688537 = 1266403) B1266403
theorem B1688651 : Blo 1124630 1688651 := bstep (se 1 (by rfl) ⟨1266488, by rfl⟩ : syracuseStep 1688651 = 2532977) B2532977
theorem B1688663 : Blo 1124630 1688663 := bstep (se 1 (by rfl) ⟨1266497, by rfl⟩ : syracuseStep 1688663 = 2532995) B2532995
theorem B4277393 : Blo 1124630 4277393 := bstep (se 2 (by rfl) ⟨1604022, by rfl⟩ : syracuseStep 4277393 = 3208045) B3208045
theorem B1688729 : Blo 1124630 1688729 := bstep (se 2 (by rfl) ⟨633273, by rfl⟩ : syracuseStep 1688729 = 1266547) B1266547
theorem B4572377 : Blo 1124630 4572377 := bstep (se 2 (by rfl) ⟨1714641, by rfl⟩ : syracuseStep 4572377 = 3429283) B3429283
theorem B1688843 : Blo 1124630 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1688855 : Blo 1124630 1688855 := bstep (se 1 (by rfl) ⟨1266641, by rfl⟩ : syracuseStep 1688855 = 2533283) B2533283
theorem B1688921 : Blo 1124630 1688921 := bstep (se 2 (by rfl) ⟨633345, by rfl⟩ : syracuseStep 1688921 = 1266691) B1266691
theorem B1689035 : Blo 1124630 1689035 := bstep (se 1 (by rfl) ⟨1266776, by rfl⟩ : syracuseStep 1689035 = 2533553) B2533553
theorem B1426891 : Blo 1124630 1426891 := bstep (se 1 (by rfl) ⟨1070168, by rfl⟩ : syracuseStep 1426891 = 2140337) B2140337
theorem B1689047 : Blo 1124630 1689047 := bstep (se 1 (by rfl) ⟨1266785, by rfl⟩ : syracuseStep 1689047 = 2533571) B2533571
theorem B1689113 : Blo 1124630 1689113 := bstep (se 2 (by rfl) ⟨633417, by rfl⟩ : syracuseStep 1689113 = 1266835) B1266835
theorem B24364637 : Blo 1124630 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B1689227 : Blo 1124630 1689227 := bstep (se 1 (by rfl) ⟨1266920, by rfl⟩ : syracuseStep 1689227 = 2533841) B2533841
theorem B1689239 : Blo 1124630 1689239 := bstep (se 1 (by rfl) ⟨1266929, by rfl⟩ : syracuseStep 1689239 = 2533859) B2533859
theorem B2410177 : Blo 1124630 2410177 := bstep (se 2 (by rfl) ⟨903816, by rfl⟩ : syracuseStep 2410177 = 1807633) B1807633
theorem B1427159 : Blo 1124630 1427159 := bstep (se 1 (by rfl) ⟨1070369, by rfl⟩ : syracuseStep 1427159 = 2140739) B2140739
theorem B1689305 : Blo 1124630 1689305 := bstep (se 2 (by rfl) ⟨633489, by rfl⟩ : syracuseStep 1689305 = 1266979) B1266979
theorem B1689419 : Blo 1124630 1689419 := bstep (se 1 (by rfl) ⟨1267064, by rfl⟩ : syracuseStep 1689419 = 2534129) B2534129
theorem B1689431 : Blo 1124630 1689431 := bstep (se 1 (by rfl) ⟨1267073, by rfl⟩ : syracuseStep 1689431 = 2534147) B2534147
theorem B4278167 : Blo 1124630 4278167 := bstep (se 1 (by rfl) ⟨3208625, by rfl⟩ : syracuseStep 4278167 = 6417251) B6417251
theorem B1689497 : Blo 1124630 1689497 := bstep (se 2 (by rfl) ⟨633561, by rfl⟩ : syracuseStep 1689497 = 1267123) B1267123
theorem B2312129 : Blo 1124630 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B8112089 : Blo 1124630 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B1689611 : Blo 1124630 1689611 := bstep (se 1 (by rfl) ⟨1267208, by rfl⟩ : syracuseStep 1689611 = 2534417) B2534417
theorem B1689623 : Blo 1124630 1689623 := bstep (se 1 (by rfl) ⟨1267217, by rfl⟩ : syracuseStep 1689623 = 2534435) B2534435
theorem B1689689 : Blo 1124630 1689689 := bstep (se 2 (by rfl) ⟨633633, by rfl⟩ : syracuseStep 1689689 = 1267267) B1267267
theorem B4278365 : Blo 1124630 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B1689803 : Blo 1124630 1689803 := bstep (se 1 (by rfl) ⟨1267352, by rfl⟩ : syracuseStep 1689803 = 2534705) B2534705
theorem B1689815 : Blo 1124630 1689815 := bstep (se 1 (by rfl) ⟨1267361, by rfl⟩ : syracuseStep 1689815 = 2534723) B2534723
theorem B1689881 : Blo 1124630 1689881 := bstep (se 2 (by rfl) ⟨633705, by rfl⟩ : syracuseStep 1689881 = 1267411) B1267411
theorem B5785931 : Blo 1124630 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B20531555 : Blo 1124630 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B1689995 : Blo 1124630 1689995 := bstep (se 1 (by rfl) ⟨1267496, by rfl⟩ : syracuseStep 1689995 = 2534993) B2534993
theorem B1690007 : Blo 1124630 1690007 := bstep (se 1 (by rfl) ⟨1267505, by rfl⟩ : syracuseStep 1690007 = 2535011) B2535011
theorem B1427863 : Blo 1124630 1427863 := bstep (se 1 (by rfl) ⟨1070897, by rfl⟩ : syracuseStep 1427863 = 2141795) B2141795
theorem B1690073 : Blo 1124630 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B1690187 : Blo 1124630 1690187 := bstep (se 1 (by rfl) ⟨1267640, by rfl⟩ : syracuseStep 1690187 = 2535281) B2535281
theorem B1690199 : Blo 1124630 1690199 := bstep (se 1 (by rfl) ⟨1267649, by rfl⟩ : syracuseStep 1690199 = 2535299) B2535299
theorem B1690265 : Blo 1124630 1690265 := bstep (se 2 (by rfl) ⟨633849, by rfl⟩ : syracuseStep 1690265 = 1267699) B1267699
theorem B1690379 : Blo 1124630 1690379 := bstep (se 1 (by rfl) ⟨1267784, by rfl⟩ : syracuseStep 1690379 = 2535569) B2535569
theorem B1690391 : Blo 1124630 1690391 := bstep (se 1 (by rfl) ⟨1267793, by rfl⟩ : syracuseStep 1690391 = 2535587) B2535587
theorem B43862849 : Blo 1124630 43862849 := bstep (se 2 (by rfl) ⟨16448568, by rfl⟩ : syracuseStep 43862849 = 32897137) B32897137
theorem B1690457 : Blo 1124630 1690457 := bstep (se 2 (by rfl) ⟨633921, by rfl⟩ : syracuseStep 1690457 = 1267843) B1267843
theorem B1690571 : Blo 1124630 1690571 := bstep (se 1 (by rfl) ⟨1267928, by rfl⟩ : syracuseStep 1690571 = 2535857) B2535857
theorem B1690583 : Blo 1124630 1690583 := bstep (se 1 (by rfl) ⟨1267937, by rfl⟩ : syracuseStep 1690583 = 2535875) B2535875
theorem B1690649 : Blo 1124630 1690649 := bstep (se 2 (by rfl) ⟨633993, by rfl⟩ : syracuseStep 1690649 = 1267987) B1267987
theorem B19254347 : Blo 1124630 19254347 := bstep (se 1 (by rfl) ⟨14440760, by rfl⟩ : syracuseStep 19254347 = 28881521) B28881521
theorem B1690763 : Blo 1124630 1690763 := bstep (se 1 (by rfl) ⟨1268072, by rfl⟩ : syracuseStep 1690763 = 2536145) B2536145
theorem B1690775 : Blo 1124630 1690775 := bstep (se 1 (by rfl) ⟨1268081, by rfl⟩ : syracuseStep 1690775 = 2536163) B2536163
theorem B2706635 : Blo 1124630 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B1690841 : Blo 1124630 1690841 := bstep (se 2 (by rfl) ⟨634065, by rfl⟩ : syracuseStep 1690841 = 1268131) B1268131
theorem B1690955 : Blo 1124630 1690955 := bstep (se 1 (by rfl) ⟨1268216, by rfl⟩ : syracuseStep 1690955 = 2536433) B2536433
theorem B1690967 : Blo 1124630 1690967 := bstep (se 1 (by rfl) ⟨1268225, by rfl⟩ : syracuseStep 1690967 = 2536451) B2536451
theorem B1691033 : Blo 1124630 1691033 := bstep (se 2 (by rfl) ⟨634137, by rfl⟩ : syracuseStep 1691033 = 1268275) B1268275
theorem B4804019 : Blo 1124630 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B1691147 : Blo 1124630 1691147 := bstep (se 1 (by rfl) ⟨1268360, by rfl⟩ : syracuseStep 1691147 = 2536721) B2536721
theorem B1691159 : Blo 1124630 1691159 := bstep (se 1 (by rfl) ⟨1268369, by rfl⟩ : syracuseStep 1691159 = 2536739) B2536739
theorem B17583685 : Blo 1124630 17583685 := bstep (se 4 (by rfl) ⟨1648470, by rfl⟩ : syracuseStep 17583685 = 3296941) B3296941
theorem B1691225 : Blo 1124630 1691225 := bstep (se 2 (by rfl) ⟨634209, by rfl⟩ : syracuseStep 1691225 = 1268419) B1268419
theorem B1265323 : Blo 1124630 1265323 := bstep (se 1 (by rfl) ⟨948992, by rfl⟩ : syracuseStep 1265323 = 1897985) B1897985
theorem B1691339 : Blo 1124630 1691339 := bstep (se 1 (by rfl) ⟨1268504, by rfl⟩ : syracuseStep 1691339 = 2537009) B2537009
theorem B1691351 : Blo 1124630 1691351 := bstep (se 1 (by rfl) ⟨1268513, by rfl⟩ : syracuseStep 1691351 = 2537027) B2537027
theorem B1265431 : Blo 1124630 1265431 := bstep (se 1 (by rfl) ⟨949073, by rfl⟩ : syracuseStep 1265431 = 1898147) B1898147
theorem B1691417 : Blo 1124630 1691417 := bstep (se 2 (by rfl) ⟨634281, by rfl⟩ : syracuseStep 1691417 = 1268563) B1268563
theorem B2281331 : Blo 1124630 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B1691531 : Blo 1124630 1691531 := bstep (se 1 (by rfl) ⟨1268648, by rfl⟩ : syracuseStep 1691531 = 2537297) B2537297
theorem B1691543 : Blo 1124630 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B1265611 : Blo 1124630 1265611 := bstep (se 1 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 1265611 = 1898417) B1898417
theorem B1691609 : Blo 1124630 1691609 := bstep (se 2 (by rfl) ⟨634353, by rfl⟩ : syracuseStep 1691609 = 1268707) B1268707
theorem B4280323 : Blo 1124630 4280323 := bstep (se 1 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 4280323 = 6420485) B6420485
theorem B1265719 : Blo 1124630 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B1691723 : Blo 1124630 1691723 := bstep (se 1 (by rfl) ⟨1268792, by rfl⟩ : syracuseStep 1691723 = 2537585) B2537585
theorem B1691735 : Blo 1124630 1691735 := bstep (se 1 (by rfl) ⟨1268801, by rfl⟩ : syracuseStep 1691735 = 2537603) B2537603
theorem B2314379 : Blo 1124630 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B1691801 : Blo 1124630 1691801 := bstep (se 2 (by rfl) ⟨634425, by rfl⟩ : syracuseStep 1691801 = 1268851) B1268851
theorem B1265899 : Blo 1124630 1265899 := bstep (se 1 (by rfl) ⟨949424, by rfl⟩ : syracuseStep 1265899 = 1898849) B1898849
theorem B1691915 : Blo 1124630 1691915 := bstep (se 1 (by rfl) ⟨1268936, by rfl⟩ : syracuseStep 1691915 = 2537873) B2537873
theorem B1691927 : Blo 1124630 1691927 := bstep (se 1 (by rfl) ⟨1268945, by rfl⟩ : syracuseStep 1691927 = 2537891) B2537891
theorem B4280627 : Blo 1124630 4280627 := bstep (se 1 (by rfl) ⟨3210470, by rfl⟩ : syracuseStep 4280627 = 6420941) B6420941
theorem B1266007 : Blo 1124630 1266007 := bstep (se 1 (by rfl) ⟨949505, by rfl⟩ : syracuseStep 1266007 = 1899011) B1899011
theorem B1691993 : Blo 1124630 1691993 := bstep (se 2 (by rfl) ⟨634497, by rfl⟩ : syracuseStep 1691993 = 1268995) B1268995
theorem B1692107 : Blo 1124630 1692107 := bstep (se 1 (by rfl) ⟨1269080, by rfl⟩ : syracuseStep 1692107 = 2538161) B2538161
theorem B1692119 : Blo 1124630 1692119 := bstep (se 1 (by rfl) ⟨1269089, by rfl⟩ : syracuseStep 1692119 = 2538179) B2538179
theorem B1266187 : Blo 1124630 1266187 := bstep (se 1 (by rfl) ⟨949640, by rfl⟩ : syracuseStep 1266187 = 1899281) B1899281
theorem B1626647 : Blo 1124630 1626647 := bstep (se 1 (by rfl) ⟨1219985, by rfl⟩ : syracuseStep 1626647 = 2439971) B2439971
theorem B1692185 : Blo 1124630 1692185 := bstep (se 2 (by rfl) ⟨634569, by rfl⟩ : syracuseStep 1692185 = 1269139) B1269139
theorem B12833315 : Blo 1124630 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B1266295 : Blo 1124630 1266295 := bstep (se 1 (by rfl) ⟨949721, by rfl⟩ : syracuseStep 1266295 = 1899443) B1899443
theorem B1692299 : Blo 1124630 1692299 := bstep (se 1 (by rfl) ⟨1269224, by rfl⟩ : syracuseStep 1692299 = 2538449) B2538449
theorem B1692311 : Blo 1124630 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B1692377 : Blo 1124630 1692377 := bstep (se 2 (by rfl) ⟨634641, by rfl⟩ : syracuseStep 1692377 = 1269283) B1269283
theorem B8540963 : Blo 1124630 8540963 := bstep (se 1 (by rfl) ⟨6405722, by rfl⟩ : syracuseStep 8540963 = 12811445) B12811445
theorem B1266475 : Blo 1124630 1266475 := bstep (se 1 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 1266475 = 1899713) B1899713
theorem B1692491 : Blo 1124630 1692491 := bstep (se 1 (by rfl) ⟨1269368, by rfl⟩ : syracuseStep 1692491 = 2538737) B2538737
theorem B1692503 : Blo 1124630 1692503 := bstep (se 1 (by rfl) ⟨1269377, by rfl⟩ : syracuseStep 1692503 = 2538755) B2538755
theorem B4805507 : Blo 1124630 4805507 := bstep (se 1 (by rfl) ⟨3604130, by rfl⟩ : syracuseStep 4805507 = 7208261) B7208261
theorem B1266583 : Blo 1124630 1266583 := bstep (se 1 (by rfl) ⟨949937, by rfl⟩ : syracuseStep 1266583 = 1899875) B1899875
theorem B1692569 : Blo 1124630 1692569 := bstep (se 2 (by rfl) ⟨634713, by rfl⟩ : syracuseStep 1692569 = 1269427) B1269427
theorem B4281281 : Blo 1124630 4281281 := bstep (se 2 (by rfl) ⟨1605480, by rfl⟩ : syracuseStep 4281281 = 3210961) B3210961
theorem B1692683 : Blo 1124630 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B1692695 : Blo 1124630 1692695 := bstep (se 1 (by rfl) ⟨1269521, by rfl⟩ : syracuseStep 1692695 = 2539043) B2539043
theorem B1266763 : Blo 1124630 1266763 := bstep (se 1 (by rfl) ⟨950072, by rfl⟩ : syracuseStep 1266763 = 1900145) B1900145
theorem B1692761 : Blo 1124630 1692761 := bstep (se 2 (by rfl) ⟨634785, by rfl⟩ : syracuseStep 1692761 = 1269571) B1269571
theorem B1266871 : Blo 1124630 1266871 := bstep (se 1 (by rfl) ⟨950153, by rfl⟩ : syracuseStep 1266871 = 1900307) B1900307
theorem B1692875 : Blo 1124630 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B1692887 : Blo 1124630 1692887 := bstep (se 1 (by rfl) ⟨1269665, by rfl⟩ : syracuseStep 1692887 = 2539331) B2539331
theorem B1267051 : Blo 1124630 1267051 := bstep (se 1 (by rfl) ⟨950288, by rfl⟩ : syracuseStep 1267051 = 1900577) B1900577
theorem B5133761 : Blo 1124630 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B1267159 : Blo 1124630 1267159 := bstep (se 1 (by rfl) ⟨950369, by rfl⟩ : syracuseStep 1267159 = 1900739) B1900739
theorem B6411737 : Blo 1124630 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B5133869 : Blo 1124630 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B1267339 : Blo 1124630 1267339 := bstep (se 1 (by rfl) ⟨950504, by rfl⟩ : syracuseStep 1267339 = 1901009) B1901009
theorem B2709143 : Blo 1124630 2709143 := bstep (se 1 (by rfl) ⟨2031857, by rfl⟩ : syracuseStep 2709143 = 4063715) B4063715
theorem B1267447 : Blo 1124630 1267447 := bstep (se 1 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 1267447 = 1901171) B1901171
theorem B1267627 : Blo 1124630 1267627 := bstep (se 1 (by rfl) ⟨950720, by rfl⟩ : syracuseStep 1267627 = 1901441) B1901441
theorem B1267735 : Blo 1124630 1267735 := bstep (se 1 (by rfl) ⟨950801, by rfl⟩ : syracuseStep 1267735 = 1901603) B1901603
theorem B2283635 : Blo 1124630 2283635 := bstep (se 1 (by rfl) ⟨1712726, by rfl⟩ : syracuseStep 2283635 = 3425453) B3425453
theorem B43341965 : Blo 1124630 43341965 := bstep (se 3 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 43341965 = 16253237) B16253237
theorem B3954839 : Blo 1124630 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B4282541 : Blo 1124630 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B1267915 : Blo 1124630 1267915 := bstep (se 1 (by rfl) ⟨950936, by rfl⟩ : syracuseStep 1267915 = 1901873) B1901873
theorem B4282571 : Blo 1124630 4282571 := bstep (se 1 (by rfl) ⟨3211928, by rfl⟩ : syracuseStep 4282571 = 6423857) B6423857
theorem B1202423 : Blo 1124630 1202423 := bstep (se 1 (by rfl) ⟨901817, by rfl⟩ : syracuseStep 1202423 = 1803635) B1803635
theorem B1268023 : Blo 1124630 1268023 := bstep (se 1 (by rfl) ⟨951017, by rfl⟩ : syracuseStep 1268023 = 1902035) B1902035
theorem B1268203 : Blo 1124630 1268203 := bstep (se 1 (by rfl) ⟨951152, by rfl⟩ : syracuseStep 1268203 = 1902305) B1902305
theorem B1268311 : Blo 1124630 1268311 := bstep (se 1 (by rfl) ⟨951233, by rfl⟩ : syracuseStep 1268311 = 1902467) B1902467
theorem B1268491 : Blo 1124630 1268491 := bstep (se 1 (by rfl) ⟨951368, by rfl⟩ : syracuseStep 1268491 = 1902737) B1902737
theorem B4283225 : Blo 1124630 4283225 := bstep (se 2 (by rfl) ⟨1606209, by rfl⟩ : syracuseStep 4283225 = 3212419) B3212419
theorem B1268599 : Blo 1124630 1268599 := bstep (se 1 (by rfl) ⟨951449, by rfl⟩ : syracuseStep 1268599 = 1902899) B1902899
theorem B1268779 : Blo 1124630 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B4807745 : Blo 1124630 4807745 := bstep (se 2 (by rfl) ⟨1802904, by rfl⟩ : syracuseStep 4807745 = 3605809) B3605809
theorem B6413377 : Blo 1124630 6413377 := bstep (se 2 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 6413377 = 4810033) B4810033
theorem B17357975 : Blo 1124630 17357975 := bstep (se 1 (by rfl) ⟨13018481, by rfl⟩ : syracuseStep 17357975 = 26036963) B26036963
theorem B1268887 : Blo 1124630 1268887 := bstep (se 1 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 1268887 = 1903331) B1903331
theorem B4283543 : Blo 1124630 4283543 := bstep (se 1 (by rfl) ⟨3212657, by rfl⟩ : syracuseStep 4283543 = 6425315) B6425315
theorem B1269067 : Blo 1124630 1269067 := bstep (se 1 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 1269067 = 1903601) B1903601
theorem B8117597 : Blo 1124630 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B1269175 : Blo 1124630 1269175 := bstep (se 1 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 1269175 = 1903763) B1903763
theorem B1269355 : Blo 1124630 1269355 := bstep (se 1 (by rfl) ⟨952016, by rfl⟩ : syracuseStep 1269355 = 1904033) B1904033
theorem B1302199 : Blo 1124630 1302199 := bstep (se 1 (by rfl) ⟨976649, by rfl⟩ : syracuseStep 1302199 = 1953299) B1953299
theorem B1269463 : Blo 1124630 1269463 := bstep (se 1 (by rfl) ⟨952097, by rfl⟩ : syracuseStep 1269463 = 1904195) B1904195
theorem B4054835 : Blo 1124630 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B4284211 : Blo 1124630 4284211 := bstep (se 1 (by rfl) ⟨3213158, by rfl⟩ : syracuseStep 4284211 = 6426317) B6426317
theorem B1269643 : Blo 1124630 1269643 := bstep (se 1 (by rfl) ⟨952232, by rfl⟩ : syracuseStep 1269643 = 1904465) B1904465
theorem B1204183 : Blo 1124630 1204183 := bstep (se 1 (by rfl) ⟨903137, by rfl⟩ : syracuseStep 1204183 = 1806275) B1806275
theorem B24404003 : Blo 1124630 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B1302571 : Blo 1124630 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B2711603 : Blo 1124630 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B2711641 : Blo 1124630 2711641 := bstep (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) B2033731
theorem B3203545 : Blo 1124630 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B6840877 : Blo 1124630 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B4809419 : Blo 1124630 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B1205003 : Blo 1124630 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B5202733 : Blo 1124630 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B3204161 : Blo 1124630 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B2057345 : Blo 1124630 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B5137667 : Blo 1124630 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B5694785 : Blo 1124630 5694785 := bstep (se 2 (by rfl) ⟨2135544, by rfl⟩ : syracuseStep 5694785 = 4271089) B4271089
theorem B4056493 : Blo 1124630 4056493 := bstep (se 3 (by rfl) ⟨760592, by rfl⟩ : syracuseStep 4056493 = 1521185) B1521185
theorem B4810205 : Blo 1124630 4810205 := bstep (se 3 (by rfl) ⟨901913, by rfl⟩ : syracuseStep 4810205 = 1803827) B1803827
theorem B2287169 : Blo 1124630 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B9758387 : Blo 1124630 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B14444405 : Blo 1124630 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B8546309 : Blo 1124630 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B3664151 : Blo 1124630 3664151 := bstep (se 1 (by rfl) ⟨2748113, by rfl⟩ : syracuseStep 3664151 = 5496227) B5496227
theorem B6416819 : Blo 1124630 6416819 := bstep (se 1 (by rfl) ⟨4812614, by rfl⟩ : syracuseStep 6416819 = 9625229) B9625229
theorem B13560281 : Blo 1124630 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B3795659 : Blo 1124630 3795659 := bstep (se 1 (by rfl) ⟨2846744, by rfl⟩ : syracuseStep 3795659 = 5693489) B5693489
theorem B4811537 : Blo 1124630 4811537 := bstep (se 2 (by rfl) ⟨1804326, by rfl⟩ : syracuseStep 4811537 = 3608653) B3608653
theorem B10840877 : Blo 1124630 10840877 := bstep (se 3 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 10840877 = 4065329) B4065329
theorem B14445377 : Blo 1124630 14445377 := bstep (se 2 (by rfl) ⟨5417016, by rfl⟩ : syracuseStep 14445377 = 10834033) B10834033
theorem B3042251 : Blo 1124630 3042251 := bstep (se 1 (by rfl) ⟨2281688, by rfl⟩ : syracuseStep 3042251 = 4563377) B4563377
theorem B3795929 : Blo 1124630 3795929 := bstep (se 2 (by rfl) ⟨1423473, by rfl⟩ : syracuseStep 3795929 = 2846947) B2846947
theorem B41184217 : Blo 1124630 41184217 := bstep (se 2 (by rfl) ⟨15444081, by rfl⟩ : syracuseStep 41184217 = 30888163) B30888163
theorem B6843457 : Blo 1124630 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B3042379 : Blo 1124630 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B1928267 : Blo 1124630 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B3206233 : Blo 1124630 3206233 := bstep (se 2 (by rfl) ⟨1202337, by rfl⟩ : syracuseStep 3206233 = 2404675) B2404675
theorem B14281859 : Blo 1124630 14281859 := bstep (se 1 (by rfl) ⟨10711394, by rfl⟩ : syracuseStep 14281859 = 21422789) B21422789
theorem B2026711 : Blo 1124630 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B5696729 : Blo 1124630 5696729 := bstep (se 2 (by rfl) ⟨2136273, by rfl⟩ : syracuseStep 5696729 = 4272547) B4272547
theorem B2059609 : Blo 1124630 2059609 := bstep (se 2 (by rfl) ⟨772353, by rfl⟩ : syracuseStep 2059609 = 1544707) B1544707
theorem B3206621 : Blo 1124630 3206621 := bstep (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) B1202483
theorem B3796631 : Blo 1124630 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B6418277 : Blo 1124630 6418277 := bstep (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) B1203427
theorem B4059031 : Blo 1124630 4059031 := bstep (se 1 (by rfl) ⟨3044273, by rfl⟩ : syracuseStep 4059031 = 6088547) B6088547
theorem B4812803 : Blo 1124630 4812803 := bstep (se 1 (by rfl) ⟨3609602, by rfl⟩ : syracuseStep 4812803 = 7219205) B7219205
theorem B2846785 : Blo 1124630 2846785 := bstep (se 2 (by rfl) ⟨1067544, by rfl⟩ : syracuseStep 2846785 = 2135089) B2135089
theorem B3797171 : Blo 1124630 3797171 := bstep (se 1 (by rfl) ⟨2847878, by rfl⟩ : syracuseStep 3797171 = 5695757) B5695757
theorem B8548739 : Blo 1124630 8548739 := bstep (se 1 (by rfl) ⟨6411554, by rfl⟩ : syracuseStep 8548739 = 12823109) B12823109
theorem B3797441 : Blo 1124630 3797441 := bstep (se 2 (by rfl) ⟨1424040, by rfl⟩ : syracuseStep 3797441 = 2848081) B2848081
theorem B6844945 : Blo 1124630 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B1602137 : Blo 1124630 1602137 := bstep (se 2 (by rfl) ⟨600801, by rfl⟩ : syracuseStep 1602137 = 1201603) B1201603
theorem B2847383 : Blo 1124630 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B2028311 : Blo 1124630 2028311 := bstep (se 1 (by rfl) ⟨1521233, by rfl⟩ : syracuseStep 2028311 = 3042467) B3042467
theorem B5698349 : Blo 1124630 5698349 := bstep (se 3 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 5698349 = 2136881) B2136881
theorem B24343361 : Blo 1124630 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B3797981 : Blo 1124630 3797981 := bstep (se 3 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 3797981 = 1424243) B1424243
theorem B20542481 : Blo 1124630 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B1209463 : Blo 1124630 1209463 := bstep (se 1 (by rfl) ⟨907097, by rfl⟩ : syracuseStep 1209463 = 1814195) B1814195
theorem B8123597 : Blo 1124630 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B8352973 : Blo 1124630 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1602775 : Blo 1124630 1602775 := bstep (se 1 (by rfl) ⟨1202081, by rfl⟩ : syracuseStep 1602775 = 2404163) B2404163
theorem B2848193 : Blo 1124630 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B1897931 : Blo 1124630 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B1898059 : Blo 1124630 1898059 := bstep (se 1 (by rfl) ⟨1423544, by rfl⟩ : syracuseStep 1898059 = 2847089) B2847089
theorem B5863063 : Blo 1124630 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B8124083 : Blo 1124630 8124083 := bstep (se 1 (by rfl) ⟨6093062, by rfl⟩ : syracuseStep 8124083 = 12186125) B12186125
theorem B1898201 : Blo 1124630 1898201 := bstep (se 2 (by rfl) ⟨711825, by rfl⟩ : syracuseStep 1898201 = 1423651) B1423651
theorem B1898329 : Blo 1124630 1898329 := bstep (se 2 (by rfl) ⟨711873, by rfl⟩ : syracuseStep 1898329 = 1423747) B1423747
theorem B1603481 : Blo 1124630 1603481 := bstep (se 2 (by rfl) ⟨601305, by rfl⟩ : syracuseStep 1603481 = 1202611) B1202611
theorem B2848729 : Blo 1124630 2848729 := bstep (se 2 (by rfl) ⟨1068273, by rfl⟩ : syracuseStep 2848729 = 2136547) B2136547
theorem B1603595 : Blo 1124630 1603595 := bstep (se 1 (by rfl) ⟨1202696, by rfl⟩ : syracuseStep 1603595 = 2405393) B2405393
theorem B3799115 : Blo 1124630 3799115 := bstep (se 1 (by rfl) ⟨2849336, by rfl⟩ : syracuseStep 3799115 = 5698673) B5698673
theorem B3209537 : Blo 1124630 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B3799385 : Blo 1124630 3799385 := bstep (se 2 (by rfl) ⟨1424769, by rfl⟩ : syracuseStep 3799385 = 2849539) B2849539
theorem B1898903 : Blo 1124630 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B6093235 : Blo 1124630 6093235 := bstep (se 1 (by rfl) ⟨4569926, by rfl⟩ : syracuseStep 6093235 = 9139853) B9139853
theorem B3209651 : Blo 1124630 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B1899031 : Blo 1124630 1899031 := bstep (se 1 (by rfl) ⟨1424273, by rfl⟩ : syracuseStep 1899031 = 2848547) B2848547
theorem B1604119 : Blo 1124630 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B2030359 : Blo 1124630 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B3800087 : Blo 1124630 3800087 := bstep (se 1 (by rfl) ⟨2850065, by rfl⟩ : syracuseStep 3800087 = 5700131) B5700131
theorem B4815895 : Blo 1124630 4815895 := bstep (se 1 (by rfl) ⟨3611921, by rfl⟩ : syracuseStep 4815895 = 7223843) B7223843
theorem B2030617 : Blo 1124630 2030617 := bstep (se 2 (by rfl) ⟨761481, by rfl⟩ : syracuseStep 2030617 = 1522963) B1522963
theorem B2849843 : Blo 1124630 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B1899659 : Blo 1124630 1899659 := bstep (se 1 (by rfl) ⟨1424744, by rfl⟩ : syracuseStep 1899659 = 2849489) B2849489
theorem B72973493 : Blo 1124630 72973493 := bstep (se 5 (by rfl) ⟨3420632, by rfl⟩ : syracuseStep 72973493 = 6841265) B6841265
theorem B1899787 : Blo 1124630 1899787 := bstep (se 1 (by rfl) ⟨1424840, by rfl⟩ : syracuseStep 1899787 = 2849681) B2849681
theorem B1604939 : Blo 1124630 1604939 := bstep (se 1 (by rfl) ⟨1203704, by rfl⟩ : syracuseStep 1604939 = 2407409) B2407409
theorem B2030935 : Blo 1124630 2030935 := bstep (se 1 (by rfl) ⟨1523201, by rfl⟩ : syracuseStep 2030935 = 3046403) B3046403
theorem B2850137 : Blo 1124630 2850137 := bstep (se 2 (by rfl) ⟨1068801, by rfl⟩ : syracuseStep 2850137 = 2137603) B2137603
theorem B1899929 : Blo 1124630 1899929 := bstep (se 2 (by rfl) ⟨712473, by rfl⟩ : syracuseStep 1899929 = 1424947) B1424947
theorem B1801739 : Blo 1124630 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B1900057 : Blo 1124630 1900057 := bstep (se 2 (by rfl) ⟨712521, by rfl⟩ : syracuseStep 1900057 = 1425043) B1425043
theorem B3800627 : Blo 1124630 3800627 := bstep (se 1 (by rfl) ⟨2850470, by rfl⟩ : syracuseStep 3800627 = 5700941) B5700941
theorem B3046987 : Blo 1124630 3046987 := bstep (se 1 (by rfl) ⟨2285240, by rfl⟩ : syracuseStep 3046987 = 4570481) B4570481
theorem B8552141 : Blo 1124630 8552141 := bstep (se 3 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 8552141 = 3207053) B3207053
theorem B3800897 : Blo 1124630 3800897 := bstep (se 2 (by rfl) ⟨1425336, by rfl⟩ : syracuseStep 3800897 = 2850673) B2850673
theorem B1802071 : Blo 1124630 1802071 := bstep (se 1 (by rfl) ⟨1351553, by rfl⟩ : syracuseStep 1802071 = 2703107) B2703107
theorem B7208797 : Blo 1124630 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B12844979 : Blo 1124630 12844979 := bstep (se 1 (by rfl) ⟨9633734, by rfl⟩ : syracuseStep 12844979 = 19267469) B19267469
theorem B1605691 : Blo 1124630 1605691 := bstep (se 1 (by rfl) ⟨1204268, by rfl⟩ : syracuseStep 1605691 = 2408537) B2408537
theorem B5701751 : Blo 1124630 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B6947045 : Blo 1124630 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B2851159 : Blo 1124630 2851159 := bstep (se 1 (by rfl) ⟨2138369, by rfl⟩ : syracuseStep 2851159 = 4276739) B4276739
theorem B3801491 : Blo 1124630 3801491 := bstep (se 1 (by rfl) ⟨2851118, by rfl⟩ : syracuseStep 3801491 = 5702237) B5702237
theorem B73073137 : Blo 1124630 73073137 := bstep (se 2 (by rfl) ⟨27402426, by rfl⟩ : syracuseStep 73073137 = 54804853) B54804853
theorem B6423083 : Blo 1124630 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B2032247 : Blo 1124630 2032247 := bstep (se 1 (by rfl) ⟨1524185, by rfl⟩ : syracuseStep 2032247 = 3048371) B3048371
theorem B2851463 : Blo 1124630 2851463 := bstep (se 1 (by rfl) ⟨2138597, by rfl⟩ : syracuseStep 2851463 = 4277195) B4277195
theorem B1901191 : Blo 1124630 1901191 := bstep (se 1 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 1901191 = 2851787) B2851787
theorem B2851595 : Blo 1124630 2851595 := bstep (se 1 (by rfl) ⟨2138696, by rfl⟩ : syracuseStep 2851595 = 4277393) B4277393
theorem B3212065 : Blo 1124630 3212065 := bstep (se 2 (by rfl) ⟨1204524, by rfl⟩ : syracuseStep 3212065 = 2409049) B2409049
theorem B3048251 : Blo 1124630 3048251 := bstep (se 1 (by rfl) ⟨2286188, by rfl⟩ : syracuseStep 3048251 = 4572377) B4572377
theorem B54887381 : Blo 1124630 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B5702723 : Blo 1124630 5702723 := bstep (se 1 (by rfl) ⟨4277042, by rfl⟩ : syracuseStep 5702723 = 8554085) B8554085
theorem B2852111 : Blo 1124630 2852111 := bstep (se 1 (by rfl) ⟨2139083, by rfl⟩ : syracuseStep 2852111 = 4278167) B4278167
theorem B1901839 : Blo 1124630 1901839 := bstep (se 1 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 1901839 = 2852759) B2852759
theorem B5408059 : Blo 1124630 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B5703047 : Blo 1124630 5703047 := bstep (se 1 (by rfl) ⟨4277285, by rfl⟩ : syracuseStep 5703047 = 8554571) B8554571
theorem B2852243 : Blo 1124630 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B3802895 : Blo 1124630 3802895 := bstep (se 1 (by rfl) ⟨2852171, by rfl⟩ : syracuseStep 3802895 = 5704343) B5704343
theorem B1902379 : Blo 1124630 1902379 := bstep (se 1 (by rfl) ⟨1426784, by rfl⟩ : syracuseStep 1902379 = 2853569) B2853569
theorem B5408657 : Blo 1124630 5408657 := bstep (se 2 (by rfl) ⟨2028246, by rfl⟩ : syracuseStep 5408657 = 4056493) B4056493
theorem B1902521 : Blo 1124630 1902521 := bstep (se 2 (by rfl) ⟨713445, by rfl⟩ : syracuseStep 1902521 = 1426891) B1426891
theorem B6424541 : Blo 1124630 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B3803165 : Blo 1124630 3803165 := bstep (se 3 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 3803165 = 1426187) B1426187
theorem B3213341 : Blo 1124630 3213341 := bstep (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) B1205003
theorem B3213569 : Blo 1124630 3213569 := bstep (se 2 (by rfl) ⟨1205088, by rfl⟩ : syracuseStep 3213569 = 2410177) B2410177
theorem B6425041 : Blo 1124630 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B2853377 : Blo 1124630 2853377 := bstep (se 2 (by rfl) ⟨1070016, by rfl⟩ : syracuseStep 2853377 = 2140033) B2140033
theorem B3213911 : Blo 1124630 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B1903223 : Blo 1124630 1903223 := bstep (se 1 (by rfl) ⟨1427417, by rfl⟩ : syracuseStep 1903223 = 2854835) B2854835
theorem B3607411 : Blo 1124630 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B2853751 : Blo 1124630 2853751 := bstep (se 1 (by rfl) ⟨2140313, by rfl⟩ : syracuseStep 2853751 = 4280627) B4280627
theorem B8555543 : Blo 1124630 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B1903675 : Blo 1124630 1903675 := bstep (se 1 (by rfl) ⟨1427756, by rfl⟩ : syracuseStep 1903675 = 2855513) B2855513
theorem B1903817 : Blo 1124630 1903817 := bstep (se 2 (by rfl) ⟨713931, by rfl⟩ : syracuseStep 1903817 = 1427863) B1427863
theorem B2854187 : Blo 1124630 2854187 := bstep (se 1 (by rfl) ⟨2140640, by rfl⟩ : syracuseStep 2854187 = 4281281) B4281281
theorem B3804569 : Blo 1124630 3804569 := bstep (se 2 (by rfl) ⟨1426713, by rfl⟩ : syracuseStep 3804569 = 2853427) B2853427
theorem B1806095 : Blo 1124630 1806095 := bstep (se 1 (by rfl) ⟨1354571, by rfl⟩ : syracuseStep 1806095 = 2709143) B2709143
theorem B1904519 : Blo 1124630 1904519 := bstep (se 1 (by rfl) ⟨1428389, by rfl⟩ : syracuseStep 1904519 = 2856779) B2856779
theorem B3805271 : Blo 1124630 3805271 := bstep (se 1 (by rfl) ⟨2853953, by rfl⟩ : syracuseStep 3805271 = 5707907) B5707907
theorem B2855027 : Blo 1124630 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B2855047 : Blo 1124630 2855047 := bstep (se 1 (by rfl) ⟨2141285, by rfl⟩ : syracuseStep 2855047 = 4282571) B4282571
theorem B12849353 : Blo 1124630 12849353 := bstep (se 2 (by rfl) ⟨4818507, by rfl⟩ : syracuseStep 12849353 = 9637015) B9637015
theorem B6427025 : Blo 1124630 6427025 := bstep (se 2 (by rfl) ⟨2410134, by rfl⟩ : syracuseStep 6427025 = 4820269) B4820269
theorem B2855321 : Blo 1124630 2855321 := bstep (se 2 (by rfl) ⟨1070745, by rfl⟩ : syracuseStep 2855321 = 2141491) B2141491
theorem B6951377 : Blo 1124630 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B2855483 : Blo 1124630 2855483 := bstep (se 1 (by rfl) ⟨2141612, by rfl⟩ : syracuseStep 2855483 = 4283225) B4283225
theorem B3805757 : Blo 1124630 3805757 := bstep (se 3 (by rfl) ⟨713579, by rfl⟩ : syracuseStep 3805757 = 1427159) B1427159
theorem B11571983 : Blo 1124630 11571983 := bstep (se 1 (by rfl) ⟨8678987, by rfl⟩ : syracuseStep 11571983 = 17357975) B17357975
theorem B2855695 : Blo 1124630 2855695 := bstep (se 1 (by rfl) ⟨2141771, by rfl⟩ : syracuseStep 2855695 = 4283543) B4283543
theorem B5706611 : Blo 1124630 5706611 := bstep (se 1 (by rfl) ⟨4279958, by rfl⟩ : syracuseStep 5706611 = 8559917) B8559917
theorem B5641145 : Blo 1124630 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B2855969 : Blo 1124630 2855969 := bstep (se 2 (by rfl) ⟨1070988, by rfl⟩ : syracuseStep 2855969 = 2141977) B2141977
theorem B9638999 : Blo 1124630 9638999 := bstep (se 1 (by rfl) ⟨7229249, by rfl⟩ : syracuseStep 9638999 = 14458499) B14458499
theorem B3085427 : Blo 1124630 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B6165677 : Blo 1124630 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B5412041 : Blo 1124630 5412041 := bstep (se 2 (by rfl) ⟨2029515, by rfl⟩ : syracuseStep 5412041 = 4059031) B4059031
theorem B5707097 : Blo 1124630 5707097 := bstep (se 2 (by rfl) ⟨2140161, by rfl⟩ : syracuseStep 5707097 = 4280323) B4280323
theorem B8131985 : Blo 1124630 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B24352177 : Blo 1124630 24352177 := bstep (se 2 (by rfl) ⟨9132066, by rfl⟩ : syracuseStep 24352177 = 18264133) B18264133
theorem B16226021 : Blo 1124630 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B3807161 : Blo 1124630 3807161 := bstep (se 2 (by rfl) ⟨1427685, by rfl⟩ : syracuseStep 3807161 = 2855371) B2855371
theorem B2136107 : Blo 1124630 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B5773619 : Blo 1124630 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B3807755 : Blo 1124630 3807755 := bstep (se 1 (by rfl) ⟨2855816, by rfl⟩ : syracuseStep 3807755 = 5711633) B5711633
theorem B3807863 : Blo 1124630 3807863 := bstep (se 1 (by rfl) ⟨2855897, by rfl⟩ : syracuseStep 3807863 = 5711795) B5711795
theorem B2137033 : Blo 1124630 2137033 := bstep (se 2 (by rfl) ⟨801387, by rfl⟩ : syracuseStep 2137033 = 1602775) B1602775
theorem B12852269 : Blo 1124630 12852269 := bstep (se 3 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 12852269 = 4819601) B4819601
theorem B2530439 : Blo 1124630 2530439 := bstep (se 1 (by rfl) ⟨1897829, by rfl⟩ : syracuseStep 2530439 = 3795659) B3795659
theorem B3808457 : Blo 1124630 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B2530619 : Blo 1124630 2530619 := bstep (se 1 (by rfl) ⟨1897964, by rfl⟩ : syracuseStep 2530619 = 3795929) B3795929
theorem B4332935 : Blo 1124630 4332935 := bstep (se 1 (by rfl) ⟨3249701, by rfl⟩ : syracuseStep 4332935 = 6499403) B6499403
theorem B1285511 : Blo 1124630 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B5709203 : Blo 1124630 5709203 := bstep (se 1 (by rfl) ⟨4281902, by rfl⟩ : syracuseStep 5709203 = 8563805) B8563805
theorem B2530745 : Blo 1124630 2530745 := bstep (se 2 (by rfl) ⟨949029, by rfl⟩ : syracuseStep 2530745 = 1898059) B1898059
theorem B6495709 : Blo 1124630 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B2137747 : Blo 1124630 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B5480129 : Blo 1124630 5480129 := bstep (se 2 (by rfl) ⟨2055048, by rfl⟩ : syracuseStep 5480129 = 4110097) B4110097
theorem B2531087 : Blo 1124630 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B2531105 : Blo 1124630 2531105 := bstep (se 2 (by rfl) ⟨949164, by rfl⟩ : syracuseStep 2531105 = 1898329) B1898329
theorem B2531447 : Blo 1124630 2531447 := bstep (se 1 (by rfl) ⟨1898585, by rfl⟩ : syracuseStep 2531447 = 3797171) B3797171
theorem B2531627 : Blo 1124630 2531627 := bstep (se 1 (by rfl) ⟨1898720, by rfl⟩ : syracuseStep 2531627 = 3797441) B3797441
theorem B1352207 : Blo 1124630 1352207 := bstep (se 1 (by rfl) ⟨1014155, by rfl⟩ : syracuseStep 1352207 = 2028311) B2028311
theorem B7217693 : Blo 1124630 7217693 := bstep (se 3 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 7217693 = 2706635) B2706635
theorem B16228907 : Blo 1124630 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B2531987 : Blo 1124630 2531987 := bstep (se 1 (by rfl) ⟨1898990, by rfl⟩ : syracuseStep 2531987 = 3797981) B3797981
theorem B2532041 : Blo 1124630 2532041 := bstep (se 2 (by rfl) ⟨949515, by rfl⟩ : syracuseStep 2532041 = 1899031) B1899031
theorem B2138825 : Blo 1124630 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B5415731 : Blo 1124630 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B5416055 : Blo 1124630 5416055 := bstep (se 1 (by rfl) ⟨4062041, by rfl⟩ : syracuseStep 5416055 = 8124083) B8124083
theorem B2532743 : Blo 1124630 2532743 := bstep (se 1 (by rfl) ⟨1899557, by rfl⟩ : syracuseStep 2532743 = 3799115) B3799115
theorem B2139691 : Blo 1124630 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B2532923 : Blo 1124630 2532923 := bstep (se 1 (by rfl) ⟨1899692, by rfl⟩ : syracuseStep 2532923 = 3799385) B3799385
theorem B2139767 : Blo 1124630 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B2565767 : Blo 1124630 2565767 := bstep (se 1 (by rfl) ⟨1924325, by rfl⟩ : syracuseStep 2565767 = 3848651) B3848651
theorem B2533049 : Blo 1124630 2533049 := bstep (se 2 (by rfl) ⟨949893, by rfl⟩ : syracuseStep 2533049 = 1899787) B1899787
theorem B24323813 : Blo 1124630 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B9611045 : Blo 1124630 9611045 := bstep (se 4 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 9611045 = 1802071) B1802071
theorem B2533391 : Blo 1124630 2533391 := bstep (se 1 (by rfl) ⟨1900043, by rfl⟩ : syracuseStep 2533391 = 3800087) B3800087
theorem B2533409 : Blo 1124630 2533409 := bstep (se 2 (by rfl) ⟨950028, by rfl⟩ : syracuseStep 2533409 = 1900057) B1900057
theorem B1124667 : Blo 1124630 1124667 := bstep (se 1 (by rfl) ⟨843500, by rfl⟩ : syracuseStep 1124667 = 1687001) B1687001
theorem B2533751 : Blo 1124630 2533751 := bstep (se 1 (by rfl) ⟨1900313, by rfl⟩ : syracuseStep 2533751 = 3800627) B3800627
theorem B1124743 : Blo 1124630 1124743 := bstep (se 1 (by rfl) ⟨843557, by rfl⟩ : syracuseStep 1124743 = 1687115) B1687115
theorem B1124751 : Blo 1124630 1124751 := bstep (se 1 (by rfl) ⟨843563, by rfl⟩ : syracuseStep 1124751 = 1687127) B1687127
theorem B5712281 : Blo 1124630 5712281 := bstep (se 2 (by rfl) ⟨2142105, by rfl⟩ : syracuseStep 5712281 = 4284211) B4284211
theorem B1124795 : Blo 1124630 1124795 := bstep (se 1 (by rfl) ⟨843596, by rfl⟩ : syracuseStep 1124795 = 1687193) B1687193
theorem B9611729 : Blo 1124630 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B1124871 : Blo 1124630 1124871 := bstep (se 1 (by rfl) ⟨843653, by rfl⟩ : syracuseStep 1124871 = 1687307) B1687307
theorem B4270603 : Blo 1124630 4270603 := bstep (se 1 (by rfl) ⟨3202952, by rfl⟩ : syracuseStep 4270603 = 6405905) B6405905
theorem B1124879 : Blo 1124630 1124879 := bstep (se 1 (by rfl) ⟨843659, by rfl⟩ : syracuseStep 1124879 = 1687319) B1687319
theorem B2533931 : Blo 1124630 2533931 := bstep (se 1 (by rfl) ⟨1900448, by rfl⟩ : syracuseStep 2533931 = 3800897) B3800897
theorem B1124923 : Blo 1124630 1124923 := bstep (se 1 (by rfl) ⟨843692, by rfl⟩ : syracuseStep 1124923 = 1687385) B1687385
theorem B8563319 : Blo 1124630 8563319 := bstep (se 1 (by rfl) ⟨6422489, by rfl⟩ : syracuseStep 8563319 = 12844979) B12844979
theorem B1124999 : Blo 1124630 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B1125007 : Blo 1124630 1125007 := bstep (se 1 (by rfl) ⟨843755, by rfl⟩ : syracuseStep 1125007 = 1687511) B1687511
theorem B1125051 : Blo 1124630 1125051 := bstep (se 1 (by rfl) ⟨843788, by rfl⟩ : syracuseStep 1125051 = 1687577) B1687577
theorem B1125127 : Blo 1124630 1125127 := bstep (se 1 (by rfl) ⟨843845, by rfl⟩ : syracuseStep 1125127 = 1687691) B1687691
theorem B1125135 : Blo 1124630 1125135 := bstep (se 1 (by rfl) ⟨843851, by rfl⟩ : syracuseStep 1125135 = 1687703) B1687703
theorem B3615521 : Blo 1124630 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B4270907 : Blo 1124630 4270907 := bstep (se 1 (by rfl) ⟨3203180, by rfl⟩ : syracuseStep 4270907 = 6406361) B6406361
theorem B1125179 : Blo 1124630 1125179 := bstep (se 1 (by rfl) ⟨843884, by rfl⟩ : syracuseStep 1125179 = 1687769) B1687769
theorem B1125255 : Blo 1124630 1125255 := bstep (se 1 (by rfl) ⟨843941, by rfl⟩ : syracuseStep 1125255 = 1687883) B1687883
theorem B1125263 : Blo 1124630 1125263 := bstep (se 1 (by rfl) ⟨843947, by rfl⟩ : syracuseStep 1125263 = 1687895) B1687895
theorem B1354639 : Blo 1124630 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B2534291 : Blo 1124630 2534291 := bstep (se 1 (by rfl) ⟨1900718, by rfl⟩ : syracuseStep 2534291 = 3801437) B3801437
theorem B1125307 : Blo 1124630 1125307 := bstep (se 1 (by rfl) ⟨843980, by rfl⟩ : syracuseStep 1125307 = 1687961) B1687961
theorem B2534345 : Blo 1124630 2534345 := bstep (se 2 (by rfl) ⟨950379, by rfl⟩ : syracuseStep 2534345 = 1900759) B1900759
theorem B1125383 : Blo 1124630 1125383 := bstep (se 1 (by rfl) ⟨844037, by rfl⟩ : syracuseStep 1125383 = 1688075) B1688075
theorem B1125391 : Blo 1124630 1125391 := bstep (se 1 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 1125391 = 1688087) B1688087
theorem B6171677 : Blo 1124630 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B2540842019 : Blo 1124630 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B1125435 : Blo 1124630 1125435 := bstep (se 1 (by rfl) ⟨844076, by rfl⟩ : syracuseStep 1125435 = 1688153) B1688153
theorem B2567227 : Blo 1124630 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B1125511 : Blo 1124630 1125511 := bstep (se 1 (by rfl) ⟨844133, by rfl⟩ : syracuseStep 1125511 = 1688267) B1688267
theorem B1125519 : Blo 1124630 1125519 := bstep (se 1 (by rfl) ⟨844139, by rfl⟩ : syracuseStep 1125519 = 1688279) B1688279
theorem B1125563 : Blo 1124630 1125563 := bstep (se 1 (by rfl) ⟨844172, by rfl⟩ : syracuseStep 1125563 = 1688345) B1688345
theorem B1125639 : Blo 1124630 1125639 := bstep (se 1 (by rfl) ⟨844229, by rfl⟩ : syracuseStep 1125639 = 1688459) B1688459
theorem B1125647 : Blo 1124630 1125647 := bstep (se 1 (by rfl) ⟨844235, by rfl⟩ : syracuseStep 1125647 = 1688471) B1688471
theorem B4271393 : Blo 1124630 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B1125691 : Blo 1124630 1125691 := bstep (se 1 (by rfl) ⟨844268, by rfl⟩ : syracuseStep 1125691 = 1688537) B1688537
theorem B1125767 : Blo 1124630 1125767 := bstep (se 1 (by rfl) ⟨844325, by rfl⟩ : syracuseStep 1125767 = 1688651) B1688651
theorem B1125775 : Blo 1124630 1125775 := bstep (se 1 (by rfl) ⟨844331, by rfl⟩ : syracuseStep 1125775 = 1688663) B1688663
theorem B9121169 : Blo 1124630 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B1125819 : Blo 1124630 1125819 := bstep (se 1 (by rfl) ⟨844364, by rfl⟩ : syracuseStep 1125819 = 1688729) B1688729
theorem B1125895 : Blo 1124630 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B1125903 : Blo 1124630 1125903 := bstep (se 1 (by rfl) ⟨844427, by rfl⟩ : syracuseStep 1125903 = 1688855) B1688855
theorem B2141711 : Blo 1124630 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B1125947 : Blo 1124630 1125947 := bstep (se 1 (by rfl) ⟨844460, by rfl⟩ : syracuseStep 1125947 = 1688921) B1688921
theorem B8564291 : Blo 1124630 8564291 := bstep (se 1 (by rfl) ⟨6423218, by rfl⟩ : syracuseStep 8564291 = 12846437) B12846437
theorem B1126023 : Blo 1124630 1126023 := bstep (se 1 (by rfl) ⟨844517, by rfl⟩ : syracuseStep 1126023 = 1689035) B1689035
theorem B2535047 : Blo 1124630 2535047 := bstep (se 1 (by rfl) ⟨1901285, by rfl⟩ : syracuseStep 2535047 = 3802571) B3802571
theorem B1126031 : Blo 1124630 1126031 := bstep (se 1 (by rfl) ⟨844523, by rfl⟩ : syracuseStep 1126031 = 1689047) B1689047
theorem B1126075 : Blo 1124630 1126075 := bstep (se 1 (by rfl) ⟨844556, by rfl⟩ : syracuseStep 1126075 = 1689113) B1689113
theorem B1126151 : Blo 1124630 1126151 := bstep (se 1 (by rfl) ⟨844613, by rfl⟩ : syracuseStep 1126151 = 1689227) B1689227
theorem B1126159 : Blo 1124630 1126159 := bstep (se 1 (by rfl) ⟨844619, by rfl⟩ : syracuseStep 1126159 = 1689239) B1689239
theorem B1126203 : Blo 1124630 1126203 := bstep (se 1 (by rfl) ⟨844652, by rfl⟩ : syracuseStep 1126203 = 1689305) B1689305
theorem B2535227 : Blo 1124630 2535227 := bstep (se 1 (by rfl) ⟨1901420, by rfl⟩ : syracuseStep 2535227 = 3802841) B3802841
theorem B1126279 : Blo 1124630 1126279 := bstep (se 1 (by rfl) ⟨844709, by rfl⟩ : syracuseStep 1126279 = 1689419) B1689419
theorem B1126287 : Blo 1124630 1126287 := bstep (se 1 (by rfl) ⟨844715, by rfl⟩ : syracuseStep 1126287 = 1689431) B1689431
theorem B1355663 : Blo 1124630 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B4632473 : Blo 1124630 4632473 := bstep (se 2 (by rfl) ⟨1737177, by rfl⟩ : syracuseStep 4632473 = 3474355) B3474355
theorem B2535353 : Blo 1124630 2535353 := bstep (se 2 (by rfl) ⟨950757, by rfl⟩ : syracuseStep 2535353 = 1901515) B1901515
theorem B1126331 : Blo 1124630 1126331 := bstep (se 1 (by rfl) ⟨844748, by rfl⟩ : syracuseStep 1126331 = 1689497) B1689497
theorem B1126407 : Blo 1124630 1126407 := bstep (se 1 (by rfl) ⟨844805, by rfl⟩ : syracuseStep 1126407 = 1689611) B1689611
theorem B1126415 : Blo 1124630 1126415 := bstep (se 1 (by rfl) ⟨844811, by rfl⟩ : syracuseStep 1126415 = 1689623) B1689623
theorem B1126459 : Blo 1124630 1126459 := bstep (se 1 (by rfl) ⟨844844, by rfl⟩ : syracuseStep 1126459 = 1689689) B1689689
theorem B4337725 : Blo 1124630 4337725 := bstep (se 3 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 4337725 = 1626647) B1626647
theorem B1126535 : Blo 1124630 1126535 := bstep (se 1 (by rfl) ⟨844901, by rfl⟩ : syracuseStep 1126535 = 1689803) B1689803
theorem B1126543 : Blo 1124630 1126543 := bstep (se 1 (by rfl) ⟨844907, by rfl⟩ : syracuseStep 1126543 = 1689815) B1689815
theorem B1126587 : Blo 1124630 1126587 := bstep (se 1 (by rfl) ⟨844940, by rfl⟩ : syracuseStep 1126587 = 1689881) B1689881
theorem B4272365 : Blo 1124630 4272365 := bstep (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) B1602137
theorem B1126663 : Blo 1124630 1126663 := bstep (se 1 (by rfl) ⟨844997, by rfl⟩ : syracuseStep 1126663 = 1689995) B1689995
theorem B1126671 : Blo 1124630 1126671 := bstep (se 1 (by rfl) ⟨845003, by rfl⟩ : syracuseStep 1126671 = 1690007) B1690007
theorem B2535695 : Blo 1124630 2535695 := bstep (se 1 (by rfl) ⟨1901771, by rfl⟩ : syracuseStep 2535695 = 3803543) B3803543
theorem B2535713 : Blo 1124630 2535713 := bstep (se 2 (by rfl) ⟨950892, by rfl⟩ : syracuseStep 2535713 = 1901785) B1901785
theorem B2404667 : Blo 1124630 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B1126715 : Blo 1124630 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B1126791 : Blo 1124630 1126791 := bstep (se 1 (by rfl) ⟨845093, by rfl⟩ : syracuseStep 1126791 = 1690187) B1690187
theorem B1126799 : Blo 1124630 1126799 := bstep (se 1 (by rfl) ⟨845099, by rfl⟩ : syracuseStep 1126799 = 1690199) B1690199
theorem B1126843 : Blo 1124630 1126843 := bstep (se 1 (by rfl) ⟨845132, by rfl⟩ : syracuseStep 1126843 = 1690265) B1690265
theorem B1126919 : Blo 1124630 1126919 := bstep (se 1 (by rfl) ⟨845189, by rfl⟩ : syracuseStep 1126919 = 1690379) B1690379
theorem B1126927 : Blo 1124630 1126927 := bstep (se 1 (by rfl) ⟨845195, by rfl⟩ : syracuseStep 1126927 = 1690391) B1690391
theorem B29241899 : Blo 1124630 29241899 := bstep (se 1 (by rfl) ⟨21931424, by rfl⟩ : syracuseStep 29241899 = 43862849) B43862849
theorem B1126971 : Blo 1124630 1126971 := bstep (se 1 (by rfl) ⟨845228, by rfl⟩ : syracuseStep 1126971 = 1690457) B1690457
theorem B2536055 : Blo 1124630 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B1127047 : Blo 1124630 1127047 := bstep (se 1 (by rfl) ⟨845285, by rfl⟩ : syracuseStep 1127047 = 1690571) B1690571
theorem B1127055 : Blo 1124630 1127055 := bstep (se 1 (by rfl) ⟨845291, by rfl⟩ : syracuseStep 1127055 = 1690583) B1690583
theorem B1127099 : Blo 1124630 1127099 := bstep (se 1 (by rfl) ⟨845324, by rfl⟩ : syracuseStep 1127099 = 1690649) B1690649
theorem B1127175 : Blo 1124630 1127175 := bstep (se 1 (by rfl) ⟨845381, by rfl⟩ : syracuseStep 1127175 = 1690763) B1690763
theorem B1127183 : Blo 1124630 1127183 := bstep (se 1 (by rfl) ⟨845387, by rfl⟩ : syracuseStep 1127183 = 1690775) B1690775
theorem B2536235 : Blo 1124630 2536235 := bstep (se 1 (by rfl) ⟨1902176, by rfl⟩ : syracuseStep 2536235 = 3804353) B3804353
theorem B1127227 : Blo 1124630 1127227 := bstep (se 1 (by rfl) ⟨845420, by rfl⟩ : syracuseStep 1127227 = 1690841) B1690841
theorem B1127303 : Blo 1124630 1127303 := bstep (se 1 (by rfl) ⟨845477, by rfl⟩ : syracuseStep 1127303 = 1690955) B1690955
theorem B1127311 : Blo 1124630 1127311 := bstep (se 1 (by rfl) ⟨845483, by rfl⟩ : syracuseStep 1127311 = 1690967) B1690967
theorem B1127355 : Blo 1124630 1127355 := bstep (se 1 (by rfl) ⟨845516, by rfl⟩ : syracuseStep 1127355 = 1691033) B1691033
theorem B5419979 : Blo 1124630 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B1127431 : Blo 1124630 1127431 := bstep (se 1 (by rfl) ⟨845573, by rfl⟩ : syracuseStep 1127431 = 1691147) B1691147
theorem B1127439 : Blo 1124630 1127439 := bstep (se 1 (by rfl) ⟨845579, by rfl⟩ : syracuseStep 1127439 = 1691159) B1691159
theorem B1127483 : Blo 1124630 1127483 := bstep (se 1 (by rfl) ⟨845612, by rfl⟩ : syracuseStep 1127483 = 1691225) B1691225
theorem B2405495 : Blo 1124630 2405495 := bstep (se 1 (by rfl) ⟨1804121, by rfl⟩ : syracuseStep 2405495 = 3608243) B3608243
theorem B1127559 : Blo 1124630 1127559 := bstep (se 1 (by rfl) ⟨845669, by rfl⟩ : syracuseStep 1127559 = 1691339) B1691339
theorem B1127567 : Blo 1124630 1127567 := bstep (se 1 (by rfl) ⟨845675, by rfl⟩ : syracuseStep 1127567 = 1691351) B1691351
theorem B2536595 : Blo 1124630 2536595 := bstep (se 1 (by rfl) ⟨1902446, by rfl⟩ : syracuseStep 2536595 = 3804893) B3804893
theorem B25801877 : Blo 1124630 25801877 := bstep (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) B1209463
theorem B1127611 : Blo 1124630 1127611 := bstep (se 1 (by rfl) ⟨845708, by rfl⟩ : syracuseStep 1127611 = 1691417) B1691417
theorem B2536649 : Blo 1124630 2536649 := bstep (se 2 (by rfl) ⟨951243, by rfl⟩ : syracuseStep 2536649 = 1902487) B1902487
theorem B1520887 : Blo 1124630 1520887 := bstep (se 1 (by rfl) ⟨1140665, by rfl⟩ : syracuseStep 1520887 = 2281331) B2281331
theorem B1127687 : Blo 1124630 1127687 := bstep (se 1 (by rfl) ⟨845765, by rfl⟩ : syracuseStep 1127687 = 1691531) B1691531
theorem B1127695 : Blo 1124630 1127695 := bstep (se 1 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 1127695 = 1691543) B1691543
theorem B1127739 : Blo 1124630 1127739 := bstep (se 1 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 1127739 = 1691609) B1691609
theorem B1127815 : Blo 1124630 1127815 := bstep (se 1 (by rfl) ⟨845861, by rfl⟩ : syracuseStep 1127815 = 1691723) B1691723
theorem B1127823 : Blo 1124630 1127823 := bstep (se 1 (by rfl) ⟨845867, by rfl⟩ : syracuseStep 1127823 = 1691735) B1691735
theorem B1127867 : Blo 1124630 1127867 := bstep (se 1 (by rfl) ⟨845900, by rfl⟩ : syracuseStep 1127867 = 1691801) B1691801
theorem B1127943 : Blo 1124630 1127943 := bstep (se 1 (by rfl) ⟨845957, by rfl⟩ : syracuseStep 1127943 = 1691915) B1691915
theorem B1127951 : Blo 1124630 1127951 := bstep (se 1 (by rfl) ⟨845963, by rfl⟩ : syracuseStep 1127951 = 1691927) B1691927
theorem B1127995 : Blo 1124630 1127995 := bstep (se 1 (by rfl) ⟨845996, by rfl⟩ : syracuseStep 1127995 = 1691993) B1691993
theorem B1128071 : Blo 1124630 1128071 := bstep (se 1 (by rfl) ⟨846053, by rfl⟩ : syracuseStep 1128071 = 1692107) B1692107
theorem B1128079 : Blo 1124630 1128079 := bstep (se 1 (by rfl) ⟨846059, by rfl⟩ : syracuseStep 1128079 = 1692119) B1692119
theorem B1128123 : Blo 1124630 1128123 := bstep (se 1 (by rfl) ⟨846092, by rfl⟩ : syracuseStep 1128123 = 1692185) B1692185
theorem B1128199 : Blo 1124630 1128199 := bstep (se 1 (by rfl) ⟨846149, by rfl⟩ : syracuseStep 1128199 = 1692299) B1692299
theorem B1128207 : Blo 1124630 1128207 := bstep (se 1 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 1128207 = 1692311) B1692311
theorem B1128251 : Blo 1124630 1128251 := bstep (se 1 (by rfl) ⟨846188, by rfl⟩ : syracuseStep 1128251 = 1692377) B1692377
theorem B2537351 : Blo 1124630 2537351 := bstep (se 1 (by rfl) ⟨1903013, by rfl⟩ : syracuseStep 2537351 = 3806027) B3806027
theorem B1128327 : Blo 1124630 1128327 := bstep (se 1 (by rfl) ⟨846245, by rfl⟩ : syracuseStep 1128327 = 1692491) B1692491
theorem B1128335 : Blo 1124630 1128335 := bstep (se 1 (by rfl) ⟨846251, by rfl⟩ : syracuseStep 1128335 = 1692503) B1692503
theorem B1128379 : Blo 1124630 1128379 := bstep (se 1 (by rfl) ⟨846284, by rfl⟩ : syracuseStep 1128379 = 1692569) B1692569
theorem B6862795 : Blo 1124630 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B1128455 : Blo 1124630 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B1128463 : Blo 1124630 1128463 := bstep (se 1 (by rfl) ⟨846347, by rfl⟩ : syracuseStep 1128463 = 1692695) B1692695
theorem B2537531 : Blo 1124630 2537531 := bstep (se 1 (by rfl) ⟨1903148, by rfl⟩ : syracuseStep 2537531 = 3806297) B3806297
theorem B1128507 : Blo 1124630 1128507 := bstep (se 1 (by rfl) ⟨846380, by rfl⟩ : syracuseStep 1128507 = 1692761) B1692761
theorem B1128583 : Blo 1124630 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B1128591 : Blo 1124630 1128591 := bstep (se 1 (by rfl) ⟨846443, by rfl⟩ : syracuseStep 1128591 = 1692887) B1692887
theorem B2537657 : Blo 1124630 2537657 := bstep (se 2 (by rfl) ⟨951621, by rfl⟩ : syracuseStep 2537657 = 1903243) B1903243
theorem B3422507 : Blo 1124630 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B4274491 : Blo 1124630 4274491 := bstep (se 1 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 4274491 = 6411737) B6411737
theorem B3422579 : Blo 1124630 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B2537999 : Blo 1124630 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B2538017 : Blo 1124630 2538017 := bstep (se 2 (by rfl) ⟨951756, by rfl⟩ : syracuseStep 2538017 = 1903513) B1903513
theorem B1522423 : Blo 1124630 1522423 := bstep (se 1 (by rfl) ⟨1141817, by rfl⟩ : syracuseStep 1522423 = 2283635) B2283635
theorem B9124609 : Blo 1124630 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B4274977 : Blo 1124630 4274977 := bstep (se 2 (by rfl) ⟨1603116, by rfl⟩ : syracuseStep 4274977 = 3206233) B3206233
theorem B2538359 : Blo 1124630 2538359 := bstep (se 1 (by rfl) ⟨1903769, by rfl⟩ : syracuseStep 2538359 = 3807539) B3807539
theorem B5421977 : Blo 1124630 5421977 := bstep (se 2 (by rfl) ⟨2033241, by rfl⟩ : syracuseStep 5421977 = 4066483) B4066483
theorem B9878435 : Blo 1124630 9878435 := bstep (se 1 (by rfl) ⟨7408826, by rfl⟩ : syracuseStep 9878435 = 14817653) B14817653
theorem B1424299 : Blo 1124630 1424299 := bstep (se 1 (by rfl) ⟨1068224, by rfl⟩ : syracuseStep 1424299 = 2136449) B2136449
theorem B2538539 : Blo 1124630 2538539 := bstep (se 1 (by rfl) ⟨1903904, by rfl⟩ : syracuseStep 2538539 = 3807809) B3807809
theorem B2538899 : Blo 1124630 2538899 := bstep (se 1 (by rfl) ⟨1904174, by rfl⟩ : syracuseStep 2538899 = 3808349) B3808349
theorem B1686971 : Blo 1124630 1686971 := bstep (se 1 (by rfl) ⟨1265228, by rfl⟩ : syracuseStep 1686971 = 2530457) B2530457
theorem B2538953 : Blo 1124630 2538953 := bstep (se 2 (by rfl) ⟨952107, by rfl⟩ : syracuseStep 2538953 = 1904215) B1904215
theorem B11124173 : Blo 1124630 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1687031 : Blo 1124630 1687031 := bstep (se 1 (by rfl) ⟨1265273, by rfl⟩ : syracuseStep 1687031 = 2530547) B2530547
theorem B1687055 : Blo 1124630 1687055 := bstep (se 1 (by rfl) ⟨1265291, by rfl⟩ : syracuseStep 1687055 = 2530583) B2530583
theorem B1687097 : Blo 1124630 1687097 := bstep (se 2 (by rfl) ⟨632661, by rfl⟩ : syracuseStep 1687097 = 1265323) B1265323
theorem B1687175 : Blo 1124630 1687175 := bstep (se 1 (by rfl) ⟨1265381, by rfl⟩ : syracuseStep 1687175 = 2530763) B2530763
theorem B1687211 : Blo 1124630 1687211 := bstep (se 1 (by rfl) ⟨1265408, by rfl⟩ : syracuseStep 1687211 = 2530817) B2530817
theorem B1687241 : Blo 1124630 1687241 := bstep (se 2 (by rfl) ⟨632715, by rfl⟩ : syracuseStep 1687241 = 1265431) B1265431
theorem B4275949 : Blo 1124630 4275949 := bstep (se 3 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 4275949 = 1603481) B1603481
theorem B1687355 : Blo 1124630 1687355 := bstep (se 1 (by rfl) ⟨1265516, by rfl⟩ : syracuseStep 1687355 = 2531033) B2531033
theorem B8568665 : Blo 1124630 8568665 := bstep (se 2 (by rfl) ⟨3213249, by rfl⟩ : syracuseStep 8568665 = 6426499) B6426499
theorem B1687415 : Blo 1124630 1687415 := bstep (se 1 (by rfl) ⟨1265561, by rfl⟩ : syracuseStep 1687415 = 2531123) B2531123
theorem B2703223 : Blo 1124630 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B1425271 : Blo 1124630 1425271 := bstep (se 1 (by rfl) ⟨1068953, by rfl⟩ : syracuseStep 1425271 = 2137907) B2137907
theorem B1687439 : Blo 1124630 1687439 := bstep (se 1 (by rfl) ⟨1265579, by rfl⟩ : syracuseStep 1687439 = 2531159) B2531159
theorem B1687481 : Blo 1124630 1687481 := bstep (se 2 (by rfl) ⟨632805, by rfl⟩ : syracuseStep 1687481 = 1265611) B1265611
theorem B1687559 : Blo 1124630 1687559 := bstep (se 1 (by rfl) ⟨1265669, by rfl⟩ : syracuseStep 1687559 = 2531339) B2531339
theorem B16269335 : Blo 1124630 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B4276253 : Blo 1124630 4276253 := bstep (se 3 (by rfl) ⟨801797, by rfl⟩ : syracuseStep 4276253 = 1603595) B1603595
theorem B1687595 : Blo 1124630 1687595 := bstep (se 1 (by rfl) ⟨1265696, by rfl⟩ : syracuseStep 1687595 = 2531393) B2531393
theorem B1687625 : Blo 1124630 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B1687739 : Blo 1124630 1687739 := bstep (se 1 (by rfl) ⟨1265804, by rfl⟩ : syracuseStep 1687739 = 2531609) B2531609
theorem B1425595 : Blo 1124630 1425595 := bstep (se 1 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 1425595 = 2138393) B2138393
theorem B1687799 : Blo 1124630 1687799 := bstep (se 1 (by rfl) ⟨1265849, by rfl⟩ : syracuseStep 1687799 = 2531699) B2531699
theorem B1687823 : Blo 1124630 1687823 := bstep (se 1 (by rfl) ⟨1265867, by rfl⟩ : syracuseStep 1687823 = 2531735) B2531735
theorem B1687865 : Blo 1124630 1687865 := bstep (se 2 (by rfl) ⟨632949, by rfl⟩ : syracuseStep 1687865 = 1265899) B1265899
theorem B1687943 : Blo 1124630 1687943 := bstep (se 1 (by rfl) ⟨1265957, by rfl⟩ : syracuseStep 1687943 = 2531915) B2531915
theorem B1687979 : Blo 1124630 1687979 := bstep (se 1 (by rfl) ⟨1265984, by rfl⟩ : syracuseStep 1687979 = 2531969) B2531969
theorem B1688009 : Blo 1124630 1688009 := bstep (se 2 (by rfl) ⟨633003, by rfl⟩ : syracuseStep 1688009 = 1266007) B1266007
theorem B1688123 : Blo 1124630 1688123 := bstep (se 1 (by rfl) ⟨1266092, by rfl⟩ : syracuseStep 1688123 = 2532185) B2532185
theorem B1688183 : Blo 1124630 1688183 := bstep (se 1 (by rfl) ⟨1266137, by rfl⟩ : syracuseStep 1688183 = 2532275) B2532275
theorem B1688207 : Blo 1124630 1688207 := bstep (se 1 (by rfl) ⟨1266155, by rfl⟩ : syracuseStep 1688207 = 2532311) B2532311
theorem B1688249 : Blo 1124630 1688249 := bstep (se 2 (by rfl) ⟨633093, by rfl⟩ : syracuseStep 1688249 = 1266187) B1266187
theorem B9126593 : Blo 1124630 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1688327 : Blo 1124630 1688327 := bstep (se 1 (by rfl) ⟨1266245, by rfl⟩ : syracuseStep 1688327 = 2532491) B2532491
theorem B8569637 : Blo 1124630 8569637 := bstep (se 4 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 8569637 = 1606807) B1606807
theorem B1688363 : Blo 1124630 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B1688393 : Blo 1124630 1688393 := bstep (se 2 (by rfl) ⟨633147, by rfl⟩ : syracuseStep 1688393 = 1266295) B1266295
theorem B3425111 : Blo 1124630 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B1688507 : Blo 1124630 1688507 := bstep (se 1 (by rfl) ⟨1266380, by rfl⟩ : syracuseStep 1688507 = 2532761) B2532761
theorem B1688567 : Blo 1124630 1688567 := bstep (se 1 (by rfl) ⟨1266425, by rfl⟩ : syracuseStep 1688567 = 2532851) B2532851
theorem B1688591 : Blo 1124630 1688591 := bstep (se 1 (by rfl) ⟨1266443, by rfl⟩ : syracuseStep 1688591 = 2532887) B2532887
theorem B1524779 : Blo 1124630 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B1688633 : Blo 1124630 1688633 := bstep (se 2 (by rfl) ⟨633237, by rfl⟩ : syracuseStep 1688633 = 1266475) B1266475
theorem B6505591 : Blo 1124630 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B1688711 : Blo 1124630 1688711 := bstep (se 1 (by rfl) ⟨1266533, by rfl⟩ : syracuseStep 1688711 = 2533067) B2533067
theorem B1426567 : Blo 1124630 1426567 := bstep (se 1 (by rfl) ⟨1069925, by rfl⟩ : syracuseStep 1426567 = 2139851) B2139851
theorem B1688747 : Blo 1124630 1688747 := bstep (se 1 (by rfl) ⟨1266560, by rfl⟩ : syracuseStep 1688747 = 2533121) B2533121
theorem B1688777 : Blo 1124630 1688777 := bstep (se 2 (by rfl) ⟨633291, by rfl⟩ : syracuseStep 1688777 = 1266583) B1266583
theorem B1688891 : Blo 1124630 1688891 := bstep (se 1 (by rfl) ⟨1266668, by rfl⟩ : syracuseStep 1688891 = 2533337) B2533337
theorem B1688951 : Blo 1124630 1688951 := bstep (se 1 (by rfl) ⟨1266713, by rfl⟩ : syracuseStep 1688951 = 2533427) B2533427
theorem B1688975 : Blo 1124630 1688975 := bstep (se 1 (by rfl) ⟨1266731, by rfl⟩ : syracuseStep 1688975 = 2533463) B2533463
theorem B1689017 : Blo 1124630 1689017 := bstep (se 2 (by rfl) ⟨633381, by rfl⟩ : syracuseStep 1689017 = 1266763) B1266763
theorem B1689095 : Blo 1124630 1689095 := bstep (se 1 (by rfl) ⟨1266821, by rfl⟩ : syracuseStep 1689095 = 2533643) B2533643
theorem B2442767 : Blo 1124630 2442767 := bstep (se 1 (by rfl) ⟨1832075, by rfl⟩ : syracuseStep 2442767 = 3664151) B3664151
theorem B1689131 : Blo 1124630 1689131 := bstep (se 1 (by rfl) ⟨1266848, by rfl⟩ : syracuseStep 1689131 = 2533697) B2533697
theorem B1426987 : Blo 1124630 1426987 := bstep (se 1 (by rfl) ⟨1070240, by rfl⟩ : syracuseStep 1426987 = 2140481) B2140481
theorem B1689161 : Blo 1124630 1689161 := bstep (se 2 (by rfl) ⟨633435, by rfl⟩ : syracuseStep 1689161 = 1266871) B1266871
theorem B4277879 : Blo 1124630 4277879 := bstep (se 1 (by rfl) ⟨3208409, by rfl⟩ : syracuseStep 4277879 = 6416819) B6416819
theorem B54904499 : Blo 1124630 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B1689275 : Blo 1124630 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B1689335 : Blo 1124630 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B1689359 : Blo 1124630 1689359 := bstep (se 1 (by rfl) ⟨1267019, by rfl⟩ : syracuseStep 1689359 = 2534039) B2534039
theorem B1427215 : Blo 1124630 1427215 := bstep (se 1 (by rfl) ⟨1070411, by rfl⟩ : syracuseStep 1427215 = 2140823) B2140823
theorem B1689401 : Blo 1124630 1689401 := bstep (se 2 (by rfl) ⟨633525, by rfl⟩ : syracuseStep 1689401 = 1267051) B1267051
theorem B7227251 : Blo 1124630 7227251 := bstep (se 1 (by rfl) ⟨5420438, by rfl⟩ : syracuseStep 7227251 = 10840877) B10840877
theorem B6408071 : Blo 1124630 6408071 := bstep (se 1 (by rfl) ⟨4806053, by rfl⟩ : syracuseStep 6408071 = 9612107) B9612107
theorem B1689479 : Blo 1124630 1689479 := bstep (se 1 (by rfl) ⟨1267109, by rfl⟩ : syracuseStep 1689479 = 2534219) B2534219
theorem B1689515 : Blo 1124630 1689515 := bstep (se 1 (by rfl) ⟨1267136, by rfl⟩ : syracuseStep 1689515 = 2534273) B2534273
theorem B1689545 : Blo 1124630 1689545 := bstep (se 2 (by rfl) ⟨633579, by rfl⟩ : syracuseStep 1689545 = 1267159) B1267159
theorem B11552813 : Blo 1124630 11552813 := bstep (se 3 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 11552813 = 4332305) B4332305
theorem B1689659 : Blo 1124630 1689659 := bstep (se 1 (by rfl) ⟨1267244, by rfl⟩ : syracuseStep 1689659 = 2534489) B2534489
theorem B9521239 : Blo 1124630 9521239 := bstep (se 1 (by rfl) ⟨7140929, by rfl⟩ : syracuseStep 9521239 = 14281859) B14281859
theorem B1689719 : Blo 1124630 1689719 := bstep (se 1 (by rfl) ⟨1267289, by rfl⟩ : syracuseStep 1689719 = 2534579) B2534579
theorem B1689743 : Blo 1124630 1689743 := bstep (se 1 (by rfl) ⟨1267307, by rfl⟩ : syracuseStep 1689743 = 2534615) B2534615
theorem B1689785 : Blo 1124630 1689785 := bstep (se 2 (by rfl) ⟨633669, by rfl⟩ : syracuseStep 1689785 = 1267339) B1267339
theorem B7817417 : Blo 1124630 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B5130497 : Blo 1124630 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B1689863 : Blo 1124630 1689863 := bstep (se 1 (by rfl) ⟨1267397, by rfl⟩ : syracuseStep 1689863 = 2534795) B2534795
theorem B1689899 : Blo 1124630 1689899 := bstep (se 1 (by rfl) ⟨1267424, by rfl⟩ : syracuseStep 1689899 = 2534849) B2534849
theorem B1689929 : Blo 1124630 1689929 := bstep (se 2 (by rfl) ⟨633723, by rfl⟩ : syracuseStep 1689929 = 1267447) B1267447
theorem B1690043 : Blo 1124630 1690043 := bstep (se 1 (by rfl) ⟨1267532, by rfl⟩ : syracuseStep 1690043 = 2535065) B2535065
theorem B7719389 : Blo 1124630 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B1690103 : Blo 1124630 1690103 := bstep (se 1 (by rfl) ⟨1267577, by rfl⟩ : syracuseStep 1690103 = 2535155) B2535155
theorem B1427959 : Blo 1124630 1427959 := bstep (se 1 (by rfl) ⟨1070969, by rfl⟩ : syracuseStep 1427959 = 2141939) B2141939
theorem B1690127 : Blo 1124630 1690127 := bstep (se 1 (by rfl) ⟨1267595, by rfl⟩ : syracuseStep 1690127 = 2535191) B2535191
theorem B1690169 : Blo 1124630 1690169 := bstep (se 2 (by rfl) ⟨633813, by rfl⟩ : syracuseStep 1690169 = 1267627) B1267627
theorem B4278851 : Blo 1124630 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B1690247 : Blo 1124630 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B1690283 : Blo 1124630 1690283 := bstep (se 1 (by rfl) ⟨1267712, by rfl⟩ : syracuseStep 1690283 = 2535425) B2535425
theorem B1690313 : Blo 1124630 1690313 := bstep (se 2 (by rfl) ⟨633867, by rfl⟩ : syracuseStep 1690313 = 1267735) B1267735
theorem B1690427 : Blo 1124630 1690427 := bstep (se 1 (by rfl) ⟨1267820, by rfl⟩ : syracuseStep 1690427 = 2535641) B2535641
theorem B1428283 : Blo 1124630 1428283 := bstep (se 1 (by rfl) ⟨1071212, by rfl⟩ : syracuseStep 1428283 = 2142425) B2142425
theorem B1690487 : Blo 1124630 1690487 := bstep (se 1 (by rfl) ⟨1267865, by rfl⟩ : syracuseStep 1690487 = 2535731) B2535731
theorem B1690511 : Blo 1124630 1690511 := bstep (se 1 (by rfl) ⟨1267883, by rfl⟩ : syracuseStep 1690511 = 2535767) B2535767
theorem B1690553 : Blo 1124630 1690553 := bstep (se 2 (by rfl) ⟨633957, by rfl⟩ : syracuseStep 1690553 = 1267915) B1267915
theorem B1690631 : Blo 1124630 1690631 := bstep (se 1 (by rfl) ⟨1267973, by rfl⟩ : syracuseStep 1690631 = 2535947) B2535947
theorem B1690667 : Blo 1124630 1690667 := bstep (se 1 (by rfl) ⟨1268000, by rfl⟩ : syracuseStep 1690667 = 2536001) B2536001
theorem B6409277 : Blo 1124630 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B1690697 : Blo 1124630 1690697 := bstep (se 2 (by rfl) ⟨634011, by rfl⟩ : syracuseStep 1690697 = 1268023) B1268023
theorem B1690811 : Blo 1124630 1690811 := bstep (se 1 (by rfl) ⟨1268108, by rfl⟩ : syracuseStep 1690811 = 2536217) B2536217
theorem B1690871 : Blo 1124630 1690871 := bstep (se 1 (by rfl) ⟨1268153, by rfl⟩ : syracuseStep 1690871 = 2536307) B2536307
theorem B1690895 : Blo 1124630 1690895 := bstep (se 1 (by rfl) ⟨1268171, by rfl⟩ : syracuseStep 1690895 = 2536343) B2536343
theorem B1690937 : Blo 1124630 1690937 := bstep (se 2 (by rfl) ⟨634101, by rfl⟩ : syracuseStep 1690937 = 1268203) B1268203
theorem B1691015 : Blo 1124630 1691015 := bstep (se 1 (by rfl) ⟨1268261, by rfl⟩ : syracuseStep 1691015 = 2536523) B2536523
theorem B1691051 : Blo 1124630 1691051 := bstep (se 1 (by rfl) ⟨1268288, by rfl⟩ : syracuseStep 1691051 = 2536577) B2536577
theorem B1691081 : Blo 1124630 1691081 := bstep (se 2 (by rfl) ⟨634155, by rfl⟩ : syracuseStep 1691081 = 1268311) B1268311
theorem B4279837 : Blo 1124630 4279837 := bstep (se 3 (by rfl) ⟨802469, by rfl⟩ : syracuseStep 4279837 = 1604939) B1604939
theorem B1691195 : Blo 1124630 1691195 := bstep (se 1 (by rfl) ⟨1268396, by rfl⟩ : syracuseStep 1691195 = 2536793) B2536793
theorem B21646925 : Blo 1124630 21646925 := bstep (se 3 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 21646925 = 8117597) B8117597
theorem B1691255 : Blo 1124630 1691255 := bstep (se 1 (by rfl) ⟨1268441, by rfl⟩ : syracuseStep 1691255 = 2536883) B2536883
theorem B1265287 : Blo 1124630 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B1691279 : Blo 1124630 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B1691321 : Blo 1124630 1691321 := bstep (se 2 (by rfl) ⟨634245, by rfl⟩ : syracuseStep 1691321 = 1268491) B1268491
theorem B2707145 : Blo 1124630 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B1691399 : Blo 1124630 1691399 := bstep (se 1 (by rfl) ⟨1268549, by rfl⟩ : syracuseStep 1691399 = 2537099) B2537099
theorem B1691435 : Blo 1124630 1691435 := bstep (se 1 (by rfl) ⟨1268576, by rfl⟩ : syracuseStep 1691435 = 2537153) B2537153
theorem B1265467 : Blo 1124630 1265467 := bstep (se 1 (by rfl) ⟨949100, by rfl⟩ : syracuseStep 1265467 = 1898201) B1898201
theorem B1691465 : Blo 1124630 1691465 := bstep (se 2 (by rfl) ⟨634299, by rfl⟩ : syracuseStep 1691465 = 1268599) B1268599
theorem B1691579 : Blo 1124630 1691579 := bstep (se 1 (by rfl) ⟨1268684, by rfl⟩ : syracuseStep 1691579 = 2537369) B2537369
theorem B1691639 : Blo 1124630 1691639 := bstep (se 1 (by rfl) ⟨1268729, by rfl⟩ : syracuseStep 1691639 = 2537459) B2537459
theorem B1691663 : Blo 1124630 1691663 := bstep (se 1 (by rfl) ⟨1268747, by rfl⟩ : syracuseStep 1691663 = 2537495) B2537495
theorem B2707489 : Blo 1124630 2707489 := bstep (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) B2030617
theorem B1691705 : Blo 1124630 1691705 := bstep (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) B1268779
theorem B1691783 : Blo 1124630 1691783 := bstep (se 1 (by rfl) ⟨1268837, by rfl⟩ : syracuseStep 1691783 = 2537675) B2537675
theorem B1691819 : Blo 1124630 1691819 := bstep (se 1 (by rfl) ⟨1268864, by rfl⟩ : syracuseStep 1691819 = 2537729) B2537729
theorem B1691849 : Blo 1124630 1691849 := bstep (se 2 (by rfl) ⟨634443, by rfl⟩ : syracuseStep 1691849 = 1268887) B1268887
theorem B1265935 : Blo 1124630 1265935 := bstep (se 1 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 1265935 = 1898903) B1898903
theorem B1691963 : Blo 1124630 1691963 := bstep (se 1 (by rfl) ⟨1268972, by rfl⟩ : syracuseStep 1691963 = 2537945) B2537945
theorem B1692023 : Blo 1124630 1692023 := bstep (se 1 (by rfl) ⟨1269017, by rfl⟩ : syracuseStep 1692023 = 2538035) B2538035
theorem B1692047 : Blo 1124630 1692047 := bstep (se 1 (by rfl) ⟨1269035, by rfl⟩ : syracuseStep 1692047 = 2538071) B2538071
theorem B1692089 : Blo 1124630 1692089 := bstep (se 2 (by rfl) ⟨634533, by rfl⟩ : syracuseStep 1692089 = 1269067) B1269067
theorem B2707913 : Blo 1124630 2707913 := bstep (se 2 (by rfl) ⟨1015467, by rfl⟩ : syracuseStep 2707913 = 2030935) B2030935
theorem B1692167 : Blo 1124630 1692167 := bstep (se 1 (by rfl) ⟨1269125, by rfl⟩ : syracuseStep 1692167 = 2538251) B2538251
theorem B1692203 : Blo 1124630 1692203 := bstep (se 1 (by rfl) ⟨1269152, by rfl⟩ : syracuseStep 1692203 = 2538305) B2538305
theorem B1692233 : Blo 1124630 1692233 := bstep (se 2 (by rfl) ⟨634587, by rfl⟩ : syracuseStep 1692233 = 1269175) B1269175
theorem B1692347 : Blo 1124630 1692347 := bstep (se 1 (by rfl) ⟨1269260, by rfl⟩ : syracuseStep 1692347 = 2538521) B2538521
theorem B1692407 : Blo 1124630 1692407 := bstep (se 1 (by rfl) ⟨1269305, by rfl⟩ : syracuseStep 1692407 = 2538611) B2538611
theorem B1266439 : Blo 1124630 1266439 := bstep (se 1 (by rfl) ⟨949829, by rfl⟩ : syracuseStep 1266439 = 1899659) B1899659
theorem B1692431 : Blo 1124630 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B48648995 : Blo 1124630 48648995 := bstep (se 1 (by rfl) ⟨36486746, by rfl⟩ : syracuseStep 48648995 = 72973493) B72973493
theorem B1692473 : Blo 1124630 1692473 := bstep (se 2 (by rfl) ⟨634677, by rfl⟩ : syracuseStep 1692473 = 1269355) B1269355
theorem B1692551 : Blo 1124630 1692551 := bstep (se 1 (by rfl) ⟨1269413, by rfl⟩ : syracuseStep 1692551 = 2538827) B2538827
theorem B1692587 : Blo 1124630 1692587 := bstep (se 1 (by rfl) ⟨1269440, by rfl⟩ : syracuseStep 1692587 = 2538881) B2538881
theorem B1266619 : Blo 1124630 1266619 := bstep (se 1 (by rfl) ⟨949964, by rfl⟩ : syracuseStep 1266619 = 1899929) B1899929
theorem B1692617 : Blo 1124630 1692617 := bstep (se 2 (by rfl) ⟨634731, by rfl⟩ : syracuseStep 1692617 = 1269463) B1269463
theorem B1201159 : Blo 1124630 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B1692731 : Blo 1124630 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B1692791 : Blo 1124630 1692791 := bstep (se 1 (by rfl) ⟨1269593, by rfl⟩ : syracuseStep 1692791 = 2539187) B2539187
theorem B1692815 : Blo 1124630 1692815 := bstep (se 1 (by rfl) ⟨1269611, by rfl⟩ : syracuseStep 1692815 = 2539223) B2539223
theorem B1692857 : Blo 1124630 1692857 := bstep (se 2 (by rfl) ⟨634821, by rfl⟩ : syracuseStep 1692857 = 1269643) B1269643
theorem B1692935 : Blo 1124630 1692935 := bstep (se 1 (by rfl) ⟨1269701, by rfl⟩ : syracuseStep 1692935 = 2539403) B2539403
theorem B1267087 : Blo 1124630 1267087 := bstep (se 1 (by rfl) ⟨950315, by rfl⟩ : syracuseStep 1267087 = 1900631) B1900631
theorem B7230941 : Blo 1124630 7230941 := bstep (se 3 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 7230941 = 2711603) B2711603
theorem B7820803 : Blo 1124630 7820803 := bstep (se 1 (by rfl) ⟨5865602, by rfl⟩ : syracuseStep 7820803 = 11731205) B11731205
theorem B1201979 : Blo 1124630 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B2709335 : Blo 1124630 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B10835801 : Blo 1124630 10835801 := bstep (se 2 (by rfl) ⟨4063425, by rfl⟩ : syracuseStep 10835801 = 8126851) B8126851
theorem B27383669 : Blo 1124630 27383669 := bstep (se 5 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 27383669 = 2567219) B2567219
theorem B1267591 : Blo 1124630 1267591 := bstep (se 1 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 1267591 = 1901387) B1901387
theorem B1267771 : Blo 1124630 1267771 := bstep (se 1 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 1267771 = 1901657) B1901657
theorem B4282739 : Blo 1124630 4282739 := bstep (se 1 (by rfl) ⟨3212054, by rfl⟩ : syracuseStep 4282739 = 6424109) B6424109
theorem B6936977 : Blo 1124630 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B16243091 : Blo 1124630 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B2710027 : Blo 1124630 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B1268239 : Blo 1124630 1268239 := bstep (se 1 (by rfl) ⟨951179, by rfl⟩ : syracuseStep 1268239 = 1902359) B1902359
theorem B2710103 : Blo 1124630 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B17324837 : Blo 1124630 17324837 := bstep (se 4 (by rfl) ⟨1624203, by rfl⟩ : syracuseStep 17324837 = 3248407) B3248407
theorem B13687703 : Blo 1124630 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B1268743 : Blo 1124630 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B1268923 : Blo 1124630 1268923 := bstep (se 1 (by rfl) ⟨951692, by rfl⟩ : syracuseStep 1268923 = 1903385) B1903385
theorem B12836231 : Blo 1124630 12836231 := bstep (se 1 (by rfl) ⟨9627173, by rfl⟩ : syracuseStep 12836231 = 19254347) B19254347
theorem B4873619 : Blo 1124630 4873619 := bstep (se 1 (by rfl) ⟨3655214, by rfl⟩ : syracuseStep 4873619 = 7310429) B7310429
theorem B3202679 : Blo 1124630 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1269391 : Blo 1124630 1269391 := bstep (se 1 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 1269391 = 1904087) B1904087
theorem B4808393 : Blo 1124630 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B23125733 : Blo 1124630 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B4808429 : Blo 1124630 4808429 := bstep (se 3 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 4808429 = 1803161) B1803161
theorem B2711411 : Blo 1124630 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B4809145 : Blo 1124630 4809145 := bstep (se 2 (by rfl) ⟨1803429, by rfl⟩ : syracuseStep 4809145 = 3606859) B3606859
theorem B12345821 : Blo 1124630 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B5693975 : Blo 1124630 5693975 := bstep (se 1 (by rfl) ⟨4270481, by rfl⟩ : syracuseStep 5693975 = 8540963) B8540963
theorem B4284971 : Blo 1124630 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B3203671 : Blo 1124630 3203671 := bstep (se 1 (by rfl) ⟨2402753, by rfl⟩ : syracuseStep 3203671 = 4805507) B4805507
theorem B27780245 : Blo 1124630 27780245 := bstep (se 6 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 27780245 = 1302199) B1302199
theorem B54912289 : Blo 1124630 54912289 := bstep (se 2 (by rfl) ⟨20592108, by rfl⟩ : syracuseStep 54912289 = 41184217) B41184217
theorem B28894643 : Blo 1124630 28894643 := bstep (se 1 (by rfl) ⟨21670982, by rfl⟩ : syracuseStep 28894643 = 43341965) B43341965
theorem B2746145 : Blo 1124630 2746145 := bstep (se 2 (by rfl) ⟨1029804, by rfl⟩ : syracuseStep 2746145 = 2059609) B2059609
theorem B3205163 : Blo 1124630 3205163 := bstep (se 1 (by rfl) ⟨2403872, by rfl⟩ : syracuseStep 3205163 = 4807745) B4807745
theorem B2058529 : Blo 1124630 2058529 := bstep (se 2 (by rfl) ⟨771948, by rfl⟩ : syracuseStep 2058529 = 1543897) B1543897
theorem B3795713 : Blo 1124630 3795713 := bstep (se 2 (by rfl) ⟨1423392, by rfl⟩ : syracuseStep 3795713 = 2846785) B2846785
theorem B4811521 : Blo 1124630 4811521 := bstep (se 2 (by rfl) ⟨1804320, by rfl⟩ : syracuseStep 4811521 = 3608641) B3608641
theorem B10546237 : Blo 1124630 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B3206279 : Blo 1124630 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B2059465 : Blo 1124630 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B3206461 : Blo 1124630 3206461 := bstep (se 3 (by rfl) ⟨601211, by rfl⟩ : syracuseStep 3206461 = 1202423) B1202423
theorem B1371563 : Blo 1124630 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B5697053 : Blo 1124630 5697053 := bstep (se 3 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 5697053 = 2136395) B2136395
theorem B15429149 : Blo 1124630 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B3796523 : Blo 1124630 3796523 := bstep (se 1 (by rfl) ⟨2847392, by rfl⟩ : syracuseStep 3796523 = 5694785) B5694785
theorem B3206803 : Blo 1124630 3206803 := bstep (se 1 (by rfl) ⟨2405102, by rfl⟩ : syracuseStep 3206803 = 4810205) B4810205
theorem B2027209 : Blo 1124630 2027209 := bstep (se 2 (by rfl) ⟨760203, by rfl⟩ : syracuseStep 2027209 = 1520407) B1520407
theorem B10809125 : Blo 1124630 10809125 := bstep (se 4 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 10809125 = 2026711) B2026711
theorem B4878139 : Blo 1124630 4878139 := bstep (se 1 (by rfl) ⟨3658604, by rfl⟩ : syracuseStep 4878139 = 7317209) B7317209
theorem B9629603 : Blo 1124630 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B5697539 : Blo 1124630 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B2846735 : Blo 1124630 2846735 := bstep (se 1 (by rfl) ⟨2135051, by rfl⟩ : syracuseStep 2846735 = 4270103) B4270103
theorem B1601579 : Blo 1124630 1601579 := bstep (se 1 (by rfl) ⟨1201184, by rfl⟩ : syracuseStep 1601579 = 2402369) B2402369
theorem B11137297 : Blo 1124630 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B9040187 : Blo 1124630 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B3207691 : Blo 1124630 3207691 := bstep (se 1 (by rfl) ⟨2405768, by rfl⟩ : syracuseStep 3207691 = 4811537) B4811537
theorem B9630251 : Blo 1124630 9630251 := bstep (se 1 (by rfl) ⟨7222688, by rfl⟩ : syracuseStep 9630251 = 14445377) B14445377
theorem B2028167 : Blo 1124630 2028167 := bstep (se 1 (by rfl) ⟨1521125, by rfl⟩ : syracuseStep 2028167 = 3042251) B3042251
theorem B2847433 : Blo 1124630 2847433 := bstep (se 2 (by rfl) ⟨1067787, by rfl⟩ : syracuseStep 2847433 = 2135575) B2135575
theorem B5206799 : Blo 1124630 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B3797819 : Blo 1124630 3797819 := bstep (se 1 (by rfl) ⟨2848364, by rfl⟩ : syracuseStep 3797819 = 5696729) B5696729
theorem B2847575 : Blo 1124630 2847575 := bstep (se 1 (by rfl) ⟨2135681, by rfl⟩ : syracuseStep 2847575 = 4271363) B4271363
theorem B3208193 : Blo 1124630 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B9139333 : Blo 1124630 9139333 := bstep (se 4 (by rfl) ⟨856812, by rfl⟩ : syracuseStep 9139333 = 1713625) B1713625
theorem B3798305 : Blo 1124630 3798305 := bstep (se 2 (by rfl) ⟨1424364, by rfl⟩ : syracuseStep 3798305 = 2848729) B2848729
theorem B3208535 : Blo 1124630 3208535 := bstep (se 1 (by rfl) ⟨2406401, by rfl⟩ : syracuseStep 3208535 = 4812803) B4812803
theorem B1603003 : Blo 1124630 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B5699159 : Blo 1124630 5699159 := bstep (se 1 (by rfl) ⟨4274369, by rfl⟩ : syracuseStep 5699159 = 8548739) B8548739
theorem B93779653 : Blo 1124630 93779653 := bstep (se 4 (by rfl) ⟨8791842, by rfl⟩ : syracuseStep 93779653 = 17583685) B17583685
theorem B1898255 : Blo 1124630 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B3798899 : Blo 1124630 3798899 := bstep (se 1 (by rfl) ⟨2849174, by rfl⟩ : syracuseStep 3798899 = 5698349) B5698349
theorem B3045235 : Blo 1124630 3045235 := bstep (se 1 (by rfl) ⟨2283926, by rfl⟩ : syracuseStep 3045235 = 4567853) B4567853
theorem B8124313 : Blo 1124630 8124313 := bstep (se 2 (by rfl) ⟨3046617, by rfl⟩ : syracuseStep 8124313 = 6093235) B6093235
theorem B13694987 : Blo 1124630 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B5404715 : Blo 1124630 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B5699645 : Blo 1124630 5699645 := bstep (se 3 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 5699645 = 2137367) B2137367
theorem B1898795 : Blo 1124630 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B2030113 : Blo 1124630 2030113 := bstep (se 2 (by rfl) ⟨761292, by rfl⟩ : syracuseStep 2030113 = 1522585) B1522585
theorem B1899193 : Blo 1124630 1899193 := bstep (se 2 (by rfl) ⟨712197, by rfl⟩ : syracuseStep 1899193 = 1424395) B1424395
theorem B6421193 : Blo 1124630 6421193 := bstep (se 2 (by rfl) ⟨2407947, by rfl⟩ : syracuseStep 6421193 = 4815895) B4815895
theorem B8551169 : Blo 1124630 8551169 := bstep (se 2 (by rfl) ⟨3206688, by rfl⟩ : syracuseStep 8551169 = 6413377) B6413377
theorem B3046187 : Blo 1124630 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B2849651 : Blo 1124630 2849651 := bstep (se 1 (by rfl) ⟨2137238, by rfl⟩ : syracuseStep 2849651 = 4274477) B4274477
theorem B1604495 : Blo 1124630 1604495 := bstep (se 1 (by rfl) ⟨1203371, by rfl⟩ : syracuseStep 1604495 = 2406743) B2406743
theorem B3210425 : Blo 1124630 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B1899895 : Blo 1124630 1899895 := bstep (se 1 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 1899895 = 2849843) B2849843
theorem B2850167 : Blo 1124630 2850167 := bstep (se 1 (by rfl) ⟨2137625, by rfl⟩ : syracuseStep 2850167 = 4275251) B4275251
theorem B4062649 : Blo 1124630 4062649 := bstep (se 2 (by rfl) ⟨1523493, by rfl⟩ : syracuseStep 4062649 = 3046987) B3046987
theorem B1900091 : Blo 1124630 1900091 := bstep (se 1 (by rfl) ⟨1425068, by rfl⟩ : syracuseStep 1900091 = 2850137) B2850137
theorem B10813121 : Blo 1124630 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B3604169 : Blo 1124630 3604169 := bstep (se 2 (by rfl) ⟨1351563, by rfl⟩ : syracuseStep 3604169 = 2703127) B2703127
theorem B5701427 : Blo 1124630 5701427 := bstep (se 1 (by rfl) ⟨4276070, by rfl⟩ : syracuseStep 5701427 = 8552141) B8552141
theorem B1900489 : Blo 1124630 1900489 := bstep (se 2 (by rfl) ⟨712683, by rfl⟩ : syracuseStep 1900489 = 1425367) B1425367
theorem B1605577 : Blo 1124630 1605577 := bstep (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) B1204183
theorem B10846223 : Blo 1124630 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B2850835 : Blo 1124630 2850835 := bstep (se 1 (by rfl) ⟨2138126, by rfl⟩ : syracuseStep 2850835 = 4276253) B4276253
theorem B3801167 : Blo 1124630 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B1900793 : Blo 1124630 1900793 := bstep (se 2 (by rfl) ⟨712797, by rfl⟩ : syracuseStep 1900793 = 1425595) B1425595
theorem B1900975 : Blo 1124630 1900975 := bstep (se 1 (by rfl) ⟨1425731, by rfl⟩ : syracuseStep 1900975 = 2851463) B2851463
theorem B3801545 : Blo 1124630 3801545 := bstep (se 2 (by rfl) ⟨1425579, by rfl⟩ : syracuseStep 3801545 = 2851159) B2851159
theorem B1901063 : Blo 1124630 1901063 := bstep (se 1 (by rfl) ⟨1425797, by rfl⟩ : syracuseStep 1901063 = 2851595) B2851595
theorem B3801815 : Blo 1124630 3801815 := bstep (se 1 (by rfl) ⟨2851361, by rfl⟩ : syracuseStep 3801815 = 5702723) B5702723
theorem B1901407 : Blo 1124630 1901407 := bstep (se 1 (by rfl) ⟨1426055, by rfl⟩ : syracuseStep 1901407 = 2852111) B2852111
theorem B3802031 : Blo 1124630 3802031 := bstep (se 1 (by rfl) ⟨2851523, by rfl⟩ : syracuseStep 3802031 = 5703047) B5703047
theorem B1901495 : Blo 1124630 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B2851919 : Blo 1124630 2851919 := bstep (se 1 (by rfl) ⟨2138939, by rfl⟩ : syracuseStep 2851919 = 4277879) B4277879
theorem B36602999 : Blo 1124630 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B4818167 : Blo 1124630 4818167 := bstep (se 1 (by rfl) ⟨3613625, by rfl⟩ : syracuseStep 4818167 = 7227251) B7227251
theorem B3605771 : Blo 1124630 3605771 := bstep (se 1 (by rfl) ⟨2704328, by rfl⟩ : syracuseStep 3605771 = 5408657) B5408657
theorem B7701875 : Blo 1124630 7701875 := bstep (se 1 (by rfl) ⟨5776406, by rfl⟩ : syracuseStep 7701875 = 11552813) B11552813
theorem B3605885 : Blo 1124630 3605885 := bstep (se 3 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 3605885 = 1352207) B1352207
theorem B5211611 : Blo 1124630 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B1902089 : Blo 1124630 1902089 := bstep (se 2 (by rfl) ⟨713283, by rfl⟩ : syracuseStep 1902089 = 1426567) B1426567
theorem B5146259 : Blo 1124630 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B1902251 : Blo 1124630 1902251 := bstep (se 1 (by rfl) ⟨1426688, by rfl⟩ : syracuseStep 1902251 = 2853377) B2853377
theorem B2852567 : Blo 1124630 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B7210745 : Blo 1124630 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B5703533 : Blo 1124630 5703533 := bstep (se 3 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 5703533 = 2138825) B2138825
theorem B5703695 : Blo 1124630 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B2852921 : Blo 1124630 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B1902649 : Blo 1124630 1902649 := bstep (se 2 (by rfl) ⟨713493, by rfl⟩ : syracuseStep 1902649 = 1426987) B1426987
theorem B8128669 : Blo 1124630 8128669 := bstep (se 3 (by rfl) ⟨1524125, by rfl⟩ : syracuseStep 8128669 = 3048251) B3048251
theorem B1902791 : Blo 1124630 1902791 := bstep (se 1 (by rfl) ⟨1427093, by rfl⟩ : syracuseStep 1902791 = 2854187) B2854187
theorem B1902953 : Blo 1124630 1902953 := bstep (se 2 (by rfl) ⟨713607, by rfl⟩ : syracuseStep 1902953 = 1427215) B1427215
theorem B1804763 : Blo 1124630 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B1903351 : Blo 1124630 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B1903547 : Blo 1124630 1903547 := bstep (se 1 (by rfl) ⟨1427660, by rfl⟩ : syracuseStep 1903547 = 2855321) B2855321
theorem B1805275 : Blo 1124630 1805275 := bstep (se 1 (by rfl) ⟨1353956, by rfl⟩ : syracuseStep 1805275 = 2707913) B2707913
theorem B1903655 : Blo 1124630 1903655 := bstep (se 1 (by rfl) ⟨1427741, by rfl⟩ : syracuseStep 1903655 = 2855483) B2855483
theorem B3804407 : Blo 1124630 3804407 := bstep (se 1 (by rfl) ⟨2853305, by rfl⟩ : syracuseStep 3804407 = 5706611) B5706611
theorem B1903945 : Blo 1124630 1903945 := bstep (se 2 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 1903945 = 1427959) B1427959
theorem B1903979 : Blo 1124630 1903979 := bstep (se 1 (by rfl) ⟨1427984, by rfl⟩ : syracuseStep 1903979 = 2855969) B2855969
theorem B6425999 : Blo 1124630 6425999 := bstep (se 1 (by rfl) ⟨4819499, by rfl⟩ : syracuseStep 6425999 = 9638999) B9638999
theorem B3608027 : Blo 1124630 3608027 := bstep (se 1 (by rfl) ⟨2706020, by rfl⟩ : syracuseStep 3608027 = 5412041) B5412041
theorem B3804731 : Blo 1124630 3804731 := bstep (se 1 (by rfl) ⟨2853548, by rfl⟩ : syracuseStep 3804731 = 5707097) B5707097
theorem B4820627 : Blo 1124630 4820627 := bstep (se 1 (by rfl) ⟨3615470, by rfl⟩ : syracuseStep 4820627 = 7230941) B7230941
theorem B1904377 : Blo 1124630 1904377 := bstep (se 2 (by rfl) ⟨714141, by rfl⟩ : syracuseStep 1904377 = 1428283) B1428283
theorem B10817347 : Blo 1124630 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B3805001 : Blo 1124630 3805001 := bstep (se 2 (by rfl) ⟨1426875, by rfl⟩ : syracuseStep 3805001 = 2853751) B2853751
theorem B1806185 : Blo 1124630 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B36507509 : Blo 1124630 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B1806223 : Blo 1124630 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B18255779 : Blo 1124630 18255779 := bstep (se 1 (by rfl) ⟨13691834, by rfl⟩ : syracuseStep 18255779 = 27383669) B27383669
theorem B14061649 : Blo 1124630 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B2855159 : Blo 1124630 2855159 := bstep (se 1 (by rfl) ⟨2141369, by rfl⟩ : syracuseStep 2855159 = 4282739) B4282739
theorem B4624651 : Blo 1124630 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B5706449 : Blo 1124630 5706449 := bstep (se 2 (by rfl) ⟨2139918, by rfl⟩ : syracuseStep 5706449 = 4279837) B4279837
theorem B2888623 : Blo 1124630 2888623 := bstep (se 1 (by rfl) ⟨2166467, by rfl⟩ : syracuseStep 2888623 = 4332935) B4332935
theorem B8557487 : Blo 1124630 8557487 := bstep (se 1 (by rfl) ⟨6418115, by rfl⟩ : syracuseStep 8557487 = 12836231) B12836231
theorem B3249079 : Blo 1124630 3249079 := bstep (se 1 (by rfl) ⟨2436809, by rfl⟩ : syracuseStep 3249079 = 4873619) B4873619
theorem B3806135 : Blo 1124630 3806135 := bstep (se 1 (by rfl) ⟨2854601, by rfl⟩ : syracuseStep 3806135 = 5709203) B5709203
theorem B1807607 : Blo 1124630 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B26056181 : Blo 1124630 26056181 := bstep (se 5 (by rfl) ⟨1221383, by rfl⟩ : syracuseStep 26056181 = 2442767) B2442767
theorem B3806729 : Blo 1124630 3806729 := bstep (se 2 (by rfl) ⟨1427523, by rfl⟩ : syracuseStep 3806729 = 2855047) B2855047
theorem B8230547 : Blo 1124630 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B14849729 : Blo 1124630 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B10819271 : Blo 1124630 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B2856647 : Blo 1124630 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B3610487 : Blo 1124630 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B3610703 : Blo 1124630 3610703 := bstep (se 1 (by rfl) ⟨2708027, by rfl⟩ : syracuseStep 3610703 = 5416055) B5416055
theorem B18520163 : Blo 1124630 18520163 := bstep (se 1 (by rfl) ⟨13890122, by rfl⟩ : syracuseStep 18520163 = 27780245) B27780245
theorem B28907765 : Blo 1124630 28907765 := bstep (se 5 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 28907765 = 2710103) B2710103
theorem B3807593 : Blo 1124630 3807593 := bstep (se 2 (by rfl) ⟨1427847, by rfl⟩ : syracuseStep 3807593 = 2855695) B2855695
theorem B2136775 : Blo 1124630 2136775 := bstep (se 1 (by rfl) ⟨1602581, by rfl⟩ : syracuseStep 2136775 = 3205163) B3205163
theorem B3808187 : Blo 1124630 3808187 := bstep (se 1 (by rfl) ⟨2856140, by rfl⟩ : syracuseStep 3808187 = 5712281) B5712281
theorem B5708879 : Blo 1124630 5708879 := bstep (se 1 (by rfl) ⟨4281659, by rfl⟩ : syracuseStep 5708879 = 8563319) B8563319
theorem B2530475 : Blo 1124630 2530475 := bstep (se 1 (by rfl) ⟨1897856, by rfl⟩ : syracuseStep 2530475 = 3795713) B3795713
theorem B2137337 : Blo 1124630 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B10427737 : Blo 1124630 10427737 := bstep (se 2 (by rfl) ⟨3910401, by rfl⟩ : syracuseStep 10427737 = 7820803) B7820803
theorem B9641389 : Blo 1124630 9641389 := bstep (se 3 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 9641389 = 3615521) B3615521
theorem B2137519 : Blo 1124630 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B2531015 : Blo 1124630 2531015 := bstep (se 1 (by rfl) ⟨1898261, by rfl⟩ : syracuseStep 2531015 = 3796523) B3796523
theorem B5709527 : Blo 1124630 5709527 := bstep (se 1 (by rfl) ⟨4282145, by rfl⟩ : syracuseStep 5709527 = 8564291) B8564291
theorem B1352111 : Blo 1124630 1352111 := bstep (se 1 (by rfl) ⟨1014083, by rfl⟩ : syracuseStep 1352111 = 2028167) B2028167
theorem B2531879 : Blo 1124630 2531879 := bstep (se 1 (by rfl) ⟨1898909, by rfl⟩ : syracuseStep 2531879 = 3797819) B3797819
theorem B3613319 : Blo 1124630 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B2138795 : Blo 1124630 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B3613369 : Blo 1124630 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B2532203 : Blo 1124630 2532203 := bstep (se 1 (by rfl) ⟨1899152, by rfl⟩ : syracuseStep 2532203 = 3798305) B3798305
theorem B2139023 : Blo 1124630 2139023 := bstep (se 1 (by rfl) ⟨1604267, by rfl⟩ : syracuseStep 2139023 = 3208535) B3208535
theorem B2532257 : Blo 1124630 2532257 := bstep (se 2 (by rfl) ⟨949596, by rfl⟩ : syracuseStep 2532257 = 1899193) B1899193
theorem B12166145 : Blo 1124630 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B29664461 : Blo 1124630 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B2532599 : Blo 1124630 2532599 := bstep (se 1 (by rfl) ⟨1899449, by rfl⟩ : syracuseStep 2532599 = 3798899) B3798899
theorem B2533193 : Blo 1124630 2533193 := bstep (se 2 (by rfl) ⟨949947, by rfl⟩ : syracuseStep 2533193 = 1899895) B1899895
theorem B5416865 : Blo 1124630 5416865 := bstep (se 2 (by rfl) ⟨2031324, by rfl⟩ : syracuseStep 5416865 = 4062649) B4062649
theorem B3614651 : Blo 1124630 3614651 := bstep (se 1 (by rfl) ⟨2710988, by rfl⟩ : syracuseStep 3614651 = 5421977) B5421977
theorem B8660945 : Blo 1124630 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B2140283 : Blo 1124630 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B1124647 : Blo 1124630 1124647 := bstep (se 1 (by rfl) ⟨843485, by rfl⟩ : syracuseStep 1124647 = 1686971) B1686971
theorem B1124687 : Blo 1124630 1124687 := bstep (se 1 (by rfl) ⟨843515, by rfl⟩ : syracuseStep 1124687 = 1687031) B1687031
theorem B1124703 : Blo 1124630 1124703 := bstep (se 1 (by rfl) ⟨843527, by rfl⟩ : syracuseStep 1124703 = 1687055) B1687055
theorem B1124731 : Blo 1124630 1124731 := bstep (se 1 (by rfl) ⟨843548, by rfl⟩ : syracuseStep 1124731 = 1687097) B1687097
theorem B3615101 : Blo 1124630 3615101 := bstep (se 3 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 3615101 = 1355663) B1355663
theorem B1124783 : Blo 1124630 1124783 := bstep (se 1 (by rfl) ⟨843587, by rfl⟩ : syracuseStep 1124783 = 1687175) B1687175
theorem B1124807 : Blo 1124630 1124807 := bstep (se 1 (by rfl) ⟨843605, by rfl⟩ : syracuseStep 1124807 = 1687211) B1687211
theorem B1124827 : Blo 1124630 1124827 := bstep (se 1 (by rfl) ⟨843620, by rfl⟩ : syracuseStep 1124827 = 1687241) B1687241
theorem B2402779 : Blo 1124630 2402779 := bstep (se 1 (by rfl) ⟨1802084, by rfl⟩ : syracuseStep 2402779 = 3604169) B3604169
theorem B1124903 : Blo 1124630 1124903 := bstep (se 1 (by rfl) ⟨843677, by rfl⟩ : syracuseStep 1124903 = 1687355) B1687355
theorem B5712443 : Blo 1124630 5712443 := bstep (se 1 (by rfl) ⟨4284332, by rfl⟩ : syracuseStep 5712443 = 8568665) B8568665
theorem B1124943 : Blo 1124630 1124943 := bstep (se 1 (by rfl) ⟨843707, by rfl⟩ : syracuseStep 1124943 = 1687415) B1687415
theorem B1124959 : Blo 1124630 1124959 := bstep (se 1 (by rfl) ⟨843719, by rfl⟩ : syracuseStep 1124959 = 1687439) B1687439
theorem B2533985 : Blo 1124630 2533985 := bstep (se 2 (by rfl) ⟨950244, by rfl⟩ : syracuseStep 2533985 = 1900489) B1900489
theorem B2140769 : Blo 1124630 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B1124987 : Blo 1124630 1124987 := bstep (se 1 (by rfl) ⟨843740, by rfl⟩ : syracuseStep 1124987 = 1687481) B1687481
theorem B1125039 : Blo 1124630 1125039 := bstep (se 1 (by rfl) ⟨843779, by rfl⟩ : syracuseStep 1125039 = 1687559) B1687559
theorem B1125063 : Blo 1124630 1125063 := bstep (se 1 (by rfl) ⟨843797, by rfl⟩ : syracuseStep 1125063 = 1687595) B1687595
theorem B1125083 : Blo 1124630 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B2140921 : Blo 1124630 2140921 := bstep (se 2 (by rfl) ⟨802845, by rfl⟩ : syracuseStep 2140921 = 1605691) B1605691
theorem B4270877 : Blo 1124630 4270877 := bstep (se 3 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 4270877 = 1601579) B1601579
theorem B1125159 : Blo 1124630 1125159 := bstep (se 1 (by rfl) ⟨843869, by rfl⟩ : syracuseStep 1125159 = 1687739) B1687739
theorem B4631363 : Blo 1124630 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B1125199 : Blo 1124630 1125199 := bstep (se 1 (by rfl) ⟨843899, by rfl⟩ : syracuseStep 1125199 = 1687799) B1687799
theorem B1125215 : Blo 1124630 1125215 := bstep (se 1 (by rfl) ⟨843911, by rfl⟩ : syracuseStep 1125215 = 1687823) B1687823
theorem B1125243 : Blo 1124630 1125243 := bstep (se 1 (by rfl) ⟨843932, by rfl⟩ : syracuseStep 1125243 = 1687865) B1687865
theorem B1125295 : Blo 1124630 1125295 := bstep (se 1 (by rfl) ⟨843971, by rfl⟩ : syracuseStep 1125295 = 1687943) B1687943
theorem B2534327 : Blo 1124630 2534327 := bstep (se 1 (by rfl) ⟨1900745, by rfl⟩ : syracuseStep 2534327 = 3801491) B3801491
theorem B1125319 : Blo 1124630 1125319 := bstep (se 1 (by rfl) ⟨843989, by rfl⟩ : syracuseStep 1125319 = 1687979) B1687979
theorem B1125339 : Blo 1124630 1125339 := bstep (se 1 (by rfl) ⟨844004, by rfl⟩ : syracuseStep 1125339 = 1688009) B1688009
theorem B1125415 : Blo 1124630 1125415 := bstep (se 1 (by rfl) ⟨844061, by rfl⟩ : syracuseStep 1125415 = 1688123) B1688123
theorem B1125455 : Blo 1124630 1125455 := bstep (se 1 (by rfl) ⟨844091, by rfl⟩ : syracuseStep 1125455 = 1688183) B1688183
theorem B1125471 : Blo 1124630 1125471 := bstep (se 1 (by rfl) ⟨844103, by rfl⟩ : syracuseStep 1125471 = 1688207) B1688207
theorem B16264309 : Blo 1124630 16264309 := bstep (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) B1524779
theorem B1125499 : Blo 1124630 1125499 := bstep (se 1 (by rfl) ⟨844124, by rfl⟩ : syracuseStep 1125499 = 1688249) B1688249
theorem B1125551 : Blo 1124630 1125551 := bstep (se 1 (by rfl) ⟨844163, by rfl⟩ : syracuseStep 1125551 = 1688327) B1688327
theorem B5713091 : Blo 1124630 5713091 := bstep (se 1 (by rfl) ⟨4284818, by rfl⟩ : syracuseStep 5713091 = 8569637) B8569637
theorem B1125575 : Blo 1124630 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B1125595 : Blo 1124630 1125595 := bstep (se 1 (by rfl) ⟨844196, by rfl⟩ : syracuseStep 1125595 = 1688393) B1688393
theorem B1125671 : Blo 1124630 1125671 := bstep (se 1 (by rfl) ⟨844253, by rfl⟩ : syracuseStep 1125671 = 1688507) B1688507
theorem B97430849 : Blo 1124630 97430849 := bstep (se 2 (by rfl) ⟨36536568, by rfl⟩ : syracuseStep 97430849 = 73073137) B73073137
theorem B1125711 : Blo 1124630 1125711 := bstep (se 1 (by rfl) ⟨844283, by rfl⟩ : syracuseStep 1125711 = 1688567) B1688567
theorem B1125727 : Blo 1124630 1125727 := bstep (se 1 (by rfl) ⟨844295, by rfl⟩ : syracuseStep 1125727 = 1688591) B1688591
theorem B1125755 : Blo 1124630 1125755 := bstep (se 1 (by rfl) ⟨844316, by rfl⟩ : syracuseStep 1125755 = 1688633) B1688633
theorem B1125807 : Blo 1124630 1125807 := bstep (se 1 (by rfl) ⟨844355, by rfl⟩ : syracuseStep 1125807 = 1688711) B1688711
theorem B1125831 : Blo 1124630 1125831 := bstep (se 1 (by rfl) ⟨844373, by rfl⟩ : syracuseStep 1125831 = 1688747) B1688747
theorem B4271561 : Blo 1124630 4271561 := bstep (se 2 (by rfl) ⟨1601835, by rfl⟩ : syracuseStep 4271561 = 3203671) B3203671
theorem B1125851 : Blo 1124630 1125851 := bstep (se 1 (by rfl) ⟨844388, by rfl⟩ : syracuseStep 1125851 = 1688777) B1688777
theorem B2534921 : Blo 1124630 2534921 := bstep (se 2 (by rfl) ⟨950595, by rfl⟩ : syracuseStep 2534921 = 1901191) B1901191
theorem B1125927 : Blo 1124630 1125927 := bstep (se 1 (by rfl) ⟨844445, by rfl⟩ : syracuseStep 1125927 = 1688891) B1688891
theorem B1125967 : Blo 1124630 1125967 := bstep (se 1 (by rfl) ⟨844475, by rfl⟩ : syracuseStep 1125967 = 1688951) B1688951
theorem B1125983 : Blo 1124630 1125983 := bstep (se 1 (by rfl) ⟨844487, by rfl⟩ : syracuseStep 1125983 = 1688975) B1688975
theorem B1126011 : Blo 1124630 1126011 := bstep (se 1 (by rfl) ⟨844508, by rfl⟩ : syracuseStep 1126011 = 1689017) B1689017
theorem B1126063 : Blo 1124630 1126063 := bstep (se 1 (by rfl) ⟨844547, by rfl⟩ : syracuseStep 1126063 = 1689095) B1689095
theorem B1126087 : Blo 1124630 1126087 := bstep (se 1 (by rfl) ⟨844565, by rfl⟩ : syracuseStep 1126087 = 1689131) B1689131
theorem B1126107 : Blo 1124630 1126107 := bstep (se 1 (by rfl) ⟨844580, by rfl⟩ : syracuseStep 1126107 = 1689161) B1689161
theorem B1126183 : Blo 1124630 1126183 := bstep (se 1 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 1126183 = 1689275) B1689275
theorem B1126223 : Blo 1124630 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B1126239 : Blo 1124630 1126239 := bstep (se 1 (by rfl) ⟨844679, by rfl⟩ : syracuseStep 1126239 = 1689359) B1689359
theorem B2535263 : Blo 1124630 2535263 := bstep (se 1 (by rfl) ⟨1901447, by rfl⟩ : syracuseStep 2535263 = 3802895) B3802895
theorem B1126267 : Blo 1124630 1126267 := bstep (se 1 (by rfl) ⟨844700, by rfl⟩ : syracuseStep 1126267 = 1689401) B1689401
theorem B4272047 : Blo 1124630 4272047 := bstep (se 1 (by rfl) ⟨3204035, by rfl⟩ : syracuseStep 4272047 = 6408071) B6408071
theorem B1126319 : Blo 1124630 1126319 := bstep (se 1 (by rfl) ⟨844739, by rfl⟩ : syracuseStep 1126319 = 1689479) B1689479
theorem B1126343 : Blo 1124630 1126343 := bstep (se 1 (by rfl) ⟨844757, by rfl⟩ : syracuseStep 1126343 = 1689515) B1689515
theorem B1126363 : Blo 1124630 1126363 := bstep (se 1 (by rfl) ⟨844772, by rfl⟩ : syracuseStep 1126363 = 1689545) B1689545
theorem B2535443 : Blo 1124630 2535443 := bstep (se 1 (by rfl) ⟨1901582, by rfl⟩ : syracuseStep 2535443 = 3803165) B3803165
theorem B2142227 : Blo 1124630 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B1126439 : Blo 1124630 1126439 := bstep (se 1 (by rfl) ⟨844829, by rfl⟩ : syracuseStep 1126439 = 1689659) B1689659
theorem B1126479 : Blo 1124630 1126479 := bstep (se 1 (by rfl) ⟨844859, by rfl⟩ : syracuseStep 1126479 = 1689719) B1689719
theorem B1126495 : Blo 1124630 1126495 := bstep (se 1 (by rfl) ⟨844871, by rfl⟩ : syracuseStep 1126495 = 1689743) B1689743
theorem B1126523 : Blo 1124630 1126523 := bstep (se 1 (by rfl) ⟨844892, by rfl⟩ : syracuseStep 1126523 = 1689785) B1689785
theorem B2142379 : Blo 1124630 2142379 := bstep (se 1 (by rfl) ⟨1606784, by rfl⟩ : syracuseStep 2142379 = 3213569) B3213569
theorem B1126575 : Blo 1124630 1126575 := bstep (se 1 (by rfl) ⟨844931, by rfl⟩ : syracuseStep 1126575 = 1689863) B1689863
theorem B1126599 : Blo 1124630 1126599 := bstep (se 1 (by rfl) ⟨844949, by rfl⟩ : syracuseStep 1126599 = 1689899) B1689899
theorem B1126619 : Blo 1124630 1126619 := bstep (se 1 (by rfl) ⟨844964, by rfl⟩ : syracuseStep 1126619 = 1689929) B1689929
theorem B1126695 : Blo 1124630 1126695 := bstep (se 1 (by rfl) ⟨845021, by rfl⟩ : syracuseStep 1126695 = 1690043) B1690043
theorem B5419325 : Blo 1124630 5419325 := bstep (se 3 (by rfl) ⟨1016123, by rfl⟩ : syracuseStep 5419325 = 2032247) B2032247
theorem B1126735 : Blo 1124630 1126735 := bstep (se 1 (by rfl) ⟨845051, by rfl⟩ : syracuseStep 1126735 = 1690103) B1690103
theorem B1126751 : Blo 1124630 1126751 := bstep (se 1 (by rfl) ⟨845063, by rfl⟩ : syracuseStep 1126751 = 1690127) B1690127
theorem B2535785 : Blo 1124630 2535785 := bstep (se 2 (by rfl) ⟨950919, by rfl⟩ : syracuseStep 2535785 = 1901839) B1901839
theorem B1126779 : Blo 1124630 1126779 := bstep (se 1 (by rfl) ⟨845084, by rfl⟩ : syracuseStep 1126779 = 1690169) B1690169
theorem B73216385 : Blo 1124630 73216385 := bstep (se 2 (by rfl) ⟨27456144, by rfl⟩ : syracuseStep 73216385 = 54912289) B54912289
theorem B2142607 : Blo 1124630 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B1126831 : Blo 1124630 1126831 := bstep (se 1 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 1126831 = 1690247) B1690247
theorem B1126855 : Blo 1124630 1126855 := bstep (se 1 (by rfl) ⟨845141, by rfl⟩ : syracuseStep 1126855 = 1690283) B1690283
theorem B1126875 : Blo 1124630 1126875 := bstep (se 1 (by rfl) ⟨845156, by rfl⟩ : syracuseStep 1126875 = 1690313) B1690313
theorem B1126951 : Blo 1124630 1126951 := bstep (se 1 (by rfl) ⟨845213, by rfl⟩ : syracuseStep 1126951 = 1690427) B1690427
theorem B1126991 : Blo 1124630 1126991 := bstep (se 1 (by rfl) ⟨845243, by rfl⟩ : syracuseStep 1126991 = 1690487) B1690487
theorem B1127007 : Blo 1124630 1127007 := bstep (se 1 (by rfl) ⟨845255, by rfl⟩ : syracuseStep 1127007 = 1690511) B1690511
theorem B1127035 : Blo 1124630 1127035 := bstep (se 1 (by rfl) ⟨845276, by rfl⟩ : syracuseStep 1127035 = 1690553) B1690553
theorem B1127087 : Blo 1124630 1127087 := bstep (se 1 (by rfl) ⟨845315, by rfl⟩ : syracuseStep 1127087 = 1690631) B1690631
theorem B1127111 : Blo 1124630 1127111 := bstep (se 1 (by rfl) ⟨845333, by rfl⟩ : syracuseStep 1127111 = 1690667) B1690667
theorem B4272851 : Blo 1124630 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B1127131 : Blo 1124630 1127131 := bstep (se 1 (by rfl) ⟨845348, by rfl⟩ : syracuseStep 1127131 = 1690697) B1690697
theorem B1127207 : Blo 1124630 1127207 := bstep (se 1 (by rfl) ⟨845405, by rfl⟩ : syracuseStep 1127207 = 1690811) B1690811
theorem B1127247 : Blo 1124630 1127247 := bstep (se 1 (by rfl) ⟨845435, by rfl⟩ : syracuseStep 1127247 = 1690871) B1690871
theorem B1127263 : Blo 1124630 1127263 := bstep (se 1 (by rfl) ⟨845447, by rfl⟩ : syracuseStep 1127263 = 1690895) B1690895
theorem B1127291 : Blo 1124630 1127291 := bstep (se 1 (by rfl) ⟨845468, by rfl⟩ : syracuseStep 1127291 = 1690937) B1690937
theorem B1127343 : Blo 1124630 1127343 := bstep (se 1 (by rfl) ⟨845507, by rfl⟩ : syracuseStep 1127343 = 1691015) B1691015
theorem B2536379 : Blo 1124630 2536379 := bstep (se 1 (by rfl) ⟨1902284, by rfl⟩ : syracuseStep 2536379 = 3804569) B3804569
theorem B1127367 : Blo 1124630 1127367 := bstep (se 1 (by rfl) ⟨845525, by rfl⟩ : syracuseStep 1127367 = 1691051) B1691051
theorem B1127387 : Blo 1124630 1127387 := bstep (se 1 (by rfl) ⟨845540, by rfl⟩ : syracuseStep 1127387 = 1691081) B1691081
theorem B1127463 : Blo 1124630 1127463 := bstep (se 1 (by rfl) ⟨845597, by rfl⟩ : syracuseStep 1127463 = 1691195) B1691195
theorem B14431283 : Blo 1124630 14431283 := bstep (se 1 (by rfl) ⟨10823462, by rfl⟩ : syracuseStep 14431283 = 21646925) B21646925
theorem B2536505 : Blo 1124630 2536505 := bstep (se 2 (by rfl) ⟨951189, by rfl⟩ : syracuseStep 2536505 = 1902379) B1902379
theorem B1127503 : Blo 1124630 1127503 := bstep (se 1 (by rfl) ⟨845627, by rfl⟩ : syracuseStep 1127503 = 1691255) B1691255
theorem B1127519 : Blo 1124630 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B1127547 : Blo 1124630 1127547 := bstep (se 1 (by rfl) ⟨845660, by rfl⟩ : syracuseStep 1127547 = 1691321) B1691321
theorem B1127599 : Blo 1124630 1127599 := bstep (se 1 (by rfl) ⟨845699, by rfl⟩ : syracuseStep 1127599 = 1691399) B1691399
theorem B1127623 : Blo 1124630 1127623 := bstep (se 1 (by rfl) ⟨845717, by rfl⟩ : syracuseStep 1127623 = 1691435) B1691435
theorem B1127643 : Blo 1124630 1127643 := bstep (se 1 (by rfl) ⟨845732, by rfl⟩ : syracuseStep 1127643 = 1691465) B1691465
theorem B1127719 : Blo 1124630 1127719 := bstep (se 1 (by rfl) ⟨845789, by rfl⟩ : syracuseStep 1127719 = 1691579) B1691579
theorem B1127759 : Blo 1124630 1127759 := bstep (se 1 (by rfl) ⟨845819, by rfl⟩ : syracuseStep 1127759 = 1691639) B1691639
theorem B1127775 : Blo 1124630 1127775 := bstep (se 1 (by rfl) ⟨845831, by rfl⟩ : syracuseStep 1127775 = 1691663) B1691663
theorem B1127803 : Blo 1124630 1127803 := bstep (se 1 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 1127803 = 1691705) B1691705
theorem B2536847 : Blo 1124630 2536847 := bstep (se 1 (by rfl) ⟨1902635, by rfl⟩ : syracuseStep 2536847 = 3805271) B3805271
theorem B1127855 : Blo 1124630 1127855 := bstep (se 1 (by rfl) ⟨845891, by rfl⟩ : syracuseStep 1127855 = 1691783) B1691783
theorem B1127879 : Blo 1124630 1127879 := bstep (se 1 (by rfl) ⟨845909, by rfl⟩ : syracuseStep 1127879 = 1691819) B1691819
theorem B12694985 : Blo 1124630 12694985 := bstep (se 2 (by rfl) ⟨4760619, by rfl⟩ : syracuseStep 12694985 = 9521239) B9521239
theorem B1127899 : Blo 1124630 1127899 := bstep (se 1 (by rfl) ⟨845924, by rfl⟩ : syracuseStep 1127899 = 1691849) B1691849
theorem B8566235 : Blo 1124630 8566235 := bstep (se 1 (by rfl) ⟨6424676, by rfl⟩ : syracuseStep 8566235 = 12849353) B12849353
theorem B10827269 : Blo 1124630 10827269 := bstep (se 4 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 10827269 = 2030113) B2030113
theorem B1127975 : Blo 1124630 1127975 := bstep (se 1 (by rfl) ⟨845981, by rfl⟩ : syracuseStep 1127975 = 1691963) B1691963
theorem B1128015 : Blo 1124630 1128015 := bstep (se 1 (by rfl) ⟨846011, by rfl⟩ : syracuseStep 1128015 = 1692023) B1692023
theorem B1128031 : Blo 1124630 1128031 := bstep (se 1 (by rfl) ⟨846023, by rfl⟩ : syracuseStep 1128031 = 1692047) B1692047
theorem B1128059 : Blo 1124630 1128059 := bstep (se 1 (by rfl) ⟨846044, by rfl⟩ : syracuseStep 1128059 = 1692089) B1692089
theorem B1128111 : Blo 1124630 1128111 := bstep (se 1 (by rfl) ⟨846083, by rfl⟩ : syracuseStep 1128111 = 1692167) B1692167
theorem B1128135 : Blo 1124630 1128135 := bstep (se 1 (by rfl) ⟨846101, by rfl⟩ : syracuseStep 1128135 = 1692203) B1692203
theorem B2537171 : Blo 1124630 2537171 := bstep (se 1 (by rfl) ⟨1902878, by rfl⟩ : syracuseStep 2537171 = 3805757) B3805757
theorem B1128155 : Blo 1124630 1128155 := bstep (se 1 (by rfl) ⟨846116, by rfl⟩ : syracuseStep 1128155 = 1692233) B1692233
theorem B1128231 : Blo 1124630 1128231 := bstep (se 1 (by rfl) ⟨846173, by rfl⟩ : syracuseStep 1128231 = 1692347) B1692347
theorem B1128271 : Blo 1124630 1128271 := bstep (se 1 (by rfl) ⟨846203, by rfl⟩ : syracuseStep 1128271 = 1692407) B1692407
theorem B7714655 : Blo 1124630 7714655 := bstep (se 1 (by rfl) ⟨5785991, by rfl⟩ : syracuseStep 7714655 = 11571983) B11571983
theorem B1128287 : Blo 1124630 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B1128315 : Blo 1124630 1128315 := bstep (se 1 (by rfl) ⟨846236, by rfl⟩ : syracuseStep 1128315 = 1692473) B1692473
theorem B1128367 : Blo 1124630 1128367 := bstep (se 1 (by rfl) ⟨846275, by rfl⟩ : syracuseStep 1128367 = 1692551) B1692551
theorem B8566721 : Blo 1124630 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B1128391 : Blo 1124630 1128391 := bstep (se 1 (by rfl) ⟨846293, by rfl⟩ : syracuseStep 1128391 = 1692587) B1692587
theorem B1128411 : Blo 1124630 1128411 := bstep (se 1 (by rfl) ⟨846308, by rfl⟩ : syracuseStep 1128411 = 1692617) B1692617
theorem B1128487 : Blo 1124630 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B1128527 : Blo 1124630 1128527 := bstep (se 1 (by rfl) ⟨846395, by rfl⟩ : syracuseStep 1128527 = 1692791) B1692791
theorem B1128543 : Blo 1124630 1128543 := bstep (se 1 (by rfl) ⟨846407, by rfl⟩ : syracuseStep 1128543 = 1692815) B1692815
theorem B1128571 : Blo 1124630 1128571 := bstep (se 1 (by rfl) ⟨846428, by rfl⟩ : syracuseStep 1128571 = 1692857) B1692857
theorem B1128623 : Blo 1124630 1128623 := bstep (se 1 (by rfl) ⟨846467, by rfl⟩ : syracuseStep 1128623 = 1692935) B1692935
theorem B5421323 : Blo 1124630 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B7223867 : Blo 1124630 7223867 := bstep (se 1 (by rfl) ⟨5417900, by rfl⟩ : syracuseStep 7223867 = 10835801) B10835801
theorem B2538107 : Blo 1124630 2538107 := bstep (se 1 (by rfl) ⟨1903580, by rfl⟩ : syracuseStep 2538107 = 3807161) B3807161
theorem B1424071 : Blo 1124630 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B3422969 : Blo 1124630 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B2538233 : Blo 1124630 2538233 := bstep (se 2 (by rfl) ⟨951837, by rfl⟩ : syracuseStep 2538233 = 1903675) B1903675
theorem B3849079 : Blo 1124630 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B10828727 : Blo 1124630 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B2538503 : Blo 1124630 2538503 := bstep (se 1 (by rfl) ⟨1903877, by rfl⟩ : syracuseStep 2538503 = 3807755) B3807755
theorem B2538575 : Blo 1124630 2538575 := bstep (se 1 (by rfl) ⟨1903931, by rfl⟩ : syracuseStep 2538575 = 3807863) B3807863
theorem B4275281 : Blo 1124630 4275281 := bstep (se 2 (by rfl) ⟨1603230, by rfl⟩ : syracuseStep 4275281 = 3206461) B3206461
theorem B14630005 : Blo 1124630 14630005 := bstep (se 5 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 14630005 = 1371563) B1371563
theorem B11549891 : Blo 1124630 11549891 := bstep (se 1 (by rfl) ⟨8662418, by rfl⟩ : syracuseStep 11549891 = 17324837) B17324837
theorem B9125135 : Blo 1124630 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B8568179 : Blo 1124630 8568179 := bstep (se 1 (by rfl) ⟨6426134, by rfl⟩ : syracuseStep 8568179 = 12852269) B12852269
theorem B1686959 : Blo 1124630 1686959 := bstep (se 1 (by rfl) ⟨1265219, by rfl⟩ : syracuseStep 1686959 = 2530439) B2530439
theorem B2538971 : Blo 1124630 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B1687049 : Blo 1124630 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B4275737 : Blo 1124630 4275737 := bstep (se 2 (by rfl) ⟨1603401, by rfl⟩ : syracuseStep 4275737 = 3206803) B3206803
theorem B1687079 : Blo 1124630 1687079 := bstep (se 1 (by rfl) ⟨1265309, by rfl⟩ : syracuseStep 1687079 = 2530619) B2530619
theorem B2702945 : Blo 1124630 2702945 := bstep (se 2 (by rfl) ⟨1013604, by rfl⟩ : syracuseStep 2702945 = 2027209) B2027209
theorem B1687163 : Blo 1124630 1687163 := bstep (se 1 (by rfl) ⟨1265372, by rfl⟩ : syracuseStep 1687163 = 2530745) B2530745
theorem B1687289 : Blo 1124630 1687289 := bstep (se 2 (by rfl) ⟨632733, by rfl⟩ : syracuseStep 1687289 = 1265467) B1265467
theorem B6504185 : Blo 1124630 6504185 := bstep (se 2 (by rfl) ⟨2439069, by rfl⟩ : syracuseStep 6504185 = 4878139) B4878139
theorem B15417155 : Blo 1124630 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B1687391 : Blo 1124630 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B1687403 : Blo 1124630 1687403 := bstep (se 1 (by rfl) ⟨1265552, by rfl⟩ : syracuseStep 1687403 = 2531105) B2531105
theorem B1687631 : Blo 1124630 1687631 := bstep (se 1 (by rfl) ⟨1265723, by rfl⟩ : syracuseStep 1687631 = 2531447) B2531447
theorem B5783633 : Blo 1124630 5783633 := bstep (se 2 (by rfl) ⟨2168862, by rfl⟩ : syracuseStep 5783633 = 4337725) B4337725
theorem B1687751 : Blo 1124630 1687751 := bstep (se 1 (by rfl) ⟨1265813, by rfl⟩ : syracuseStep 1687751 = 2531627) B2531627
theorem B1687913 : Blo 1124630 1687913 := bstep (se 2 (by rfl) ⟨632967, by rfl⟩ : syracuseStep 1687913 = 1265935) B1265935
theorem B1687991 : Blo 1124630 1687991 := bstep (se 1 (by rfl) ⟨1265993, by rfl⟩ : syracuseStep 1687991 = 2531987) B2531987
theorem B1688027 : Blo 1124630 1688027 := bstep (se 1 (by rfl) ⟨1266020, by rfl⟩ : syracuseStep 1688027 = 2532041) B2532041
theorem B13681325 : Blo 1124630 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B4276921 : Blo 1124630 4276921 := bstep (se 2 (by rfl) ⟨1603845, by rfl⟩ : syracuseStep 4276921 = 3207691) B3207691
theorem B9126685 : Blo 1124630 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B1688495 : Blo 1124630 1688495 := bstep (se 1 (by rfl) ⟨1266371, by rfl⟩ : syracuseStep 1688495 = 2532743) B2532743
theorem B1688585 : Blo 1124630 1688585 := bstep (se 2 (by rfl) ⟨633219, by rfl⟩ : syracuseStep 1688585 = 1266439) B1266439
theorem B1688615 : Blo 1124630 1688615 := bstep (se 1 (by rfl) ⟨1266461, by rfl⟩ : syracuseStep 1688615 = 2532923) B2532923
theorem B1426511 : Blo 1124630 1426511 := bstep (se 1 (by rfl) ⟨1069883, by rfl⟩ : syracuseStep 1426511 = 2139767) B2139767
theorem B1688699 : Blo 1124630 1688699 := bstep (se 1 (by rfl) ⟨1266524, by rfl⟩ : syracuseStep 1688699 = 2533049) B2533049
theorem B6407363 : Blo 1124630 6407363 := bstep (se 1 (by rfl) ⟨4805522, by rfl⟩ : syracuseStep 6407363 = 9611045) B9611045
theorem B1688825 : Blo 1124630 1688825 := bstep (se 2 (by rfl) ⟨633309, by rfl⟩ : syracuseStep 1688825 = 1266619) B1266619
theorem B1688927 : Blo 1124630 1688927 := bstep (se 1 (by rfl) ⟨1266695, by rfl⟩ : syracuseStep 1688927 = 2533391) B2533391
theorem B1688939 : Blo 1124630 1688939 := bstep (se 1 (by rfl) ⟨1266704, by rfl⟩ : syracuseStep 1688939 = 2533409) B2533409
theorem B1689167 : Blo 1124630 1689167 := bstep (se 1 (by rfl) ⟨1266875, by rfl⟩ : syracuseStep 1689167 = 2533751) B2533751
theorem B6407819 : Blo 1124630 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B1689287 : Blo 1124630 1689287 := bstep (se 1 (by rfl) ⟨1266965, by rfl⟩ : syracuseStep 1689287 = 2533931) B2533931
theorem B1689449 : Blo 1124630 1689449 := bstep (se 2 (by rfl) ⟨633543, by rfl⟩ : syracuseStep 1689449 = 1267087) B1267087
theorem B1689527 : Blo 1124630 1689527 := bstep (se 1 (by rfl) ⟨1267145, by rfl⟩ : syracuseStep 1689527 = 2534291) B2534291
theorem B1689563 : Blo 1124630 1689563 := bstep (se 1 (by rfl) ⟨1267172, by rfl⟩ : syracuseStep 1689563 = 2534345) B2534345
theorem B4114451 : Blo 1124630 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B1693894679 : Blo 1124630 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B6080779 : Blo 1124630 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B1427807 : Blo 1124630 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B4278653 : Blo 1124630 4278653 := bstep (se 3 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 4278653 = 1604495) B1604495
theorem B1690031 : Blo 1124630 1690031 := bstep (se 1 (by rfl) ⟨1267523, by rfl⟩ : syracuseStep 1690031 = 2535047) B2535047
theorem B1690121 : Blo 1124630 1690121 := bstep (se 2 (by rfl) ⟨633795, by rfl⟩ : syracuseStep 1690121 = 1267591) B1267591
theorem B10832417 : Blo 1124630 10832417 := bstep (se 2 (by rfl) ⟨4062156, by rfl⟩ : syracuseStep 10832417 = 8124313) B8124313
theorem B1690151 : Blo 1124630 1690151 := bstep (se 1 (by rfl) ⟨1267613, by rfl⟩ : syracuseStep 1690151 = 2535227) B2535227
theorem B1690235 : Blo 1124630 1690235 := bstep (se 1 (by rfl) ⟨1267676, by rfl⟩ : syracuseStep 1690235 = 2535353) B2535353
theorem B1690361 : Blo 1124630 1690361 := bstep (se 2 (by rfl) ⟨633885, by rfl⟩ : syracuseStep 1690361 = 1267771) B1267771
theorem B1690463 : Blo 1124630 1690463 := bstep (se 1 (by rfl) ⟨1267847, by rfl⟩ : syracuseStep 1690463 = 2535695) B2535695
theorem B1690475 : Blo 1124630 1690475 := bstep (se 1 (by rfl) ⟨1267856, by rfl⟩ : syracuseStep 1690475 = 2535713) B2535713
theorem B1690703 : Blo 1124630 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B1690823 : Blo 1124630 1690823 := bstep (se 1 (by rfl) ⟨1268117, by rfl⟩ : syracuseStep 1690823 = 2536235) B2536235
theorem B1690985 : Blo 1124630 1690985 := bstep (se 2 (by rfl) ⟨634119, by rfl⟩ : syracuseStep 1690985 = 1268239) B1268239
theorem B1691063 : Blo 1124630 1691063 := bstep (se 1 (by rfl) ⟨1268297, by rfl⟩ : syracuseStep 1691063 = 2536595) B2536595
theorem B1691099 : Blo 1124630 1691099 := bstep (se 1 (by rfl) ⟨1268324, by rfl⟩ : syracuseStep 1691099 = 2536649) B2536649
theorem B3428029 : Blo 1124630 3428029 := bstep (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) B1285511
theorem B1265503 : Blo 1124630 1265503 := bstep (se 1 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 1265503 = 1898255) B1898255
theorem B1691567 : Blo 1124630 1691567 := bstep (se 1 (by rfl) ⟨1268675, by rfl⟩ : syracuseStep 1691567 = 2537351) B2537351
theorem B9129991 : Blo 1124630 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B1691657 : Blo 1124630 1691657 := bstep (se 2 (by rfl) ⟨634371, by rfl⟩ : syracuseStep 1691657 = 1268743) B1268743
theorem B1691687 : Blo 1124630 1691687 := bstep (se 1 (by rfl) ⟨1268765, by rfl⟩ : syracuseStep 1691687 = 2537531) B2537531
theorem B1691771 : Blo 1124630 1691771 := bstep (se 1 (by rfl) ⟨1268828, by rfl⟩ : syracuseStep 1691771 = 2537657) B2537657
theorem B1265863 : Blo 1124630 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1691897 : Blo 1124630 1691897 := bstep (se 2 (by rfl) ⟨634461, by rfl⟩ : syracuseStep 1691897 = 1268923) B1268923
theorem B8540477 : Blo 1124630 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B1691999 : Blo 1124630 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B1692011 : Blo 1124630 1692011 := bstep (se 1 (by rfl) ⟨1269008, by rfl⟩ : syracuseStep 1692011 = 2538017) B2538017
theorem B4280795 : Blo 1124630 4280795 := bstep (se 1 (by rfl) ⟨3210596, by rfl⟩ : syracuseStep 4280795 = 6421193) B6421193
theorem B1692239 : Blo 1124630 1692239 := bstep (se 1 (by rfl) ⟨1269179, by rfl⟩ : syracuseStep 1692239 = 2538359) B2538359
theorem B1692359 : Blo 1124630 1692359 := bstep (se 1 (by rfl) ⟨1269269, by rfl⟩ : syracuseStep 1692359 = 2538539) B2538539
theorem B1692521 : Blo 1124630 1692521 := bstep (se 2 (by rfl) ⟨634695, by rfl⟩ : syracuseStep 1692521 = 1269391) B1269391
theorem B1692599 : Blo 1124630 1692599 := bstep (se 1 (by rfl) ⟨1269449, by rfl⟩ : syracuseStep 1692599 = 2538899) B2538899
theorem B1692635 : Blo 1124630 1692635 := bstep (se 1 (by rfl) ⟨1269476, by rfl⟩ : syracuseStep 1692635 = 2538953) B2538953
theorem B1266727 : Blo 1124630 1266727 := bstep (se 1 (by rfl) ⟨950045, by rfl⟩ : syracuseStep 1266727 = 1900091) B1900091
theorem B14439941 : Blo 1124630 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B4282055 : Blo 1124630 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B6084395 : Blo 1124630 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B2283407 : Blo 1124630 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B6412193 : Blo 1124630 6412193 := bstep (se 2 (by rfl) ⟨2404572, by rfl⟩ : syracuseStep 6412193 = 4809145) B4809145
theorem B36591587 : Blo 1124630 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B6412445 : Blo 1124630 6412445 := bstep (se 3 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 6412445 = 2404667) B2404667
theorem B24107165 : Blo 1124630 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B4282753 : Blo 1124630 4282753 := bstep (se 2 (by rfl) ⟨1606032, by rfl⟩ : syracuseStep 4282753 = 3212065) B3212065
theorem B18537005 : Blo 1124630 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B1268347 : Blo 1124630 1268347 := bstep (se 1 (by rfl) ⟨951260, by rfl⟩ : syracuseStep 1268347 = 1902521) B1902521
theorem B4283027 : Blo 1124630 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B8674121 : Blo 1124630 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B1268815 : Blo 1124630 1268815 := bstep (se 1 (by rfl) ⟨951611, by rfl⟩ : syracuseStep 1268815 = 1903223) B1903223
theorem B13884797 : Blo 1124630 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B1269211 : Blo 1124630 1269211 := bstep (se 1 (by rfl) ⟨951908, by rfl⟩ : syracuseStep 1269211 = 1903817) B1903817
theorem B1269679 : Blo 1124630 1269679 := bstep (se 1 (by rfl) ⟨952259, by rfl⟩ : syracuseStep 1269679 = 1904519) B1904519
theorem B4284683 : Blo 1124630 4284683 := bstep (se 1 (by rfl) ⟨3213512, by rfl⟩ : syracuseStep 4284683 = 6427025) B6427025
theorem B6414653 : Blo 1124630 6414653 := bstep (se 3 (by rfl) ⟨1202747, by rfl⟩ : syracuseStep 6414653 = 2405495) B2405495
theorem B2744705 : Blo 1124630 2744705 := bstep (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) B2058529
theorem B16441805 : Blo 1124630 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B32432663 : Blo 1124630 32432663 := bstep (se 1 (by rfl) ⟨24324497, by rfl⟩ : syracuseStep 32432663 = 48648995) B48648995
theorem B3760763 : Blo 1124630 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B5694137 : Blo 1124630 5694137 := bstep (se 2 (by rfl) ⟨2135301, by rfl⟩ : syracuseStep 5694137 = 4270603) B4270603
theorem B2056951 : Blo 1124630 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B6415361 : Blo 1124630 6415361 := bstep (se 2 (by rfl) ⟨2405760, by rfl⟩ : syracuseStep 6415361 = 4811521) B4811521
theorem B4809881 : Blo 1124630 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B2745953 : Blo 1124630 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B6842045 : Blo 1124630 6842045 := bstep (se 3 (by rfl) ⟨1282883, by rfl⟩ : syracuseStep 6842045 = 2565767) B2565767
theorem B3205277 : Blo 1124630 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B3205595 : Blo 1124630 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B3205619 : Blo 1124630 3205619 := bstep (se 1 (by rfl) ⟨2404214, by rfl⟩ : syracuseStep 3205619 = 4808429) B4808429
theorem B3795983 : Blo 1124630 3795983 := bstep (se 1 (by rfl) ⟨2846987, by rfl⟩ : syracuseStep 3795983 = 5693975) B5693975
theorem B4811795 : Blo 1124630 4811795 := bstep (se 1 (by rfl) ⟨3608846, by rfl⟩ : syracuseStep 4811795 = 7217693) B7217693
theorem B3796577 : Blo 1124630 3796577 := bstep (se 2 (by rfl) ⟨1423716, by rfl⟩ : syracuseStep 3796577 = 2847433) B2847433
theorem B19263095 : Blo 1124630 19263095 := bstep (se 1 (by rfl) ⟨14447321, by rfl⟩ : syracuseStep 19263095 = 28894643) B28894643
theorem B16215875 : Blo 1124630 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B1830763 : Blo 1124630 1830763 := bstep (se 1 (by rfl) ⟨1373072, by rfl⟩ : syracuseStep 1830763 = 2746145) B2746145
theorem B1601545 : Blo 1124630 1601545 := bstep (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) B1201159
theorem B12185777 : Blo 1124630 12185777 := bstep (se 2 (by rfl) ⟨4569666, by rfl⟩ : syracuseStep 12185777 = 9139333) B9139333
theorem B2027849 : Blo 1124630 2027849 := bstep (se 2 (by rfl) ⟨760443, by rfl⟩ : syracuseStep 2027849 = 1520887) B1520887
theorem B2847271 : Blo 1124630 2847271 := bstep (se 1 (by rfl) ⟨2135453, by rfl⟩ : syracuseStep 2847271 = 4270907) B4270907
theorem B32469569 : Blo 1124630 32469569 := bstep (se 2 (by rfl) ⟨12176088, by rfl⟩ : syracuseStep 32469569 = 24352177) B24352177
theorem B2847595 : Blo 1124630 2847595 := bstep (se 1 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 2847595 = 4271393) B4271393
theorem B125039537 : Blo 1124630 125039537 := bstep (se 2 (by rfl) ⟨46889826, by rfl⟩ : syracuseStep 125039537 = 93779653) B93779653
theorem B3798035 : Blo 1124630 3798035 := bstep (se 1 (by rfl) ⟨2848526, by rfl⟩ : syracuseStep 3798035 = 5697053) B5697053
theorem B10286099 : Blo 1124630 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B4060313 : Blo 1124630 4060313 := bstep (se 2 (by rfl) ⟨1522617, by rfl⟩ : syracuseStep 4060313 = 3045235) B3045235
theorem B7206083 : Blo 1124630 7206083 := bstep (se 1 (by rfl) ⟨5404562, by rfl⟩ : syracuseStep 7206083 = 10809125) B10809125
theorem B6419735 : Blo 1124630 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B3798359 : Blo 1124630 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B1897823 : Blo 1124630 1897823 := bstep (se 1 (by rfl) ⟨1423367, by rfl⟩ : syracuseStep 1897823 = 2846735) B2846735
theorem B2848243 : Blo 1124630 2848243 := bstep (se 1 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 2848243 = 4272365) B4272365
theorem B19494599 : Blo 1124630 19494599 := bstep (se 1 (by rfl) ⟨14620949, by rfl⟩ : syracuseStep 19494599 = 29241899) B29241899
theorem B6420167 : Blo 1124630 6420167 := bstep (se 1 (by rfl) ⟨4815125, by rfl⟩ : syracuseStep 6420167 = 9630251) B9630251
theorem B5699321 : Blo 1124630 5699321 := bstep (se 2 (by rfl) ⟨2137245, by rfl⟩ : syracuseStep 5699321 = 4274491) B4274491
theorem B1898383 : Blo 1124630 1898383 := bstep (se 1 (by rfl) ⟨1423787, by rfl⟩ : syracuseStep 1898383 = 2847575) B2847575
theorem B17201251 : Blo 1124630 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B2029897 : Blo 1124630 2029897 := bstep (se 2 (by rfl) ⟨761211, by rfl⟩ : syracuseStep 2029897 = 1522423) B1522423
theorem B5699969 : Blo 1124630 5699969 := bstep (se 2 (by rfl) ⟨2137488, by rfl⟩ : syracuseStep 5699969 = 4274977) B4274977
theorem B3799439 : Blo 1124630 3799439 := bstep (se 1 (by rfl) ⟨2849579, by rfl⟩ : syracuseStep 3799439 = 5699159) B5699159
theorem B1899065 : Blo 1124630 1899065 := bstep (se 2 (by rfl) ⟨712149, by rfl⟩ : syracuseStep 1899065 = 1424299) B1424299
theorem B2849377 : Blo 1124630 2849377 := bstep (se 2 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 2849377 = 2137033) B2137033
theorem B3603143 : Blo 1124630 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B3799763 : Blo 1124630 3799763 := bstep (se 1 (by rfl) ⟨2849822, by rfl⟩ : syracuseStep 3799763 = 5699645) B5699645
theorem B5700779 : Blo 1124630 5700779 := bstep (se 1 (by rfl) ⟨4275584, by rfl⟩ : syracuseStep 5700779 = 8551169) B8551169
theorem B14613677 : Blo 1124630 14613677 := bstep (se 3 (by rfl) ⟨2740064, by rfl⟩ : syracuseStep 14613677 = 5480129) B5480129
theorem B2030791 : Blo 1124630 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B1899767 : Blo 1124630 1899767 := bstep (se 1 (by rfl) ⟨1424825, by rfl⟩ : syracuseStep 1899767 = 2849651) B2849651
theorem B6585623 : Blo 1124630 6585623 := bstep (se 1 (by rfl) ⟨4939217, by rfl⟩ : syracuseStep 6585623 = 9878435) B9878435
theorem B4816253 : Blo 1124630 4816253 := bstep (se 3 (by rfl) ⟨903047, by rfl⟩ : syracuseStep 4816253 = 1806095) B1806095
theorem B2850329 : Blo 1124630 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B1900111 : Blo 1124630 1900111 := bstep (se 1 (by rfl) ⟨1425083, by rfl⟩ : syracuseStep 1900111 = 2850167) B2850167
theorem B5701265 : Blo 1124630 5701265 := bstep (se 2 (by rfl) ⟨2137974, by rfl⟩ : syracuseStep 5701265 = 4275949) B4275949
theorem B36601573 : Blo 1124630 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B12353261 : Blo 1124630 12353261 := bstep (se 3 (by rfl) ⟨2316236, by rfl⟩ : syracuseStep 12353261 = 4632473) B4632473
theorem B7208747 : Blo 1124630 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B3604297 : Blo 1124630 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B1900361 : Blo 1124630 1900361 := bstep (se 2 (by rfl) ⟨712635, by rfl⟩ : syracuseStep 1900361 = 1425271) B1425271
theorem B3800951 : Blo 1124630 3800951 := bstep (se 1 (by rfl) ⟨2850713, by rfl⟩ : syracuseStep 3800951 = 5701427) B5701427
theorem B3801113 : Blo 1124630 3801113 := bstep (se 2 (by rfl) ⟨1425417, by rfl⟩ : syracuseStep 3801113 = 2850835) B2850835
theorem B1901279 : Blo 1124630 1901279 := bstep (se 1 (by rfl) ⟨1425959, by rfl⟩ : syracuseStep 1901279 = 2851919) B2851919
theorem B3212111 : Blo 1124630 3212111 := bstep (se 1 (by rfl) ⟨2409083, by rfl⟩ : syracuseStep 3212111 = 4818167) B4818167
theorem B5407597 : Blo 1124630 5407597 := bstep (se 3 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 5407597 = 2027849) B2027849
theorem B5702561 : Blo 1124630 5702561 := bstep (se 2 (by rfl) ⟨2138460, by rfl⟩ : syracuseStep 5702561 = 4276921) B4276921
theorem B4817825 : Blo 1124630 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B3474407 : Blo 1124630 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B3605629 : Blo 1124630 3605629 := bstep (se 3 (by rfl) ⟨676055, by rfl⟩ : syracuseStep 3605629 = 1352111) B1352111
theorem B1901711 : Blo 1124630 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B3802355 : Blo 1124630 3802355 := bstep (se 1 (by rfl) ⟨2851766, by rfl⟩ : syracuseStep 3802355 = 5703533) B5703533
theorem B3802463 : Blo 1124630 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B1901947 : Blo 1124630 1901947 := bstep (se 1 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 1901947 = 2852921) B2852921
theorem B2852435 : Blo 1124630 2852435 := bstep (se 1 (by rfl) ⟨2139326, by rfl⟩ : syracuseStep 2852435 = 4278653) B4278653
theorem B10028701 : Blo 1124630 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B3213751 : Blo 1124630 3213751 := bstep (se 1 (by rfl) ⟨2410313, by rfl⟩ : syracuseStep 3213751 = 4820627) B4820627
theorem B1903439 : Blo 1124630 1903439 := bstep (se 1 (by rfl) ⟨1427579, by rfl⟩ : syracuseStep 1903439 = 2855159) B2855159
theorem B3804029 : Blo 1124630 3804029 := bstep (se 3 (by rfl) ⟨713255, by rfl⟩ : syracuseStep 3804029 = 1426511) B1426511
theorem B2853863 : Blo 1124630 2853863 := bstep (se 1 (by rfl) ⟨2140397, by rfl⟩ : syracuseStep 2853863 = 4280795) B4280795
theorem B3804299 : Blo 1124630 3804299 := bstep (se 1 (by rfl) ⟨2853224, by rfl⟩ : syracuseStep 3804299 = 5706449) B5706449
theorem B5704991 : Blo 1124630 5704991 := bstep (se 1 (by rfl) ⟨4278743, by rfl⟩ : syracuseStep 5704991 = 8557487) B8557487
theorem B4820285 : Blo 1124630 4820285 := bstep (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) B1807607
theorem B2854561 : Blo 1124630 2854561 := bstep (se 2 (by rfl) ⟨1070460, by rfl⟩ : syracuseStep 2854561 = 2140921) B2140921
theorem B17370787 : Blo 1124630 17370787 := bstep (se 1 (by rfl) ⟨13028090, by rfl⟩ : syracuseStep 17370787 = 26056181) B26056181
theorem B9899819 : Blo 1124630 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B7212847 : Blo 1124630 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B2854703 : Blo 1124630 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B1904431 : Blo 1124630 1904431 := bstep (se 1 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 1904431 = 2856647) B2856647
theorem B19271843 : Blo 1124630 19271843 := bstep (se 1 (by rfl) ⟨14453882, by rfl⟩ : syracuseStep 19271843 = 28907765) B28907765
theorem B12358003 : Blo 1124630 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B2855351 : Blo 1124630 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B3805919 : Blo 1124630 3805919 := bstep (se 1 (by rfl) ⟨2854439, by rfl⟩ : syracuseStep 3805919 = 5708879) B5708879
theorem B14423129 : Blo 1124630 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B3806351 : Blo 1124630 3806351 := bstep (se 1 (by rfl) ⟨2854763, by rfl⟩ : syracuseStep 3806351 = 5709527) B5709527
theorem B2135393 : Blo 1124630 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B18748865 : Blo 1124630 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B2856455 : Blo 1124630 2856455 := bstep (se 1 (by rfl) ⟨2142341, by rfl⟩ : syracuseStep 2856455 = 4284683) B4284683
theorem B2856505 : Blo 1124630 2856505 := bstep (se 2 (by rfl) ⟨1071189, by rfl⟩ : syracuseStep 2856505 = 2142379) B2142379
theorem B5707421 : Blo 1124630 5707421 := bstep (se 3 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 5707421 = 2140283) B2140283
theorem B6166201 : Blo 1124630 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B2856809 : Blo 1124630 2856809 := bstep (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) B2142607
theorem B3807485 : Blo 1124630 3807485 := bstep (se 3 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 3807485 = 1427807) B1427807
theorem B4561363 : Blo 1124630 4561363 := bstep (se 1 (by rfl) ⟨3421022, by rfl⟩ : syracuseStep 4561363 = 6842045) B6842045
theorem B3611243 : Blo 1124630 3611243 := bstep (se 1 (by rfl) ⟨2708432, by rfl⟩ : syracuseStep 3611243 = 5416865) B5416865
theorem B5773963 : Blo 1124630 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B2136851 : Blo 1124630 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B5708717 : Blo 1124630 5708717 := bstep (se 3 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 5708717 = 2140769) B2140769
theorem B2137079 : Blo 1124630 2137079 := bstep (se 1 (by rfl) ⟨1602809, by rfl⟩ : syracuseStep 2137079 = 3205619) B3205619
theorem B3808295 : Blo 1124630 3808295 := bstep (se 1 (by rfl) ⟨2856221, by rfl⟩ : syracuseStep 3808295 = 5712443) B5712443
theorem B9608381 : Blo 1124630 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B3087575 : Blo 1124630 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B2530655 : Blo 1124630 2530655 := bstep (se 1 (by rfl) ⟨1897991, by rfl⟩ : syracuseStep 2530655 = 3795983) B3795983
theorem B3808727 : Blo 1124630 3808727 := bstep (se 1 (by rfl) ⟨2856545, by rfl⟩ : syracuseStep 3808727 = 5713091) B5713091
theorem B64953899 : Blo 1124630 64953899 := bstep (se 1 (by rfl) ⟨48715424, by rfl⟩ : syracuseStep 64953899 = 97430849) B97430849
theorem B2531051 : Blo 1124630 2531051 := bstep (se 1 (by rfl) ⟨1898288, by rfl⟩ : syracuseStep 2531051 = 3796577) B3796577
theorem B131768117 : Blo 1124630 131768117 := bstep (se 5 (by rfl) ⟨6176630, by rfl⟩ : syracuseStep 131768117 = 12353261) B12353261
theorem B2531177 : Blo 1124630 2531177 := bstep (se 2 (by rfl) ⟨949191, by rfl⟩ : syracuseStep 2531177 = 1898383) B1898383
theorem B3612883 : Blo 1124630 3612883 := bstep (se 1 (by rfl) ⟨2709662, by rfl⟩ : syracuseStep 3612883 = 5419325) B5419325
theorem B5710337 : Blo 1124630 5710337 := bstep (se 2 (by rfl) ⟨2141376, by rfl⟩ : syracuseStep 5710337 = 4282753) B4282753
theorem B2532023 : Blo 1124630 2532023 := bstep (se 1 (by rfl) ⟨1899017, by rfl⟩ : syracuseStep 2532023 = 3798035) B3798035
theorem B6857399 : Blo 1124630 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B2532239 : Blo 1124630 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B8463323 : Blo 1124630 8463323 := bstep (se 1 (by rfl) ⟨6347492, by rfl⟩ : syracuseStep 8463323 = 12694985) B12694985
theorem B5710823 : Blo 1124630 5710823 := bstep (se 1 (by rfl) ⟨4283117, by rfl⟩ : syracuseStep 5710823 = 8566235) B8566235
theorem B7218179 : Blo 1124630 7218179 := bstep (se 1 (by rfl) ⟨5413634, by rfl⟩ : syracuseStep 7218179 = 10827269) B10827269
theorem B5711147 : Blo 1124630 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B19506673 : Blo 1124630 19506673 := bstep (se 2 (by rfl) ⟨7315002, by rfl⟩ : syracuseStep 19506673 = 14630005) B14630005
theorem B3614215 : Blo 1124630 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B2532959 : Blo 1124630 2532959 := bstep (se 1 (by rfl) ⟨1899719, by rfl⟩ : syracuseStep 2532959 = 3799439) B3799439
theorem B13903649 : Blo 1124630 13903649 := bstep (se 2 (by rfl) ⟨5213868, by rfl⟩ : syracuseStep 13903649 = 10427737) B10427737
theorem B2533175 : Blo 1124630 2533175 := bstep (se 1 (by rfl) ⟨1899881, by rfl⟩ : syracuseStep 2533175 = 3799763) B3799763
theorem B12855185 : Blo 1124630 12855185 := bstep (se 2 (by rfl) ⟨4820694, by rfl⟩ : syracuseStep 12855185 = 9641389) B9641389
theorem B7219151 : Blo 1124630 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B2533481 : Blo 1124630 2533481 := bstep (se 2 (by rfl) ⟨950055, by rfl⟩ : syracuseStep 2533481 = 1900111) B1900111
theorem B9742451 : Blo 1124630 9742451 := bstep (se 1 (by rfl) ⟨7306838, by rfl⟩ : syracuseStep 9742451 = 14613677) B14613677
theorem B5712119 : Blo 1124630 5712119 := bstep (se 1 (by rfl) ⟨4284089, by rfl⟩ : syracuseStep 5712119 = 8568179) B8568179
theorem B1124639 : Blo 1124630 1124639 := bstep (se 1 (by rfl) ⟨843479, by rfl⟩ : syracuseStep 1124639 = 1686959) B1686959
theorem B48802097 : Blo 1124630 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B1124699 : Blo 1124630 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B1124719 : Blo 1124630 1124719 := bstep (se 1 (by rfl) ⟨843539, by rfl⟩ : syracuseStep 1124719 = 1687079) B1687079
theorem B1124775 : Blo 1124630 1124775 := bstep (se 1 (by rfl) ⟨843581, by rfl⟩ : syracuseStep 1124775 = 1687163) B1687163
theorem B1124859 : Blo 1124630 1124859 := bstep (se 1 (by rfl) ⟨843644, by rfl⟩ : syracuseStep 1124859 = 1687289) B1687289
theorem B4336123 : Blo 1124630 4336123 := bstep (se 1 (by rfl) ⟨3252092, by rfl⟩ : syracuseStep 4336123 = 6504185) B6504185
theorem B1124927 : Blo 1124630 1124927 := bstep (se 1 (by rfl) ⟨843695, by rfl⟩ : syracuseStep 1124927 = 1687391) B1687391
theorem B1124935 : Blo 1124630 1124935 := bstep (se 1 (by rfl) ⟨843701, by rfl⟩ : syracuseStep 1124935 = 1687403) B1687403
theorem B2533967 : Blo 1124630 2533967 := bstep (se 1 (by rfl) ⟨1900475, by rfl⟩ : syracuseStep 2533967 = 3800951) B3800951
theorem B5712605 : Blo 1124630 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B1125087 : Blo 1124630 1125087 := bstep (se 1 (by rfl) ⟨843815, by rfl⟩ : syracuseStep 1125087 = 1687631) B1687631
theorem B2534111 : Blo 1124630 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B1125167 : Blo 1124630 1125167 := bstep (se 1 (by rfl) ⟨843875, by rfl⟩ : syracuseStep 1125167 = 1687751) B1687751
theorem B1125275 : Blo 1124630 1125275 := bstep (se 1 (by rfl) ⟨843956, by rfl⟩ : syracuseStep 1125275 = 1687913) B1687913
theorem B1125327 : Blo 1124630 1125327 := bstep (se 1 (by rfl) ⟨843995, by rfl⟩ : syracuseStep 1125327 = 1687991) B1687991
theorem B2534363 : Blo 1124630 2534363 := bstep (se 1 (by rfl) ⟨1900772, by rfl⟩ : syracuseStep 2534363 = 3801545) B3801545
theorem B1125351 : Blo 1124630 1125351 := bstep (se 1 (by rfl) ⟨844013, by rfl⟩ : syracuseStep 1125351 = 1688027) B1688027
theorem B9120883 : Blo 1124630 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2534543 : Blo 1124630 2534543 := bstep (se 1 (by rfl) ⟨1900907, by rfl⟩ : syracuseStep 2534543 = 3801815) B3801815
theorem B2534633 : Blo 1124630 2534633 := bstep (se 2 (by rfl) ⟨950487, by rfl⟩ : syracuseStep 2534633 = 1900975) B1900975
theorem B1125663 : Blo 1124630 1125663 := bstep (se 1 (by rfl) ⟨844247, by rfl⟩ : syracuseStep 1125663 = 1688495) B1688495
theorem B2534687 : Blo 1124630 2534687 := bstep (se 1 (by rfl) ⟨1901015, by rfl⟩ : syracuseStep 2534687 = 3802031) B3802031
theorem B1125723 : Blo 1124630 1125723 := bstep (se 1 (by rfl) ⟨844292, by rfl⟩ : syracuseStep 1125723 = 1688585) B1688585
theorem B1125743 : Blo 1124630 1125743 := bstep (se 1 (by rfl) ⟨844307, by rfl⟩ : syracuseStep 1125743 = 1688615) B1688615
theorem B1125799 : Blo 1124630 1125799 := bstep (se 1 (by rfl) ⟨844349, by rfl⟩ : syracuseStep 1125799 = 1688699) B1688699
theorem B4271575 : Blo 1124630 4271575 := bstep (se 1 (by rfl) ⟨3203681, by rfl⟩ : syracuseStep 4271575 = 6407363) B6407363
theorem B1125883 : Blo 1124630 1125883 := bstep (se 1 (by rfl) ⟨844412, by rfl⟩ : syracuseStep 1125883 = 1688825) B1688825
theorem B2403847 : Blo 1124630 2403847 := bstep (se 1 (by rfl) ⟨1802885, by rfl⟩ : syracuseStep 2403847 = 3605771) B3605771
theorem B1125951 : Blo 1124630 1125951 := bstep (se 1 (by rfl) ⟨844463, by rfl⟩ : syracuseStep 1125951 = 1688927) B1688927
theorem B1125959 : Blo 1124630 1125959 := bstep (se 1 (by rfl) ⟨844469, by rfl⟩ : syracuseStep 1125959 = 1688939) B1688939
theorem B2403923 : Blo 1124630 2403923 := bstep (se 1 (by rfl) ⟨1802942, by rfl⟩ : syracuseStep 2403923 = 3605885) B3605885
theorem B12168913 : Blo 1124630 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B1126111 : Blo 1124630 1126111 := bstep (se 1 (by rfl) ⟨844583, by rfl⟩ : syracuseStep 1126111 = 1689167) B1689167
theorem B4271879 : Blo 1124630 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B2535209 : Blo 1124630 2535209 := bstep (se 2 (by rfl) ⟨950703, by rfl⟩ : syracuseStep 2535209 = 1901407) B1901407
theorem B1126191 : Blo 1124630 1126191 := bstep (se 1 (by rfl) ⟨844643, by rfl⟩ : syracuseStep 1126191 = 1689287) B1689287
theorem B1126299 : Blo 1124630 1126299 := bstep (se 1 (by rfl) ⟨844724, by rfl⟩ : syracuseStep 1126299 = 1689449) B1689449
theorem B1126351 : Blo 1124630 1126351 := bstep (se 1 (by rfl) ⟨844763, by rfl⟩ : syracuseStep 1126351 = 1689527) B1689527
theorem B1126375 : Blo 1124630 1126375 := bstep (se 1 (by rfl) ⟨844781, by rfl⟩ : syracuseStep 1126375 = 1689563) B1689563
theorem B1129263119 : Blo 1124630 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B1126687 : Blo 1124630 1126687 := bstep (se 1 (by rfl) ⟨845015, by rfl⟩ : syracuseStep 1126687 = 1690031) B1690031
theorem B1126747 : Blo 1124630 1126747 := bstep (se 1 (by rfl) ⟨845060, by rfl⟩ : syracuseStep 1126747 = 1690121) B1690121
theorem B7221611 : Blo 1124630 7221611 := bstep (se 1 (by rfl) ⟨5416208, by rfl⟩ : syracuseStep 7221611 = 10832417) B10832417
theorem B1126767 : Blo 1124630 1126767 := bstep (se 1 (by rfl) ⟨845075, by rfl⟩ : syracuseStep 1126767 = 1690151) B1690151
theorem B1126823 : Blo 1124630 1126823 := bstep (se 1 (by rfl) ⟨845117, by rfl⟩ : syracuseStep 1126823 = 1690235) B1690235
theorem B1126907 : Blo 1124630 1126907 := bstep (se 1 (by rfl) ⟨845180, by rfl⟩ : syracuseStep 1126907 = 1690361) B1690361
theorem B1126975 : Blo 1124630 1126975 := bstep (se 1 (by rfl) ⟨845231, by rfl⟩ : syracuseStep 1126975 = 1690463) B1690463
theorem B1126983 : Blo 1124630 1126983 := bstep (se 1 (by rfl) ⟨845237, by rfl⟩ : syracuseStep 1126983 = 1690475) B1690475
theorem B1127135 : Blo 1124630 1127135 := bstep (se 1 (by rfl) ⟨845351, by rfl⟩ : syracuseStep 1127135 = 1690703) B1690703
theorem B1127215 : Blo 1124630 1127215 := bstep (se 1 (by rfl) ⟨845411, by rfl⟩ : syracuseStep 1127215 = 1690823) B1690823
theorem B2536271 : Blo 1124630 2536271 := bstep (se 1 (by rfl) ⟨1902203, by rfl⟩ : syracuseStep 2536271 = 3804407) B3804407
theorem B1127323 : Blo 1124630 1127323 := bstep (se 1 (by rfl) ⟨845492, by rfl⟩ : syracuseStep 1127323 = 1690985) B1690985
theorem B1127375 : Blo 1124630 1127375 := bstep (se 1 (by rfl) ⟨845531, by rfl⟩ : syracuseStep 1127375 = 1691063) B1691063
theorem B2405351 : Blo 1124630 2405351 := bstep (se 1 (by rfl) ⟨1804013, by rfl⟩ : syracuseStep 2405351 = 3608027) B3608027
theorem B1127399 : Blo 1124630 1127399 := bstep (se 1 (by rfl) ⟨845549, by rfl⟩ : syracuseStep 1127399 = 1691099) B1691099
theorem B2536487 : Blo 1124630 2536487 := bstep (se 1 (by rfl) ⟨1902365, by rfl⟩ : syracuseStep 2536487 = 3804731) B3804731
theorem B2536667 : Blo 1124630 2536667 := bstep (se 1 (by rfl) ⟨1902500, by rfl⟩ : syracuseStep 2536667 = 3805001) B3805001
theorem B12170519 : Blo 1124630 12170519 := bstep (se 1 (by rfl) ⟨9127889, by rfl⟩ : syracuseStep 12170519 = 18255779) B18255779
theorem B1127711 : Blo 1124630 1127711 := bstep (se 1 (by rfl) ⟨845783, by rfl⟩ : syracuseStep 1127711 = 1691567) B1691567
theorem B1127771 : Blo 1124630 1127771 := bstep (se 1 (by rfl) ⟨845828, by rfl⟩ : syracuseStep 1127771 = 1691657) B1691657
theorem B1127791 : Blo 1124630 1127791 := bstep (se 1 (by rfl) ⟨845843, by rfl⟩ : syracuseStep 1127791 = 1691687) B1691687
theorem B2536865 : Blo 1124630 2536865 := bstep (se 2 (by rfl) ⟨951324, by rfl⟩ : syracuseStep 2536865 = 1902649) B1902649
theorem B1127847 : Blo 1124630 1127847 := bstep (se 1 (by rfl) ⟨845885, by rfl⟩ : syracuseStep 1127847 = 1691771) B1691771
theorem B1127931 : Blo 1124630 1127931 := bstep (se 1 (by rfl) ⟨845948, by rfl⟩ : syracuseStep 1127931 = 1691897) B1691897
theorem B1127999 : Blo 1124630 1127999 := bstep (se 1 (by rfl) ⟨845999, by rfl⟩ : syracuseStep 1127999 = 1691999) B1691999
theorem B1128007 : Blo 1124630 1128007 := bstep (se 1 (by rfl) ⟨846005, by rfl⟩ : syracuseStep 1128007 = 1692011) B1692011
theorem B8107705 : Blo 1124630 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B1128159 : Blo 1124630 1128159 := bstep (se 1 (by rfl) ⟨846119, by rfl⟩ : syracuseStep 1128159 = 1692239) B1692239
theorem B1128239 : Blo 1124630 1128239 := bstep (se 1 (by rfl) ⟨846179, by rfl⟩ : syracuseStep 1128239 = 1692359) B1692359
theorem B702199637 : Blo 1124630 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B1128347 : Blo 1124630 1128347 := bstep (se 1 (by rfl) ⟨846260, by rfl⟩ : syracuseStep 1128347 = 1692521) B1692521
theorem B2537423 : Blo 1124630 2537423 := bstep (se 1 (by rfl) ⟨1903067, by rfl⟩ : syracuseStep 2537423 = 3806135) B3806135
theorem B1128399 : Blo 1124630 1128399 := bstep (se 1 (by rfl) ⟨846299, by rfl⟩ : syracuseStep 1128399 = 1692599) B1692599
theorem B1128423 : Blo 1124630 1128423 := bstep (se 1 (by rfl) ⟨846317, by rfl⟩ : syracuseStep 1128423 = 1692635) B1692635
theorem B2537801 : Blo 1124630 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B2537819 : Blo 1124630 2537819 := bstep (se 1 (by rfl) ⟨1903364, by rfl⟩ : syracuseStep 2537819 = 3806729) B3806729
theorem B5487031 : Blo 1124630 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B2406991 : Blo 1124630 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B1522271 : Blo 1124630 1522271 := bstep (se 1 (by rfl) ⟨1141703, by rfl⟩ : syracuseStep 1522271 = 2283407) B2283407
theorem B4274795 : Blo 1124630 4274795 := bstep (se 1 (by rfl) ⟨3206096, by rfl⟩ : syracuseStep 4274795 = 6412193) B6412193
theorem B2407033 : Blo 1124630 2407033 := bstep (se 2 (by rfl) ⟨902637, by rfl⟩ : syracuseStep 2407033 = 1805275) B1805275
theorem B24394391 : Blo 1124630 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B4274963 : Blo 1124630 4274963 := bstep (se 1 (by rfl) ⟨3206222, by rfl⟩ : syracuseStep 4274963 = 6412445) B6412445
theorem B16071443 : Blo 1124630 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B2538395 : Blo 1124630 2538395 := bstep (se 1 (by rfl) ⟨1903796, by rfl⟩ : syracuseStep 2538395 = 3807593) B3807593
theorem B2538593 : Blo 1124630 2538593 := bstep (se 2 (by rfl) ⟨951972, by rfl⟩ : syracuseStep 2538593 = 1903945) B1903945
theorem B5782747 : Blo 1124630 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B2538791 : Blo 1124630 2538791 := bstep (se 1 (by rfl) ⟨1904093, by rfl⟩ : syracuseStep 2538791 = 3808187) B3808187
theorem B1686983 : Blo 1124630 1686983 := bstep (se 1 (by rfl) ⟨1265237, by rfl⟩ : syracuseStep 1686983 = 2530475) B2530475
theorem B1424891 : Blo 1124630 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B4570705 : Blo 1124630 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B9256531 : Blo 1124630 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B2539169 : Blo 1124630 2539169 := bstep (se 2 (by rfl) ⟨952188, by rfl⟩ : syracuseStep 2539169 = 1904377) B1904377
theorem B1687337 : Blo 1124630 1687337 := bstep (se 2 (by rfl) ⟨632751, by rfl⟩ : syracuseStep 1687337 = 1265503) B1265503
theorem B1687343 : Blo 1124630 1687343 := bstep (se 1 (by rfl) ⟨1265507, by rfl⟩ : syracuseStep 1687343 = 2531015) B2531015
theorem B2441017 : Blo 1124630 2441017 := bstep (se 2 (by rfl) ⟨915381, by rfl⟩ : syracuseStep 2441017 = 1830763) B1830763
theorem B2408297 : Blo 1124630 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B12173321 : Blo 1124630 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B4276435 : Blo 1124630 4276435 := bstep (se 1 (by rfl) ⟨3207326, by rfl⟩ : syracuseStep 4276435 = 6414653) B6414653
theorem B1687817 : Blo 1124630 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B10961203 : Blo 1124630 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B1687919 : Blo 1124630 1687919 := bstep (se 1 (by rfl) ⟨1265939, by rfl⟩ : syracuseStep 1687919 = 2531879) B2531879
theorem B2408879 : Blo 1124630 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B1425863 : Blo 1124630 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B1688135 : Blo 1124630 1688135 := bstep (se 1 (by rfl) ⟨1266101, by rfl⟩ : syracuseStep 1688135 = 2532203) B2532203
theorem B1426015 : Blo 1124630 1426015 := bstep (se 1 (by rfl) ⟨1069511, by rfl⟩ : syracuseStep 1426015 = 2139023) B2139023
theorem B1688171 : Blo 1124630 1688171 := bstep (se 1 (by rfl) ⟨1266128, by rfl⟩ : syracuseStep 1688171 = 2532257) B2532257
theorem B8110763 : Blo 1124630 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B4276907 : Blo 1124630 4276907 := bstep (se 1 (by rfl) ⟨3207680, by rfl⟩ : syracuseStep 4276907 = 6415361) B6415361
theorem B19776307 : Blo 1124630 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B1688399 : Blo 1124630 1688399 := bstep (se 1 (by rfl) ⟨1266299, by rfl⟩ : syracuseStep 1688399 = 2532599) B2532599
theorem B1688795 : Blo 1124630 1688795 := bstep (se 1 (by rfl) ⟨1266596, by rfl⟩ : syracuseStep 1688795 = 2533193) B2533193
theorem B3851497 : Blo 1124630 3851497 := bstep (se 2 (by rfl) ⟨1444311, by rfl⟩ : syracuseStep 3851497 = 2888623) B2888623
theorem B2409767 : Blo 1124630 2409767 := bstep (se 1 (by rfl) ⟨1807325, by rfl⟩ : syracuseStep 2409767 = 3614651) B3614651
theorem B1688969 : Blo 1124630 1688969 := bstep (se 2 (by rfl) ⟨633363, by rfl⟩ : syracuseStep 1688969 = 1266727) B1266727
theorem B2410067 : Blo 1124630 2410067 := bstep (se 1 (by rfl) ⟨1807550, by rfl⟩ : syracuseStep 2410067 = 3615101) B3615101
theorem B1689323 : Blo 1124630 1689323 := bstep (se 1 (by rfl) ⟨1266992, by rfl⟩ : syracuseStep 1689323 = 2533985) B2533985
theorem B1689551 : Blo 1124630 1689551 := bstep (se 1 (by rfl) ⟨1267163, by rfl⟩ : syracuseStep 1689551 = 2534327) B2534327
theorem B1689947 : Blo 1124630 1689947 := bstep (se 1 (by rfl) ⟨1267460, by rfl⟩ : syracuseStep 1689947 = 2534921) B2534921
theorem B1690175 : Blo 1124630 1690175 := bstep (se 1 (by rfl) ⟨1267631, by rfl⟩ : syracuseStep 1690175 = 2535263) B2535263
theorem B1690295 : Blo 1124630 1690295 := bstep (se 1 (by rfl) ⟨1267721, by rfl⟩ : syracuseStep 1690295 = 2535443) B2535443
theorem B1690523 : Blo 1124630 1690523 := bstep (se 1 (by rfl) ⟨1267892, by rfl⟩ : syracuseStep 1690523 = 2535785) B2535785
theorem B48810923 : Blo 1124630 48810923 := bstep (se 1 (by rfl) ⟨36608192, by rfl⟩ : syracuseStep 48810923 = 73216385) B73216385
theorem B21646379 : Blo 1124630 21646379 := bstep (se 1 (by rfl) ⟨16234784, by rfl⟩ : syracuseStep 21646379 = 32469569) B32469569
theorem B2706529 : Blo 1124630 2706529 := bstep (se 2 (by rfl) ⟨1014948, by rfl⟩ : syracuseStep 2706529 = 2029897) B2029897
theorem B1690919 : Blo 1124630 1690919 := bstep (se 1 (by rfl) ⟨1268189, by rfl⟩ : syracuseStep 1690919 = 2536379) B2536379
theorem B9620855 : Blo 1124630 9620855 := bstep (se 1 (by rfl) ⟨7215641, by rfl⟩ : syracuseStep 9620855 = 14431283) B14431283
theorem B1691003 : Blo 1124630 1691003 := bstep (se 1 (by rfl) ⟨1268252, by rfl⟩ : syracuseStep 1691003 = 2536505) B2536505
theorem B2706875 : Blo 1124630 2706875 := bstep (se 1 (by rfl) ⟨2030156, by rfl⟩ : syracuseStep 2706875 = 4060313) B4060313
theorem B4804055 : Blo 1124630 4804055 := bstep (se 1 (by rfl) ⟨3603041, by rfl⟩ : syracuseStep 4804055 = 7206083) B7206083
theorem B1691129 : Blo 1124630 1691129 := bstep (se 2 (by rfl) ⟨634173, by rfl⟩ : syracuseStep 1691129 = 1268347) B1268347
theorem B4279823 : Blo 1124630 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B1265215 : Blo 1124630 1265215 := bstep (se 1 (by rfl) ⟨948911, by rfl⟩ : syracuseStep 1265215 = 1897823) B1897823
theorem B1691231 : Blo 1124630 1691231 := bstep (se 1 (by rfl) ⟨1268423, by rfl⟩ : syracuseStep 1691231 = 2536847) B2536847
theorem B4280111 : Blo 1124630 4280111 := bstep (se 1 (by rfl) ⟨3210083, by rfl⟩ : syracuseStep 4280111 = 6420167) B6420167
theorem B1691447 : Blo 1124630 1691447 := bstep (se 1 (by rfl) ⟨1268585, by rfl⟩ : syracuseStep 1691447 = 2537171) B2537171
theorem B5132105 : Blo 1124630 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B1691753 : Blo 1124630 1691753 := bstep (se 2 (by rfl) ⟨634407, by rfl⟩ : syracuseStep 1691753 = 1268815) B1268815
theorem B2707721 : Blo 1124630 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B1266043 : Blo 1124630 1266043 := bstep (se 1 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 1266043 = 1899065) B1899065
theorem B1692071 : Blo 1124630 1692071 := bstep (se 1 (by rfl) ⟨1269053, by rfl⟩ : syracuseStep 1692071 = 2538107) B2538107
theorem B2281979 : Blo 1124630 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B1692155 : Blo 1124630 1692155 := bstep (se 1 (by rfl) ⟨1269116, by rfl⟩ : syracuseStep 1692155 = 2538233) B2538233
theorem B1692281 : Blo 1124630 1692281 := bstep (se 2 (by rfl) ⟨634605, by rfl⟩ : syracuseStep 1692281 = 1269211) B1269211
theorem B1692335 : Blo 1124630 1692335 := bstep (se 1 (by rfl) ⟨1269251, by rfl⟩ : syracuseStep 1692335 = 2538503) B2538503
theorem B1692383 : Blo 1124630 1692383 := bstep (se 1 (by rfl) ⟨1269287, by rfl⟩ : syracuseStep 1692383 = 2538575) B2538575
theorem B1266511 : Blo 1124630 1266511 := bstep (se 1 (by rfl) ⟨949883, by rfl⟩ : syracuseStep 1266511 = 1899767) B1899767
theorem B6083423 : Blo 1124630 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B1692647 : Blo 1124630 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B4805729 : Blo 1124630 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B4805831 : Blo 1124630 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B10278103 : Blo 1124630 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B1266907 : Blo 1124630 1266907 := bstep (se 1 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 1266907 = 1900361) B1900361
theorem B1692905 : Blo 1124630 1692905 := bstep (se 2 (by rfl) ⟨634839, by rfl⟩ : syracuseStep 1692905 = 1269679) B1269679
theorem B7230815 : Blo 1124630 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B3855755 : Blo 1124630 3855755 := bstep (se 1 (by rfl) ⟨2891816, by rfl⟩ : syracuseStep 3855755 = 5783633) B5783633
theorem B1267195 : Blo 1124630 1267195 := bstep (se 1 (by rfl) ⟨950396, by rfl⟩ : syracuseStep 1267195 = 1900793) B1900793
theorem B1267375 : Blo 1124630 1267375 := bstep (se 1 (by rfl) ⟨950531, by rfl⟩ : syracuseStep 1267375 = 1901063) B1901063
theorem B1267663 : Blo 1124630 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B24401999 : Blo 1124630 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B5134583 : Blo 1124630 5134583 := bstep (se 1 (by rfl) ⟨3850937, by rfl⟩ : syracuseStep 5134583 = 7701875) B7701875
theorem B2742601 : Blo 1124630 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B1268059 : Blo 1124630 1268059 := bstep (se 1 (by rfl) ⟨951044, by rfl⟩ : syracuseStep 1268059 = 1902089) B1902089
theorem B1268167 : Blo 1124630 1268167 := bstep (se 1 (by rfl) ⟨951125, by rfl⟩ : syracuseStep 1268167 = 1902251) B1902251
theorem B4807163 : Blo 1124630 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B1268527 : Blo 1124630 1268527 := bstep (se 1 (by rfl) ⟨951395, by rfl⟩ : syracuseStep 1268527 = 1902791) B1902791
theorem B1268635 : Blo 1124630 1268635 := bstep (se 1 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 1268635 = 1902953) B1902953
theorem B1203175 : Blo 1124630 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B1269031 : Blo 1124630 1269031 := bstep (se 1 (by rfl) ⟨951773, by rfl⟩ : syracuseStep 1269031 = 1903547) B1903547
theorem B1269103 : Blo 1124630 1269103 := bstep (se 1 (by rfl) ⟨951827, by rfl⟩ : syracuseStep 1269103 = 1903655) B1903655
theorem B1269319 : Blo 1124630 1269319 := bstep (se 1 (by rfl) ⟨951989, by rfl⟩ : syracuseStep 1269319 = 1903979) B1903979
theorem B4283999 : Blo 1124630 4283999 := bstep (se 1 (by rfl) ⟨3212999, by rfl⟩ : syracuseStep 4283999 = 6425999) B6425999
theorem B24338339 : Blo 1124630 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B10838225 : Blo 1124630 10838225 := bstep (se 2 (by rfl) ⟨4064334, by rfl⟩ : syracuseStep 10838225 = 8128669) B8128669
theorem B5693651 : Blo 1124630 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B3203705 : Blo 1124630 3203705 := bstep (se 2 (by rfl) ⟨1201389, by rfl⟩ : syracuseStep 3203705 = 2402779) B2402779
theorem B9626627 : Blo 1124630 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B4056263 : Blo 1124630 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B12346775 : Blo 1124630 12346775 := bstep (se 1 (by rfl) ⟨9260081, by rfl⟩ : syracuseStep 12346775 = 18520163) B18520163
theorem B21685745 : Blo 1124630 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B13723357 : Blo 1124630 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B17328421 : Blo 1124630 17328421 := bstep (se 4 (by rfl) ⟨1624539, by rfl⟩ : syracuseStep 17328421 = 3249079) B3249079
theorem B9628541 : Blo 1124630 9628541 := bstep (se 3 (by rfl) ⟨1805351, by rfl⟩ : syracuseStep 9628541 = 3610703) B3610703
theorem B1829803 : Blo 1124630 1829803 := bstep (se 1 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 1829803 = 2744705) B2744705
theorem B21621775 : Blo 1124630 21621775 := bstep (se 1 (by rfl) ⟨16216331, by rfl⟩ : syracuseStep 21621775 = 32432663) B32432663
theorem B3796091 : Blo 1124630 3796091 := bstep (se 1 (by rfl) ⟨2847068, by rfl⟩ : syracuseStep 3796091 = 5694137) B5694137
theorem B3796361 : Blo 1124630 3796361 := bstep (se 2 (by rfl) ⟨1423635, by rfl⟩ : syracuseStep 3796361 = 2847271) B2847271
theorem B3206587 : Blo 1124630 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B1830635 : Blo 1124630 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B3796793 : Blo 1124630 3796793 := bstep (se 2 (by rfl) ⟨1423797, by rfl⟩ : syracuseStep 3796793 = 2847595) B2847595
theorem B8548253 : Blo 1124630 8548253 := bstep (se 3 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 8548253 = 3205595) B3205595
theorem B2847251 : Blo 1124630 2847251 := bstep (se 1 (by rfl) ⟨2135438, by rfl⟩ : syracuseStep 2847251 = 4270877) B4270877
theorem B3797657 : Blo 1124630 3797657 := bstep (se 2 (by rfl) ⟨1424121, by rfl⟩ : syracuseStep 3797657 = 2848243) B2848243
theorem B3207863 : Blo 1124630 3207863 := bstep (se 1 (by rfl) ⟨2405897, by rfl⟩ : syracuseStep 3207863 = 4811795) B4811795
theorem B207942389 : Blo 1124630 207942389 := bstep (se 5 (by rfl) ⟨9747299, by rfl⟩ : syracuseStep 207942389 = 19494599) B19494599
theorem B2847707 : Blo 1124630 2847707 := bstep (se 1 (by rfl) ⟨2135780, by rfl⟩ : syracuseStep 2847707 = 4271561) B4271561
theorem B12842063 : Blo 1124630 12842063 := bstep (se 1 (by rfl) ⟨9631547, by rfl⟩ : syracuseStep 12842063 = 19263095) B19263095
theorem B10810583 : Blo 1124630 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B2848031 : Blo 1124630 2848031 := bstep (se 1 (by rfl) ⟨2136023, by rfl⟩ : syracuseStep 2848031 = 4272047) B4272047
theorem B8123851 : Blo 1124630 8123851 := bstep (se 1 (by rfl) ⟨6092888, by rfl⟩ : syracuseStep 8123851 = 12185777) B12185777
theorem B22935001 : Blo 1124630 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B2848567 : Blo 1124630 2848567 := bstep (se 1 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 2848567 = 4272851) B4272851
theorem B83359691 : Blo 1124630 83359691 := bstep (se 1 (by rfl) ⟨62519768, by rfl⟩ : syracuseStep 83359691 = 125039537) B125039537
theorem B3799169 : Blo 1124630 3799169 := bstep (se 2 (by rfl) ⟨1424688, by rfl⟩ : syracuseStep 3799169 = 2849377) B2849377
theorem B1898761 : Blo 1124630 1898761 := bstep (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) B1424071
theorem B2849033 : Blo 1124630 2849033 := bstep (se 2 (by rfl) ⟨1068387, by rfl⟩ : syracuseStep 2849033 = 2136775) B2136775
theorem B3799547 : Blo 1124630 3799547 := bstep (se 1 (by rfl) ⟨2849660, by rfl⟩ : syracuseStep 3799547 = 5699321) B5699321
theorem B5143103 : Blo 1124630 5143103 := bstep (se 1 (by rfl) ⟨3857327, by rfl⟩ : syracuseStep 5143103 = 7714655) B7714655
theorem B3799979 : Blo 1124630 3799979 := bstep (se 1 (by rfl) ⟨2849984, by rfl⟩ : syracuseStep 3799979 = 5699969) B5699969
theorem B4815911 : Blo 1124630 4815911 := bstep (se 1 (by rfl) ⟨3611933, by rfl⟩ : syracuseStep 4815911 = 7223867) B7223867
theorem B2850025 : Blo 1124630 2850025 := bstep (se 2 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 2850025 = 2137519) B2137519
theorem B2850187 : Blo 1124630 2850187 := bstep (se 1 (by rfl) ⟨2137640, by rfl⟩ : syracuseStep 2850187 = 4275281) B4275281
theorem B3800519 : Blo 1124630 3800519 := bstep (se 1 (by rfl) ⟨2850389, by rfl⟩ : syracuseStep 3800519 = 5700779) B5700779
theorem B7699927 : Blo 1124630 7699927 := bstep (se 1 (by rfl) ⟨5774945, by rfl⟩ : syracuseStep 7699927 = 11549891) B11549891
theorem B4390415 : Blo 1124630 4390415 := bstep (se 1 (by rfl) ⟨3292811, by rfl⟩ : syracuseStep 4390415 = 6585623) B6585623
theorem B3210835 : Blo 1124630 3210835 := bstep (se 1 (by rfl) ⟨2408126, by rfl⟩ : syracuseStep 3210835 = 4816253) B4816253
theorem B4816493 : Blo 1124630 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B1900219 : Blo 1124630 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B2850491 : Blo 1124630 2850491 := bstep (se 1 (by rfl) ⟨2137868, by rfl⟩ : syracuseStep 2850491 = 4275737) B4275737
theorem B1801963 : Blo 1124630 1801963 := bstep (se 1 (by rfl) ⟨1351472, by rfl⟩ : syracuseStep 1801963 = 2702945) B2702945
theorem B3800843 : Blo 1124630 3800843 := bstep (se 1 (by rfl) ⟨2850632, by rfl⟩ : syracuseStep 3800843 = 5701265) B5701265
theorem B5701913 : Blo 1124630 5701913 := bstep (se 2 (by rfl) ⟨2138217, by rfl⟩ : syracuseStep 5701913 = 4276435) B4276435
theorem B4817177 : Blo 1124630 4817177 := bstep (se 2 (by rfl) ⟨1806441, by rfl⟩ : syracuseStep 4817177 = 3612883) B3612883
theorem B1605919 : Blo 1124630 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B14614937 : Blo 1124630 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B5407175 : Blo 1124630 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B2851271 : Blo 1124630 2851271 := bstep (se 1 (by rfl) ⟨2138453, by rfl⟩ : syracuseStep 2851271 = 4276907) B4276907
theorem B3801707 : Blo 1124630 3801707 := bstep (se 1 (by rfl) ⟨2851280, by rfl⟩ : syracuseStep 3801707 = 5702561) B5702561
theorem B3211883 : Blo 1124630 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B1901353 : Blo 1124630 1901353 := bstep (se 2 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 1901353 = 1426015) B1426015
theorem B1606511 : Blo 1124630 1606511 := bstep (se 1 (by rfl) ⟨1204883, by rfl⟩ : syracuseStep 1606511 = 2409767) B2409767
theorem B1901623 : Blo 1124630 1901623 := bstep (se 1 (by rfl) ⟨1426217, by rfl⟩ : syracuseStep 1901623 = 2852435) B2852435
theorem B1606711 : Blo 1124630 1606711 := bstep (se 1 (by rfl) ⟨1205033, by rfl⟩ : syracuseStep 1606711 = 2410067) B2410067
theorem B7210129 : Blo 1124630 7210129 := bstep (se 2 (by rfl) ⟨2703798, by rfl⟩ : syracuseStep 7210129 = 5407597) B5407597
theorem B3802301 : Blo 1124630 3802301 := bstep (se 3 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 3802301 = 1425863) B1425863
theorem B18286397 : Blo 1124630 18286397 := bstep (se 3 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 18286397 = 6857399) B6857399
theorem B32540615 : Blo 1124630 32540615 := bstep (se 1 (by rfl) ⟨24405461, by rfl⟩ : syracuseStep 32540615 = 48810923) B48810923
theorem B1902575 : Blo 1124630 1902575 := bstep (se 1 (by rfl) ⟨1426931, by rfl⟩ : syracuseStep 1902575 = 2853863) B2853863
theorem B4818953 : Blo 1124630 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B3803327 : Blo 1124630 3803327 := bstep (se 1 (by rfl) ⟨2852495, by rfl⟩ : syracuseStep 3803327 = 5704991) B5704991
theorem B13371601 : Blo 1124630 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B3213523 : Blo 1124630 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B29264165 : Blo 1124630 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B1804583 : Blo 1124630 1804583 := bstep (se 1 (by rfl) ⟨1353437, by rfl⟩ : syracuseStep 1804583 = 2706875) B2706875
theorem B2853215 : Blo 1124630 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B2853407 : Blo 1124630 2853407 := bstep (se 1 (by rfl) ⟨2140055, by rfl⟩ : syracuseStep 2853407 = 4280111) B4280111
theorem B1903135 : Blo 1124630 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B12847895 : Blo 1124630 12847895 := bstep (se 1 (by rfl) ⟨9635921, by rfl⟩ : syracuseStep 12847895 = 19271843) B19271843
theorem B1805147 : Blo 1124630 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B1903567 : Blo 1124630 1903567 := bstep (se 1 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 1903567 = 2855351) B2855351
theorem B23104561 : Blo 1124630 23104561 := bstep (se 2 (by rfl) ⟨8664210, by rfl⟩ : syracuseStep 23104561 = 17328421) B17328421
theorem B4820543 : Blo 1124630 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B1904303 : Blo 1124630 1904303 := bstep (se 1 (by rfl) ⟨1428227, by rfl⟩ : syracuseStep 1904303 = 2856455) B2856455
theorem B3804947 : Blo 1124630 3804947 := bstep (se 1 (by rfl) ⟨2853710, by rfl⟩ : syracuseStep 3804947 = 5707421) B5707421
theorem B1904539 : Blo 1124630 1904539 := bstep (se 1 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 1904539 = 2856809) B2856809
theorem B3608705 : Blo 1124630 3608705 := bstep (se 2 (by rfl) ⟨1353264, by rfl⟩ : syracuseStep 3608705 = 2706529) B2706529
theorem B12161177 : Blo 1124630 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B3805811 : Blo 1124630 3805811 := bstep (se 1 (by rfl) ⟨2854358, by rfl⟩ : syracuseStep 3805811 = 5708717) B5708717
theorem B3806081 : Blo 1124630 3806081 := bstep (se 2 (by rfl) ⟨1427280, by rfl⟩ : syracuseStep 3806081 = 2854561) B2854561
theorem B16225217 : Blo 1124630 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B2855999 : Blo 1124630 2855999 := bstep (se 1 (by rfl) ⟨2141999, by rfl⟩ : syracuseStep 2855999 = 4283999) B4283999
theorem B16225559 : Blo 1124630 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B3806891 : Blo 1124630 3806891 := bstep (se 1 (by rfl) ⟨2855168, by rfl⟩ : syracuseStep 3806891 = 5710337) B5710337
theorem B2135803 : Blo 1124630 2135803 := bstep (se 1 (by rfl) ⟨1601852, by rfl⟩ : syracuseStep 2135803 = 3203705) B3203705
theorem B3807215 : Blo 1124630 3807215 := bstep (se 1 (by rfl) ⟨2855411, by rfl⟩ : syracuseStep 3807215 = 5710823) B5710823
theorem B3807431 : Blo 1124630 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B8231183 : Blo 1124630 8231183 := bstep (se 1 (by rfl) ⟨6173387, by rfl⟩ : syracuseStep 8231183 = 12346775) B12346775
theorem B14457163 : Blo 1124630 14457163 := bstep (se 1 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 14457163 = 21685745) B21685745
theorem B3808079 : Blo 1124630 3808079 := bstep (se 1 (by rfl) ⟨2856059, by rfl⟩ : syracuseStep 3808079 = 5712119) B5712119
theorem B13704137 : Blo 1124630 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B3808403 : Blo 1124630 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B30580001 : Blo 1124630 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B3808673 : Blo 1124630 3808673 := bstep (se 2 (by rfl) ⟨1428252, by rfl⟩ : syracuseStep 3808673 = 2856505) B2856505
theorem B2530727 : Blo 1124630 2530727 := bstep (se 1 (by rfl) ⟨1898045, by rfl⟩ : syracuseStep 2530727 = 3796091) B3796091
theorem B2530907 : Blo 1124630 2530907 := bstep (se 1 (by rfl) ⟨1898180, by rfl⟩ : syracuseStep 2530907 = 3796361) B3796361
theorem B1220423 : Blo 1124630 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B2531195 : Blo 1124630 2531195 := bstep (se 1 (by rfl) ⟨1898396, by rfl⟩ : syracuseStep 2531195 = 3796793) B3796793
theorem B2531681 : Blo 1124630 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B2531771 : Blo 1124630 2531771 := bstep (se 1 (by rfl) ⟨1898828, by rfl⟩ : syracuseStep 2531771 = 3797657) B3797657
theorem B2138575 : Blo 1124630 2138575 := bstep (se 1 (by rfl) ⟨1603931, by rfl⟩ : syracuseStep 2138575 = 3207863) B3207863
theorem B8561375 : Blo 1124630 8561375 := bstep (se 1 (by rfl) ⟨6421031, by rfl⟩ : syracuseStep 8561375 = 12842063) B12842063
theorem B468133091 : Blo 1124630 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B2532779 : Blo 1124630 2532779 := bstep (se 1 (by rfl) ⟨1899584, by rfl⟩ : syracuseStep 2532779 = 3799169) B3799169
theorem B7710329 : Blo 1124630 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B2533031 : Blo 1124630 2533031 := bstep (se 1 (by rfl) ⟨1899773, by rfl⟩ : syracuseStep 2533031 = 3799547) B3799547
theorem B16262927 : Blo 1124630 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B2533319 : Blo 1124630 2533319 := bstep (se 1 (by rfl) ⟨1899989, by rfl⟩ : syracuseStep 2533319 = 3799979) B3799979
theorem B10266569 : Blo 1124630 10266569 := bstep (se 2 (by rfl) ⟨3849963, by rfl⟩ : syracuseStep 10266569 = 7699927) B7699927
theorem B2533625 : Blo 1124630 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B1124655 : Blo 1124630 1124655 := bstep (se 1 (by rfl) ⟨843491, by rfl⟩ : syracuseStep 1124655 = 1686983) B1686983
theorem B2533679 : Blo 1124630 2533679 := bstep (se 1 (by rfl) ⟨1900259, by rfl⟩ : syracuseStep 2533679 = 3800519) B3800519
theorem B2402617 : Blo 1124630 2402617 := bstep (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) B1801963
theorem B2926943 : Blo 1124630 2926943 := bstep (se 1 (by rfl) ⟨2195207, by rfl⟩ : syracuseStep 2926943 = 4390415) B4390415
theorem B3254689 : Blo 1124630 3254689 := bstep (se 2 (by rfl) ⟨1220508, by rfl⟩ : syracuseStep 3254689 = 2441017) B2441017
theorem B2533895 : Blo 1124630 2533895 := bstep (se 1 (by rfl) ⟨1900421, by rfl⟩ : syracuseStep 2533895 = 3800843) B3800843
theorem B1124891 : Blo 1124630 1124891 := bstep (se 1 (by rfl) ⟨843668, by rfl⟩ : syracuseStep 1124891 = 1687337) B1687337
theorem B1124895 : Blo 1124630 1124895 := bstep (se 1 (by rfl) ⟨843671, by rfl⟩ : syracuseStep 1124895 = 1687343) B1687343
theorem B2534075 : Blo 1124630 2534075 := bstep (se 1 (by rfl) ⟨1900556, by rfl⟩ : syracuseStep 2534075 = 3801113) B3801113
theorem B1125211 : Blo 1124630 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B1125279 : Blo 1124630 1125279 := bstep (se 1 (by rfl) ⟨843959, by rfl⟩ : syracuseStep 1125279 = 1687919) B1687919
theorem B1125423 : Blo 1124630 1125423 := bstep (se 1 (by rfl) ⟨844067, by rfl⟩ : syracuseStep 1125423 = 1688135) B1688135
theorem B1125447 : Blo 1124630 1125447 := bstep (se 1 (by rfl) ⟨844085, by rfl⟩ : syracuseStep 1125447 = 1688171) B1688171
theorem B1125599 : Blo 1124630 1125599 := bstep (se 1 (by rfl) ⟨844199, by rfl⟩ : syracuseStep 1125599 = 1688399) B1688399
theorem B2141407 : Blo 1124630 2141407 := bstep (se 1 (by rfl) ⟨1606055, by rfl⟩ : syracuseStep 2141407 = 3212111) B3212111
theorem B1125863 : Blo 1124630 1125863 := bstep (se 1 (by rfl) ⟨844397, by rfl⟩ : syracuseStep 1125863 = 1688795) B1688795
theorem B2534903 : Blo 1124630 2534903 := bstep (se 1 (by rfl) ⟨1901177, by rfl⟩ : syracuseStep 2534903 = 3802355) B3802355
theorem B2534975 : Blo 1124630 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B1125979 : Blo 1124630 1125979 := bstep (se 1 (by rfl) ⟨844484, by rfl⟩ : syracuseStep 1125979 = 1688969) B1688969
theorem B1126215 : Blo 1124630 1126215 := bstep (se 1 (by rfl) ⟨844661, by rfl⟩ : syracuseStep 1126215 = 1689323) B1689323
theorem B1126367 : Blo 1124630 1126367 := bstep (se 1 (by rfl) ⟨844775, by rfl⟩ : syracuseStep 1126367 = 1689551) B1689551
theorem B1126631 : Blo 1124630 1126631 := bstep (se 1 (by rfl) ⟨844973, by rfl⟩ : syracuseStep 1126631 = 1689947) B1689947
theorem B1126783 : Blo 1124630 1126783 := bstep (se 1 (by rfl) ⟨845087, by rfl⟩ : syracuseStep 1126783 = 1690175) B1690175
theorem B1126863 : Blo 1124630 1126863 := bstep (se 1 (by rfl) ⟨845147, by rfl⟩ : syracuseStep 1126863 = 1690295) B1690295
theorem B2535929 : Blo 1124630 2535929 := bstep (se 2 (by rfl) ⟨950973, by rfl⟩ : syracuseStep 2535929 = 1901947) B1901947
theorem B2536019 : Blo 1124630 2536019 := bstep (se 1 (by rfl) ⟨1902014, by rfl⟩ : syracuseStep 2536019 = 3804029) B3804029
theorem B1127015 : Blo 1124630 1127015 := bstep (se 1 (by rfl) ⟨845261, by rfl⟩ : syracuseStep 1127015 = 1690523) B1690523
theorem B14430919 : Blo 1124630 14430919 := bstep (se 1 (by rfl) ⟨10823189, by rfl⟩ : syracuseStep 14430919 = 21646379) B21646379
theorem B2536199 : Blo 1124630 2536199 := bstep (se 1 (by rfl) ⟨1902149, by rfl⟩ : syracuseStep 2536199 = 3804299) B3804299
theorem B1127279 : Blo 1124630 1127279 := bstep (se 1 (by rfl) ⟨845459, by rfl⟩ : syracuseStep 1127279 = 1690919) B1690919
theorem B1127335 : Blo 1124630 1127335 := bstep (se 1 (by rfl) ⟨845501, by rfl⟩ : syracuseStep 1127335 = 1691003) B1691003
theorem B18297809 : Blo 1124630 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B1127419 : Blo 1124630 1127419 := bstep (se 1 (by rfl) ⟨845564, by rfl⟩ : syracuseStep 1127419 = 1691129) B1691129
theorem B1127487 : Blo 1124630 1127487 := bstep (se 1 (by rfl) ⟨845615, by rfl⟩ : syracuseStep 1127487 = 1691231) B1691231
theorem B6599879 : Blo 1124630 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B1127631 : Blo 1124630 1127631 := bstep (se 1 (by rfl) ⟨845723, by rfl⟩ : syracuseStep 1127631 = 1691447) B1691447
theorem B3421403 : Blo 1124630 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B1127835 : Blo 1124630 1127835 := bstep (se 1 (by rfl) ⟨845876, by rfl⟩ : syracuseStep 1127835 = 1691753) B1691753
theorem B1128047 : Blo 1124630 1128047 := bstep (se 1 (by rfl) ⟨846035, by rfl⟩ : syracuseStep 1128047 = 1692071) B1692071
theorem B1128103 : Blo 1124630 1128103 := bstep (se 1 (by rfl) ⟨846077, by rfl⟩ : syracuseStep 1128103 = 1692155) B1692155
theorem B1128187 : Blo 1124630 1128187 := bstep (se 1 (by rfl) ⟨846140, by rfl⟩ : syracuseStep 1128187 = 1692281) B1692281
theorem B1128223 : Blo 1124630 1128223 := bstep (se 1 (by rfl) ⟨846167, by rfl⟩ : syracuseStep 1128223 = 1692335) B1692335
theorem B2537279 : Blo 1124630 2537279 := bstep (se 1 (by rfl) ⟨1902959, by rfl⟩ : syracuseStep 2537279 = 3805919) B3805919
theorem B1128255 : Blo 1124630 1128255 := bstep (se 1 (by rfl) ⟨846191, by rfl⟩ : syracuseStep 1128255 = 1692383) B1692383
theorem B1128431 : Blo 1124630 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B5781497 : Blo 1124630 5781497 := bstep (se 2 (by rfl) ⟨2168061, by rfl⟩ : syracuseStep 5781497 = 4336123) B4336123
theorem B9615419 : Blo 1124630 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B2537567 : Blo 1124630 2537567 := bstep (se 1 (by rfl) ⟨1903175, by rfl⟩ : syracuseStep 2537567 = 3806351) B3806351
theorem B1128603 : Blo 1124630 1128603 := bstep (se 1 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 1128603 = 1692905) B1692905
theorem B1423595 : Blo 1124630 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B2570503 : Blo 1124630 2570503 := bstep (se 1 (by rfl) ⟨1927877, by rfl⟩ : syracuseStep 2570503 = 3855755) B3855755
theorem B2439737 : Blo 1124630 2439737 := bstep (se 2 (by rfl) ⟨914901, by rfl⟩ : syracuseStep 2439737 = 1829803) B1829803
theorem B3423055 : Blo 1124630 3423055 := bstep (se 1 (by rfl) ⟨2567291, by rfl⟩ : syracuseStep 3423055 = 5134583) B5134583
theorem B2538323 : Blo 1124630 2538323 := bstep (se 1 (by rfl) ⟨1903742, by rfl⟩ : syracuseStep 2538323 = 3807485) B3807485
theorem B2407495 : Blo 1124630 2407495 := bstep (se 1 (by rfl) ⟨1805621, by rfl⟩ : syracuseStep 2407495 = 3611243) B3611243
theorem B1424567 : Blo 1124630 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B4275449 : Blo 1124630 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B1424719 : Blo 1124630 1424719 := bstep (se 1 (by rfl) ⟨1068539, by rfl⟩ : syracuseStep 1424719 = 2137079) B2137079
theorem B2538863 : Blo 1124630 2538863 := bstep (se 1 (by rfl) ⟨1904147, by rfl⟩ : syracuseStep 2538863 = 3808295) B3808295
theorem B1686953 : Blo 1124630 1686953 := bstep (se 2 (by rfl) ⟨632607, by rfl⟩ : syracuseStep 1686953 = 1265215) B1265215
theorem B6405587 : Blo 1124630 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1687103 : Blo 1124630 1687103 := bstep (se 1 (by rfl) ⟨1265327, by rfl⟩ : syracuseStep 1687103 = 2530655) B2530655
theorem B2539151 : Blo 1124630 2539151 := bstep (se 1 (by rfl) ⟨1904363, by rfl⟩ : syracuseStep 2539151 = 3808727) B3808727
theorem B43302599 : Blo 1124630 43302599 := bstep (se 1 (by rfl) ⟨32476949, by rfl⟩ : syracuseStep 43302599 = 64953899) B64953899
theorem B9617129 : Blo 1124630 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B2539241 : Blo 1124630 2539241 := bstep (se 2 (by rfl) ⟨952215, by rfl⟩ : syracuseStep 2539241 = 1904431) B1904431
theorem B1687367 : Blo 1124630 1687367 := bstep (se 1 (by rfl) ⟨1265525, by rfl⟩ : syracuseStep 1687367 = 2531051) B2531051
theorem B1687451 : Blo 1124630 1687451 := bstep (se 1 (by rfl) ⟨1265588, by rfl⟩ : syracuseStep 1687451 = 2531177) B2531177
theorem B7225483 : Blo 1124630 7225483 := bstep (se 1 (by rfl) ⟨5419112, by rfl⟩ : syracuseStep 7225483 = 10838225) B10838225
theorem B1688015 : Blo 1124630 1688015 := bstep (se 1 (by rfl) ⟨1266011, by rfl⟩ : syracuseStep 1688015 = 2532023) B2532023
theorem B1688057 : Blo 1124630 1688057 := bstep (se 2 (by rfl) ⟨633021, by rfl⟩ : syracuseStep 1688057 = 1266043) B1266043
theorem B1688159 : Blo 1124630 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B2704175 : Blo 1124630 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1688639 : Blo 1124630 1688639 := bstep (se 1 (by rfl) ⟨1266479, by rfl⟩ : syracuseStep 1688639 = 2532959) B2532959
theorem B1688681 : Blo 1124630 1688681 := bstep (se 2 (by rfl) ⟨633255, by rfl⟩ : syracuseStep 1688681 = 1266511) B1266511
theorem B1688783 : Blo 1124630 1688783 := bstep (se 1 (by rfl) ⟨1266587, by rfl⟩ : syracuseStep 1688783 = 2533175) B2533175
theorem B8570123 : Blo 1124630 8570123 := bstep (se 1 (by rfl) ⟨6427592, by rfl⟩ : syracuseStep 8570123 = 12855185) B12855185
theorem B1688987 : Blo 1124630 1688987 := bstep (se 1 (by rfl) ⟨1266740, by rfl⟩ : syracuseStep 1688987 = 2533481) B2533481
theorem B1689209 : Blo 1124630 1689209 := bstep (se 2 (by rfl) ⟨633453, by rfl⟩ : syracuseStep 1689209 = 1266907) B1266907
theorem B1689311 : Blo 1124630 1689311 := bstep (se 1 (by rfl) ⟨1266983, by rfl⟩ : syracuseStep 1689311 = 2533967) B2533967
theorem B1689407 : Blo 1124630 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B10831801 : Blo 1124630 10831801 := bstep (se 2 (by rfl) ⟨4061925, by rfl⟩ : syracuseStep 10831801 = 8123851) B8123851
theorem B1689575 : Blo 1124630 1689575 := bstep (se 1 (by rfl) ⟨1267181, by rfl⟩ : syracuseStep 1689575 = 2534363) B2534363
theorem B1689593 : Blo 1124630 1689593 := bstep (se 2 (by rfl) ⟨633597, by rfl⟩ : syracuseStep 1689593 = 1267195) B1267195
theorem B1689695 : Blo 1124630 1689695 := bstep (se 1 (by rfl) ⟨1267271, by rfl⟩ : syracuseStep 1689695 = 2534543) B2534543
theorem B1689755 : Blo 1124630 1689755 := bstep (se 1 (by rfl) ⟨1267316, by rfl⟩ : syracuseStep 1689755 = 2534633) B2534633
theorem B1689791 : Blo 1124630 1689791 := bstep (se 1 (by rfl) ⟨1267343, by rfl⟩ : syracuseStep 1689791 = 2534687) B2534687
theorem B1689833 : Blo 1124630 1689833 := bstep (se 2 (by rfl) ⟨633687, by rfl⟩ : syracuseStep 1689833 = 1267375) B1267375
theorem B1690139 : Blo 1124630 1690139 := bstep (se 1 (by rfl) ⟨1267604, by rfl⟩ : syracuseStep 1690139 = 2535209) B2535209
theorem B1690217 : Blo 1124630 1690217 := bstep (se 2 (by rfl) ⟨633831, by rfl⟩ : syracuseStep 1690217 = 1267663) B1267663
theorem B3656801 : Blo 1124630 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B1690745 : Blo 1124630 1690745 := bstep (se 2 (by rfl) ⟨634029, by rfl⟩ : syracuseStep 1690745 = 1268059) B1268059
theorem B138628259 : Blo 1124630 138628259 := bstep (se 1 (by rfl) ⟨103971194, by rfl⟩ : syracuseStep 138628259 = 207942389) B207942389
theorem B1690847 : Blo 1124630 1690847 := bstep (se 1 (by rfl) ⟨1268135, by rfl⟩ : syracuseStep 1690847 = 2536271) B2536271
theorem B1690889 : Blo 1124630 1690889 := bstep (se 2 (by rfl) ⟨634083, by rfl⟩ : syracuseStep 1690889 = 1268167) B1268167
theorem B6081817 : Blo 1124630 6081817 := bstep (se 2 (by rfl) ⟨2280681, by rfl⟩ : syracuseStep 6081817 = 4561363) B4561363
theorem B1690991 : Blo 1124630 1690991 := bstep (se 1 (by rfl) ⟨1268243, by rfl⟩ : syracuseStep 1690991 = 2536487) B2536487
theorem B1691111 : Blo 1124630 1691111 := bstep (se 1 (by rfl) ⟨1268333, by rfl⟩ : syracuseStep 1691111 = 2536667) B2536667
theorem B8113679 : Blo 1124630 8113679 := bstep (se 1 (by rfl) ⟨6085259, by rfl⟩ : syracuseStep 8113679 = 12170519) B12170519
theorem B1691243 : Blo 1124630 1691243 := bstep (se 1 (by rfl) ⟨1268432, by rfl⟩ : syracuseStep 1691243 = 2536865) B2536865
theorem B1691369 : Blo 1124630 1691369 := bstep (se 2 (by rfl) ⟨634263, by rfl⟩ : syracuseStep 1691369 = 1268527) B1268527
theorem B1691513 : Blo 1124630 1691513 := bstep (se 2 (by rfl) ⟨634317, by rfl⟩ : syracuseStep 1691513 = 1268635) B1268635
theorem B1691615 : Blo 1124630 1691615 := bstep (se 1 (by rfl) ⟨1268711, by rfl⟩ : syracuseStep 1691615 = 2537423) B2537423
theorem B1691867 : Blo 1124630 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B6410461 : Blo 1124630 6410461 := bstep (se 3 (by rfl) ⟨1201961, by rfl⟩ : syracuseStep 6410461 = 2403923) B2403923
theorem B1691879 : Blo 1124630 1691879 := bstep (se 1 (by rfl) ⟨1268909, by rfl⟩ : syracuseStep 1691879 = 2537819) B2537819
theorem B3428735 : Blo 1124630 3428735 := bstep (se 1 (by rfl) ⟨2571551, by rfl⟩ : syracuseStep 3428735 = 5143103) B5143103
theorem B1692041 : Blo 1124630 1692041 := bstep (se 2 (by rfl) ⟨634515, by rfl⟩ : syracuseStep 1692041 = 1269031) B1269031
theorem B1692137 : Blo 1124630 1692137 := bstep (se 2 (by rfl) ⟨634551, by rfl⟩ : syracuseStep 1692137 = 1269103) B1269103
theorem B1692263 : Blo 1124630 1692263 := bstep (se 1 (by rfl) ⟨1269197, by rfl⟩ : syracuseStep 1692263 = 2538395) B2538395
theorem B1692395 : Blo 1124630 1692395 := bstep (se 1 (by rfl) ⟨1269296, by rfl⟩ : syracuseStep 1692395 = 2538593) B2538593
theorem B1692425 : Blo 1124630 1692425 := bstep (se 2 (by rfl) ⟨634659, by rfl⟩ : syracuseStep 1692425 = 1269319) B1269319
theorem B4281113 : Blo 1124630 4281113 := bstep (se 2 (by rfl) ⟨1605417, by rfl⟩ : syracuseStep 4281113 = 3210835) B3210835
theorem B12342041 : Blo 1124630 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B1692527 : Blo 1124630 1692527 := bstep (se 1 (by rfl) ⟨1269395, by rfl⟩ : syracuseStep 1692527 = 2538791) B2538791
theorem B1692779 : Blo 1124630 1692779 := bstep (se 1 (by rfl) ⟨1269584, by rfl⟩ : syracuseStep 1692779 = 2539169) B2539169
theorem B8115547 : Blo 1124630 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1267519 : Blo 1124630 1267519 := bstep (se 1 (by rfl) ⟨950639, by rfl⟩ : syracuseStep 1267519 = 1901279) B1901279
theorem B2316271 : Blo 1124630 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B1267807 : Blo 1124630 1267807 := bstep (se 1 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 1267807 = 1901711) B1901711
theorem B26368409 : Blo 1124630 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B6085277 : Blo 1124630 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B4807505 : Blo 1124630 4807505 := bstep (se 2 (by rfl) ⟨1802814, by rfl⟩ : syracuseStep 4807505 = 3605629) B3605629
theorem B5135329 : Blo 1124630 5135329 := bstep (se 2 (by rfl) ⟨1925748, by rfl⟩ : syracuseStep 5135329 = 3851497) B3851497
theorem B1268959 : Blo 1124630 1268959 := bstep (se 1 (by rfl) ⟨951719, by rfl⟩ : syracuseStep 1268959 = 1903439) B1903439
theorem B26008897 : Blo 1124630 26008897 := bstep (se 2 (by rfl) ⟨9753336, by rfl⟩ : syracuseStep 26008897 = 19506673) B19506673
theorem B6413903 : Blo 1124630 6413903 := bstep (se 1 (by rfl) ⟨4810427, by rfl⟩ : syracuseStep 6413903 = 9620855) B9620855
theorem B3202703 : Blo 1124630 3202703 := bstep (se 1 (by rfl) ⟨2402027, by rfl⟩ : syracuseStep 3202703 = 4804055) B4804055
theorem B22568861 : Blo 1124630 22568861 := bstep (se 3 (by rfl) ⟨4231661, by rfl⟩ : syracuseStep 22568861 = 8463323) B8463323
theorem B4055615 : Blo 1124630 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B4285001 : Blo 1124630 4285001 := bstep (se 2 (by rfl) ⟨1606875, by rfl⟩ : syracuseStep 4285001 = 3213751) B3213751
theorem B3203819 : Blo 1124630 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B3203887 : Blo 1124630 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B49996973 : Blo 1124630 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B28829033 : Blo 1124630 28829033 := bstep (se 2 (by rfl) ⟨10810887, by rfl⟩ : syracuseStep 28829033 = 21621775) B21621775
theorem B3204775 : Blo 1124630 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B5695433 : Blo 1124630 5695433 := bstep (se 2 (by rfl) ⟨2135787, by rfl⟩ : syracuseStep 5695433 = 4271575) B4271575
theorem B3205129 : Blo 1124630 3205129 := bstep (se 2 (by rfl) ⟨1201923, by rfl⟩ : syracuseStep 3205129 = 2403847) B2403847
theorem B2058383 : Blo 1124630 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B23161049 : Blo 1124630 23161049 := bstep (se 2 (by rfl) ⟨8685393, by rfl⟩ : syracuseStep 23161049 = 17370787) B17370787
theorem B87845411 : Blo 1124630 87845411 := bstep (se 1 (by rfl) ⟨65884058, by rfl⟩ : syracuseStep 87845411 = 131768117) B131768117
theorem B3795767 : Blo 1124630 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B65071997 : Blo 1124630 65071997 := bstep (se 3 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 65071997 = 24401999) B24401999
theorem B25979869 : Blo 1124630 25979869 := bstep (se 3 (by rfl) ⟨4871225, by rfl⟩ : syracuseStep 25979869 = 9742451) B9742451
theorem B16477337 : Blo 1124630 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B4812119 : Blo 1124630 4812119 := bstep (se 1 (by rfl) ⟨3609089, by rfl⟩ : syracuseStep 4812119 = 7218179) B7218179
theorem B6417751 : Blo 1124630 6417751 := bstep (se 1 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 6417751 = 9626627) B9626627
theorem B9269099 : Blo 1124630 9269099 := bstep (se 1 (by rfl) ⟨6951824, by rfl⟩ : syracuseStep 9269099 = 13903649) B13903649
theorem B4812767 : Blo 1124630 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B32534731 : Blo 1124630 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B4059389 : Blo 1124630 4059389 := bstep (se 3 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 4059389 = 1522271) B1522271
theorem B6419027 : Blo 1124630 6419027 := bstep (se 1 (by rfl) ⟨4814270, by rfl⟩ : syracuseStep 6419027 = 9628541) B9628541
theorem B10810273 : Blo 1124630 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B8221601 : Blo 1124630 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B3798089 : Blo 1124630 3798089 := bstep (se 2 (by rfl) ⟨1424283, by rfl⟩ : syracuseStep 3798089 = 2848567) B2848567
theorem B2847919 : Blo 1124630 2847919 := bstep (se 1 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 2847919 = 4271879) B4271879
theorem B5698835 : Blo 1124630 5698835 := bstep (se 1 (by rfl) ⟨4274126, by rfl⟩ : syracuseStep 5698835 = 8548253) B8548253
theorem B752842079 : Blo 1124630 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B4814407 : Blo 1124630 4814407 := bstep (se 1 (by rfl) ⟨3610805, by rfl⟩ : syracuseStep 4814407 = 7221611) B7221611
theorem B1898167 : Blo 1124630 1898167 := bstep (se 1 (by rfl) ⟨1423625, by rfl⟩ : syracuseStep 1898167 = 2847251) B2847251
theorem B1898471 : Blo 1124630 1898471 := bstep (se 1 (by rfl) ⟨1423853, by rfl⟩ : syracuseStep 1898471 = 2847707) B2847707
theorem B1603567 : Blo 1124630 1603567 := bstep (se 1 (by rfl) ⟨1202675, by rfl⟩ : syracuseStep 1603567 = 2405351) B2405351
theorem B3209321 : Blo 1124630 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B7207055 : Blo 1124630 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B3209377 : Blo 1124630 3209377 := bstep (se 2 (by rfl) ⟨1203516, by rfl⟩ : syracuseStep 3209377 = 2407033) B2407033
theorem B7698617 : Blo 1124630 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B1898687 : Blo 1124630 1898687 := bstep (se 1 (by rfl) ⟨1424015, by rfl⟩ : syracuseStep 1898687 = 2848031) B2848031
theorem B55573127 : Blo 1124630 55573127 := bstep (se 1 (by rfl) ⟨41679845, by rfl⟩ : syracuseStep 55573127 = 83359691) B83359691
theorem B1604233 : Blo 1124630 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B3799709 : Blo 1124630 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B1899355 : Blo 1124630 1899355 := bstep (se 1 (by rfl) ⟨1424516, by rfl⟩ : syracuseStep 1899355 = 2849033) B2849033
theorem B3800033 : Blo 1124630 3800033 := bstep (se 2 (by rfl) ⟨1425012, by rfl⟩ : syracuseStep 3800033 = 2850025) B2850025
theorem B2849863 : Blo 1124630 2849863 := bstep (se 1 (by rfl) ⟨2137397, by rfl⟩ : syracuseStep 2849863 = 4274795) B4274795
theorem B2849975 : Blo 1124630 2849975 := bstep (se 1 (by rfl) ⟨2137481, by rfl⟩ : syracuseStep 2849975 = 4274963) B4274963
theorem B10714295 : Blo 1124630 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B3800249 : Blo 1124630 3800249 := bstep (se 2 (by rfl) ⟨1425093, by rfl⟩ : syracuseStep 3800249 = 2850187) B2850187
theorem B3210607 : Blo 1124630 3210607 := bstep (se 1 (by rfl) ⟨2407955, by rfl⟩ : syracuseStep 3210607 = 4815911) B4815911
theorem B6094273 : Blo 1124630 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B6422125 : Blo 1124630 6422125 := bstep (se 3 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 6422125 = 2408297) B2408297
theorem B3210995 : Blo 1124630 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B1900327 : Blo 1124630 1900327 := bstep (se 1 (by rfl) ⟨1425245, by rfl⟩ : syracuseStep 1900327 = 2850491) B2850491
theorem B9633977 : Blo 1124630 9633977 := bstep (se 2 (by rfl) ⟨3612741, by rfl⟩ : syracuseStep 9633977 = 7225483) B7225483
theorem B3801275 : Blo 1124630 3801275 := bstep (se 1 (by rfl) ⟨2850956, by rfl⟩ : syracuseStep 3801275 = 5701913) B5701913
theorem B3211451 : Blo 1124630 3211451 := bstep (se 1 (by rfl) ⟨2408588, by rfl⟩ : syracuseStep 3211451 = 4817177) B4817177
theorem B1900847 : Blo 1124630 1900847 := bstep (se 1 (by rfl) ⟨1425635, by rfl⟩ : syracuseStep 1900847 = 2851271) B2851271
theorem B1802783 : Blo 1124630 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B2851433 : Blo 1124630 2851433 := bstep (se 2 (by rfl) ⟨1069287, by rfl⟩ : syracuseStep 2851433 = 2138575) B2138575
theorem B9143293 : Blo 1124630 9143293 := bstep (se 3 (by rfl) ⟨1714367, by rfl⟩ : syracuseStep 9143293 = 3428735) B3428735
theorem B14419133 : Blo 1124630 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B12190931 : Blo 1124630 12190931 := bstep (se 1 (by rfl) ⟨9143198, by rfl⟩ : syracuseStep 12190931 = 18286397) B18286397
theorem B21693743 : Blo 1124630 21693743 := bstep (se 1 (by rfl) ⟨16270307, by rfl⟩ : syracuseStep 21693743 = 32540615) B32540615
theorem B3212635 : Blo 1124630 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B1902143 : Blo 1124630 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B1902271 : Blo 1124630 1902271 := bstep (se 1 (by rfl) ⟨1426703, by rfl⟩ : syracuseStep 1902271 = 2853407) B2853407
theorem B5409119 : Blo 1124630 5409119 := bstep (se 1 (by rfl) ⟨4056839, by rfl⟩ : syracuseStep 5409119 = 8113679) B8113679
theorem B3213695 : Blo 1124630 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B17828801 : Blo 1124630 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B8228027 : Blo 1124630 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B2854075 : Blo 1124630 2854075 := bstep (se 1 (by rfl) ⟨2140556, by rfl⟩ : syracuseStep 2854075 = 4281113) B4281113
theorem B10816811 : Blo 1124630 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B1903999 : Blo 1124630 1903999 := bstep (se 1 (by rfl) ⟨1427999, by rfl⟩ : syracuseStep 1903999 = 2855999) B2855999
theorem B10817039 : Blo 1124630 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B34639825 : Blo 1124630 34639825 := bstep (se 2 (by rfl) ⟨12989934, by rfl⟩ : syracuseStep 34639825 = 25979869) B25979869
theorem B30806081 : Blo 1124630 30806081 := bstep (se 2 (by rfl) ⟨11552280, by rfl⟩ : syracuseStep 30806081 = 23104561) B23104561
theorem B2855209 : Blo 1124630 2855209 := bstep (se 2 (by rfl) ⟨1070703, by rfl⟩ : syracuseStep 2855209 = 2141407) B2141407
theorem B8557001 : Blo 1124630 8557001 := bstep (se 2 (by rfl) ⟨3208875, by rfl⟩ : syracuseStep 8557001 = 6417751) B6417751
theorem B20386667 : Blo 1124630 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B2135135 : Blo 1124630 2135135 := bstep (se 1 (by rfl) ⟨1601351, by rfl⟩ : syracuseStep 2135135 = 3202703) B3202703
theorem B15045907 : Blo 1124630 15045907 := bstep (se 1 (by rfl) ⟨11284430, by rfl⟩ : syracuseStep 15045907 = 22568861) B22568861
theorem B2856667 : Blo 1124630 2856667 := bstep (se 1 (by rfl) ⟨2142500, by rfl⟩ : syracuseStep 2856667 = 4285001) B4285001
theorem B5707583 : Blo 1124630 5707583 := bstep (se 1 (by rfl) ⟨4280687, by rfl⟩ : syracuseStep 5707583 = 8561375) B8561375
theorem B2135879 : Blo 1124630 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B312088727 : Blo 1124630 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B19241225 : Blo 1124630 19241225 := bstep (se 2 (by rfl) ⟨7215459, by rfl⟩ : syracuseStep 19241225 = 14430919) B14430919
theorem B15440699 : Blo 1124630 15440699 := bstep (se 1 (by rfl) ⟨11580524, by rfl⟩ : syracuseStep 15440699 = 23161049) B23161049
theorem B58563607 : Blo 1124630 58563607 := bstep (se 1 (by rfl) ⟨43922705, by rfl⟩ : syracuseStep 58563607 = 87845411) B87845411
theorem B10820729 : Blo 1124630 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B2530511 : Blo 1124630 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B10984891 : Blo 1124630 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B2530889 : Blo 1124630 2530889 := bstep (se 2 (by rfl) ⟨949083, by rfl⟩ : syracuseStep 2530889 = 1898167) B1898167
theorem B2138089 : Blo 1124630 2138089 := bstep (se 2 (by rfl) ⟨801783, by rfl⟩ : syracuseStep 2138089 = 1603567) B1603567
theorem B3088361 : Blo 1124630 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B19276217 : Blo 1124630 19276217 := bstep (se 2 (by rfl) ⟨7228581, by rfl⟩ : syracuseStep 19276217 = 14457163) B14457163
theorem B5481067 : Blo 1124630 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B12198539 : Blo 1124630 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B2532059 : Blo 1124630 2532059 := bstep (se 1 (by rfl) ⟨1899044, by rfl⟩ : syracuseStep 2532059 = 3798089) B3798089
theorem B4399919 : Blo 1124630 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B2138977 : Blo 1124630 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B4564073 : Blo 1124630 4564073 := bstep (se 2 (by rfl) ⟨1711527, by rfl⟩ : syracuseStep 4564073 = 3423055) B3423055
theorem B2532473 : Blo 1124630 2532473 := bstep (se 2 (by rfl) ⟨949677, by rfl⟩ : syracuseStep 2532473 = 1899355) B1899355
theorem B2139547 : Blo 1124630 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B34678529 : Blo 1124630 34678529 := bstep (se 2 (by rfl) ⟨13004448, by rfl⟩ : syracuseStep 34678529 = 26008897) B26008897
theorem B2533139 : Blo 1124630 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B2533355 : Blo 1124630 2533355 := bstep (se 1 (by rfl) ⟨1900016, by rfl⟩ : syracuseStep 2533355 = 3800033) B3800033
theorem B2533499 : Blo 1124630 2533499 := bstep (se 1 (by rfl) ⟨1900124, by rfl⟩ : syracuseStep 2533499 = 3800249) B3800249
theorem B8562833 : Blo 1124630 8562833 := bstep (se 2 (by rfl) ⟨3211062, by rfl⟩ : syracuseStep 8562833 = 6422125) B6422125
theorem B3254461 : Blo 1124630 3254461 := bstep (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) B1220423
theorem B1124635 : Blo 1124630 1124635 := bstep (se 1 (by rfl) ⟨843476, by rfl⟩ : syracuseStep 1124635 = 1686953) B1686953
theorem B4270391 : Blo 1124630 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B1124735 : Blo 1124630 1124735 := bstep (se 1 (by rfl) ⟨843551, by rfl⟩ : syracuseStep 1124735 = 1687103) B1687103
theorem B2533769 : Blo 1124630 2533769 := bstep (se 2 (by rfl) ⟨950163, by rfl⟩ : syracuseStep 2533769 = 1900327) B1900327
theorem B2140663 : Blo 1124630 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B1124911 : Blo 1124630 1124911 := bstep (se 1 (by rfl) ⟨843683, by rfl⟩ : syracuseStep 1124911 = 1687367) B1687367
theorem B1124967 : Blo 1124630 1124967 := bstep (se 1 (by rfl) ⟨843725, by rfl⟩ : syracuseStep 1124967 = 1687451) B1687451
theorem B9743291 : Blo 1124630 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B1125343 : Blo 1124630 1125343 := bstep (se 1 (by rfl) ⟨844007, by rfl⟩ : syracuseStep 1125343 = 1688015) B1688015
theorem B1125371 : Blo 1124630 1125371 := bstep (se 1 (by rfl) ⟨844028, by rfl⟩ : syracuseStep 1125371 = 1688057) B1688057
theorem B2141225 : Blo 1124630 2141225 := bstep (se 2 (by rfl) ⟨802959, by rfl⟩ : syracuseStep 2141225 = 1605919) B1605919
theorem B1125439 : Blo 1124630 1125439 := bstep (se 1 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 1125439 = 1688159) B1688159
theorem B2534471 : Blo 1124630 2534471 := bstep (se 1 (by rfl) ⟨1900853, by rfl⟩ : syracuseStep 2534471 = 3801707) B3801707
theorem B2141255 : Blo 1124630 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B1125759 : Blo 1124630 1125759 := bstep (se 1 (by rfl) ⟨844319, by rfl⟩ : syracuseStep 1125759 = 1688639) B1688639
theorem B1125787 : Blo 1124630 1125787 := bstep (se 1 (by rfl) ⟨844340, by rfl⟩ : syracuseStep 1125787 = 1688681) B1688681
theorem B2534867 : Blo 1124630 2534867 := bstep (se 1 (by rfl) ⟨1901150, by rfl⟩ : syracuseStep 2534867 = 3802301) B3802301
theorem B1125855 : Blo 1124630 1125855 := bstep (se 1 (by rfl) ⟨844391, by rfl⟩ : syracuseStep 1125855 = 1688783) B1688783
theorem B5713415 : Blo 1124630 5713415 := bstep (se 1 (by rfl) ⟨4285061, by rfl⟩ : syracuseStep 5713415 = 8570123) B8570123
theorem B1125991 : Blo 1124630 1125991 := bstep (se 1 (by rfl) ⟨844493, by rfl⟩ : syracuseStep 1125991 = 1688987) B1688987
theorem B2535137 : Blo 1124630 2535137 := bstep (se 2 (by rfl) ⟨950676, by rfl⟩ : syracuseStep 2535137 = 1901353) B1901353
theorem B4271849 : Blo 1124630 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B1126139 : Blo 1124630 1126139 := bstep (se 1 (by rfl) ⟨844604, by rfl⟩ : syracuseStep 1126139 = 1689209) B1689209
theorem B1126207 : Blo 1124630 1126207 := bstep (se 1 (by rfl) ⟨844655, by rfl⟩ : syracuseStep 1126207 = 1689311) B1689311
theorem B1126271 : Blo 1124630 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B1126383 : Blo 1124630 1126383 := bstep (se 1 (by rfl) ⟨844787, by rfl⟩ : syracuseStep 1126383 = 1689575) B1689575
theorem B1126395 : Blo 1124630 1126395 := bstep (se 1 (by rfl) ⟨844796, by rfl⟩ : syracuseStep 1126395 = 1689593) B1689593
theorem B1126463 : Blo 1124630 1126463 := bstep (se 1 (by rfl) ⟨844847, by rfl⟩ : syracuseStep 1126463 = 1689695) B1689695
theorem B2535497 : Blo 1124630 2535497 := bstep (se 2 (by rfl) ⟨950811, by rfl⟩ : syracuseStep 2535497 = 1901623) B1901623
theorem B2142281 : Blo 1124630 2142281 := bstep (se 2 (by rfl) ⟨803355, by rfl⟩ : syracuseStep 2142281 = 1606711) B1606711
theorem B1126503 : Blo 1124630 1126503 := bstep (se 1 (by rfl) ⟨844877, by rfl⟩ : syracuseStep 1126503 = 1689755) B1689755
theorem B1126527 : Blo 1124630 1126527 := bstep (se 1 (by rfl) ⟨844895, by rfl⟩ : syracuseStep 1126527 = 1689791) B1689791
theorem B2535551 : Blo 1124630 2535551 := bstep (se 1 (by rfl) ⟨1901663, by rfl⟩ : syracuseStep 2535551 = 3803327) B3803327
theorem B1126555 : Blo 1124630 1126555 := bstep (se 1 (by rfl) ⟨844916, by rfl⟩ : syracuseStep 1126555 = 1689833) B1689833
theorem B9613505 : Blo 1124630 9613505 := bstep (se 2 (by rfl) ⟨3605064, by rfl⟩ : syracuseStep 9613505 = 7210129) B7210129
theorem B19509443 : Blo 1124630 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B1126759 : Blo 1124630 1126759 := bstep (se 1 (by rfl) ⟨845069, by rfl⟩ : syracuseStep 1126759 = 1690139) B1690139
theorem B1126811 : Blo 1124630 1126811 := bstep (se 1 (by rfl) ⟨845108, by rfl⟩ : syracuseStep 1126811 = 1690217) B1690217
theorem B8565263 : Blo 1124630 8565263 := bstep (se 1 (by rfl) ⟨6423947, by rfl⟩ : syracuseStep 8565263 = 12847895) B12847895
theorem B2437867 : Blo 1124630 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B1127163 : Blo 1124630 1127163 := bstep (se 1 (by rfl) ⟨845372, by rfl⟩ : syracuseStep 1127163 = 1690745) B1690745
theorem B92418839 : Blo 1124630 92418839 := bstep (se 1 (by rfl) ⟨69314129, by rfl⟩ : syracuseStep 92418839 = 138628259) B138628259
theorem B1127231 : Blo 1124630 1127231 := bstep (se 1 (by rfl) ⟨845423, by rfl⟩ : syracuseStep 1127231 = 1690847) B1690847
theorem B1127259 : Blo 1124630 1127259 := bstep (se 1 (by rfl) ⟨845444, by rfl⟩ : syracuseStep 1127259 = 1690889) B1690889
theorem B4273033 : Blo 1124630 4273033 := bstep (se 2 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 4273033 = 3204775) B3204775
theorem B1127327 : Blo 1124630 1127327 := bstep (se 1 (by rfl) ⟨845495, by rfl⟩ : syracuseStep 1127327 = 1690991) B1690991
theorem B1127407 : Blo 1124630 1127407 := bstep (se 1 (by rfl) ⟨845555, by rfl⟩ : syracuseStep 1127407 = 1691111) B1691111
theorem B1127495 : Blo 1124630 1127495 := bstep (se 1 (by rfl) ⟨845621, by rfl⟩ : syracuseStep 1127495 = 1691243) B1691243
theorem B1127579 : Blo 1124630 1127579 := bstep (se 1 (by rfl) ⟨845684, by rfl⟩ : syracuseStep 1127579 = 1691369) B1691369
theorem B2536631 : Blo 1124630 2536631 := bstep (se 1 (by rfl) ⟨1902473, by rfl⟩ : syracuseStep 2536631 = 3804947) B3804947
theorem B1127675 : Blo 1124630 1127675 := bstep (se 1 (by rfl) ⟨845756, by rfl⟩ : syracuseStep 1127675 = 1691513) B1691513
theorem B1127743 : Blo 1124630 1127743 := bstep (se 1 (by rfl) ⟨845807, by rfl⟩ : syracuseStep 1127743 = 1691615) B1691615
theorem B4273505 : Blo 1124630 4273505 := bstep (se 2 (by rfl) ⟨1602564, by rfl⟩ : syracuseStep 4273505 = 3205129) B3205129
theorem B2405803 : Blo 1124630 2405803 := bstep (se 1 (by rfl) ⟨1804352, by rfl⟩ : syracuseStep 2405803 = 3608705) B3608705
theorem B8107451 : Blo 1124630 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B1127911 : Blo 1124630 1127911 := bstep (se 1 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 1127911 = 1691867) B1691867
theorem B1127919 : Blo 1124630 1127919 := bstep (se 1 (by rfl) ⟨845939, by rfl⟩ : syracuseStep 1127919 = 1691879) B1691879
theorem B1128027 : Blo 1124630 1128027 := bstep (se 1 (by rfl) ⟨846020, by rfl⟩ : syracuseStep 1128027 = 1692041) B1692041
theorem B1128091 : Blo 1124630 1128091 := bstep (se 1 (by rfl) ⟨846068, by rfl⟩ : syracuseStep 1128091 = 1692137) B1692137
theorem B1128175 : Blo 1124630 1128175 := bstep (se 1 (by rfl) ⟨846131, by rfl⟩ : syracuseStep 1128175 = 1692263) B1692263
theorem B2537207 : Blo 1124630 2537207 := bstep (se 1 (by rfl) ⟨1902905, by rfl⟩ : syracuseStep 2537207 = 3805811) B3805811
theorem B1128263 : Blo 1124630 1128263 := bstep (se 1 (by rfl) ⟨846197, by rfl⟩ : syracuseStep 1128263 = 1692395) B1692395
theorem B1128283 : Blo 1124630 1128283 := bstep (se 1 (by rfl) ⟨846212, by rfl⟩ : syracuseStep 1128283 = 1692425) B1692425
theorem B4339585 : Blo 1124630 4339585 := bstep (se 2 (by rfl) ⟨1627344, by rfl⟩ : syracuseStep 4339585 = 3254689) B3254689
theorem B1128351 : Blo 1124630 1128351 := bstep (se 1 (by rfl) ⟨846263, by rfl⟩ : syracuseStep 1128351 = 1692527) B1692527
theorem B2537387 : Blo 1124630 2537387 := bstep (se 1 (by rfl) ⟨1903040, by rfl⟩ : syracuseStep 2537387 = 3806081) B3806081
theorem B2537513 : Blo 1124630 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B1128519 : Blo 1124630 1128519 := bstep (se 1 (by rfl) ⟨846389, by rfl⟩ : syracuseStep 1128519 = 1692779) B1692779
theorem B2537927 : Blo 1124630 2537927 := bstep (se 1 (by rfl) ⟨1903445, by rfl⟩ : syracuseStep 2537927 = 3806891) B3806891
theorem B2538089 : Blo 1124630 2538089 := bstep (se 2 (by rfl) ⟨951783, by rfl⟩ : syracuseStep 2538089 = 1903567) B1903567
theorem B2538143 : Blo 1124630 2538143 := bstep (se 1 (by rfl) ⟨1903607, by rfl⟩ : syracuseStep 2538143 = 3807215) B3807215
theorem B2538287 : Blo 1124630 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B5487455 : Blo 1124630 5487455 := bstep (se 1 (by rfl) ⟨4115591, by rfl⟩ : syracuseStep 5487455 = 8231183) B8231183
theorem B17578939 : Blo 1124630 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B20560877 : Blo 1124630 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B8109089 : Blo 1124630 8109089 := bstep (se 2 (by rfl) ⟨3040908, by rfl⟩ : syracuseStep 8109089 = 6081817) B6081817
theorem B2538719 : Blo 1124630 2538719 := bstep (se 1 (by rfl) ⟨1904039, by rfl⟩ : syracuseStep 2538719 = 3808079) B3808079
theorem B2538935 : Blo 1124630 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B2539115 : Blo 1124630 2539115 := bstep (se 1 (by rfl) ⟨1904336, by rfl⟩ : syracuseStep 2539115 = 3808673) B3808673
theorem B1687151 : Blo 1124630 1687151 := bstep (se 1 (by rfl) ⟨1265363, by rfl⟩ : syracuseStep 1687151 = 2530727) B2530727
theorem B4275935 : Blo 1124630 4275935 := bstep (se 1 (by rfl) ⟨3206951, by rfl⟩ : syracuseStep 4275935 = 6413903) B6413903
theorem B1687271 : Blo 1124630 1687271 := bstep (se 1 (by rfl) ⟨1265453, by rfl⟩ : syracuseStep 1687271 = 2530907) B2530907
theorem B2539385 : Blo 1124630 2539385 := bstep (se 2 (by rfl) ⟨952269, by rfl⟩ : syracuseStep 2539385 = 1904539) B1904539
theorem B1687463 : Blo 1124630 1687463 := bstep (se 1 (by rfl) ⟨1265597, by rfl⟩ : syracuseStep 1687463 = 2531195) B2531195
theorem B15417325 : Blo 1124630 15417325 := bstep (se 3 (by rfl) ⟨2890748, by rfl⟩ : syracuseStep 15417325 = 5781497) B5781497
theorem B1687787 : Blo 1124630 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B1687847 : Blo 1124630 1687847 := bstep (se 1 (by rfl) ⟨1265885, by rfl⟩ : syracuseStep 1687847 = 2531771) B2531771
theorem B5489021 : Blo 1124630 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B2703743 : Blo 1124630 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B19219355 : Blo 1124630 19219355 := bstep (se 1 (by rfl) ⟨14414516, by rfl⟩ : syracuseStep 19219355 = 28829033) B28829033
theorem B1688519 : Blo 1124630 1688519 := bstep (se 1 (by rfl) ⟨1266389, by rfl⟩ : syracuseStep 1688519 = 2532779) B2532779
theorem B1688687 : Blo 1124630 1688687 := bstep (se 1 (by rfl) ⟨1266515, by rfl⟩ : syracuseStep 1688687 = 2533031) B2533031
theorem B1688879 : Blo 1124630 1688879 := bstep (se 1 (by rfl) ⟨1266659, by rfl⟩ : syracuseStep 1688879 = 2533319) B2533319
theorem B1689083 : Blo 1124630 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B1689119 : Blo 1124630 1689119 := bstep (se 1 (by rfl) ⟨1266839, by rfl⟩ : syracuseStep 1689119 = 2533679) B2533679
theorem B1951295 : Blo 1124630 1951295 := bstep (se 1 (by rfl) ⟨1463471, by rfl⟩ : syracuseStep 1951295 = 2926943) B2926943
theorem B1689263 : Blo 1124630 1689263 := bstep (se 1 (by rfl) ⟨1266947, by rfl⟩ : syracuseStep 1689263 = 2533895) B2533895
theorem B1689383 : Blo 1124630 1689383 := bstep (se 1 (by rfl) ⟨1267037, by rfl⟩ : syracuseStep 1689383 = 2534075) B2534075
theorem B1689935 : Blo 1124630 1689935 := bstep (se 1 (by rfl) ⟨1267451, by rfl⟩ : syracuseStep 1689935 = 2534903) B2534903
theorem B1689983 : Blo 1124630 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B1690025 : Blo 1124630 1690025 := bstep (se 2 (by rfl) ⟨633759, by rfl⟩ : syracuseStep 1690025 = 1267519) B1267519
theorem B6179399 : Blo 1124630 6179399 := bstep (se 1 (by rfl) ⟨4634549, by rfl⟩ : syracuseStep 6179399 = 9269099) B9269099
theorem B1690409 : Blo 1124630 1690409 := bstep (se 2 (by rfl) ⟨633903, by rfl⟩ : syracuseStep 1690409 = 1267807) B1267807
theorem B2706259 : Blo 1124630 2706259 := bstep (se 1 (by rfl) ⟨2029694, by rfl⟩ : syracuseStep 2706259 = 4059389) B4059389
theorem B4279169 : Blo 1124630 4279169 := bstep (se 2 (by rfl) ⟨1604688, by rfl⟩ : syracuseStep 4279169 = 3209377) B3209377
theorem B1690619 : Blo 1124630 1690619 := bstep (se 1 (by rfl) ⟨1267964, by rfl⟩ : syracuseStep 1690619 = 2535929) B2535929
theorem B3427337 : Blo 1124630 3427337 := bstep (se 2 (by rfl) ⟨1285251, by rfl⟩ : syracuseStep 3427337 = 2570503) B2570503
theorem B1690679 : Blo 1124630 1690679 := bstep (se 1 (by rfl) ⟨1268009, by rfl⟩ : syracuseStep 1690679 = 2536019) B2536019
theorem B4279351 : Blo 1124630 4279351 := bstep (se 1 (by rfl) ⟨3209513, by rfl⟩ : syracuseStep 4279351 = 6419027) B6419027
theorem B1690799 : Blo 1124630 1690799 := bstep (se 1 (by rfl) ⟨1268099, by rfl⟩ : syracuseStep 1690799 = 2536199) B2536199
theorem B2280935 : Blo 1124630 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B501894719 : Blo 1124630 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B1691519 : Blo 1124630 1691519 := bstep (se 1 (by rfl) ⟨1268639, by rfl⟩ : syracuseStep 1691519 = 2537279) B2537279
theorem B1265647 : Blo 1124630 1265647 := bstep (se 1 (by rfl) ⟨949235, by rfl⟩ : syracuseStep 1265647 = 1898471) B1898471
theorem B6410279 : Blo 1124630 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B1691711 : Blo 1124630 1691711 := bstep (se 1 (by rfl) ⟨1268783, by rfl⟩ : syracuseStep 1691711 = 2537567) B2537567
theorem B4804703 : Blo 1124630 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B5132411 : Blo 1124630 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B1265791 : Blo 1124630 1265791 := bstep (se 1 (by rfl) ⟨949343, by rfl⟩ : syracuseStep 1265791 = 1898687) B1898687
theorem B1691945 : Blo 1124630 1691945 := bstep (se 2 (by rfl) ⟨634479, by rfl⟩ : syracuseStep 1691945 = 1268959) B1268959
theorem B1626491 : Blo 1124630 1626491 := bstep (se 1 (by rfl) ⟨1219868, by rfl⟩ : syracuseStep 1626491 = 2439737) B2439737
theorem B37048751 : Blo 1124630 37048751 := bstep (se 1 (by rfl) ⟨27786563, by rfl⟩ : syracuseStep 37048751 = 55573127) B55573127
theorem B4280809 : Blo 1124630 4280809 := bstep (se 2 (by rfl) ⟨1605303, by rfl⟩ : syracuseStep 4280809 = 3210607) B3210607
theorem B1692215 : Blo 1124630 1692215 := bstep (se 1 (by rfl) ⟨1269161, by rfl⟩ : syracuseStep 1692215 = 2538323) B2538323
theorem B1692575 : Blo 1124630 1692575 := bstep (se 1 (by rfl) ⟨1269431, by rfl⟩ : syracuseStep 1692575 = 2538863) B2538863
theorem B1692767 : Blo 1124630 1692767 := bstep (se 1 (by rfl) ⟨1269575, by rfl⟩ : syracuseStep 1692767 = 2539151) B2539151
theorem B6411419 : Blo 1124630 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B1692827 : Blo 1124630 1692827 := bstep (se 1 (by rfl) ⟨1269620, by rfl⟩ : syracuseStep 1692827 = 2539241) B2539241
theorem B1268383 : Blo 1124630 1268383 := bstep (se 1 (by rfl) ⟨951287, by rfl⟩ : syracuseStep 1268383 = 1902575) B1902575
theorem B1203055 : Blo 1124630 1203055 := bstep (se 1 (by rfl) ⟨902291, by rfl⟩ : syracuseStep 1203055 = 1804583) B1804583
theorem B1203431 : Blo 1124630 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B4284029 : Blo 1124630 4284029 := bstep (se 3 (by rfl) ⟨803255, by rfl⟩ : syracuseStep 4284029 = 1606511) B1606511
theorem B1269535 : Blo 1124630 1269535 := bstep (se 1 (by rfl) ⟨952151, by rfl⟩ : syracuseStep 1269535 = 1904303) B1904303
theorem B14442401 : Blo 1124630 14442401 := bstep (se 2 (by rfl) ⟨5415900, by rfl⟩ : syracuseStep 14442401 = 10831801) B10831801
theorem B4284697 : Blo 1124630 4284697 := bstep (se 2 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 4284697 = 3213523) B3213523
theorem B3203489 : Blo 1124630 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B133325261 : Blo 1124630 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B4056851 : Blo 1124630 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B3205003 : Blo 1124630 3205003 := bstep (se 1 (by rfl) ⟨2403752, by rfl⟩ : syracuseStep 3205003 = 4807505) B4807505
theorem B9136091 : Blo 1124630 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B43379641 : Blo 1124630 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B8547281 : Blo 1124630 8547281 := bstep (se 2 (by rfl) ⟨3205230, by rfl⟩ : syracuseStep 8547281 = 6410461) B6410461
theorem B3796253 : Blo 1124630 3796253 := bstep (se 3 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 3796253 = 1423595) B1423595
theorem B10841951 : Blo 1124630 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B14413697 : Blo 1124630 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B3796955 : Blo 1124630 3796955 := bstep (se 1 (by rfl) ⟨2847716, by rfl⟩ : syracuseStep 3796955 = 5695433) B5695433
theorem B6844379 : Blo 1124630 6844379 := bstep (se 1 (by rfl) ⟨5133284, by rfl⟩ : syracuseStep 6844379 = 10266569) B10266569
theorem B3797225 : Blo 1124630 3797225 := bstep (se 2 (by rfl) ⟨1423959, by rfl⟩ : syracuseStep 3797225 = 2847919) B2847919
theorem B43381331 : Blo 1124630 43381331 := bstep (se 1 (by rfl) ⟨32535998, by rfl⟩ : syracuseStep 43381331 = 65071997) B65071997
theorem B6419209 : Blo 1124630 6419209 := bstep (se 2 (by rfl) ⟨2407203, by rfl⟩ : syracuseStep 6419209 = 4814407) B4814407
theorem B3208079 : Blo 1124630 3208079 := bstep (se 1 (by rfl) ⟨2406059, by rfl⟩ : syracuseStep 3208079 = 4812119) B4812119
theorem B2847737 : Blo 1124630 2847737 := bstep (se 2 (by rfl) ⟨1067901, by rfl⟩ : syracuseStep 2847737 = 2135803) B2135803
theorem B3208511 : Blo 1124630 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B3798845 : Blo 1124630 3798845 := bstep (se 3 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 3798845 = 1424567) B1424567
theorem B3799223 : Blo 1124630 3799223 := bstep (se 1 (by rfl) ⟨2849417, by rfl⟩ : syracuseStep 3799223 = 5698835) B5698835
theorem B6847105 : Blo 1124630 6847105 := bstep (se 2 (by rfl) ⟨2567664, by rfl⟩ : syracuseStep 6847105 = 5135329) B5135329
theorem B3799817 : Blo 1124630 3799817 := bstep (se 2 (by rfl) ⟨1424931, by rfl⟩ : syracuseStep 3799817 = 2849863) B2849863
theorem B3209993 : Blo 1124630 3209993 := bstep (se 2 (by rfl) ⟨1203747, by rfl⟩ : syracuseStep 3209993 = 2407495) B2407495
theorem B1899625 : Blo 1124630 1899625 := bstep (se 2 (by rfl) ⟨712359, by rfl⟩ : syracuseStep 1899625 = 1424719) B1424719
theorem B8125697 : Blo 1124630 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B1899983 : Blo 1124630 1899983 := bstep (se 1 (by rfl) ⟨1424987, by rfl⟩ : syracuseStep 1899983 = 2849975) B2849975
theorem B7142863 : Blo 1124630 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B2850299 : Blo 1124630 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B28868399 : Blo 1124630 28868399 := bstep (se 1 (by rfl) ⟨21651299, by rfl⟩ : syracuseStep 28868399 = 43302599) B43302599
theorem B6422651 : Blo 1124630 6422651 := bstep (se 1 (by rfl) ⟨4816988, by rfl⟩ : syracuseStep 6422651 = 9633977) B9633977
theorem B1802495 : Blo 1124630 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B1900955 : Blo 1124630 1900955 := bstep (se 1 (by rfl) ⟨1425716, by rfl⟩ : syracuseStep 1900955 = 2851433) B2851433
theorem B12812903 : Blo 1124630 12812903 := bstep (se 1 (by rfl) ⟨9609677, by rfl⟩ : syracuseStep 12812903 = 19219355) B19219355
theorem B8127287 : Blo 1124630 8127287 := bstep (se 1 (by rfl) ⟨6095465, by rfl⟩ : syracuseStep 8127287 = 12190931) B12190931
theorem B7308089 : Blo 1124630 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B2851969 : Blo 1124630 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B12191057 : Blo 1124630 12191057 := bstep (se 2 (by rfl) ⟨4571646, by rfl⟩ : syracuseStep 12191057 = 9143293) B9143293
theorem B3606079 : Blo 1124630 3606079 := bstep (se 1 (by rfl) ⟨2704559, by rfl⟩ : syracuseStep 3606079 = 5409119) B5409119
theorem B2852729 : Blo 1124630 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B2852779 : Blo 1124630 2852779 := bstep (se 1 (by rfl) ⟨2139584, by rfl⟩ : syracuseStep 2852779 = 4279169) B4279169
theorem B7211207 : Blo 1124630 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B54364445 : Blo 1124630 54364445 := bstep (se 3 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 54364445 = 20386667) B20386667
theorem B7211359 : Blo 1124630 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B334596479 : Blo 1124630 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B5704667 : Blo 1124630 5704667 := bstep (se 1 (by rfl) ⟨4278500, by rfl⟩ : syracuseStep 5704667 = 8557001) B8557001
theorem B2854217 : Blo 1124630 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B8556029 : Blo 1124630 8556029 := bstep (se 3 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 8556029 = 3208511) B3208511
theorem B3608345 : Blo 1124630 3608345 := bstep (se 2 (by rfl) ⟨1353129, by rfl⟩ : syracuseStep 3608345 = 2706259) B2706259
theorem B3805055 : Blo 1124630 3805055 := bstep (se 1 (by rfl) ⟨2853791, by rfl⟩ : syracuseStep 3805055 = 5707583) B5707583
theorem B57839521 : Blo 1124630 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B5705801 : Blo 1124630 5705801 := bstep (se 2 (by rfl) ⟨2139675, by rfl⟩ : syracuseStep 5705801 = 4279351) B4279351
theorem B3805433 : Blo 1124630 3805433 := bstep (se 2 (by rfl) ⟨1427037, by rfl⟩ : syracuseStep 3805433 = 2854075) B2854075
theorem B10293799 : Blo 1124630 10293799 := bstep (se 1 (by rfl) ⟨7720349, by rfl⟩ : syracuseStep 10293799 = 15440699) B15440699
theorem B10818269 : Blo 1124630 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B2856019 : Blo 1124630 2856019 := bstep (se 1 (by rfl) ⟨2142014, by rfl⟩ : syracuseStep 2856019 = 4284029) B4284029
theorem B2135659 : Blo 1124630 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B12850811 : Blo 1124630 12850811 := bstep (se 1 (by rfl) ⟨9638108, by rfl⟩ : syracuseStep 12850811 = 19276217) B19276217
theorem B3806945 : Blo 1124630 3806945 := bstep (se 2 (by rfl) ⟨1427604, by rfl⟩ : syracuseStep 3806945 = 2855209) B2855209
theorem B5707745 : Blo 1124630 5707745 := bstep (se 2 (by rfl) ⟨2140404, by rfl⟩ : syracuseStep 5707745 = 4280809) B4280809
theorem B20813813 : Blo 1124630 20813813 := bstep (se 5 (by rfl) ⟨975647, by rfl⟩ : syracuseStep 20813813 = 1951295) B1951295
theorem B8558945 : Blo 1124630 8558945 := bstep (se 2 (by rfl) ⟨3209604, by rfl⟩ : syracuseStep 8558945 = 6419209) B6419209
theorem B5708555 : Blo 1124630 5708555 := bstep (se 1 (by rfl) ⟨4281416, by rfl⟩ : syracuseStep 5708555 = 8562833) B8562833
theorem B20061209 : Blo 1124630 20061209 := bstep (se 2 (by rfl) ⟨7522953, by rfl⟩ : syracuseStep 20061209 = 15045907) B15045907
theorem B6495527 : Blo 1124630 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B2530835 : Blo 1124630 2530835 := bstep (se 1 (by rfl) ⟨1898126, by rfl⟩ : syracuseStep 2530835 = 3796253) B3796253
theorem B3808889 : Blo 1124630 3808889 := bstep (se 2 (by rfl) ⟨1428333, by rfl⟩ : syracuseStep 3808889 = 2856667) B2856667
theorem B3808943 : Blo 1124630 3808943 := bstep (se 1 (by rfl) ⟨2856707, by rfl⟩ : syracuseStep 3808943 = 5713415) B5713415
theorem B9609131 : Blo 1124630 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B2531303 : Blo 1124630 2531303 := bstep (se 1 (by rfl) ⟨1898477, by rfl⟩ : syracuseStep 2531303 = 3796955) B3796955
theorem B2531483 : Blo 1124630 2531483 := bstep (se 1 (by rfl) ⟨1898612, by rfl⟩ : syracuseStep 2531483 = 3797225) B3797225
theorem B5710013 : Blo 1124630 5710013 := bstep (se 3 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 5710013 = 2141255) B2141255
theorem B5710175 : Blo 1124630 5710175 := bstep (se 1 (by rfl) ⟨4282631, by rfl⟩ : syracuseStep 5710175 = 8565263) B8565263
theorem B61612559 : Blo 1124630 61612559 := bstep (se 1 (by rfl) ⟨46209419, by rfl⟩ : syracuseStep 61612559 = 92418839) B92418839
theorem B2138719 : Blo 1124630 2138719 := bstep (se 1 (by rfl) ⟨1604039, by rfl⟩ : syracuseStep 2138719 = 3208079) B3208079
theorem B2532563 : Blo 1124630 2532563 := bstep (se 1 (by rfl) ⟨1899422, by rfl⟩ : syracuseStep 2532563 = 3798845) B3798845
theorem B23438585 : Blo 1124630 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B2532815 : Blo 1124630 2532815 := bstep (se 1 (by rfl) ⟨1899611, by rfl⟩ : syracuseStep 2532815 = 3799223) B3799223
theorem B2532833 : Blo 1124630 2532833 := bstep (se 2 (by rfl) ⟨949812, by rfl⟩ : syracuseStep 2532833 = 1899625) B1899625
theorem B2533211 : Blo 1124630 2533211 := bstep (se 1 (by rfl) ⟨1899908, by rfl⟩ : syracuseStep 2533211 = 3799817) B3799817
theorem B2139995 : Blo 1124630 2139995 := bstep (se 1 (by rfl) ⟨1604996, by rfl⟩ : syracuseStep 2139995 = 3209993) B3209993
theorem B13707251 : Blo 1124630 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B23144453 : Blo 1124630 23144453 := bstep (se 4 (by rfl) ⟨2169792, by rfl⟩ : syracuseStep 23144453 = 4339585) B4339585
theorem B5417131 : Blo 1124630 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B1124767 : Blo 1124630 1124767 := bstep (se 1 (by rfl) ⟨843575, by rfl⟩ : syracuseStep 1124767 = 1687151) B1687151
theorem B1124847 : Blo 1124630 1124847 := bstep (se 1 (by rfl) ⟨843635, by rfl⟩ : syracuseStep 1124847 = 1687271) B1687271
theorem B19245599 : Blo 1124630 19245599 := bstep (se 1 (by rfl) ⟨14434199, by rfl⟩ : syracuseStep 19245599 = 28868399) B28868399
theorem B1124975 : Blo 1124630 1124975 := bstep (se 1 (by rfl) ⟨843731, by rfl⟩ : syracuseStep 1124975 = 1687463) B1687463
theorem B20556433 : Blo 1124630 20556433 := bstep (se 2 (by rfl) ⟨7708662, by rfl⟩ : syracuseStep 20556433 = 15417325) B15417325
theorem B2534183 : Blo 1124630 2534183 := bstep (se 1 (by rfl) ⟨1900637, by rfl⟩ : syracuseStep 2534183 = 3801275) B3801275
theorem B2140967 : Blo 1124630 2140967 := bstep (se 1 (by rfl) ⟨1605725, by rfl⟩ : syracuseStep 2140967 = 3211451) B3211451
theorem B1125191 : Blo 1124630 1125191 := bstep (se 1 (by rfl) ⟨843893, by rfl⟩ : syracuseStep 1125191 = 1687787) B1687787
theorem B1125231 : Blo 1124630 1125231 := bstep (se 1 (by rfl) ⟨843923, by rfl⟩ : syracuseStep 1125231 = 1687847) B1687847
theorem B5712929 : Blo 1124630 5712929 := bstep (se 2 (by rfl) ⟨2142348, by rfl⟩ : syracuseStep 5712929 = 4284697) B4284697
theorem B1125679 : Blo 1124630 1125679 := bstep (se 1 (by rfl) ⟨844259, by rfl⟩ : syracuseStep 1125679 = 1688519) B1688519
theorem B1125791 : Blo 1124630 1125791 := bstep (se 1 (by rfl) ⟨844343, by rfl⟩ : syracuseStep 1125791 = 1688687) B1688687
theorem B9612755 : Blo 1124630 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B1125919 : Blo 1124630 1125919 := bstep (se 1 (by rfl) ⟨844439, by rfl⟩ : syracuseStep 1125919 = 1688879) B1688879
theorem B14462495 : Blo 1124630 14462495 := bstep (se 1 (by rfl) ⟨10846871, by rfl⟩ : syracuseStep 14462495 = 21693743) B21693743
theorem B4337309 : Blo 1124630 4337309 := bstep (se 3 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 4337309 = 1626491) B1626491
theorem B1126055 : Blo 1124630 1126055 := bstep (se 1 (by rfl) ⟨844541, by rfl⟩ : syracuseStep 1126055 = 1689083) B1689083
theorem B1126079 : Blo 1124630 1126079 := bstep (se 1 (by rfl) ⟨844559, by rfl⟩ : syracuseStep 1126079 = 1689119) B1689119
theorem B1126175 : Blo 1124630 1126175 := bstep (se 1 (by rfl) ⟨844631, by rfl⟩ : syracuseStep 1126175 = 1689263) B1689263
theorem B1126255 : Blo 1124630 1126255 := bstep (se 1 (by rfl) ⟨844691, by rfl⟩ : syracuseStep 1126255 = 1689383) B1689383
theorem B1126623 : Blo 1124630 1126623 := bstep (se 1 (by rfl) ⟨844967, by rfl⟩ : syracuseStep 1126623 = 1689935) B1689935
theorem B1126655 : Blo 1124630 1126655 := bstep (se 1 (by rfl) ⟨844991, by rfl⟩ : syracuseStep 1126655 = 1689983) B1689983
theorem B2142463 : Blo 1124630 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B1126683 : Blo 1124630 1126683 := bstep (se 1 (by rfl) ⟨845012, by rfl⟩ : syracuseStep 1126683 = 1690025) B1690025
theorem B1126939 : Blo 1124630 1126939 := bstep (se 1 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 1126939 = 1690409) B1690409
theorem B1127079 : Blo 1124630 1127079 := bstep (se 1 (by rfl) ⟨845309, by rfl⟩ : syracuseStep 1127079 = 1690619) B1690619
theorem B1127119 : Blo 1124630 1127119 := bstep (se 1 (by rfl) ⟨845339, by rfl⟩ : syracuseStep 1127119 = 1690679) B1690679
theorem B1127199 : Blo 1124630 1127199 := bstep (se 1 (by rfl) ⟨845399, by rfl⟩ : syracuseStep 1127199 = 1690799) B1690799
theorem B2536361 : Blo 1124630 2536361 := bstep (se 2 (by rfl) ⟨951135, by rfl⟩ : syracuseStep 2536361 = 1902271) B1902271
theorem B1520623 : Blo 1124630 1520623 := bstep (se 1 (by rfl) ⟨1140467, by rfl⟩ : syracuseStep 1520623 = 2280935) B2280935
theorem B4273337 : Blo 1124630 4273337 := bstep (se 2 (by rfl) ⟨1602501, by rfl⟩ : syracuseStep 4273337 = 3205003) B3205003
theorem B1127679 : Blo 1124630 1127679 := bstep (se 1 (by rfl) ⟨845759, by rfl⟩ : syracuseStep 1127679 = 1691519) B1691519
theorem B4273519 : Blo 1124630 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B1127807 : Blo 1124630 1127807 := bstep (se 1 (by rfl) ⟨845855, by rfl⟩ : syracuseStep 1127807 = 1691711) B1691711
theorem B3421607 : Blo 1124630 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B1127963 : Blo 1124630 1127963 := bstep (se 1 (by rfl) ⟨845972, by rfl⟩ : syracuseStep 1127963 = 1691945) B1691945
theorem B12170861 : Blo 1124630 12170861 := bstep (se 3 (by rfl) ⟨2282036, by rfl⟩ : syracuseStep 12170861 = 4564073) B4564073
theorem B1128143 : Blo 1124630 1128143 := bstep (se 1 (by rfl) ⟨846107, by rfl⟩ : syracuseStep 1128143 = 1692215) B1692215
theorem B1128383 : Blo 1124630 1128383 := bstep (se 1 (by rfl) ⟨846287, by rfl⟩ : syracuseStep 1128383 = 1692575) B1692575
theorem B1423423 : Blo 1124630 1423423 := bstep (se 1 (by rfl) ⟨1067567, by rfl⟩ : syracuseStep 1423423 = 2135135) B2135135
theorem B1128511 : Blo 1124630 1128511 := bstep (se 1 (by rfl) ⟨846383, by rfl⟩ : syracuseStep 1128511 = 1692767) B1692767
theorem B4274279 : Blo 1124630 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B1128551 : Blo 1124630 1128551 := bstep (se 1 (by rfl) ⟨846413, by rfl⟩ : syracuseStep 1128551 = 1692827) B1692827
theorem B1423919 : Blo 1124630 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B12827483 : Blo 1124630 12827483 := bstep (se 1 (by rfl) ⟨9620612, by rfl⟩ : syracuseStep 12827483 = 19241225) B19241225
theorem B2538665 : Blo 1124630 2538665 := bstep (se 2 (by rfl) ⟨951999, by rfl⟩ : syracuseStep 2538665 = 1903999) B1903999
theorem B1687007 : Blo 1124630 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B1687259 : Blo 1124630 1687259 := bstep (se 1 (by rfl) ⟨1265444, by rfl⟩ : syracuseStep 1687259 = 2530889) B2530889
theorem B46186433 : Blo 1124630 46186433 := bstep (se 2 (by rfl) ⟨17319912, by rfl⟩ : syracuseStep 46186433 = 34639825) B34639825
theorem B1687529 : Blo 1124630 1687529 := bstep (se 2 (by rfl) ⟨632823, by rfl⟩ : syracuseStep 1687529 = 1265647) B1265647
theorem B1687721 : Blo 1124630 1687721 := bstep (se 2 (by rfl) ⟨632895, by rfl⟩ : syracuseStep 1687721 = 1265791) B1265791
theorem B88883507 : Blo 1124630 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B1688039 : Blo 1124630 1688039 := bstep (se 1 (by rfl) ⟨1266029, by rfl⟩ : syracuseStep 1688039 = 2532059) B2532059
theorem B2933279 : Blo 1124630 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B1688315 : Blo 1124630 1688315 := bstep (se 1 (by rfl) ⟨1266236, by rfl⟩ : syracuseStep 1688315 = 2532473) B2532473
theorem B23119019 : Blo 1124630 23119019 := bstep (se 1 (by rfl) ⟨17339264, by rfl⟩ : syracuseStep 23119019 = 34678529) B34678529
theorem B1688759 : Blo 1124630 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B1688903 : Blo 1124630 1688903 := bstep (se 1 (by rfl) ⟨1266677, by rfl⟩ : syracuseStep 1688903 = 2533355) B2533355
theorem B1688999 : Blo 1124630 1688999 := bstep (se 1 (by rfl) ⟨1266749, by rfl⟩ : syracuseStep 1688999 = 2533499) B2533499
theorem B1689179 : Blo 1124630 1689179 := bstep (se 1 (by rfl) ⟨1266884, by rfl⟩ : syracuseStep 1689179 = 2533769) B2533769
theorem B1427483 : Blo 1124630 1427483 := bstep (se 1 (by rfl) ⟨1070612, by rfl⟩ : syracuseStep 1427483 = 2141225) B2141225
theorem B1689647 : Blo 1124630 1689647 := bstep (se 1 (by rfl) ⟨1267235, by rfl⟩ : syracuseStep 1689647 = 2534471) B2534471
theorem B1689911 : Blo 1124630 1689911 := bstep (se 1 (by rfl) ⟨1267433, by rfl⟩ : syracuseStep 1689911 = 2534867) B2534867
theorem B1690091 : Blo 1124630 1690091 := bstep (se 1 (by rfl) ⟨1267568, by rfl⟩ : syracuseStep 1690091 = 2535137) B2535137
theorem B7227967 : Blo 1124630 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B1690331 : Blo 1124630 1690331 := bstep (se 1 (by rfl) ⟨1267748, by rfl⟩ : syracuseStep 1690331 = 2535497) B2535497
theorem B1428187 : Blo 1124630 1428187 := bstep (se 1 (by rfl) ⟨1071140, by rfl⟩ : syracuseStep 1428187 = 2142281) B2142281
theorem B1690367 : Blo 1124630 1690367 := bstep (se 1 (by rfl) ⟨1267775, by rfl⟩ : syracuseStep 1690367 = 2535551) B2535551
theorem B6409003 : Blo 1124630 6409003 := bstep (se 1 (by rfl) ⟨4806752, by rfl⟩ : syracuseStep 6409003 = 9613505) B9613505
theorem B28855277 : Blo 1124630 28855277 := bstep (se 3 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 28855277 = 10820729) B10820729
theorem B28920887 : Blo 1124630 28920887 := bstep (se 1 (by rfl) ⟨21690665, by rfl⟩ : syracuseStep 28920887 = 43381331) B43381331
theorem B21941405 : Blo 1124630 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B1691087 : Blo 1124630 1691087 := bstep (se 1 (by rfl) ⟨1268315, by rfl⟩ : syracuseStep 1691087 = 2536631) B2536631
theorem B9129473 : Blo 1124630 9129473 := bstep (se 2 (by rfl) ⟨3423552, by rfl⟩ : syracuseStep 9129473 = 6847105) B6847105
theorem B1691177 : Blo 1124630 1691177 := bstep (se 2 (by rfl) ⟨634191, by rfl⟩ : syracuseStep 1691177 = 1268383) B1268383
theorem B1691471 : Blo 1124630 1691471 := bstep (se 1 (by rfl) ⟨1268603, by rfl⟩ : syracuseStep 1691471 = 2537207) B2537207
theorem B1691591 : Blo 1124630 1691591 := bstep (se 1 (by rfl) ⟨1268693, by rfl⟩ : syracuseStep 1691591 = 2537387) B2537387
theorem B1691675 : Blo 1124630 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B1691951 : Blo 1124630 1691951 := bstep (se 1 (by rfl) ⟨1268963, by rfl⟩ : syracuseStep 1691951 = 2537927) B2537927
theorem B1692059 : Blo 1124630 1692059 := bstep (se 1 (by rfl) ⟨1269044, by rfl⟩ : syracuseStep 1692059 = 2538089) B2538089
theorem B1692095 : Blo 1124630 1692095 := bstep (se 1 (by rfl) ⟨1269071, by rfl⟩ : syracuseStep 1692095 = 2538143) B2538143
theorem B1692191 : Blo 1124630 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B3658303 : Blo 1124630 3658303 := bstep (se 1 (by rfl) ⟨2743727, by rfl⟩ : syracuseStep 3658303 = 5487455) B5487455
theorem B9523817 : Blo 1124630 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B1692479 : Blo 1124630 1692479 := bstep (se 1 (by rfl) ⟨1269359, by rfl⟩ : syracuseStep 1692479 = 2538719) B2538719
theorem B1692623 : Blo 1124630 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B1266655 : Blo 1124630 1266655 := bstep (se 1 (by rfl) ⟨949991, by rfl⟩ : syracuseStep 1266655 = 1899983) B1899983
theorem B1692713 : Blo 1124630 1692713 := bstep (se 2 (by rfl) ⟨634767, by rfl⟩ : syracuseStep 1692713 = 1269535) B1269535
theorem B1692743 : Blo 1124630 1692743 := bstep (se 1 (by rfl) ⟨1269557, by rfl⟩ : syracuseStep 1692743 = 2539115) B2539115
theorem B1692923 : Blo 1124630 1692923 := bstep (se 1 (by rfl) ⟨1269692, by rfl⟩ : syracuseStep 1692923 = 2539385) B2539385
theorem B1267231 : Blo 1124630 1267231 := bstep (se 1 (by rfl) ⟨950423, by rfl⟩ : syracuseStep 1267231 = 1900847) B1900847
theorem B3659347 : Blo 1124630 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B17357125 : Blo 1124630 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B1268095 : Blo 1124630 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B4807421 : Blo 1124630 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B32529437 : Blo 1124630 32529437 := bstep (se 3 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 32529437 = 12198539) B12198539
theorem B4119599 : Blo 1124630 4119599 := bstep (se 1 (by rfl) ⟨3089699, by rfl⟩ : syracuseStep 4119599 = 6179399) B6179399
theorem B4283513 : Blo 1124630 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B11885867 : Blo 1124630 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B2284891 : Blo 1124630 2284891 := bstep (se 1 (by rfl) ⟨1713668, by rfl⟩ : syracuseStep 2284891 = 3427337) B3427337
theorem B20537387 : Blo 1124630 20537387 := bstep (se 1 (by rfl) ⟨15403040, by rfl⟩ : syracuseStep 20537387 = 30806081) B30806081
theorem B3203135 : Blo 1124630 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B24699167 : Blo 1124630 24699167 := bstep (se 1 (by rfl) ⟨18524375, by rfl⟩ : syracuseStep 24699167 = 37048751) B37048751
theorem B13001957 : Blo 1124630 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B6416293 : Blo 1124630 6416293 := bstep (se 4 (by rfl) ⟨601527, by rfl⟩ : syracuseStep 6416293 = 1203055) B1203055
theorem B9628267 : Blo 1124630 9628267 := bstep (se 1 (by rfl) ⟨7221200, by rfl⟩ : syracuseStep 9628267 = 14442401) B14442401
theorem B2058907 : Blo 1124630 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B832236605 : Blo 1124630 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B5697377 : Blo 1124630 5697377 := bstep (se 2 (by rfl) ⟨2136516, by rfl⟩ : syracuseStep 5697377 = 4273033) B4273033
theorem B6090727 : Blo 1124630 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B2846927 : Blo 1124630 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B3207737 : Blo 1124630 3207737 := bstep (se 2 (by rfl) ⟨1202901, by rfl⟩ : syracuseStep 3207737 = 2405803) B2405803
theorem B5698187 : Blo 1124630 5698187 := bstep (se 1 (by rfl) ⟨4273640, by rfl⟩ : syracuseStep 5698187 = 8547281) B8547281
theorem B2847899 : Blo 1124630 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B13006295 : Blo 1124630 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B3209149 : Blo 1124630 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B1898491 : Blo 1124630 1898491 := bstep (se 1 (by rfl) ⟨1423868, by rfl⟩ : syracuseStep 1898491 = 2847737) B2847737
theorem B2849003 : Blo 1124630 2849003 := bstep (se 1 (by rfl) ⟨2136752, by rfl⟩ : syracuseStep 2849003 = 4273505) B4273505
theorem B5404967 : Blo 1124630 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B78084809 : Blo 1124630 78084809 := bstep (se 2 (by rfl) ⟨29281803, by rfl⟩ : syracuseStep 78084809 = 58563607) B58563607
theorem B14646521 : Blo 1124630 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B5406059 : Blo 1124630 5406059 := bstep (se 1 (by rfl) ⟨4054544, by rfl⟩ : syracuseStep 5406059 = 8109089) B8109089
theorem B1900199 : Blo 1124630 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B2850623 : Blo 1124630 2850623 := bstep (se 1 (by rfl) ⟨2137967, by rfl⟩ : syracuseStep 2850623 = 4275935) B4275935
theorem B18251677 : Blo 1124630 18251677 := bstep (se 3 (by rfl) ⟨3422189, by rfl⟩ : syracuseStep 18251677 = 6844379) B6844379
theorem B2850785 : Blo 1124630 2850785 := bstep (se 2 (by rfl) ⟨1069044, by rfl⟩ : syracuseStep 2850785 = 2138089) B2138089
theorem B2851625 : Blo 1124630 2851625 := bstep (se 2 (by rfl) ⟨1069359, by rfl⟩ : syracuseStep 2851625 = 2138719) B2138719
theorem B8127371 : Blo 1124630 8127371 := bstep (se 1 (by rfl) ⟨6095528, by rfl⟩ : syracuseStep 8127371 = 12191057) B12191057
theorem B1901819 : Blo 1124630 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B3802625 : Blo 1124630 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B36242963 : Blo 1124630 36242963 := bstep (se 1 (by rfl) ⟨27182222, by rfl⟩ : syracuseStep 36242963 = 54364445) B54364445
theorem B3803111 : Blo 1124630 3803111 := bstep (se 1 (by rfl) ⟨2852333, by rfl⟩ : syracuseStep 3803111 = 5704667) B5704667
theorem B19236851 : Blo 1124630 19236851 := bstep (se 1 (by rfl) ⟨14427638, by rfl⟩ : syracuseStep 19236851 = 28855277) B28855277
theorem B1902811 : Blo 1124630 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B5704019 : Blo 1124630 5704019 := bstep (se 1 (by rfl) ⟨4278014, by rfl⟩ : syracuseStep 5704019 = 8556029) B8556029
theorem B8555057 : Blo 1124630 8555057 := bstep (se 2 (by rfl) ⟨3208146, by rfl⟩ : syracuseStep 8555057 = 6416293) B6416293
theorem B3803705 : Blo 1124630 3803705 := bstep (se 2 (by rfl) ⟨1426389, by rfl⟩ : syracuseStep 3803705 = 2852779) B2852779
theorem B3803867 : Blo 1124630 3803867 := bstep (se 1 (by rfl) ⟨2852900, by rfl⟩ : syracuseStep 3803867 = 5705801) B5705801
theorem B7212179 : Blo 1124630 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B9637289 : Blo 1124630 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B1904249 : Blo 1124630 1904249 := bstep (se 2 (by rfl) ⟨714093, by rfl⟩ : syracuseStep 1904249 = 1428187) B1428187
theorem B3805163 : Blo 1124630 3805163 := bstep (se 1 (by rfl) ⟨2853872, by rfl⟩ : syracuseStep 3805163 = 5707745) B5707745
theorem B5705963 : Blo 1124630 5705963 := bstep (se 1 (by rfl) ⟨4279472, by rfl⟩ : syracuseStep 5705963 = 8558945) B8558945
theorem B3805703 : Blo 1124630 3805703 := bstep (se 1 (by rfl) ⟨2854277, by rfl⟩ : syracuseStep 3805703 = 5708555) B5708555
theorem B2855675 : Blo 1124630 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B4330351 : Blo 1124630 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B2135423 : Blo 1124630 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B3806621 : Blo 1124630 3806621 := bstep (se 3 (by rfl) ⟨713741, by rfl⟩ : syracuseStep 3806621 = 1427483) B1427483
theorem B3806675 : Blo 1124630 3806675 := bstep (se 1 (by rfl) ⟨2855006, by rfl⟩ : syracuseStep 3806675 = 5710013) B5710013
theorem B3806783 : Blo 1124630 3806783 := bstep (se 1 (by rfl) ⟨2855087, by rfl⟩ : syracuseStep 3806783 = 5710175) B5710175
theorem B2856617 : Blo 1124630 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B3808025 : Blo 1124630 3808025 := bstep (se 2 (by rfl) ⟨1428009, by rfl⟩ : syracuseStep 3808025 = 2856019) B2856019
theorem B3808619 : Blo 1124630 3808619 := bstep (se 1 (by rfl) ⟨2856464, by rfl⟩ : syracuseStep 3808619 = 5712929) B5712929
theorem B9641663 : Blo 1124630 9641663 := bstep (se 1 (by rfl) ⟨7231247, by rfl⟩ : syracuseStep 9641663 = 14462495) B14462495
theorem B2891539 : Blo 1124630 2891539 := bstep (se 1 (by rfl) ⟨2168654, by rfl⟩ : syracuseStep 2891539 = 4337309) B4337309
theorem B2531321 : Blo 1124630 2531321 := bstep (se 2 (by rfl) ⟨949245, by rfl⟩ : syracuseStep 2531321 = 1898491) B1898491
theorem B2138491 : Blo 1124630 2138491 := bstep (se 1 (by rfl) ⟨1603868, by rfl⟩ : syracuseStep 2138491 = 3207737) B3207737
theorem B23142833 : Blo 1124630 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B1124671 : Blo 1124630 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B1124839 : Blo 1124630 1124839 := bstep (se 1 (by rfl) ⟨843629, by rfl⟩ : syracuseStep 1124839 = 1687259) B1687259
theorem B1125019 : Blo 1124630 1125019 := bstep (se 1 (by rfl) ⟨843764, by rfl⟩ : syracuseStep 1125019 = 1687529) B1687529
theorem B1125147 : Blo 1124630 1125147 := bstep (se 1 (by rfl) ⟨843860, by rfl⟩ : syracuseStep 1125147 = 1687721) B1687721
theorem B1125359 : Blo 1124630 1125359 := bstep (se 1 (by rfl) ⟨844019, by rfl⟩ : syracuseStep 1125359 = 1688039) B1688039
theorem B1125543 : Blo 1124630 1125543 := bstep (se 1 (by rfl) ⟨844157, by rfl⟩ : syracuseStep 1125543 = 1688315) B1688315
theorem B5418191 : Blo 1124630 5418191 := bstep (se 1 (by rfl) ⟨4063643, by rfl⟩ : syracuseStep 5418191 = 8127287) B8127287
theorem B15412679 : Blo 1124630 15412679 := bstep (se 1 (by rfl) ⟨11559509, by rfl⟩ : syracuseStep 15412679 = 23119019) B23119019
theorem B1125839 : Blo 1124630 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B237022685 : Blo 1124630 237022685 := bstep (se 3 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 237022685 = 88883507) B88883507
theorem B1125935 : Blo 1124630 1125935 := bstep (se 1 (by rfl) ⟨844451, by rfl⟩ : syracuseStep 1125935 = 1688903) B1688903
theorem B1125999 : Blo 1124630 1125999 := bstep (se 1 (by rfl) ⟨844499, by rfl⟩ : syracuseStep 1125999 = 1688999) B1688999
theorem B1126119 : Blo 1124630 1126119 := bstep (se 1 (by rfl) ⟨844589, by rfl⟩ : syracuseStep 1126119 = 1689179) B1689179
theorem B1126431 : Blo 1124630 1126431 := bstep (se 1 (by rfl) ⟨844823, by rfl⟩ : syracuseStep 1126431 = 1689647) B1689647
theorem B1126607 : Blo 1124630 1126607 := bstep (se 1 (by rfl) ⟨844955, by rfl⟩ : syracuseStep 1126607 = 1689911) B1689911
theorem B1126727 : Blo 1124630 1126727 := bstep (se 1 (by rfl) ⟨845045, by rfl⟩ : syracuseStep 1126727 = 1690091) B1690091
theorem B1126887 : Blo 1124630 1126887 := bstep (se 1 (by rfl) ⟨845165, by rfl⟩ : syracuseStep 1126887 = 1690331) B1690331
theorem B1126911 : Blo 1124630 1126911 := bstep (se 1 (by rfl) ⟨845183, by rfl⟩ : syracuseStep 1126911 = 1690367) B1690367
theorem B19280591 : Blo 1124630 19280591 := bstep (se 1 (by rfl) ⟨14460443, by rfl⟩ : syracuseStep 19280591 = 28920887) B28920887
theorem B14627603 : Blo 1124630 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B1127391 : Blo 1124630 1127391 := bstep (se 1 (by rfl) ⟨845543, by rfl⟩ : syracuseStep 1127391 = 1691087) B1691087
theorem B1127451 : Blo 1124630 1127451 := bstep (se 1 (by rfl) ⟨845588, by rfl⟩ : syracuseStep 1127451 = 1691177) B1691177
theorem B1127647 : Blo 1124630 1127647 := bstep (se 1 (by rfl) ⟨845735, by rfl⟩ : syracuseStep 1127647 = 1691471) B1691471
theorem B2536703 : Blo 1124630 2536703 := bstep (se 1 (by rfl) ⟨1902527, by rfl⟩ : syracuseStep 2536703 = 3805055) B3805055
theorem B1127727 : Blo 1124630 1127727 := bstep (se 1 (by rfl) ⟨845795, by rfl⟩ : syracuseStep 1127727 = 1691591) B1691591
theorem B1127783 : Blo 1124630 1127783 := bstep (se 1 (by rfl) ⟨845837, by rfl⟩ : syracuseStep 1127783 = 1691675) B1691675
theorem B2536955 : Blo 1124630 2536955 := bstep (se 1 (by rfl) ⟨1902716, by rfl⟩ : syracuseStep 2536955 = 3805433) B3805433
theorem B1127967 : Blo 1124630 1127967 := bstep (se 1 (by rfl) ⟨845975, by rfl⟩ : syracuseStep 1127967 = 1691951) B1691951
theorem B7222841 : Blo 1124630 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B1128039 : Blo 1124630 1128039 := bstep (se 1 (by rfl) ⟨846029, by rfl⟩ : syracuseStep 1128039 = 1692059) B1692059
theorem B1128063 : Blo 1124630 1128063 := bstep (se 1 (by rfl) ⟨846047, by rfl⟩ : syracuseStep 1128063 = 1692095) B1692095
theorem B19510949 : Blo 1124630 19510949 := bstep (se 4 (by rfl) ⟨1829151, by rfl⟩ : syracuseStep 19510949 = 3658303) B3658303
theorem B1128127 : Blo 1124630 1128127 := bstep (se 1 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 1128127 = 1692191) B1692191
theorem B9615145 : Blo 1124630 9615145 := bstep (se 2 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 9615145 = 7211359) B7211359
theorem B1128319 : Blo 1124630 1128319 := bstep (se 1 (by rfl) ⟨846239, by rfl⟩ : syracuseStep 1128319 = 1692479) B1692479
theorem B1128415 : Blo 1124630 1128415 := bstep (se 1 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 1128415 = 1692623) B1692623
theorem B1128475 : Blo 1124630 1128475 := bstep (se 1 (by rfl) ⟨846356, by rfl⟩ : syracuseStep 1128475 = 1692713) B1692713
theorem B1128495 : Blo 1124630 1128495 := bstep (se 1 (by rfl) ⟨846371, by rfl⟩ : syracuseStep 1128495 = 1692743) B1692743
theorem B1128615 : Blo 1124630 1128615 := bstep (se 1 (by rfl) ⟨846461, by rfl⟩ : syracuseStep 1128615 = 1692923) B1692923
theorem B27408577 : Blo 1124630 27408577 := bstep (se 2 (by rfl) ⟨10278216, by rfl⟩ : syracuseStep 27408577 = 20556433) B20556433
theorem B8567207 : Blo 1124630 8567207 := bstep (se 1 (by rfl) ⟨6425405, by rfl⟩ : syracuseStep 8567207 = 12850811) B12850811
theorem B9124285 : Blo 1124630 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B2537963 : Blo 1124630 2537963 := bstep (se 1 (by rfl) ⟨1903472, by rfl⟩ : syracuseStep 2537963 = 3806945) B3806945
theorem B13875875 : Blo 1124630 13875875 := bstep (se 1 (by rfl) ⟨10406906, by rfl⟩ : syracuseStep 13875875 = 20813813) B20813813
theorem B1687223 : Blo 1124630 1687223 := bstep (se 1 (by rfl) ⟨1265417, by rfl⟩ : syracuseStep 1687223 = 2530835) B2530835
theorem B2539259 : Blo 1124630 2539259 := bstep (se 1 (by rfl) ⟨1904444, by rfl⟩ : syracuseStep 2539259 = 3808889) B3808889
theorem B2539295 : Blo 1124630 2539295 := bstep (se 1 (by rfl) ⟨1904471, by rfl⟩ : syracuseStep 2539295 = 3808943) B3808943
theorem B77119361 : Blo 1124630 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B8109989 : Blo 1124630 8109989 := bstep (se 4 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 8109989 = 1520623) B1520623
theorem B6406087 : Blo 1124630 6406087 := bstep (se 1 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 6406087 = 9609131) B9609131
theorem B1687535 : Blo 1124630 1687535 := bstep (se 1 (by rfl) ⟨1265651, by rfl⟩ : syracuseStep 1687535 = 2531303) B2531303
theorem B1687655 : Blo 1124630 1687655 := bstep (se 1 (by rfl) ⟨1265741, by rfl⟩ : syracuseStep 1687655 = 2531483) B2531483
theorem B16466111 : Blo 1124630 16466111 := bstep (se 1 (by rfl) ⟨12349583, by rfl⟩ : syracuseStep 16466111 = 24699167) B24699167
theorem B41075039 : Blo 1124630 41075039 := bstep (se 1 (by rfl) ⟨30806279, by rfl⟩ : syracuseStep 41075039 = 61612559) B61612559
theorem B1688375 : Blo 1124630 1688375 := bstep (se 1 (by rfl) ⟨1266281, by rfl⟩ : syracuseStep 1688375 = 2532563) B2532563
theorem B8667971 : Blo 1124630 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B1688543 : Blo 1124630 1688543 := bstep (se 1 (by rfl) ⟨1266407, by rfl⟩ : syracuseStep 1688543 = 2532815) B2532815
theorem B1688555 : Blo 1124630 1688555 := bstep (se 1 (by rfl) ⟨1266416, by rfl⟩ : syracuseStep 1688555 = 2532833) B2532833
theorem B892257277 : Blo 1124630 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B1688807 : Blo 1124630 1688807 := bstep (se 1 (by rfl) ⟨1266605, by rfl⟩ : syracuseStep 1688807 = 2533211) B2533211
theorem B1426663 : Blo 1124630 1426663 := bstep (se 1 (by rfl) ⟨1069997, by rfl⟩ : syracuseStep 1426663 = 2139995) B2139995
theorem B1688873 : Blo 1124630 1688873 := bstep (se 2 (by rfl) ⟨633327, by rfl⟩ : syracuseStep 1688873 = 1266655) B1266655
theorem B12830399 : Blo 1124630 12830399 := bstep (se 1 (by rfl) ⟨9622799, by rfl⟩ : syracuseStep 12830399 = 19245599) B19245599
theorem B1689455 : Blo 1124630 1689455 := bstep (se 1 (by rfl) ⟨1267091, by rfl⟩ : syracuseStep 1689455 = 2534183) B2534183
theorem B1427311 : Blo 1124630 1427311 := bstep (se 1 (by rfl) ⟨1070483, by rfl⟩ : syracuseStep 1427311 = 2140967) B2140967
theorem B1689641 : Blo 1124630 1689641 := bstep (se 2 (by rfl) ⟨633615, by rfl⟩ : syracuseStep 1689641 = 1267231) B1267231
theorem B6408503 : Blo 1124630 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B4278865 : Blo 1124630 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B53496557 : Blo 1124630 53496557 := bstep (se 3 (by rfl) ⟨10030604, by rfl⟩ : syracuseStep 53496557 = 20061209) B20061209
theorem B1690793 : Blo 1124630 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B1690907 : Blo 1124630 1690907 := bstep (se 1 (by rfl) ⟨1268180, by rfl⟩ : syracuseStep 1690907 = 2536361) B2536361
theorem B8670863 : Blo 1124630 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B8113907 : Blo 1124630 8113907 := bstep (se 1 (by rfl) ⟨6085430, by rfl⟩ : syracuseStep 8113907 = 12170861) B12170861
theorem B52056539 : Blo 1124630 52056539 := bstep (se 1 (by rfl) ⟨39042404, by rfl⟩ : syracuseStep 52056539 = 78084809) B78084809
theorem B9622253 : Blo 1124630 9622253 := bstep (se 3 (by rfl) ⟨1804172, by rfl⟩ : syracuseStep 9622253 = 3608345) B3608345
theorem B1692443 : Blo 1124630 1692443 := bstep (se 1 (by rfl) ⟨1269332, by rfl⟩ : syracuseStep 1692443 = 2538665) B2538665
theorem B1266799 : Blo 1124630 1266799 := bstep (se 1 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 1266799 = 1900199) B1900199
theorem B24335569 : Blo 1124630 24335569 := bstep (se 2 (by rfl) ⟨9125838, by rfl⟩ : syracuseStep 24335569 = 18251677) B18251677
theorem B30790955 : Blo 1124630 30790955 := bstep (se 1 (by rfl) ⟨23093216, by rfl⟩ : syracuseStep 30790955 = 46186433) B46186433
theorem B4281767 : Blo 1124630 4281767 := bstep (se 1 (by rfl) ⟨3211325, by rfl⟩ : syracuseStep 4281767 = 6422651) B6422651
theorem B1201663 : Blo 1124630 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B1267303 : Blo 1124630 1267303 := bstep (se 1 (by rfl) ⟨950477, by rfl⟩ : syracuseStep 1267303 = 1900955) B1900955
theorem B1955519 : Blo 1124630 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B8541935 : Blo 1124630 8541935 := bstep (se 1 (by rfl) ⟨6406451, by rfl⟩ : syracuseStep 8541935 = 12812903) B12812903
theorem B4872059 : Blo 1124630 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B4807471 : Blo 1124630 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B4808105 : Blo 1124630 4808105 := bstep (se 2 (by rfl) ⟨1803039, by rfl⟩ : syracuseStep 4808105 = 3606079) B3606079
theorem B6086315 : Blo 1124630 6086315 := bstep (se 1 (by rfl) ⟨4564736, by rfl⟩ : syracuseStep 6086315 = 9129473) B9129473
theorem B6349211 : Blo 1124630 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B12837689 : Blo 1124630 12837689 := bstep (se 2 (by rfl) ⟨4814133, by rfl⟩ : syracuseStep 12837689 = 9628267) B9628267
theorem B2745209 : Blo 1124630 2745209 := bstep (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) B2058907
theorem B8545337 : Blo 1124630 8545337 := bstep (se 2 (by rfl) ⟨3204501, by rfl⟩ : syracuseStep 8545337 = 6409003) B6409003
theorem B3204947 : Blo 1124630 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B21686291 : Blo 1124630 21686291 := bstep (se 1 (by rfl) ⟨16264718, by rfl⟩ : syracuseStep 21686291 = 32529437) B32529437
theorem B2746399 : Blo 1124630 2746399 := bstep (se 1 (by rfl) ⟨2059799, by rfl⟩ : syracuseStep 2746399 = 4119599) B4119599
theorem B7923911 : Blo 1124630 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B8120969 : Blo 1124630 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B13691591 : Blo 1124630 13691591 := bstep (se 1 (by rfl) ⟨10268693, by rfl⟩ : syracuseStep 13691591 = 20537387) B20537387
theorem B13725065 : Blo 1124630 13725065 := bstep (se 2 (by rfl) ⟨5146899, by rfl⟩ : syracuseStep 13725065 = 10293799) B10293799
theorem B15625723 : Blo 1124630 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B9138167 : Blo 1124630 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B15429635 : Blo 1124630 15429635 := bstep (se 1 (by rfl) ⟨11572226, by rfl⟩ : syracuseStep 15429635 = 23144453) B23144453
theorem B3797117 : Blo 1124630 3797117 := bstep (se 3 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 3797117 = 1423919) B1423919
theorem B12186085 : Blo 1124630 12186085 := bstep (se 4 (by rfl) ⟨1142445, by rfl⟩ : syracuseStep 12186085 = 2284891) B2284891
theorem B5698025 : Blo 1124630 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B554824403 : Blo 1124630 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B4879129 : Blo 1124630 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B2847545 : Blo 1124630 2847545 := bstep (se 2 (by rfl) ⟨1067829, by rfl⟩ : syracuseStep 2847545 = 2135659) B2135659
theorem B3798251 : Blo 1124630 3798251 := bstep (se 1 (by rfl) ⟨2848688, by rfl⟩ : syracuseStep 3798251 = 5697377) B5697377
theorem B1897897 : Blo 1124630 1897897 := bstep (se 2 (by rfl) ⟨711711, by rfl⟩ : syracuseStep 1897897 = 1423423) B1423423
theorem B1897951 : Blo 1124630 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B3798791 : Blo 1124630 3798791 := bstep (se 1 (by rfl) ⟨2849093, by rfl⟩ : syracuseStep 3798791 = 5698187) B5698187
theorem B1898599 : Blo 1124630 1898599 := bstep (se 1 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 1898599 = 2847899) B2847899
theorem B2848891 : Blo 1124630 2848891 := bstep (se 1 (by rfl) ⟨2136668, by rfl⟩ : syracuseStep 2848891 = 4273337) B4273337
theorem B14416157 : Blo 1124630 14416157 := bstep (se 3 (by rfl) ⟨2703029, by rfl⟩ : syracuseStep 14416157 = 5406059) B5406059
theorem B2849519 : Blo 1124630 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B1899335 : Blo 1124630 1899335 := bstep (se 1 (by rfl) ⟨1424501, by rfl⟩ : syracuseStep 1899335 = 2849003) B2849003
theorem B3603311 : Blo 1124630 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B8551655 : Blo 1124630 8551655 := bstep (se 1 (by rfl) ⟨6413741, by rfl⟩ : syracuseStep 8551655 = 12827483) B12827483
theorem B9764347 : Blo 1124630 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B1900415 : Blo 1124630 1900415 := bstep (se 1 (by rfl) ⟨1425311, by rfl⟩ : syracuseStep 1900415 = 2850623) B2850623
theorem B1900523 : Blo 1124630 1900523 := bstep (se 1 (by rfl) ⟨1425392, by rfl⟩ : syracuseStep 1900523 = 2850785) B2850785
theorem B10977407 : Blo 1124630 10977407 := bstep (se 1 (by rfl) ⟨8233055, by rfl⟩ : syracuseStep 10977407 = 16466111) B16466111
theorem B2851321 : Blo 1124630 2851321 := bstep (se 2 (by rfl) ⟨1069245, by rfl⟩ : syracuseStep 2851321 = 2138491) B2138491
theorem B1901083 : Blo 1124630 1901083 := bstep (se 1 (by rfl) ⟨1425812, by rfl⟩ : syracuseStep 1901083 = 2851625) B2851625
theorem B8553599 : Blo 1124630 8553599 := bstep (se 1 (by rfl) ⟨6415199, by rfl⟩ : syracuseStep 8553599 = 12830399) B12830399
theorem B1189676369 : Blo 1124630 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B3802679 : Blo 1124630 3802679 := bstep (se 1 (by rfl) ⟨2852009, by rfl⟩ : syracuseStep 3802679 = 5704019) B5704019
theorem B1902217 : Blo 1124630 1902217 := bstep (se 2 (by rfl) ⟨713331, by rfl⟩ : syracuseStep 1902217 = 1426663) B1426663
theorem B5703371 : Blo 1124630 5703371 := bstep (se 1 (by rfl) ⟨4277528, by rfl⟩ : syracuseStep 5703371 = 8555057) B8555057
theorem B6424859 : Blo 1124630 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B1903081 : Blo 1124630 1903081 := bstep (se 2 (by rfl) ⟨713655, by rfl⟩ : syracuseStep 1903081 = 1427311) B1427311
theorem B5409271 : Blo 1124630 5409271 := bstep (se 1 (by rfl) ⟨4056953, by rfl⟩ : syracuseStep 5409271 = 8113907) B8113907
theorem B3803975 : Blo 1124630 3803975 := bstep (se 1 (by rfl) ⟨2852981, by rfl⟩ : syracuseStep 3803975 = 5705963) B5705963
theorem B34704359 : Blo 1124630 34704359 := bstep (se 1 (by rfl) ⟨26028269, by rfl⟩ : syracuseStep 34704359 = 52056539) B52056539
theorem B1903783 : Blo 1124630 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B5705153 : Blo 1124630 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B2854511 : Blo 1124630 2854511 := bstep (se 1 (by rfl) ⟨2140883, by rfl⟩ : syracuseStep 2854511 = 4281767) B4281767
theorem B1904411 : Blo 1124630 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B3248039 : Blo 1124630 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B6427775 : Blo 1124630 6427775 := bstep (se 1 (by rfl) ⟨4820831, by rfl⟩ : syracuseStep 6427775 = 9641663) B9641663
theorem B4232807 : Blo 1124630 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B8558459 : Blo 1124630 8558459 := bstep (se 1 (by rfl) ⟨6418844, by rfl⟩ : syracuseStep 8558459 = 12837689) B12837689
theorem B5773801 : Blo 1124630 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B2136631 : Blo 1124630 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B14457527 : Blo 1124630 14457527 := bstep (se 1 (by rfl) ⟨10843145, by rfl⟩ : syracuseStep 14457527 = 21686291) B21686291
theorem B32447425 : Blo 1124630 32447425 := bstep (se 2 (by rfl) ⟨12167784, by rfl⟩ : syracuseStep 32447425 = 24335569) B24335569
theorem B5413979 : Blo 1124630 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B2530529 : Blo 1124630 2530529 := bstep (se 2 (by rfl) ⟨948948, by rfl⟩ : syracuseStep 2530529 = 1897897) B1897897
theorem B2530601 : Blo 1124630 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B3612127 : Blo 1124630 3612127 := bstep (se 1 (by rfl) ⟨2709095, by rfl⟩ : syracuseStep 3612127 = 5418191) B5418191
theorem B9150043 : Blo 1124630 9150043 := bstep (se 1 (by rfl) ⟨6862532, by rfl⟩ : syracuseStep 9150043 = 13725065) B13725065
theorem B158015123 : Blo 1124630 158015123 := bstep (se 1 (by rfl) ⟨118511342, by rfl⟩ : syracuseStep 158015123 = 237022685) B237022685
theorem B12820193 : Blo 1124630 12820193 := bstep (se 2 (by rfl) ⟨4807572, by rfl⟩ : syracuseStep 12820193 = 9615145) B9615145
theorem B2531411 : Blo 1124630 2531411 := bstep (se 1 (by rfl) ⟨1898558, by rfl⟩ : syracuseStep 2531411 = 3797117) B3797117
theorem B2531465 : Blo 1124630 2531465 := bstep (se 2 (by rfl) ⟨949299, by rfl⟩ : syracuseStep 2531465 = 1898599) B1898599
theorem B36544769 : Blo 1124630 36544769 := bstep (se 2 (by rfl) ⟨13704288, by rfl⟩ : syracuseStep 36544769 = 27408577) B27408577
theorem B12853727 : Blo 1124630 12853727 := bstep (se 1 (by rfl) ⟨9640295, by rfl⟩ : syracuseStep 12853727 = 19280591) B19280591
theorem B12165713 : Blo 1124630 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B2532167 : Blo 1124630 2532167 := bstep (se 1 (by rfl) ⟨1899125, by rfl⟩ : syracuseStep 2532167 = 3798251) B3798251
theorem B2532527 : Blo 1124630 2532527 := bstep (se 1 (by rfl) ⟨1899395, by rfl⟩ : syracuseStep 2532527 = 3798791) B3798791
theorem B9610771 : Blo 1124630 9610771 := bstep (se 1 (by rfl) ⟨7208078, by rfl⟩ : syracuseStep 9610771 = 14416157) B14416157
theorem B5711471 : Blo 1124630 5711471 := bstep (se 1 (by rfl) ⟨4283603, by rfl⟩ : syracuseStep 5711471 = 8567207) B8567207
theorem B9250583 : Blo 1124630 9250583 := bstep (se 1 (by rfl) ⟨6937937, by rfl⟩ : syracuseStep 9250583 = 13875875) B13875875
theorem B2402207 : Blo 1124630 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B13019129 : Blo 1124630 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B1124815 : Blo 1124630 1124815 := bstep (se 1 (by rfl) ⟨843611, by rfl⟩ : syracuseStep 1124815 = 1687223) B1687223
theorem B1125023 : Blo 1124630 1125023 := bstep (se 1 (by rfl) ⟨843767, by rfl⟩ : syracuseStep 1125023 = 1687535) B1687535
theorem B1125103 : Blo 1124630 1125103 := bstep (se 1 (by rfl) ⟨843827, by rfl⟩ : syracuseStep 1125103 = 1687655) B1687655
theorem B1125583 : Blo 1124630 1125583 := bstep (se 1 (by rfl) ⟨844187, by rfl⟩ : syracuseStep 1125583 = 1688375) B1688375
theorem B5778647 : Blo 1124630 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B5418247 : Blo 1124630 5418247 := bstep (se 1 (by rfl) ⟨4063685, by rfl⟩ : syracuseStep 5418247 = 8127371) B8127371
theorem B1125695 : Blo 1124630 1125695 := bstep (se 1 (by rfl) ⟨844271, by rfl⟩ : syracuseStep 1125695 = 1688543) B1688543
theorem B1125703 : Blo 1124630 1125703 := bstep (se 1 (by rfl) ⟨844277, by rfl⟩ : syracuseStep 1125703 = 1688555) B1688555
theorem B1125871 : Blo 1124630 1125871 := bstep (se 1 (by rfl) ⟨844403, by rfl⟩ : syracuseStep 1125871 = 1688807) B1688807
theorem B1125915 : Blo 1124630 1125915 := bstep (se 1 (by rfl) ⟨844436, by rfl⟩ : syracuseStep 1125915 = 1688873) B1688873
theorem B2535083 : Blo 1124630 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B24161975 : Blo 1124630 24161975 := bstep (se 1 (by rfl) ⟨18121481, by rfl⟩ : syracuseStep 24161975 = 36242963) B36242963
theorem B1126303 : Blo 1124630 1126303 := bstep (se 1 (by rfl) ⟨844727, by rfl⟩ : syracuseStep 1126303 = 1689455) B1689455
theorem B2535407 : Blo 1124630 2535407 := bstep (se 1 (by rfl) ⟨1901555, by rfl⟩ : syracuseStep 2535407 = 3803111) B3803111
theorem B12824567 : Blo 1124630 12824567 := bstep (se 1 (by rfl) ⟨9618425, by rfl⟩ : syracuseStep 12824567 = 19236851) B19236851
theorem B1126427 : Blo 1124630 1126427 := bstep (se 1 (by rfl) ⟨844820, by rfl⟩ : syracuseStep 1126427 = 1689641) B1689641
theorem B4272335 : Blo 1124630 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B2535803 : Blo 1124630 2535803 := bstep (se 1 (by rfl) ⟨1901852, by rfl⟩ : syracuseStep 2535803 = 3803705) B3803705
theorem B2535911 : Blo 1124630 2535911 := bstep (se 1 (by rfl) ⟨1901933, by rfl⟩ : syracuseStep 2535911 = 3803867) B3803867
theorem B35664371 : Blo 1124630 35664371 := bstep (se 1 (by rfl) ⟨26748278, by rfl⟩ : syracuseStep 35664371 = 53496557) B53496557
theorem B1127195 : Blo 1124630 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B1127271 : Blo 1124630 1127271 := bstep (se 1 (by rfl) ⟨845453, by rfl⟩ : syracuseStep 1127271 = 1690907) B1690907
theorem B7320557 : Blo 1124630 7320557 := bstep (se 3 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 7320557 = 2745209) B2745209
theorem B5780575 : Blo 1124630 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B2536775 : Blo 1124630 2536775 := bstep (se 1 (by rfl) ⟨1902581, by rfl⟩ : syracuseStep 2536775 = 3805163) B3805163
theorem B2537081 : Blo 1124630 2537081 := bstep (se 2 (by rfl) ⟨951405, by rfl⟩ : syracuseStep 2537081 = 1902811) B1902811
theorem B2537135 : Blo 1124630 2537135 := bstep (se 1 (by rfl) ⟨1902851, by rfl⟩ : syracuseStep 2537135 = 3805703) B3805703
theorem B1128295 : Blo 1124630 1128295 := bstep (se 1 (by rfl) ⟨846221, by rfl⟩ : syracuseStep 1128295 = 1692443) B1692443
theorem B20527303 : Blo 1124630 20527303 := bstep (se 1 (by rfl) ⟨15395477, by rfl⟩ : syracuseStep 20527303 = 30790955) B30790955
theorem B2537747 : Blo 1124630 2537747 := bstep (se 1 (by rfl) ⟨1903310, by rfl⟩ : syracuseStep 2537747 = 3806621) B3806621
theorem B2537783 : Blo 1124630 2537783 := bstep (se 1 (by rfl) ⟨1903337, by rfl⟩ : syracuseStep 2537783 = 3806675) B3806675
theorem B2537855 : Blo 1124630 2537855 := bstep (se 1 (by rfl) ⟨1903391, by rfl⟩ : syracuseStep 2537855 = 3806783) B3806783
theorem B2538683 : Blo 1124630 2538683 := bstep (se 1 (by rfl) ⟨1904012, by rfl⟩ : syracuseStep 2538683 = 3808025) B3808025
theorem B2539079 : Blo 1124630 2539079 := bstep (se 1 (by rfl) ⟨1904309, by rfl⟩ : syracuseStep 2539079 = 3808619) B3808619
theorem B1687547 : Blo 1124630 1687547 := bstep (se 1 (by rfl) ⟨1265660, by rfl⟩ : syracuseStep 1687547 = 2531321) B2531321
theorem B6505505 : Blo 1124630 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B1689065 : Blo 1124630 1689065 := bstep (se 2 (by rfl) ⟨633399, by rfl⟩ : syracuseStep 1689065 = 1266799) B1266799
theorem B9127727 : Blo 1124630 9127727 := bstep (se 1 (by rfl) ⟨6845795, by rfl⟩ : syracuseStep 9127727 = 13691591) B13691591
theorem B1689737 : Blo 1124630 1689737 := bstep (se 2 (by rfl) ⟨633651, by rfl⟩ : syracuseStep 1689737 = 1267303) B1267303
theorem B10275119 : Blo 1124630 10275119 := bstep (se 1 (by rfl) ⟨7706339, by rfl⟩ : syracuseStep 10275119 = 15412679) B15412679
theorem B9751735 : Blo 1124630 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B1691135 : Blo 1124630 1691135 := bstep (se 1 (by rfl) ⟨1268351, by rfl⟩ : syracuseStep 1691135 = 2536703) B2536703
theorem B1691303 : Blo 1124630 1691303 := bstep (se 1 (by rfl) ⟨1268477, by rfl⟩ : syracuseStep 1691303 = 2536955) B2536955
theorem B6409961 : Blo 1124630 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B1691975 : Blo 1124630 1691975 := bstep (se 1 (by rfl) ⟨1268981, by rfl⟩ : syracuseStep 1691975 = 2537963) B2537963
theorem B1266223 : Blo 1124630 1266223 := bstep (se 1 (by rfl) ⟨949667, by rfl⟩ : syracuseStep 1266223 = 1899335) B1899335
theorem B3855385 : Blo 1124630 3855385 := bstep (se 2 (by rfl) ⟨1445769, by rfl⟩ : syracuseStep 3855385 = 2891539) B2891539
theorem B1692839 : Blo 1124630 1692839 := bstep (se 1 (by rfl) ⟨1269629, by rfl⟩ : syracuseStep 1692839 = 2539259) B2539259
theorem B1692863 : Blo 1124630 1692863 := bstep (se 1 (by rfl) ⟨1269647, by rfl⟩ : syracuseStep 1692863 = 2539295) B2539295
theorem B1266943 : Blo 1124630 1266943 := bstep (se 1 (by rfl) ⟨950207, by rfl⟩ : syracuseStep 1266943 = 1900415) B1900415
theorem B8541449 : Blo 1124630 8541449 := bstep (se 2 (by rfl) ⟨3203043, by rfl⟩ : syracuseStep 8541449 = 6406087) B6406087
theorem B1267015 : Blo 1124630 1267015 := bstep (se 1 (by rfl) ⟨950261, by rfl⟩ : syracuseStep 1267015 = 1900523) B1900523
theorem B27383359 : Blo 1124630 27383359 := bstep (se 1 (by rfl) ⟨20537519, by rfl⟩ : syracuseStep 27383359 = 41075039) B41075039
theorem B1267879 : Blo 1124630 1267879 := bstep (se 1 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 1267879 = 1901819) B1901819
theorem B1269499 : Blo 1124630 1269499 := bstep (se 1 (by rfl) ⟨952124, by rfl⟩ : syracuseStep 1269499 = 1904249) B1904249
theorem B3661865 : Blo 1124630 3661865 := bstep (se 2 (by rfl) ⟨1373199, by rfl⟩ : syracuseStep 3661865 = 2746399) B2746399
theorem B6414835 : Blo 1124630 6414835 := bstep (se 1 (by rfl) ⟨4811126, by rfl⟩ : syracuseStep 6414835 = 9622253) B9622253
theorem B5694461 : Blo 1124630 5694461 := bstep (se 3 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 5694461 = 2135423) B2135423
theorem B1303679 : Blo 1124630 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B5694623 : Blo 1124630 5694623 := bstep (se 1 (by rfl) ⟨4270967, by rfl⟩ : syracuseStep 5694623 = 8541935) B8541935
theorem B20834297 : Blo 1124630 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B3205403 : Blo 1124630 3205403 := bstep (se 1 (by rfl) ⟨2404052, by rfl⟩ : syracuseStep 3205403 = 4808105) B4808105
theorem B4057543 : Blo 1124630 4057543 := bstep (se 1 (by rfl) ⟨3043157, by rfl⟩ : syracuseStep 4057543 = 6086315) B6086315
theorem B15428555 : Blo 1124630 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B21130429 : Blo 1124630 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B16248113 : Blo 1124630 16248113 := bstep (se 2 (by rfl) ⟨6093042, by rfl⟩ : syracuseStep 16248113 = 12186085) B12186085
theorem B5696891 : Blo 1124630 5696891 := bstep (se 1 (by rfl) ⟨4272668, by rfl⟩ : syracuseStep 5696891 = 8545337) B8545337
theorem B1602217 : Blo 1124630 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B6092111 : Blo 1124630 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B10286423 : Blo 1124630 10286423 := bstep (se 1 (by rfl) ⟨7714817, by rfl⟩ : syracuseStep 10286423 = 15429635) B15429635
theorem B3798521 : Blo 1124630 3798521 := bstep (se 2 (by rfl) ⟨1424445, by rfl⟩ : syracuseStep 3798521 = 2848891) B2848891
theorem B3798683 : Blo 1124630 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B19232477 : Blo 1124630 19232477 := bstep (se 3 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 19232477 = 7212179) B7212179
theorem B369882935 : Blo 1124630 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B1898363 : Blo 1124630 1898363 := bstep (se 1 (by rfl) ⟨1423772, by rfl⟩ : syracuseStep 1898363 = 2847545) B2847545
theorem B4815227 : Blo 1124630 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B13007299 : Blo 1124630 13007299 := bstep (se 1 (by rfl) ⟨9755474, by rfl⟩ : syracuseStep 13007299 = 19510949) B19510949
theorem B1899679 : Blo 1124630 1899679 := bstep (se 1 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 1899679 = 2849519) B2849519
theorem B5701103 : Blo 1124630 5701103 := bstep (se 1 (by rfl) ⟨4275827, by rfl⟩ : syracuseStep 5701103 = 8551655) B8551655
theorem B51412907 : Blo 1124630 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B5406659 : Blo 1124630 5406659 := bstep (se 1 (by rfl) ⟨4054994, by rfl⟩ : syracuseStep 5406659 = 8109989) B8109989
theorem B8553113 : Blo 1124630 8553113 := bstep (se 2 (by rfl) ⟨3207417, by rfl⟩ : syracuseStep 8553113 = 6414835) B6414835
theorem B3801761 : Blo 1124630 3801761 := bstep (se 2 (by rfl) ⟨1425660, by rfl⟩ : syracuseStep 3801761 = 2851321) B2851321
theorem B5702399 : Blo 1124630 5702399 := bstep (se 1 (by rfl) ⟨4276799, by rfl⟩ : syracuseStep 5702399 = 8553599) B8553599
theorem B3802247 : Blo 1124630 3802247 := bstep (se 1 (by rfl) ⟨2851685, by rfl⟩ : syracuseStep 3802247 = 5703371) B5703371
theorem B6850079 : Blo 1124630 6850079 := bstep (se 1 (by rfl) ⟨5137559, by rfl⟩ : syracuseStep 6850079 = 10275119) B10275119
theorem B23136239 : Blo 1124630 23136239 := bstep (se 1 (by rfl) ⟨17352179, by rfl⟩ : syracuseStep 23136239 = 34704359) B34704359
theorem B12814361 : Blo 1124630 12814361 := bstep (se 2 (by rfl) ⟨4805385, by rfl⟩ : syracuseStep 12814361 = 9610771) B9610771
theorem B3803435 : Blo 1124630 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1903007 : Blo 1124630 1903007 := bstep (se 1 (by rfl) ⟨1427255, by rfl⟩ : syracuseStep 1903007 = 2854511) B2854511
theorem B3476477 : Blo 1124630 3476477 := bstep (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) B1303679
theorem B7212361 : Blo 1124630 7212361 := bstep (se 2 (by rfl) ⟨2704635, by rfl⟩ : syracuseStep 7212361 = 5409271) B5409271
theorem B3172470317 : Blo 1124630 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B2821871 : Blo 1124630 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B5705639 : Blo 1124630 5705639 := bstep (se 1 (by rfl) ⟨4279229, by rfl⟩ : syracuseStep 5705639 = 8558459) B8558459
theorem B9638351 : Blo 1124630 9638351 := bstep (se 1 (by rfl) ⟨7228763, by rfl⟩ : syracuseStep 9638351 = 14457527) B14457527
theorem B2136289 : Blo 1124630 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B52009253 : Blo 1124630 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B3807647 : Blo 1124630 3807647 := bstep (se 1 (by rfl) ⟨2855735, by rfl⟩ : syracuseStep 3807647 = 5711471) B5711471
theorem B7707433 : Blo 1124630 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B2136935 : Blo 1124630 2136935 := bstep (se 1 (by rfl) ⟨1602701, by rfl⟩ : syracuseStep 2136935 = 3205403) B3205403
theorem B36511145 : Blo 1124630 36511145 := bstep (se 2 (by rfl) ⟨13691679, by rfl⟩ : syracuseStep 36511145 = 27383359) B27383359
theorem B27369737 : Blo 1124630 27369737 := bstep (se 2 (by rfl) ⟨10263651, by rfl⟩ : syracuseStep 27369737 = 20527303) B20527303
theorem B17343065 : Blo 1124630 17343065 := bstep (se 2 (by rfl) ⟨6503649, by rfl⟩ : syracuseStep 17343065 = 13007299) B13007299
theorem B6857615 : Blo 1124630 6857615 := bstep (se 1 (by rfl) ⟨5143211, by rfl⟩ : syracuseStep 6857615 = 10286423) B10286423
theorem B2532347 : Blo 1124630 2532347 := bstep (se 1 (by rfl) ⟨1899260, by rfl⟩ : syracuseStep 2532347 = 3798521) B3798521
theorem B2532455 : Blo 1124630 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B12821651 : Blo 1124630 12821651 := bstep (se 1 (by rfl) ⟨9616238, by rfl⟩ : syracuseStep 12821651 = 19232477) B19232477
theorem B246588623 : Blo 1124630 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B43263233 : Blo 1124630 43263233 := bstep (se 2 (by rfl) ⟨16223712, by rfl⟩ : syracuseStep 43263233 = 32447425) B32447425
theorem B2532905 : Blo 1124630 2532905 := bstep (se 2 (by rfl) ⟨949839, by rfl⟩ : syracuseStep 2532905 = 1899679) B1899679
theorem B12200057 : Blo 1124630 12200057 := bstep (se 2 (by rfl) ⟨4575021, by rfl⟩ : syracuseStep 12200057 = 9150043) B9150043
theorem B8661437 : Blo 1124630 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B1125031 : Blo 1124630 1125031 := bstep (se 1 (by rfl) ⟨843773, by rfl⟩ : syracuseStep 1125031 = 1687547) B1687547
theorem B7318271 : Blo 1124630 7318271 := bstep (se 1 (by rfl) ⟨5488703, by rfl⟩ : syracuseStep 7318271 = 10977407) B10977407
theorem B4337003 : Blo 1124630 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B2534777 : Blo 1124630 2534777 := bstep (se 2 (by rfl) ⟨950541, by rfl⟩ : syracuseStep 2534777 = 1901083) B1901083
theorem B1126043 : Blo 1124630 1126043 := bstep (se 1 (by rfl) ⟨844532, by rfl⟩ : syracuseStep 1126043 = 1689065) B1689065
theorem B2535119 : Blo 1124630 2535119 := bstep (se 1 (by rfl) ⟨1901339, by rfl⟩ : syracuseStep 2535119 = 3802679) B3802679
theorem B1126491 : Blo 1124630 1126491 := bstep (se 1 (by rfl) ⟨844868, by rfl⟩ : syracuseStep 1126491 = 1689737) B1689737
theorem B2535983 : Blo 1124630 2535983 := bstep (se 1 (by rfl) ⟨1901987, by rfl⟩ : syracuseStep 2535983 = 3803975) B3803975
theorem B2536289 : Blo 1124630 2536289 := bstep (se 2 (by rfl) ⟨951108, by rfl⟩ : syracuseStep 2536289 = 1902217) B1902217
theorem B1127423 : Blo 1124630 1127423 := bstep (se 1 (by rfl) ⟨845567, by rfl⟩ : syracuseStep 1127423 = 1691135) B1691135
theorem B21640229 : Blo 1124630 21640229 := bstep (se 4 (by rfl) ⟨2028771, by rfl⟩ : syracuseStep 21640229 = 4057543) B4057543
theorem B1127535 : Blo 1124630 1127535 := bstep (se 1 (by rfl) ⟨845651, by rfl⟩ : syracuseStep 1127535 = 1691303) B1691303
theorem B4273307 : Blo 1124630 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B1127983 : Blo 1124630 1127983 := bstep (se 1 (by rfl) ⟨845987, by rfl⟩ : syracuseStep 1127983 = 1691975) B1691975
theorem B2537441 : Blo 1124630 2537441 := bstep (se 2 (by rfl) ⟨951540, by rfl⟩ : syracuseStep 2537441 = 1903081) B1903081
theorem B1128559 : Blo 1124630 1128559 := bstep (se 1 (by rfl) ⟨846419, by rfl⟩ : syracuseStep 1128559 = 1692839) B1692839
theorem B1128575 : Blo 1124630 1128575 := bstep (se 1 (by rfl) ⟨846431, by rfl⟩ : syracuseStep 1128575 = 1692863) B1692863
theorem B2538377 : Blo 1124630 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B7224329 : Blo 1124630 7224329 := bstep (se 2 (by rfl) ⟨2709123, by rfl⟩ : syracuseStep 7224329 = 5418247) B5418247
theorem B1687019 : Blo 1124630 1687019 := bstep (se 1 (by rfl) ⟨1265264, by rfl⟩ : syracuseStep 1687019 = 2530529) B2530529
theorem B1687067 : Blo 1124630 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B2441243 : Blo 1124630 2441243 := bstep (se 1 (by rfl) ⟨1830932, by rfl⟩ : syracuseStep 2441243 = 3661865) B3661865
theorem B1687607 : Blo 1124630 1687607 := bstep (se 1 (by rfl) ⟨1265705, by rfl⟩ : syracuseStep 1687607 = 2531411) B2531411
theorem B1687643 : Blo 1124630 1687643 := bstep (se 1 (by rfl) ⟨1265732, by rfl⟩ : syracuseStep 1687643 = 2531465) B2531465
theorem B24363179 : Blo 1124630 24363179 := bstep (se 1 (by rfl) ⟨18272384, by rfl⟩ : syracuseStep 24363179 = 36544769) B36544769
theorem B8569151 : Blo 1124630 8569151 := bstep (se 1 (by rfl) ⟨6426863, by rfl⟩ : syracuseStep 8569151 = 12853727) B12853727
theorem B8110475 : Blo 1124630 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B1688111 : Blo 1124630 1688111 := bstep (se 1 (by rfl) ⟨1266083, by rfl⟩ : syracuseStep 1688111 = 2532167) B2532167
theorem B1688297 : Blo 1124630 1688297 := bstep (se 2 (by rfl) ⟨633111, by rfl⟩ : syracuseStep 1688297 = 1266223) B1266223
theorem B1688351 : Blo 1124630 1688351 := bstep (se 1 (by rfl) ⟨1266263, by rfl⟩ : syracuseStep 1688351 = 2532527) B2532527
theorem B1689257 : Blo 1124630 1689257 := bstep (se 2 (by rfl) ⟨633471, by rfl⟩ : syracuseStep 1689257 = 1266943) B1266943
theorem B1689353 : Blo 1124630 1689353 := bstep (se 2 (by rfl) ⟨633507, by rfl⟩ : syracuseStep 1689353 = 1267015) B1267015
theorem B3852431 : Blo 1124630 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B10832075 : Blo 1124630 10832075 := bstep (se 1 (by rfl) ⟨8124056, by rfl⟩ : syracuseStep 10832075 = 16248113) B16248113
theorem B1690055 : Blo 1124630 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B16107983 : Blo 1124630 16107983 := bstep (se 1 (by rfl) ⟨12080987, by rfl⟩ : syracuseStep 16107983 = 24161975) B24161975
theorem B1690271 : Blo 1124630 1690271 := bstep (se 1 (by rfl) ⟨1267703, by rfl⟩ : syracuseStep 1690271 = 2535407) B2535407
theorem B1690505 : Blo 1124630 1690505 := bstep (se 2 (by rfl) ⟨633939, by rfl⟩ : syracuseStep 1690505 = 1267879) B1267879
theorem B14437277 : Blo 1124630 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B1690535 : Blo 1124630 1690535 := bstep (se 1 (by rfl) ⟨1267901, by rfl⟩ : syracuseStep 1690535 = 2535803) B2535803
theorem B1690607 : Blo 1124630 1690607 := bstep (se 1 (by rfl) ⟨1267955, by rfl⟩ : syracuseStep 1690607 = 2535911) B2535911
theorem B23776247 : Blo 1124630 23776247 := bstep (se 1 (by rfl) ⟨17832185, by rfl⟩ : syracuseStep 23776247 = 35664371) B35664371
theorem B1691183 : Blo 1124630 1691183 := bstep (se 1 (by rfl) ⟨1268387, by rfl⟩ : syracuseStep 1691183 = 2536775) B2536775
theorem B1691387 : Blo 1124630 1691387 := bstep (se 1 (by rfl) ⟨1268540, by rfl⟩ : syracuseStep 1691387 = 2537081) B2537081
theorem B1691423 : Blo 1124630 1691423 := bstep (se 1 (by rfl) ⟨1268567, by rfl⟩ : syracuseStep 1691423 = 2537135) B2537135
theorem B1265575 : Blo 1124630 1265575 := bstep (se 1 (by rfl) ⟨949181, by rfl⟩ : syracuseStep 1265575 = 1898363) B1898363
theorem B1691831 : Blo 1124630 1691831 := bstep (se 1 (by rfl) ⟨1268873, by rfl⟩ : syracuseStep 1691831 = 2537747) B2537747
theorem B1691855 : Blo 1124630 1691855 := bstep (se 1 (by rfl) ⟨1268891, by rfl⟩ : syracuseStep 1691855 = 2537783) B2537783
theorem B1691903 : Blo 1124630 1691903 := bstep (se 1 (by rfl) ⟨1268927, by rfl⟩ : syracuseStep 1691903 = 2537855) B2537855
theorem B1692455 : Blo 1124630 1692455 := bstep (se 1 (by rfl) ⟨1269341, by rfl⟩ : syracuseStep 1692455 = 2538683) B2538683
theorem B1692665 : Blo 1124630 1692665 := bstep (se 2 (by rfl) ⟨634749, by rfl⟩ : syracuseStep 1692665 = 1269499) B1269499
theorem B1692719 : Blo 1124630 1692719 := bstep (se 1 (by rfl) ⟨1269539, by rfl⟩ : syracuseStep 1692719 = 2539079) B2539079
theorem B6085151 : Blo 1124630 6085151 := bstep (se 1 (by rfl) ⟨4563863, by rfl⟩ : syracuseStep 6085151 = 9127727) B9127727
theorem B4283239 : Blo 1124630 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B1269607 : Blo 1124630 1269607 := bstep (se 1 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 1269607 = 1904411) B1904411
theorem B4285183 : Blo 1124630 4285183 := bstep (se 1 (by rfl) ⟨3213887, by rfl⟩ : syracuseStep 4285183 = 6427775) B6427775
theorem B5694299 : Blo 1124630 5694299 := bstep (se 1 (by rfl) ⟨4270724, by rfl⟩ : syracuseStep 5694299 = 8541449) B8541449
theorem B16245629 : Blo 1124630 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B28173905 : Blo 1124630 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B24668221 : Blo 1124630 24668221 := bstep (se 3 (by rfl) ⟨4625291, by rfl⟩ : syracuseStep 24668221 = 9250583) B9250583
theorem B105343415 : Blo 1124630 105343415 := bstep (se 1 (by rfl) ⟨79007561, by rfl⟩ : syracuseStep 105343415 = 158015123) B158015123
theorem B8546795 : Blo 1124630 8546795 := bstep (se 1 (by rfl) ⟨6410096, by rfl⟩ : syracuseStep 8546795 = 12820193) B12820193
theorem B3796307 : Blo 1124630 3796307 := bstep (se 1 (by rfl) ⟨2847230, by rfl⟩ : syracuseStep 3796307 = 5694461) B5694461
theorem B3796415 : Blo 1124630 3796415 := bstep (se 1 (by rfl) ⟨2847311, by rfl⟩ : syracuseStep 3796415 = 5694623) B5694623
theorem B12840605 : Blo 1124630 12840605 := bstep (se 3 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 12840605 = 4815227) B4815227
theorem B1601471 : Blo 1124630 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B13889531 : Blo 1124630 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B8679419 : Blo 1124630 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B5140513 : Blo 1124630 5140513 := bstep (se 2 (by rfl) ⟨1927692, by rfl⟩ : syracuseStep 5140513 = 3855385) B3855385
theorem B10285703 : Blo 1124630 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B3797927 : Blo 1124630 3797927 := bstep (se 1 (by rfl) ⟨2848445, by rfl⟩ : syracuseStep 3797927 = 5696891) B5696891
theorem B8549711 : Blo 1124630 8549711 := bstep (se 1 (by rfl) ⟨6412283, by rfl⟩ : syracuseStep 8549711 = 12824567) B12824567
theorem B2848223 : Blo 1124630 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B7698401 : Blo 1124630 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B4880371 : Blo 1124630 4880371 := bstep (se 1 (by rfl) ⟨3660278, by rfl⟩ : syracuseStep 4880371 = 7320557) B7320557
theorem B2848841 : Blo 1124630 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B4816169 : Blo 1124630 4816169 := bstep (se 2 (by rfl) ⟨1806063, by rfl⟩ : syracuseStep 4816169 = 3612127) B3612127
theorem B3800735 : Blo 1124630 3800735 := bstep (se 1 (by rfl) ⟨2850551, by rfl⟩ : syracuseStep 3800735 = 5701103) B5701103
theorem B137101085 : Blo 1124630 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B3604439 : Blo 1124630 3604439 := bstep (se 1 (by rfl) ⟨2703329, by rfl⟩ : syracuseStep 3604439 = 5406659) B5406659
theorem B5406983 : Blo 1124630 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B5702075 : Blo 1124630 5702075 := bstep (se 1 (by rfl) ⟨4276556, by rfl⟩ : syracuseStep 5702075 = 8553113) B8553113
theorem B3801599 : Blo 1124630 3801599 := bstep (se 1 (by rfl) ⟨2851199, by rfl⟩ : syracuseStep 3801599 = 5702399) B5702399
theorem B2114980211 : Blo 1124630 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B3803759 : Blo 1124630 3803759 := bstep (se 1 (by rfl) ⟨2852819, by rfl⟩ : syracuseStep 3803759 = 5705639) B5705639
theorem B6425567 : Blo 1124630 6425567 := bstep (se 1 (by rfl) ⟨4819175, by rfl⟩ : syracuseStep 6425567 = 9638351) B9638351
theorem B34672835 : Blo 1124630 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B6854017 : Blo 1124630 6854017 := bstep (se 2 (by rfl) ⟨2570256, by rfl⟩ : syracuseStep 6854017 = 5140513) B5140513
theorem B28842155 : Blo 1124630 28842155 := bstep (se 1 (by rfl) ⟨21631616, by rfl⟩ : syracuseStep 28842155 = 43263233) B43263233
theorem B18782603 : Blo 1124630 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B8133371 : Blo 1124630 8133371 := bstep (se 1 (by rfl) ⟨6100028, by rfl⟩ : syracuseStep 8133371 = 12200057) B12200057
theorem B70228943 : Blo 1124630 70228943 := bstep (se 1 (by rfl) ⟨52671707, by rfl⟩ : syracuseStep 70228943 = 105343415) B105343415
theorem B5774291 : Blo 1124630 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B2530871 : Blo 1124630 2530871 := bstep (se 1 (by rfl) ⟨1898153, by rfl⟩ : syracuseStep 2530871 = 3796307) B3796307
theorem B2891335 : Blo 1124630 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B2530943 : Blo 1124630 2530943 := bstep (se 1 (by rfl) ⟨1898207, by rfl⟩ : syracuseStep 2530943 = 3796415) B3796415
theorem B8560403 : Blo 1124630 8560403 := bstep (se 1 (by rfl) ⟨6420302, by rfl⟩ : syracuseStep 8560403 = 12840605) B12840605
theorem B6857135 : Blo 1124630 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B2531951 : Blo 1124630 2531951 := bstep (se 1 (by rfl) ⟨1898963, by rfl⟩ : syracuseStep 2531951 = 3797927) B3797927
theorem B14426819 : Blo 1124630 14426819 := bstep (se 1 (by rfl) ⟨10820114, by rfl⟩ : syracuseStep 14426819 = 21640229) B21640229
theorem B5710985 : Blo 1124630 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B1124679 : Blo 1124630 1124679 := bstep (se 1 (by rfl) ⟨843509, by rfl⟩ : syracuseStep 1124679 = 1687019) B1687019
theorem B1124711 : Blo 1124630 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B2533823 : Blo 1124630 2533823 := bstep (se 1 (by rfl) ⟨1900367, by rfl⟩ : syracuseStep 2533823 = 3800735) B3800735
theorem B4270589 : Blo 1124630 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B91400723 : Blo 1124630 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B2402959 : Blo 1124630 2402959 := bstep (se 1 (by rfl) ⟨1802219, by rfl⟩ : syracuseStep 2402959 = 3604439) B3604439
theorem B1125071 : Blo 1124630 1125071 := bstep (se 1 (by rfl) ⟨843803, by rfl⟩ : syracuseStep 1125071 = 1687607) B1687607
theorem B1125095 : Blo 1124630 1125095 := bstep (se 1 (by rfl) ⟨843821, by rfl⟩ : syracuseStep 1125095 = 1687643) B1687643
theorem B5712767 : Blo 1124630 5712767 := bstep (se 1 (by rfl) ⟨4284575, by rfl⟩ : syracuseStep 5712767 = 8569151) B8569151
theorem B1125407 : Blo 1124630 1125407 := bstep (se 1 (by rfl) ⟨844055, by rfl⟩ : syracuseStep 1125407 = 1688111) B1688111
theorem B2534507 : Blo 1124630 2534507 := bstep (se 1 (by rfl) ⟨1900880, by rfl⟩ : syracuseStep 2534507 = 3801761) B3801761
theorem B1125531 : Blo 1124630 1125531 := bstep (se 1 (by rfl) ⟨844148, by rfl⟩ : syracuseStep 1125531 = 1688297) B1688297
theorem B1125567 : Blo 1124630 1125567 := bstep (se 1 (by rfl) ⟨844175, by rfl⟩ : syracuseStep 1125567 = 1688351) B1688351
theorem B2534831 : Blo 1124630 2534831 := bstep (se 1 (by rfl) ⟨1901123, by rfl⟩ : syracuseStep 2534831 = 3802247) B3802247
theorem B5713577 : Blo 1124630 5713577 := bstep (se 2 (by rfl) ⟨2142591, by rfl⟩ : syracuseStep 5713577 = 4285183) B4285183
theorem B4566719 : Blo 1124630 4566719 := bstep (se 1 (by rfl) ⟨3425039, by rfl⟩ : syracuseStep 4566719 = 6850079) B6850079
theorem B1126171 : Blo 1124630 1126171 := bstep (se 1 (by rfl) ⟨844628, by rfl⟩ : syracuseStep 1126171 = 1689257) B1689257
theorem B1126235 : Blo 1124630 1126235 := bstep (se 1 (by rfl) ⟨844676, by rfl⟩ : syracuseStep 1126235 = 1689353) B1689353
theorem B2568287 : Blo 1124630 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B7221383 : Blo 1124630 7221383 := bstep (se 1 (by rfl) ⟨5416037, by rfl⟩ : syracuseStep 7221383 = 10832075) B10832075
theorem B2535623 : Blo 1124630 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B1126703 : Blo 1124630 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B1126847 : Blo 1124630 1126847 := bstep (se 1 (by rfl) ⟨845135, by rfl⟩ : syracuseStep 1126847 = 1690271) B1690271
theorem B1127003 : Blo 1124630 1127003 := bstep (se 1 (by rfl) ⟨845252, by rfl⟩ : syracuseStep 1127003 = 1690505) B1690505
theorem B1127023 : Blo 1124630 1127023 := bstep (se 1 (by rfl) ⟨845267, by rfl⟩ : syracuseStep 1127023 = 1690535) B1690535
theorem B1127071 : Blo 1124630 1127071 := bstep (se 1 (by rfl) ⟨845303, by rfl⟩ : syracuseStep 1127071 = 1690607) B1690607
theorem B1127455 : Blo 1124630 1127455 := bstep (se 1 (by rfl) ⟨845591, by rfl⟩ : syracuseStep 1127455 = 1691183) B1691183
theorem B1127591 : Blo 1124630 1127591 := bstep (se 1 (by rfl) ⟨845693, by rfl⟩ : syracuseStep 1127591 = 1691387) B1691387
theorem B1127615 : Blo 1124630 1127615 := bstep (se 1 (by rfl) ⟨845711, by rfl⟩ : syracuseStep 1127615 = 1691423) B1691423
theorem B1127887 : Blo 1124630 1127887 := bstep (se 1 (by rfl) ⟨845915, by rfl⟩ : syracuseStep 1127887 = 1691831) B1691831
theorem B1127903 : Blo 1124630 1127903 := bstep (se 1 (by rfl) ⟨845927, by rfl⟩ : syracuseStep 1127903 = 1691855) B1691855
theorem B1127935 : Blo 1124630 1127935 := bstep (se 1 (by rfl) ⟨845951, by rfl⟩ : syracuseStep 1127935 = 1691903) B1691903
theorem B1128303 : Blo 1124630 1128303 := bstep (se 1 (by rfl) ⟨846227, by rfl⟩ : syracuseStep 1128303 = 1692455) B1692455
theorem B1128443 : Blo 1124630 1128443 := bstep (se 1 (by rfl) ⟨846332, by rfl⟩ : syracuseStep 1128443 = 1692665) B1692665
theorem B1128479 : Blo 1124630 1128479 := bstep (se 1 (by rfl) ⟨846359, by rfl⟩ : syracuseStep 1128479 = 1692719) B1692719
theorem B2538431 : Blo 1124630 2538431 := bstep (se 1 (by rfl) ⟨1903823, by rfl⟩ : syracuseStep 2538431 = 3807647) B3807647
theorem B9616481 : Blo 1124630 9616481 := bstep (se 2 (by rfl) ⟨3606180, by rfl⟩ : syracuseStep 9616481 = 7212361) B7212361
theorem B1424623 : Blo 1124630 1424623 := bstep (se 1 (by rfl) ⟨1068467, by rfl⟩ : syracuseStep 1424623 = 2136935) B2136935
theorem B1687433 : Blo 1124630 1687433 := bstep (se 2 (by rfl) ⟨632787, by rfl⟩ : syracuseStep 1687433 = 1265575) B1265575
theorem B10830419 : Blo 1124630 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B4571743 : Blo 1124630 4571743 := bstep (se 1 (by rfl) ⟨3428807, by rfl⟩ : syracuseStep 4571743 = 6857615) B6857615
theorem B1688231 : Blo 1124630 1688231 := bstep (se 1 (by rfl) ⟨1266173, by rfl⟩ : syracuseStep 1688231 = 2532347) B2532347
theorem B1688303 : Blo 1124630 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B1688603 : Blo 1124630 1688603 := bstep (se 1 (by rfl) ⟨1266452, by rfl⟩ : syracuseStep 1688603 = 2532905) B2532905
theorem B1689851 : Blo 1124630 1689851 := bstep (se 1 (by rfl) ⟨1267388, by rfl⟩ : syracuseStep 1689851 = 2534777) B2534777
theorem B1690079 : Blo 1124630 1690079 := bstep (se 1 (by rfl) ⟨1267559, by rfl⟩ : syracuseStep 1690079 = 2535119) B2535119
theorem B6507161 : Blo 1124630 6507161 := bstep (se 2 (by rfl) ⟨2440185, by rfl⟩ : syracuseStep 6507161 = 4880371) B4880371
theorem B9259687 : Blo 1124630 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B5786279 : Blo 1124630 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B1690655 : Blo 1124630 1690655 := bstep (se 1 (by rfl) ⟨1267991, by rfl⟩ : syracuseStep 1690655 = 2535983) B2535983
theorem B1690859 : Blo 1124630 1690859 := bstep (se 1 (by rfl) ⟨1268144, by rfl⟩ : syracuseStep 1690859 = 2536289) B2536289
theorem B10276577 : Blo 1124630 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B5132267 : Blo 1124630 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B1691627 : Blo 1124630 1691627 := bstep (se 1 (by rfl) ⟨1268720, by rfl⟩ : syracuseStep 1691627 = 2537441) B2537441
theorem B1692251 : Blo 1124630 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B7524989 : Blo 1124630 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B1692809 : Blo 1124630 1692809 := bstep (se 2 (by rfl) ⟨634803, by rfl⟩ : syracuseStep 1692809 = 1269607) B1269607
theorem B1627495 : Blo 1124630 1627495 := bstep (se 1 (by rfl) ⟨1220621, by rfl⟩ : syracuseStep 1627495 = 2441243) B2441243
theorem B16242119 : Blo 1124630 16242119 := bstep (se 1 (by rfl) ⟨12181589, by rfl⟩ : syracuseStep 16242119 = 24363179) B24363179
theorem B8542907 : Blo 1124630 8542907 := bstep (se 1 (by rfl) ⟨6407180, by rfl⟩ : syracuseStep 8542907 = 12814361) B12814361
theorem B1268671 : Blo 1124630 1268671 := bstep (se 1 (by rfl) ⟨951503, by rfl⟩ : syracuseStep 1268671 = 1903007) B1903007
theorem B10738655 : Blo 1124630 10738655 := bstep (se 1 (by rfl) ⟨8053991, by rfl⟩ : syracuseStep 10738655 = 16107983) B16107983
theorem B9624851 : Blo 1124630 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B15850831 : Blo 1124630 15850831 := bstep (se 1 (by rfl) ⟨11888123, by rfl⟩ : syracuseStep 15850831 = 23776247) B23776247
theorem B32890961 : Blo 1124630 32890961 := bstep (se 2 (by rfl) ⟨12334110, by rfl⟩ : syracuseStep 32890961 = 24668221) B24668221
theorem B4056767 : Blo 1124630 4056767 := bstep (se 1 (by rfl) ⟨3042575, by rfl⟩ : syracuseStep 4056767 = 6085151) B6085151
theorem B24340763 : Blo 1124630 24340763 := bstep (se 1 (by rfl) ⟨18255572, by rfl⟩ : syracuseStep 24340763 = 36511145) B36511145
theorem B61696637 : Blo 1124630 61696637 := bstep (se 3 (by rfl) ⟨11568119, by rfl⟩ : syracuseStep 61696637 = 23136239) B23136239
theorem B18246491 : Blo 1124630 18246491 := bstep (se 1 (by rfl) ⟨13684868, by rfl⟩ : syracuseStep 18246491 = 27369737) B27369737
theorem B11562043 : Blo 1124630 11562043 := bstep (se 1 (by rfl) ⟨8671532, by rfl⟩ : syracuseStep 11562043 = 17343065) B17343065
theorem B3796199 : Blo 1124630 3796199 := bstep (se 1 (by rfl) ⟨2847149, by rfl⟩ : syracuseStep 3796199 = 5694299) B5694299
theorem B8547767 : Blo 1124630 8547767 := bstep (se 1 (by rfl) ⟨6410825, by rfl⟩ : syracuseStep 8547767 = 12821651) B12821651
theorem B164392415 : Blo 1124630 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B5697863 : Blo 1124630 5697863 := bstep (se 1 (by rfl) ⟨4273397, by rfl⟩ : syracuseStep 5697863 = 8546795) B8546795
theorem B4878847 : Blo 1124630 4878847 := bstep (se 1 (by rfl) ⟨3659135, by rfl⟩ : syracuseStep 4878847 = 7318271) B7318271
theorem B9270605 : Blo 1124630 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B2848385 : Blo 1124630 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B2848871 : Blo 1124630 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B5699807 : Blo 1124630 5699807 := bstep (se 1 (by rfl) ⟨4274855, by rfl⟩ : syracuseStep 5699807 = 8549711) B8549711
theorem B1898815 : Blo 1124630 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B1899227 : Blo 1124630 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B4816219 : Blo 1124630 4816219 := bstep (se 1 (by rfl) ⟨3612164, by rfl⟩ : syracuseStep 4816219 = 7224329) B7224329
theorem B3210779 : Blo 1124630 3210779 := bstep (se 1 (by rfl) ⟨2408084, by rfl⟩ : syracuseStep 3210779 = 4816169) B4816169
theorem B3604655 : Blo 1124630 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B3801383 : Blo 1124630 3801383 := bstep (se 1 (by rfl) ⟨2851037, by rfl⟩ : syracuseStep 3801383 = 5702075) B5702075
theorem B6095657 : Blo 1124630 6095657 := bstep (se 2 (by rfl) ⟨2285871, by rfl⟩ : syracuseStep 6095657 = 4571743) B4571743
theorem B6851051 : Blo 1124630 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B5016659 : Blo 1124630 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B49384997 : Blo 1124630 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B12521735 : Blo 1124630 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B5706935 : Blo 1124630 5706935 := bstep (se 1 (by rfl) ⟨4280201, by rfl⟩ : syracuseStep 5706935 = 8560403) B8560403
theorem B21927307 : Blo 1124630 21927307 := bstep (se 1 (by rfl) ⟨16445480, by rfl⟩ : syracuseStep 21927307 = 32890961) B32890961
theorem B3807323 : Blo 1124630 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B16227175 : Blo 1124630 16227175 := bstep (se 1 (by rfl) ⟨12170381, by rfl⟩ : syracuseStep 16227175 = 24340763) B24340763
theorem B41131091 : Blo 1124630 41131091 := bstep (se 1 (by rfl) ⟨30848318, by rfl⟩ : syracuseStep 41131091 = 61696637) B61696637
theorem B12164327 : Blo 1124630 12164327 := bstep (se 1 (by rfl) ⟨9123245, by rfl⟩ : syracuseStep 12164327 = 18246491) B18246491
theorem B3808511 : Blo 1124630 3808511 := bstep (se 1 (by rfl) ⟨2856383, by rfl⟩ : syracuseStep 3808511 = 5712767) B5712767
theorem B2530799 : Blo 1124630 2530799 := bstep (se 1 (by rfl) ⟨1898099, by rfl⟩ : syracuseStep 2530799 = 3796199) B3796199
theorem B3809051 : Blo 1124630 3809051 := bstep (se 1 (by rfl) ⟨2856788, by rfl⟩ : syracuseStep 3809051 = 5713577) B5713577
theorem B1712191 : Blo 1124630 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B2531753 : Blo 1124630 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B2140519 : Blo 1124630 2140519 := bstep (se 1 (by rfl) ⟨1605389, by rfl⟩ : syracuseStep 2140519 = 3210779) B3210779
theorem B1124955 : Blo 1124630 1124955 := bstep (se 1 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 1124955 = 1687433) B1687433
theorem B2534399 : Blo 1124630 2534399 := bstep (se 1 (by rfl) ⟨1900799, by rfl⟩ : syracuseStep 2534399 = 3801599) B3801599
theorem B7220279 : Blo 1124630 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B1125487 : Blo 1124630 1125487 := bstep (se 1 (by rfl) ⟨844115, by rfl⟩ : syracuseStep 1125487 = 1688231) B1688231
theorem B1125535 : Blo 1124630 1125535 := bstep (se 1 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 1125535 = 1688303) B1688303
theorem B1125735 : Blo 1124630 1125735 := bstep (se 1 (by rfl) ⟨844301, by rfl⟩ : syracuseStep 1125735 = 1688603) B1688603
theorem B1126567 : Blo 1124630 1126567 := bstep (se 1 (by rfl) ⟨844925, by rfl⟩ : syracuseStep 1126567 = 1689851) B1689851
theorem B1409986807 : Blo 1124630 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B1126719 : Blo 1124630 1126719 := bstep (se 1 (by rfl) ⟨845039, by rfl⟩ : syracuseStep 1126719 = 1690079) B1690079
theorem B2535839 : Blo 1124630 2535839 := bstep (se 1 (by rfl) ⟨1901879, by rfl⟩ : syracuseStep 2535839 = 3803759) B3803759
theorem B4338107 : Blo 1124630 4338107 := bstep (se 1 (by rfl) ⟨3253580, by rfl⟩ : syracuseStep 4338107 = 6507161) B6507161
theorem B1127103 : Blo 1124630 1127103 := bstep (se 1 (by rfl) ⟨845327, by rfl⟩ : syracuseStep 1127103 = 1690655) B1690655
theorem B1127239 : Blo 1124630 1127239 := bstep (se 1 (by rfl) ⟨845429, by rfl⟩ : syracuseStep 1127239 = 1690859) B1690859
theorem B3421511 : Blo 1124630 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B1127751 : Blo 1124630 1127751 := bstep (se 1 (by rfl) ⟨845813, by rfl⟩ : syracuseStep 1127751 = 1691627) B1691627
theorem B23115223 : Blo 1124630 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B1128167 : Blo 1124630 1128167 := bstep (se 1 (by rfl) ⟨846125, by rfl⟩ : syracuseStep 1128167 = 1692251) B1692251
theorem B1128539 : Blo 1124630 1128539 := bstep (se 1 (by rfl) ⟨846404, by rfl⟩ : syracuseStep 1128539 = 1692809) B1692809
theorem B10828079 : Blo 1124630 10828079 := bstep (se 1 (by rfl) ⟨8121059, by rfl⟩ : syracuseStep 10828079 = 16242119) B16242119
theorem B15416057 : Blo 1124630 15416057 := bstep (se 2 (by rfl) ⟨5781021, by rfl⟩ : syracuseStep 15416057 = 11562043) B11562043
theorem B5422247 : Blo 1124630 5422247 := bstep (se 1 (by rfl) ⟨4066685, by rfl⟩ : syracuseStep 5422247 = 8133371) B8133371
theorem B3849527 : Blo 1124630 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B7159103 : Blo 1124630 7159103 := bstep (se 1 (by rfl) ⟨5369327, by rfl⟩ : syracuseStep 7159103 = 10738655) B10738655
theorem B1687247 : Blo 1124630 1687247 := bstep (se 1 (by rfl) ⟨1265435, by rfl⟩ : syracuseStep 1687247 = 2530871) B2530871
theorem B1687295 : Blo 1124630 1687295 := bstep (se 1 (by rfl) ⟨1265471, by rfl⟩ : syracuseStep 1687295 = 2530943) B2530943
theorem B4571423 : Blo 1124630 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B1687967 : Blo 1124630 1687967 := bstep (se 1 (by rfl) ⟨1265975, by rfl⟩ : syracuseStep 1687967 = 2531951) B2531951
theorem B9617879 : Blo 1124630 9617879 := bstep (se 1 (by rfl) ⟨7213409, by rfl⟩ : syracuseStep 9617879 = 14426819) B14426819
theorem B6505129 : Blo 1124630 6505129 := bstep (se 2 (by rfl) ⟨2439423, by rfl⟩ : syracuseStep 6505129 = 4878847) B4878847
theorem B2704511 : Blo 1124630 2704511 := bstep (se 1 (by rfl) ⟨2028383, by rfl⟩ : syracuseStep 2704511 = 4056767) B4056767
theorem B1689215 : Blo 1124630 1689215 := bstep (se 1 (by rfl) ⟨1266911, by rfl⟩ : syracuseStep 1689215 = 2533823) B2533823
theorem B60933815 : Blo 1124630 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B1689671 : Blo 1124630 1689671 := bstep (se 1 (by rfl) ⟨1267253, by rfl⟩ : syracuseStep 1689671 = 2534507) B2534507
theorem B1689887 : Blo 1124630 1689887 := bstep (se 1 (by rfl) ⟨1267415, by rfl⟩ : syracuseStep 1689887 = 2534831) B2534831
theorem B109594943 : Blo 1124630 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B1690415 : Blo 1124630 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B6180403 : Blo 1124630 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B1691561 : Blo 1124630 1691561 := bstep (se 2 (by rfl) ⟨634335, by rfl⟩ : syracuseStep 1691561 = 1268671) B1268671
theorem B1266151 : Blo 1124630 1266151 := bstep (se 1 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 1266151 = 1899227) B1899227
theorem B1692287 : Blo 1124630 1692287 := bstep (se 1 (by rfl) ⟨1269215, by rfl⟩ : syracuseStep 1692287 = 2538431) B2538431
theorem B6410987 : Blo 1124630 6410987 := bstep (se 1 (by rfl) ⟨4808240, by rfl⟩ : syracuseStep 6410987 = 9616481) B9616481
theorem B3855113 : Blo 1124630 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B3857519 : Blo 1124630 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B4283711 : Blo 1124630 4283711 := bstep (se 1 (by rfl) ⟨3212783, by rfl⟩ : syracuseStep 4283711 = 6425567) B6425567
theorem B3203945 : Blo 1124630 3203945 := bstep (se 2 (by rfl) ⟨1201479, by rfl⟩ : syracuseStep 3203945 = 2402959) B2402959
theorem B19228103 : Blo 1124630 19228103 := bstep (se 1 (by rfl) ⟨14421077, by rfl⟩ : syracuseStep 19228103 = 28842155) B28842155
theorem B5695271 : Blo 1124630 5695271 := bstep (se 1 (by rfl) ⟨4271453, by rfl⟩ : syracuseStep 5695271 = 8542907) B8542907
theorem B46819295 : Blo 1124630 46819295 := bstep (se 1 (by rfl) ⟨35114471, by rfl⟩ : syracuseStep 46819295 = 70228943) B70228943
theorem B6416567 : Blo 1124630 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B2847059 : Blo 1124630 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B9138689 : Blo 1124630 9138689 := bstep (se 2 (by rfl) ⟨3427008, by rfl⟩ : syracuseStep 9138689 = 6854017) B6854017
theorem B8679973 : Blo 1124630 8679973 := bstep (se 4 (by rfl) ⟨813747, by rfl⟩ : syracuseStep 8679973 = 1627495) B1627495
theorem B5698511 : Blo 1124630 5698511 := bstep (se 1 (by rfl) ⟨4273883, by rfl⟩ : syracuseStep 5698511 = 8547767) B8547767
theorem B3044479 : Blo 1124630 3044479 := bstep (se 1 (by rfl) ⟨2283359, by rfl⟩ : syracuseStep 3044479 = 4566719) B4566719
theorem B4814255 : Blo 1124630 4814255 := bstep (se 1 (by rfl) ⟨3610691, by rfl⟩ : syracuseStep 4814255 = 7221383) B7221383
theorem B3798575 : Blo 1124630 3798575 := bstep (se 1 (by rfl) ⟨2848931, by rfl⟩ : syracuseStep 3798575 = 5697863) B5697863
theorem B1898923 : Blo 1124630 1898923 := bstep (se 1 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 1898923 = 2848385) B2848385
theorem B1899247 : Blo 1124630 1899247 := bstep (se 1 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 1899247 = 2848871) B2848871
theorem B3799871 : Blo 1124630 3799871 := bstep (se 1 (by rfl) ⟨2849903, by rfl⟩ : syracuseStep 3799871 = 5699807) B5699807
theorem B1899497 : Blo 1124630 1899497 := bstep (se 2 (by rfl) ⟨712311, by rfl⟩ : syracuseStep 1899497 = 1424623) B1424623
theorem B21134441 : Blo 1124630 21134441 := bstep (se 2 (by rfl) ⟨7925415, by rfl⟩ : syracuseStep 21134441 = 15850831) B15850831
theorem B6421625 : Blo 1124630 6421625 := bstep (se 2 (by rfl) ⟨2408109, by rfl⟩ : syracuseStep 6421625 = 4816219) B4816219
theorem B3047615 : Blo 1124630 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B4063771 : Blo 1124630 4063771 := bstep (se 1 (by rfl) ⟨3047828, by rfl⟩ : syracuseStep 4063771 = 6095657) B6095657
theorem B1803007 : Blo 1124630 1803007 := bstep (se 1 (by rfl) ⟨1352255, by rfl⟩ : syracuseStep 1803007 = 2704511) B2704511
theorem B53511029 : Blo 1124630 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B2854025 : Blo 1124630 2854025 := bstep (se 2 (by rfl) ⟨1070259, by rfl⟩ : syracuseStep 2854025 = 2140519) B2140519
theorem B3804623 : Blo 1124630 3804623 := bstep (se 1 (by rfl) ⟨2853467, by rfl⟩ : syracuseStep 3804623 = 5706935) B5706935
theorem B2855807 : Blo 1124630 2855807 := bstep (se 1 (by rfl) ⟨2141855, by rfl⟩ : syracuseStep 2855807 = 4283711) B4283711
theorem B30079718549 : Blo 1124630 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B2135963 : Blo 1124630 2135963 := bstep (se 1 (by rfl) ⟨1601972, by rfl⟩ : syracuseStep 2135963 = 3203945) B3203945
theorem B11573297 : Blo 1124630 11573297 := bstep (se 2 (by rfl) ⟨4339986, by rfl⟩ : syracuseStep 11573297 = 8679973) B8679973
theorem B12818735 : Blo 1124630 12818735 := bstep (se 1 (by rfl) ⟨9614051, by rfl⟩ : syracuseStep 12818735 = 19228103) B19228103
theorem B29236409 : Blo 1124630 29236409 := bstep (se 2 (by rfl) ⟨10963653, by rfl⟩ : syracuseStep 29236409 = 21927307) B21927307
theorem B2892071 : Blo 1124630 2892071 := bstep (se 1 (by rfl) ⟨2169053, by rfl⟩ : syracuseStep 2892071 = 4338107) B4338107
theorem B2531897 : Blo 1124630 2531897 := bstep (se 2 (by rfl) ⟨949461, by rfl⟩ : syracuseStep 2531897 = 1898923) B1898923
theorem B2532329 : Blo 1124630 2532329 := bstep (se 2 (by rfl) ⟨949623, by rfl⟩ : syracuseStep 2532329 = 1899247) B1899247
theorem B2532383 : Blo 1124630 2532383 := bstep (se 1 (by rfl) ⟨1899287, by rfl⟩ : syracuseStep 2532383 = 3798575) B3798575
theorem B21636233 : Blo 1124630 21636233 := bstep (se 2 (by rfl) ⟨8113587, by rfl⟩ : syracuseStep 21636233 = 16227175) B16227175
theorem B7218719 : Blo 1124630 7218719 := bstep (se 1 (by rfl) ⟨5414039, by rfl⟩ : syracuseStep 7218719 = 10828079) B10828079
theorem B2533247 : Blo 1124630 2533247 := bstep (se 1 (by rfl) ⟨1899935, by rfl⟩ : syracuseStep 2533247 = 3799871) B3799871
theorem B3614831 : Blo 1124630 3614831 := bstep (se 1 (by rfl) ⟨2711123, by rfl⟩ : syracuseStep 3614831 = 5422247) B5422247
theorem B2566351 : Blo 1124630 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B1124831 : Blo 1124630 1124831 := bstep (se 1 (by rfl) ⟨843623, by rfl⟩ : syracuseStep 1124831 = 1687247) B1687247
theorem B1124863 : Blo 1124630 1124863 := bstep (se 1 (by rfl) ⟨843647, by rfl⟩ : syracuseStep 1124863 = 1687295) B1687295
theorem B2403103 : Blo 1124630 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B2534255 : Blo 1124630 2534255 := bstep (se 1 (by rfl) ⟨1900691, by rfl⟩ : syracuseStep 2534255 = 3801383) B3801383
theorem B1125311 : Blo 1124630 1125311 := bstep (se 1 (by rfl) ⟨843983, by rfl⟩ : syracuseStep 1125311 = 1687967) B1687967
theorem B1126143 : Blo 1124630 1126143 := bstep (se 1 (by rfl) ⟨844607, by rfl⟩ : syracuseStep 1126143 = 1689215) B1689215
theorem B1126447 : Blo 1124630 1126447 := bstep (se 1 (by rfl) ⟨844835, by rfl⟩ : syracuseStep 1126447 = 1689671) B1689671
theorem B1126591 : Blo 1124630 1126591 := bstep (se 1 (by rfl) ⟨844943, by rfl⟩ : syracuseStep 1126591 = 1689887) B1689887
theorem B4567367 : Blo 1124630 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B1126943 : Blo 1124630 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B1127707 : Blo 1124630 1127707 := bstep (se 1 (by rfl) ⟨845780, by rfl⟩ : syracuseStep 1127707 = 1691561) B1691561
theorem B1128191 : Blo 1124630 1128191 := bstep (se 1 (by rfl) ⟨846143, by rfl⟩ : syracuseStep 1128191 = 1692287) B1692287
theorem B4273991 : Blo 1124630 4273991 := bstep (se 1 (by rfl) ⟨3205493, by rfl⟩ : syracuseStep 4273991 = 6410987) B6410987
theorem B2570075 : Blo 1124630 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B2538215 : Blo 1124630 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B8240537 : Blo 1124630 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B2571679 : Blo 1124630 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B8109551 : Blo 1124630 8109551 := bstep (se 1 (by rfl) ⟨6082163, by rfl⟩ : syracuseStep 8109551 = 12164327) B12164327
theorem B2539007 : Blo 1124630 2539007 := bstep (se 1 (by rfl) ⟨1904255, by rfl⟩ : syracuseStep 2539007 = 3808511) B3808511
theorem B1687199 : Blo 1124630 1687199 := bstep (se 1 (by rfl) ⟨1265399, by rfl⟩ : syracuseStep 1687199 = 2530799) B2530799
theorem B2539367 : Blo 1124630 2539367 := bstep (se 1 (by rfl) ⟨1904525, by rfl⟩ : syracuseStep 2539367 = 3809051) B3809051
theorem B1687835 : Blo 1124630 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B1688201 : Blo 1124630 1688201 := bstep (se 2 (by rfl) ⟨633075, by rfl⟩ : syracuseStep 1688201 = 1266151) B1266151
theorem B31212863 : Blo 1124630 31212863 := bstep (se 1 (by rfl) ⟨23409647, by rfl⟩ : syracuseStep 31212863 = 46819295) B46819295
theorem B4277711 : Blo 1124630 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B30820297 : Blo 1124630 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B1689599 : Blo 1124630 1689599 := bstep (se 1 (by rfl) ⟨1267199, by rfl⟩ : syracuseStep 1689599 = 2534399) B2534399
theorem B1690559 : Blo 1124630 1690559 := bstep (se 1 (by rfl) ⟨1267919, by rfl⟩ : syracuseStep 1690559 = 2535839) B2535839
theorem B2281007 : Blo 1124630 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B10277371 : Blo 1124630 10277371 := bstep (se 1 (by rfl) ⟨7708028, by rfl⟩ : syracuseStep 10277371 = 15416057) B15416057
theorem B1266331 : Blo 1124630 1266331 := bstep (se 1 (by rfl) ⟨949748, by rfl⟩ : syracuseStep 1266331 = 1899497) B1899497
theorem B4281083 : Blo 1124630 4281083 := bstep (se 1 (by rfl) ⟨3210812, by rfl⟩ : syracuseStep 4281083 = 6421625) B6421625
theorem B4772735 : Blo 1124630 4772735 := bstep (se 1 (by rfl) ⟨3579551, by rfl⟩ : syracuseStep 4772735 = 7159103) B7159103
theorem B2282921 : Blo 1124630 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B6411919 : Blo 1124630 6411919 := bstep (se 1 (by rfl) ⟨4808939, by rfl⟩ : syracuseStep 6411919 = 9617879) B9617879
theorem B40622543 : Blo 1124630 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B73063295 : Blo 1124630 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B32923331 : Blo 1124630 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B8347823 : Blo 1124630 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B34694021 : Blo 1124630 34694021 := bstep (se 4 (by rfl) ⟨3252564, by rfl⟩ : syracuseStep 34694021 = 6505129) B6505129
theorem B27420727 : Blo 1124630 27420727 := bstep (se 1 (by rfl) ⟨20565545, by rfl⟩ : syracuseStep 27420727 = 41131091) B41131091
theorem B3796847 : Blo 1124630 3796847 := bstep (se 1 (by rfl) ⟨2847635, by rfl⟩ : syracuseStep 3796847 = 5695271) B5695271
theorem B4059305 : Blo 1124630 4059305 := bstep (se 2 (by rfl) ⟨1522239, by rfl⟩ : syracuseStep 4059305 = 3044479) B3044479
theorem B4813519 : Blo 1124630 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B1898039 : Blo 1124630 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B6092459 : Blo 1124630 6092459 := bstep (se 1 (by rfl) ⟨4569344, by rfl⟩ : syracuseStep 6092459 = 9138689) B9138689
theorem B3799007 : Blo 1124630 3799007 := bstep (se 1 (by rfl) ⟨2849255, by rfl⟩ : syracuseStep 3799007 = 5698511) B5698511
theorem B3209503 : Blo 1124630 3209503 := bstep (se 1 (by rfl) ⟨2407127, by rfl⟩ : syracuseStep 3209503 = 4814255) B4814255
theorem B14089627 : Blo 1124630 14089627 := bstep (se 1 (by rfl) ⟨10567220, by rfl⟩ : syracuseStep 14089627 = 21134441) B21134441
theorem B2031743 : Blo 1124630 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B20808575 : Blo 1124630 20808575 := bstep (se 1 (by rfl) ⟨15606431, by rfl⟩ : syracuseStep 20808575 = 31212863) B31212863
theorem B2851807 : Blo 1124630 2851807 := bstep (se 1 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 2851807 = 4277711) B4277711
theorem B1902683 : Blo 1124630 1902683 := bstep (se 1 (by rfl) ⟨1427012, by rfl⟩ : syracuseStep 1902683 = 2854025) B2854025
theorem B41093729 : Blo 1124630 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B2854055 : Blo 1124630 2854055 := bstep (se 1 (by rfl) ⟨2140541, by rfl⟩ : syracuseStep 2854055 = 4281083) B4281083
theorem B1903871 : Blo 1124630 1903871 := bstep (se 1 (by rfl) ⟨1427903, by rfl⟩ : syracuseStep 1903871 = 2855807) B2855807
theorem B14424155 : Blo 1124630 14424155 := bstep (se 1 (by rfl) ⟨10818116, by rfl⟩ : syracuseStep 14424155 = 21636233) B21636233
theorem B2531231 : Blo 1124630 2531231 := bstep (se 1 (by rfl) ⟨1898423, by rfl⟩ : syracuseStep 2531231 = 3796847) B3796847
theorem B1713383 : Blo 1124630 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B2532671 : Blo 1124630 2532671 := bstep (se 1 (by rfl) ⟨1899503, by rfl⟩ : syracuseStep 2532671 = 3799007) B3799007
theorem B18786169 : Blo 1124630 18786169 := bstep (se 2 (by rfl) ⟨7044813, by rfl⟩ : syracuseStep 18786169 = 14089627) B14089627
theorem B1124799 : Blo 1124630 1124799 := bstep (se 1 (by rfl) ⟨843599, by rfl⟩ : syracuseStep 1124799 = 1687199) B1687199
theorem B1125223 : Blo 1124630 1125223 := bstep (se 1 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 1125223 = 1687835) B1687835
theorem B1125467 : Blo 1124630 1125467 := bstep (se 1 (by rfl) ⟨844100, by rfl⟩ : syracuseStep 1125467 = 1688201) B1688201
theorem B5418361 : Blo 1124630 5418361 := bstep (se 2 (by rfl) ⟨2031885, by rfl⟩ : syracuseStep 5418361 = 4063771) B4063771
theorem B7712189 : Blo 1124630 7712189 := bstep (se 3 (by rfl) ⟨1446035, by rfl⟩ : syracuseStep 7712189 = 2892071) B2892071
theorem B2404009 : Blo 1124630 2404009 := bstep (se 2 (by rfl) ⟨901503, by rfl⟩ : syracuseStep 2404009 = 1803007) B1803007
theorem B1126399 : Blo 1124630 1126399 := bstep (se 1 (by rfl) ⟨844799, by rfl⟩ : syracuseStep 1126399 = 1689599) B1689599
theorem B1127039 : Blo 1124630 1127039 := bstep (se 1 (by rfl) ⟨845279, by rfl⟩ : syracuseStep 1127039 = 1690559) B1690559
theorem B2536415 : Blo 1124630 2536415 := bstep (se 1 (by rfl) ⟨1902311, by rfl⟩ : syracuseStep 2536415 = 3804623) B3804623
theorem B3421801 : Blo 1124630 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B20053145699 : Blo 1124630 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B1521947 : Blo 1124630 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B1423975 : Blo 1124630 1423975 := bstep (se 1 (by rfl) ⟨1067981, by rfl⟩ : syracuseStep 1423975 = 2135963) B2135963
theorem B7715531 : Blo 1124630 7715531 := bstep (se 1 (by rfl) ⟨5786648, by rfl⟩ : syracuseStep 7715531 = 11573297) B11573297
theorem B27081695 : Blo 1124630 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B48708863 : Blo 1124630 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B203636693 : Blo 1124630 203636693 := bstep (se 7 (by rfl) ⟨2386367, by rfl⟩ : syracuseStep 203636693 = 4772735) B4772735
theorem B1687931 : Blo 1124630 1687931 := bstep (se 1 (by rfl) ⟨1265948, by rfl⟩ : syracuseStep 1687931 = 2531897) B2531897
theorem B1688219 : Blo 1124630 1688219 := bstep (se 1 (by rfl) ⟨1266164, by rfl⟩ : syracuseStep 1688219 = 2532329) B2532329
theorem B1688255 : Blo 1124630 1688255 := bstep (se 1 (by rfl) ⟨1266191, by rfl⟩ : syracuseStep 1688255 = 2532383) B2532383
theorem B1688441 : Blo 1124630 1688441 := bstep (se 2 (by rfl) ⟨633165, by rfl⟩ : syracuseStep 1688441 = 1266331) B1266331
theorem B1688831 : Blo 1124630 1688831 := bstep (se 1 (by rfl) ⟨1266623, by rfl⟩ : syracuseStep 1688831 = 2533247) B2533247
theorem B2409887 : Blo 1124630 2409887 := bstep (se 1 (by rfl) ⟨1807415, by rfl⟩ : syracuseStep 2409887 = 3614831) B3614831
theorem B1689503 : Blo 1124630 1689503 := bstep (se 1 (by rfl) ⟨1267127, by rfl⟩ : syracuseStep 1689503 = 2534255) B2534255
theorem B2706203 : Blo 1124630 2706203 := bstep (se 1 (by rfl) ⟨2029652, by rfl⟩ : syracuseStep 2706203 = 4059305) B4059305
theorem B4279337 : Blo 1124630 4279337 := bstep (se 2 (by rfl) ⟨1604751, by rfl⟩ : syracuseStep 4279337 = 3209503) B3209503
theorem B1265359 : Blo 1124630 1265359 := bstep (se 1 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 1265359 = 1898039) B1898039
theorem B6082685 : Blo 1124630 6082685 := bstep (se 3 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 6082685 = 2281007) B2281007
theorem B1692143 : Blo 1124630 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B3428905 : Blo 1124630 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B5493691 : Blo 1124630 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B1692671 : Blo 1124630 1692671 := bstep (se 1 (by rfl) ⟨1269503, by rfl⟩ : syracuseStep 1692671 = 2539007) B2539007
theorem B1692911 : Blo 1124630 1692911 := bstep (se 1 (by rfl) ⟨1269683, by rfl⟩ : syracuseStep 1692911 = 2539367) B2539367
theorem B35674019 : Blo 1124630 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B12179645 : Blo 1124630 12179645 := bstep (se 3 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 12179645 = 4567367) B4567367
theorem B54812645 : Blo 1124630 54812645 := bstep (se 4 (by rfl) ⟨5138685, by rfl⟩ : syracuseStep 54812645 = 10277371) B10277371
theorem B36560969 : Blo 1124630 36560969 := bstep (se 2 (by rfl) ⟨13710363, by rfl⟩ : syracuseStep 36560969 = 27420727) B27420727
theorem B3204137 : Blo 1124630 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B8545823 : Blo 1124630 8545823 := bstep (se 1 (by rfl) ⟨6409367, by rfl⟩ : syracuseStep 8545823 = 12818735) B12818735
theorem B19490939 : Blo 1124630 19490939 := bstep (se 1 (by rfl) ⟨14618204, by rfl⟩ : syracuseStep 19490939 = 29236409) B29236409
theorem B21948887 : Blo 1124630 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B5565215 : Blo 1124630 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B23129347 : Blo 1124630 23129347 := bstep (se 1 (by rfl) ⟨17347010, by rfl⟩ : syracuseStep 23129347 = 34694021) B34694021
theorem B6418025 : Blo 1124630 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B4812479 : Blo 1124630 4812479 := bstep (se 1 (by rfl) ⟨3609359, by rfl⟩ : syracuseStep 4812479 = 7218719) B7218719
theorem B8549225 : Blo 1124630 8549225 := bstep (se 2 (by rfl) ⟨3205959, by rfl⟩ : syracuseStep 8549225 = 6411919) B6411919
theorem B4061639 : Blo 1124630 4061639 := bstep (se 1 (by rfl) ⟨3046229, by rfl⟩ : syracuseStep 4061639 = 6092459) B6092459
theorem B2849327 : Blo 1124630 2849327 := bstep (se 1 (by rfl) ⟨2136995, by rfl⟩ : syracuseStep 2849327 = 4273991) B4273991
theorem B5406367 : Blo 1124630 5406367 := bstep (se 1 (by rfl) ⟨4054775, by rfl⟩ : syracuseStep 5406367 = 8109551) B8109551
theorem B1606591 : Blo 1124630 1606591 := bstep (se 1 (by rfl) ⟨1204943, by rfl⟩ : syracuseStep 1606591 = 2409887) B2409887
theorem B3802409 : Blo 1124630 3802409 := bstep (se 2 (by rfl) ⟨1425903, by rfl⟩ : syracuseStep 3802409 = 2851807) B2851807
theorem B27395819 : Blo 1124630 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B1804135 : Blo 1124630 1804135 := bstep (se 1 (by rfl) ⟨1353101, by rfl⟩ : syracuseStep 1804135 = 2706203) B2706203
theorem B2852891 : Blo 1124630 2852891 := bstep (se 1 (by rfl) ⟨2139668, by rfl⟩ : syracuseStep 2852891 = 4279337) B4279337
theorem B1902703 : Blo 1124630 1902703 := bstep (se 1 (by rfl) ⟨1427027, by rfl⟩ : syracuseStep 1902703 = 2854055) B2854055
theorem B30839129 : Blo 1124630 30839129 := bstep (se 2 (by rfl) ⟨11564673, by rfl⟩ : syracuseStep 30839129 = 23129347) B23129347
theorem B36541763 : Blo 1124630 36541763 := bstep (se 1 (by rfl) ⟨27406322, by rfl⟩ : syracuseStep 36541763 = 54812645) B54812645
theorem B3710143 : Blo 1124630 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B4562401 : Blo 1124630 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B13368763799 : Blo 1124630 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B1354495 : Blo 1124630 1354495 := bstep (se 1 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 1354495 = 2031743) B2031743
theorem B1125287 : Blo 1124630 1125287 := bstep (se 1 (by rfl) ⟨843965, by rfl⟩ : syracuseStep 1125287 = 1687931) B1687931
theorem B1125479 : Blo 1124630 1125479 := bstep (se 1 (by rfl) ⟨844109, by rfl⟩ : syracuseStep 1125479 = 1688219) B1688219
theorem B1125503 : Blo 1124630 1125503 := bstep (se 1 (by rfl) ⟨844127, by rfl⟩ : syracuseStep 1125503 = 1688255) B1688255
theorem B1125627 : Blo 1124630 1125627 := bstep (se 1 (by rfl) ⟨844220, by rfl⟩ : syracuseStep 1125627 = 1688441) B1688441
theorem B13872383 : Blo 1124630 13872383 := bstep (se 1 (by rfl) ⟨10404287, by rfl⟩ : syracuseStep 13872383 = 20808575) B20808575
theorem B1125887 : Blo 1124630 1125887 := bstep (se 1 (by rfl) ⟨844415, by rfl⟩ : syracuseStep 1125887 = 1688831) B1688831
theorem B1126335 : Blo 1124630 1126335 := bstep (se 1 (by rfl) ⟨844751, by rfl⟩ : syracuseStep 1126335 = 1689503) B1689503
theorem B25048225 : Blo 1124630 25048225 := bstep (se 2 (by rfl) ⟨9393084, by rfl⟩ : syracuseStep 25048225 = 18786169) B18786169
theorem B1128095 : Blo 1124630 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1128447 : Blo 1124630 1128447 := bstep (se 1 (by rfl) ⟨846335, by rfl⟩ : syracuseStep 1128447 = 1692671) B1692671
theorem B1128607 : Blo 1124630 1128607 := bstep (se 1 (by rfl) ⟨846455, by rfl⟩ : syracuseStep 1128607 = 1692911) B1692911
theorem B9616103 : Blo 1124630 9616103 := bstep (se 1 (by rfl) ⟨7212077, by rfl⟩ : syracuseStep 9616103 = 14424155) B14424155
theorem B7224481 : Blo 1124630 7224481 := bstep (se 2 (by rfl) ⟨2709180, by rfl⟩ : syracuseStep 7224481 = 5418361) B5418361
theorem B1687145 : Blo 1124630 1687145 := bstep (se 2 (by rfl) ⟨632679, by rfl⟩ : syracuseStep 1687145 = 1265359) B1265359
theorem B1687487 : Blo 1124630 1687487 := bstep (se 1 (by rfl) ⟨1265615, by rfl⟩ : syracuseStep 1687487 = 2531231) B2531231
theorem B4571873 : Blo 1124630 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B1688447 : Blo 1124630 1688447 := bstep (se 1 (by rfl) ⟨1266335, by rfl⟩ : syracuseStep 1688447 = 2532671) B2532671
theorem B7324921 : Blo 1124630 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B12993959 : Blo 1124630 12993959 := bstep (se 1 (by rfl) ⟨9745469, by rfl⟩ : syracuseStep 12993959 = 19490939) B19490939
theorem B14632591 : Blo 1124630 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B4278683 : Blo 1124630 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B1690943 : Blo 1124630 1690943 := bstep (se 1 (by rfl) ⟨1268207, by rfl⟩ : syracuseStep 1690943 = 2536415) B2536415
theorem B2707759 : Blo 1124630 2707759 := bstep (se 1 (by rfl) ⟨2030819, by rfl⟩ : syracuseStep 2707759 = 4061639) B4061639
theorem B1268455 : Blo 1124630 1268455 := bstep (se 1 (by rfl) ⟨951341, by rfl⟩ : syracuseStep 1268455 = 1902683) B1902683
theorem B1269247 : Blo 1124630 1269247 := bstep (se 1 (by rfl) ⟨951935, by rfl⟩ : syracuseStep 1269247 = 1903871) B1903871
theorem B4055123 : Blo 1124630 4055123 := bstep (se 1 (by rfl) ⟨3041342, by rfl⟩ : syracuseStep 4055123 = 6082685) B6082685
theorem B8544365 : Blo 1124630 8544365 := bstep (se 3 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 8544365 = 3204137) B3204137
theorem B23782679 : Blo 1124630 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B8119763 : Blo 1124630 8119763 := bstep (se 1 (by rfl) ⟨6089822, by rfl⟩ : syracuseStep 8119763 = 12179645) B12179645
theorem B3205345 : Blo 1124630 3205345 := bstep (se 2 (by rfl) ⟨1202004, by rfl⟩ : syracuseStep 3205345 = 2404009) B2404009
theorem B24373979 : Blo 1124630 24373979 := bstep (se 1 (by rfl) ⟨18280484, by rfl⟩ : syracuseStep 24373979 = 36560969) B36560969
theorem B4058525 : Blo 1124630 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B1142255 : Blo 1124630 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B5697215 : Blo 1124630 5697215 := bstep (se 1 (by rfl) ⟨4272911, by rfl⟩ : syracuseStep 5697215 = 8545823) B8545823
theorem B20574749 : Blo 1124630 20574749 := bstep (se 3 (by rfl) ⟨3857765, by rfl⟩ : syracuseStep 20574749 = 7715531) B7715531
theorem B5141459 : Blo 1124630 5141459 := bstep (se 1 (by rfl) ⟨3856094, by rfl⟩ : syracuseStep 5141459 = 7712189) B7712189
theorem B3208319 : Blo 1124630 3208319 := bstep (se 1 (by rfl) ⟨2406239, by rfl⟩ : syracuseStep 3208319 = 4812479) B4812479
theorem B5699483 : Blo 1124630 5699483 := bstep (se 1 (by rfl) ⟨4274612, by rfl⟩ : syracuseStep 5699483 = 8549225) B8549225
theorem B1898633 : Blo 1124630 1898633 := bstep (se 2 (by rfl) ⟨711987, by rfl⟩ : syracuseStep 1898633 = 1423975) B1423975
theorem B1899551 : Blo 1124630 1899551 := bstep (se 1 (by rfl) ⟨1424663, by rfl⟩ : syracuseStep 1899551 = 2849327) B2849327
theorem B18054463 : Blo 1124630 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B32472575 : Blo 1124630 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B7208489 : Blo 1124630 7208489 := bstep (se 2 (by rfl) ⟨2703183, by rfl⟩ : syracuseStep 7208489 = 5406367) B5406367
theorem B135757795 : Blo 1124630 135757795 := bstep (se 1 (by rfl) ⟨101818346, by rfl⟩ : syracuseStep 135757795 = 203636693) B203636693
theorem B3047915 : Blo 1124630 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B1901927 : Blo 1124630 1901927 := bstep (se 1 (by rfl) ⟨1426445, by rfl⟩ : syracuseStep 1901927 = 2852891) B2852891
theorem B2852455 : Blo 1124630 2852455 := bstep (se 1 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 2852455 = 4278683) B4278683
theorem B1805993 : Blo 1124630 1805993 := bstep (se 2 (by rfl) ⟨677247, by rfl⟩ : syracuseStep 1805993 = 1354495) B1354495
theorem B3610345 : Blo 1124630 3610345 := bstep (se 2 (by rfl) ⟨1353879, by rfl⟩ : syracuseStep 3610345 = 2707759) B2707759
theorem B8912509199 : Blo 1124630 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B5413175 : Blo 1124630 5413175 := bstep (se 1 (by rfl) ⟨4059881, by rfl⟩ : syracuseStep 5413175 = 8119763) B8119763
theorem B39066245 : Blo 1124630 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B33397633 : Blo 1124630 33397633 := bstep (se 2 (by rfl) ⟨12524112, by rfl⟩ : syracuseStep 33397633 = 25048225) B25048225
theorem B9248255 : Blo 1124630 9248255 := bstep (se 1 (by rfl) ⟨6936191, by rfl⟩ : syracuseStep 9248255 = 13872383) B13872383
theorem B2138879 : Blo 1124630 2138879 := bstep (se 1 (by rfl) ⟨1604159, by rfl⟩ : syracuseStep 2138879 = 3208319) B3208319
theorem B10822733 : Blo 1124630 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B1124763 : Blo 1124630 1124763 := bstep (se 1 (by rfl) ⟨843572, by rfl⟩ : syracuseStep 1124763 = 1687145) B1687145
theorem B1124991 : Blo 1124630 1124991 := bstep (se 1 (by rfl) ⟨843743, by rfl⟩ : syracuseStep 1124991 = 1687487) B1687487
theorem B1125631 : Blo 1124630 1125631 := bstep (se 1 (by rfl) ⟨844223, by rfl⟩ : syracuseStep 1125631 = 1688447) B1688447
theorem B2534939 : Blo 1124630 2534939 := bstep (se 1 (by rfl) ⟨1901204, by rfl⟩ : syracuseStep 2534939 = 3802409) B3802409
theorem B8662639 : Blo 1124630 8662639 := bstep (se 1 (by rfl) ⟨6496979, by rfl⟩ : syracuseStep 8662639 = 12993959) B12993959
theorem B18263879 : Blo 1124630 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B2142121 : Blo 1124630 2142121 := bstep (se 2 (by rfl) ⟨803295, by rfl⟩ : syracuseStep 2142121 = 1606591) B1606591
theorem B19510121 : Blo 1124630 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B1127295 : Blo 1124630 1127295 := bstep (se 1 (by rfl) ⟨845471, by rfl⟩ : syracuseStep 1127295 = 1690943) B1690943
theorem B2405513 : Blo 1124630 2405513 := bstep (se 2 (by rfl) ⟨902067, by rfl⟩ : syracuseStep 2405513 = 1804135) B1804135
theorem B2536937 : Blo 1124630 2536937 := bstep (se 2 (by rfl) ⟨951351, by rfl⟩ : syracuseStep 2536937 = 1902703) B1902703
theorem B20559419 : Blo 1124630 20559419 := bstep (se 1 (by rfl) ⟨15419564, by rfl⟩ : syracuseStep 20559419 = 30839129) B30839129
theorem B4273793 : Blo 1124630 4273793 := bstep (se 2 (by rfl) ⟨1602672, by rfl⟩ : syracuseStep 4273793 = 3205345) B3205345
theorem B24361175 : Blo 1124630 24361175 := bstep (se 1 (by rfl) ⟨18270881, by rfl⟩ : syracuseStep 24361175 = 36541763) B36541763
theorem B2703415 : Blo 1124630 2703415 := bstep (se 1 (by rfl) ⟨2027561, by rfl⟩ : syracuseStep 2703415 = 4055123) B4055123
theorem B13716499 : Blo 1124630 13716499 := bstep (se 1 (by rfl) ⟨10287374, by rfl⟩ : syracuseStep 13716499 = 20574749) B20574749
theorem B3427639 : Blo 1124630 3427639 := bstep (se 1 (by rfl) ⟨2570729, by rfl⟩ : syracuseStep 3427639 = 5141459) B5141459
theorem B1691273 : Blo 1124630 1691273 := bstep (se 2 (by rfl) ⟨634227, by rfl⟩ : syracuseStep 1691273 = 1268455) B1268455
theorem B1265755 : Blo 1124630 1265755 := bstep (se 1 (by rfl) ⟨949316, by rfl⟩ : syracuseStep 1265755 = 1898633) B1898633
theorem B24072617 : Blo 1124630 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B6410735 : Blo 1124630 6410735 := bstep (se 1 (by rfl) ⟨4808051, by rfl⟩ : syracuseStep 6410735 = 9616103) B9616103
theorem B6083201 : Blo 1124630 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B1692329 : Blo 1124630 1692329 := bstep (se 2 (by rfl) ⟨634623, by rfl⟩ : syracuseStep 1692329 = 1269247) B1269247
theorem B1266367 : Blo 1124630 1266367 := bstep (se 1 (by rfl) ⟨949775, by rfl⟩ : syracuseStep 1266367 = 1899551) B1899551
theorem B21648383 : Blo 1124630 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B4805659 : Blo 1124630 4805659 := bstep (se 1 (by rfl) ⟨3604244, by rfl⟩ : syracuseStep 4805659 = 7208489) B7208489
theorem B5696243 : Blo 1124630 5696243 := bstep (se 1 (by rfl) ⟨4272182, by rfl⟩ : syracuseStep 5696243 = 8544365) B8544365
theorem B15855119 : Blo 1124630 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B19787429 : Blo 1124630 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B16249319 : Blo 1124630 16249319 := bstep (se 1 (by rfl) ⟨12186989, by rfl⟩ : syracuseStep 16249319 = 24373979) B24373979
theorem B3798143 : Blo 1124630 3798143 := bstep (se 1 (by rfl) ⟨2848607, by rfl⟩ : syracuseStep 3798143 = 5697215) B5697215
theorem B3799655 : Blo 1124630 3799655 := bstep (se 1 (by rfl) ⟨2849741, by rfl⟩ : syracuseStep 3799655 = 5699483) B5699483
theorem B3046013 : Blo 1124630 3046013 := bstep (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) B1142255
theorem B9632641 : Blo 1124630 9632641 := bstep (se 2 (by rfl) ⟨3612240, by rfl⟩ : syracuseStep 9632641 = 7224481) B7224481
theorem B181010393 : Blo 1124630 181010393 := bstep (se 2 (by rfl) ⟨67878897, by rfl⟩ : syracuseStep 181010393 = 135757795) B135757795
theorem B3604553 : Blo 1124630 3604553 := bstep (se 2 (by rfl) ⟨1351707, by rfl⟩ : syracuseStep 3604553 = 2703415) B2703415
theorem B8127773 : Blo 1124630 8127773 := bstep (se 3 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 8127773 = 3047915) B3047915
theorem B16221869 : Blo 1124630 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B3803273 : Blo 1124630 3803273 := bstep (se 2 (by rfl) ⟨1426227, by rfl⟩ : syracuseStep 3803273 = 2852455) B2852455
theorem B18288665 : Blo 1124630 18288665 := bstep (se 2 (by rfl) ⟨6858249, by rfl⟩ : syracuseStep 18288665 = 13716499) B13716499
theorem B3608783 : Blo 1124630 3608783 := bstep (se 1 (by rfl) ⟨2706587, by rfl⟩ : syracuseStep 3608783 = 5413175) B5413175
theorem B6165503 : Blo 1124630 6165503 := bstep (se 1 (by rfl) ⟨4624127, by rfl⟩ : syracuseStep 6165503 = 9248255) B9248255
theorem B2856161 : Blo 1124630 2856161 := bstep (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) B2142121
theorem B7215155 : Blo 1124630 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B2532095 : Blo 1124630 2532095 := bstep (se 1 (by rfl) ⟨1899071, by rfl⟩ : syracuseStep 2532095 = 3798143) B3798143
theorem B13706279 : Blo 1124630 13706279 := bstep (se 1 (by rfl) ⟨10279709, by rfl⟩ : syracuseStep 13706279 = 20559419) B20559419
theorem B2533103 : Blo 1124630 2533103 := bstep (se 1 (by rfl) ⟨1899827, by rfl⟩ : syracuseStep 2533103 = 3799655) B3799655
theorem B1127515 : Blo 1124630 1127515 := bstep (se 1 (by rfl) ⟨845636, by rfl⟩ : syracuseStep 1127515 = 1691273) B1691273
theorem B4273823 : Blo 1124630 4273823 := bstep (se 1 (by rfl) ⟨3205367, by rfl⟩ : syracuseStep 4273823 = 6410735) B6410735
theorem B1128219 : Blo 1124630 1128219 := bstep (se 1 (by rfl) ⟨846164, by rfl⟩ : syracuseStep 1128219 = 1692329) B1692329
theorem B14432255 : Blo 1124630 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B5941672799 : Blo 1124630 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B11550185 : Blo 1124630 11550185 := bstep (se 2 (by rfl) ⟨4331319, by rfl⟩ : syracuseStep 11550185 = 8662639) B8662639
theorem B1687673 : Blo 1124630 1687673 := bstep (se 2 (by rfl) ⟨632877, by rfl⟩ : syracuseStep 1687673 = 1265755) B1265755
theorem B1425919 : Blo 1124630 1425919 := bstep (se 1 (by rfl) ⟨1069439, by rfl⟩ : syracuseStep 1425919 = 2138879) B2138879
theorem B1688489 : Blo 1124630 1688489 := bstep (se 2 (by rfl) ⟨633183, by rfl⟩ : syracuseStep 1688489 = 1266367) B1266367
theorem B6407545 : Blo 1124630 6407545 := bstep (se 2 (by rfl) ⟨2402829, by rfl⟩ : syracuseStep 6407545 = 4805659) B4805659
theorem B10570079 : Blo 1124630 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B1689959 : Blo 1124630 1689959 := bstep (se 1 (by rfl) ⟨1267469, by rfl⟩ : syracuseStep 1689959 = 2534939) B2534939
theorem B13191619 : Blo 1124630 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B12175919 : Blo 1124630 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B10832879 : Blo 1124630 10832879 := bstep (se 1 (by rfl) ⟨8124659, by rfl⟩ : syracuseStep 10832879 = 16249319) B16249319
theorem B1691291 : Blo 1124630 1691291 := bstep (se 1 (by rfl) ⟨1268468, by rfl⟩ : syracuseStep 1691291 = 2536937) B2536937
theorem B16240783 : Blo 1124630 16240783 := bstep (se 1 (by rfl) ⟨12180587, by rfl⟩ : syracuseStep 16240783 = 24361175) B24361175
theorem B120673595 : Blo 1124630 120673595 := bstep (se 1 (by rfl) ⟨90505196, by rfl⟩ : syracuseStep 120673595 = 181010393) B181010393
theorem B1267951 : Blo 1124630 1267951 := bstep (se 1 (by rfl) ⟨950963, by rfl⟩ : syracuseStep 1267951 = 1901927) B1901927
theorem B1203995 : Blo 1124630 1203995 := bstep (se 1 (by rfl) ⟨902996, by rfl⟩ : syracuseStep 1203995 = 1805993) B1805993
theorem B16048411 : Blo 1124630 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B26044163 : Blo 1124630 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B18280741 : Blo 1124630 18280741 := bstep (se 4 (by rfl) ⟨1713819, by rfl⟩ : syracuseStep 18280741 = 3427639) B3427639
theorem B3797495 : Blo 1124630 3797495 := bstep (se 1 (by rfl) ⟨2848121, by rfl⟩ : syracuseStep 3797495 = 5696243) B5696243
theorem B4813793 : Blo 1124630 4813793 := bstep (se 2 (by rfl) ⟨1805172, by rfl⟩ : syracuseStep 4813793 = 3610345) B3610345
theorem B13006747 : Blo 1124630 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B1603675 : Blo 1124630 1603675 := bstep (se 1 (by rfl) ⟨1202756, by rfl⟩ : syracuseStep 1603675 = 2405513) B2405513
theorem B2849195 : Blo 1124630 2849195 := bstep (se 1 (by rfl) ⟨2136896, by rfl⟩ : syracuseStep 2849195 = 4273793) B4273793
theorem B44530177 : Blo 1124630 44530177 := bstep (se 2 (by rfl) ⟨16698816, by rfl⟩ : syracuseStep 44530177 = 33397633) B33397633
theorem B12843521 : Blo 1124630 12843521 := bstep (se 2 (by rfl) ⟨4816320, by rfl⟩ : syracuseStep 12843521 = 9632641) B9632641
theorem B2030675 : Blo 1124630 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B1901225 : Blo 1124630 1901225 := bstep (se 2 (by rfl) ⟨712959, by rfl⟩ : syracuseStep 1901225 = 1425919) B1425919
theorem B10814579 : Blo 1124630 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B7046719 : Blo 1124630 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B12192443 : Blo 1124630 12192443 := bstep (se 1 (by rfl) ⟨9144332, by rfl⟩ : syracuseStep 12192443 = 18288665) B18288665
theorem B1904107 : Blo 1124630 1904107 := bstep (se 1 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 1904107 = 2856161) B2856161
theorem B342366101 : Blo 1124630 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B2138233 : Blo 1124630 2138233 := bstep (se 2 (by rfl) ⟨801837, by rfl⟩ : syracuseStep 2138233 = 1603675) B1603675
theorem B5415133 : Blo 1124630 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B2531663 : Blo 1124630 2531663 := bstep (se 1 (by rfl) ⟨1898747, by rfl⟩ : syracuseStep 2531663 = 3797495) B3797495
theorem B8562347 : Blo 1124630 8562347 := bstep (se 1 (by rfl) ⟨6421760, by rfl⟩ : syracuseStep 8562347 = 12843521) B12843521
theorem B2403035 : Blo 1124630 2403035 := bstep (se 1 (by rfl) ⟨1802276, by rfl⟩ : syracuseStep 2403035 = 3604553) B3604553
theorem B1125115 : Blo 1124630 1125115 := bstep (se 1 (by rfl) ⟨843836, by rfl⟩ : syracuseStep 1125115 = 1687673) B1687673
theorem B1125659 : Blo 1124630 1125659 := bstep (se 1 (by rfl) ⟨844244, by rfl⟩ : syracuseStep 1125659 = 1688489) B1688489
theorem B5418515 : Blo 1124630 5418515 := bstep (se 1 (by rfl) ⟨4063886, by rfl⟩ : syracuseStep 5418515 = 8127773) B8127773
theorem B2535515 : Blo 1124630 2535515 := bstep (se 1 (by rfl) ⟨1901636, by rfl⟩ : syracuseStep 2535515 = 3803273) B3803273
theorem B1126639 : Blo 1124630 1126639 := bstep (se 1 (by rfl) ⟨844979, by rfl⟩ : syracuseStep 1126639 = 1689959) B1689959
theorem B7221919 : Blo 1124630 7221919 := bstep (se 1 (by rfl) ⟨5416439, by rfl⟩ : syracuseStep 7221919 = 10832879) B10832879
theorem B1127527 : Blo 1124630 1127527 := bstep (se 1 (by rfl) ⟨845645, by rfl⟩ : syracuseStep 1127527 = 1691291) B1691291
theorem B2405855 : Blo 1124630 2405855 := bstep (se 1 (by rfl) ⟨1804391, by rfl⟩ : syracuseStep 2405855 = 3608783) B3608783
theorem B4110335 : Blo 1124630 4110335 := bstep (se 1 (by rfl) ⟨3082751, by rfl⟩ : syracuseStep 4110335 = 6165503) B6165503
theorem B321796253 : Blo 1124630 321796253 := bstep (se 3 (by rfl) ⟨60336797, by rfl⟩ : syracuseStep 321796253 = 120673595) B120673595
theorem B1688063 : Blo 1124630 1688063 := bstep (se 1 (by rfl) ⟨1266047, by rfl⟩ : syracuseStep 1688063 = 2532095) B2532095
theorem B1688735 : Blo 1124630 1688735 := bstep (se 1 (by rfl) ⟨1266551, by rfl⟩ : syracuseStep 1688735 = 2533103) B2533103
theorem B15844460797 : Blo 1124630 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B1690601 : Blo 1124630 1690601 := bstep (se 2 (by rfl) ⟨633975, by rfl⟩ : syracuseStep 1690601 = 1267951) B1267951
theorem B9621503 : Blo 1124630 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B8117279 : Blo 1124630 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B8543393 : Blo 1124630 8543393 := bstep (se 2 (by rfl) ⟨3203772, by rfl⟩ : syracuseStep 8543393 = 6407545) B6407545
theorem B17588825 : Blo 1124630 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B4810103 : Blo 1124630 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B21654377 : Blo 1124630 21654377 := bstep (se 2 (by rfl) ⟨8120391, by rfl⟩ : syracuseStep 21654377 = 16240783) B16240783
theorem B24374321 : Blo 1124630 24374321 := bstep (se 2 (by rfl) ⟨9140370, by rfl⟩ : syracuseStep 24374321 = 18280741) B18280741
theorem B9137519 : Blo 1124630 9137519 := bstep (se 1 (by rfl) ⟨6853139, by rfl⟩ : syracuseStep 9137519 = 13706279) B13706279
theorem B17362775 : Blo 1124630 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B3209195 : Blo 1124630 3209195 := bstep (se 1 (by rfl) ⟨2406896, by rfl⟩ : syracuseStep 3209195 = 4813793) B4813793
theorem B59373569 : Blo 1124630 59373569 := bstep (se 2 (by rfl) ⟨22265088, by rfl⟩ : syracuseStep 59373569 = 44530177) B44530177
theorem B2849215 : Blo 1124630 2849215 := bstep (se 1 (by rfl) ⟨2136911, by rfl⟩ : syracuseStep 2849215 = 4273823) B4273823
theorem B1899463 : Blo 1124630 1899463 := bstep (se 1 (by rfl) ⟨1424597, by rfl⟩ : syracuseStep 1899463 = 2849195) B2849195
theorem B3210653 : Blo 1124630 3210653 := bstep (se 3 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 3210653 = 1203995) B1203995
theorem B69369317 : Blo 1124630 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B7700123 : Blo 1124630 7700123 := bstep (se 1 (by rfl) ⟨5775092, by rfl⟩ : syracuseStep 7700123 = 11550185) B11550185
theorem B2850977 : Blo 1124630 2850977 := bstep (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) B2138233
theorem B7209719 : Blo 1124630 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B8128295 : Blo 1124630 8128295 := bstep (se 1 (by rfl) ⟨6096221, by rfl⟩ : syracuseStep 8128295 = 12192443) B12192443
theorem B5411519 : Blo 1124630 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B5708231 : Blo 1124630 5708231 := bstep (se 1 (by rfl) ⟨4281173, by rfl⟩ : syracuseStep 5708231 = 8562347) B8562347
theorem B11575183 : Blo 1124630 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B2532617 : Blo 1124630 2532617 := bstep (se 2 (by rfl) ⟨949731, by rfl⟩ : syracuseStep 2532617 = 1899463) B1899463
theorem B2139463 : Blo 1124630 2139463 := bstep (se 1 (by rfl) ⟨1604597, by rfl⟩ : syracuseStep 2139463 = 3209195) B3209195
theorem B2140435 : Blo 1124630 2140435 := bstep (se 1 (by rfl) ⟨1605326, by rfl⟩ : syracuseStep 2140435 = 3210653) B3210653
theorem B46246211 : Blo 1124630 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B7220177 : Blo 1124630 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B1125375 : Blo 1124630 1125375 := bstep (se 1 (by rfl) ⟨844031, by rfl⟩ : syracuseStep 1125375 = 1688063) B1688063
theorem B1125823 : Blo 1124630 1125823 := bstep (se 1 (by rfl) ⟨844367, by rfl⟩ : syracuseStep 1125823 = 1688735) B1688735
theorem B1127067 : Blo 1124630 1127067 := bstep (se 1 (by rfl) ⟨845300, by rfl⟩ : syracuseStep 1127067 = 1690601) B1690601
theorem B228244067 : Blo 1124630 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B2538809 : Blo 1124630 2538809 := bstep (se 2 (by rfl) ⟨952053, by rfl⟩ : syracuseStep 2538809 = 1904107) B1904107
theorem B1687775 : Blo 1124630 1687775 := bstep (se 1 (by rfl) ⟨1265831, by rfl⟩ : syracuseStep 1687775 = 2531663) B2531663
theorem B14436251 : Blo 1124630 14436251 := bstep (se 1 (by rfl) ⟨10827188, by rfl⟩ : syracuseStep 14436251 = 21654377) B21654377
theorem B1690343 : Blo 1124630 1690343 := bstep (se 1 (by rfl) ⟨1267757, by rfl⟩ : syracuseStep 1690343 = 2535515) B2535515
theorem B2740223 : Blo 1124630 2740223 := bstep (se 1 (by rfl) ⟨2055167, by rfl⟩ : syracuseStep 2740223 = 4110335) B4110335
theorem B20533661 : Blo 1124630 20533661 := bstep (se 3 (by rfl) ⟨3850061, by rfl⟩ : syracuseStep 20533661 = 7700123) B7700123
theorem B1267483 : Blo 1124630 1267483 := bstep (se 1 (by rfl) ⟨950612, by rfl⟩ : syracuseStep 1267483 = 1901225) B1901225
theorem B6414335 : Blo 1124630 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B21125947729 : Blo 1124630 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B5695595 : Blo 1124630 5695595 := bstep (se 1 (by rfl) ⟨4271696, by rfl⟩ : syracuseStep 5695595 = 8543393) B8543393
theorem B11725883 : Blo 1124630 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B858123341 : Blo 1124630 858123341 := bstep (se 3 (by rfl) ⟨160898126, by rfl⟩ : syracuseStep 858123341 = 321796253) B321796253
theorem B9629225 : Blo 1124630 9629225 := bstep (se 2 (by rfl) ⟨3610959, by rfl⟩ : syracuseStep 9629225 = 7221919) B7221919
theorem B3206735 : Blo 1124630 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B1602023 : Blo 1124630 1602023 := bstep (se 1 (by rfl) ⟨1201517, by rfl⟩ : syracuseStep 1602023 = 2403035) B2403035
theorem B16249547 : Blo 1124630 16249547 := bstep (se 1 (by rfl) ⟨12187160, by rfl⟩ : syracuseStep 16249547 = 24374321) B24374321
theorem B6091679 : Blo 1124630 6091679 := bstep (se 1 (by rfl) ⟨4568759, by rfl⟩ : syracuseStep 6091679 = 9137519) B9137519
theorem B37582501 : Blo 1124630 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B3798953 : Blo 1124630 3798953 := bstep (se 2 (by rfl) ⟨1424607, by rfl⟩ : syracuseStep 3798953 = 2849215) B2849215
theorem B1603903 : Blo 1124630 1603903 := bstep (se 1 (by rfl) ⟨1202927, by rfl⟩ : syracuseStep 1603903 = 2405855) B2405855
theorem B39582379 : Blo 1124630 39582379 := bstep (se 1 (by rfl) ⟨29686784, by rfl⟩ : syracuseStep 39582379 = 59373569) B59373569
theorem B14449373 : Blo 1124630 14449373 := bstep (se 3 (by rfl) ⟨2709257, by rfl⟩ : syracuseStep 14449373 = 5418515) B5418515
theorem B1900651 : Blo 1124630 1900651 := bstep (se 1 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 1900651 = 2850977) B2850977
theorem B28167930305 : Blo 1124630 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B2852617 : Blo 1124630 2852617 := bstep (se 2 (by rfl) ⟨1069731, by rfl⟩ : syracuseStep 2852617 = 2139463) B2139463
theorem B2853913 : Blo 1124630 2853913 := bstep (se 2 (by rfl) ⟨1070217, by rfl⟩ : syracuseStep 2853913 = 2140435) B2140435
theorem B3607679 : Blo 1124630 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B3805487 : Blo 1124630 3805487 := bstep (se 1 (by rfl) ⟨2854115, by rfl⟩ : syracuseStep 3805487 = 5708231) B5708231
theorem B50110001 : Blo 1124630 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B2137823 : Blo 1124630 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B2138537 : Blo 1124630 2138537 := bstep (se 2 (by rfl) ⟨801951, by rfl⟩ : syracuseStep 2138537 = 1603903) B1603903
theorem B2532635 : Blo 1124630 2532635 := bstep (se 1 (by rfl) ⟨1899476, by rfl⟩ : syracuseStep 2532635 = 3798953) B3798953
theorem B1125183 : Blo 1124630 1125183 := bstep (se 1 (by rfl) ⟨843887, by rfl⟩ : syracuseStep 1125183 = 1687775) B1687775
theorem B5418863 : Blo 1124630 5418863 := bstep (se 1 (by rfl) ⟨4064147, by rfl⟩ : syracuseStep 5418863 = 8128295) B8128295
theorem B4272061 : Blo 1124630 4272061 := bstep (se 3 (by rfl) ⟨801011, by rfl⟩ : syracuseStep 4272061 = 1602023) B1602023
theorem B1126895 : Blo 1124630 1126895 := bstep (se 1 (by rfl) ⟨845171, by rfl⟩ : syracuseStep 1126895 = 1690343) B1690343
theorem B4276223 : Blo 1124630 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B1688411 : Blo 1124630 1688411 := bstep (se 1 (by rfl) ⟨1266308, by rfl⟩ : syracuseStep 1688411 = 2532617) B2532617
theorem B7817255 : Blo 1124630 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B572082227 : Blo 1124630 572082227 := bstep (se 1 (by rfl) ⟨429061670, by rfl⟩ : syracuseStep 572082227 = 858123341) B858123341
theorem B1689977 : Blo 1124630 1689977 := bstep (se 2 (by rfl) ⟨633741, by rfl⟩ : syracuseStep 1689977 = 1267483) B1267483
theorem B10833031 : Blo 1124630 10833031 := bstep (se 1 (by rfl) ⟨8124773, by rfl⟩ : syracuseStep 10833031 = 16249547) B16249547
theorem B52776505 : Blo 1124630 52776505 := bstep (se 2 (by rfl) ⟨19791189, by rfl⟩ : syracuseStep 52776505 = 39582379) B39582379
theorem B152162711 : Blo 1124630 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B1692539 : Blo 1124630 1692539 := bstep (se 1 (by rfl) ⟨1269404, by rfl⟩ : syracuseStep 1692539 = 2538809) B2538809
theorem B4806479 : Blo 1124630 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B9624167 : Blo 1124630 9624167 := bstep (se 1 (by rfl) ⟨7218125, by rfl⟩ : syracuseStep 9624167 = 14436251) B14436251
theorem B1826815 : Blo 1124630 1826815 := bstep (se 1 (by rfl) ⟨1370111, by rfl⟩ : syracuseStep 1826815 = 2740223) B2740223
theorem B13689107 : Blo 1124630 13689107 := bstep (se 1 (by rfl) ⟨10266830, by rfl⟩ : syracuseStep 13689107 = 20533661) B20533661
theorem B3797063 : Blo 1124630 3797063 := bstep (se 1 (by rfl) ⟨2847797, by rfl⟩ : syracuseStep 3797063 = 5695595) B5695595
theorem B30830807 : Blo 1124630 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B4813451 : Blo 1124630 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B6419483 : Blo 1124630 6419483 := bstep (se 1 (by rfl) ⟨4814612, by rfl⟩ : syracuseStep 6419483 = 9629225) B9629225
theorem B4061119 : Blo 1124630 4061119 := bstep (se 1 (by rfl) ⟨3045839, by rfl⟩ : syracuseStep 4061119 = 6091679) B6091679
theorem B9632915 : Blo 1124630 9632915 := bstep (se 1 (by rfl) ⟨7224686, by rfl⟩ : syracuseStep 9632915 = 14449373) B14449373
theorem B15433577 : Blo 1124630 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B18778620203 : Blo 1124630 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B5211503 : Blo 1124630 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B381388151 : Blo 1124630 381388151 := bstep (se 1 (by rfl) ⟨286041113, by rfl⟩ : syracuseStep 381388151 = 572082227) B572082227
theorem B3803489 : Blo 1124630 3803489 := bstep (se 2 (by rfl) ⟨1426308, by rfl⟩ : syracuseStep 3803489 = 2852617) B2852617
theorem B3805217 : Blo 1124630 3805217 := bstep (se 2 (by rfl) ⟨1426956, by rfl⟩ : syracuseStep 3805217 = 2853913) B2853913
theorem B12817277 : Blo 1124630 12817277 := bstep (se 3 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 12817277 = 4806479) B4806479
theorem B3612575 : Blo 1124630 3612575 := bstep (se 1 (by rfl) ⟨2709431, by rfl⟩ : syracuseStep 3612575 = 5418863) B5418863
theorem B5414825 : Blo 1124630 5414825 := bstep (se 2 (by rfl) ⟨2030559, by rfl⟩ : syracuseStep 5414825 = 4061119) B4061119
theorem B2531375 : Blo 1124630 2531375 := bstep (se 1 (by rfl) ⟨1898531, by rfl⟩ : syracuseStep 2531375 = 3797063) B3797063
theorem B20553871 : Blo 1124630 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B2435753 : Blo 1124630 2435753 := bstep (se 2 (by rfl) ⟨913407, by rfl⟩ : syracuseStep 2435753 = 1826815) B1826815
theorem B2534201 : Blo 1124630 2534201 := bstep (se 2 (by rfl) ⟨950325, by rfl⟩ : syracuseStep 2534201 = 1900651) B1900651
theorem B1125607 : Blo 1124630 1125607 := bstep (se 1 (by rfl) ⟨844205, by rfl⟩ : syracuseStep 1125607 = 1688411) B1688411
theorem B1126651 : Blo 1124630 1126651 := bstep (se 1 (by rfl) ⟨844988, by rfl⟩ : syracuseStep 1126651 = 1689977) B1689977
theorem B2536991 : Blo 1124630 2536991 := bstep (se 1 (by rfl) ⟨1902743, by rfl⟩ : syracuseStep 2536991 = 3805487) B3805487
theorem B1128359 : Blo 1124630 1128359 := bstep (se 1 (by rfl) ⟨846269, by rfl⟩ : syracuseStep 1128359 = 1692539) B1692539
theorem B70368673 : Blo 1124630 70368673 := bstep (se 2 (by rfl) ⟨26388252, by rfl⟩ : syracuseStep 70368673 = 52776505) B52776505
theorem B33406667 : Blo 1124630 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B1425215 : Blo 1124630 1425215 := bstep (se 1 (by rfl) ⟨1068911, by rfl⟩ : syracuseStep 1425215 = 2137823) B2137823
theorem B9126071 : Blo 1124630 9126071 := bstep (se 1 (by rfl) ⟨6844553, by rfl⟩ : syracuseStep 9126071 = 13689107) B13689107
theorem B1425691 : Blo 1124630 1425691 := bstep (se 1 (by rfl) ⟨1069268, by rfl⟩ : syracuseStep 1425691 = 2138537) B2138537
theorem B1688423 : Blo 1124630 1688423 := bstep (se 1 (by rfl) ⟨1266317, by rfl⟩ : syracuseStep 1688423 = 2532635) B2532635
theorem B9620477 : Blo 1124630 9620477 := bstep (se 3 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 9620477 = 3607679) B3607679
theorem B4279655 : Blo 1124630 4279655 := bstep (se 1 (by rfl) ⟨3209741, by rfl⟩ : syracuseStep 4279655 = 6419483) B6419483
theorem B2850815 : Blo 1124630 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B101441807 : Blo 1124630 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B14444041 : Blo 1124630 14444041 := bstep (se 2 (by rfl) ⟨5416515, by rfl⟩ : syracuseStep 14444041 = 10833031) B10833031
theorem B6416111 : Blo 1124630 6416111 := bstep (se 1 (by rfl) ⟨4812083, by rfl⟩ : syracuseStep 6416111 = 9624167) B9624167
theorem B5696081 : Blo 1124630 5696081 := bstep (se 2 (by rfl) ⟨2136030, by rfl⟩ : syracuseStep 5696081 = 4272061) B4272061
theorem B3208967 : Blo 1124630 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B6421943 : Blo 1124630 6421943 := bstep (se 1 (by rfl) ⟨4816457, by rfl⟩ : syracuseStep 6421943 = 9632915) B9632915
theorem B10289051 : Blo 1124630 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B12519080135 : Blo 1124630 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B1900921 : Blo 1124630 1900921 := bstep (se 2 (by rfl) ⟨712845, by rfl⟩ : syracuseStep 1900921 = 1425691) B1425691
theorem B3474335 : Blo 1124630 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B2853103 : Blo 1124630 2853103 := bstep (se 1 (by rfl) ⟨2139827, by rfl⟩ : syracuseStep 2853103 = 4279655) B4279655
theorem B3609883 : Blo 1124630 3609883 := bstep (se 1 (by rfl) ⟨2707412, by rfl⟩ : syracuseStep 3609883 = 5414825) B5414825
theorem B2139311 : Blo 1124630 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B93824897 : Blo 1124630 93824897 := bstep (se 2 (by rfl) ⟨35184336, by rfl⟩ : syracuseStep 93824897 = 70368673) B70368673
theorem B6859367 : Blo 1124630 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B27405161 : Blo 1124630 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B1125615 : Blo 1124630 1125615 := bstep (se 1 (by rfl) ⟨844211, by rfl⟩ : syracuseStep 1125615 = 1688423) B1688423
theorem B254258767 : Blo 1124630 254258767 := bstep (se 1 (by rfl) ⟨190694075, by rfl⟩ : syracuseStep 254258767 = 381388151) B381388151
theorem B2535659 : Blo 1124630 2535659 := bstep (se 1 (by rfl) ⟨1901744, by rfl⟩ : syracuseStep 2535659 = 3803489) B3803489
theorem B2536811 : Blo 1124630 2536811 := bstep (se 1 (by rfl) ⟨1902608, by rfl⟩ : syracuseStep 2536811 = 3805217) B3805217
theorem B2408383 : Blo 1124630 2408383 := bstep (se 1 (by rfl) ⟨1806287, by rfl⟩ : syracuseStep 2408383 = 3612575) B3612575
theorem B1687583 : Blo 1124630 1687583 := bstep (se 1 (by rfl) ⟨1265687, by rfl⟩ : syracuseStep 1687583 = 2531375) B2531375
theorem B4277407 : Blo 1124630 4277407 := bstep (se 1 (by rfl) ⟨3208055, by rfl⟩ : syracuseStep 4277407 = 6416111) B6416111
theorem B1623835 : Blo 1124630 1623835 := bstep (se 1 (by rfl) ⟨1217876, by rfl⟩ : syracuseStep 1623835 = 2435753) B2435753
theorem B1689467 : Blo 1124630 1689467 := bstep (se 1 (by rfl) ⟨1267100, by rfl⟩ : syracuseStep 1689467 = 2534201) B2534201
theorem B1691327 : Blo 1124630 1691327 := bstep (se 1 (by rfl) ⟨1268495, by rfl⟩ : syracuseStep 1691327 = 2536991) B2536991
theorem B4281295 : Blo 1124630 4281295 := bstep (se 1 (by rfl) ⟨3210971, by rfl⟩ : syracuseStep 4281295 = 6421943) B6421943
theorem B22271111 : Blo 1124630 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B6084047 : Blo 1124630 6084047 := bstep (se 1 (by rfl) ⟨4563035, by rfl⟩ : syracuseStep 6084047 = 9126071) B9126071
theorem B6413651 : Blo 1124630 6413651 := bstep (se 1 (by rfl) ⟨4810238, by rfl⟩ : syracuseStep 6413651 = 9620477) B9620477
theorem B19258721 : Blo 1124630 19258721 := bstep (se 2 (by rfl) ⟨7222020, by rfl⟩ : syracuseStep 19258721 = 14444041) B14444041
theorem B8544851 : Blo 1124630 8544851 := bstep (se 1 (by rfl) ⟨6408638, by rfl⟩ : syracuseStep 8544851 = 12817277) B12817277
theorem B67627871 : Blo 1124630 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B3797387 : Blo 1124630 3797387 := bstep (se 1 (by rfl) ⟨2848040, by rfl⟩ : syracuseStep 3797387 = 5696081) B5696081
theorem B3800573 : Blo 1124630 3800573 := bstep (se 3 (by rfl) ⟨712607, by rfl⟩ : syracuseStep 3800573 = 1425215) B1425215
theorem B1900543 : Blo 1124630 1900543 := bstep (se 1 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 1900543 = 2850815) B2850815
theorem B5703209 : Blo 1124630 5703209 := bstep (se 2 (by rfl) ⟨2138703, by rfl⟩ : syracuseStep 5703209 = 4277407) B4277407
theorem B2165113 : Blo 1124630 2165113 := bstep (se 2 (by rfl) ⟨811917, by rfl⟩ : syracuseStep 2165113 = 1623835) B1623835
theorem B3804137 : Blo 1124630 3804137 := bstep (se 2 (by rfl) ⟨1426551, by rfl⟩ : syracuseStep 3804137 = 2853103) B2853103
theorem B5704829 : Blo 1124630 5704829 := bstep (se 3 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 5704829 = 2139311) B2139311
theorem B14847407 : Blo 1124630 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B5708393 : Blo 1124630 5708393 := bstep (se 2 (by rfl) ⟨2140647, by rfl⟩ : syracuseStep 5708393 = 4281295) B4281295
theorem B2531591 : Blo 1124630 2531591 := bstep (se 1 (by rfl) ⟨1898693, by rfl⟩ : syracuseStep 2531591 = 3797387) B3797387
theorem B2533715 : Blo 1124630 2533715 := bstep (se 1 (by rfl) ⟨1900286, by rfl⟩ : syracuseStep 2533715 = 3800573) B3800573
theorem B2534057 : Blo 1124630 2534057 := bstep (se 2 (by rfl) ⟨950271, by rfl⟩ : syracuseStep 2534057 = 1900543) B1900543
theorem B1125055 : Blo 1124630 1125055 := bstep (se 1 (by rfl) ⟨843791, by rfl⟩ : syracuseStep 1125055 = 1687583) B1687583
theorem B8346053423 : Blo 1124630 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B2534561 : Blo 1124630 2534561 := bstep (se 2 (by rfl) ⟨950460, by rfl⟩ : syracuseStep 2534561 = 1900921) B1900921
theorem B1126311 : Blo 1124630 1126311 := bstep (se 1 (by rfl) ⟨844733, by rfl⟩ : syracuseStep 1126311 = 1689467) B1689467
theorem B1127551 : Blo 1124630 1127551 := bstep (se 1 (by rfl) ⟨845663, by rfl⟩ : syracuseStep 1127551 = 1691327) B1691327
theorem B4275767 : Blo 1124630 4275767 := bstep (se 1 (by rfl) ⟨3206825, by rfl⟩ : syracuseStep 4275767 = 6413651) B6413651
theorem B4572911 : Blo 1124630 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B18270107 : Blo 1124630 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1690439 : Blo 1124630 1690439 := bstep (se 1 (by rfl) ⟨1267829, by rfl⟩ : syracuseStep 1690439 = 2535659) B2535659
theorem B1691207 : Blo 1124630 1691207 := bstep (se 1 (by rfl) ⟨1268405, by rfl⟩ : syracuseStep 1691207 = 2536811) B2536811
theorem B2316223 : Blo 1124630 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B4056031 : Blo 1124630 4056031 := bstep (se 1 (by rfl) ⟨3042023, by rfl⟩ : syracuseStep 4056031 = 6084047) B6084047
theorem B339011689 : Blo 1124630 339011689 := bstep (se 2 (by rfl) ⟨127129383, by rfl⟩ : syracuseStep 339011689 = 254258767) B254258767
theorem B12839147 : Blo 1124630 12839147 := bstep (se 1 (by rfl) ⟨9629360, by rfl⟩ : syracuseStep 12839147 = 19258721) B19258721
theorem B5696567 : Blo 1124630 5696567 := bstep (se 1 (by rfl) ⟨4272425, by rfl⟩ : syracuseStep 5696567 = 8544851) B8544851
theorem B4813177 : Blo 1124630 4813177 := bstep (se 2 (by rfl) ⟨1804941, by rfl⟩ : syracuseStep 4813177 = 3609883) B3609883
theorem B45085247 : Blo 1124630 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B1000798901 : Blo 1124630 1000798901 := bstep (se 5 (by rfl) ⟨46912448, by rfl⟩ : syracuseStep 1000798901 = 93824897) B93824897
theorem B3211177 : Blo 1124630 3211177 := bstep (se 2 (by rfl) ⟨1204191, by rfl⟩ : syracuseStep 3211177 = 2408383) B2408383
theorem B3802139 : Blo 1124630 3802139 := bstep (se 1 (by rfl) ⟨2851604, by rfl⟩ : syracuseStep 3802139 = 5703209) B5703209
theorem B3048607 : Blo 1124630 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B5408041 : Blo 1124630 5408041 := bstep (se 2 (by rfl) ⟨2028015, by rfl⟩ : syracuseStep 5408041 = 4056031) B4056031
theorem B3803219 : Blo 1124630 3803219 := bstep (se 1 (by rfl) ⟨2852414, by rfl⟩ : syracuseStep 3803219 = 5704829) B5704829
theorem B9898271 : Blo 1124630 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B3805595 : Blo 1124630 3805595 := bstep (se 1 (by rfl) ⟨2854196, by rfl⟩ : syracuseStep 3805595 = 5708393) B5708393
theorem B8559431 : Blo 1124630 8559431 := bstep (se 1 (by rfl) ⟨6419573, by rfl⟩ : syracuseStep 8559431 = 12839147) B12839147
theorem B3088297 : Blo 1124630 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B30056831 : Blo 1124630 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B667199267 : Blo 1124630 667199267 := bstep (se 1 (by rfl) ⟨500399450, by rfl⟩ : syracuseStep 667199267 = 1000798901) B1000798901
theorem B1126959 : Blo 1124630 1126959 := bstep (se 1 (by rfl) ⟨845219, by rfl⟩ : syracuseStep 1126959 = 1690439) B1690439
theorem B11547269 : Blo 1124630 11547269 := bstep (se 4 (by rfl) ⟨1082556, by rfl⟩ : syracuseStep 11547269 = 2165113) B2165113
theorem B2536091 : Blo 1124630 2536091 := bstep (se 1 (by rfl) ⟨1902068, by rfl⟩ : syracuseStep 2536091 = 3804137) B3804137
theorem B1127471 : Blo 1124630 1127471 := bstep (se 1 (by rfl) ⟨845603, by rfl⟩ : syracuseStep 1127471 = 1691207) B1691207
theorem B452015585 : Blo 1124630 452015585 := bstep (se 2 (by rfl) ⟨169505844, by rfl⟩ : syracuseStep 452015585 = 339011689) B339011689
theorem B1687727 : Blo 1124630 1687727 := bstep (se 1 (by rfl) ⟨1265795, by rfl⟩ : syracuseStep 1687727 = 2531591) B2531591
theorem B1689143 : Blo 1124630 1689143 := bstep (se 1 (by rfl) ⟨1266857, by rfl⟩ : syracuseStep 1689143 = 2533715) B2533715
theorem B1689371 : Blo 1124630 1689371 := bstep (se 1 (by rfl) ⟨1267028, by rfl⟩ : syracuseStep 1689371 = 2534057) B2534057
theorem B1689707 : Blo 1124630 1689707 := bstep (se 1 (by rfl) ⟨1267280, by rfl⟩ : syracuseStep 1689707 = 2534561) B2534561
theorem B22256142461 : Blo 1124630 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B4281569 : Blo 1124630 4281569 := bstep (se 2 (by rfl) ⟨1605588, by rfl⟩ : syracuseStep 4281569 = 3211177) B3211177
theorem B12180071 : Blo 1124630 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B6417569 : Blo 1124630 6417569 := bstep (se 2 (by rfl) ⟨2406588, by rfl⟩ : syracuseStep 6417569 = 4813177) B4813177
theorem B3797711 : Blo 1124630 3797711 := bstep (se 1 (by rfl) ⟨2848283, by rfl⟩ : syracuseStep 3797711 = 5696567) B5696567
theorem B2850511 : Blo 1124630 2850511 := bstep (se 1 (by rfl) ⟨2137883, by rfl⟩ : syracuseStep 2850511 = 4275767) B4275767
theorem B7210721 : Blo 1124630 7210721 := bstep (se 2 (by rfl) ⟨2704020, by rfl⟩ : syracuseStep 7210721 = 5408041) B5408041
theorem B2854379 : Blo 1124630 2854379 := bstep (se 1 (by rfl) ⟨2140784, by rfl⟩ : syracuseStep 2854379 = 4281569) B4281569
theorem B5706287 : Blo 1124630 5706287 := bstep (se 1 (by rfl) ⟨4279715, by rfl⟩ : syracuseStep 5706287 = 8559431) B8559431
theorem B16259237 : Blo 1124630 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B444799511 : Blo 1124630 444799511 := bstep (se 1 (by rfl) ⟨333599633, by rfl⟩ : syracuseStep 444799511 = 667199267) B667199267
theorem B2531807 : Blo 1124630 2531807 := bstep (se 1 (by rfl) ⟨1898855, by rfl⟩ : syracuseStep 2531807 = 3797711) B3797711
theorem B301343723 : Blo 1124630 301343723 := bstep (se 1 (by rfl) ⟨226007792, by rfl⟩ : syracuseStep 301343723 = 452015585) B452015585
theorem B1125151 : Blo 1124630 1125151 := bstep (se 1 (by rfl) ⟨843863, by rfl⟩ : syracuseStep 1125151 = 1687727) B1687727
theorem B2534759 : Blo 1124630 2534759 := bstep (se 1 (by rfl) ⟨1901069, by rfl⟩ : syracuseStep 2534759 = 3802139) B3802139
theorem B1126095 : Blo 1124630 1126095 := bstep (se 1 (by rfl) ⟨844571, by rfl⟩ : syracuseStep 1126095 = 1689143) B1689143
theorem B1126247 : Blo 1124630 1126247 := bstep (se 1 (by rfl) ⟨844685, by rfl⟩ : syracuseStep 1126247 = 1689371) B1689371
theorem B2535479 : Blo 1124630 2535479 := bstep (se 1 (by rfl) ⟨1901609, by rfl⟩ : syracuseStep 2535479 = 3803219) B3803219
theorem B1126471 : Blo 1124630 1126471 := bstep (se 1 (by rfl) ⟨844853, by rfl⟩ : syracuseStep 1126471 = 1689707) B1689707
theorem B14837428307 : Blo 1124630 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B6598847 : Blo 1124630 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B2537063 : Blo 1124630 2537063 := bstep (se 1 (by rfl) ⟨1902797, by rfl⟩ : syracuseStep 2537063 = 3805595) B3805595
theorem B20037887 : Blo 1124630 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B4278379 : Blo 1124630 4278379 := bstep (se 1 (by rfl) ⟨3208784, by rfl⟩ : syracuseStep 4278379 = 6417569) B6417569
theorem B1690727 : Blo 1124630 1690727 := bstep (se 1 (by rfl) ⟨1268045, by rfl⟩ : syracuseStep 1690727 = 2536091) B2536091
theorem B4117729 : Blo 1124630 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B8120047 : Blo 1124630 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B7698179 : Blo 1124630 7698179 := bstep (se 1 (by rfl) ⟨5773634, by rfl⟩ : syracuseStep 7698179 = 11547269) B11547269
theorem B3800681 : Blo 1124630 3800681 := bstep (se 2 (by rfl) ⟨1425255, by rfl⟩ : syracuseStep 3800681 = 2850511) B2850511
theorem B1902919 : Blo 1124630 1902919 := bstep (se 1 (by rfl) ⟨1427189, by rfl⟩ : syracuseStep 1902919 = 2854379) B2854379
theorem B5704505 : Blo 1124630 5704505 := bstep (se 2 (by rfl) ⟨2139189, by rfl⟩ : syracuseStep 5704505 = 4278379) B4278379
theorem B3804191 : Blo 1124630 3804191 := bstep (se 1 (by rfl) ⟨2853143, by rfl⟩ : syracuseStep 3804191 = 5706287) B5706287
theorem B9891618871 : Blo 1124630 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B4399231 : Blo 1124630 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B2533787 : Blo 1124630 2533787 := bstep (se 1 (by rfl) ⟨1900340, by rfl⟩ : syracuseStep 2533787 = 3800681) B3800681
theorem B1127151 : Blo 1124630 1127151 := bstep (se 1 (by rfl) ⟨845363, by rfl⟩ : syracuseStep 1127151 = 1690727) B1690727
theorem B10826729 : Blo 1124630 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B296533007 : Blo 1124630 296533007 := bstep (se 1 (by rfl) ⟨222399755, by rfl⟩ : syracuseStep 296533007 = 444799511) B444799511
theorem B1687871 : Blo 1124630 1687871 := bstep (se 1 (by rfl) ⟨1265903, by rfl⟩ : syracuseStep 1687871 = 2531807) B2531807
theorem B5490305 : Blo 1124630 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B1689839 : Blo 1124630 1689839 := bstep (se 1 (by rfl) ⟨1267379, by rfl⟩ : syracuseStep 1689839 = 2534759) B2534759
theorem B1690319 : Blo 1124630 1690319 := bstep (se 1 (by rfl) ⟨1267739, by rfl⟩ : syracuseStep 1690319 = 2535479) B2535479
theorem B1691375 : Blo 1124630 1691375 := bstep (se 1 (by rfl) ⟨1268531, by rfl⟩ : syracuseStep 1691375 = 2537063) B2537063
theorem B5132119 : Blo 1124630 5132119 := bstep (se 1 (by rfl) ⟨3849089, by rfl⟩ : syracuseStep 5132119 = 7698179) B7698179
theorem B13358591 : Blo 1124630 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B4807147 : Blo 1124630 4807147 := bstep (se 1 (by rfl) ⟨3605360, by rfl⟩ : syracuseStep 4807147 = 7210721) B7210721
theorem B10839491 : Blo 1124630 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B200895815 : Blo 1124630 200895815 := bstep (se 1 (by rfl) ⟨150671861, by rfl⟩ : syracuseStep 200895815 = 301343723) B301343723
theorem B13188825161 : Blo 1124630 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B5865641 : Blo 1124630 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B3803003 : Blo 1124630 3803003 := bstep (se 1 (by rfl) ⟨2852252, by rfl⟩ : syracuseStep 3803003 = 5704505) B5704505
theorem B133930543 : Blo 1124630 133930543 := bstep (se 1 (by rfl) ⟨100447907, by rfl⟩ : syracuseStep 133930543 = 200895815) B200895815
theorem B7217819 : Blo 1124630 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B1125247 : Blo 1124630 1125247 := bstep (se 1 (by rfl) ⟨843935, by rfl⟩ : syracuseStep 1125247 = 1687871) B1687871
theorem B1126559 : Blo 1124630 1126559 := bstep (se 1 (by rfl) ⟨844919, by rfl⟩ : syracuseStep 1126559 = 1689839) B1689839
theorem B1126879 : Blo 1124630 1126879 := bstep (se 1 (by rfl) ⟨845159, by rfl⟩ : syracuseStep 1126879 = 1690319) B1690319
theorem B2536127 : Blo 1124630 2536127 := bstep (se 1 (by rfl) ⟨1902095, by rfl⟩ : syracuseStep 2536127 = 3804191) B3804191
theorem B1127583 : Blo 1124630 1127583 := bstep (se 1 (by rfl) ⟨845687, by rfl⟩ : syracuseStep 1127583 = 1691375) B1691375
theorem B2537225 : Blo 1124630 2537225 := bstep (se 2 (by rfl) ⟨951459, by rfl⟩ : syracuseStep 2537225 = 1902919) B1902919
theorem B7226327 : Blo 1124630 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B1689191 : Blo 1124630 1689191 := bstep (se 1 (by rfl) ⟨1266893, by rfl⟩ : syracuseStep 1689191 = 2533787) B2533787
theorem B6409529 : Blo 1124630 6409529 := bstep (se 2 (by rfl) ⟨2403573, by rfl⟩ : syracuseStep 6409529 = 4807147) B4807147
theorem B3660203 : Blo 1124630 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B8905727 : Blo 1124630 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B6842825 : Blo 1124630 6842825 := bstep (se 2 (by rfl) ⟨2566059, by rfl⟩ : syracuseStep 6842825 = 5132119) B5132119
theorem B197688671 : Blo 1124630 197688671 := bstep (se 1 (by rfl) ⟨148266503, by rfl⟩ : syracuseStep 197688671 = 296533007) B296533007
theorem B4817551 : Blo 1124630 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B5937151 : Blo 1124630 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B4561883 : Blo 1124630 4561883 := bstep (se 1 (by rfl) ⟨3421412, by rfl⟩ : syracuseStep 4561883 = 6842825) B6842825
theorem B8792550107 : Blo 1124630 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B3910427 : Blo 1124630 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B1126127 : Blo 1124630 1126127 := bstep (se 1 (by rfl) ⟨844595, by rfl⟩ : syracuseStep 1126127 = 1689191) B1689191
theorem B2535335 : Blo 1124630 2535335 := bstep (se 1 (by rfl) ⟨1901501, by rfl⟩ : syracuseStep 2535335 = 3803003) B3803003
theorem B4273019 : Blo 1124630 4273019 := bstep (se 1 (by rfl) ⟨3204764, by rfl⟩ : syracuseStep 4273019 = 6409529) B6409529
theorem B2440135 : Blo 1124630 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B1690751 : Blo 1124630 1690751 := bstep (se 1 (by rfl) ⟨1268063, by rfl⟩ : syracuseStep 1690751 = 2536127) B2536127
theorem B1691483 : Blo 1124630 1691483 := bstep (se 1 (by rfl) ⟨1268612, by rfl⟩ : syracuseStep 1691483 = 2537225) B2537225
theorem B178574057 : Blo 1124630 178574057 := bstep (se 2 (by rfl) ⟨66965271, by rfl⟩ : syracuseStep 178574057 = 133930543) B133930543
theorem B4811879 : Blo 1124630 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B131792447 : Blo 1124630 131792447 := bstep (se 1 (by rfl) ⟨98844335, by rfl⟩ : syracuseStep 131792447 = 197688671) B197688671
theorem B6423401 : Blo 1124630 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B119049371 : Blo 1124630 119049371 := bstep (se 1 (by rfl) ⟨89287028, by rfl⟩ : syracuseStep 119049371 = 178574057) B178574057
theorem B13014053 : Blo 1124630 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B87861631 : Blo 1124630 87861631 := bstep (se 1 (by rfl) ⟨65896223, by rfl⟩ : syracuseStep 87861631 = 131792447) B131792447
theorem B1127167 : Blo 1124630 1127167 := bstep (se 1 (by rfl) ⟨845375, by rfl⟩ : syracuseStep 1127167 = 1690751) B1690751
theorem B1127655 : Blo 1124630 1127655 := bstep (se 1 (by rfl) ⟨845741, by rfl⟩ : syracuseStep 1127655 = 1691483) B1691483
theorem B2606951 : Blo 1124630 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B1690223 : Blo 1124630 1690223 := bstep (se 1 (by rfl) ⟨1267667, by rfl⟩ : syracuseStep 1690223 = 2535335) B2535335
theorem B7916201 : Blo 1124630 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B3041255 : Blo 1124630 3041255 := bstep (se 1 (by rfl) ⟨2280941, by rfl⟩ : syracuseStep 3041255 = 4561883) B4561883
theorem B5861700071 : Blo 1124630 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B3207919 : Blo 1124630 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B2848679 : Blo 1124630 2848679 := bstep (se 1 (by rfl) ⟨2136509, by rfl⟩ : syracuseStep 2848679 = 4273019) B4273019
theorem B1737967 : Blo 1124630 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B5277467 : Blo 1124630 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B79366247 : Blo 1124630 79366247 := bstep (se 1 (by rfl) ⟨59524685, by rfl⟩ : syracuseStep 79366247 = 119049371) B119049371
theorem B117148841 : Blo 1124630 117148841 := bstep (se 2 (by rfl) ⟨43930815, by rfl⟩ : syracuseStep 117148841 = 87861631) B87861631
theorem B1126815 : Blo 1124630 1126815 := bstep (se 1 (by rfl) ⟨845111, by rfl⟩ : syracuseStep 1126815 = 1690223) B1690223
theorem B4277225 : Blo 1124630 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B3907800047 : Blo 1124630 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B4282267 : Blo 1124630 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B8676035 : Blo 1124630 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B2027503 : Blo 1124630 2027503 := bstep (se 1 (by rfl) ⟨1520627, by rfl⟩ : syracuseStep 2027503 = 3041255) B3041255
theorem B1899119 : Blo 1124630 1899119 := bstep (se 1 (by rfl) ⟨1424339, by rfl⟩ : syracuseStep 1899119 = 2848679) B2848679
theorem B2851483 : Blo 1124630 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B5709689 : Blo 1124630 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B846573301 : Blo 1124630 846573301 := bstep (se 5 (by rfl) ⟨39683123, by rfl⟩ : syracuseStep 846573301 = 79366247) B79366247
theorem B3518311 : Blo 1124630 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B2605200031 : Blo 1124630 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B78099227 : Blo 1124630 78099227 := bstep (se 1 (by rfl) ⟨58574420, by rfl⟩ : syracuseStep 78099227 = 117148841) B117148841
theorem B2703337 : Blo 1124630 2703337 := bstep (se 2 (by rfl) ⟨1013751, by rfl⟩ : syracuseStep 2703337 = 2027503) B2027503
theorem B5784023 : Blo 1124630 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B1266079 : Blo 1124630 1266079 := bstep (se 1 (by rfl) ⟨949559, by rfl⟩ : syracuseStep 1266079 = 1899119) B1899119
theorem B2317289 : Blo 1124630 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B3801977 : Blo 1124630 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B4691081 : Blo 1124630 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B3806459 : Blo 1124630 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B1688105 : Blo 1124630 1688105 := bstep (se 2 (by rfl) ⟨633039, by rfl⟩ : syracuseStep 1688105 = 1266079) B1266079
theorem B6179437 : Blo 1124630 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B4515057605 : Blo 1124630 4515057605 := bstep (se 4 (by rfl) ⟨423286650, by rfl⟩ : syracuseStep 4515057605 = 846573301) B846573301
theorem B3856015 : Blo 1124630 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B3473600041 : Blo 1124630 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B52066151 : Blo 1124630 52066151 := bstep (se 1 (by rfl) ⟨39049613, by rfl⟩ : syracuseStep 52066151 = 78099227) B78099227
theorem B14417797 : Blo 1124630 14417797 := bstep (se 4 (by rfl) ⟨1351668, by rfl⟩ : syracuseStep 14417797 = 2703337) B2703337
theorem B3010038403 : Blo 1124630 3010038403 := bstep (se 1 (by rfl) ⟨2257528802, by rfl⟩ : syracuseStep 3010038403 = 4515057605) B4515057605
theorem B4631466721 : Blo 1124630 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B34710767 : Blo 1124630 34710767 := bstep (se 1 (by rfl) ⟨26033075, by rfl⟩ : syracuseStep 34710767 = 52066151) B52066151
theorem B1125403 : Blo 1124630 1125403 := bstep (se 1 (by rfl) ⟨844052, by rfl⟩ : syracuseStep 1125403 = 1688105) B1688105
theorem B2534651 : Blo 1124630 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B8239249 : Blo 1124630 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B2537639 : Blo 1124630 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B19223729 : Blo 1124630 19223729 := bstep (se 2 (by rfl) ⟨7208898, by rfl⟩ : syracuseStep 19223729 = 14417797) B14417797
theorem B12509549 : Blo 1124630 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B5141353 : Blo 1124630 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B43942661 : Blo 1124630 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B12815819 : Blo 1124630 12815819 := bstep (se 1 (by rfl) ⟨9611864, by rfl⟩ : syracuseStep 12815819 = 19223729) B19223729
theorem B23140511 : Blo 1124630 23140511 := bstep (se 1 (by rfl) ⟨17355383, by rfl⟩ : syracuseStep 23140511 = 34710767) B34710767
theorem B6855137 : Blo 1124630 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B8339699 : Blo 1124630 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B1689767 : Blo 1124630 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B1691759 : Blo 1124630 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B4013384537 : Blo 1124630 4013384537 := bstep (se 2 (by rfl) ⟨1505019201, by rfl⟩ : syracuseStep 4013384537 = 3010038403) B3010038403
theorem B6175288961 : Blo 1124630 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B29295107 : Blo 1124630 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B10702358765 : Blo 1124630 10702358765 := bstep (se 3 (by rfl) ⟨2006692268, by rfl⟩ : syracuseStep 10702358765 = 4013384537) B4013384537
theorem B1126511 : Blo 1124630 1126511 := bstep (se 1 (by rfl) ⟨844883, by rfl⟩ : syracuseStep 1126511 = 1689767) B1689767
theorem B1127839 : Blo 1124630 1127839 := bstep (se 1 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 1127839 = 1691759) B1691759
theorem B4570091 : Blo 1124630 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B4116859307 : Blo 1124630 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B5559799 : Blo 1124630 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B8543879 : Blo 1124630 8543879 := bstep (se 1 (by rfl) ⟨6407909, by rfl⟩ : syracuseStep 8543879 = 12815819) B12815819
theorem B15427007 : Blo 1124630 15427007 := bstep (se 1 (by rfl) ⟨11570255, by rfl⟩ : syracuseStep 15427007 = 23140511) B23140511
theorem B19530071 : Blo 1124630 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B7134905843 : Blo 1124630 7134905843 := bstep (se 1 (by rfl) ⟨5351179382, by rfl⟩ : syracuseStep 7134905843 = 10702358765) B10702358765
theorem B7413065 : Blo 1124630 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B2744572871 : Blo 1124630 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B5695919 : Blo 1124630 5695919 := bstep (se 1 (by rfl) ⟨4271939, by rfl⟩ : syracuseStep 5695919 = 8543879) B8543879
theorem B10284671 : Blo 1124630 10284671 := bstep (se 1 (by rfl) ⟨7713503, by rfl⟩ : syracuseStep 10284671 = 15427007) B15427007
theorem B3046727 : Blo 1124630 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B4756603895 : Blo 1124630 4756603895 := bstep (se 1 (by rfl) ⟨3567452921, by rfl⟩ : syracuseStep 4756603895 = 7134905843) B7134905843
theorem B6856447 : Blo 1124630 6856447 := bstep (se 1 (by rfl) ⟨5142335, by rfl⟩ : syracuseStep 6856447 = 10284671) B10284671
theorem B13020047 : Blo 1124630 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B1829715247 : Blo 1124630 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B4942043 : Blo 1124630 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B3797279 : Blo 1124630 3797279 := bstep (se 1 (by rfl) ⟨2847959, by rfl⟩ : syracuseStep 3797279 = 5695919) B5695919
theorem B2031151 : Blo 1124630 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B2531519 : Blo 1124630 2531519 := bstep (se 1 (by rfl) ⟨1898639, by rfl⟩ : syracuseStep 2531519 = 3797279) B3797279
theorem B2439620329 : Blo 1124630 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B3171069263 : Blo 1124630 3171069263 := bstep (se 1 (by rfl) ⟨2378301947, by rfl⟩ : syracuseStep 3171069263 = 4756603895) B4756603895
theorem B3294695 : Blo 1124630 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B2708201 : Blo 1124630 2708201 := bstep (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) B2031151
theorem B8680031 : Blo 1124630 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B9141929 : Blo 1124630 9141929 := bstep (se 2 (by rfl) ⟨3428223, by rfl⟩ : syracuseStep 9141929 = 6856447) B6856447
theorem B2196463 : Blo 1124630 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B7221869 : Blo 1124630 7221869 := bstep (se 3 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 7221869 = 2708201) B2708201
theorem B3252827105 : Blo 1124630 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B1687679 : Blo 1124630 1687679 := bstep (se 1 (by rfl) ⟨1265759, by rfl⟩ : syracuseStep 1687679 = 2531519) B2531519
theorem B2114046175 : Blo 1124630 2114046175 := bstep (se 1 (by rfl) ⟨1585534631, by rfl⟩ : syracuseStep 2114046175 = 3171069263) B3171069263
theorem B5786687 : Blo 1124630 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B6094619 : Blo 1124630 6094619 := bstep (se 1 (by rfl) ⟨4570964, by rfl⟩ : syracuseStep 6094619 = 9141929) B9141929
theorem B1125119 : Blo 1124630 1125119 := bstep (se 1 (by rfl) ⟨843839, by rfl⟩ : syracuseStep 1125119 = 1687679) B1687679
theorem B2928617 : Blo 1124630 2928617 := bstep (se 2 (by rfl) ⟨1098231, by rfl⟩ : syracuseStep 2928617 = 2196463) B2196463
theorem B2818728233 : Blo 1124630 2818728233 := bstep (se 2 (by rfl) ⟨1057023087, by rfl⟩ : syracuseStep 2818728233 = 2114046175) B2114046175
theorem B15431165 : Blo 1124630 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B4814579 : Blo 1124630 4814579 := bstep (se 1 (by rfl) ⟨3610934, by rfl⟩ : syracuseStep 4814579 = 7221869) B7221869
theorem B2168551403 : Blo 1124630 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B4063079 : Blo 1124630 4063079 := bstep (se 1 (by rfl) ⟨3047309, by rfl⟩ : syracuseStep 4063079 = 6094619) B6094619
theorem B1879152155 : Blo 1124630 1879152155 := bstep (se 1 (by rfl) ⟨1409364116, by rfl⟩ : syracuseStep 1879152155 = 2818728233) B2818728233
theorem B1445700935 : Blo 1124630 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B1952411 : Blo 1124630 1952411 := bstep (se 1 (by rfl) ⟨1464308, by rfl⟩ : syracuseStep 1952411 = 2928617) B2928617
theorem B10834877 : Blo 1124630 10834877 := bstep (se 3 (by rfl) ⟨2031539, by rfl⟩ : syracuseStep 10834877 = 4063079) B4063079
theorem B10287443 : Blo 1124630 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B3209719 : Blo 1124630 3209719 := bstep (se 1 (by rfl) ⟨2407289, by rfl⟩ : syracuseStep 3209719 = 4814579) B4814579
theorem B27433181 : Blo 1124630 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B7223251 : Blo 1124630 7223251 := bstep (se 1 (by rfl) ⟨5417438, by rfl⟩ : syracuseStep 7223251 = 10834877) B10834877
theorem B1252768103 : Blo 1124630 1252768103 := bstep (se 1 (by rfl) ⟨939576077, by rfl⟩ : syracuseStep 1252768103 = 1879152155) B1879152155
theorem B4279625 : Blo 1124630 4279625 := bstep (se 2 (by rfl) ⟨1604859, by rfl⟩ : syracuseStep 4279625 = 3209719) B3209719
theorem B963800623 : Blo 1124630 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B5206429 : Blo 1124630 5206429 := bstep (se 3 (by rfl) ⟨976205, by rfl⟩ : syracuseStep 5206429 = 1952411) B1952411
theorem B2853083 : Blo 1124630 2853083 := bstep (se 1 (by rfl) ⟨2139812, by rfl⟩ : syracuseStep 2853083 = 4279625) B4279625
theorem B73155149 : Blo 1124630 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B5140269989 : Blo 1124630 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B835178735 : Blo 1124630 835178735 := bstep (se 1 (by rfl) ⟨626384051, by rfl⟩ : syracuseStep 835178735 = 1252768103) B1252768103
theorem B6941905 : Blo 1124630 6941905 := bstep (se 2 (by rfl) ⟨2603214, by rfl⟩ : syracuseStep 6941905 = 5206429) B5206429
theorem B9631001 : Blo 1124630 9631001 := bstep (se 2 (by rfl) ⟨3611625, by rfl⟩ : syracuseStep 9631001 = 7223251) B7223251
theorem B1902055 : Blo 1124630 1902055 := bstep (se 1 (by rfl) ⟨1426541, by rfl⟩ : syracuseStep 1902055 = 2853083) B2853083
theorem B3426846659 : Blo 1124630 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B48770099 : Blo 1124630 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B556785823 : Blo 1124630 556785823 := bstep (se 1 (by rfl) ⟨417589367, by rfl⟩ : syracuseStep 556785823 = 835178735) B835178735
theorem B37023493 : Blo 1124630 37023493 := bstep (se 4 (by rfl) ⟨3470952, by rfl⟩ : syracuseStep 37023493 = 6941905) B6941905
theorem B6420667 : Blo 1124630 6420667 := bstep (se 1 (by rfl) ⟨4815500, by rfl⟩ : syracuseStep 6420667 = 9631001) B9631001
theorem B32513399 : Blo 1124630 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B8560889 : Blo 1124630 8560889 := bstep (se 2 (by rfl) ⟨3210333, by rfl⟩ : syracuseStep 8560889 = 6420667) B6420667
theorem B2284564439 : Blo 1124630 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B2536073 : Blo 1124630 2536073 := bstep (se 2 (by rfl) ⟨951027, by rfl⟩ : syracuseStep 2536073 = 1902055) B1902055
theorem B49364657 : Blo 1124630 49364657 := bstep (se 2 (by rfl) ⟨18511746, by rfl⟩ : syracuseStep 49364657 = 37023493) B37023493
theorem B742381097 : Blo 1124630 742381097 := bstep (se 2 (by rfl) ⟨278392911, by rfl⟩ : syracuseStep 742381097 = 556785823) B556785823
theorem B1979682925 : Blo 1124630 1979682925 := bstep (se 3 (by rfl) ⟨371190548, by rfl⟩ : syracuseStep 1979682925 = 742381097) B742381097
theorem B5707259 : Blo 1124630 5707259 := bstep (se 1 (by rfl) ⟨4280444, by rfl⟩ : syracuseStep 5707259 = 8560889) B8560889
theorem B32909771 : Blo 1124630 32909771 := bstep (se 1 (by rfl) ⟨24682328, by rfl⟩ : syracuseStep 32909771 = 49364657) B49364657
theorem B21675599 : Blo 1124630 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B1523042959 : Blo 1124630 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B1690715 : Blo 1124630 1690715 := bstep (se 1 (by rfl) ⟨1268036, by rfl⟩ : syracuseStep 1690715 = 2536073) B2536073
theorem B3804839 : Blo 1124630 3804839 := bstep (se 1 (by rfl) ⟨2853629, by rfl⟩ : syracuseStep 3804839 = 5707259) B5707259
theorem B87759389 : Blo 1124630 87759389 := bstep (se 3 (by rfl) ⟨16454885, by rfl⟩ : syracuseStep 87759389 = 32909771) B32909771
theorem B1127143 : Blo 1124630 1127143 := bstep (se 1 (by rfl) ⟨845357, by rfl⟩ : syracuseStep 1127143 = 1690715) B1690715
theorem B2639577233 : Blo 1124630 2639577233 := bstep (se 2 (by rfl) ⟨989841462, by rfl⟩ : syracuseStep 2639577233 = 1979682925) B1979682925
theorem B2030723945 : Blo 1124630 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B14450399 : Blo 1124630 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B1353815963 : Blo 1124630 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B7038872621 : Blo 1124630 7038872621 := bstep (se 3 (by rfl) ⟨1319788616, by rfl⟩ : syracuseStep 7038872621 = 2639577233) B2639577233
theorem B2536559 : Blo 1124630 2536559 := bstep (se 1 (by rfl) ⟨1902419, by rfl⟩ : syracuseStep 2536559 = 3804839) B3804839
theorem B58506259 : Blo 1124630 58506259 := bstep (se 1 (by rfl) ⟨43879694, by rfl⟩ : syracuseStep 58506259 = 87759389) B87759389
theorem B9633599 : Blo 1124630 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B4692581747 : Blo 1124630 4692581747 := bstep (se 1 (by rfl) ⟨3519436310, by rfl⟩ : syracuseStep 4692581747 = 7038872621) B7038872621
theorem B902543975 : Blo 1124630 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B1691039 : Blo 1124630 1691039 := bstep (se 1 (by rfl) ⟨1268279, by rfl⟩ : syracuseStep 1691039 = 2536559) B2536559
theorem B78008345 : Blo 1124630 78008345 := bstep (se 2 (by rfl) ⟨29253129, by rfl⟩ : syracuseStep 78008345 = 58506259) B58506259
theorem B6422399 : Blo 1124630 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B52005563 : Blo 1124630 52005563 := bstep (se 1 (by rfl) ⟨39004172, by rfl⟩ : syracuseStep 52005563 = 78008345) B78008345
theorem B601695983 : Blo 1124630 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B1127359 : Blo 1124630 1127359 := bstep (se 1 (by rfl) ⟨845519, by rfl⟩ : syracuseStep 1127359 = 1691039) B1691039
theorem B4281599 : Blo 1124630 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B3128387831 : Blo 1124630 3128387831 := bstep (se 1 (by rfl) ⟨2346290873, by rfl⟩ : syracuseStep 3128387831 = 4692581747) B4692581747
theorem B34670375 : Blo 1124630 34670375 := bstep (se 1 (by rfl) ⟨26002781, by rfl⟩ : syracuseStep 34670375 = 52005563) B52005563
theorem B2854399 : Blo 1124630 2854399 := bstep (se 1 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 2854399 = 4281599) B4281599
theorem B1604522621 : Blo 1124630 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B2085591887 : Blo 1124630 2085591887 := bstep (se 1 (by rfl) ⟨1564193915, by rfl⟩ : syracuseStep 2085591887 = 3128387831) B3128387831
theorem B3805865 : Blo 1124630 3805865 := bstep (se 2 (by rfl) ⟨1427199, by rfl⟩ : syracuseStep 3805865 = 2854399) B2854399
theorem B23113583 : Blo 1124630 23113583 := bstep (se 1 (by rfl) ⟨17335187, by rfl⟩ : syracuseStep 23113583 = 34670375) B34670375
theorem B4278726989 : Blo 1124630 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B1390394591 : Blo 1124630 1390394591 := bstep (se 1 (by rfl) ⟨1042795943, by rfl⟩ : syracuseStep 1390394591 = 2085591887) B2085591887
theorem B15409055 : Blo 1124630 15409055 := bstep (se 1 (by rfl) ⟨11556791, by rfl⟩ : syracuseStep 15409055 = 23113583) B23113583
theorem B2537243 : Blo 1124630 2537243 := bstep (se 1 (by rfl) ⟨1902932, by rfl⟩ : syracuseStep 2537243 = 3805865) B3805865
theorem B926929727 : Blo 1124630 926929727 := bstep (se 1 (by rfl) ⟨695197295, by rfl⟩ : syracuseStep 926929727 = 1390394591) B1390394591
theorem B2852484659 : Blo 1124630 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B617953151 : Blo 1124630 617953151 := bstep (se 1 (by rfl) ⟨463464863, by rfl⟩ : syracuseStep 617953151 = 926929727) B926929727
theorem B10272703 : Blo 1124630 10272703 := bstep (se 1 (by rfl) ⟨7704527, by rfl⟩ : syracuseStep 10272703 = 15409055) B15409055
theorem B1691495 : Blo 1124630 1691495 := bstep (se 1 (by rfl) ⟨1268621, by rfl⟩ : syracuseStep 1691495 = 2537243) B2537243
theorem B1901656439 : Blo 1124630 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B411968767 : Blo 1124630 411968767 := bstep (se 1 (by rfl) ⟨308976575, by rfl⟩ : syracuseStep 411968767 = 617953151) B617953151
theorem B1267770959 : Blo 1124630 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B1127663 : Blo 1124630 1127663 := bstep (se 1 (by rfl) ⟨845747, by rfl⟩ : syracuseStep 1127663 = 1691495) B1691495
theorem B13696937 : Blo 1124630 13696937 := bstep (se 2 (by rfl) ⟨5136351, by rfl⟩ : syracuseStep 13696937 = 10272703) B10272703
theorem B549291689 : Blo 1124630 549291689 := bstep (se 2 (by rfl) ⟨205984383, by rfl⟩ : syracuseStep 549291689 = 411968767) B411968767
theorem B9131291 : Blo 1124630 9131291 := bstep (se 1 (by rfl) ⟨6848468, by rfl⟩ : syracuseStep 9131291 = 13696937) B13696937
theorem B845180639 : Blo 1124630 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B563453759 : Blo 1124630 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B366194459 : Blo 1124630 366194459 := bstep (se 1 (by rfl) ⟨274645844, by rfl⟩ : syracuseStep 366194459 = 549291689) B549291689
theorem B6087527 : Blo 1124630 6087527 := bstep (se 1 (by rfl) ⟨4565645, by rfl⟩ : syracuseStep 6087527 = 9131291) B9131291
theorem B244129639 : Blo 1124630 244129639 := bstep (se 1 (by rfl) ⟨183097229, by rfl⟩ : syracuseStep 244129639 = 366194459) B366194459
theorem B4058351 : Blo 1124630 4058351 := bstep (se 1 (by rfl) ⟨3043763, by rfl⟩ : syracuseStep 4058351 = 6087527) B6087527
theorem B1502543357 : Blo 1124630 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 1124630 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B2705567 : Blo 1124630 2705567 := bstep (se 1 (by rfl) ⟨2029175, by rfl⟩ : syracuseStep 2705567 = 4058351) B4058351
theorem B325506185 : Blo 1124630 325506185 := bstep (se 2 (by rfl) ⟨122064819, by rfl⟩ : syracuseStep 325506185 = 244129639) B244129639
theorem B7214845 : Blo 1124630 7214845 := bstep (se 3 (by rfl) ⟨1352783, by rfl⟩ : syracuseStep 7214845 = 2705567) B2705567
theorem B217004123 : Blo 1124630 217004123 := bstep (se 1 (by rfl) ⟨162753092, by rfl⟩ : syracuseStep 217004123 = 325506185) B325506185
theorem B667797047 : Blo 1124630 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B445198031 : Blo 1124630 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B9619793 : Blo 1124630 9619793 := bstep (se 2 (by rfl) ⟨3607422, by rfl⟩ : syracuseStep 9619793 = 7214845) B7214845
theorem B144669415 : Blo 1124630 144669415 := bstep (se 1 (by rfl) ⟨108502061, by rfl⟩ : syracuseStep 144669415 = 217004123) B217004123
theorem B296798687 : Blo 1124630 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B192892553 : Blo 1124630 192892553 := bstep (se 2 (by rfl) ⟨72334707, by rfl⟩ : syracuseStep 192892553 = 144669415) B144669415
theorem B6413195 : Blo 1124630 6413195 := bstep (se 1 (by rfl) ⟨4809896, by rfl⟩ : syracuseStep 6413195 = 9619793) B9619793
theorem B197865791 : Blo 1124630 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B128595035 : Blo 1124630 128595035 := bstep (se 1 (by rfl) ⟨96446276, by rfl⟩ : syracuseStep 128595035 = 192892553) B192892553
theorem B4275463 : Blo 1124630 4275463 := bstep (se 1 (by rfl) ⟨3206597, by rfl⟩ : syracuseStep 4275463 = 6413195) B6413195
theorem B85730023 : Blo 1124630 85730023 := bstep (se 1 (by rfl) ⟨64297517, by rfl⟩ : syracuseStep 85730023 = 128595035) B128595035
theorem B131910527 : Blo 1124630 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B5700617 : Blo 1124630 5700617 := bstep (se 2 (by rfl) ⟨2137731, by rfl⟩ : syracuseStep 5700617 = 4275463) B4275463
theorem B114306697 : Blo 1124630 114306697 := bstep (se 2 (by rfl) ⟨42865011, by rfl⟩ : syracuseStep 114306697 = 85730023) B85730023
theorem B87940351 : Blo 1124630 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B3800411 : Blo 1124630 3800411 := bstep (se 1 (by rfl) ⟨2850308, by rfl⟩ : syracuseStep 3800411 = 5700617) B5700617
theorem B117253801 : Blo 1124630 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B2533607 : Blo 1124630 2533607 := bstep (se 1 (by rfl) ⟨1900205, by rfl⟩ : syracuseStep 2533607 = 3800411) B3800411
theorem B609635717 : Blo 1124630 609635717 := bstep (se 4 (by rfl) ⟨57153348, by rfl⟩ : syracuseStep 609635717 = 114306697) B114306697
theorem B406423811 : Blo 1124630 406423811 := bstep (se 1 (by rfl) ⟨304817858, by rfl⟩ : syracuseStep 406423811 = 609635717) B609635717
theorem B625353605 : Blo 1124630 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B1689071 : Blo 1124630 1689071 := bstep (se 1 (by rfl) ⟨1266803, by rfl⟩ : syracuseStep 1689071 = 2533607) B2533607
theorem B1126047 : Blo 1124630 1126047 := bstep (se 1 (by rfl) ⟨844535, by rfl⟩ : syracuseStep 1126047 = 1689071) B1689071
theorem B270949207 : Blo 1124630 270949207 := bstep (se 1 (by rfl) ⟨203211905, by rfl⟩ : syracuseStep 270949207 = 406423811) B406423811
theorem B416902403 : Blo 1124630 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 1124630 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B361265609 : Blo 1124630 361265609 := bstep (se 2 (by rfl) ⟨135474603, by rfl⟩ : syracuseStep 361265609 = 270949207) B270949207
theorem B741159827 : Blo 1124630 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B963374957 : Blo 1124630 963374957 := bstep (se 3 (by rfl) ⟨180632804, by rfl⟩ : syracuseStep 963374957 = 361265609) B361265609
theorem B642249971 : Blo 1124630 642249971 := bstep (se 1 (by rfl) ⟨481687478, by rfl⟩ : syracuseStep 642249971 = 963374957) B963374957
theorem B494106551 : Blo 1124630 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B428166647 : Blo 1124630 428166647 := bstep (se 1 (by rfl) ⟨321124985, by rfl⟩ : syracuseStep 428166647 = 642249971) B642249971
theorem B329404367 : Blo 1124630 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B285444431 : Blo 1124630 285444431 := bstep (se 1 (by rfl) ⟨214083323, by rfl⟩ : syracuseStep 285444431 = 428166647) B428166647
theorem B219602911 : Blo 1124630 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B190296287 : Blo 1124630 190296287 := bstep (se 1 (by rfl) ⟨142722215, by rfl⟩ : syracuseStep 190296287 = 285444431) B285444431
theorem B292803881 : Blo 1124630 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 1124630 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B126864191 : Blo 1124630 126864191 := bstep (se 1 (by rfl) ⟨95148143, by rfl⟩ : syracuseStep 126864191 = 190296287) B190296287
theorem B338304509 : Blo 1124630 338304509 := bstep (se 3 (by rfl) ⟨63432095, by rfl⟩ : syracuseStep 338304509 = 126864191) B126864191
theorem B1041080465 : Blo 1124630 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B225536339 : Blo 1124630 225536339 := bstep (se 1 (by rfl) ⟨169152254, by rfl⟩ : syracuseStep 225536339 = 338304509) B338304509
theorem B694053643 : Blo 1124630 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 1124630 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B150357559 : Blo 1124630 150357559 := bstep (se 1 (by rfl) ⟨112768169, by rfl⟩ : syracuseStep 150357559 = 225536339) B225536339
theorem B200476745 : Blo 1124630 200476745 := bstep (se 2 (by rfl) ⟨75178779, by rfl⟩ : syracuseStep 200476745 = 150357559) B150357559
theorem B616936571 : Blo 1124630 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 1124630 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B133651163 : Blo 1124630 133651163 := bstep (se 1 (by rfl) ⟨100238372, by rfl⟩ : syracuseStep 133651163 = 200476745) B200476745
theorem B89100775 : Blo 1124630 89100775 := bstep (se 1 (by rfl) ⟨66825581, by rfl⟩ : syracuseStep 89100775 = 133651163) B133651163
theorem B1096776125 : Blo 1124630 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B475204133 : Blo 1124630 475204133 := bstep (se 4 (by rfl) ⟨44550387, by rfl⟩ : syracuseStep 475204133 = 89100775) B89100775
theorem B731184083 : Blo 1124630 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B316802755 : Blo 1124630 316802755 := bstep (se 1 (by rfl) ⟨237602066, by rfl⟩ : syracuseStep 316802755 = 475204133) B475204133
theorem B487456055 : Blo 1124630 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 1124630 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B422403673 : Blo 1124630 422403673 := bstep (se 2 (by rfl) ⟨158401377, by rfl⟩ : syracuseStep 422403673 = 316802755) B316802755
theorem B216647135 : Blo 1124630 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B563204897 : Blo 1124630 563204897 := bstep (se 2 (by rfl) ⟨211201836, by rfl⟩ : syracuseStep 563204897 = 422403673) B422403673
theorem B375469931 : Blo 1124630 375469931 := bstep (se 1 (by rfl) ⟨281602448, by rfl⟩ : syracuseStep 375469931 = 563204897) B563204897
theorem B144431423 : Blo 1124630 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 1124630 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B250313287 : Blo 1124630 250313287 := bstep (se 1 (by rfl) ⟨187734965, by rfl⟩ : syracuseStep 250313287 = 375469931) B375469931
theorem B333751049 : Blo 1124630 333751049 := bstep (se 2 (by rfl) ⟨125156643, by rfl⟩ : syracuseStep 333751049 = 250313287) B250313287
theorem B64191743 : Blo 1124630 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B222500699 : Blo 1124630 222500699 := bstep (se 1 (by rfl) ⟨166875524, by rfl⟩ : syracuseStep 222500699 = 333751049) B333751049
theorem B42794495 : Blo 1124630 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 1124630 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B148333799 : Blo 1124630 148333799 := bstep (se 1 (by rfl) ⟨111250349, by rfl⟩ : syracuseStep 148333799 = 222500699) B222500699
theorem B395556797 : Blo 1124630 395556797 := bstep (se 3 (by rfl) ⟨74166899, by rfl⟩ : syracuseStep 395556797 = 148333799) B148333799
theorem B76079101 : Blo 1124630 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B263704531 : Blo 1124630 263704531 := bstep (se 1 (by rfl) ⟨197778398, by rfl⟩ : syracuseStep 263704531 = 395556797) B395556797
theorem B101438801 : Blo 1124630 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B351606041 : Blo 1124630 351606041 := bstep (se 2 (by rfl) ⟨131852265, by rfl⟩ : syracuseStep 351606041 = 263704531) B263704531
theorem B67625867 : Blo 1124630 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B180335645 : Blo 1124630 180335645 := bstep (se 3 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 180335645 = 67625867) B67625867
theorem B234404027 : Blo 1124630 234404027 := bstep (se 1 (by rfl) ⟨175803020, by rfl⟩ : syracuseStep 234404027 = 351606041) B351606041
theorem B120223763 : Blo 1124630 120223763 := bstep (se 1 (by rfl) ⟨90167822, by rfl⟩ : syracuseStep 120223763 = 180335645) B180335645
theorem B156269351 : Blo 1124630 156269351 := bstep (se 1 (by rfl) ⟨117202013, by rfl⟩ : syracuseStep 156269351 = 234404027) B234404027
theorem B104179567 : Blo 1124630 104179567 := bstep (se 1 (by rfl) ⟨78134675, by rfl⟩ : syracuseStep 104179567 = 156269351) B156269351
theorem B80149175 : Blo 1124630 80149175 := bstep (se 1 (by rfl) ⟨60111881, by rfl⟩ : syracuseStep 80149175 = 120223763) B120223763
theorem B138906089 : Blo 1124630 138906089 := bstep (se 2 (by rfl) ⟨52089783, by rfl⟩ : syracuseStep 138906089 = 104179567) B104179567
theorem B53432783 : Blo 1124630 53432783 := bstep (se 1 (by rfl) ⟨40074587, by rfl⟩ : syracuseStep 53432783 = 80149175) B80149175
theorem B92604059 : Blo 1124630 92604059 := bstep (se 1 (by rfl) ⟨69453044, by rfl⟩ : syracuseStep 92604059 = 138906089) B138906089
theorem B35621855 : Blo 1124630 35621855 := bstep (se 1 (by rfl) ⟨26716391, by rfl⟩ : syracuseStep 35621855 = 53432783) B53432783
theorem B61736039 : Blo 1124630 61736039 := bstep (se 1 (by rfl) ⟨46302029, by rfl⟩ : syracuseStep 61736039 = 92604059) B92604059
theorem B23747903 : Blo 1124630 23747903 := bstep (se 1 (by rfl) ⟨17810927, by rfl⟩ : syracuseStep 23747903 = 35621855) B35621855
theorem B41157359 : Blo 1124630 41157359 := bstep (se 1 (by rfl) ⟨30868019, by rfl⟩ : syracuseStep 41157359 = 61736039) B61736039
theorem B15831935 : Blo 1124630 15831935 := bstep (se 1 (by rfl) ⟨11873951, by rfl⟩ : syracuseStep 15831935 = 23747903) B23747903
theorem B10554623 : Blo 1124630 10554623 := bstep (se 1 (by rfl) ⟨7915967, by rfl⟩ : syracuseStep 10554623 = 15831935) B15831935
theorem B27438239 : Blo 1124630 27438239 := bstep (se 1 (by rfl) ⟨20578679, by rfl⟩ : syracuseStep 27438239 = 41157359) B41157359
theorem B18292159 : Blo 1124630 18292159 := bstep (se 1 (by rfl) ⟨13719119, by rfl⟩ : syracuseStep 18292159 = 27438239) B27438239
theorem B7036415 : Blo 1124630 7036415 := bstep (se 1 (by rfl) ⟨5277311, by rfl⟩ : syracuseStep 7036415 = 10554623) B10554623
theorem B4690943 : Blo 1124630 4690943 := bstep (se 1 (by rfl) ⟨3518207, by rfl⟩ : syracuseStep 4690943 = 7036415) B7036415
theorem B24389545 : Blo 1124630 24389545 := bstep (se 2 (by rfl) ⟨9146079, by rfl⟩ : syracuseStep 24389545 = 18292159) B18292159
theorem B32519393 : Blo 1124630 32519393 := bstep (se 2 (by rfl) ⟨12194772, by rfl⟩ : syracuseStep 32519393 = 24389545) B24389545
theorem B3127295 : Blo 1124630 3127295 := bstep (se 1 (by rfl) ⟨2345471, by rfl⟩ : syracuseStep 3127295 = 4690943) B4690943
theorem B8339453 : Blo 1124630 8339453 := bstep (se 3 (by rfl) ⟨1563647, by rfl⟩ : syracuseStep 8339453 = 3127295) B3127295
theorem B21679595 : Blo 1124630 21679595 := bstep (se 1 (by rfl) ⟨16259696, by rfl⟩ : syracuseStep 21679595 = 32519393) B32519393
theorem B14453063 : Blo 1124630 14453063 := bstep (se 1 (by rfl) ⟨10839797, by rfl⟩ : syracuseStep 14453063 = 21679595) B21679595
theorem B5559635 : Blo 1124630 5559635 := bstep (se 1 (by rfl) ⟨4169726, by rfl⟩ : syracuseStep 5559635 = 8339453) B8339453
theorem B9635375 : Blo 1124630 9635375 := bstep (se 1 (by rfl) ⟨7226531, by rfl⟩ : syracuseStep 9635375 = 14453063) B14453063
theorem B14825693 : Blo 1124630 14825693 := bstep (se 3 (by rfl) ⟨2779817, by rfl⟩ : syracuseStep 14825693 = 5559635) B5559635
theorem B6423583 : Blo 1124630 6423583 := bstep (se 1 (by rfl) ⟨4817687, by rfl⟩ : syracuseStep 6423583 = 9635375) B9635375
theorem B39535181 : Blo 1124630 39535181 := bstep (se 3 (by rfl) ⟨7412846, by rfl⟩ : syracuseStep 39535181 = 14825693) B14825693
theorem B26356787 : Blo 1124630 26356787 := bstep (se 1 (by rfl) ⟨19767590, by rfl⟩ : syracuseStep 26356787 = 39535181) B39535181
theorem B8564777 : Blo 1124630 8564777 := bstep (se 2 (by rfl) ⟨3211791, by rfl⟩ : syracuseStep 8564777 = 6423583) B6423583
theorem B17571191 : Blo 1124630 17571191 := bstep (se 1 (by rfl) ⟨13178393, by rfl⟩ : syracuseStep 17571191 = 26356787) B26356787
theorem B5709851 : Blo 1124630 5709851 := bstep (se 1 (by rfl) ⟨4282388, by rfl⟩ : syracuseStep 5709851 = 8564777) B8564777
theorem B3806567 : Blo 1124630 3806567 := bstep (se 1 (by rfl) ⟨2854925, by rfl⟩ : syracuseStep 3806567 = 5709851) B5709851
theorem B187426037 : Blo 1124630 187426037 := bstep (se 5 (by rfl) ⟨8785595, by rfl⟩ : syracuseStep 187426037 = 17571191) B17571191
theorem B124950691 : Blo 1124630 124950691 := bstep (se 1 (by rfl) ⟨93713018, by rfl⟩ : syracuseStep 124950691 = 187426037) B187426037
theorem B2537711 : Blo 1124630 2537711 := bstep (se 1 (by rfl) ⟨1903283, by rfl⟩ : syracuseStep 2537711 = 3806567) B3806567
theorem B166600921 : Blo 1124630 166600921 := bstep (se 2 (by rfl) ⟨62475345, by rfl⟩ : syracuseStep 166600921 = 124950691) B124950691
theorem B1691807 : Blo 1124630 1691807 := bstep (se 1 (by rfl) ⟨1268855, by rfl⟩ : syracuseStep 1691807 = 2537711) B2537711
theorem B222134561 : Blo 1124630 222134561 := bstep (se 2 (by rfl) ⟨83300460, by rfl⟩ : syracuseStep 222134561 = 166600921) B166600921
theorem B1127871 : Blo 1124630 1127871 := bstep (se 1 (by rfl) ⟨845903, by rfl⟩ : syracuseStep 1127871 = 1691807) B1691807
theorem B148089707 : Blo 1124630 148089707 := bstep (se 1 (by rfl) ⟨111067280, by rfl⟩ : syracuseStep 148089707 = 222134561) B222134561
theorem B98726471 : Blo 1124630 98726471 := bstep (se 1 (by rfl) ⟨74044853, by rfl⟩ : syracuseStep 98726471 = 148089707) B148089707
theorem B65817647 : Blo 1124630 65817647 := bstep (se 1 (by rfl) ⟨49363235, by rfl⟩ : syracuseStep 65817647 = 98726471) B98726471
theorem B43878431 : Blo 1124630 43878431 := bstep (se 1 (by rfl) ⟨32908823, by rfl⟩ : syracuseStep 43878431 = 65817647) B65817647
theorem B29252287 : Blo 1124630 29252287 := bstep (se 1 (by rfl) ⟨21939215, by rfl⟩ : syracuseStep 29252287 = 43878431) B43878431
theorem B39003049 : Blo 1124630 39003049 := bstep (se 2 (by rfl) ⟨14626143, by rfl⟩ : syracuseStep 39003049 = 29252287) B29252287
theorem B52004065 : Blo 1124630 52004065 := bstep (se 2 (by rfl) ⟨19501524, by rfl⟩ : syracuseStep 52004065 = 39003049) B39003049
theorem B69338753 : Blo 1124630 69338753 := bstep (se 2 (by rfl) ⟨26002032, by rfl⟩ : syracuseStep 69338753 = 52004065) B52004065
theorem B46225835 : Blo 1124630 46225835 := bstep (se 1 (by rfl) ⟨34669376, by rfl⟩ : syracuseStep 46225835 = 69338753) B69338753
theorem B30817223 : Blo 1124630 30817223 := bstep (se 1 (by rfl) ⟨23112917, by rfl⟩ : syracuseStep 30817223 = 46225835) B46225835
theorem B20544815 : Blo 1124630 20544815 := bstep (se 1 (by rfl) ⟨15408611, by rfl⟩ : syracuseStep 20544815 = 30817223) B30817223
theorem B13696543 : Blo 1124630 13696543 := bstep (se 1 (by rfl) ⟨10272407, by rfl⟩ : syracuseStep 13696543 = 20544815) B20544815
theorem B73048229 : Blo 1124630 73048229 := bstep (se 4 (by rfl) ⟨6848271, by rfl⟩ : syracuseStep 73048229 = 13696543) B13696543
theorem B48698819 : Blo 1124630 48698819 := bstep (se 1 (by rfl) ⟨36524114, by rfl⟩ : syracuseStep 48698819 = 73048229) B73048229
theorem B32465879 : Blo 1124630 32465879 := bstep (se 1 (by rfl) ⟨24349409, by rfl⟩ : syracuseStep 32465879 = 48698819) B48698819
theorem B21643919 : Blo 1124630 21643919 := bstep (se 1 (by rfl) ⟨16232939, by rfl⟩ : syracuseStep 21643919 = 32465879) B32465879
theorem B14429279 : Blo 1124630 14429279 := bstep (se 1 (by rfl) ⟨10821959, by rfl⟩ : syracuseStep 14429279 = 21643919) B21643919
theorem B9619519 : Blo 1124630 9619519 := bstep (se 1 (by rfl) ⟨7214639, by rfl⟩ : syracuseStep 9619519 = 14429279) B14429279
theorem B12826025 : Blo 1124630 12826025 := bstep (se 2 (by rfl) ⟨4809759, by rfl⟩ : syracuseStep 12826025 = 9619519) B9619519
theorem B8550683 : Blo 1124630 8550683 := bstep (se 1 (by rfl) ⟨6413012, by rfl⟩ : syracuseStep 8550683 = 12826025) B12826025
theorem B5700455 : Blo 1124630 5700455 := bstep (se 1 (by rfl) ⟨4275341, by rfl⟩ : syracuseStep 5700455 = 8550683) B8550683
theorem B3800303 : Blo 1124630 3800303 := bstep (se 1 (by rfl) ⟨2850227, by rfl⟩ : syracuseStep 3800303 = 5700455) B5700455
theorem B2533535 : Blo 1124630 2533535 := bstep (se 1 (by rfl) ⟨1900151, by rfl⟩ : syracuseStep 2533535 = 3800303) B3800303
theorem B1689023 : Blo 1124630 1689023 := bstep (se 1 (by rfl) ⟨1266767, by rfl⟩ : syracuseStep 1689023 = 2533535) B2533535
theorem B1126015 : Blo 1124630 1126015 := bstep (se 1 (by rfl) ⟨844511, by rfl⟩ : syracuseStep 1126015 = 1689023) B1689023

theorem C0 (j : ℕ) (h1 : 281157 ≤ j) (h2 : j ≤ 281856) : Blo 1124630 (4 * j + 3) := by
  interval_cases j
  · exact B1124631
  · exact B1124635
  · exact B1124639
  · exact B1124643
  · exact B1124647
  · exact B1124651
  · exact B1124655
  · exact B1124659
  · exact B1124663
  · exact B1124667
  · exact B1124671
  · exact B1124675
  · exact B1124679
  · exact B1124683
  · exact B1124687
  · exact B1124691
  · exact B1124695
  · exact B1124699
  · exact B1124703
  · exact B1124707
  · exact B1124711
  · exact B1124715
  · exact B1124719
  · exact B1124723
  · exact B1124727
  · exact B1124731
  · exact B1124735
  · exact B1124739
  · exact B1124743
  · exact B1124747
  · exact B1124751
  · exact B1124755
  · exact B1124759
  · exact B1124763
  · exact B1124767
  · exact B1124771
  · exact B1124775
  · exact B1124779
  · exact B1124783
  · exact B1124787
  · exact B1124791
  · exact B1124795
  · exact B1124799
  · exact B1124803
  · exact B1124807
  · exact B1124811
  · exact B1124815
  · exact B1124819
  · exact B1124823
  · exact B1124827
  · exact B1124831
  · exact B1124835
  · exact B1124839
  · exact B1124843
  · exact B1124847
  · exact B1124851
  · exact B1124855
  · exact B1124859
  · exact B1124863
  · exact B1124867
  · exact B1124871
  · exact B1124875
  · exact B1124879
  · exact B1124883
  · exact B1124887
  · exact B1124891
  · exact B1124895
  · exact B1124899
  · exact B1124903
  · exact B1124907
  · exact B1124911
  · exact B1124915
  · exact B1124919
  · exact B1124923
  · exact B1124927
  · exact B1124931
  · exact B1124935
  · exact B1124939
  · exact B1124943
  · exact B1124947
  · exact B1124951
  · exact B1124955
  · exact B1124959
  · exact B1124963
  · exact B1124967
  · exact B1124971
  · exact B1124975
  · exact B1124979
  · exact B1124983
  · exact B1124987
  · exact B1124991
  · exact B1124995
  · exact B1124999
  · exact B1125003
  · exact B1125007
  · exact B1125011
  · exact B1125015
  · exact B1125019
  · exact B1125023
  · exact B1125027
  · exact B1125031
  · exact B1125035
  · exact B1125039
  · exact B1125043
  · exact B1125047
  · exact B1125051
  · exact B1125055
  · exact B1125059
  · exact B1125063
  · exact B1125067
  · exact B1125071
  · exact B1125075
  · exact B1125079
  · exact B1125083
  · exact B1125087
  · exact B1125091
  · exact B1125095
  · exact B1125099
  · exact B1125103
  · exact B1125107
  · exact B1125111
  · exact B1125115
  · exact B1125119
  · exact B1125123
  · exact B1125127
  · exact B1125131
  · exact B1125135
  · exact B1125139
  · exact B1125143
  · exact B1125147
  · exact B1125151
  · exact B1125155
  · exact B1125159
  · exact B1125163
  · exact B1125167
  · exact B1125171
  · exact B1125175
  · exact B1125179
  · exact B1125183
  · exact B1125187
  · exact B1125191
  · exact B1125195
  · exact B1125199
  · exact B1125203
  · exact B1125207
  · exact B1125211
  · exact B1125215
  · exact B1125219
  · exact B1125223
  · exact B1125227
  · exact B1125231
  · exact B1125235
  · exact B1125239
  · exact B1125243
  · exact B1125247
  · exact B1125251
  · exact B1125255
  · exact B1125259
  · exact B1125263
  · exact B1125267
  · exact B1125271
  · exact B1125275
  · exact B1125279
  · exact B1125283
  · exact B1125287
  · exact B1125291
  · exact B1125295
  · exact B1125299
  · exact B1125303
  · exact B1125307
  · exact B1125311
  · exact B1125315
  · exact B1125319
  · exact B1125323
  · exact B1125327
  · exact B1125331
  · exact B1125335
  · exact B1125339
  · exact B1125343
  · exact B1125347
  · exact B1125351
  · exact B1125355
  · exact B1125359
  · exact B1125363
  · exact B1125367
  · exact B1125371
  · exact B1125375
  · exact B1125379
  · exact B1125383
  · exact B1125387
  · exact B1125391
  · exact B1125395
  · exact B1125399
  · exact B1125403
  · exact B1125407
  · exact B1125411
  · exact B1125415
  · exact B1125419
  · exact B1125423
  · exact B1125427
  · exact B1125431
  · exact B1125435
  · exact B1125439
  · exact B1125443
  · exact B1125447
  · exact B1125451
  · exact B1125455
  · exact B1125459
  · exact B1125463
  · exact B1125467
  · exact B1125471
  · exact B1125475
  · exact B1125479
  · exact B1125483
  · exact B1125487
  · exact B1125491
  · exact B1125495
  · exact B1125499
  · exact B1125503
  · exact B1125507
  · exact B1125511
  · exact B1125515
  · exact B1125519
  · exact B1125523
  · exact B1125527
  · exact B1125531
  · exact B1125535
  · exact B1125539
  · exact B1125543
  · exact B1125547
  · exact B1125551
  · exact B1125555
  · exact B1125559
  · exact B1125563
  · exact B1125567
  · exact B1125571
  · exact B1125575
  · exact B1125579
  · exact B1125583
  · exact B1125587
  · exact B1125591
  · exact B1125595
  · exact B1125599
  · exact B1125603
  · exact B1125607
  · exact B1125611
  · exact B1125615
  · exact B1125619
  · exact B1125623
  · exact B1125627
  · exact B1125631
  · exact B1125635
  · exact B1125639
  · exact B1125643
  · exact B1125647
  · exact B1125651
  · exact B1125655
  · exact B1125659
  · exact B1125663
  · exact B1125667
  · exact B1125671
  · exact B1125675
  · exact B1125679
  · exact B1125683
  · exact B1125687
  · exact B1125691
  · exact B1125695
  · exact B1125699
  · exact B1125703
  · exact B1125707
  · exact B1125711
  · exact B1125715
  · exact B1125719
  · exact B1125723
  · exact B1125727
  · exact B1125731
  · exact B1125735
  · exact B1125739
  · exact B1125743
  · exact B1125747
  · exact B1125751
  · exact B1125755
  · exact B1125759
  · exact B1125763
  · exact B1125767
  · exact B1125771
  · exact B1125775
  · exact B1125779
  · exact B1125783
  · exact B1125787
  · exact B1125791
  · exact B1125795
  · exact B1125799
  · exact B1125803
  · exact B1125807
  · exact B1125811
  · exact B1125815
  · exact B1125819
  · exact B1125823
  · exact B1125827
  · exact B1125831
  · exact B1125835
  · exact B1125839
  · exact B1125843
  · exact B1125847
  · exact B1125851
  · exact B1125855
  · exact B1125859
  · exact B1125863
  · exact B1125867
  · exact B1125871
  · exact B1125875
  · exact B1125879
  · exact B1125883
  · exact B1125887
  · exact B1125891
  · exact B1125895
  · exact B1125899
  · exact B1125903
  · exact B1125907
  · exact B1125911
  · exact B1125915
  · exact B1125919
  · exact B1125923
  · exact B1125927
  · exact B1125931
  · exact B1125935
  · exact B1125939
  · exact B1125943
  · exact B1125947
  · exact B1125951
  · exact B1125955
  · exact B1125959
  · exact B1125963
  · exact B1125967
  · exact B1125971
  · exact B1125975
  · exact B1125979
  · exact B1125983
  · exact B1125987
  · exact B1125991
  · exact B1125995
  · exact B1125999
  · exact B1126003
  · exact B1126007
  · exact B1126011
  · exact B1126015
  · exact B1126019
  · exact B1126023
  · exact B1126027
  · exact B1126031
  · exact B1126035
  · exact B1126039
  · exact B1126043
  · exact B1126047
  · exact B1126051
  · exact B1126055
  · exact B1126059
  · exact B1126063
  · exact B1126067
  · exact B1126071
  · exact B1126075
  · exact B1126079
  · exact B1126083
  · exact B1126087
  · exact B1126091
  · exact B1126095
  · exact B1126099
  · exact B1126103
  · exact B1126107
  · exact B1126111
  · exact B1126115
  · exact B1126119
  · exact B1126123
  · exact B1126127
  · exact B1126131
  · exact B1126135
  · exact B1126139
  · exact B1126143
  · exact B1126147
  · exact B1126151
  · exact B1126155
  · exact B1126159
  · exact B1126163
  · exact B1126167
  · exact B1126171
  · exact B1126175
  · exact B1126179
  · exact B1126183
  · exact B1126187
  · exact B1126191
  · exact B1126195
  · exact B1126199
  · exact B1126203
  · exact B1126207
  · exact B1126211
  · exact B1126215
  · exact B1126219
  · exact B1126223
  · exact B1126227
  · exact B1126231
  · exact B1126235
  · exact B1126239
  · exact B1126243
  · exact B1126247
  · exact B1126251
  · exact B1126255
  · exact B1126259
  · exact B1126263
  · exact B1126267
  · exact B1126271
  · exact B1126275
  · exact B1126279
  · exact B1126283
  · exact B1126287
  · exact B1126291
  · exact B1126295
  · exact B1126299
  · exact B1126303
  · exact B1126307
  · exact B1126311
  · exact B1126315
  · exact B1126319
  · exact B1126323
  · exact B1126327
  · exact B1126331
  · exact B1126335
  · exact B1126339
  · exact B1126343
  · exact B1126347
  · exact B1126351
  · exact B1126355
  · exact B1126359
  · exact B1126363
  · exact B1126367
  · exact B1126371
  · exact B1126375
  · exact B1126379
  · exact B1126383
  · exact B1126387
  · exact B1126391
  · exact B1126395
  · exact B1126399
  · exact B1126403
  · exact B1126407
  · exact B1126411
  · exact B1126415
  · exact B1126419
  · exact B1126423
  · exact B1126427
  · exact B1126431
  · exact B1126435
  · exact B1126439
  · exact B1126443
  · exact B1126447
  · exact B1126451
  · exact B1126455
  · exact B1126459
  · exact B1126463
  · exact B1126467
  · exact B1126471
  · exact B1126475
  · exact B1126479
  · exact B1126483
  · exact B1126487
  · exact B1126491
  · exact B1126495
  · exact B1126499
  · exact B1126503
  · exact B1126507
  · exact B1126511
  · exact B1126515
  · exact B1126519
  · exact B1126523
  · exact B1126527
  · exact B1126531
  · exact B1126535
  · exact B1126539
  · exact B1126543
  · exact B1126547
  · exact B1126551
  · exact B1126555
  · exact B1126559
  · exact B1126563
  · exact B1126567
  · exact B1126571
  · exact B1126575
  · exact B1126579
  · exact B1126583
  · exact B1126587
  · exact B1126591
  · exact B1126595
  · exact B1126599
  · exact B1126603
  · exact B1126607
  · exact B1126611
  · exact B1126615
  · exact B1126619
  · exact B1126623
  · exact B1126627
  · exact B1126631
  · exact B1126635
  · exact B1126639
  · exact B1126643
  · exact B1126647
  · exact B1126651
  · exact B1126655
  · exact B1126659
  · exact B1126663
  · exact B1126667
  · exact B1126671
  · exact B1126675
  · exact B1126679
  · exact B1126683
  · exact B1126687
  · exact B1126691
  · exact B1126695
  · exact B1126699
  · exact B1126703
  · exact B1126707
  · exact B1126711
  · exact B1126715
  · exact B1126719
  · exact B1126723
  · exact B1126727
  · exact B1126731
  · exact B1126735
  · exact B1126739
  · exact B1126743
  · exact B1126747
  · exact B1126751
  · exact B1126755
  · exact B1126759
  · exact B1126763
  · exact B1126767
  · exact B1126771
  · exact B1126775
  · exact B1126779
  · exact B1126783
  · exact B1126787
  · exact B1126791
  · exact B1126795
  · exact B1126799
  · exact B1126803
  · exact B1126807
  · exact B1126811
  · exact B1126815
  · exact B1126819
  · exact B1126823
  · exact B1126827
  · exact B1126831
  · exact B1126835
  · exact B1126839
  · exact B1126843
  · exact B1126847
  · exact B1126851
  · exact B1126855
  · exact B1126859
  · exact B1126863
  · exact B1126867
  · exact B1126871
  · exact B1126875
  · exact B1126879
  · exact B1126883
  · exact B1126887
  · exact B1126891
  · exact B1126895
  · exact B1126899
  · exact B1126903
  · exact B1126907
  · exact B1126911
  · exact B1126915
  · exact B1126919
  · exact B1126923
  · exact B1126927
  · exact B1126931
  · exact B1126935
  · exact B1126939
  · exact B1126943
  · exact B1126947
  · exact B1126951
  · exact B1126955
  · exact B1126959
  · exact B1126963
  · exact B1126967
  · exact B1126971
  · exact B1126975
  · exact B1126979
  · exact B1126983
  · exact B1126987
  · exact B1126991
  · exact B1126995
  · exact B1126999
  · exact B1127003
  · exact B1127007
  · exact B1127011
  · exact B1127015
  · exact B1127019
  · exact B1127023
  · exact B1127027
  · exact B1127031
  · exact B1127035
  · exact B1127039
  · exact B1127043
  · exact B1127047
  · exact B1127051
  · exact B1127055
  · exact B1127059
  · exact B1127063
  · exact B1127067
  · exact B1127071
  · exact B1127075
  · exact B1127079
  · exact B1127083
  · exact B1127087
  · exact B1127091
  · exact B1127095
  · exact B1127099
  · exact B1127103
  · exact B1127107
  · exact B1127111
  · exact B1127115
  · exact B1127119
  · exact B1127123
  · exact B1127127
  · exact B1127131
  · exact B1127135
  · exact B1127139
  · exact B1127143
  · exact B1127147
  · exact B1127151
  · exact B1127155
  · exact B1127159
  · exact B1127163
  · exact B1127167
  · exact B1127171
  · exact B1127175
  · exact B1127179
  · exact B1127183
  · exact B1127187
  · exact B1127191
  · exact B1127195
  · exact B1127199
  · exact B1127203
  · exact B1127207
  · exact B1127211
  · exact B1127215
  · exact B1127219
  · exact B1127223
  · exact B1127227
  · exact B1127231
  · exact B1127235
  · exact B1127239
  · exact B1127243
  · exact B1127247
  · exact B1127251
  · exact B1127255
  · exact B1127259
  · exact B1127263
  · exact B1127267
  · exact B1127271
  · exact B1127275
  · exact B1127279
  · exact B1127283
  · exact B1127287
  · exact B1127291
  · exact B1127295
  · exact B1127299
  · exact B1127303
  · exact B1127307
  · exact B1127311
  · exact B1127315
  · exact B1127319
  · exact B1127323
  · exact B1127327
  · exact B1127331
  · exact B1127335
  · exact B1127339
  · exact B1127343
  · exact B1127347
  · exact B1127351
  · exact B1127355
  · exact B1127359
  · exact B1127363
  · exact B1127367
  · exact B1127371
  · exact B1127375
  · exact B1127379
  · exact B1127383
  · exact B1127387
  · exact B1127391
  · exact B1127395
  · exact B1127399
  · exact B1127403
  · exact B1127407
  · exact B1127411
  · exact B1127415
  · exact B1127419
  · exact B1127423
  · exact B1127427

theorem C1 (j : ℕ) (h1 : 281857 ≤ j) (h2 : j ≤ 282156) : Blo 1124630 (4 * j + 3) := by
  interval_cases j
  · exact B1127431
  · exact B1127435
  · exact B1127439
  · exact B1127443
  · exact B1127447
  · exact B1127451
  · exact B1127455
  · exact B1127459
  · exact B1127463
  · exact B1127467
  · exact B1127471
  · exact B1127475
  · exact B1127479
  · exact B1127483
  · exact B1127487
  · exact B1127491
  · exact B1127495
  · exact B1127499
  · exact B1127503
  · exact B1127507
  · exact B1127511
  · exact B1127515
  · exact B1127519
  · exact B1127523
  · exact B1127527
  · exact B1127531
  · exact B1127535
  · exact B1127539
  · exact B1127543
  · exact B1127547
  · exact B1127551
  · exact B1127555
  · exact B1127559
  · exact B1127563
  · exact B1127567
  · exact B1127571
  · exact B1127575
  · exact B1127579
  · exact B1127583
  · exact B1127587
  · exact B1127591
  · exact B1127595
  · exact B1127599
  · exact B1127603
  · exact B1127607
  · exact B1127611
  · exact B1127615
  · exact B1127619
  · exact B1127623
  · exact B1127627
  · exact B1127631
  · exact B1127635
  · exact B1127639
  · exact B1127643
  · exact B1127647
  · exact B1127651
  · exact B1127655
  · exact B1127659
  · exact B1127663
  · exact B1127667
  · exact B1127671
  · exact B1127675
  · exact B1127679
  · exact B1127683
  · exact B1127687
  · exact B1127691
  · exact B1127695
  · exact B1127699
  · exact B1127703
  · exact B1127707
  · exact B1127711
  · exact B1127715
  · exact B1127719
  · exact B1127723
  · exact B1127727
  · exact B1127731
  · exact B1127735
  · exact B1127739
  · exact B1127743
  · exact B1127747
  · exact B1127751
  · exact B1127755
  · exact B1127759
  · exact B1127763
  · exact B1127767
  · exact B1127771
  · exact B1127775
  · exact B1127779
  · exact B1127783
  · exact B1127787
  · exact B1127791
  · exact B1127795
  · exact B1127799
  · exact B1127803
  · exact B1127807
  · exact B1127811
  · exact B1127815
  · exact B1127819
  · exact B1127823
  · exact B1127827
  · exact B1127831
  · exact B1127835
  · exact B1127839
  · exact B1127843
  · exact B1127847
  · exact B1127851
  · exact B1127855
  · exact B1127859
  · exact B1127863
  · exact B1127867
  · exact B1127871
  · exact B1127875
  · exact B1127879
  · exact B1127883
  · exact B1127887
  · exact B1127891
  · exact B1127895
  · exact B1127899
  · exact B1127903
  · exact B1127907
  · exact B1127911
  · exact B1127915
  · exact B1127919
  · exact B1127923
  · exact B1127927
  · exact B1127931
  · exact B1127935
  · exact B1127939
  · exact B1127943
  · exact B1127947
  · exact B1127951
  · exact B1127955
  · exact B1127959
  · exact B1127963
  · exact B1127967
  · exact B1127971
  · exact B1127975
  · exact B1127979
  · exact B1127983
  · exact B1127987
  · exact B1127991
  · exact B1127995
  · exact B1127999
  · exact B1128003
  · exact B1128007
  · exact B1128011
  · exact B1128015
  · exact B1128019
  · exact B1128023
  · exact B1128027
  · exact B1128031
  · exact B1128035
  · exact B1128039
  · exact B1128043
  · exact B1128047
  · exact B1128051
  · exact B1128055
  · exact B1128059
  · exact B1128063
  · exact B1128067
  · exact B1128071
  · exact B1128075
  · exact B1128079
  · exact B1128083
  · exact B1128087
  · exact B1128091
  · exact B1128095
  · exact B1128099
  · exact B1128103
  · exact B1128107
  · exact B1128111
  · exact B1128115
  · exact B1128119
  · exact B1128123
  · exact B1128127
  · exact B1128131
  · exact B1128135
  · exact B1128139
  · exact B1128143
  · exact B1128147
  · exact B1128151
  · exact B1128155
  · exact B1128159
  · exact B1128163
  · exact B1128167
  · exact B1128171
  · exact B1128175
  · exact B1128179
  · exact B1128183
  · exact B1128187
  · exact B1128191
  · exact B1128195
  · exact B1128199
  · exact B1128203
  · exact B1128207
  · exact B1128211
  · exact B1128215
  · exact B1128219
  · exact B1128223
  · exact B1128227
  · exact B1128231
  · exact B1128235
  · exact B1128239
  · exact B1128243
  · exact B1128247
  · exact B1128251
  · exact B1128255
  · exact B1128259
  · exact B1128263
  · exact B1128267
  · exact B1128271
  · exact B1128275
  · exact B1128279
  · exact B1128283
  · exact B1128287
  · exact B1128291
  · exact B1128295
  · exact B1128299
  · exact B1128303
  · exact B1128307
  · exact B1128311
  · exact B1128315
  · exact B1128319
  · exact B1128323
  · exact B1128327
  · exact B1128331
  · exact B1128335
  · exact B1128339
  · exact B1128343
  · exact B1128347
  · exact B1128351
  · exact B1128355
  · exact B1128359
  · exact B1128363
  · exact B1128367
  · exact B1128371
  · exact B1128375
  · exact B1128379
  · exact B1128383
  · exact B1128387
  · exact B1128391
  · exact B1128395
  · exact B1128399
  · exact B1128403
  · exact B1128407
  · exact B1128411
  · exact B1128415
  · exact B1128419
  · exact B1128423
  · exact B1128427
  · exact B1128431
  · exact B1128435
  · exact B1128439
  · exact B1128443
  · exact B1128447
  · exact B1128451
  · exact B1128455
  · exact B1128459
  · exact B1128463
  · exact B1128467
  · exact B1128471
  · exact B1128475
  · exact B1128479
  · exact B1128483
  · exact B1128487
  · exact B1128491
  · exact B1128495
  · exact B1128499
  · exact B1128503
  · exact B1128507
  · exact B1128511
  · exact B1128515
  · exact B1128519
  · exact B1128523
  · exact B1128527
  · exact B1128531
  · exact B1128535
  · exact B1128539
  · exact B1128543
  · exact B1128547
  · exact B1128551
  · exact B1128555
  · exact B1128559
  · exact B1128563
  · exact B1128567
  · exact B1128571
  · exact B1128575
  · exact B1128579
  · exact B1128583
  · exact B1128587
  · exact B1128591
  · exact B1128595
  · exact B1128599
  · exact B1128603
  · exact B1128607
  · exact B1128611
  · exact B1128615
  · exact B1128619
  · exact B1128623
  · exact B1128627

theorem solution (m : ℕ) (hlo : 1124630 ≤ m) (hhi : m ≤ 1128630) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 281157 ≤ j := by omega
    have hj2 : j ≤ 282156 := by omega
    have hb : Blo 1124630 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 281857 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
