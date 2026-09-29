-- Prove2me | solution 1 for syracuse_descends_range_1174404_1176404
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:28.107927+00:00
-- url     : https://prove2.me/submissions/4e56c6e9-6835-4474-9743-f07fe162945d

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


theorem B3964949 : Blo 1174404 3964949 := bbase (se 6 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 3964949 = 185857) (by norm_num)
theorem B2646053 : Blo 1174404 2646053 := bbase (se 4 (by rfl) ⟨248067, by rfl⟩ : syracuseStep 2646053 = 496135) (by norm_num)
theorem B2973773 : Blo 1174404 2973773 := bbase (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) (by norm_num)
theorem B1982549 : Blo 1174404 1982549 := bbase (se 8 (by rfl) ⟨11616, by rfl⟩ : syracuseStep 1982549 = 23233) (by norm_num)
theorem B5021797 : Blo 1174404 5021797 := bbase (se 4 (by rfl) ⟨470793, by rfl⟩ : syracuseStep 5021797 = 941587) (by norm_num)
theorem B2646125 : Blo 1174404 2646125 := bbase (se 3 (by rfl) ⟨496148, by rfl⟩ : syracuseStep 2646125 = 992297) (by norm_num)
theorem B6029477 : Blo 1174404 6029477 := bbase (se 4 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 6029477 = 1130527) (by norm_num)
theorem B2678957 : Blo 1174404 2678957 := bbase (se 3 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 2678957 = 1004609) (by norm_num)
theorem B4464821 : Blo 1174404 4464821 := bbase (se 5 (by rfl) ⟨209288, by rfl⟩ : syracuseStep 4464821 = 418577) (by norm_num)
theorem B1507513 : Blo 1174404 1507513 := bbase (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) (by norm_num)
theorem B2646197 : Blo 1174404 2646197 := bbase (se 5 (by rfl) ⟨124040, by rfl⟩ : syracuseStep 2646197 = 248081) (by norm_num)
theorem B1982677 : Blo 1174404 1982677 := bbase (se 7 (by rfl) ⟨23234, by rfl⟩ : syracuseStep 1982677 = 46469) (by norm_num)
theorem B2646269 : Blo 1174404 2646269 := bbase (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) (by norm_num)
theorem B1982765 : Blo 1174404 1982765 := bbase (se 3 (by rfl) ⟨371768, by rfl⟩ : syracuseStep 1982765 = 743537) (by norm_num)
theorem B2646341 : Blo 1174404 2646341 := bbase (se 4 (by rfl) ⟨248094, by rfl⟩ : syracuseStep 2646341 = 496189) (by norm_num)
theorem B1761629 : Blo 1174404 1761629 := bbase (se 3 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 1761629 = 660611) (by norm_num)
theorem B1761653 : Blo 1174404 1761653 := bbase (se 5 (by rfl) ⟨82577, by rfl⟩ : syracuseStep 1761653 = 165155) (by norm_num)
theorem B1761677 : Blo 1174404 1761677 := bbase (se 3 (by rfl) ⟨330314, by rfl⟩ : syracuseStep 1761677 = 660629) (by norm_num)
theorem B2646413 : Blo 1174404 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B10043797 : Blo 1174404 10043797 := bbase (se 6 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 10043797 = 470803) (by norm_num)
theorem B1761701 : Blo 1174404 1761701 := bbase (se 4 (by rfl) ⟨165159, by rfl⟩ : syracuseStep 1761701 = 330319) (by norm_num)
theorem B2974117 : Blo 1174404 2974117 := bbase (se 4 (by rfl) ⟨278823, by rfl⟩ : syracuseStep 2974117 = 557647) (by norm_num)
theorem B1982893 : Blo 1174404 1982893 := bbase (se 3 (by rfl) ⟨371792, by rfl⟩ : syracuseStep 1982893 = 743585) (by norm_num)
theorem B5947829 : Blo 1174404 5947829 := bbase (se 5 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 5947829 = 557609) (by norm_num)
theorem B1761725 : Blo 1174404 1761725 := bbase (se 3 (by rfl) ⟨330323, by rfl⟩ : syracuseStep 1761725 = 660647) (by norm_num)
theorem B3965381 : Blo 1174404 3965381 := bbase (se 4 (by rfl) ⟨371754, by rfl⟩ : syracuseStep 3965381 = 743509) (by norm_num)
theorem B1761749 : Blo 1174404 1761749 := bbase (se 7 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 1761749 = 41291) (by norm_num)
theorem B2646485 : Blo 1174404 2646485 := bbase (se 7 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 2646485 = 62027) (by norm_num)
theorem B1761773 : Blo 1174404 1761773 := bbase (se 3 (by rfl) ⟨330332, by rfl⟩ : syracuseStep 1761773 = 660665) (by norm_num)
theorem B1761797 : Blo 1174404 1761797 := bbase (se 4 (by rfl) ⟨165168, by rfl⟩ : syracuseStep 1761797 = 330337) (by norm_num)
theorem B1982981 : Blo 1174404 1982981 := bbase (se 4 (by rfl) ⟨185904, by rfl⟩ : syracuseStep 1982981 = 371809) (by norm_num)
theorem B2974229 : Blo 1174404 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1761821 : Blo 1174404 1761821 := bbase (se 3 (by rfl) ⟨330341, by rfl⟩ : syracuseStep 1761821 = 660683) (by norm_num)
theorem B2646557 : Blo 1174404 2646557 := bbase (se 3 (by rfl) ⟨496229, by rfl⟩ : syracuseStep 2646557 = 992459) (by norm_num)
theorem B1761845 : Blo 1174404 1761845 := bbase (se 5 (by rfl) ⟨82586, by rfl⟩ : syracuseStep 1761845 = 165173) (by norm_num)
theorem B5644853 : Blo 1174404 5644853 := bbase (se 5 (by rfl) ⟨264602, by rfl⟩ : syracuseStep 5644853 = 529205) (by norm_num)
theorem B5653061 : Blo 1174404 5653061 := bbase (se 4 (by rfl) ⟨529974, by rfl⟩ : syracuseStep 5653061 = 1059949) (by norm_num)
theorem B1761869 : Blo 1174404 1761869 := bbase (se 3 (by rfl) ⟨330350, by rfl⟩ : syracuseStep 1761869 = 660701) (by norm_num)
theorem B1761893 : Blo 1174404 1761893 := bbase (se 4 (by rfl) ⟨165177, by rfl⟩ : syracuseStep 1761893 = 330355) (by norm_num)
theorem B2646629 : Blo 1174404 2646629 := bbase (se 4 (by rfl) ⟨248121, by rfl⟩ : syracuseStep 2646629 = 496243) (by norm_num)
theorem B1761917 : Blo 1174404 1761917 := bbase (se 3 (by rfl) ⟨330359, by rfl⟩ : syracuseStep 1761917 = 660719) (by norm_num)
theorem B1983109 : Blo 1174404 1983109 := bbase (se 4 (by rfl) ⟨185916, by rfl⟩ : syracuseStep 1983109 = 371833) (by norm_num)
theorem B1761941 : Blo 1174404 1761941 := bbase (se 6 (by rfl) ⟨41295, by rfl⟩ : syracuseStep 1761941 = 82591) (by norm_num)
theorem B1761965 : Blo 1174404 1761965 := bbase (se 3 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 1761965 = 660737) (by norm_num)
theorem B2646701 : Blo 1174404 2646701 := bbase (se 3 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 2646701 = 992513) (by norm_num)
theorem B1761989 : Blo 1174404 1761989 := bbase (se 4 (by rfl) ⟨165186, by rfl⟩ : syracuseStep 1761989 = 330373) (by norm_num)
theorem B3572437 : Blo 1174404 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B2974421 : Blo 1174404 2974421 := bbase (se 7 (by rfl) ⟨34856, by rfl⟩ : syracuseStep 2974421 = 69713) (by norm_num)
theorem B13394645 : Blo 1174404 13394645 := bbase (se 7 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 13394645 = 313937) (by norm_num)
theorem B1762013 : Blo 1174404 1762013 := bbase (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) (by norm_num)
theorem B1983197 : Blo 1174404 1983197 := bbase (se 3 (by rfl) ⟨371849, by rfl⟩ : syracuseStep 1983197 = 743699) (by norm_num)
theorem B1762037 : Blo 1174404 1762037 := bbase (se 5 (by rfl) ⟨82595, by rfl⟩ : syracuseStep 1762037 = 165191) (by norm_num)
theorem B2646773 : Blo 1174404 2646773 := bbase (se 5 (by rfl) ⟨124067, by rfl⟩ : syracuseStep 2646773 = 248135) (by norm_num)
theorem B1762061 : Blo 1174404 1762061 := bbase (se 3 (by rfl) ⟨330386, by rfl⟩ : syracuseStep 1762061 = 660773) (by norm_num)
theorem B2679565 : Blo 1174404 2679565 := bbase (se 3 (by rfl) ⟨502418, by rfl⟩ : syracuseStep 2679565 = 1004837) (by norm_num)
theorem B1762085 : Blo 1174404 1762085 := bbase (se 4 (by rfl) ⟨165195, by rfl⟩ : syracuseStep 1762085 = 330391) (by norm_num)
theorem B1762109 : Blo 1174404 1762109 := bbase (se 3 (by rfl) ⟨330395, by rfl⟩ : syracuseStep 1762109 = 660791) (by norm_num)
theorem B2646845 : Blo 1174404 2646845 := bbase (se 3 (by rfl) ⟨496283, by rfl⟩ : syracuseStep 2646845 = 992567) (by norm_num)
theorem B1762133 : Blo 1174404 1762133 := bbase (se 9 (by rfl) ⟨5162, by rfl⟩ : syracuseStep 1762133 = 10325) (by norm_num)
theorem B1983325 : Blo 1174404 1983325 := bbase (se 3 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 1983325 = 743747) (by norm_num)
theorem B1254241 : Blo 1174404 1254241 := bbase (se 2 (by rfl) ⟨470340, by rfl⟩ : syracuseStep 1254241 = 940681) (by norm_num)
theorem B1762157 : Blo 1174404 1762157 := bbase (se 3 (by rfl) ⟨330404, by rfl⟩ : syracuseStep 1762157 = 660809) (by norm_num)
theorem B3965813 : Blo 1174404 3965813 := bbase (se 5 (by rfl) ⟨185897, by rfl⟩ : syracuseStep 3965813 = 371795) (by norm_num)
theorem B1762181 : Blo 1174404 1762181 := bbase (se 4 (by rfl) ⟨165204, by rfl⟩ : syracuseStep 1762181 = 330409) (by norm_num)
theorem B5088133 : Blo 1174404 5088133 := bbase (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) (by norm_num)
theorem B3015557 : Blo 1174404 3015557 := bbase (se 4 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 3015557 = 565417) (by norm_num)
theorem B1762205 : Blo 1174404 1762205 := bbase (se 3 (by rfl) ⟨330413, by rfl⟩ : syracuseStep 1762205 = 660827) (by norm_num)
theorem B1254313 : Blo 1174404 1254313 := bbase (se 2 (by rfl) ⟨470367, by rfl⟩ : syracuseStep 1254313 = 940735) (by norm_num)
theorem B1762229 : Blo 1174404 1762229 := bbase (se 5 (by rfl) ⟨82604, by rfl⟩ : syracuseStep 1762229 = 165209) (by norm_num)
theorem B1983413 : Blo 1174404 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B1762253 : Blo 1174404 1762253 := bbase (se 3 (by rfl) ⟨330422, by rfl⟩ : syracuseStep 1762253 = 660845) (by norm_num)
theorem B15074261 : Blo 1174404 15074261 := bbase (se 7 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 15074261 = 353303) (by norm_num)
theorem B1762277 : Blo 1174404 1762277 := bbase (se 4 (by rfl) ⟨165213, by rfl⟩ : syracuseStep 1762277 = 330427) (by norm_num)
theorem B1762301 : Blo 1174404 1762301 := bbase (se 3 (by rfl) ⟨330431, by rfl⟩ : syracuseStep 1762301 = 660863) (by norm_num)
theorem B1762325 : Blo 1174404 1762325 := bbase (se 6 (by rfl) ⟨41304, by rfl⟩ : syracuseStep 1762325 = 82609) (by norm_num)
theorem B8471573 : Blo 1174404 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B10322965 : Blo 1174404 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B1762349 : Blo 1174404 1762349 := bbase (se 3 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 1762349 = 660881) (by norm_num)
theorem B2974765 : Blo 1174404 2974765 := bbase (se 3 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 2974765 = 1115537) (by norm_num)
theorem B1983541 : Blo 1174404 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B1762373 : Blo 1174404 1762373 := bbase (se 4 (by rfl) ⟨165222, by rfl⟩ : syracuseStep 1762373 = 330445) (by norm_num)
theorem B4523093 : Blo 1174404 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B1762397 : Blo 1174404 1762397 := bbase (se 3 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 1762397 = 660899) (by norm_num)
theorem B1762421 : Blo 1174404 1762421 := bbase (se 5 (by rfl) ⟨82613, by rfl⟩ : syracuseStep 1762421 = 165227) (by norm_num)
theorem B4236421 : Blo 1174404 4236421 := bbase (se 4 (by rfl) ⟨397164, by rfl⟩ : syracuseStep 4236421 = 794329) (by norm_num)
theorem B1762445 : Blo 1174404 1762445 := bbase (se 3 (by rfl) ⟨330458, by rfl⟩ : syracuseStep 1762445 = 660917) (by norm_num)
theorem B1983629 : Blo 1174404 1983629 := bbase (se 3 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 1983629 = 743861) (by norm_num)
theorem B2974877 : Blo 1174404 2974877 := bbase (se 3 (by rfl) ⟨557789, by rfl⟩ : syracuseStep 2974877 = 1115579) (by norm_num)
theorem B1762469 : Blo 1174404 1762469 := bbase (se 4 (by rfl) ⟨165231, by rfl⟩ : syracuseStep 1762469 = 330463) (by norm_num)
theorem B1762493 : Blo 1174404 1762493 := bbase (se 3 (by rfl) ⟨330467, by rfl⟩ : syracuseStep 1762493 = 660935) (by norm_num)
theorem B36660437 : Blo 1174404 36660437 := bbase (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) (by norm_num)
theorem B1762517 : Blo 1174404 1762517 := bbase (se 7 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 1762517 = 41309) (by norm_num)
theorem B1672429 : Blo 1174404 1672429 := bbase (se 3 (by rfl) ⟨313580, by rfl⟩ : syracuseStep 1672429 = 627161) (by norm_num)
theorem B1762541 : Blo 1174404 1762541 := bbase (se 3 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 1762541 = 660953) (by norm_num)
theorem B1762565 : Blo 1174404 1762565 := bbase (se 4 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 1762565 = 330481) (by norm_num)
theorem B1983757 : Blo 1174404 1983757 := bbase (se 3 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 1983757 = 743909) (by norm_num)
theorem B1254685 : Blo 1174404 1254685 := bbase (se 3 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 1254685 = 470507) (by norm_num)
theorem B1762589 : Blo 1174404 1762589 := bbase (se 3 (by rfl) ⟨330485, by rfl⟩ : syracuseStep 1762589 = 660971) (by norm_num)
theorem B3966245 : Blo 1174404 3966245 := bbase (se 4 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 3966245 = 743671) (by norm_num)
theorem B1762613 : Blo 1174404 1762613 := bbase (se 5 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 1762613 = 165245) (by norm_num)
theorem B1762637 : Blo 1174404 1762637 := bbase (se 3 (by rfl) ⟨330494, by rfl⟩ : syracuseStep 1762637 = 660989) (by norm_num)
theorem B2975069 : Blo 1174404 2975069 := bbase (se 3 (by rfl) ⟨557825, by rfl⟩ : syracuseStep 2975069 = 1115651) (by norm_num)
theorem B1762661 : Blo 1174404 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1983845 : Blo 1174404 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B1762685 : Blo 1174404 1762685 := bbase (se 3 (by rfl) ⟨330503, by rfl⟩ : syracuseStep 1762685 = 661007) (by norm_num)
theorem B1762709 : Blo 1174404 1762709 := bbase (se 6 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 1762709 = 82627) (by norm_num)
theorem B5727653 : Blo 1174404 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B2229677 : Blo 1174404 2229677 := bbase (se 3 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 2229677 = 836129) (by norm_num)
theorem B1762733 : Blo 1174404 1762733 := bbase (se 3 (by rfl) ⟨330512, by rfl⟩ : syracuseStep 1762733 = 661025) (by norm_num)
theorem B1672645 : Blo 1174404 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B1762757 : Blo 1174404 1762757 := bbase (se 4 (by rfl) ⟨165258, by rfl⟩ : syracuseStep 1762757 = 330517) (by norm_num)
theorem B1762781 : Blo 1174404 1762781 := bbase (se 3 (by rfl) ⟨330521, by rfl⟩ : syracuseStep 1762781 = 661043) (by norm_num)
theorem B1983973 : Blo 1174404 1983973 := bbase (se 4 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 1983973 = 371995) (by norm_num)
theorem B1762805 : Blo 1174404 1762805 := bbase (se 5 (by rfl) ⟨82631, by rfl⟩ : syracuseStep 1762805 = 165263) (by norm_num)
theorem B1762829 : Blo 1174404 1762829 := bbase (se 3 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 1762829 = 661061) (by norm_num)
theorem B1762853 : Blo 1174404 1762853 := bbase (se 4 (by rfl) ⟨165267, by rfl⟩ : syracuseStep 1762853 = 330535) (by norm_num)
theorem B1762877 : Blo 1174404 1762877 := bbase (se 3 (by rfl) ⟨330539, by rfl⟩ : syracuseStep 1762877 = 661079) (by norm_num)
theorem B1984061 : Blo 1174404 1984061 := bbase (se 3 (by rfl) ⟨372011, by rfl⟩ : syracuseStep 1984061 = 744023) (by norm_num)
theorem B4236869 : Blo 1174404 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B1762901 : Blo 1174404 1762901 := bbase (se 8 (by rfl) ⟨10329, by rfl⟩ : syracuseStep 1762901 = 20659) (by norm_num)
theorem B4769381 : Blo 1174404 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B1762925 : Blo 1174404 1762925 := bbase (se 3 (by rfl) ⟨330548, by rfl⟩ : syracuseStep 1762925 = 661097) (by norm_num)
theorem B2508421 : Blo 1174404 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B1762949 : Blo 1174404 1762949 := bbase (se 4 (by rfl) ⟨165276, by rfl⟩ : syracuseStep 1762949 = 330553) (by norm_num)
theorem B1255061 : Blo 1174404 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B1590941 : Blo 1174404 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B1762973 : Blo 1174404 1762973 := bbase (se 3 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 1762973 = 661115) (by norm_num)
theorem B1787557 : Blo 1174404 1787557 := bbase (se 4 (by rfl) ⟨167583, by rfl⟩ : syracuseStep 1787557 = 335167) (by norm_num)
theorem B1762997 : Blo 1174404 1762997 := bbase (se 5 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 1762997 = 165281) (by norm_num)
theorem B2975413 : Blo 1174404 2975413 := bbase (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) (by norm_num)
theorem B1984189 : Blo 1174404 1984189 := bbase (se 3 (by rfl) ⟨372035, by rfl⟩ : syracuseStep 1984189 = 744071) (by norm_num)
theorem B5949125 : Blo 1174404 5949125 := bbase (se 4 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 5949125 = 1115461) (by norm_num)
theorem B1763021 : Blo 1174404 1763021 := bbase (se 3 (by rfl) ⟨330566, by rfl⟩ : syracuseStep 1763021 = 661133) (by norm_num)
theorem B3966677 : Blo 1174404 3966677 := bbase (se 7 (by rfl) ⟨46484, by rfl⟩ : syracuseStep 3966677 = 92969) (by norm_num)
theorem B3819221 : Blo 1174404 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B1255133 : Blo 1174404 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B1763045 : Blo 1174404 1763045 := bbase (se 4 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 1763045 = 330571) (by norm_num)
theorem B1763069 : Blo 1174404 1763069 := bbase (se 3 (by rfl) ⟨330575, by rfl⟩ : syracuseStep 1763069 = 661151) (by norm_num)
theorem B1763093 : Blo 1174404 1763093 := bbase (se 6 (by rfl) ⟨41322, by rfl⟩ : syracuseStep 1763093 = 82645) (by norm_num)
theorem B1984277 : Blo 1174404 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B2975525 : Blo 1174404 2975525 := bbase (se 4 (by rfl) ⟨278955, by rfl⟩ : syracuseStep 2975525 = 557911) (by norm_num)
theorem B1763117 : Blo 1174404 1763117 := bbase (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) (by norm_num)
theorem B1673021 : Blo 1174404 1673021 := bbase (se 3 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 1673021 = 627383) (by norm_num)
theorem B1763141 : Blo 1174404 1763141 := bbase (se 4 (by rfl) ⟨165294, by rfl⟩ : syracuseStep 1763141 = 330589) (by norm_num)
theorem B1763165 : Blo 1174404 1763165 := bbase (se 3 (by rfl) ⟨330593, by rfl⟩ : syracuseStep 1763165 = 661187) (by norm_num)
theorem B1271665 : Blo 1174404 1271665 := bbase (se 2 (by rfl) ⟨476874, by rfl⟩ : syracuseStep 1271665 = 953749) (by norm_num)
theorem B1763189 : Blo 1174404 1763189 := bbase (se 5 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 1763189 = 165299) (by norm_num)
theorem B1763213 : Blo 1174404 1763213 := bbase (se 3 (by rfl) ⟨330602, by rfl⟩ : syracuseStep 1763213 = 661205) (by norm_num)
theorem B1984405 : Blo 1174404 1984405 := bbase (se 6 (by rfl) ⟨46509, by rfl⟩ : syracuseStep 1984405 = 93019) (by norm_num)
theorem B8931221 : Blo 1174404 8931221 := bbase (se 6 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 8931221 = 418651) (by norm_num)
theorem B1255321 : Blo 1174404 1255321 := bbase (se 2 (by rfl) ⟨470745, by rfl⟩ : syracuseStep 1255321 = 941491) (by norm_num)
theorem B1763237 : Blo 1174404 1763237 := bbase (se 4 (by rfl) ⟨165303, by rfl⟩ : syracuseStep 1763237 = 330607) (by norm_num)
theorem B1763261 : Blo 1174404 1763261 := bbase (se 3 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 1763261 = 661223) (by norm_num)
theorem B1763285 : Blo 1174404 1763285 := bbase (se 7 (by rfl) ⟨20663, by rfl⟩ : syracuseStep 1763285 = 41327) (by norm_num)
theorem B2975717 : Blo 1174404 2975717 := bbase (se 4 (by rfl) ⟨278973, by rfl⟩ : syracuseStep 2975717 = 557947) (by norm_num)
theorem B1763309 : Blo 1174404 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B1984493 : Blo 1174404 1984493 := bbase (se 3 (by rfl) ⟨372092, by rfl⟩ : syracuseStep 1984493 = 744185) (by norm_num)
theorem B1763333 : Blo 1174404 1763333 := bbase (se 4 (by rfl) ⟨165312, by rfl⟩ : syracuseStep 1763333 = 330625) (by norm_num)
theorem B1763357 : Blo 1174404 1763357 := bbase (se 3 (by rfl) ⟨330629, by rfl⟩ : syracuseStep 1763357 = 661259) (by norm_num)
theorem B1763381 : Blo 1174404 1763381 := bbase (se 5 (by rfl) ⟨82658, by rfl⟩ : syracuseStep 1763381 = 165317) (by norm_num)
theorem B1763405 : Blo 1174404 1763405 := bbase (se 3 (by rfl) ⟨330638, by rfl⟩ : syracuseStep 1763405 = 661277) (by norm_num)
theorem B1255505 : Blo 1174404 1255505 := bbase (se 2 (by rfl) ⟨470814, by rfl⟩ : syracuseStep 1255505 = 941629) (by norm_num)
theorem B1763429 : Blo 1174404 1763429 := bbase (se 4 (by rfl) ⟨165321, by rfl⟩ : syracuseStep 1763429 = 330643) (by norm_num)
theorem B1984621 : Blo 1174404 1984621 := bbase (se 3 (by rfl) ⟨372116, by rfl⟩ : syracuseStep 1984621 = 744233) (by norm_num)
theorem B1763453 : Blo 1174404 1763453 := bbase (se 3 (by rfl) ⟨330647, by rfl⟩ : syracuseStep 1763453 = 661295) (by norm_num)
theorem B3967109 : Blo 1174404 3967109 := bbase (se 4 (by rfl) ⟨371916, by rfl⟩ : syracuseStep 3967109 = 743833) (by norm_num)
theorem B5646485 : Blo 1174404 5646485 := bbase (se 6 (by rfl) ⟨132339, by rfl⟩ : syracuseStep 5646485 = 264679) (by norm_num)
theorem B1763477 : Blo 1174404 1763477 := bbase (se 6 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 1763477 = 82663) (by norm_num)
theorem B2230429 : Blo 1174404 2230429 := bbase (se 3 (by rfl) ⟨418205, by rfl⟩ : syracuseStep 2230429 = 836411) (by norm_num)
theorem B1763501 : Blo 1174404 1763501 := bbase (se 3 (by rfl) ⟨330656, by rfl⟩ : syracuseStep 1763501 = 661313) (by norm_num)
theorem B1763525 : Blo 1174404 1763525 := bbase (se 4 (by rfl) ⟨165330, by rfl⟩ : syracuseStep 1763525 = 330661) (by norm_num)
theorem B1984709 : Blo 1174404 1984709 := bbase (se 4 (by rfl) ⟨186066, by rfl⟩ : syracuseStep 1984709 = 372133) (by norm_num)
theorem B1763549 : Blo 1174404 1763549 := bbase (se 3 (by rfl) ⟨330665, by rfl⟩ : syracuseStep 1763549 = 661331) (by norm_num)
theorem B1763573 : Blo 1174404 1763573 := bbase (se 5 (by rfl) ⟨82667, by rfl⟩ : syracuseStep 1763573 = 165335) (by norm_num)
theorem B1321213 : Blo 1174404 1321213 := bbase (se 3 (by rfl) ⟨247727, by rfl⟩ : syracuseStep 1321213 = 495455) (by norm_num)
theorem B3221765 : Blo 1174404 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B1763597 : Blo 1174404 1763597 := bbase (se 3 (by rfl) ⟨330674, by rfl⟩ : syracuseStep 1763597 = 661349) (by norm_num)
theorem B1321249 : Blo 1174404 1321249 := bbase (se 2 (by rfl) ⟨495468, by rfl⟩ : syracuseStep 1321249 = 990937) (by norm_num)
theorem B1763621 : Blo 1174404 1763621 := bbase (se 4 (by rfl) ⟨165339, by rfl⟩ : syracuseStep 1763621 = 330679) (by norm_num)
theorem B2230573 : Blo 1174404 2230573 := bbase (se 3 (by rfl) ⟨418232, by rfl⟩ : syracuseStep 2230573 = 836465) (by norm_num)
theorem B8923445 : Blo 1174404 8923445 := bbase (se 5 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 8923445 = 836573) (by norm_num)
theorem B2976061 : Blo 1174404 2976061 := bbase (se 3 (by rfl) ⟨558011, by rfl⟩ : syracuseStep 2976061 = 1116023) (by norm_num)
theorem B1763645 : Blo 1174404 1763645 := bbase (se 3 (by rfl) ⟨330683, by rfl⟩ : syracuseStep 1763645 = 661367) (by norm_num)
theorem B1321285 : Blo 1174404 1321285 := bbase (se 4 (by rfl) ⟨123870, by rfl⟩ : syracuseStep 1321285 = 247741) (by norm_num)
theorem B1984837 : Blo 1174404 1984837 := bbase (se 4 (by rfl) ⟨186078, by rfl⟩ : syracuseStep 1984837 = 372157) (by norm_num)
theorem B1763669 : Blo 1174404 1763669 := bbase (se 10 (by rfl) ⟨2583, by rfl⟩ : syracuseStep 1763669 = 5167) (by norm_num)
theorem B10045781 : Blo 1174404 10045781 := bbase (se 10 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 10045781 = 29431) (by norm_num)
theorem B1321321 : Blo 1174404 1321321 := bbase (se 2 (by rfl) ⟨495495, by rfl⟩ : syracuseStep 1321321 = 990991) (by norm_num)
theorem B1763693 : Blo 1174404 1763693 := bbase (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) (by norm_num)
theorem B8046965 : Blo 1174404 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B1763717 : Blo 1174404 1763717 := bbase (se 4 (by rfl) ⟨165348, by rfl⟩ : syracuseStep 1763717 = 330697) (by norm_num)
theorem B1321357 : Blo 1174404 1321357 := bbase (se 3 (by rfl) ⟨247754, by rfl⟩ : syracuseStep 1321357 = 495509) (by norm_num)
theorem B3344789 : Blo 1174404 3344789 := bbase (se 6 (by rfl) ⟨78393, by rfl⟩ : syracuseStep 3344789 = 156787) (by norm_num)
theorem B2681245 : Blo 1174404 2681245 := bbase (se 3 (by rfl) ⟨502733, by rfl⟩ : syracuseStep 2681245 = 1005467) (by norm_num)
theorem B1763741 : Blo 1174404 1763741 := bbase (se 3 (by rfl) ⟨330701, by rfl⟩ : syracuseStep 1763741 = 661403) (by norm_num)
theorem B1984925 : Blo 1174404 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B2976173 : Blo 1174404 2976173 := bbase (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) (by norm_num)
theorem B1321393 : Blo 1174404 1321393 := bbase (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) (by norm_num)
theorem B1763765 : Blo 1174404 1763765 := bbase (se 5 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 1763765 = 165353) (by norm_num)
theorem B1411525 : Blo 1174404 1411525 := bbase (se 4 (by rfl) ⟨132330, by rfl⟩ : syracuseStep 1411525 = 264661) (by norm_num)
theorem B2230733 : Blo 1174404 2230733 := bbase (se 3 (by rfl) ⟨418262, by rfl⟩ : syracuseStep 2230733 = 836525) (by norm_num)
theorem B1763789 : Blo 1174404 1763789 := bbase (se 3 (by rfl) ⟨330710, by rfl⟩ : syracuseStep 1763789 = 661421) (by norm_num)
theorem B1321429 : Blo 1174404 1321429 := bbase (se 7 (by rfl) ⟨15485, by rfl⟩ : syracuseStep 1321429 = 30971) (by norm_num)
theorem B11446741 : Blo 1174404 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B1763813 : Blo 1174404 1763813 := bbase (se 4 (by rfl) ⟨165357, by rfl⟩ : syracuseStep 1763813 = 330715) (by norm_num)
theorem B1321465 : Blo 1174404 1321465 := bbase (se 2 (by rfl) ⟨495549, by rfl⟩ : syracuseStep 1321465 = 991099) (by norm_num)
theorem B2509309 : Blo 1174404 2509309 := bbase (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) (by norm_num)
theorem B1763837 : Blo 1174404 1763837 := bbase (se 3 (by rfl) ⟨330719, by rfl⟩ : syracuseStep 1763837 = 661439) (by norm_num)
theorem B3574277 : Blo 1174404 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B1763861 : Blo 1174404 1763861 := bbase (se 6 (by rfl) ⟨41340, by rfl⟩ : syracuseStep 1763861 = 82681) (by norm_num)
theorem B1321501 : Blo 1174404 1321501 := bbase (se 3 (by rfl) ⟨247781, by rfl⟩ : syracuseStep 1321501 = 495563) (by norm_num)
theorem B1985053 : Blo 1174404 1985053 := bbase (se 3 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 1985053 = 744395) (by norm_num)
theorem B1763885 : Blo 1174404 1763885 := bbase (se 3 (by rfl) ⟨330728, by rfl⟩ : syracuseStep 1763885 = 661457) (by norm_num)
theorem B3967541 : Blo 1174404 3967541 := bbase (se 5 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 3967541 = 371957) (by norm_num)
theorem B1321537 : Blo 1174404 1321537 := bbase (se 2 (by rfl) ⟨495576, by rfl⟩ : syracuseStep 1321537 = 991153) (by norm_num)
theorem B1763909 : Blo 1174404 1763909 := bbase (se 4 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 1763909 = 330733) (by norm_num)
theorem B2230877 : Blo 1174404 2230877 := bbase (se 3 (by rfl) ⟨418289, by rfl⟩ : syracuseStep 2230877 = 836579) (by norm_num)
theorem B1763933 : Blo 1174404 1763933 := bbase (se 3 (by rfl) ⟨330737, by rfl⟩ : syracuseStep 1763933 = 661475) (by norm_num)
theorem B1321573 : Blo 1174404 1321573 := bbase (se 4 (by rfl) ⟨123897, by rfl⟩ : syracuseStep 1321573 = 247795) (by norm_num)
theorem B2976365 : Blo 1174404 2976365 := bbase (se 3 (by rfl) ⟨558068, by rfl⟩ : syracuseStep 2976365 = 1116137) (by norm_num)
theorem B1763957 : Blo 1174404 1763957 := bbase (se 5 (by rfl) ⟨82685, by rfl⟩ : syracuseStep 1763957 = 165371) (by norm_num)
theorem B1985141 : Blo 1174404 1985141 := bbase (se 5 (by rfl) ⟨93053, by rfl⟩ : syracuseStep 1985141 = 186107) (by norm_num)
theorem B1321609 : Blo 1174404 1321609 := bbase (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) (by norm_num)
theorem B1763981 : Blo 1174404 1763981 := bbase (se 3 (by rfl) ⟨330746, by rfl⟩ : syracuseStep 1763981 = 661493) (by norm_num)
theorem B4459157 : Blo 1174404 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B1764005 : Blo 1174404 1764005 := bbase (se 4 (by rfl) ⟨165375, by rfl⟩ : syracuseStep 1764005 = 330751) (by norm_num)
theorem B1321645 : Blo 1174404 1321645 := bbase (se 3 (by rfl) ⟨247808, by rfl⟩ : syracuseStep 1321645 = 495617) (by norm_num)
theorem B1764029 : Blo 1174404 1764029 := bbase (se 3 (by rfl) ⟨330755, by rfl⟩ : syracuseStep 1764029 = 661511) (by norm_num)
theorem B1321681 : Blo 1174404 1321681 := bbase (se 2 (by rfl) ⟨495630, by rfl⟩ : syracuseStep 1321681 = 991261) (by norm_num)
theorem B1764053 : Blo 1174404 1764053 := bbase (se 7 (by rfl) ⟨20672, by rfl⟩ : syracuseStep 1764053 = 41345) (by norm_num)
theorem B1764077 : Blo 1174404 1764077 := bbase (se 3 (by rfl) ⟨330764, by rfl⟩ : syracuseStep 1764077 = 661529) (by norm_num)
theorem B1321717 : Blo 1174404 1321717 := bbase (se 5 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 1321717 = 123911) (by norm_num)
theorem B1764101 : Blo 1174404 1764101 := bbase (se 4 (by rfl) ⟨165384, by rfl⟩ : syracuseStep 1764101 = 330769) (by norm_num)
theorem B1321753 : Blo 1174404 1321753 := bbase (se 2 (by rfl) ⟨495657, by rfl⟩ : syracuseStep 1321753 = 991315) (by norm_num)
theorem B2116381 : Blo 1174404 2116381 := bbase (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) (by norm_num)
theorem B1764125 : Blo 1174404 1764125 := bbase (se 3 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 1764125 = 661547) (by norm_num)
theorem B1764149 : Blo 1174404 1764149 := bbase (se 5 (by rfl) ⟨82694, by rfl⟩ : syracuseStep 1764149 = 165389) (by norm_num)
theorem B1321789 : Blo 1174404 1321789 := bbase (se 3 (by rfl) ⟨247835, by rfl⟩ : syracuseStep 1321789 = 495671) (by norm_num)
theorem B1764173 : Blo 1174404 1764173 := bbase (se 3 (by rfl) ⟨330782, by rfl⟩ : syracuseStep 1764173 = 661565) (by norm_num)
theorem B1321825 : Blo 1174404 1321825 := bbase (se 2 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 1321825 = 991369) (by norm_num)
theorem B1764197 : Blo 1174404 1764197 := bbase (se 4 (by rfl) ⟨165393, by rfl⟩ : syracuseStep 1764197 = 330787) (by norm_num)
theorem B2231165 : Blo 1174404 2231165 := bbase (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) (by norm_num)
theorem B1764221 : Blo 1174404 1764221 := bbase (se 3 (by rfl) ⟨330791, by rfl⟩ : syracuseStep 1764221 = 661583) (by norm_num)
theorem B1321861 : Blo 1174404 1321861 := bbase (se 4 (by rfl) ⟨123924, by rfl⟩ : syracuseStep 1321861 = 247849) (by norm_num)
theorem B3763093 : Blo 1174404 3763093 := bbase (se 6 (by rfl) ⟨88197, by rfl⟩ : syracuseStep 3763093 = 176395) (by norm_num)
theorem B1190809 : Blo 1174404 1190809 := bbase (se 2 (by rfl) ⟨446553, by rfl⟩ : syracuseStep 1190809 = 893107) (by norm_num)
theorem B1321897 : Blo 1174404 1321897 := bbase (se 2 (by rfl) ⟨495711, by rfl⟩ : syracuseStep 1321897 = 991423) (by norm_num)
theorem B1764269 : Blo 1174404 1764269 := bbase (se 3 (by rfl) ⟨330800, by rfl⟩ : syracuseStep 1764269 = 661601) (by norm_num)
theorem B4459445 : Blo 1174404 4459445 := bbase (se 5 (by rfl) ⟨209036, by rfl⟩ : syracuseStep 4459445 = 418073) (by norm_num)
theorem B2976709 : Blo 1174404 2976709 := bbase (se 4 (by rfl) ⟨279066, by rfl⟩ : syracuseStep 2976709 = 558133) (by norm_num)
theorem B1764293 : Blo 1174404 1764293 := bbase (se 4 (by rfl) ⟨165402, by rfl⟩ : syracuseStep 1764293 = 330805) (by norm_num)
theorem B1321933 : Blo 1174404 1321933 := bbase (se 3 (by rfl) ⟨247862, by rfl⟩ : syracuseStep 1321933 = 495725) (by norm_num)
theorem B5950421 : Blo 1174404 5950421 := bbase (se 7 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 5950421 = 139463) (by norm_num)
theorem B1764317 : Blo 1174404 1764317 := bbase (se 3 (by rfl) ⟨330809, by rfl⟩ : syracuseStep 1764317 = 661619) (by norm_num)
theorem B3967973 : Blo 1174404 3967973 := bbase (se 4 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 3967973 = 743995) (by norm_num)
theorem B2116589 : Blo 1174404 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B2509805 : Blo 1174404 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B1321969 : Blo 1174404 1321969 := bbase (se 2 (by rfl) ⟨495738, by rfl⟩ : syracuseStep 1321969 = 991477) (by norm_num)
theorem B1764341 : Blo 1174404 1764341 := bbase (se 5 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 1764341 = 165407) (by norm_num)
theorem B1764365 : Blo 1174404 1764365 := bbase (se 3 (by rfl) ⟨330818, by rfl⟩ : syracuseStep 1764365 = 661637) (by norm_num)
theorem B1322005 : Blo 1174404 1322005 := bbase (se 6 (by rfl) ⟨30984, by rfl⟩ : syracuseStep 1322005 = 61969) (by norm_num)
theorem B2231317 : Blo 1174404 2231317 := bbase (se 6 (by rfl) ⟨52296, by rfl⟩ : syracuseStep 2231317 = 104593) (by norm_num)
theorem B1764389 : Blo 1174404 1764389 := bbase (se 4 (by rfl) ⟨165411, by rfl⟩ : syracuseStep 1764389 = 330823) (by norm_num)
theorem B2976821 : Blo 1174404 2976821 := bbase (se 5 (by rfl) ⟨139538, by rfl⟩ : syracuseStep 2976821 = 279077) (by norm_num)
theorem B1322041 : Blo 1174404 1322041 := bbase (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) (by norm_num)
theorem B1764413 : Blo 1174404 1764413 := bbase (se 3 (by rfl) ⟨330827, by rfl⟩ : syracuseStep 1764413 = 661655) (by norm_num)
theorem B1764437 : Blo 1174404 1764437 := bbase (se 8 (by rfl) ⟨10338, by rfl⟩ : syracuseStep 1764437 = 20677) (by norm_num)
theorem B1322077 : Blo 1174404 1322077 := bbase (se 3 (by rfl) ⟨247889, by rfl⟩ : syracuseStep 1322077 = 495779) (by norm_num)
theorem B1764461 : Blo 1174404 1764461 := bbase (se 3 (by rfl) ⟨330836, by rfl⟩ : syracuseStep 1764461 = 661673) (by norm_num)
theorem B1322113 : Blo 1174404 1322113 := bbase (se 2 (by rfl) ⟨495792, by rfl⟩ : syracuseStep 1322113 = 991585) (by norm_num)
theorem B1764485 : Blo 1174404 1764485 := bbase (se 4 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 1764485 = 330841) (by norm_num)
theorem B3763349 : Blo 1174404 3763349 := bbase (se 6 (by rfl) ⟨88203, by rfl⟩ : syracuseStep 3763349 = 176407) (by norm_num)
theorem B1764509 : Blo 1174404 1764509 := bbase (se 3 (by rfl) ⟨330845, by rfl⟩ : syracuseStep 1764509 = 661691) (by norm_num)
theorem B1322149 : Blo 1174404 1322149 := bbase (se 4 (by rfl) ⟨123951, by rfl⟩ : syracuseStep 1322149 = 247903) (by norm_num)
theorem B1764533 : Blo 1174404 1764533 := bbase (se 5 (by rfl) ⟨82712, by rfl⟩ : syracuseStep 1764533 = 165425) (by norm_num)
theorem B1322185 : Blo 1174404 1322185 := bbase (se 2 (by rfl) ⟨495819, by rfl⟩ : syracuseStep 1322185 = 991639) (by norm_num)
theorem B1674445 : Blo 1174404 1674445 := bbase (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) (by norm_num)
theorem B1764557 : Blo 1174404 1764557 := bbase (se 3 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 1764557 = 661709) (by norm_num)
theorem B1764581 : Blo 1174404 1764581 := bbase (se 4 (by rfl) ⟨165429, by rfl⟩ : syracuseStep 1764581 = 330859) (by norm_num)
theorem B1322221 : Blo 1174404 1322221 := bbase (se 3 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 1322221 = 495833) (by norm_num)
theorem B2977013 : Blo 1174404 2977013 := bbase (se 5 (by rfl) ⟨139547, by rfl⟩ : syracuseStep 2977013 = 279095) (by norm_num)
theorem B5729525 : Blo 1174404 5729525 := bbase (se 5 (by rfl) ⟨268571, by rfl⟩ : syracuseStep 5729525 = 537143) (by norm_num)
theorem B1764605 : Blo 1174404 1764605 := bbase (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) (by norm_num)
theorem B1322257 : Blo 1174404 1322257 := bbase (se 2 (by rfl) ⟨495846, by rfl⟩ : syracuseStep 1322257 = 991693) (by norm_num)
theorem B1322293 : Blo 1174404 1322293 := bbase (se 5 (by rfl) ⟨61982, by rfl⟩ : syracuseStep 1322293 = 123965) (by norm_num)
theorem B2231621 : Blo 1174404 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B4828501 : Blo 1174404 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B1322329 : Blo 1174404 1322329 := bbase (se 2 (by rfl) ⟨495873, by rfl⟩ : syracuseStep 1322329 = 991747) (by norm_num)
theorem B2116957 : Blo 1174404 2116957 := bbase (se 3 (by rfl) ⟨396929, by rfl⟩ : syracuseStep 2116957 = 793859) (by norm_num)
theorem B1322365 : Blo 1174404 1322365 := bbase (se 3 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 1322365 = 495887) (by norm_num)
theorem B3968405 : Blo 1174404 3968405 := bbase (se 6 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 3968405 = 186019) (by norm_num)
theorem B1322401 : Blo 1174404 1322401 := bbase (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) (by norm_num)
theorem B1412525 : Blo 1174404 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B1322437 : Blo 1174404 1322437 := bbase (se 4 (by rfl) ⟨123978, by rfl⟩ : syracuseStep 1322437 = 247957) (by norm_num)
theorem B2207197 : Blo 1174404 2207197 := bbase (se 3 (by rfl) ⟨413849, by rfl⟩ : syracuseStep 2207197 = 827699) (by norm_num)
theorem B1322473 : Blo 1174404 1322473 := bbase (se 2 (by rfl) ⟨495927, by rfl⟩ : syracuseStep 1322473 = 991855) (by norm_num)
theorem B1609205 : Blo 1174404 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B3575285 : Blo 1174404 3575285 := bbase (se 5 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 3575285 = 335183) (by norm_num)
theorem B1412597 : Blo 1174404 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B1322509 : Blo 1174404 1322509 := bbase (se 3 (by rfl) ⟨247970, by rfl⟩ : syracuseStep 1322509 = 495941) (by norm_num)
theorem B1322545 : Blo 1174404 1322545 := bbase (se 2 (by rfl) ⟨495954, by rfl⟩ : syracuseStep 1322545 = 991909) (by norm_num)
theorem B2977357 : Blo 1174404 2977357 := bbase (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) (by norm_num)
theorem B1322581 : Blo 1174404 1322581 := bbase (se 8 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 1322581 = 15499) (by norm_num)
theorem B1486441 : Blo 1174404 1486441 := bbase (se 2 (by rfl) ⟨557415, by rfl⟩ : syracuseStep 1486441 = 1114831) (by norm_num)
theorem B1322617 : Blo 1174404 1322617 := bbase (se 2 (by rfl) ⟨495981, by rfl⟩ : syracuseStep 1322617 = 991963) (by norm_num)
theorem B1322653 : Blo 1174404 1322653 := bbase (se 3 (by rfl) ⟨247997, by rfl⟩ : syracuseStep 1322653 = 495995) (by norm_num)
theorem B2977469 : Blo 1174404 2977469 := bbase (se 3 (by rfl) ⟨558275, by rfl⟩ : syracuseStep 2977469 = 1116551) (by norm_num)
theorem B1322689 : Blo 1174404 1322689 := bbase (se 2 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 1322689 = 992017) (by norm_num)
theorem B1322725 : Blo 1174404 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B1322761 : Blo 1174404 1322761 := bbase (se 2 (by rfl) ⟨496035, by rfl⟩ : syracuseStep 1322761 = 992071) (by norm_num)
theorem B1486613 : Blo 1174404 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B1412905 : Blo 1174404 1412905 := bbase (se 2 (by rfl) ⟨529839, by rfl⟩ : syracuseStep 1412905 = 1059679) (by norm_num)
theorem B1322797 : Blo 1174404 1322797 := bbase (se 3 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 1322797 = 496049) (by norm_num)
theorem B3968837 : Blo 1174404 3968837 := bbase (se 4 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 3968837 = 744157) (by norm_num)
theorem B1486669 : Blo 1174404 1486669 := bbase (se 3 (by rfl) ⟨278750, by rfl⟩ : syracuseStep 1486669 = 557501) (by norm_num)
theorem B2510669 : Blo 1174404 2510669 := bbase (se 3 (by rfl) ⟨470750, by rfl⟩ : syracuseStep 2510669 = 941501) (by norm_num)
theorem B1322833 : Blo 1174404 1322833 := bbase (se 2 (by rfl) ⟨496062, by rfl⟩ : syracuseStep 1322833 = 992125) (by norm_num)
theorem B1322869 : Blo 1174404 1322869 := bbase (se 5 (by rfl) ⟨62009, by rfl⟩ : syracuseStep 1322869 = 124019) (by norm_num)
theorem B2977661 : Blo 1174404 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B1322905 : Blo 1174404 1322905 := bbase (se 2 (by rfl) ⟨496089, by rfl⟩ : syracuseStep 1322905 = 992179) (by norm_num)
theorem B1486765 : Blo 1174404 1486765 := bbase (se 3 (by rfl) ⟨278768, by rfl⟩ : syracuseStep 1486765 = 557537) (by norm_num)
theorem B1322941 : Blo 1174404 1322941 := bbase (se 3 (by rfl) ⟨248051, by rfl⟩ : syracuseStep 1322941 = 496103) (by norm_num)
theorem B3346373 : Blo 1174404 3346373 := bbase (se 4 (by rfl) ⟨313722, by rfl⟩ : syracuseStep 3346373 = 627445) (by norm_num)
theorem B1413073 : Blo 1174404 1413073 := bbase (se 2 (by rfl) ⟨529902, by rfl⟩ : syracuseStep 1413073 = 1059805) (by norm_num)
theorem B2510813 : Blo 1174404 2510813 := bbase (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) (by norm_num)
theorem B1322977 : Blo 1174404 1322977 := bbase (se 2 (by rfl) ⟨496116, by rfl⟩ : syracuseStep 1322977 = 992233) (by norm_num)
theorem B6688757 : Blo 1174404 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1413121 : Blo 1174404 1413121 := bbase (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) (by norm_num)
theorem B1323013 : Blo 1174404 1323013 := bbase (se 4 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 1323013 = 248065) (by norm_num)
theorem B1323049 : Blo 1174404 1323049 := bbase (se 2 (by rfl) ⟨496143, by rfl⟩ : syracuseStep 1323049 = 992287) (by norm_num)
theorem B2232373 : Blo 1174404 2232373 := bbase (se 5 (by rfl) ⟨104642, by rfl⟩ : syracuseStep 2232373 = 209285) (by norm_num)
theorem B1323085 : Blo 1174404 1323085 := bbase (se 3 (by rfl) ⟨248078, by rfl⟩ : syracuseStep 1323085 = 496157) (by norm_num)
theorem B4460629 : Blo 1174404 4460629 := bbase (se 8 (by rfl) ⟨26136, by rfl⟩ : syracuseStep 4460629 = 52273) (by norm_num)
theorem B1486937 : Blo 1174404 1486937 := bbase (se 2 (by rfl) ⟨557601, by rfl⟩ : syracuseStep 1486937 = 1115203) (by norm_num)
theorem B1413217 : Blo 1174404 1413217 := bbase (se 2 (by rfl) ⟨529956, by rfl⟩ : syracuseStep 1413217 = 1059913) (by norm_num)
theorem B1192045 : Blo 1174404 1192045 := bbase (se 3 (by rfl) ⟨223508, by rfl⟩ : syracuseStep 1192045 = 447017) (by norm_num)
theorem B1323121 : Blo 1174404 1323121 := bbase (se 2 (by rfl) ⟨496170, by rfl⟩ : syracuseStep 1323121 = 992341) (by norm_num)
theorem B2117749 : Blo 1174404 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B2117765 : Blo 1174404 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B1486993 : Blo 1174404 1486993 := bbase (se 2 (by rfl) ⟨557622, by rfl⟩ : syracuseStep 1486993 = 1115245) (by norm_num)
theorem B1323157 : Blo 1174404 1323157 := bbase (se 6 (by rfl) ⟨31011, by rfl⟩ : syracuseStep 1323157 = 62023) (by norm_num)
theorem B4296853 : Blo 1174404 4296853 := bbase (se 6 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 4296853 = 201415) (by norm_num)
theorem B1323193 : Blo 1174404 1323193 := bbase (se 2 (by rfl) ⟨496197, by rfl⟩ : syracuseStep 1323193 = 992395) (by norm_num)
theorem B1241285 : Blo 1174404 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B2232517 : Blo 1174404 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B4526293 : Blo 1174404 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B1323229 : Blo 1174404 1323229 := bbase (se 3 (by rfl) ⟨248105, by rfl⟩ : syracuseStep 1323229 = 496211) (by norm_num)
theorem B5951717 : Blo 1174404 5951717 := bbase (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) (by norm_num)
theorem B1487089 : Blo 1174404 1487089 := bbase (se 2 (by rfl) ⟨557658, by rfl⟩ : syracuseStep 1487089 = 1115317) (by norm_num)
theorem B3969269 : Blo 1174404 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B1323265 : Blo 1174404 1323265 := bbase (se 2 (by rfl) ⟨496224, by rfl⟩ : syracuseStep 1323265 = 992449) (by norm_num)
theorem B1323301 : Blo 1174404 1323301 := bbase (se 4 (by rfl) ⟨124059, by rfl⟩ : syracuseStep 1323301 = 248119) (by norm_num)
theorem B1764245 : Blo 1174404 1764245 := bbase (se 6 (by rfl) ⟨41349, by rfl⟩ : syracuseStep 1764245 = 82699) (by norm_num)
theorem B1323337 : Blo 1174404 1323337 := bbase (se 2 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 1323337 = 992503) (by norm_num)
theorem B85766485 : Blo 1174404 85766485 := bbase (se 10 (by rfl) ⟨125634, by rfl⟩ : syracuseStep 85766485 = 251269) (by norm_num)
theorem B2117981 : Blo 1174404 2117981 := bbase (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) (by norm_num)
theorem B2232677 : Blo 1174404 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B1323373 : Blo 1174404 1323373 := bbase (se 3 (by rfl) ⟨248132, by rfl⟩ : syracuseStep 1323373 = 496265) (by norm_num)
theorem B4460933 : Blo 1174404 4460933 := bbase (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) (by norm_num)
theorem B1323409 : Blo 1174404 1323409 := bbase (se 2 (by rfl) ⟨496278, by rfl⟩ : syracuseStep 1323409 = 992557) (by norm_num)
theorem B1487261 : Blo 1174404 1487261 := bbase (se 3 (by rfl) ⟨278861, by rfl⟩ : syracuseStep 1487261 = 557723) (by norm_num)
theorem B1323445 : Blo 1174404 1323445 := bbase (se 5 (by rfl) ⟨62036, by rfl⟩ : syracuseStep 1323445 = 124073) (by norm_num)
theorem B1487317 : Blo 1174404 1487317 := bbase (se 7 (by rfl) ⟨17429, by rfl⟩ : syracuseStep 1487317 = 34859) (by norm_num)
theorem B2118125 : Blo 1174404 2118125 := bbase (se 3 (by rfl) ⟨397148, by rfl⟩ : syracuseStep 2118125 = 794297) (by norm_num)
theorem B2232821 : Blo 1174404 2232821 := bbase (se 5 (by rfl) ⟨104663, by rfl⟩ : syracuseStep 2232821 = 209327) (by norm_num)
theorem B4018693 : Blo 1174404 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B2642453 : Blo 1174404 2642453 := bbase (se 6 (by rfl) ⟨61932, by rfl⟩ : syracuseStep 2642453 = 123865) (by norm_num)
theorem B1487413 : Blo 1174404 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B1339993 : Blo 1174404 1339993 := bbase (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) (by norm_num)
theorem B2642525 : Blo 1174404 2642525 := bbase (se 3 (by rfl) ⟨495473, by rfl⟩ : syracuseStep 2642525 = 990947) (by norm_num)
theorem B3347045 : Blo 1174404 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B2642597 : Blo 1174404 2642597 := bbase (se 4 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 2642597 = 495487) (by norm_num)
theorem B3969701 : Blo 1174404 3969701 := bbase (se 4 (by rfl) ⟨372159, by rfl⟩ : syracuseStep 3969701 = 744319) (by norm_num)
theorem B2511557 : Blo 1174404 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B1487585 : Blo 1174404 1487585 := bbase (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) (by norm_num)
theorem B2642669 : Blo 1174404 2642669 := bbase (se 3 (by rfl) ⟨495500, by rfl⟩ : syracuseStep 2642669 = 991001) (by norm_num)
theorem B2233109 : Blo 1174404 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1487641 : Blo 1174404 1487641 := bbase (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) (by norm_num)
theorem B2642741 : Blo 1174404 2642741 := bbase (se 5 (by rfl) ⟨123878, by rfl⟩ : syracuseStep 2642741 = 247757) (by norm_num)
theorem B1487737 : Blo 1174404 1487737 := bbase (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) (by norm_num)
theorem B2642813 : Blo 1174404 2642813 := bbase (se 3 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 2642813 = 991055) (by norm_num)
theorem B2233261 : Blo 1174404 2233261 := bbase (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) (by norm_num)
theorem B2642885 : Blo 1174404 2642885 := bbase (se 4 (by rfl) ⟨247770, by rfl⟩ : syracuseStep 2642885 = 495541) (by norm_num)
theorem B2642957 : Blo 1174404 2642957 := bbase (se 3 (by rfl) ⟨495554, by rfl⟩ : syracuseStep 2642957 = 991109) (by norm_num)
theorem B3347477 : Blo 1174404 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B4830245 : Blo 1174404 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B1487909 : Blo 1174404 1487909 := bbase (se 4 (by rfl) ⟨139491, by rfl⟩ : syracuseStep 1487909 = 278983) (by norm_num)
theorem B2643029 : Blo 1174404 2643029 := bbase (se 8 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 2643029 = 30973) (by norm_num)
theorem B3970133 : Blo 1174404 3970133 := bbase (se 8 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 3970133 = 46525) (by norm_num)
theorem B1487965 : Blo 1174404 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B2643101 : Blo 1174404 2643101 := bbase (se 3 (by rfl) ⟨495581, by rfl⟩ : syracuseStep 2643101 = 991163) (by norm_num)
theorem B2823349 : Blo 1174404 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B1488061 : Blo 1174404 1488061 := bbase (se 3 (by rfl) ⟨279011, by rfl⟩ : syracuseStep 1488061 = 558023) (by norm_num)
theorem B2118845 : Blo 1174404 2118845 := bbase (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) (by norm_num)
theorem B2643173 : Blo 1174404 2643173 := bbase (se 4 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 2643173 = 495595) (by norm_num)
theorem B2643245 : Blo 1174404 2643245 := bbase (se 3 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 2643245 = 991217) (by norm_num)
theorem B1488233 : Blo 1174404 1488233 := bbase (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) (by norm_num)
theorem B2643317 : Blo 1174404 2643317 := bbase (se 5 (by rfl) ⟨123905, by rfl⟩ : syracuseStep 2643317 = 247811) (by norm_num)
theorem B5019029 : Blo 1174404 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B5092757 : Blo 1174404 5092757 := bbase (se 6 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 5092757 = 238723) (by norm_num)
theorem B1488289 : Blo 1174404 1488289 := bbase (se 2 (by rfl) ⟨558108, by rfl⟩ : syracuseStep 1488289 = 1116217) (by norm_num)
theorem B2512309 : Blo 1174404 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B2643389 : Blo 1174404 2643389 := bbase (se 3 (by rfl) ⟨495635, by rfl⟩ : syracuseStep 2643389 = 991271) (by norm_num)
theorem B2119133 : Blo 1174404 2119133 := bbase (se 3 (by rfl) ⟨397337, by rfl⟩ : syracuseStep 2119133 = 794675) (by norm_num)
theorem B5953013 : Blo 1174404 5953013 := bbase (se 5 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 5953013 = 558095) (by norm_num)
theorem B1488385 : Blo 1174404 1488385 := bbase (se 2 (by rfl) ⟨558144, by rfl⟩ : syracuseStep 1488385 = 1116289) (by norm_num)
theorem B2643461 : Blo 1174404 2643461 := bbase (se 4 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 2643461 = 495649) (by norm_num)
theorem B7534133 : Blo 1174404 7534133 := bbase (se 5 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 7534133 = 706325) (by norm_num)
theorem B4355653 : Blo 1174404 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B2512453 : Blo 1174404 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B2643533 : Blo 1174404 2643533 := bbase (se 3 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 2643533 = 991325) (by norm_num)
theorem B1881701 : Blo 1174404 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B2545277 : Blo 1174404 2545277 := bbase (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) (by norm_num)
theorem B2643605 : Blo 1174404 2643605 := bbase (se 6 (by rfl) ⟨61959, by rfl⟩ : syracuseStep 2643605 = 123919) (by norm_num)
theorem B6698645 : Blo 1174404 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B1488557 : Blo 1174404 1488557 := bbase (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) (by norm_num)
theorem B2643677 : Blo 1174404 2643677 := bbase (se 3 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 2643677 = 991379) (by norm_num)
theorem B1488613 : Blo 1174404 1488613 := bbase (se 4 (by rfl) ⟨139557, by rfl⟩ : syracuseStep 1488613 = 279115) (by norm_num)
theorem B3348229 : Blo 1174404 3348229 := bbase (se 4 (by rfl) ⟨313896, by rfl⟩ : syracuseStep 3348229 = 627793) (by norm_num)
theorem B1881893 : Blo 1174404 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B2643749 : Blo 1174404 2643749 := bbase (se 4 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 2643749 = 495703) (by norm_num)
theorem B1488709 : Blo 1174404 1488709 := bbase (se 4 (by rfl) ⟨139566, by rfl⟩ : syracuseStep 1488709 = 279133) (by norm_num)
theorem B3766117 : Blo 1174404 3766117 := bbase (se 4 (by rfl) ⟨353073, by rfl⟩ : syracuseStep 3766117 = 706147) (by norm_num)
theorem B2643821 : Blo 1174404 2643821 := bbase (se 3 (by rfl) ⟨495716, by rfl⟩ : syracuseStep 2643821 = 991433) (by norm_num)
theorem B6027173 : Blo 1174404 6027173 := bbase (se 4 (by rfl) ⟨565047, by rfl⟩ : syracuseStep 6027173 = 1130095) (by norm_num)
theorem B2643893 : Blo 1174404 2643893 := bbase (se 5 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 2643893 = 247865) (by norm_num)
theorem B1488881 : Blo 1174404 1488881 := bbase (se 2 (by rfl) ⟨558330, by rfl⟩ : syracuseStep 1488881 = 1116661) (by norm_num)
theorem B2643965 : Blo 1174404 2643965 := bbase (se 3 (by rfl) ⟨495743, by rfl⟩ : syracuseStep 2643965 = 991487) (by norm_num)
theorem B2414645 : Blo 1174404 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B2644037 : Blo 1174404 2644037 := bbase (se 4 (by rfl) ⟨247878, by rfl⟩ : syracuseStep 2644037 = 495757) (by norm_num)
theorem B12064853 : Blo 1174404 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B2824301 : Blo 1174404 2824301 := bbase (se 3 (by rfl) ⟨529556, by rfl⟩ : syracuseStep 2824301 = 1059113) (by norm_num)
theorem B1587317 : Blo 1174404 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B2644109 : Blo 1174404 2644109 := bbase (se 3 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 2644109 = 991541) (by norm_num)
theorem B2824357 : Blo 1174404 2824357 := bbase (se 4 (by rfl) ⟨264783, by rfl⟩ : syracuseStep 2824357 = 529567) (by norm_num)
theorem B2644181 : Blo 1174404 2644181 := bbase (se 7 (by rfl) ⟨30986, by rfl⟩ : syracuseStep 2644181 = 61973) (by norm_num)
theorem B8583413 : Blo 1174404 8583413 := bbase (se 5 (by rfl) ⟨402347, by rfl⟩ : syracuseStep 8583413 = 804695) (by norm_num)
theorem B2644253 : Blo 1174404 2644253 := bbase (se 3 (by rfl) ⟨495797, by rfl⟩ : syracuseStep 2644253 = 991595) (by norm_num)
theorem B2644325 : Blo 1174404 2644325 := bbase (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) (by norm_num)
theorem B11295125 : Blo 1174404 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B2644397 : Blo 1174404 2644397 := bbase (se 3 (by rfl) ⟨495824, by rfl⟩ : syracuseStep 2644397 = 991649) (by norm_num)
theorem B4463045 : Blo 1174404 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B2644469 : Blo 1174404 2644469 := bbase (se 5 (by rfl) ⟨123959, by rfl⟩ : syracuseStep 2644469 = 247919) (by norm_num)
theorem B2824733 : Blo 1174404 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B2644541 : Blo 1174404 2644541 := bbase (se 3 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 2644541 = 991703) (by norm_num)
theorem B2382461 : Blo 1174404 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B2644613 : Blo 1174404 2644613 := bbase (se 4 (by rfl) ⟨247932, by rfl⟩ : syracuseStep 2644613 = 495865) (by norm_num)
theorem B2644685 : Blo 1174404 2644685 := bbase (se 3 (by rfl) ⟨495878, by rfl⟩ : syracuseStep 2644685 = 991757) (by norm_num)
theorem B8583893 : Blo 1174404 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B4463333 : Blo 1174404 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B3963653 : Blo 1174404 3963653 := bbase (se 4 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 3963653 = 743185) (by norm_num)
theorem B5954309 : Blo 1174404 5954309 := bbase (se 4 (by rfl) ⟨558216, by rfl⟩ : syracuseStep 5954309 = 1116433) (by norm_num)
theorem B2824973 : Blo 1174404 2824973 := bbase (se 3 (by rfl) ⟨529682, by rfl⟩ : syracuseStep 2824973 = 1059365) (by norm_num)
theorem B2644757 : Blo 1174404 2644757 := bbase (se 6 (by rfl) ⟨61986, by rfl⟩ : syracuseStep 2644757 = 123973) (by norm_num)
theorem B2448181 : Blo 1174404 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B32168789 : Blo 1174404 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B2644829 : Blo 1174404 2644829 := bbase (se 3 (by rfl) ⟨495905, by rfl⟩ : syracuseStep 2644829 = 991811) (by norm_num)
theorem B2644901 : Blo 1174404 2644901 := bbase (se 4 (by rfl) ⟨247959, by rfl⟩ : syracuseStep 2644901 = 495919) (by norm_num)
theorem B2644973 : Blo 1174404 2644973 := bbase (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) (by norm_num)
theorem B3013669 : Blo 1174404 3013669 := bbase (se 4 (by rfl) ⟨282531, by rfl⟩ : syracuseStep 3013669 = 565063) (by norm_num)
theorem B2645045 : Blo 1174404 2645045 := bbase (se 5 (by rfl) ⟨123986, by rfl⟩ : syracuseStep 2645045 = 247973) (by norm_num)
theorem B2645117 : Blo 1174404 2645117 := bbase (se 3 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 2645117 = 991919) (by norm_num)
theorem B5020805 : Blo 1174404 5020805 := bbase (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) (by norm_num)
theorem B2972821 : Blo 1174404 2972821 := bbase (se 6 (by rfl) ⟨69675, by rfl⟩ : syracuseStep 2972821 = 139351) (by norm_num)
theorem B5946533 : Blo 1174404 5946533 := bbase (se 4 (by rfl) ⟨557487, by rfl⟩ : syracuseStep 5946533 = 1114975) (by norm_num)
theorem B3964085 : Blo 1174404 3964085 := bbase (se 5 (by rfl) ⟨185816, by rfl⟩ : syracuseStep 3964085 = 371633) (by norm_num)
theorem B5364917 : Blo 1174404 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B2645189 : Blo 1174404 2645189 := bbase (se 4 (by rfl) ⟨247986, by rfl⟩ : syracuseStep 2645189 = 495973) (by norm_num)
theorem B1883341 : Blo 1174404 1883341 := bbase (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) (by norm_num)
theorem B2972933 : Blo 1174404 2972933 := bbase (se 4 (by rfl) ⟨278712, by rfl⟩ : syracuseStep 2972933 = 557425) (by norm_num)
theorem B2645261 : Blo 1174404 2645261 := bbase (se 3 (by rfl) ⟨495986, by rfl⟩ : syracuseStep 2645261 = 991973) (by norm_num)
theorem B9534773 : Blo 1174404 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B2645333 : Blo 1174404 2645333 := bbase (se 11 (by rfl) ⟨1937, by rfl⟩ : syracuseStep 2645333 = 3875) (by norm_num)
theorem B1981813 : Blo 1174404 1981813 := bbase (se 5 (by rfl) ⟨92897, by rfl⟩ : syracuseStep 1981813 = 185795) (by norm_num)
theorem B2645405 : Blo 1174404 2645405 := bbase (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) (by norm_num)
theorem B2973125 : Blo 1174404 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1981901 : Blo 1174404 1981901 := bbase (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) (by norm_num)
theorem B2645477 : Blo 1174404 2645477 := bbase (se 4 (by rfl) ⟨248013, by rfl⟩ : syracuseStep 2645477 = 496027) (by norm_num)
theorem B1359385 : Blo 1174404 1359385 := bbase (se 2 (by rfl) ⟨509769, by rfl⟩ : syracuseStep 1359385 = 1019539) (by norm_num)
theorem B2645549 : Blo 1174404 2645549 := bbase (se 3 (by rfl) ⟨496040, by rfl⟩ : syracuseStep 2645549 = 992081) (by norm_num)
theorem B2039357 : Blo 1174404 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B1982029 : Blo 1174404 1982029 := bbase (se 3 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 1982029 = 743261) (by norm_num)
theorem B3964517 : Blo 1174404 3964517 := bbase (se 4 (by rfl) ⟨371673, by rfl⟩ : syracuseStep 3964517 = 743347) (by norm_num)
theorem B1588853 : Blo 1174404 1588853 := bbase (se 5 (by rfl) ⟨74477, by rfl⟩ : syracuseStep 1588853 = 148955) (by norm_num)
theorem B2645621 : Blo 1174404 2645621 := bbase (se 5 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 2645621 = 248027) (by norm_num)
theorem B1982117 : Blo 1174404 1982117 := bbase (se 4 (by rfl) ⟨185823, by rfl⟩ : syracuseStep 1982117 = 371647) (by norm_num)
theorem B2719397 : Blo 1174404 2719397 := bbase (se 4 (by rfl) ⟨254943, by rfl⟩ : syracuseStep 2719397 = 509887) (by norm_num)
theorem B2645693 : Blo 1174404 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B16096981 : Blo 1174404 16096981 := bbase (se 7 (by rfl) ⟨188636, by rfl⟩ : syracuseStep 16096981 = 377273) (by norm_num)
theorem B2645765 : Blo 1174404 2645765 := bbase (se 4 (by rfl) ⟨248040, by rfl⟩ : syracuseStep 2645765 = 496081) (by norm_num)
theorem B2973469 : Blo 1174404 2973469 := bbase (se 3 (by rfl) ⟨557525, by rfl⟩ : syracuseStep 2973469 = 1115051) (by norm_num)
theorem B1982245 : Blo 1174404 1982245 := bbase (se 4 (by rfl) ⟨185835, by rfl⟩ : syracuseStep 1982245 = 371671) (by norm_num)
theorem B7143221 : Blo 1174404 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B2645837 : Blo 1174404 2645837 := bbase (se 3 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 2645837 = 992189) (by norm_num)
theorem B1982333 : Blo 1174404 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B4464517 : Blo 1174404 4464517 := bbase (se 4 (by rfl) ⟨418548, by rfl⟩ : syracuseStep 4464517 = 837097) (by norm_num)
theorem B2973581 : Blo 1174404 2973581 := bbase (se 3 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 2973581 = 1115093) (by norm_num)
theorem B2645909 : Blo 1174404 2645909 := bbase (se 6 (by rfl) ⟨62013, by rfl⟩ : syracuseStep 2645909 = 124027) (by norm_num)
theorem B2645981 : Blo 1174404 2645981 := bbase (se 3 (by rfl) ⟨496121, by rfl⟩ : syracuseStep 2645981 = 992243) (by norm_num)
theorem B1982461 : Blo 1174404 1982461 := bbase (se 3 (by rfl) ⟨371711, by rfl⟩ : syracuseStep 1982461 = 743423) (by norm_num)
theorem B1884161 : Blo 1174404 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B1982515 : Blo 1174404 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B5947505 : Blo 1174404 5947505 := bstep (se 2 (by rfl) ⟨2230314, by rfl⟩ : syracuseStep 5947505 = 4460629) B4460629
theorem B1785971 : Blo 1174404 1785971 := bstep (se 1 (by rfl) ⟨1339478, by rfl⟩ : syracuseStep 1785971 = 2678957) B2678957
theorem B1884289 : Blo 1174404 1884289 := bstep (se 2 (by rfl) ⟨706608, by rfl⟩ : syracuseStep 1884289 = 1413217) B1413217
theorem B1589393 : Blo 1174404 1589393 := bstep (se 2 (by rfl) ⟨596022, by rfl⟩ : syracuseStep 1589393 = 1192045) B1192045
theorem B2646161 : Blo 1174404 2646161 := bstep (se 2 (by rfl) ⟨992310, by rfl⟩ : syracuseStep 2646161 = 1984621) B1984621
theorem B2646179 : Blo 1174404 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B1982657 : Blo 1174404 1982657 := bstep (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) B1486993
theorem B16072901 : Blo 1174404 16072901 := bstep (se 4 (by rfl) ⟨1506834, by rfl⟩ : syracuseStep 16072901 = 3013669) B3013669
theorem B2973905 : Blo 1174404 2973905 := bstep (se 2 (by rfl) ⟨1115214, by rfl⟩ : syracuseStep 2973905 = 2230429) B2230429
theorem B3965165 : Blo 1174404 3965165 := bstep (se 3 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 3965165 = 1486937) B1486937
theorem B2973955 : Blo 1174404 2973955 := bstep (se 1 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 2973955 = 4460933) B4460933
theorem B3965219 : Blo 1174404 3965219 := bstep (se 1 (by rfl) ⟨2973914, by rfl⟩ : syracuseStep 3965219 = 5947829) B5947829
theorem B1982785 : Blo 1174404 1982785 := bstep (se 2 (by rfl) ⟨743544, by rfl⟩ : syracuseStep 1982785 = 1487089) B1487089
theorem B1761617 : Blo 1174404 1761617 := bstep (se 2 (by rfl) ⟨660606, by rfl⟩ : syracuseStep 1761617 = 1321213) B1321213
theorem B1761635 : Blo 1174404 1761635 := bstep (se 1 (by rfl) ⟨1321226, by rfl⟩ : syracuseStep 1761635 = 2642453) B2642453
theorem B1982819 : Blo 1174404 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B1761665 : Blo 1174404 1761665 := bstep (se 2 (by rfl) ⟨660624, by rfl⟩ : syracuseStep 1761665 = 1321249) B1321249
theorem B3768707 : Blo 1174404 3768707 := bstep (se 1 (by rfl) ⟨2826530, by rfl⟩ : syracuseStep 3768707 = 5653061) B5653061
theorem B2974097 : Blo 1174404 2974097 := bstep (se 2 (by rfl) ⟨1115286, by rfl⟩ : syracuseStep 2974097 = 2230573) B2230573
theorem B1761683 : Blo 1174404 1761683 := bstep (se 1 (by rfl) ⟨1321262, by rfl⟩ : syracuseStep 1761683 = 2642525) B2642525
theorem B1761713 : Blo 1174404 1761713 := bstep (se 2 (by rfl) ⟨660642, by rfl⟩ : syracuseStep 1761713 = 1321285) B1321285
theorem B2646449 : Blo 1174404 2646449 := bstep (se 2 (by rfl) ⟨992418, by rfl⟩ : syracuseStep 2646449 = 1984837) B1984837
theorem B1761731 : Blo 1174404 1761731 := bstep (se 1 (by rfl) ⟨1321298, by rfl⟩ : syracuseStep 1761731 = 2642597) B2642597
theorem B2646467 : Blo 1174404 2646467 := bstep (se 1 (by rfl) ⟨1984850, by rfl⟩ : syracuseStep 2646467 = 3969701) B3969701
theorem B1761761 : Blo 1174404 1761761 := bstep (se 2 (by rfl) ⟨660660, by rfl⟩ : syracuseStep 1761761 = 1321321) B1321321
theorem B1982947 : Blo 1174404 1982947 := bstep (se 1 (by rfl) ⟨1487210, by rfl⟩ : syracuseStep 1982947 = 2974421) B2974421
theorem B8929763 : Blo 1174404 8929763 := bstep (se 1 (by rfl) ⟨6697322, by rfl⟩ : syracuseStep 8929763 = 13394645) B13394645
theorem B1761779 : Blo 1174404 1761779 := bstep (se 1 (by rfl) ⟨1321334, by rfl⟩ : syracuseStep 1761779 = 2642669) B2642669
theorem B3310093 : Blo 1174404 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B1761809 : Blo 1174404 1761809 := bstep (se 2 (by rfl) ⟨660678, by rfl⟩ : syracuseStep 1761809 = 1321357) B1321357
theorem B29000213 : Blo 1174404 29000213 := bstep (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) B1359385
theorem B1761827 : Blo 1174404 1761827 := bstep (se 1 (by rfl) ⟨1321370, by rfl⟩ : syracuseStep 1761827 = 2642741) B2642741
theorem B3965489 : Blo 1174404 3965489 := bstep (se 2 (by rfl) ⟨1487058, by rfl⟩ : syracuseStep 3965489 = 2974117) B2974117
theorem B1761857 : Blo 1174404 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B1761875 : Blo 1174404 1761875 := bstep (se 1 (by rfl) ⟨1321406, by rfl⟩ : syracuseStep 1761875 = 2642813) B2642813
theorem B1761905 : Blo 1174404 1761905 := bstep (se 2 (by rfl) ⟨660714, by rfl⟩ : syracuseStep 1761905 = 1321429) B1321429
theorem B1983089 : Blo 1174404 1983089 := bstep (se 2 (by rfl) ⟨743658, by rfl⟩ : syracuseStep 1983089 = 1487317) B1487317
theorem B1761923 : Blo 1174404 1761923 := bstep (se 1 (by rfl) ⟨1321442, by rfl⟩ : syracuseStep 1761923 = 2642885) B2642885
theorem B22889101 : Blo 1174404 22889101 := bstep (se 3 (by rfl) ⟨4291706, by rfl⟩ : syracuseStep 22889101 = 8583413) B8583413
theorem B1761953 : Blo 1174404 1761953 := bstep (se 2 (by rfl) ⟨660732, by rfl⟩ : syracuseStep 1761953 = 1321465) B1321465
theorem B5358257 : Blo 1174404 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B1761971 : Blo 1174404 1761971 := bstep (se 1 (by rfl) ⟨1321478, by rfl⟩ : syracuseStep 1761971 = 2642957) B2642957
theorem B3220163 : Blo 1174404 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B1762001 : Blo 1174404 1762001 := bstep (se 2 (by rfl) ⟨660750, by rfl⟩ : syracuseStep 1762001 = 1321501) B1321501
theorem B2646737 : Blo 1174404 2646737 := bstep (se 2 (by rfl) ⟨992526, by rfl⟩ : syracuseStep 2646737 = 1985053) B1985053
theorem B1762019 : Blo 1174404 1762019 := bstep (se 1 (by rfl) ⟨1321514, by rfl⟩ : syracuseStep 1762019 = 2643029) B2643029
theorem B3015395 : Blo 1174404 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B2646755 : Blo 1174404 2646755 := bstep (se 1 (by rfl) ⟨1985066, by rfl⟩ : syracuseStep 2646755 = 3970133) B3970133
theorem B1983217 : Blo 1174404 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B1762049 : Blo 1174404 1762049 := bstep (se 2 (by rfl) ⟨660768, by rfl⟩ : syracuseStep 1762049 = 1321537) B1321537
theorem B1762067 : Blo 1174404 1762067 := bstep (se 1 (by rfl) ⟨1321550, by rfl⟩ : syracuseStep 1762067 = 2643101) B2643101
theorem B1983251 : Blo 1174404 1983251 := bstep (se 1 (by rfl) ⟨1487438, by rfl⟩ : syracuseStep 1983251 = 2974877) B2974877
theorem B1762097 : Blo 1174404 1762097 := bstep (se 2 (by rfl) ⟨660786, by rfl⟩ : syracuseStep 1762097 = 1321573) B1321573
theorem B1762115 : Blo 1174404 1762115 := bstep (se 1 (by rfl) ⟨1321586, by rfl⟩ : syracuseStep 1762115 = 2643173) B2643173
theorem B1762145 : Blo 1174404 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B1762163 : Blo 1174404 1762163 := bstep (se 1 (by rfl) ⟨1321622, by rfl⟩ : syracuseStep 1762163 = 2643245) B2643245
theorem B1762193 : Blo 1174404 1762193 := bstep (se 2 (by rfl) ⟨660822, by rfl⟩ : syracuseStep 1762193 = 1321645) B1321645
theorem B1983379 : Blo 1174404 1983379 := bstep (se 1 (by rfl) ⟨1487534, by rfl⟩ : syracuseStep 1983379 = 2975069) B2975069
theorem B1762211 : Blo 1174404 1762211 := bstep (se 1 (by rfl) ⟨1321658, by rfl⟩ : syracuseStep 1762211 = 2643317) B2643317
theorem B1762241 : Blo 1174404 1762241 := bstep (se 2 (by rfl) ⟨660840, by rfl⟩ : syracuseStep 1762241 = 1321681) B1321681
theorem B3818435 : Blo 1174404 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B1762259 : Blo 1174404 1762259 := bstep (se 1 (by rfl) ⟨1321694, by rfl⟩ : syracuseStep 1762259 = 2643389) B2643389
theorem B1762289 : Blo 1174404 1762289 := bstep (se 2 (by rfl) ⟨660858, by rfl⟩ : syracuseStep 1762289 = 1321717) B1321717
theorem B1762307 : Blo 1174404 1762307 := bstep (se 1 (by rfl) ⟨1321730, by rfl⟩ : syracuseStep 1762307 = 2643461) B2643461
theorem B3572753 : Blo 1174404 3572753 := bstep (se 2 (by rfl) ⟨1339782, by rfl⟩ : syracuseStep 3572753 = 2679565) B2679565
theorem B1762337 : Blo 1174404 1762337 := bstep (se 2 (by rfl) ⟨660876, by rfl⟩ : syracuseStep 1762337 = 1321753) B1321753
theorem B1983521 : Blo 1174404 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B5022755 : Blo 1174404 5022755 := bstep (se 1 (by rfl) ⟨3767066, by rfl⟩ : syracuseStep 5022755 = 7534133) B7534133
theorem B1762355 : Blo 1174404 1762355 := bstep (se 1 (by rfl) ⟨1321766, by rfl⟩ : syracuseStep 1762355 = 2643533) B2643533
theorem B1254467 : Blo 1174404 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B3179587 : Blo 1174404 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B3966029 : Blo 1174404 3966029 := bstep (se 3 (by rfl) ⟨743630, by rfl⟩ : syracuseStep 3966029 = 1487261) B1487261
theorem B1762385 : Blo 1174404 1762385 := bstep (se 2 (by rfl) ⟨660894, by rfl⟩ : syracuseStep 1762385 = 1321789) B1321789
theorem B1762403 : Blo 1174404 1762403 := bstep (se 1 (by rfl) ⟨1321802, by rfl⟩ : syracuseStep 1762403 = 2643605) B2643605
theorem B4465763 : Blo 1174404 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B1672321 : Blo 1174404 1672321 := bstep (se 2 (by rfl) ⟨627120, by rfl⟩ : syracuseStep 1672321 = 1254241) B1254241
theorem B1762433 : Blo 1174404 1762433 := bstep (se 2 (by rfl) ⟨660912, by rfl⟩ : syracuseStep 1762433 = 1321825) B1321825
theorem B3966083 : Blo 1174404 3966083 := bstep (se 1 (by rfl) ⟨2974562, by rfl⟩ : syracuseStep 3966083 = 5949125) B5949125
theorem B1762451 : Blo 1174404 1762451 := bstep (se 1 (by rfl) ⟨1321838, by rfl⟩ : syracuseStep 1762451 = 2643677) B2643677
theorem B1983649 : Blo 1174404 1983649 := bstep (se 2 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 1983649 = 1487737) B1487737
theorem B1762481 : Blo 1174404 1762481 := bstep (se 2 (by rfl) ⟨660930, by rfl⟩ : syracuseStep 1762481 = 1321861) B1321861
theorem B6784177 : Blo 1174404 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B1762499 : Blo 1174404 1762499 := bstep (se 1 (by rfl) ⟨1321874, by rfl⟩ : syracuseStep 1762499 = 2643749) B2643749
theorem B1983683 : Blo 1174404 1983683 := bstep (se 1 (by rfl) ⟨1487762, by rfl⟩ : syracuseStep 1983683 = 2975525) B2975525
theorem B1672417 : Blo 1174404 1672417 := bstep (se 2 (by rfl) ⟨627156, by rfl⟩ : syracuseStep 1672417 = 1254313) B1254313
theorem B1762529 : Blo 1174404 1762529 := bstep (se 2 (by rfl) ⟨660948, by rfl⟩ : syracuseStep 1762529 = 1321897) B1321897
theorem B1762547 : Blo 1174404 1762547 := bstep (se 1 (by rfl) ⟨1321910, by rfl⟩ : syracuseStep 1762547 = 2643821) B2643821
theorem B1762577 : Blo 1174404 1762577 := bstep (se 2 (by rfl) ⟨660966, by rfl⟩ : syracuseStep 1762577 = 1321933) B1321933
theorem B1762595 : Blo 1174404 1762595 := bstep (se 1 (by rfl) ⟨1321946, by rfl⟩ : syracuseStep 1762595 = 2643893) B2643893
theorem B1762625 : Blo 1174404 1762625 := bstep (se 2 (by rfl) ⟨660984, by rfl⟩ : syracuseStep 1762625 = 1321969) B1321969
theorem B1983811 : Blo 1174404 1983811 := bstep (se 1 (by rfl) ⟨1487858, by rfl⟩ : syracuseStep 1983811 = 2975717) B2975717
theorem B1762643 : Blo 1174404 1762643 := bstep (se 1 (by rfl) ⟨1321982, by rfl⟩ : syracuseStep 1762643 = 2643965) B2643965
theorem B1762673 : Blo 1174404 1762673 := bstep (se 2 (by rfl) ⟨661002, by rfl⟩ : syracuseStep 1762673 = 1322005) B1322005
theorem B2975089 : Blo 1174404 2975089 := bstep (se 2 (by rfl) ⟨1115658, by rfl⟩ : syracuseStep 2975089 = 2231317) B2231317
theorem B13763953 : Blo 1174404 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B1762691 : Blo 1174404 1762691 := bstep (se 1 (by rfl) ⟨1322018, by rfl⟩ : syracuseStep 1762691 = 2644037) B2644037
theorem B3966353 : Blo 1174404 3966353 := bstep (se 2 (by rfl) ⟨1487382, by rfl⟩ : syracuseStep 3966353 = 2974765) B2974765
theorem B1762721 : Blo 1174404 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B1762739 : Blo 1174404 1762739 := bstep (se 1 (by rfl) ⟨1322054, by rfl⟩ : syracuseStep 1762739 = 2644109) B2644109
theorem B1762769 : Blo 1174404 1762769 := bstep (se 2 (by rfl) ⟨661038, by rfl⟩ : syracuseStep 1762769 = 1322077) B1322077
theorem B1983953 : Blo 1174404 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B1762787 : Blo 1174404 1762787 := bstep (se 1 (by rfl) ⟨1322090, by rfl⟩ : syracuseStep 1762787 = 2644181) B2644181
theorem B1762817 : Blo 1174404 1762817 := bstep (se 2 (by rfl) ⟨661056, by rfl⟩ : syracuseStep 1762817 = 1322113) B1322113
theorem B2147843 : Blo 1174404 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B1762835 : Blo 1174404 1762835 := bstep (se 1 (by rfl) ⟨1322126, by rfl⟩ : syracuseStep 1762835 = 2644253) B2644253
theorem B5948963 : Blo 1174404 5948963 := bstep (se 1 (by rfl) ⟨4461722, by rfl⟩ : syracuseStep 5948963 = 8923445) B8923445
theorem B1762865 : Blo 1174404 1762865 := bstep (se 2 (by rfl) ⟨661074, by rfl⟩ : syracuseStep 1762865 = 1322149) B1322149
theorem B1762883 : Blo 1174404 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B1984081 : Blo 1174404 1984081 := bstep (se 2 (by rfl) ⟨744030, by rfl⟩ : syracuseStep 1984081 = 1488061) B1488061
theorem B1762913 : Blo 1174404 1762913 := bstep (se 2 (by rfl) ⟨661092, by rfl⟩ : syracuseStep 1762913 = 1322185) B1322185
theorem B2229859 : Blo 1174404 2229859 := bstep (se 1 (by rfl) ⟨1672394, by rfl⟩ : syracuseStep 2229859 = 3344789) B3344789
theorem B7530083 : Blo 1174404 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B1762931 : Blo 1174404 1762931 := bstep (se 1 (by rfl) ⟨1322198, by rfl⟩ : syracuseStep 1762931 = 2644397) B2644397
theorem B1984115 : Blo 1174404 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B2975363 : Blo 1174404 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B4236941 : Blo 1174404 4236941 := bstep (se 3 (by rfl) ⟨794426, by rfl⟩ : syracuseStep 4236941 = 1588853) B1588853
theorem B2229905 : Blo 1174404 2229905 := bstep (se 2 (by rfl) ⟨836214, by rfl⟩ : syracuseStep 2229905 = 1672429) B1672429
theorem B1762961 : Blo 1174404 1762961 := bstep (se 2 (by rfl) ⟨661110, by rfl⟩ : syracuseStep 1762961 = 1322221) B1322221
theorem B1762979 : Blo 1174404 1762979 := bstep (se 1 (by rfl) ⟨1322234, by rfl⟩ : syracuseStep 1762979 = 2644469) B2644469
theorem B1763009 : Blo 1174404 1763009 := bstep (se 2 (by rfl) ⟨661128, by rfl⟩ : syracuseStep 1763009 = 1322257) B1322257
theorem B1672913 : Blo 1174404 1672913 := bstep (se 2 (by rfl) ⟨627342, by rfl⟩ : syracuseStep 1672913 = 1254685) B1254685
theorem B1763027 : Blo 1174404 1763027 := bstep (se 1 (by rfl) ⟨1322270, by rfl⟩ : syracuseStep 1763027 = 2644541) B2644541
theorem B1763057 : Blo 1174404 1763057 := bstep (se 2 (by rfl) ⟨661146, by rfl⟩ : syracuseStep 1763057 = 1322293) B1322293
theorem B1984243 : Blo 1174404 1984243 := bstep (se 1 (by rfl) ⟨1488182, by rfl⟩ : syracuseStep 1984243 = 2976365) B2976365
theorem B1763075 : Blo 1174404 1763075 := bstep (se 1 (by rfl) ⟨1322306, by rfl⟩ : syracuseStep 1763075 = 2644613) B2644613
theorem B7251725 : Blo 1174404 7251725 := bstep (se 3 (by rfl) ⟨1359698, by rfl⟩ : syracuseStep 7251725 = 2719397) B2719397
theorem B1763105 : Blo 1174404 1763105 := bstep (se 2 (by rfl) ⟨661164, by rfl⟩ : syracuseStep 1763105 = 1322329) B1322329
theorem B1763123 : Blo 1174404 1763123 := bstep (se 1 (by rfl) ⟨1322342, by rfl⟩ : syracuseStep 1763123 = 2644685) B2644685
theorem B2975555 : Blo 1174404 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B1763153 : Blo 1174404 1763153 := bstep (se 2 (by rfl) ⟨661182, by rfl⟩ : syracuseStep 1763153 = 1322365) B1322365
theorem B1763171 : Blo 1174404 1763171 := bstep (se 1 (by rfl) ⟨1322378, by rfl⟩ : syracuseStep 1763171 = 2644757) B2644757
theorem B1763201 : Blo 1174404 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B1984385 : Blo 1174404 1984385 := bstep (se 2 (by rfl) ⟨744144, by rfl⟩ : syracuseStep 1984385 = 1488289) B1488289
theorem B1763219 : Blo 1174404 1763219 := bstep (se 1 (by rfl) ⟨1322414, by rfl⟩ : syracuseStep 1763219 = 2644829) B2644829
theorem B3966893 : Blo 1174404 3966893 := bstep (se 3 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 3966893 = 1487585) B1487585
theorem B2230193 : Blo 1174404 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B1763249 : Blo 1174404 1763249 := bstep (se 2 (by rfl) ⟨661218, by rfl⟩ : syracuseStep 1763249 = 1322437) B1322437
theorem B1763267 : Blo 1174404 1763267 := bstep (se 1 (by rfl) ⟨1322450, by rfl⟩ : syracuseStep 1763267 = 2644901) B2644901
theorem B2942929 : Blo 1174404 2942929 := bstep (se 2 (by rfl) ⟨1103598, by rfl⟩ : syracuseStep 2942929 = 2207197) B2207197
theorem B1763297 : Blo 1174404 1763297 := bstep (se 2 (by rfl) ⟨661236, by rfl⟩ : syracuseStep 1763297 = 1322473) B1322473
theorem B3966947 : Blo 1174404 3966947 := bstep (se 1 (by rfl) ⟨2975210, by rfl⟩ : syracuseStep 3966947 = 5950421) B5950421
theorem B1763315 : Blo 1174404 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1984513 : Blo 1174404 1984513 := bstep (se 2 (by rfl) ⟨744192, by rfl⟩ : syracuseStep 1984513 = 1488385) B1488385
theorem B1763345 : Blo 1174404 1763345 := bstep (se 2 (by rfl) ⟨661254, by rfl⟩ : syracuseStep 1763345 = 1322509) B1322509
theorem B1763363 : Blo 1174404 1763363 := bstep (se 1 (by rfl) ⟨1322522, by rfl⟩ : syracuseStep 1763363 = 2645045) B2645045
theorem B1984547 : Blo 1174404 1984547 := bstep (se 1 (by rfl) ⟨1488410, by rfl⟩ : syracuseStep 1984547 = 2976821) B2976821
theorem B1763393 : Blo 1174404 1763393 := bstep (se 2 (by rfl) ⟨661272, by rfl⟩ : syracuseStep 1763393 = 1322545) B1322545
theorem B1763411 : Blo 1174404 1763411 := bstep (se 1 (by rfl) ⟨1322558, by rfl⟩ : syracuseStep 1763411 = 2645117) B2645117
theorem B2508899 : Blo 1174404 2508899 := bstep (se 1 (by rfl) ⟨1881674, by rfl⟩ : syracuseStep 2508899 = 3763349) B3763349
theorem B1763441 : Blo 1174404 1763441 := bstep (se 2 (by rfl) ⟨661290, by rfl⟩ : syracuseStep 1763441 = 1322581) B1322581
theorem B1763459 : Blo 1174404 1763459 := bstep (se 1 (by rfl) ⟨1322594, by rfl⟩ : syracuseStep 1763459 = 2645189) B2645189
theorem B6695045 : Blo 1174404 6695045 := bstep (se 4 (by rfl) ⟨627660, by rfl⟩ : syracuseStep 6695045 = 1255321) B1255321
theorem B1763489 : Blo 1174404 1763489 := bstep (se 2 (by rfl) ⟨661308, by rfl⟩ : syracuseStep 1763489 = 1322617) B1322617
theorem B1984675 : Blo 1174404 1984675 := bstep (se 1 (by rfl) ⟨1488506, by rfl⟩ : syracuseStep 1984675 = 2977013) B2977013
theorem B3819683 : Blo 1174404 3819683 := bstep (se 1 (by rfl) ⟨2864762, by rfl⟩ : syracuseStep 3819683 = 5729525) B5729525
theorem B3344561 : Blo 1174404 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B1763507 : Blo 1174404 1763507 := bstep (se 1 (by rfl) ⟨1322630, by rfl⟩ : syracuseStep 1763507 = 2645261) B2645261
theorem B1763537 : Blo 1174404 1763537 := bstep (se 2 (by rfl) ⟨661326, by rfl⟩ : syracuseStep 1763537 = 1322653) B1322653
theorem B1763555 : Blo 1174404 1763555 := bstep (se 1 (by rfl) ⟨1322666, by rfl⟩ : syracuseStep 1763555 = 2645333) B2645333
theorem B3967217 : Blo 1174404 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B1763585 : Blo 1174404 1763585 := bstep (se 2 (by rfl) ⟨661344, by rfl⟩ : syracuseStep 1763585 = 1322689) B1322689
theorem B1763603 : Blo 1174404 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B1763633 : Blo 1174404 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1321267 : Blo 1174404 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B1984817 : Blo 1174404 1984817 := bstep (se 2 (by rfl) ⟨744306, by rfl⟩ : syracuseStep 1984817 = 1488613) B1488613
theorem B1763651 : Blo 1174404 1763651 := bstep (se 1 (by rfl) ⟨1322738, by rfl⟩ : syracuseStep 1763651 = 2645477) B2645477
theorem B5949773 : Blo 1174404 5949773 := bstep (se 3 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 5949773 = 2231165) B2231165
theorem B1763681 : Blo 1174404 1763681 := bstep (se 2 (by rfl) ⟨661380, by rfl⟩ : syracuseStep 1763681 = 1322761) B1322761
theorem B1763699 : Blo 1174404 1763699 := bstep (se 1 (by rfl) ⟨1322774, by rfl⟩ : syracuseStep 1763699 = 2645549) B2645549
theorem B1763729 : Blo 1174404 1763729 := bstep (se 2 (by rfl) ⟨661398, by rfl⟩ : syracuseStep 1763729 = 1322797) B1322797
theorem B1763747 : Blo 1174404 1763747 := bstep (se 1 (by rfl) ⟨1322810, by rfl⟩ : syracuseStep 1763747 = 2645621) B2645621
theorem B1984945 : Blo 1174404 1984945 := bstep (se 2 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 1984945 = 1488709) B1488709
theorem B1763777 : Blo 1174404 1763777 := bstep (se 2 (by rfl) ⟨661416, by rfl⟩ : syracuseStep 1763777 = 1322833) B1322833
theorem B1321411 : Blo 1174404 1321411 := bstep (se 1 (by rfl) ⟨991058, by rfl⟩ : syracuseStep 1321411 = 1982117) B1982117
theorem B61049285 : Blo 1174404 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B1763795 : Blo 1174404 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1984979 : Blo 1174404 1984979 := bstep (se 1 (by rfl) ⟨1488734, by rfl⟩ : syracuseStep 1984979 = 2977469) B2977469
theorem B1763825 : Blo 1174404 1763825 := bstep (se 2 (by rfl) ⟨661434, by rfl⟩ : syracuseStep 1763825 = 1322869) B1322869
theorem B1763843 : Blo 1174404 1763843 := bstep (se 1 (by rfl) ⟨1322882, by rfl⟩ : syracuseStep 1763843 = 2645765) B2645765
theorem B1763873 : Blo 1174404 1763873 := bstep (se 2 (by rfl) ⟨661452, by rfl⟩ : syracuseStep 1763873 = 1322905) B1322905
theorem B4762147 : Blo 1174404 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B1673779 : Blo 1174404 1673779 := bstep (se 1 (by rfl) ⟨1255334, by rfl⟩ : syracuseStep 1673779 = 2510669) B2510669
theorem B1763891 : Blo 1174404 1763891 := bstep (se 1 (by rfl) ⟨1322918, by rfl⟩ : syracuseStep 1763891 = 2645837) B2645837
theorem B1763921 : Blo 1174404 1763921 := bstep (se 2 (by rfl) ⟨661470, by rfl⟩ : syracuseStep 1763921 = 1322941) B1322941
theorem B1321555 : Blo 1174404 1321555 := bstep (se 1 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 1321555 = 1982333) B1982333
theorem B1985107 : Blo 1174404 1985107 := bstep (se 1 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 1985107 = 2977661) B2977661
theorem B1763939 : Blo 1174404 1763939 := bstep (se 1 (by rfl) ⟨1322954, by rfl⟩ : syracuseStep 1763939 = 2645909) B2645909
theorem B1763969 : Blo 1174404 1763969 := bstep (se 2 (by rfl) ⟨661488, by rfl⟩ : syracuseStep 1763969 = 1322977) B1322977
theorem B2230915 : Blo 1174404 2230915 := bstep (se 1 (by rfl) ⟨1673186, by rfl⟩ : syracuseStep 2230915 = 3346373) B3346373
theorem B1673875 : Blo 1174404 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B1763987 : Blo 1174404 1763987 := bstep (se 1 (by rfl) ⟨1322990, by rfl⟩ : syracuseStep 1763987 = 2645981) B2645981
theorem B4459171 : Blo 1174404 4459171 := bstep (se 1 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 4459171 = 6688757) B6688757
theorem B1764017 : Blo 1174404 1764017 := bstep (se 2 (by rfl) ⟨661506, by rfl⟩ : syracuseStep 1764017 = 1323013) B1323013
theorem B1764035 : Blo 1174404 1764035 := bstep (se 1 (by rfl) ⟨1323026, by rfl⟩ : syracuseStep 1764035 = 2646053) B2646053
theorem B1764065 : Blo 1174404 1764065 := bstep (se 2 (by rfl) ⟨661524, by rfl⟩ : syracuseStep 1764065 = 1323049) B1323049
theorem B1321699 : Blo 1174404 1321699 := bstep (se 1 (by rfl) ⟨991274, by rfl⟩ : syracuseStep 1321699 = 1982549) B1982549
theorem B2976497 : Blo 1174404 2976497 := bstep (se 2 (by rfl) ⟨1116186, by rfl⟩ : syracuseStep 2976497 = 2232373) B2232373
theorem B1764083 : Blo 1174404 1764083 := bstep (se 1 (by rfl) ⟨1323062, by rfl⟩ : syracuseStep 1764083 = 2646125) B2646125
theorem B1411843 : Blo 1174404 1411843 := bstep (se 1 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 1411843 = 2117765) B2117765
theorem B3967757 : Blo 1174404 3967757 := bstep (se 3 (by rfl) ⟨743954, by rfl⟩ : syracuseStep 3967757 = 1487909) B1487909
theorem B1764113 : Blo 1174404 1764113 := bstep (se 2 (by rfl) ⟨661542, by rfl⟩ : syracuseStep 1764113 = 1323085) B1323085
theorem B2976547 : Blo 1174404 2976547 := bstep (se 1 (by rfl) ⟨2232410, by rfl⟩ : syracuseStep 2976547 = 4464821) B4464821
theorem B1764131 : Blo 1174404 1764131 := bstep (se 1 (by rfl) ⟨1323098, by rfl⟩ : syracuseStep 1764131 = 2646197) B2646197
theorem B6695729 : Blo 1174404 6695729 := bstep (se 2 (by rfl) ⟨2510898, by rfl⟩ : syracuseStep 6695729 = 5021797) B5021797
theorem B1764161 : Blo 1174404 1764161 := bstep (se 2 (by rfl) ⟨661560, by rfl⟩ : syracuseStep 1764161 = 1323121) B1323121
theorem B3967811 : Blo 1174404 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B1764179 : Blo 1174404 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B1764209 : Blo 1174404 1764209 := bstep (se 2 (by rfl) ⟨661578, by rfl⟩ : syracuseStep 1764209 = 1323157) B1323157
theorem B5729137 : Blo 1174404 5729137 := bstep (se 2 (by rfl) ⟨2148426, by rfl⟩ : syracuseStep 5729137 = 4296853) B4296853
theorem B1321843 : Blo 1174404 1321843 := bstep (se 1 (by rfl) ⟨991382, by rfl⟩ : syracuseStep 1321843 = 1982765) B1982765
theorem B1764227 : Blo 1174404 1764227 := bstep (se 1 (by rfl) ⟨1323170, by rfl⟩ : syracuseStep 1764227 = 2646341) B2646341
theorem B1174419 : Blo 1174404 1174419 := bstep (se 1 (by rfl) ⟨880814, by rfl⟩ : syracuseStep 1174419 = 1761629) B1761629
theorem B1411987 : Blo 1174404 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B2010017 : Blo 1174404 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B1174435 : Blo 1174404 1174435 := bstep (se 1 (by rfl) ⟨880826, by rfl⟩ : syracuseStep 1174435 = 1761653) B1761653
theorem B1764257 : Blo 1174404 1764257 := bstep (se 2 (by rfl) ⟨661596, by rfl⟩ : syracuseStep 1764257 = 1323193) B1323193
theorem B2976689 : Blo 1174404 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B1174451 : Blo 1174404 1174451 := bstep (se 1 (by rfl) ⟨880838, by rfl⟩ : syracuseStep 1174451 = 1761677) B1761677
theorem B1764275 : Blo 1174404 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B1174467 : Blo 1174404 1174467 := bstep (se 1 (by rfl) ⟨880850, by rfl⟩ : syracuseStep 1174467 = 1761701) B1761701
theorem B1764305 : Blo 1174404 1764305 := bstep (se 2 (by rfl) ⟨661614, by rfl⟩ : syracuseStep 1764305 = 1323229) B1323229
theorem B1174483 : Blo 1174404 1174483 := bstep (se 1 (by rfl) ⟨880862, by rfl⟩ : syracuseStep 1174483 = 1761725) B1761725
theorem B1174499 : Blo 1174404 1174499 := bstep (se 1 (by rfl) ⟨880874, by rfl⟩ : syracuseStep 1174499 = 1761749) B1761749
theorem B1764323 : Blo 1174404 1764323 := bstep (se 1 (by rfl) ⟨1323242, by rfl⟩ : syracuseStep 1764323 = 2646485) B2646485
theorem B1174515 : Blo 1174404 1174515 := bstep (se 1 (by rfl) ⟨880886, by rfl⟩ : syracuseStep 1174515 = 1761773) B1761773
theorem B1412083 : Blo 1174404 1412083 := bstep (se 1 (by rfl) ⟨1059062, by rfl⟩ : syracuseStep 1412083 = 2118125) B2118125
theorem B1764353 : Blo 1174404 1764353 := bstep (se 2 (by rfl) ⟨661632, by rfl⟩ : syracuseStep 1764353 = 1323265) B1323265
theorem B1174531 : Blo 1174404 1174531 := bstep (se 1 (by rfl) ⟨880898, by rfl⟩ : syracuseStep 1174531 = 1761797) B1761797
theorem B1321987 : Blo 1174404 1321987 := bstep (se 1 (by rfl) ⟨991490, by rfl⟩ : syracuseStep 1321987 = 1982981) B1982981
theorem B13388813 : Blo 1174404 13388813 := bstep (se 3 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 13388813 = 5020805) B5020805
theorem B1174547 : Blo 1174404 1174547 := bstep (se 1 (by rfl) ⟨880910, by rfl⟩ : syracuseStep 1174547 = 1761821) B1761821
theorem B1764371 : Blo 1174404 1764371 := bstep (se 1 (by rfl) ⟨1323278, by rfl⟩ : syracuseStep 1764371 = 2646557) B2646557
theorem B1174563 : Blo 1174404 1174563 := bstep (se 1 (by rfl) ⟨880922, by rfl⟩ : syracuseStep 1174563 = 1761845) B1761845
theorem B3763235 : Blo 1174404 3763235 := bstep (se 1 (by rfl) ⟨2822426, by rfl⟩ : syracuseStep 3763235 = 5644853) B5644853
theorem B1764401 : Blo 1174404 1764401 := bstep (se 2 (by rfl) ⟨661650, by rfl⟩ : syracuseStep 1764401 = 1323301) B1323301
theorem B1174579 : Blo 1174404 1174579 := bstep (se 1 (by rfl) ⟨880934, by rfl⟩ : syracuseStep 1174579 = 1761869) B1761869
theorem B1174595 : Blo 1174404 1174595 := bstep (se 1 (by rfl) ⟨880946, by rfl⟩ : syracuseStep 1174595 = 1761893) B1761893
theorem B2231363 : Blo 1174404 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B1764419 : Blo 1174404 1764419 := bstep (se 1 (by rfl) ⟨1323314, by rfl⟩ : syracuseStep 1764419 = 2646629) B2646629
theorem B3968081 : Blo 1174404 3968081 := bstep (se 2 (by rfl) ⟨1488030, by rfl⟩ : syracuseStep 3968081 = 2976061) B2976061
theorem B1174611 : Blo 1174404 1174611 := bstep (se 1 (by rfl) ⟨880958, by rfl⟩ : syracuseStep 1174611 = 1761917) B1761917
theorem B1174627 : Blo 1174404 1174627 := bstep (se 1 (by rfl) ⟨880970, by rfl⟩ : syracuseStep 1174627 = 1761941) B1761941
theorem B1764449 : Blo 1174404 1764449 := bstep (se 2 (by rfl) ⟨661668, by rfl⟩ : syracuseStep 1764449 = 1323337) B1323337
theorem B114355313 : Blo 1174404 114355313 := bstep (se 2 (by rfl) ⟨42883242, by rfl⟩ : syracuseStep 114355313 = 85766485) B85766485
theorem B1174643 : Blo 1174404 1174643 := bstep (se 1 (by rfl) ⟨880982, by rfl⟩ : syracuseStep 1174643 = 1761965) B1761965
theorem B1764467 : Blo 1174404 1764467 := bstep (se 1 (by rfl) ⟨1323350, by rfl⟩ : syracuseStep 1764467 = 2646701) B2646701
theorem B1174659 : Blo 1174404 1174659 := bstep (se 1 (by rfl) ⟨880994, by rfl⟩ : syracuseStep 1174659 = 1761989) B1761989
theorem B1674371 : Blo 1174404 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B7146629 : Blo 1174404 7146629 := bstep (se 4 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 7146629 = 1339993) B1339993
theorem B1764497 : Blo 1174404 1764497 := bstep (se 2 (by rfl) ⟨661686, by rfl⟩ : syracuseStep 1764497 = 1323373) B1323373
theorem B1174675 : Blo 1174404 1174675 := bstep (se 1 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 1174675 = 1762013) B1762013
theorem B1322131 : Blo 1174404 1322131 := bstep (se 1 (by rfl) ⟨991598, by rfl⟩ : syracuseStep 1322131 = 1983197) B1983197
theorem B1174691 : Blo 1174404 1174691 := bstep (se 1 (by rfl) ⟨881018, by rfl⟩ : syracuseStep 1174691 = 1762037) B1762037
theorem B1764515 : Blo 1174404 1764515 := bstep (se 1 (by rfl) ⟨1323386, by rfl⟩ : syracuseStep 1764515 = 2646773) B2646773
theorem B1174707 : Blo 1174404 1174707 := bstep (se 1 (by rfl) ⟨881030, by rfl⟩ : syracuseStep 1174707 = 1762061) B1762061
theorem B1764545 : Blo 1174404 1764545 := bstep (se 2 (by rfl) ⟨661704, by rfl⟩ : syracuseStep 1764545 = 1323409) B1323409
theorem B1174723 : Blo 1174404 1174723 := bstep (se 1 (by rfl) ⟨881042, by rfl⟩ : syracuseStep 1174723 = 1762085) B1762085
theorem B1174739 : Blo 1174404 1174739 := bstep (se 1 (by rfl) ⟨881054, by rfl⟩ : syracuseStep 1174739 = 1762109) B1762109
theorem B1764563 : Blo 1174404 1764563 := bstep (se 1 (by rfl) ⟨1323422, by rfl⟩ : syracuseStep 1764563 = 2646845) B2646845
theorem B1174755 : Blo 1174404 1174755 := bstep (se 1 (by rfl) ⟨881066, by rfl⟩ : syracuseStep 1174755 = 1762133) B1762133
theorem B1764593 : Blo 1174404 1764593 := bstep (se 2 (by rfl) ⟨661722, by rfl⟩ : syracuseStep 1764593 = 1323445) B1323445
theorem B1174771 : Blo 1174404 1174771 := bstep (se 1 (by rfl) ⟨881078, by rfl⟩ : syracuseStep 1174771 = 1762157) B1762157
theorem B1174787 : Blo 1174404 1174787 := bstep (se 1 (by rfl) ⟨881090, by rfl⟩ : syracuseStep 1174787 = 1762181) B1762181
theorem B2010371 : Blo 1174404 2010371 := bstep (se 1 (by rfl) ⟨1507778, by rfl⟩ : syracuseStep 2010371 = 3015557) B3015557
theorem B1174803 : Blo 1174404 1174803 := bstep (se 1 (by rfl) ⟨881102, by rfl⟩ : syracuseStep 1174803 = 1762205) B1762205
theorem B1174819 : Blo 1174404 1174819 := bstep (se 1 (by rfl) ⟨881114, by rfl⟩ : syracuseStep 1174819 = 1762229) B1762229
theorem B1322275 : Blo 1174404 1322275 := bstep (se 1 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 1322275 = 1983413) B1983413
theorem B1174835 : Blo 1174404 1174835 := bstep (se 1 (by rfl) ⟨881126, by rfl⟩ : syracuseStep 1174835 = 1762253) B1762253
theorem B1174851 : Blo 1174404 1174851 := bstep (se 1 (by rfl) ⟨881138, by rfl⟩ : syracuseStep 1174851 = 1762277) B1762277
theorem B1174867 : Blo 1174404 1174867 := bstep (se 1 (by rfl) ⟨881150, by rfl⟩ : syracuseStep 1174867 = 1762301) B1762301
theorem B1174883 : Blo 1174404 1174883 := bstep (se 1 (by rfl) ⟨881162, by rfl⟩ : syracuseStep 1174883 = 1762325) B1762325
theorem B5647715 : Blo 1174404 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B2231651 : Blo 1174404 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B1174899 : Blo 1174404 1174899 := bstep (se 1 (by rfl) ⟨881174, by rfl⟩ : syracuseStep 1174899 = 1762349) B1762349
theorem B1174915 : Blo 1174404 1174915 := bstep (se 1 (by rfl) ⟨881186, by rfl⟩ : syracuseStep 1174915 = 1762373) B1762373
theorem B1174931 : Blo 1174404 1174931 := bstep (se 1 (by rfl) ⟨881198, by rfl⟩ : syracuseStep 1174931 = 1762397) B1762397
theorem B1174947 : Blo 1174404 1174947 := bstep (se 1 (by rfl) ⟨881210, by rfl⟩ : syracuseStep 1174947 = 1762421) B1762421
theorem B1174963 : Blo 1174404 1174963 := bstep (se 1 (by rfl) ⟨881222, by rfl⟩ : syracuseStep 1174963 = 1762445) B1762445
theorem B1322419 : Blo 1174404 1322419 := bstep (se 1 (by rfl) ⟨991814, by rfl⟩ : syracuseStep 1322419 = 1983629) B1983629
theorem B1174979 : Blo 1174404 1174979 := bstep (se 1 (by rfl) ⟨881234, by rfl⟩ : syracuseStep 1174979 = 1762469) B1762469
theorem B1174995 : Blo 1174404 1174995 := bstep (se 1 (by rfl) ⟨881246, by rfl⟩ : syracuseStep 1174995 = 1762493) B1762493
theorem B1412563 : Blo 1174404 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B24440291 : Blo 1174404 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B1175011 : Blo 1174404 1175011 := bstep (se 1 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 1175011 = 1762517) B1762517
theorem B1175027 : Blo 1174404 1175027 := bstep (se 1 (by rfl) ⟨881270, by rfl⟩ : syracuseStep 1175027 = 1762541) B1762541
theorem B1175043 : Blo 1174404 1175043 := bstep (se 1 (by rfl) ⟨881282, by rfl⟩ : syracuseStep 1175043 = 1762565) B1762565
theorem B1175059 : Blo 1174404 1175059 := bstep (se 1 (by rfl) ⟨881294, by rfl⟩ : syracuseStep 1175059 = 1762589) B1762589
theorem B1175075 : Blo 1174404 1175075 := bstep (se 1 (by rfl) ⟨881306, by rfl⟩ : syracuseStep 1175075 = 1762613) B1762613
theorem B1175091 : Blo 1174404 1175091 := bstep (se 1 (by rfl) ⟨881318, by rfl⟩ : syracuseStep 1175091 = 1762637) B1762637
theorem B1175107 : Blo 1174404 1175107 := bstep (se 1 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 1175107 = 1762661) B1762661
theorem B1322563 : Blo 1174404 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B1175123 : Blo 1174404 1175123 := bstep (se 1 (by rfl) ⟨881342, by rfl⟩ : syracuseStep 1175123 = 1762685) B1762685
theorem B3346019 : Blo 1174404 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B1175139 : Blo 1174404 1175139 := bstep (se 1 (by rfl) ⟨881354, by rfl⟩ : syracuseStep 1175139 = 1762709) B1762709
theorem B3395171 : Blo 1174404 3395171 := bstep (se 1 (by rfl) ⟨2546378, by rfl⟩ : syracuseStep 3395171 = 5092757) B5092757
theorem B3968621 : Blo 1174404 3968621 := bstep (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) B1488233
theorem B4763249 : Blo 1174404 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1486451 : Blo 1174404 1486451 := bstep (se 1 (by rfl) ⟨1114838, by rfl⟩ : syracuseStep 1486451 = 2229677) B2229677
theorem B1175155 : Blo 1174404 1175155 := bstep (se 1 (by rfl) ⟨881366, by rfl⟩ : syracuseStep 1175155 = 1762733) B1762733
theorem B1175171 : Blo 1174404 1175171 := bstep (se 1 (by rfl) ⟨881378, by rfl⟩ : syracuseStep 1175171 = 1762757) B1762757
theorem B1175187 : Blo 1174404 1175187 := bstep (se 1 (by rfl) ⟨881390, by rfl⟩ : syracuseStep 1175187 = 1762781) B1762781
theorem B1175203 : Blo 1174404 1175203 := bstep (se 1 (by rfl) ⟨881402, by rfl⟩ : syracuseStep 1175203 = 1762805) B1762805
theorem B3968675 : Blo 1174404 3968675 := bstep (se 1 (by rfl) ⟨2976506, by rfl⟩ : syracuseStep 3968675 = 5953013) B5953013
theorem B1175219 : Blo 1174404 1175219 := bstep (se 1 (by rfl) ⟨881414, by rfl⟩ : syracuseStep 1175219 = 1762829) B1762829
theorem B1175235 : Blo 1174404 1175235 := bstep (se 1 (by rfl) ⟨881426, by rfl⟩ : syracuseStep 1175235 = 1762853) B1762853
theorem B2821841 : Blo 1174404 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B1175251 : Blo 1174404 1175251 := bstep (se 1 (by rfl) ⟨881438, by rfl⟩ : syracuseStep 1175251 = 1762877) B1762877
theorem B1322707 : Blo 1174404 1322707 := bstep (se 1 (by rfl) ⟨992030, by rfl⟩ : syracuseStep 1322707 = 1984061) B1984061
theorem B1175267 : Blo 1174404 1175267 := bstep (se 1 (by rfl) ⟨881450, by rfl⟩ : syracuseStep 1175267 = 1762901) B1762901
theorem B3264241 : Blo 1174404 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B1175283 : Blo 1174404 1175283 := bstep (se 1 (by rfl) ⟨881462, by rfl⟩ : syracuseStep 1175283 = 1762925) B1762925
theorem B1175299 : Blo 1174404 1175299 := bstep (se 1 (by rfl) ⟨881474, by rfl⟩ : syracuseStep 1175299 = 1762949) B1762949
theorem B1175315 : Blo 1174404 1175315 := bstep (se 1 (by rfl) ⟨881486, by rfl⟩ : syracuseStep 1175315 = 1762973) B1762973
theorem B1175331 : Blo 1174404 1175331 := bstep (se 1 (by rfl) ⟨881498, by rfl⟩ : syracuseStep 1175331 = 1762997) B1762997
theorem B1175347 : Blo 1174404 1175347 := bstep (se 1 (by rfl) ⟨881510, by rfl⟩ : syracuseStep 1175347 = 1763021) B1763021
theorem B1175363 : Blo 1174404 1175363 := bstep (se 1 (by rfl) ⟨881522, by rfl⟩ : syracuseStep 1175363 = 1763045) B1763045
theorem B1175379 : Blo 1174404 1175379 := bstep (se 1 (by rfl) ⟨881534, by rfl⟩ : syracuseStep 1175379 = 1763069) B1763069
theorem B1175395 : Blo 1174404 1175395 := bstep (se 1 (by rfl) ⟨881546, by rfl⟩ : syracuseStep 1175395 = 1763093) B1763093
theorem B1322851 : Blo 1174404 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B5017457 : Blo 1174404 5017457 := bstep (se 2 (by rfl) ⟨1881546, by rfl⟩ : syracuseStep 5017457 = 3763093) B3763093
theorem B1175411 : Blo 1174404 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B1175427 : Blo 1174404 1175427 := bstep (se 1 (by rfl) ⟨881570, by rfl⟩ : syracuseStep 1175427 = 1763141) B1763141
theorem B2977681 : Blo 1174404 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1175443 : Blo 1174404 1175443 := bstep (se 1 (by rfl) ⟨881582, by rfl⟩ : syracuseStep 1175443 = 1763165) B1763165
theorem B1175459 : Blo 1174404 1175459 := bstep (se 1 (by rfl) ⟨881594, by rfl⟩ : syracuseStep 1175459 = 1763189) B1763189
theorem B3968945 : Blo 1174404 3968945 := bstep (se 2 (by rfl) ⟨1488354, by rfl⟩ : syracuseStep 3968945 = 2976709) B2976709
theorem B1175475 : Blo 1174404 1175475 := bstep (se 1 (by rfl) ⟨881606, by rfl⟩ : syracuseStep 1175475 = 1763213) B1763213
theorem B4018115 : Blo 1174404 4018115 := bstep (se 1 (by rfl) ⟨3013586, by rfl⟩ : syracuseStep 4018115 = 6027173) B6027173
theorem B1175491 : Blo 1174404 1175491 := bstep (se 1 (by rfl) ⟨881618, by rfl⟩ : syracuseStep 1175491 = 1763237) B1763237
theorem B1175507 : Blo 1174404 1175507 := bstep (se 1 (by rfl) ⟨881630, by rfl⟩ : syracuseStep 1175507 = 1763261) B1763261
theorem B1175523 : Blo 1174404 1175523 := bstep (se 1 (by rfl) ⟨881642, by rfl⟩ : syracuseStep 1175523 = 1763285) B1763285
theorem B1175539 : Blo 1174404 1175539 := bstep (se 1 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 1175539 = 1763309) B1763309
theorem B1322995 : Blo 1174404 1322995 := bstep (se 1 (by rfl) ⟨992246, by rfl⟩ : syracuseStep 1322995 = 1984493) B1984493
theorem B1175555 : Blo 1174404 1175555 := bstep (se 1 (by rfl) ⟨881666, by rfl⟩ : syracuseStep 1175555 = 1763333) B1763333
theorem B1175571 : Blo 1174404 1175571 := bstep (se 1 (by rfl) ⟨881678, by rfl⟩ : syracuseStep 1175571 = 1763357) B1763357
theorem B1609763 : Blo 1174404 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1175587 : Blo 1174404 1175587 := bstep (se 1 (by rfl) ⟨881690, by rfl⟩ : syracuseStep 1175587 = 1763381) B1763381
theorem B1175603 : Blo 1174404 1175603 := bstep (se 1 (by rfl) ⟨881702, by rfl⟩ : syracuseStep 1175603 = 1763405) B1763405
theorem B1175619 : Blo 1174404 1175619 := bstep (se 1 (by rfl) ⟨881714, by rfl⟩ : syracuseStep 1175619 = 1763429) B1763429
theorem B7532621 : Blo 1174404 7532621 := bstep (se 3 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 7532621 = 2824733) B2824733
theorem B1175635 : Blo 1174404 1175635 := bstep (se 1 (by rfl) ⟨881726, by rfl⟩ : syracuseStep 1175635 = 1763453) B1763453
theorem B3764323 : Blo 1174404 3764323 := bstep (se 1 (by rfl) ⟨2823242, by rfl⟩ : syracuseStep 3764323 = 5646485) B5646485
theorem B1175651 : Blo 1174404 1175651 := bstep (se 1 (by rfl) ⟨881738, by rfl⟩ : syracuseStep 1175651 = 1763477) B1763477
theorem B1175667 : Blo 1174404 1175667 := bstep (se 1 (by rfl) ⟨881750, by rfl⟩ : syracuseStep 1175667 = 1763501) B1763501
theorem B1175683 : Blo 1174404 1175683 := bstep (se 1 (by rfl) ⟨881762, by rfl⟩ : syracuseStep 1175683 = 1763525) B1763525
theorem B1323139 : Blo 1174404 1323139 := bstep (se 1 (by rfl) ⟨992354, by rfl⟩ : syracuseStep 1323139 = 1984709) B1984709
theorem B1175699 : Blo 1174404 1175699 := bstep (se 1 (by rfl) ⟨881774, by rfl⟩ : syracuseStep 1175699 = 1763549) B1763549
theorem B1175715 : Blo 1174404 1175715 := bstep (se 1 (by rfl) ⟨881786, by rfl⟩ : syracuseStep 1175715 = 1763573) B1763573
theorem B5648561 : Blo 1174404 5648561 := bstep (se 2 (by rfl) ⟨2118210, by rfl⟩ : syracuseStep 5648561 = 4236421) B4236421
theorem B1175731 : Blo 1174404 1175731 := bstep (se 1 (by rfl) ⟨881798, by rfl⟩ : syracuseStep 1175731 = 1763597) B1763597
theorem B1175747 : Blo 1174404 1175747 := bstep (se 1 (by rfl) ⟨881810, by rfl⟩ : syracuseStep 1175747 = 1763621) B1763621
theorem B1175763 : Blo 1174404 1175763 := bstep (se 1 (by rfl) ⟨881822, by rfl⟩ : syracuseStep 1175763 = 1763645) B1763645
theorem B1175779 : Blo 1174404 1175779 := bstep (se 1 (by rfl) ⟨881834, by rfl⟩ : syracuseStep 1175779 = 1763669) B1763669
theorem B6697187 : Blo 1174404 6697187 := bstep (se 1 (by rfl) ⟨5022890, by rfl⟩ : syracuseStep 6697187 = 10045781) B10045781
theorem B3764465 : Blo 1174404 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B1175795 : Blo 1174404 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B1175811 : Blo 1174404 1175811 := bstep (se 1 (by rfl) ⟨881858, by rfl⟩ : syracuseStep 1175811 = 1763717) B1763717
theorem B2511121 : Blo 1174404 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B2232593 : Blo 1174404 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B1175827 : Blo 1174404 1175827 := bstep (se 1 (by rfl) ⟨881870, by rfl⟩ : syracuseStep 1175827 = 1763741) B1763741
theorem B1323283 : Blo 1174404 1323283 := bstep (se 1 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 1323283 = 1984925) B1984925
theorem B1175843 : Blo 1174404 1175843 := bstep (se 1 (by rfl) ⟨881882, by rfl⟩ : syracuseStep 1175843 = 1763765) B1763765
theorem B1487155 : Blo 1174404 1487155 := bstep (se 1 (by rfl) ⟨1115366, by rfl⟩ : syracuseStep 1487155 = 2230733) B2230733
theorem B1175859 : Blo 1174404 1175859 := bstep (se 1 (by rfl) ⟨881894, by rfl⟩ : syracuseStep 1175859 = 1763789) B1763789
theorem B1175875 : Blo 1174404 1175875 := bstep (se 1 (by rfl) ⟨881906, by rfl⟩ : syracuseStep 1175875 = 1763813) B1763813
theorem B6787405 : Blo 1174404 6787405 := bstep (se 3 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 6787405 = 2545277) B2545277
theorem B1175891 : Blo 1174404 1175891 := bstep (se 1 (by rfl) ⟨881918, by rfl⟩ : syracuseStep 1175891 = 1763837) B1763837
theorem B1175907 : Blo 1174404 1175907 := bstep (se 1 (by rfl) ⟨881930, by rfl⟩ : syracuseStep 1175907 = 1763861) B1763861
theorem B1175923 : Blo 1174404 1175923 := bstep (se 1 (by rfl) ⟨881942, by rfl⟩ : syracuseStep 1175923 = 1763885) B1763885
theorem B1175939 : Blo 1174404 1175939 := bstep (se 1 (by rfl) ⟨881954, by rfl⟩ : syracuseStep 1175939 = 1763909) B1763909
theorem B3346829 : Blo 1174404 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B1487251 : Blo 1174404 1487251 := bstep (se 1 (by rfl) ⟨1115438, by rfl⟩ : syracuseStep 1487251 = 2230877) B2230877
theorem B1175955 : Blo 1174404 1175955 := bstep (se 1 (by rfl) ⟨881966, by rfl⟩ : syracuseStep 1175955 = 1763933) B1763933
theorem B1175971 : Blo 1174404 1175971 := bstep (se 1 (by rfl) ⟨881978, by rfl⟩ : syracuseStep 1175971 = 1763957) B1763957
theorem B1323427 : Blo 1174404 1323427 := bstep (se 1 (by rfl) ⟨992570, by rfl⟩ : syracuseStep 1323427 = 1985141) B1985141
theorem B1175987 : Blo 1174404 1175987 := bstep (se 1 (by rfl) ⟨881990, by rfl⟩ : syracuseStep 1175987 = 1763981) B1763981
theorem B1176003 : Blo 1174404 1176003 := bstep (se 1 (by rfl) ⟨882002, by rfl⟩ : syracuseStep 1176003 = 1764005) B1764005
theorem B3969485 : Blo 1174404 3969485 := bstep (se 3 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 3969485 = 1488557) B1488557
theorem B2822609 : Blo 1174404 2822609 := bstep (se 2 (by rfl) ⟨1058478, by rfl⟩ : syracuseStep 2822609 = 2116957) B2116957
theorem B1176019 : Blo 1174404 1176019 := bstep (se 1 (by rfl) ⟨882014, by rfl⟩ : syracuseStep 1176019 = 1764029) B1764029
theorem B5722595 : Blo 1174404 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B1176035 : Blo 1174404 1176035 := bstep (se 1 (by rfl) ⟨882026, by rfl⟩ : syracuseStep 1176035 = 1764053) B1764053
theorem B2642417 : Blo 1174404 2642417 := bstep (se 2 (by rfl) ⟨990906, by rfl⟩ : syracuseStep 2642417 = 1981813) B1981813
theorem B1176051 : Blo 1174404 1176051 := bstep (se 1 (by rfl) ⟨882038, by rfl⟩ : syracuseStep 1176051 = 1764077) B1764077
theorem B2642435 : Blo 1174404 2642435 := bstep (se 1 (by rfl) ⟨1981826, by rfl⟩ : syracuseStep 2642435 = 3963653) B3963653
theorem B1176067 : Blo 1174404 1176067 := bstep (se 1 (by rfl) ⟨882050, by rfl⟩ : syracuseStep 1176067 = 1764101) B1764101
theorem B3969539 : Blo 1174404 3969539 := bstep (se 1 (by rfl) ⟨2977154, by rfl⟩ : syracuseStep 3969539 = 5954309) B5954309
theorem B1176083 : Blo 1174404 1176083 := bstep (se 1 (by rfl) ⟨882062, by rfl⟩ : syracuseStep 1176083 = 1764125) B1764125
theorem B1176099 : Blo 1174404 1176099 := bstep (se 1 (by rfl) ⟨882074, by rfl⟩ : syracuseStep 1176099 = 1764149) B1764149
theorem B1176115 : Blo 1174404 1176115 := bstep (se 1 (by rfl) ⟨882086, by rfl⟩ : syracuseStep 1176115 = 1764173) B1764173
theorem B1176131 : Blo 1174404 1176131 := bstep (se 1 (by rfl) ⟨882098, by rfl⟩ : syracuseStep 1176131 = 1764197) B1764197
theorem B3347021 : Blo 1174404 3347021 := bstep (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) B1255133
theorem B1176147 : Blo 1174404 1176147 := bstep (se 1 (by rfl) ⟨882110, by rfl⟩ : syracuseStep 1176147 = 1764221) B1764221
theorem B1176163 : Blo 1174404 1176163 := bstep (se 1 (by rfl) ⟨882122, by rfl⟩ : syracuseStep 1176163 = 1764245) B1764245
theorem B1176179 : Blo 1174404 1176179 := bstep (se 1 (by rfl) ⟨882134, by rfl⟩ : syracuseStep 1176179 = 1764269) B1764269
theorem B1176195 : Blo 1174404 1176195 := bstep (se 1 (by rfl) ⟨882146, by rfl⟩ : syracuseStep 1176195 = 1764293) B1764293
theorem B1176211 : Blo 1174404 1176211 := bstep (se 1 (by rfl) ⟨882158, by rfl⟩ : syracuseStep 1176211 = 1764317) B1764317
theorem B1176227 : Blo 1174404 1176227 := bstep (se 1 (by rfl) ⟨882170, by rfl⟩ : syracuseStep 1176227 = 1764341) B1764341
theorem B1176243 : Blo 1174404 1176243 := bstep (se 1 (by rfl) ⟨882182, by rfl⟩ : syracuseStep 1176243 = 1764365) B1764365
theorem B1176259 : Blo 1174404 1176259 := bstep (se 1 (by rfl) ⟨882194, by rfl⟩ : syracuseStep 1176259 = 1764389) B1764389
theorem B1176275 : Blo 1174404 1176275 := bstep (se 1 (by rfl) ⟨882206, by rfl⟩ : syracuseStep 1176275 = 1764413) B1764413
theorem B1176291 : Blo 1174404 1176291 := bstep (se 1 (by rfl) ⟨882218, by rfl⟩ : syracuseStep 1176291 = 1764437) B1764437
theorem B1176307 : Blo 1174404 1176307 := bstep (se 1 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 1176307 = 1764461) B1764461
theorem B1176323 : Blo 1174404 1176323 := bstep (se 1 (by rfl) ⟨882242, by rfl⟩ : syracuseStep 1176323 = 1764485) B1764485
theorem B5018381 : Blo 1174404 5018381 := bstep (se 3 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 5018381 = 1881893) B1881893
theorem B2642705 : Blo 1174404 2642705 := bstep (se 2 (by rfl) ⟨991014, by rfl⟩ : syracuseStep 2642705 = 1982029) B1982029
theorem B3969809 : Blo 1174404 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B1176339 : Blo 1174404 1176339 := bstep (se 1 (by rfl) ⟨882254, by rfl⟩ : syracuseStep 1176339 = 1764509) B1764509
theorem B2642723 : Blo 1174404 2642723 := bstep (se 1 (by rfl) ⟨1982042, by rfl⟩ : syracuseStep 2642723 = 3964085) B3964085
theorem B3576611 : Blo 1174404 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B1176355 : Blo 1174404 1176355 := bstep (se 1 (by rfl) ⟨882266, by rfl⟩ : syracuseStep 1176355 = 1764533) B1764533
theorem B1176371 : Blo 1174404 1176371 := bstep (se 1 (by rfl) ⟨882278, by rfl⟩ : syracuseStep 1176371 = 1764557) B1764557
theorem B1176387 : Blo 1174404 1176387 := bstep (se 1 (by rfl) ⟨882290, by rfl⟩ : syracuseStep 1176387 = 1764581) B1764581
theorem B14299973 : Blo 1174404 14299973 := bstep (se 4 (by rfl) ⟨1340622, by rfl⟩ : syracuseStep 14299973 = 2681245) B2681245
theorem B4461389 : Blo 1174404 4461389 := bstep (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) B1673021
theorem B1176403 : Blo 1174404 1176403 := bstep (se 1 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 1176403 = 1764605) B1764605
theorem B1487747 : Blo 1174404 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B2642993 : Blo 1174404 2642993 := bstep (se 2 (by rfl) ⟨991122, by rfl⟩ : syracuseStep 2642993 = 1982245) B1982245
theorem B2643011 : Blo 1174404 2643011 := bstep (se 1 (by rfl) ⟨1982258, by rfl⟩ : syracuseStep 2643011 = 3964517) B3964517
theorem B5952689 : Blo 1174404 5952689 := bstep (se 2 (by rfl) ⟨2232258, by rfl⟩ : syracuseStep 5952689 = 4464517) B4464517
theorem B3970349 : Blo 1174404 3970349 := bstep (se 3 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 3970349 = 1488881) B1488881
theorem B13382981 : Blo 1174404 13382981 := bstep (se 4 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 13382981 = 2509309) B2509309
theorem B2643281 : Blo 1174404 2643281 := bstep (se 2 (by rfl) ⟨991230, by rfl⟩ : syracuseStep 2643281 = 1982461) B1982461
theorem B2643299 : Blo 1174404 2643299 := bstep (se 1 (by rfl) ⟨1982474, by rfl⟩ : syracuseStep 2643299 = 3964949) B3964949
theorem B4019651 : Blo 1174404 4019651 := bstep (se 1 (by rfl) ⟨3014738, by rfl⟩ : syracuseStep 4019651 = 6029477) B6029477
theorem B2823665 : Blo 1174404 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B3348013 : Blo 1174404 3348013 := bstep (se 3 (by rfl) ⟨627752, by rfl⟩ : syracuseStep 3348013 = 1255505) B1255505
theorem B3765809 : Blo 1174404 3765809 := bstep (se 2 (by rfl) ⟨1412178, by rfl⟩ : syracuseStep 3765809 = 2824357) B2824357
theorem B1488451 : Blo 1174404 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B2643569 : Blo 1174404 2643569 := bstep (se 2 (by rfl) ⟨991338, by rfl⟩ : syracuseStep 2643569 = 1982677) B1982677
theorem B6035057 : Blo 1174404 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B2643587 : Blo 1174404 2643587 := bstep (se 1 (by rfl) ⟨1982690, by rfl⟩ : syracuseStep 2643587 = 3965381) B3965381
theorem B4232845 : Blo 1174404 4232845 := bstep (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) B1587317
theorem B1488547 : Blo 1174404 1488547 := bstep (se 1 (by rfl) ⟨1116410, by rfl⟩ : syracuseStep 1488547 = 2232821) B2232821
theorem B13391729 : Blo 1174404 13391729 := bstep (se 2 (by rfl) ⟨5021898, by rfl⟩ : syracuseStep 13391729 = 10043797) B10043797
theorem B2643857 : Blo 1174404 2643857 := bstep (se 2 (by rfl) ⟨991446, by rfl⟩ : syracuseStep 2643857 = 1982893) B1982893
theorem B2643875 : Blo 1174404 2643875 := bstep (se 1 (by rfl) ⟨1982906, by rfl⟩ : syracuseStep 2643875 = 3965813) B3965813
theorem B10049507 : Blo 1174404 10049507 := bstep (se 1 (by rfl) ⟨7537130, by rfl⟩ : syracuseStep 10049507 = 15074261) B15074261
theorem B25426061 : Blo 1174404 25426061 := bstep (se 3 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 25426061 = 9534773) B9534773
theorem B2644145 : Blo 1174404 2644145 := bstep (se 2 (by rfl) ⟨991554, by rfl⟩ : syracuseStep 2644145 = 1983109) B1983109
theorem B2644163 : Blo 1174404 2644163 := bstep (se 1 (by rfl) ⟨1983122, by rfl⟩ : syracuseStep 2644163 = 3966245) B3966245
theorem B2824579 : Blo 1174404 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B3766733 : Blo 1174404 3766733 := bstep (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) B1412525
theorem B2644433 : Blo 1174404 2644433 := bstep (se 2 (by rfl) ⟨991662, by rfl⟩ : syracuseStep 2644433 = 1983325) B1983325
theorem B2644451 : Blo 1174404 2644451 := bstep (se 1 (by rfl) ⟨1983338, by rfl⟩ : syracuseStep 2644451 = 3966677) B3966677
theorem B2546147 : Blo 1174404 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B1587745 : Blo 1174404 1587745 := bstep (se 2 (by rfl) ⟨595404, by rfl⟩ : syracuseStep 1587745 = 1190809) B1190809
theorem B5651021 : Blo 1174404 5651021 := bstep (se 3 (by rfl) ⟨1059566, by rfl⟩ : syracuseStep 5651021 = 2119133) B2119133
theorem B5954147 : Blo 1174404 5954147 := bstep (se 1 (by rfl) ⟨4465610, by rfl⟩ : syracuseStep 5954147 = 8931221) B8931221
theorem B4291213 : Blo 1174404 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B3766925 : Blo 1174404 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B8043235 : Blo 1174404 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B2644721 : Blo 1174404 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B1882867 : Blo 1174404 1882867 := bstep (se 1 (by rfl) ⟨1412150, by rfl⟩ : syracuseStep 1882867 = 2824301) B2824301
theorem B2644739 : Blo 1174404 2644739 := bstep (se 1 (by rfl) ⟨1983554, by rfl⟩ : syracuseStep 2644739 = 3967109) B3967109
theorem B5438285 : Blo 1174404 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B3963761 : Blo 1174404 3963761 := bstep (se 2 (by rfl) ⟨1486410, by rfl⟩ : syracuseStep 3963761 = 2972821) B2972821
theorem B5364643 : Blo 1174404 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B2382851 : Blo 1174404 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B2645009 : Blo 1174404 2645009 := bstep (se 2 (by rfl) ⟨991878, by rfl⟩ : syracuseStep 2645009 = 1983757) B1983757
theorem B2645027 : Blo 1174404 2645027 := bstep (se 1 (by rfl) ⟨1983770, by rfl⟩ : syracuseStep 2645027 = 3967541) B3967541
theorem B4242509 : Blo 1174404 4242509 := bstep (se 3 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 4242509 = 1590941) B1590941
theorem B1588307 : Blo 1174404 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B2972771 : Blo 1174404 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B6438001 : Blo 1174404 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B1883315 : Blo 1174404 1883315 := bstep (se 1 (by rfl) ⟨1412486, by rfl⟩ : syracuseStep 1883315 = 2824973) B2824973
theorem B21445859 : Blo 1174404 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B3349745 : Blo 1174404 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B2972963 : Blo 1174404 2972963 := bstep (se 1 (by rfl) ⟨2229722, by rfl⟩ : syracuseStep 2972963 = 4459445) B4459445
theorem B2645297 : Blo 1174404 2645297 := bstep (se 2 (by rfl) ⟨991986, by rfl⟩ : syracuseStep 2645297 = 1983973) B1983973
theorem B2645315 : Blo 1174404 2645315 := bstep (se 1 (by rfl) ⟨1983986, by rfl⟩ : syracuseStep 2645315 = 3967973) B3967973
theorem B3964301 : Blo 1174404 3964301 := bstep (se 3 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 3964301 = 1486613) B1486613
theorem B5954957 : Blo 1174404 5954957 := bstep (se 3 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 5954957 = 2233109) B2233109
theorem B5807537 : Blo 1174404 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B3349937 : Blo 1174404 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B3964355 : Blo 1174404 3964355 := bstep (se 1 (by rfl) ⟨2973266, by rfl⟩ : syracuseStep 3964355 = 5946533) B5946533
theorem B1981921 : Blo 1174404 1981921 := bstep (se 2 (by rfl) ⟨743220, by rfl⟩ : syracuseStep 1981921 = 1486441) B1486441
theorem B1981955 : Blo 1174404 1981955 := bstep (se 1 (by rfl) ⟨1486466, by rfl⟩ : syracuseStep 1981955 = 2972933) B2972933
theorem B2383409 : Blo 1174404 2383409 := bstep (se 2 (by rfl) ⟨893778, by rfl⟩ : syracuseStep 2383409 = 1787557) B1787557
theorem B2645585 : Blo 1174404 2645585 := bstep (se 2 (by rfl) ⟨992094, by rfl⟩ : syracuseStep 2645585 = 1984189) B1984189
theorem B2645603 : Blo 1174404 2645603 := bstep (se 1 (by rfl) ⟨1984202, by rfl⟩ : syracuseStep 2645603 = 3968405) B3968405
theorem B21462641 : Blo 1174404 21462641 := bstep (se 2 (by rfl) ⟨8048490, by rfl⟩ : syracuseStep 21462641 = 16096981) B16096981
theorem B1982083 : Blo 1174404 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B2383523 : Blo 1174404 2383523 := bstep (se 1 (by rfl) ⟨1787642, by rfl⟩ : syracuseStep 2383523 = 3575285) B3575285
theorem B4464305 : Blo 1174404 4464305 := bstep (se 2 (by rfl) ⟨1674114, by rfl⟩ : syracuseStep 4464305 = 3348229) B3348229
theorem B7528133 : Blo 1174404 7528133 := bstep (se 4 (by rfl) ⟨705762, by rfl⟩ : syracuseStep 7528133 = 1411525) B1411525
theorem B3964625 : Blo 1174404 3964625 := bstep (se 2 (by rfl) ⟨1486734, by rfl⟩ : syracuseStep 3964625 = 2973469) B2973469
theorem B1883873 : Blo 1174404 1883873 := bstep (se 2 (by rfl) ⟨706452, by rfl⟩ : syracuseStep 1883873 = 1412905) B1412905
theorem B1982225 : Blo 1174404 1982225 := bstep (se 2 (by rfl) ⟨743334, by rfl⟩ : syracuseStep 1982225 = 1486669) B1486669
theorem B5021489 : Blo 1174404 5021489 := bstep (se 2 (by rfl) ⟨1883058, by rfl⟩ : syracuseStep 5021489 = 3766117) B3766117
theorem B1695553 : Blo 1174404 1695553 := bstep (se 2 (by rfl) ⟨635832, by rfl⟩ : syracuseStep 1695553 = 1271665) B1271665
theorem B2645873 : Blo 1174404 2645873 := bstep (se 2 (by rfl) ⟨992202, by rfl⟩ : syracuseStep 2645873 = 1984405) B1984405
theorem B2645891 : Blo 1174404 2645891 := bstep (se 1 (by rfl) ⟨1984418, by rfl⟩ : syracuseStep 2645891 = 3968837) B3968837
theorem B1982353 : Blo 1174404 1982353 := bstep (se 2 (by rfl) ⟨743382, by rfl⟩ : syracuseStep 1982353 = 1486765) B1486765
theorem B1982387 : Blo 1174404 1982387 := bstep (se 1 (by rfl) ⟨1486790, by rfl⟩ : syracuseStep 1982387 = 2973581) B2973581
theorem B1884097 : Blo 1174404 1884097 := bstep (se 2 (by rfl) ⟨706536, by rfl⟩ : syracuseStep 1884097 = 1413073) B1413073
theorem B5644237 : Blo 1174404 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B6692813 : Blo 1174404 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B2646017 : Blo 1174404 2646017 := bstep (se 2 (by rfl) ⟨992256, by rfl⟩ : syracuseStep 2646017 = 1984513) B1984513
theorem B5021747 : Blo 1174404 5021747 := bstep (se 1 (by rfl) ⟨3766310, by rfl⟩ : syracuseStep 5021747 = 7532621) B7532621
theorem B3965003 : Blo 1174404 3965003 := bstep (se 1 (by rfl) ⟨2973752, by rfl⟩ : syracuseStep 3965003 = 5947505) B5947505
theorem B10715267 : Blo 1174404 10715267 := bstep (se 1 (by rfl) ⟨8036450, by rfl⟩ : syracuseStep 10715267 = 16072901) B16072901
theorem B1982603 : Blo 1174404 1982603 := bstep (se 1 (by rfl) ⟨1486952, by rfl⟩ : syracuseStep 1982603 = 2973905) B2973905
theorem B4464791 : Blo 1174404 4464791 := bstep (se 1 (by rfl) ⟨3348593, by rfl⟩ : syracuseStep 4464791 = 6697187) B6697187
theorem B38109365 : Blo 1174404 38109365 := bstep (se 5 (by rfl) ⟨1786376, by rfl⟩ : syracuseStep 38109365 = 3572753) B3572753
theorem B2646233 : Blo 1174404 2646233 := bstep (se 2 (by rfl) ⟨992337, by rfl⟩ : syracuseStep 2646233 = 1984675) B1984675
theorem B4235485 : Blo 1174404 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B1982731 : Blo 1174404 1982731 := bstep (se 1 (by rfl) ⟨1487048, by rfl⟩ : syracuseStep 1982731 = 2974097) B2974097
theorem B2646323 : Blo 1174404 2646323 := bstep (se 1 (by rfl) ⟨1984742, by rfl⟩ : syracuseStep 2646323 = 3969485) B3969485
theorem B1761611 : Blo 1174404 1761611 := bstep (se 1 (by rfl) ⟨1321208, by rfl⟩ : syracuseStep 1761611 = 2642417) B2642417
theorem B1761623 : Blo 1174404 1761623 := bstep (se 1 (by rfl) ⟨1321217, by rfl⟩ : syracuseStep 1761623 = 2642435) B2642435
theorem B3965273 : Blo 1174404 3965273 := bstep (se 2 (by rfl) ⟨1486977, by rfl⟩ : syracuseStep 3965273 = 2973955) B2973955
theorem B2646359 : Blo 1174404 2646359 := bstep (se 1 (by rfl) ⟨1984769, by rfl⟩ : syracuseStep 2646359 = 3969539) B3969539
theorem B4464989 : Blo 1174404 4464989 := bstep (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) B1674371
theorem B19333475 : Blo 1174404 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B17170805 : Blo 1174404 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B1761689 : Blo 1174404 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B1982873 : Blo 1174404 1982873 := bstep (se 2 (by rfl) ⟨743577, by rfl⟩ : syracuseStep 1982873 = 1487155) B1487155
theorem B3572171 : Blo 1174404 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B2146775 : Blo 1174404 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B1761803 : Blo 1174404 1761803 := bstep (se 1 (by rfl) ⟨1321352, by rfl⟩ : syracuseStep 1761803 = 2642705) B2642705
theorem B2646539 : Blo 1174404 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B1761815 : Blo 1174404 1761815 := bstep (se 1 (by rfl) ⟨1321361, by rfl⟩ : syracuseStep 1761815 = 2642723) B2642723
theorem B2384407 : Blo 1174404 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B1983001 : Blo 1174404 1983001 := bstep (se 2 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 1983001 = 1487251) B1487251
theorem B2974259 : Blo 1174404 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B2646593 : Blo 1174404 2646593 := bstep (se 2 (by rfl) ⟨992472, by rfl⟩ : syracuseStep 2646593 = 1984945) B1984945
theorem B1761881 : Blo 1174404 1761881 := bstep (se 2 (by rfl) ⟨660705, by rfl⟩ : syracuseStep 1761881 = 1321411) B1321411
theorem B1761995 : Blo 1174404 1761995 := bstep (se 1 (by rfl) ⟨1321496, by rfl⟩ : syracuseStep 1761995 = 2642993) B2642993
theorem B1762007 : Blo 1174404 1762007 := bstep (se 1 (by rfl) ⟨1321505, by rfl⟩ : syracuseStep 1762007 = 2643011) B2643011
theorem B6349529 : Blo 1174404 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B1762073 : Blo 1174404 1762073 := bstep (se 2 (by rfl) ⟨660777, by rfl⟩ : syracuseStep 1762073 = 1321555) B1321555
theorem B2646809 : Blo 1174404 2646809 := bstep (se 2 (by rfl) ⟨992553, by rfl⟩ : syracuseStep 2646809 = 1985107) B1985107
theorem B2974553 : Blo 1174404 2974553 := bstep (se 2 (by rfl) ⟨1115457, by rfl⟩ : syracuseStep 2974553 = 2230915) B2230915
theorem B2646899 : Blo 1174404 2646899 := bstep (se 1 (by rfl) ⟨1985174, by rfl⟩ : syracuseStep 2646899 = 3970349) B3970349
theorem B8921987 : Blo 1174404 8921987 := bstep (se 1 (by rfl) ⟨6691490, by rfl⟩ : syracuseStep 8921987 = 13382981) B13382981
theorem B1762187 : Blo 1174404 1762187 := bstep (se 1 (by rfl) ⟨1321640, by rfl⟩ : syracuseStep 1762187 = 2643281) B2643281
theorem B1762199 : Blo 1174404 1762199 := bstep (se 1 (by rfl) ⟨1321649, by rfl⟩ : syracuseStep 1762199 = 2643299) B2643299
theorem B2679767 : Blo 1174404 2679767 := bstep (se 1 (by rfl) ⟨2009825, by rfl⟩ : syracuseStep 2679767 = 4019651) B4019651
theorem B1762265 : Blo 1174404 1762265 := bstep (se 2 (by rfl) ⟨660849, by rfl⟩ : syracuseStep 1762265 = 1321699) B1321699
theorem B3965975 : Blo 1174404 3965975 := bstep (se 1 (by rfl) ⟨2974481, by rfl⟩ : syracuseStep 3965975 = 5948963) B5948963
theorem B1762379 : Blo 1174404 1762379 := bstep (se 1 (by rfl) ⟨1321784, by rfl⟩ : syracuseStep 1762379 = 2643569) B2643569
theorem B4023371 : Blo 1174404 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B1762391 : Blo 1174404 1762391 := bstep (se 1 (by rfl) ⟨1321793, by rfl⟩ : syracuseStep 1762391 = 2643587) B2643587
theorem B1983575 : Blo 1174404 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B1762457 : Blo 1174404 1762457 := bstep (se 2 (by rfl) ⟨660921, by rfl⟩ : syracuseStep 1762457 = 1321843) B1321843
theorem B1983703 : Blo 1174404 1983703 := bstep (se 1 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 1983703 = 2975555) B2975555
theorem B7152857 : Blo 1174404 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B1762571 : Blo 1174404 1762571 := bstep (se 1 (by rfl) ⟨1321928, by rfl⟩ : syracuseStep 1762571 = 2643857) B2643857
theorem B1762583 : Blo 1174404 1762583 := bstep (se 1 (by rfl) ⟨1321937, by rfl⟩ : syracuseStep 1762583 = 2643875) B2643875
theorem B7529773 : Blo 1174404 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B1762649 : Blo 1174404 1762649 := bstep (se 2 (by rfl) ⟨660993, by rfl⟩ : syracuseStep 1762649 = 1321987) B1321987
theorem B5727581 : Blo 1174404 5727581 := bstep (se 3 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 5727581 = 2147843) B2147843
theorem B16950707 : Blo 1174404 16950707 := bstep (se 1 (by rfl) ⟨12713030, by rfl⟩ : syracuseStep 16950707 = 25426061) B25426061
theorem B2229707 : Blo 1174404 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B1762763 : Blo 1174404 1762763 := bstep (se 1 (by rfl) ⟨1322072, by rfl⟩ : syracuseStep 1762763 = 2644145) B2644145
theorem B1762775 : Blo 1174404 1762775 := bstep (se 1 (by rfl) ⟨1322081, by rfl⟩ : syracuseStep 1762775 = 2644163) B2644163
theorem B2229761 : Blo 1174404 2229761 := bstep (se 2 (by rfl) ⟨836160, by rfl⟩ : syracuseStep 2229761 = 1672321) B1672321
theorem B1762841 : Blo 1174404 1762841 := bstep (se 2 (by rfl) ⟨661065, by rfl⟩ : syracuseStep 1762841 = 1322131) B1322131
theorem B3966515 : Blo 1174404 3966515 := bstep (se 1 (by rfl) ⟨2974886, by rfl⟩ : syracuseStep 3966515 = 5949773) B5949773
theorem B9045569 : Blo 1174404 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B40699523 : Blo 1174404 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B1762955 : Blo 1174404 1762955 := bstep (se 1 (by rfl) ⟨1322216, by rfl⟩ : syracuseStep 1762955 = 2644433) B2644433
theorem B1762967 : Blo 1174404 1762967 := bstep (se 1 (by rfl) ⟨1322225, by rfl⟩ : syracuseStep 1762967 = 2644451) B2644451
theorem B1697431 : Blo 1174404 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B10045133 : Blo 1174404 10045133 := bstep (se 3 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 10045133 = 3766925) B3766925
theorem B1763033 : Blo 1174404 1763033 := bstep (se 2 (by rfl) ⟨661137, by rfl⟩ : syracuseStep 1763033 = 1322275) B1322275
theorem B3966785 : Blo 1174404 3966785 := bstep (se 2 (by rfl) ⟨1487544, by rfl⟩ : syracuseStep 3966785 = 2975089) B2975089
theorem B18351937 : Blo 1174404 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B1763147 : Blo 1174404 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B1984331 : Blo 1174404 1984331 := bstep (se 1 (by rfl) ⟨1488248, by rfl⟩ : syracuseStep 1984331 = 2976497) B2976497
theorem B1763159 : Blo 1174404 1763159 := bstep (se 1 (by rfl) ⟨1322369, by rfl⟩ : syracuseStep 1763159 = 2644739) B2644739
theorem B1763225 : Blo 1174404 1763225 := bstep (se 2 (by rfl) ⟨661209, by rfl⟩ : syracuseStep 1763225 = 1322419) B1322419
theorem B1984459 : Blo 1174404 1984459 := bstep (se 1 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 1984459 = 2976689) B2976689
theorem B1763339 : Blo 1174404 1763339 := bstep (se 1 (by rfl) ⟨1322504, by rfl⟩ : syracuseStep 1763339 = 2645009) B2645009
theorem B2508823 : Blo 1174404 2508823 := bstep (se 1 (by rfl) ⟨1881617, by rfl⟩ : syracuseStep 2508823 = 3763235) B3763235
theorem B1763351 : Blo 1174404 1763351 := bstep (se 1 (by rfl) ⟨1322513, by rfl⟩ : syracuseStep 1763351 = 2645027) B2645027
theorem B2828339 : Blo 1174404 2828339 := bstep (se 1 (by rfl) ⟨2121254, by rfl⟩ : syracuseStep 2828339 = 4242509) B4242509
theorem B76236875 : Blo 1174404 76236875 := bstep (se 1 (by rfl) ⟨57177656, by rfl⟩ : syracuseStep 76236875 = 114355313) B114355313
theorem B1763417 : Blo 1174404 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B1984601 : Blo 1174404 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B1255543 : Blo 1174404 1255543 := bstep (se 1 (by rfl) ⟨941657, by rfl⟩ : syracuseStep 1255543 = 1883315) B1883315
theorem B14297239 : Blo 1174404 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B1763531 : Blo 1174404 1763531 := bstep (se 1 (by rfl) ⟨1322648, by rfl⟩ : syracuseStep 1763531 = 2645297) B2645297
theorem B1763543 : Blo 1174404 1763543 := bstep (se 1 (by rfl) ⟨1322657, by rfl⟩ : syracuseStep 1763543 = 2645315) B2645315
theorem B1984729 : Blo 1174404 1984729 := bstep (se 2 (by rfl) ⟨744273, by rfl⟩ : syracuseStep 1984729 = 1488547) B1488547
theorem B1763609 : Blo 1174404 1763609 := bstep (se 2 (by rfl) ⟨661353, by rfl⟩ : syracuseStep 1763609 = 1322707) B1322707
theorem B4352321 : Blo 1174404 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B1321303 : Blo 1174404 1321303 := bstep (se 1 (by rfl) ⟨990977, by rfl⟩ : syracuseStep 1321303 = 1981955) B1981955
theorem B3967325 : Blo 1174404 3967325 := bstep (se 3 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 3967325 = 1487747) B1487747
theorem B1763723 : Blo 1174404 1763723 := bstep (se 1 (by rfl) ⟨1322792, by rfl⟩ : syracuseStep 1763723 = 2645585) B2645585
theorem B2230679 : Blo 1174404 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B1763735 : Blo 1174404 1763735 := bstep (se 1 (by rfl) ⟨1322801, by rfl⟩ : syracuseStep 1763735 = 2645603) B2645603
theorem B2263447 : Blo 1174404 2263447 := bstep (se 1 (by rfl) ⟨1697585, by rfl⟩ : syracuseStep 2263447 = 3395171) B3395171
theorem B2976203 : Blo 1174404 2976203 := bstep (se 1 (by rfl) ⟨2232152, by rfl⟩ : syracuseStep 2976203 = 4464305) B4464305
theorem B1763801 : Blo 1174404 1763801 := bstep (se 2 (by rfl) ⟨661425, by rfl⟩ : syracuseStep 1763801 = 1322851) B1322851
theorem B1255915 : Blo 1174404 1255915 := bstep (se 1 (by rfl) ⟨941936, by rfl⟩ : syracuseStep 1255915 = 1883873) B1883873
theorem B1321483 : Blo 1174404 1321483 := bstep (se 1 (by rfl) ⟨991112, by rfl⟩ : syracuseStep 1321483 = 1982225) B1982225
theorem B3344971 : Blo 1174404 3344971 := bstep (se 1 (by rfl) ⟨2508728, by rfl⟩ : syracuseStep 3344971 = 5017457) B5017457
theorem B1763915 : Blo 1174404 1763915 := bstep (se 1 (by rfl) ⟨1322936, by rfl⟩ : syracuseStep 1763915 = 2645873) B2645873
theorem B1763927 : Blo 1174404 1763927 := bstep (se 1 (by rfl) ⟨1322945, by rfl⟩ : syracuseStep 1763927 = 2645891) B2645891
theorem B1321591 : Blo 1174404 1321591 := bstep (se 1 (by rfl) ⟨991193, by rfl⟩ : syracuseStep 1321591 = 1982387) B1982387
theorem B1763993 : Blo 1174404 1763993 := bstep (se 2 (by rfl) ⟨661497, by rfl⟩ : syracuseStep 1763993 = 1322995) B1322995
theorem B5024429 : Blo 1174404 5024429 := bstep (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) B1884161
theorem B1190647 : Blo 1174404 1190647 := bstep (se 1 (by rfl) ⟨892985, by rfl⟩ : syracuseStep 1190647 = 1785971) B1785971
theorem B1764107 : Blo 1174404 1764107 := bstep (se 1 (by rfl) ⟨1323080, by rfl⟩ : syracuseStep 1764107 = 2646161) B2646161
theorem B1764119 : Blo 1174404 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B1321771 : Blo 1174404 1321771 := bstep (se 1 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 1321771 = 1982657) B1982657
theorem B2509643 : Blo 1174404 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B1764185 : Blo 1174404 1764185 := bstep (se 2 (by rfl) ⟨661569, by rfl⟩ : syracuseStep 1764185 = 1323139) B1323139
theorem B3345245 : Blo 1174404 3345245 := bstep (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) B1254467
theorem B1174411 : Blo 1174404 1174411 := bstep (se 1 (by rfl) ⟨880808, by rfl⟩ : syracuseStep 1174411 = 1761617) B1761617
theorem B1174423 : Blo 1174404 1174423 := bstep (se 1 (by rfl) ⟨880817, by rfl⟩ : syracuseStep 1174423 = 1761635) B1761635
theorem B1321879 : Blo 1174404 1321879 := bstep (se 1 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 1321879 = 1982819) B1982819
theorem B1174443 : Blo 1174404 1174443 := bstep (se 1 (by rfl) ⟨880832, by rfl⟩ : syracuseStep 1174443 = 1761665) B1761665
theorem B2231219 : Blo 1174404 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B1174455 : Blo 1174404 1174455 := bstep (se 1 (by rfl) ⟨880841, by rfl⟩ : syracuseStep 1174455 = 1761683) B1761683
theorem B1174475 : Blo 1174404 1174475 := bstep (se 1 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 1174475 = 1761713) B1761713
theorem B1764299 : Blo 1174404 1764299 := bstep (se 1 (by rfl) ⟨1323224, by rfl⟩ : syracuseStep 1764299 = 2646449) B2646449
theorem B1174487 : Blo 1174404 1174487 := bstep (se 1 (by rfl) ⟨880865, by rfl⟩ : syracuseStep 1174487 = 1761731) B1761731
theorem B1764311 : Blo 1174404 1764311 := bstep (se 1 (by rfl) ⟨1323233, by rfl⟩ : syracuseStep 1764311 = 2646467) B2646467
theorem B1174507 : Blo 1174404 1174507 := bstep (se 1 (by rfl) ⟨880880, by rfl⟩ : syracuseStep 1174507 = 1761761) B1761761
theorem B1174519 : Blo 1174404 1174519 := bstep (se 1 (by rfl) ⟨880889, by rfl⟩ : syracuseStep 1174519 = 1761779) B1761779
theorem B1174539 : Blo 1174404 1174539 := bstep (se 1 (by rfl) ⟨880904, by rfl⟩ : syracuseStep 1174539 = 1761809) B1761809
theorem B1174551 : Blo 1174404 1174551 := bstep (se 1 (by rfl) ⟨880913, by rfl⟩ : syracuseStep 1174551 = 1761827) B1761827
theorem B1764377 : Blo 1174404 1764377 := bstep (se 2 (by rfl) ⟨661641, by rfl⟩ : syracuseStep 1764377 = 1323283) B1323283
theorem B1174571 : Blo 1174404 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B4238381 : Blo 1174404 4238381 := bstep (se 3 (by rfl) ⟨794696, by rfl⟩ : syracuseStep 4238381 = 1589393) B1589393
theorem B1174583 : Blo 1174404 1174583 := bstep (se 1 (by rfl) ⟨880937, by rfl⟩ : syracuseStep 1174583 = 1761875) B1761875
theorem B1174603 : Blo 1174404 1174603 := bstep (se 1 (by rfl) ⟨880952, by rfl⟩ : syracuseStep 1174603 = 1761905) B1761905
theorem B1322059 : Blo 1174404 1322059 := bstep (se 1 (by rfl) ⟨991544, by rfl⟩ : syracuseStep 1322059 = 1983089) B1983089
theorem B1174615 : Blo 1174404 1174615 := bstep (se 1 (by rfl) ⟨880961, by rfl⟩ : syracuseStep 1174615 = 1761923) B1761923
theorem B10185821 : Blo 1174404 10185821 := bstep (se 3 (by rfl) ⟨1909841, by rfl⟩ : syracuseStep 10185821 = 3819683) B3819683
theorem B1174635 : Blo 1174404 1174635 := bstep (se 1 (by rfl) ⟨880976, by rfl⟩ : syracuseStep 1174635 = 1761953) B1761953
theorem B1174647 : Blo 1174404 1174647 := bstep (se 1 (by rfl) ⟨880985, by rfl⟩ : syracuseStep 1174647 = 1761971) B1761971
theorem B1174667 : Blo 1174404 1174667 := bstep (se 1 (by rfl) ⟨881000, by rfl⟩ : syracuseStep 1174667 = 1762001) B1762001
theorem B1764491 : Blo 1174404 1764491 := bstep (se 1 (by rfl) ⟨1323368, by rfl⟩ : syracuseStep 1764491 = 2646737) B2646737
theorem B1174679 : Blo 1174404 1174679 := bstep (se 1 (by rfl) ⟨881009, by rfl⟩ : syracuseStep 1174679 = 1762019) B1762019
theorem B2010263 : Blo 1174404 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B1764503 : Blo 1174404 1764503 := bstep (se 1 (by rfl) ⟨1323377, by rfl⟩ : syracuseStep 1764503 = 2646755) B2646755
theorem B1174699 : Blo 1174404 1174699 := bstep (se 1 (by rfl) ⟨881024, by rfl⟩ : syracuseStep 1174699 = 1762049) B1762049
theorem B3345587 : Blo 1174404 3345587 := bstep (se 1 (by rfl) ⟨2509190, by rfl⟩ : syracuseStep 3345587 = 5018381) B5018381
theorem B1174711 : Blo 1174404 1174711 := bstep (se 1 (by rfl) ⟨881033, by rfl⟩ : syracuseStep 1174711 = 1762067) B1762067
theorem B1322167 : Blo 1174404 1322167 := bstep (se 1 (by rfl) ⟨991625, by rfl⟩ : syracuseStep 1322167 = 1983251) B1983251
theorem B1174731 : Blo 1174404 1174731 := bstep (se 1 (by rfl) ⟨881048, by rfl⟩ : syracuseStep 1174731 = 1762097) B1762097
theorem B1174743 : Blo 1174404 1174743 := bstep (se 1 (by rfl) ⟨881057, by rfl⟩ : syracuseStep 1174743 = 1762115) B1762115
theorem B1764569 : Blo 1174404 1764569 := bstep (se 2 (by rfl) ⟨661713, by rfl⟩ : syracuseStep 1764569 = 1323427) B1323427
theorem B1174763 : Blo 1174404 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B1174775 : Blo 1174404 1174775 := bstep (se 1 (by rfl) ⟨881081, by rfl⟩ : syracuseStep 1174775 = 1762163) B1762163
theorem B1174795 : Blo 1174404 1174795 := bstep (se 1 (by rfl) ⟨881096, by rfl⟩ : syracuseStep 1174795 = 1762193) B1762193
theorem B1174807 : Blo 1174404 1174807 := bstep (se 1 (by rfl) ⟨881105, by rfl⟩ : syracuseStep 1174807 = 1762211) B1762211
theorem B1174827 : Blo 1174404 1174827 := bstep (se 1 (by rfl) ⟨881120, by rfl⟩ : syracuseStep 1174827 = 1762241) B1762241
theorem B1174839 : Blo 1174404 1174839 := bstep (se 1 (by rfl) ⟨881129, by rfl⟩ : syracuseStep 1174839 = 1762259) B1762259
theorem B1174859 : Blo 1174404 1174859 := bstep (se 1 (by rfl) ⟨881144, by rfl⟩ : syracuseStep 1174859 = 1762289) B1762289
theorem B1174871 : Blo 1174404 1174871 := bstep (se 1 (by rfl) ⟨881153, by rfl⟩ : syracuseStep 1174871 = 1762307) B1762307
theorem B1174891 : Blo 1174404 1174891 := bstep (se 1 (by rfl) ⟨881168, by rfl⟩ : syracuseStep 1174891 = 1762337) B1762337
theorem B1322347 : Blo 1174404 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B1174903 : Blo 1174404 1174903 := bstep (se 1 (by rfl) ⟨881177, by rfl⟩ : syracuseStep 1174903 = 1762355) B1762355
theorem B1174923 : Blo 1174404 1174923 := bstep (se 1 (by rfl) ⟨881192, by rfl⟩ : syracuseStep 1174923 = 1762385) B1762385
theorem B1174935 : Blo 1174404 1174935 := bstep (se 1 (by rfl) ⟨881201, by rfl⟩ : syracuseStep 1174935 = 1762403) B1762403
theorem B2977175 : Blo 1174404 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B2231705 : Blo 1174404 2231705 := bstep (se 2 (by rfl) ⟨836889, by rfl⟩ : syracuseStep 2231705 = 1673779) B1673779
theorem B1174955 : Blo 1174404 1174955 := bstep (se 1 (by rfl) ⟨881216, by rfl⟩ : syracuseStep 1174955 = 1762433) B1762433
theorem B1174967 : Blo 1174404 1174967 := bstep (se 1 (by rfl) ⟨881225, by rfl⟩ : syracuseStep 1174967 = 1762451) B1762451
theorem B1174987 : Blo 1174404 1174987 := bstep (se 1 (by rfl) ⟨881240, by rfl⟩ : syracuseStep 1174987 = 1762481) B1762481
theorem B3968459 : Blo 1174404 3968459 := bstep (se 1 (by rfl) ⟨2976344, by rfl⟩ : syracuseStep 3968459 = 5952689) B5952689
theorem B1174999 : Blo 1174404 1174999 := bstep (se 1 (by rfl) ⟨881249, by rfl⟩ : syracuseStep 1174999 = 1762499) B1762499
theorem B1322455 : Blo 1174404 1322455 := bstep (se 1 (by rfl) ⟨991841, by rfl⟩ : syracuseStep 1322455 = 1983683) B1983683
theorem B1175019 : Blo 1174404 1175019 := bstep (se 1 (by rfl) ⟨881264, by rfl⟩ : syracuseStep 1175019 = 1762529) B1762529
theorem B1175031 : Blo 1174404 1175031 := bstep (se 1 (by rfl) ⟨881273, by rfl⟩ : syracuseStep 1175031 = 1762547) B1762547
theorem B1175051 : Blo 1174404 1175051 := bstep (se 1 (by rfl) ⟨881288, by rfl⟩ : syracuseStep 1175051 = 1762577) B1762577
theorem B5721617 : Blo 1174404 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B30518801 : Blo 1174404 30518801 := bstep (se 2 (by rfl) ⟨11444550, by rfl⟩ : syracuseStep 30518801 = 22889101) B22889101
theorem B1175063 : Blo 1174404 1175063 := bstep (se 1 (by rfl) ⟨881297, by rfl⟩ : syracuseStep 1175063 = 1762595) B1762595
theorem B1175083 : Blo 1174404 1175083 := bstep (se 1 (by rfl) ⟨881312, by rfl⟩ : syracuseStep 1175083 = 1762625) B1762625
theorem B1175095 : Blo 1174404 1175095 := bstep (se 1 (by rfl) ⟨881321, by rfl⟩ : syracuseStep 1175095 = 1762643) B1762643
theorem B1175115 : Blo 1174404 1175115 := bstep (se 1 (by rfl) ⟨881336, by rfl⟩ : syracuseStep 1175115 = 1762673) B1762673
theorem B1175127 : Blo 1174404 1175127 := bstep (se 1 (by rfl) ⟨881345, by rfl⟩ : syracuseStep 1175127 = 1762691) B1762691
theorem B5951069 : Blo 1174404 5951069 := bstep (se 3 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 5951069 = 2231651) B2231651
theorem B1175147 : Blo 1174404 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B1175159 : Blo 1174404 1175159 := bstep (se 1 (by rfl) ⟨881369, by rfl⟩ : syracuseStep 1175159 = 1762739) B1762739
theorem B1175179 : Blo 1174404 1175179 := bstep (se 1 (by rfl) ⟨881384, by rfl⟩ : syracuseStep 1175179 = 1762769) B1762769
theorem B1322635 : Blo 1174404 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B1175191 : Blo 1174404 1175191 := bstep (se 1 (by rfl) ⟨881393, by rfl⟩ : syracuseStep 1175191 = 1762787) B1762787
theorem B2510489 : Blo 1174404 2510489 := bstep (se 2 (by rfl) ⟨941433, by rfl⟩ : syracuseStep 2510489 = 1882867) B1882867
theorem B1175211 : Blo 1174404 1175211 := bstep (se 1 (by rfl) ⟨881408, by rfl⟩ : syracuseStep 1175211 = 1762817) B1762817
theorem B1175223 : Blo 1174404 1175223 := bstep (se 1 (by rfl) ⟨881417, by rfl⟩ : syracuseStep 1175223 = 1762835) B1762835
theorem B1175243 : Blo 1174404 1175243 := bstep (se 1 (by rfl) ⟨881432, by rfl⟩ : syracuseStep 1175243 = 1762865) B1762865
theorem B1175255 : Blo 1174404 1175255 := bstep (se 1 (by rfl) ⟨881441, by rfl⟩ : syracuseStep 1175255 = 1762883) B1762883
theorem B3968729 : Blo 1174404 3968729 := bstep (se 2 (by rfl) ⟨1488273, by rfl⟩ : syracuseStep 3968729 = 2976547) B2976547
theorem B1175275 : Blo 1174404 1175275 := bstep (se 1 (by rfl) ⟨881456, by rfl⟩ : syracuseStep 1175275 = 1762913) B1762913
theorem B1175287 : Blo 1174404 1175287 := bstep (se 1 (by rfl) ⟨881465, by rfl⟩ : syracuseStep 1175287 = 1762931) B1762931
theorem B1322743 : Blo 1174404 1322743 := bstep (se 1 (by rfl) ⟨992057, by rfl⟩ : syracuseStep 1322743 = 1984115) B1984115
theorem B1486603 : Blo 1174404 1486603 := bstep (se 1 (by rfl) ⟨1114952, by rfl⟩ : syracuseStep 1486603 = 2229905) B2229905
theorem B1175307 : Blo 1174404 1175307 := bstep (se 1 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 1175307 = 1762961) B1762961
theorem B1175319 : Blo 1174404 1175319 := bstep (se 1 (by rfl) ⟨881489, by rfl⟩ : syracuseStep 1175319 = 1762979) B1762979
theorem B1175339 : Blo 1174404 1175339 := bstep (se 1 (by rfl) ⟨881504, by rfl⟩ : syracuseStep 1175339 = 1763009) B1763009
theorem B8933165 : Blo 1174404 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B1175351 : Blo 1174404 1175351 := bstep (se 1 (by rfl) ⟨881513, by rfl⟩ : syracuseStep 1175351 = 1763027) B1763027
theorem B1175371 : Blo 1174404 1175371 := bstep (se 1 (by rfl) ⟨881528, by rfl⟩ : syracuseStep 1175371 = 1763057) B1763057
theorem B1175383 : Blo 1174404 1175383 := bstep (se 1 (by rfl) ⟨881537, by rfl⟩ : syracuseStep 1175383 = 1763075) B1763075
theorem B1175403 : Blo 1174404 1175403 := bstep (se 1 (by rfl) ⟨881552, by rfl⟩ : syracuseStep 1175403 = 1763105) B1763105
theorem B1175415 : Blo 1174404 1175415 := bstep (se 1 (by rfl) ⟨881561, by rfl⟩ : syracuseStep 1175415 = 1763123) B1763123
theorem B1175435 : Blo 1174404 1175435 := bstep (se 1 (by rfl) ⟨881576, by rfl⟩ : syracuseStep 1175435 = 1763153) B1763153
theorem B1175447 : Blo 1174404 1175447 := bstep (se 1 (by rfl) ⟨881585, by rfl⟩ : syracuseStep 1175447 = 1763171) B1763171
theorem B1175467 : Blo 1174404 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B1322923 : Blo 1174404 1322923 := bstep (se 1 (by rfl) ⟨992192, by rfl⟩ : syracuseStep 1322923 = 1984385) B1984385
theorem B1175479 : Blo 1174404 1175479 := bstep (se 1 (by rfl) ⟨881609, by rfl⟩ : syracuseStep 1175479 = 1763219) B1763219
theorem B1175499 : Blo 1174404 1175499 := bstep (se 1 (by rfl) ⟨881624, by rfl⟩ : syracuseStep 1175499 = 1763249) B1763249
theorem B1175511 : Blo 1174404 1175511 := bstep (se 1 (by rfl) ⟨881633, by rfl⟩ : syracuseStep 1175511 = 1763267) B1763267
theorem B1175531 : Blo 1174404 1175531 := bstep (se 1 (by rfl) ⟨881648, by rfl⟩ : syracuseStep 1175531 = 1763297) B1763297
theorem B1175543 : Blo 1174404 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B1175563 : Blo 1174404 1175563 := bstep (se 1 (by rfl) ⟨881672, by rfl⟩ : syracuseStep 1175563 = 1763345) B1763345
theorem B1175575 : Blo 1174404 1175575 := bstep (se 1 (by rfl) ⟨881681, by rfl⟩ : syracuseStep 1175575 = 1763363) B1763363
theorem B1323031 : Blo 1174404 1323031 := bstep (se 1 (by rfl) ⟨992273, by rfl⟩ : syracuseStep 1323031 = 1984547) B1984547
theorem B1175595 : Blo 1174404 1175595 := bstep (se 1 (by rfl) ⟨881696, by rfl⟩ : syracuseStep 1175595 = 1763393) B1763393
theorem B1175607 : Blo 1174404 1175607 := bstep (se 1 (by rfl) ⟨881705, by rfl⟩ : syracuseStep 1175607 = 1763411) B1763411
theorem B1175627 : Blo 1174404 1175627 := bstep (se 1 (by rfl) ⟨881720, by rfl⟩ : syracuseStep 1175627 = 1763441) B1763441
theorem B1175639 : Blo 1174404 1175639 := bstep (se 1 (by rfl) ⟨881729, by rfl⟩ : syracuseStep 1175639 = 1763459) B1763459
theorem B4239449 : Blo 1174404 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B1175659 : Blo 1174404 1175659 := bstep (se 1 (by rfl) ⟨881744, by rfl⟩ : syracuseStep 1175659 = 1763489) B1763489
theorem B1175671 : Blo 1174404 1175671 := bstep (se 1 (by rfl) ⟨881753, by rfl⟩ : syracuseStep 1175671 = 1763507) B1763507
theorem B1175691 : Blo 1174404 1175691 := bstep (se 1 (by rfl) ⟨881768, by rfl⟩ : syracuseStep 1175691 = 1763537) B1763537
theorem B1175703 : Blo 1174404 1175703 := bstep (se 1 (by rfl) ⟨881777, by rfl⟩ : syracuseStep 1175703 = 1763555) B1763555
theorem B1175723 : Blo 1174404 1175723 := bstep (se 1 (by rfl) ⟨881792, by rfl⟩ : syracuseStep 1175723 = 1763585) B1763585
theorem B1175735 : Blo 1174404 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B1175755 : Blo 1174404 1175755 := bstep (se 1 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 1175755 = 1763633) B1763633
theorem B8925389 : Blo 1174404 8925389 := bstep (se 3 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 8925389 = 3347021) B3347021
theorem B1323211 : Blo 1174404 1323211 := bstep (se 1 (by rfl) ⟨992408, by rfl⟩ : syracuseStep 1323211 = 1984817) B1984817
theorem B1175767 : Blo 1174404 1175767 := bstep (se 1 (by rfl) ⟨881825, by rfl⟩ : syracuseStep 1175767 = 1763651) B1763651
theorem B1175787 : Blo 1174404 1175787 := bstep (se 1 (by rfl) ⟨881840, by rfl⟩ : syracuseStep 1175787 = 1763681) B1763681
theorem B1175799 : Blo 1174404 1175799 := bstep (se 1 (by rfl) ⟨881849, by rfl⟩ : syracuseStep 1175799 = 1763699) B1763699
theorem B1175819 : Blo 1174404 1175819 := bstep (se 1 (by rfl) ⟨881864, by rfl⟩ : syracuseStep 1175819 = 1763729) B1763729
theorem B1175831 : Blo 1174404 1175831 := bstep (se 1 (by rfl) ⟨881873, by rfl⟩ : syracuseStep 1175831 = 1763747) B1763747
theorem B1175851 : Blo 1174404 1175851 := bstep (se 1 (by rfl) ⟨881888, by rfl⟩ : syracuseStep 1175851 = 1763777) B1763777
theorem B2511155 : Blo 1174404 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B1175863 : Blo 1174404 1175863 := bstep (se 1 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 1175863 = 1763795) B1763795
theorem B1323319 : Blo 1174404 1323319 := bstep (se 1 (by rfl) ⟨992489, by rfl⟩ : syracuseStep 1323319 = 1984979) B1984979
theorem B1175883 : Blo 1174404 1175883 := bstep (se 1 (by rfl) ⟨881912, by rfl⟩ : syracuseStep 1175883 = 1763825) B1763825
theorem B1175895 : Blo 1174404 1175895 := bstep (se 1 (by rfl) ⟨881921, by rfl⟩ : syracuseStep 1175895 = 1763843) B1763843
theorem B1175915 : Blo 1174404 1175915 := bstep (se 1 (by rfl) ⟨881936, by rfl⟩ : syracuseStep 1175915 = 1763873) B1763873
theorem B1175927 : Blo 1174404 1175927 := bstep (se 1 (by rfl) ⟨881945, by rfl⟩ : syracuseStep 1175927 = 1763891) B1763891
theorem B1175947 : Blo 1174404 1175947 := bstep (se 1 (by rfl) ⟨881960, by rfl⟩ : syracuseStep 1175947 = 1763921) B1763921
theorem B1175959 : Blo 1174404 1175959 := bstep (se 1 (by rfl) ⟨881969, by rfl⟩ : syracuseStep 1175959 = 1763939) B1763939
theorem B3969431 : Blo 1174404 3969431 := bstep (se 1 (by rfl) ⟨2977073, by rfl⟩ : syracuseStep 3969431 = 5954147) B5954147
theorem B1175979 : Blo 1174404 1175979 := bstep (se 1 (by rfl) ⟨881984, by rfl⟩ : syracuseStep 1175979 = 1763969) B1763969
theorem B1175991 : Blo 1174404 1175991 := bstep (se 1 (by rfl) ⟨881993, by rfl⟩ : syracuseStep 1175991 = 1763987) B1763987
theorem B1176011 : Blo 1174404 1176011 := bstep (se 1 (by rfl) ⟨882008, by rfl⟩ : syracuseStep 1176011 = 1764017) B1764017
theorem B1176023 : Blo 1174404 1176023 := bstep (se 1 (by rfl) ⟨882017, by rfl⟩ : syracuseStep 1176023 = 1764035) B1764035
theorem B1176043 : Blo 1174404 1176043 := bstep (se 1 (by rfl) ⟨882032, by rfl⟩ : syracuseStep 1176043 = 1764065) B1764065
theorem B1176055 : Blo 1174404 1176055 := bstep (se 1 (by rfl) ⟨882041, by rfl⟩ : syracuseStep 1176055 = 1764083) B1764083
theorem B1176075 : Blo 1174404 1176075 := bstep (se 1 (by rfl) ⟨882056, by rfl⟩ : syracuseStep 1176075 = 1764113) B1764113
theorem B1176087 : Blo 1174404 1176087 := bstep (se 1 (by rfl) ⟨882065, by rfl⟩ : syracuseStep 1176087 = 1764131) B1764131
theorem B1176107 : Blo 1174404 1176107 := bstep (se 1 (by rfl) ⟨882080, by rfl⟩ : syracuseStep 1176107 = 1764161) B1764161
theorem B4461101 : Blo 1174404 4461101 := bstep (se 3 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 4461101 = 1672913) B1672913
theorem B3625523 : Blo 1174404 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B1176119 : Blo 1174404 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B2642507 : Blo 1174404 2642507 := bstep (se 1 (by rfl) ⟨1981880, by rfl⟩ : syracuseStep 2642507 = 3963761) B3963761
theorem B1176139 : Blo 1174404 1176139 := bstep (se 1 (by rfl) ⟨882104, by rfl⟩ : syracuseStep 1176139 = 1764209) B1764209
theorem B1176151 : Blo 1174404 1176151 := bstep (se 1 (by rfl) ⟨882113, by rfl⟩ : syracuseStep 1176151 = 1764227) B1764227
theorem B1340011 : Blo 1174404 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1176171 : Blo 1174404 1176171 := bstep (se 1 (by rfl) ⟨882128, by rfl⟩ : syracuseStep 1176171 = 1764257) B1764257
theorem B1176183 : Blo 1174404 1176183 := bstep (se 1 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 1176183 = 1764275) B1764275
theorem B2642561 : Blo 1174404 2642561 := bstep (se 2 (by rfl) ⟨990960, by rfl⟩ : syracuseStep 2642561 = 1981921) B1981921
theorem B1176203 : Blo 1174404 1176203 := bstep (se 1 (by rfl) ⟨882152, by rfl⟩ : syracuseStep 1176203 = 1764305) B1764305
theorem B1176215 : Blo 1174404 1176215 := bstep (se 1 (by rfl) ⟨882161, by rfl⟩ : syracuseStep 1176215 = 1764323) B1764323
theorem B1176235 : Blo 1174404 1176235 := bstep (se 1 (by rfl) ⟨882176, by rfl⟩ : syracuseStep 1176235 = 1764353) B1764353
theorem B8925875 : Blo 1174404 8925875 := bstep (se 1 (by rfl) ⟨6694406, by rfl⟩ : syracuseStep 8925875 = 13388813) B13388813
theorem B1176247 : Blo 1174404 1176247 := bstep (se 1 (by rfl) ⟨882185, by rfl⟩ : syracuseStep 1176247 = 1764371) B1764371
theorem B1176267 : Blo 1174404 1176267 := bstep (se 1 (by rfl) ⟨882200, by rfl⟩ : syracuseStep 1176267 = 1764401) B1764401
theorem B19337933 : Blo 1174404 19337933 := bstep (se 3 (by rfl) ⟨3625862, by rfl⟩ : syracuseStep 19337933 = 7251725) B7251725
theorem B1487575 : Blo 1174404 1487575 := bstep (se 1 (by rfl) ⟨1115681, by rfl⟩ : syracuseStep 1487575 = 2231363) B2231363
theorem B1176279 : Blo 1174404 1176279 := bstep (se 1 (by rfl) ⟨882209, by rfl⟩ : syracuseStep 1176279 = 1764419) B1764419
theorem B1176299 : Blo 1174404 1176299 := bstep (se 1 (by rfl) ⟨882224, by rfl⟩ : syracuseStep 1176299 = 1764449) B1764449
theorem B1176311 : Blo 1174404 1176311 := bstep (se 1 (by rfl) ⟨882233, by rfl⟩ : syracuseStep 1176311 = 1764467) B1764467
theorem B4764419 : Blo 1174404 4764419 := bstep (se 1 (by rfl) ⟨3573314, by rfl⟩ : syracuseStep 4764419 = 7146629) B7146629
theorem B1176331 : Blo 1174404 1176331 := bstep (se 1 (by rfl) ⟨882248, by rfl⟩ : syracuseStep 1176331 = 1764497) B1764497
theorem B1176343 : Blo 1174404 1176343 := bstep (se 1 (by rfl) ⟨882257, by rfl⟩ : syracuseStep 1176343 = 1764515) B1764515
theorem B1176363 : Blo 1174404 1176363 := bstep (se 1 (by rfl) ⟨882272, by rfl⟩ : syracuseStep 1176363 = 1764545) B1764545
theorem B1176375 : Blo 1174404 1176375 := bstep (se 1 (by rfl) ⟨882281, by rfl⟩ : syracuseStep 1176375 = 1764563) B1764563
theorem B2233163 : Blo 1174404 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B1176395 : Blo 1174404 1176395 := bstep (se 1 (by rfl) ⟨882296, by rfl⟩ : syracuseStep 1176395 = 1764593) B1764593
theorem B2642777 : Blo 1174404 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B3765143 : Blo 1174404 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B2642867 : Blo 1174404 2642867 := bstep (se 1 (by rfl) ⟨1982150, by rfl⟩ : syracuseStep 2642867 = 3964301) B3964301
theorem B3969971 : Blo 1174404 3969971 := bstep (se 1 (by rfl) ⟨2977478, by rfl⟩ : syracuseStep 3969971 = 5954957) B5954957
theorem B3871691 : Blo 1174404 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B2642903 : Blo 1174404 2642903 := bstep (se 1 (by rfl) ⟨1982177, by rfl⟩ : syracuseStep 2642903 = 3964355) B3964355
theorem B3175499 : Blo 1174404 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B14308427 : Blo 1174404 14308427 := bstep (se 1 (by rfl) ⟨10731320, by rfl⟩ : syracuseStep 14308427 = 21462641) B21462641
theorem B5018755 : Blo 1174404 5018755 := bstep (se 1 (by rfl) ⟨3764066, by rfl⟩ : syracuseStep 5018755 = 7528133) B7528133
theorem B1881227 : Blo 1174404 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B2643083 : Blo 1174404 2643083 := bstep (se 1 (by rfl) ⟨1982312, by rfl⟩ : syracuseStep 2643083 = 3964625) B3964625
theorem B2643137 : Blo 1174404 2643137 := bstep (se 2 (by rfl) ⟨991176, by rfl⟩ : syracuseStep 2643137 = 1982353) B1982353
theorem B3970241 : Blo 1174404 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B3347659 : Blo 1174404 3347659 := bstep (se 1 (by rfl) ⟨2510744, by rfl⟩ : syracuseStep 3347659 = 5021489) B5021489
theorem B2512129 : Blo 1174404 2512129 := bstep (se 2 (by rfl) ⟨942048, by rfl⟩ : syracuseStep 2512129 = 1884097) B1884097
theorem B7525649 : Blo 1174404 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B4461875 : Blo 1174404 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B21443957 : Blo 1174404 21443957 := bstep (se 5 (by rfl) ⟨1005185, by rfl⟩ : syracuseStep 21443957 = 2010371) B2010371
theorem B2643353 : Blo 1174404 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B3765707 : Blo 1174404 3765707 := bstep (se 1 (by rfl) ⟨2824280, by rfl⟩ : syracuseStep 3765707 = 5648561) B5648561
theorem B5019097 : Blo 1174404 5019097 := bstep (se 2 (by rfl) ⟨1882161, by rfl⟩ : syracuseStep 5019097 = 3764323) B3764323
theorem B2643443 : Blo 1174404 2643443 := bstep (se 1 (by rfl) ⟨1982582, by rfl⟩ : syracuseStep 2643443 = 3965165) B3965165
theorem B2512385 : Blo 1174404 2512385 := bstep (se 2 (by rfl) ⟨942144, by rfl⟩ : syracuseStep 2512385 = 1884289) B1884289
theorem B8467973 : Blo 1174404 8467973 := bstep (se 4 (by rfl) ⟨793872, by rfl⟩ : syracuseStep 8467973 = 1587745) B1587745
theorem B1488395 : Blo 1174404 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B2643479 : Blo 1174404 2643479 := bstep (se 1 (by rfl) ⟨1982609, by rfl⟩ : syracuseStep 2643479 = 3965219) B3965219
theorem B2512471 : Blo 1174404 2512471 := bstep (se 1 (by rfl) ⟨1884353, by rfl⟩ : syracuseStep 2512471 = 3768707) B3768707
theorem B6690397 : Blo 1174404 6690397 := bstep (se 3 (by rfl) ⟨1254449, by rfl⟩ : syracuseStep 6690397 = 2508899) B2508899
theorem B1881739 : Blo 1174404 1881739 := bstep (se 1 (by rfl) ⟨1411304, by rfl⟩ : syracuseStep 1881739 = 2822609) B2822609
theorem B3815063 : Blo 1174404 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B5953175 : Blo 1174404 5953175 := bstep (se 1 (by rfl) ⟨4464881, by rfl⟩ : syracuseStep 5953175 = 8929763) B8929763
theorem B3348161 : Blo 1174404 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B2643659 : Blo 1174404 2643659 := bstep (se 1 (by rfl) ⟨1982744, by rfl⟩ : syracuseStep 2643659 = 3965489) B3965489
theorem B2643713 : Blo 1174404 2643713 := bstep (se 2 (by rfl) ⟨991392, by rfl⟩ : syracuseStep 2643713 = 1982785) B1982785
theorem B9049873 : Blo 1174404 9049873 := bstep (se 2 (by rfl) ⟨3393702, by rfl⟩ : syracuseStep 9049873 = 6787405) B6787405
theorem B3766105 : Blo 1174404 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B9533315 : Blo 1174404 9533315 := bstep (se 1 (by rfl) ⟨7149986, by rfl⟩ : syracuseStep 9533315 = 14299973) B14299973
theorem B2643929 : Blo 1174404 2643929 := bstep (se 2 (by rfl) ⟨991473, by rfl⟩ : syracuseStep 2643929 = 1982947) B1982947
theorem B4413457 : Blo 1174404 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B3348503 : Blo 1174404 3348503 := bstep (se 1 (by rfl) ⟨2511377, by rfl⟩ : syracuseStep 3348503 = 5022755) B5022755
theorem B2644019 : Blo 1174404 2644019 := bstep (se 1 (by rfl) ⟨1983014, by rfl⟩ : syracuseStep 2644019 = 3966029) B3966029
theorem B2644055 : Blo 1174404 2644055 := bstep (se 1 (by rfl) ⟨1983041, by rfl⟩ : syracuseStep 2644055 = 3966083) B3966083
theorem B8927333 : Blo 1174404 8927333 := bstep (se 4 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 8927333 = 1673875) B1673875
theorem B5945561 : Blo 1174404 5945561 := bstep (se 2 (by rfl) ⟨2229585, by rfl⟩ : syracuseStep 5945561 = 4459171) B4459171
theorem B2644235 : Blo 1174404 2644235 := bstep (se 1 (by rfl) ⟨1983176, by rfl⟩ : syracuseStep 2644235 = 3966353) B3966353
theorem B2644289 : Blo 1174404 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B1882457 : Blo 1174404 1882457 := bstep (se 2 (by rfl) ⟨705921, by rfl⟩ : syracuseStep 1882457 = 1411843) B1411843
theorem B5020055 : Blo 1174404 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B2824627 : Blo 1174404 2824627 := bstep (se 1 (by rfl) ⟨2118470, by rfl⟩ : syracuseStep 2824627 = 4236941) B4236941
theorem B8919557 : Blo 1174404 8919557 := bstep (se 4 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 8919557 = 1672417) B1672417
theorem B1882649 : Blo 1174404 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B2644505 : Blo 1174404 2644505 := bstep (se 2 (by rfl) ⟨991689, by rfl⟩ : syracuseStep 2644505 = 1983379) B1983379
theorem B8927819 : Blo 1174404 8927819 := bstep (se 1 (by rfl) ⟨6695864, by rfl⟩ : syracuseStep 8927819 = 13391729) B13391729
theorem B2644595 : Blo 1174404 2644595 := bstep (se 1 (by rfl) ⟨1983446, by rfl⟩ : syracuseStep 2644595 = 3966893) B3966893
theorem B2644631 : Blo 1174404 2644631 := bstep (se 1 (by rfl) ⟨1983473, by rfl⟩ : syracuseStep 2644631 = 3966947) B3966947
theorem B6699671 : Blo 1174404 6699671 := bstep (se 1 (by rfl) ⟨5024753, by rfl⟩ : syracuseStep 6699671 = 10049507) B10049507
theorem B1882777 : Blo 1174404 1882777 := bstep (se 2 (by rfl) ⟨706041, by rfl⟩ : syracuseStep 1882777 = 1412083) B1412083
theorem B4463363 : Blo 1174404 4463363 := bstep (se 1 (by rfl) ⟨3347522, by rfl⟩ : syracuseStep 4463363 = 6695045) B6695045
theorem B10042157 : Blo 1174404 10042157 := bstep (se 3 (by rfl) ⟨1882904, by rfl⟩ : syracuseStep 10042157 = 3765809) B3765809
theorem B8584001 : Blo 1174404 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B2644811 : Blo 1174404 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B2644865 : Blo 1174404 2644865 := bstep (se 2 (by rfl) ⟨991824, by rfl⟩ : syracuseStep 2644865 = 1983649) B1983649
theorem B3963869 : Blo 1174404 3963869 := bstep (se 3 (by rfl) ⟨743225, by rfl⟩ : syracuseStep 3963869 = 1486451) B1486451
theorem B9042949 : Blo 1174404 9042949 := bstep (se 4 (by rfl) ⟨847776, by rfl⟩ : syracuseStep 9042949 = 1695553) B1695553
theorem B3767347 : Blo 1174404 3767347 := bstep (se 1 (by rfl) ⟨2825510, by rfl⟩ : syracuseStep 3767347 = 5651021) B5651021
theorem B2645081 : Blo 1174404 2645081 := bstep (se 2 (by rfl) ⟨991905, by rfl⟩ : syracuseStep 2645081 = 1983811) B1983811
theorem B2645171 : Blo 1174404 2645171 := bstep (se 1 (by rfl) ⟨1983878, by rfl⟩ : syracuseStep 2645171 = 3967757) B3967757
theorem B4463819 : Blo 1174404 4463819 := bstep (se 1 (by rfl) ⟨3347864, by rfl⟩ : syracuseStep 4463819 = 6695729) B6695729
theorem B2645207 : Blo 1174404 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B30555397 : Blo 1174404 30555397 := bstep (se 4 (by rfl) ⟨2864568, by rfl⟩ : syracuseStep 30555397 = 5729137) B5729137
theorem B1883417 : Blo 1174404 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B1588567 : Blo 1174404 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B2645387 : Blo 1174404 2645387 := bstep (se 1 (by rfl) ⟨1984040, by rfl⟩ : syracuseStep 2645387 = 3968081) B3968081
theorem B4464017 : Blo 1174404 4464017 := bstep (se 2 (by rfl) ⟨1674006, by rfl⟩ : syracuseStep 4464017 = 3348013) B3348013
theorem B171589013 : Blo 1174404 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B1981847 : Blo 1174404 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B2645441 : Blo 1174404 2645441 := bstep (se 2 (by rfl) ⟨992040, by rfl⟩ : syracuseStep 2645441 = 1984081) B1984081
theorem B2973145 : Blo 1174404 2973145 := bstep (se 2 (by rfl) ⟨1114929, by rfl⟩ : syracuseStep 2973145 = 2229859) B2229859
theorem B5643793 : Blo 1174404 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B1981975 : Blo 1174404 1981975 := bstep (se 1 (by rfl) ⟨1486481, by rfl⟩ : syracuseStep 1981975 = 2972963) B2972963
theorem B16293527 : Blo 1174404 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B2645657 : Blo 1174404 2645657 := bstep (se 2 (by rfl) ⟨992121, by rfl⟩ : syracuseStep 2645657 = 1984243) B1984243
theorem B1588939 : Blo 1174404 1588939 := bstep (se 1 (by rfl) ⟨1191704, by rfl⟩ : syracuseStep 1588939 = 2383409) B2383409
theorem B2645747 : Blo 1174404 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B1589015 : Blo 1174404 1589015 := bstep (se 1 (by rfl) ⟨1191761, by rfl⟩ : syracuseStep 1589015 = 2383523) B2383523
theorem B2645783 : Blo 1174404 2645783 := bstep (se 1 (by rfl) ⟨1984337, by rfl⟩ : syracuseStep 2645783 = 3968675) B3968675
theorem B5947181 : Blo 1174404 5947181 := bstep (se 3 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 5947181 = 2230193) B2230193
theorem B10182493 : Blo 1174404 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B3923905 : Blo 1174404 3923905 := bstep (se 2 (by rfl) ⟨1471464, by rfl⟩ : syracuseStep 3923905 = 2942929) B2942929
theorem B2645963 : Blo 1174404 2645963 := bstep (se 1 (by rfl) ⟨1984472, by rfl⟩ : syracuseStep 2645963 = 3968945) B3968945
theorem B2678743 : Blo 1174404 2678743 := bstep (se 1 (by rfl) ⟨2009057, by rfl⟩ : syracuseStep 2678743 = 4018115) B4018115
theorem B2826299 : Blo 1174404 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B2646287 : Blo 1174404 2646287 := bstep (se 1 (by rfl) ⟨1984715, by rfl⟩ : syracuseStep 2646287 = 3969431) B3969431
theorem B2646305 : Blo 1174404 2646305 := bstep (se 2 (by rfl) ⟨992364, by rfl⟩ : syracuseStep 2646305 = 1984729) B1984729
theorem B28574045 : Blo 1174404 28574045 := bstep (se 3 (by rfl) ⟨5357633, by rfl⟩ : syracuseStep 28574045 = 10715267) B10715267
theorem B2974067 : Blo 1174404 2974067 := bstep (se 1 (by rfl) ⟨2230550, by rfl⟩ : syracuseStep 2974067 = 4461101) B4461101
theorem B1982839 : Blo 1174404 1982839 := bstep (se 1 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 1982839 = 2974259) B2974259
theorem B2417015 : Blo 1174404 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B1761671 : Blo 1174404 1761671 := bstep (se 1 (by rfl) ⟨1321253, by rfl⟩ : syracuseStep 1761671 = 2642507) B2642507
theorem B1761707 : Blo 1174404 1761707 := bstep (se 1 (by rfl) ⟨1321280, by rfl⟩ : syracuseStep 1761707 = 2642561) B2642561
theorem B1761737 : Blo 1174404 1761737 := bstep (se 2 (by rfl) ⟨660651, by rfl⟩ : syracuseStep 1761737 = 1321303) B1321303
theorem B1761851 : Blo 1174404 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1983035 : Blo 1174404 1983035 := bstep (se 1 (by rfl) ⟨1487276, by rfl⟩ : syracuseStep 1983035 = 2974553) B2974553
theorem B5947991 : Blo 1174404 5947991 := bstep (se 1 (by rfl) ⟨4460993, by rfl⟩ : syracuseStep 5947991 = 8921987) B8921987
theorem B1761911 : Blo 1174404 1761911 := bstep (se 1 (by rfl) ⟨1321433, by rfl⟩ : syracuseStep 1761911 = 2642867) B2642867
theorem B2646647 : Blo 1174404 2646647 := bstep (se 1 (by rfl) ⟨1984985, by rfl⟩ : syracuseStep 2646647 = 3969971) B3969971
theorem B2581127 : Blo 1174404 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B1761935 : Blo 1174404 1761935 := bstep (se 1 (by rfl) ⟨1321451, by rfl⟩ : syracuseStep 1761935 = 2642903) B2642903
theorem B1786511 : Blo 1174404 1786511 := bstep (se 1 (by rfl) ⟨1339883, by rfl⟩ : syracuseStep 1786511 = 2679767) B2679767
theorem B1761977 : Blo 1174404 1761977 := bstep (se 2 (by rfl) ⟨660741, by rfl⟩ : syracuseStep 1761977 = 1321483) B1321483
theorem B1254151 : Blo 1174404 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B1762055 : Blo 1174404 1762055 := bstep (se 1 (by rfl) ⟨1321541, by rfl⟩ : syracuseStep 1762055 = 2643083) B2643083
theorem B76251941 : Blo 1174404 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B1762091 : Blo 1174404 1762091 := bstep (se 1 (by rfl) ⟨1321568, by rfl⟩ : syracuseStep 1762091 = 2643137) B2643137
theorem B2646827 : Blo 1174404 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B1786681 : Blo 1174404 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B4768571 : Blo 1174404 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B1762121 : Blo 1174404 1762121 := bstep (se 2 (by rfl) ⟨660795, by rfl⟩ : syracuseStep 1762121 = 1321591) B1321591
theorem B2974583 : Blo 1174404 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B3818387 : Blo 1174404 3818387 := bstep (se 1 (by rfl) ⟨2863790, by rfl⟩ : syracuseStep 3818387 = 5727581) B5727581
theorem B14295971 : Blo 1174404 14295971 := bstep (se 1 (by rfl) ⟨10721978, by rfl⟩ : syracuseStep 14295971 = 21443957) B21443957
theorem B1762235 : Blo 1174404 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B1983433 : Blo 1174404 1983433 := bstep (se 2 (by rfl) ⟨743787, by rfl⟩ : syracuseStep 1983433 = 1487575) B1487575
theorem B1762295 : Blo 1174404 1762295 := bstep (se 1 (by rfl) ⟨1321721, by rfl⟩ : syracuseStep 1762295 = 2643443) B2643443
theorem B5645315 : Blo 1174404 5645315 := bstep (se 1 (by rfl) ⟨4233986, by rfl⟩ : syracuseStep 5645315 = 8467973) B8467973
theorem B1762319 : Blo 1174404 1762319 := bstep (se 1 (by rfl) ⟨1321739, by rfl⟩ : syracuseStep 1762319 = 2643479) B2643479
theorem B6030379 : Blo 1174404 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B1762361 : Blo 1174404 1762361 := bstep (se 2 (by rfl) ⟨660885, by rfl⟩ : syracuseStep 1762361 = 1321771) B1321771
theorem B5948477 : Blo 1174404 5948477 := bstep (se 3 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 5948477 = 2230679) B2230679
theorem B1762439 : Blo 1174404 1762439 := bstep (se 1 (by rfl) ⟨1321829, by rfl⟩ : syracuseStep 1762439 = 2643659) B2643659
theorem B1762475 : Blo 1174404 1762475 := bstep (se 1 (by rfl) ⟨1321856, by rfl⟩ : syracuseStep 1762475 = 2643713) B2643713
theorem B1762505 : Blo 1174404 1762505 := bstep (se 2 (by rfl) ⟨660939, by rfl⟩ : syracuseStep 1762505 = 1321879) B1321879
theorem B1762619 : Blo 1174404 1762619 := bstep (se 1 (by rfl) ⟨1321964, by rfl⟩ : syracuseStep 1762619 = 2643929) B2643929
theorem B1885559 : Blo 1174404 1885559 := bstep (se 1 (by rfl) ⟨1414169, by rfl⟩ : syracuseStep 1885559 = 2828339) B2828339
theorem B1762679 : Blo 1174404 1762679 := bstep (se 1 (by rfl) ⟨1322009, by rfl⟩ : syracuseStep 1762679 = 2644019) B2644019
theorem B50824583 : Blo 1174404 50824583 := bstep (se 1 (by rfl) ⟨38118437, by rfl⟩ : syracuseStep 50824583 = 76236875) B76236875
theorem B1762703 : Blo 1174404 1762703 := bstep (se 1 (by rfl) ⟨1322027, by rfl⟩ : syracuseStep 1762703 = 2644055) B2644055
theorem B5023129 : Blo 1174404 5023129 := bstep (se 2 (by rfl) ⟨1883673, by rfl⟩ : syracuseStep 5023129 = 3767347) B3767347
theorem B1762745 : Blo 1174404 1762745 := bstep (se 2 (by rfl) ⟨661029, by rfl⟩ : syracuseStep 1762745 = 1322059) B1322059
theorem B1762823 : Blo 1174404 1762823 := bstep (se 1 (by rfl) ⟨1322117, by rfl⟩ : syracuseStep 1762823 = 2644235) B2644235
theorem B1762859 : Blo 1174404 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B2901547 : Blo 1174404 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B1254971 : Blo 1174404 1254971 := bstep (se 1 (by rfl) ⟨941228, by rfl⟩ : syracuseStep 1254971 = 1882457) B1882457
theorem B1762889 : Blo 1174404 1762889 := bstep (se 2 (by rfl) ⟨661083, by rfl⟩ : syracuseStep 1762889 = 1322167) B1322167
theorem B1984135 : Blo 1174404 1984135 := bstep (se 1 (by rfl) ⟨1488101, by rfl⟩ : syracuseStep 1984135 = 2976203) B2976203
theorem B40740529 : Blo 1174404 40740529 := bstep (se 2 (by rfl) ⟨15277698, by rfl⟩ : syracuseStep 40740529 = 30555397) B30555397
theorem B1255099 : Blo 1174404 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B1763003 : Blo 1174404 1763003 := bstep (se 1 (by rfl) ⟨1322252, by rfl⟩ : syracuseStep 1763003 = 2644505) B2644505
theorem B1763063 : Blo 1174404 1763063 := bstep (se 1 (by rfl) ⟨1322297, by rfl⟩ : syracuseStep 1763063 = 2644595) B2644595
theorem B1763087 : Blo 1174404 1763087 := bstep (se 1 (by rfl) ⟨1322315, by rfl⟩ : syracuseStep 1763087 = 2644631) B2644631
theorem B4466447 : Blo 1174404 4466447 := bstep (se 1 (by rfl) ⟨3349835, by rfl⟩ : syracuseStep 4466447 = 6699671) B6699671
theorem B1763129 : Blo 1174404 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B2975575 : Blo 1174404 2975575 := bstep (se 1 (by rfl) ⟨2231681, by rfl⟩ : syracuseStep 2975575 = 4463363) B4463363
theorem B6694771 : Blo 1174404 6694771 := bstep (se 1 (by rfl) ⟨5021078, by rfl⟩ : syracuseStep 6694771 = 10042157) B10042157
theorem B1763207 : Blo 1174404 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B2230163 : Blo 1174404 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B1763243 : Blo 1174404 1763243 := bstep (se 1 (by rfl) ⟨1322432, by rfl⟩ : syracuseStep 1763243 = 2644865) B2644865
theorem B1763273 : Blo 1174404 1763273 := bstep (se 2 (by rfl) ⟨661227, by rfl⟩ : syracuseStep 1763273 = 1322455) B1322455
theorem B1763387 : Blo 1174404 1763387 := bstep (se 1 (by rfl) ⟨1322540, by rfl⟩ : syracuseStep 1763387 = 2645081) B2645081
theorem B4237373 : Blo 1174404 4237373 := bstep (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) B1589015
theorem B2230391 : Blo 1174404 2230391 := bstep (se 1 (by rfl) ⟨1672793, by rfl⟩ : syracuseStep 2230391 = 3345587) B3345587
theorem B1763447 : Blo 1174404 1763447 := bstep (se 1 (by rfl) ⟨1322585, by rfl⟩ : syracuseStep 1763447 = 2645171) B2645171
theorem B2975879 : Blo 1174404 2975879 := bstep (se 1 (by rfl) ⟨2231909, by rfl⟩ : syracuseStep 2975879 = 4463819) B4463819
theorem B1763471 : Blo 1174404 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B2508985 : Blo 1174404 2508985 := bstep (se 2 (by rfl) ⟨940869, by rfl⟩ : syracuseStep 2508985 = 1881739) B1881739
theorem B1763513 : Blo 1174404 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B2263241 : Blo 1174404 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B22898933 : Blo 1174404 22898933 := bstep (se 5 (by rfl) ⟨1073387, by rfl⟩ : syracuseStep 22898933 = 2146775) B2146775
theorem B1763591 : Blo 1174404 1763591 := bstep (se 1 (by rfl) ⟨1322693, by rfl⟩ : syracuseStep 1763591 = 2645387) B2645387
theorem B2976011 : Blo 1174404 2976011 := bstep (se 1 (by rfl) ⟨2232008, by rfl⟩ : syracuseStep 2976011 = 4464017) B4464017
theorem B1321231 : Blo 1174404 1321231 := bstep (se 1 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 1321231 = 1981847) B1981847
theorem B1984783 : Blo 1174404 1984783 := bstep (se 1 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 1984783 = 2977175) B2977175
theorem B1763627 : Blo 1174404 1763627 := bstep (se 1 (by rfl) ⟨1322720, by rfl⟩ : syracuseStep 1763627 = 2645441) B2645441
theorem B1763657 : Blo 1174404 1763657 := bstep (se 2 (by rfl) ⟨661371, by rfl⟩ : syracuseStep 1763657 = 1322743) B1322743
theorem B3967379 : Blo 1174404 3967379 := bstep (se 1 (by rfl) ⟨2975534, by rfl⟩ : syracuseStep 3967379 = 5951069) B5951069
theorem B1673659 : Blo 1174404 1673659 := bstep (se 1 (by rfl) ⟨1255244, by rfl⟩ : syracuseStep 1673659 = 2510489) B2510489
theorem B1763771 : Blo 1174404 1763771 := bstep (se 1 (by rfl) ⟨1322828, by rfl⟩ : syracuseStep 1763771 = 2645657) B2645657
theorem B13576657 : Blo 1174404 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1763831 : Blo 1174404 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B1763855 : Blo 1174404 1763855 := bstep (se 1 (by rfl) ⟨1322891, by rfl⟩ : syracuseStep 1763855 = 2645783) B2645783
theorem B1763897 : Blo 1174404 1763897 := bstep (se 2 (by rfl) ⟨661461, by rfl⟩ : syracuseStep 1763897 = 1322923) B1322923
theorem B1763975 : Blo 1174404 1763975 := bstep (se 1 (by rfl) ⟨1322981, by rfl⟩ : syracuseStep 1763975 = 2645963) B2645963
theorem B1764011 : Blo 1174404 1764011 := bstep (se 1 (by rfl) ⟨1323008, by rfl⟩ : syracuseStep 1764011 = 2646017) B2646017
theorem B3345097 : Blo 1174404 3345097 := bstep (se 2 (by rfl) ⟨1254411, by rfl⟩ : syracuseStep 3345097 = 2508823) B2508823
theorem B1764041 : Blo 1174404 1764041 := bstep (se 2 (by rfl) ⟨661515, by rfl⟩ : syracuseStep 1764041 = 1323031) B1323031
theorem B23538437 : Blo 1174404 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B1321735 : Blo 1174404 1321735 := bstep (se 1 (by rfl) ⟨991301, by rfl⟩ : syracuseStep 1321735 = 1982603) B1982603
theorem B2976527 : Blo 1174404 2976527 := bstep (se 1 (by rfl) ⟨2232395, by rfl⟩ : syracuseStep 2976527 = 4464791) B4464791
theorem B25406243 : Blo 1174404 25406243 := bstep (se 1 (by rfl) ⟨19054682, by rfl⟩ : syracuseStep 25406243 = 38109365) B38109365
theorem B12716837 : Blo 1174404 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B5950259 : Blo 1174404 5950259 := bstep (se 1 (by rfl) ⟨4462694, by rfl⟩ : syracuseStep 5950259 = 8925389) B8925389
theorem B1764155 : Blo 1174404 1764155 := bstep (se 1 (by rfl) ⟨1323116, by rfl⟩ : syracuseStep 1764155 = 2646233) B2646233
theorem B1674103 : Blo 1174404 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B1764215 : Blo 1174404 1764215 := bstep (se 1 (by rfl) ⟨1323161, by rfl⟩ : syracuseStep 1764215 = 2646323) B2646323
theorem B1174407 : Blo 1174404 1174407 := bstep (se 1 (by rfl) ⟨880805, by rfl⟩ : syracuseStep 1174407 = 1761611) B1761611
theorem B1174415 : Blo 1174404 1174415 := bstep (se 1 (by rfl) ⟨880811, by rfl⟩ : syracuseStep 1174415 = 1761623) B1761623
theorem B1764239 : Blo 1174404 1764239 := bstep (se 1 (by rfl) ⟨1323179, by rfl⟩ : syracuseStep 1764239 = 2646359) B2646359
theorem B2976659 : Blo 1174404 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B12888983 : Blo 1174404 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B11447203 : Blo 1174404 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B20089781 : Blo 1174404 20089781 := bstep (se 5 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 20089781 = 1883417) B1883417
theorem B1764281 : Blo 1174404 1764281 := bstep (se 2 (by rfl) ⟨661605, by rfl⟩ : syracuseStep 1764281 = 1323211) B1323211
theorem B1174459 : Blo 1174404 1174459 := bstep (se 1 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 1174459 = 1761689) B1761689
theorem B1321915 : Blo 1174404 1321915 := bstep (se 1 (by rfl) ⟨991436, by rfl⟩ : syracuseStep 1321915 = 1982873) B1982873
theorem B5647313 : Blo 1174404 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1174535 : Blo 1174404 1174535 := bstep (se 1 (by rfl) ⟨880901, by rfl⟩ : syracuseStep 1174535 = 1761803) B1761803
theorem B1764359 : Blo 1174404 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B1174543 : Blo 1174404 1174543 := bstep (se 1 (by rfl) ⟨880907, by rfl⟩ : syracuseStep 1174543 = 1761815) B1761815
theorem B1764395 : Blo 1174404 1764395 := bstep (se 1 (by rfl) ⟨1323296, by rfl⟩ : syracuseStep 1764395 = 2646593) B2646593
theorem B1174587 : Blo 1174404 1174587 := bstep (se 1 (by rfl) ⟨880940, by rfl⟩ : syracuseStep 1174587 = 1761881) B1761881
theorem B5360701 : Blo 1174404 5360701 := bstep (se 3 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 5360701 = 2010263) B2010263
theorem B1764425 : Blo 1174404 1764425 := bstep (se 2 (by rfl) ⟨661659, by rfl⟩ : syracuseStep 1764425 = 1323319) B1323319
theorem B5950583 : Blo 1174404 5950583 := bstep (se 1 (by rfl) ⟨4462937, by rfl⟩ : syracuseStep 5950583 = 8925875) B8925875
theorem B1174663 : Blo 1174404 1174663 := bstep (se 1 (by rfl) ⟨880997, by rfl⟩ : syracuseStep 1174663 = 1761995) B1761995
theorem B1174671 : Blo 1174404 1174671 := bstep (se 1 (by rfl) ⟨881003, by rfl⟩ : syracuseStep 1174671 = 1762007) B1762007
theorem B1174715 : Blo 1174404 1174715 := bstep (se 1 (by rfl) ⟨881036, by rfl⟩ : syracuseStep 1174715 = 1762073) B1762073
theorem B1764539 : Blo 1174404 1764539 := bstep (se 1 (by rfl) ⟨1323404, by rfl⟩ : syracuseStep 1764539 = 2646809) B2646809
theorem B1764599 : Blo 1174404 1764599 := bstep (se 1 (by rfl) ⟨1323449, by rfl⟩ : syracuseStep 1764599 = 2646899) B2646899
theorem B1174791 : Blo 1174404 1174791 := bstep (se 1 (by rfl) ⟨881093, by rfl⟩ : syracuseStep 1174791 = 1762187) B1762187
theorem B1174799 : Blo 1174404 1174799 := bstep (se 1 (by rfl) ⟨881099, by rfl⟩ : syracuseStep 1174799 = 1762199) B1762199
theorem B6696229 : Blo 1174404 6696229 := bstep (se 4 (by rfl) ⟨627771, by rfl⟩ : syracuseStep 6696229 = 1255543) B1255543
theorem B1174843 : Blo 1174404 1174843 := bstep (se 1 (by rfl) ⟨881132, by rfl⟩ : syracuseStep 1174843 = 1762265) B1762265
theorem B2116999 : Blo 1174404 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1174919 : Blo 1174404 1174919 := bstep (se 1 (by rfl) ⟨881189, by rfl⟩ : syracuseStep 1174919 = 1762379) B1762379
theorem B2682247 : Blo 1174404 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B1174927 : Blo 1174404 1174927 := bstep (se 1 (by rfl) ⟨881195, by rfl⟩ : syracuseStep 1174927 = 1762391) B1762391
theorem B1322383 : Blo 1174404 1322383 := bstep (se 1 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 1322383 = 1983575) B1983575
theorem B4459961 : Blo 1174404 4459961 := bstep (se 2 (by rfl) ⟨1672485, by rfl⟩ : syracuseStep 4459961 = 3344971) B3344971
theorem B1174971 : Blo 1174404 1174971 := bstep (se 1 (by rfl) ⟨881228, by rfl⟩ : syracuseStep 1174971 = 1762457) B1762457
theorem B1175047 : Blo 1174404 1175047 := bstep (se 1 (by rfl) ⟨881285, by rfl⟩ : syracuseStep 1175047 = 1762571) B1762571
theorem B5017099 : Blo 1174404 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B1175055 : Blo 1174404 1175055 := bstep (se 1 (by rfl) ⟨881291, by rfl⟩ : syracuseStep 1175055 = 1762583) B1762583
theorem B2510369 : Blo 1174404 2510369 := bstep (se 2 (by rfl) ⟨941388, by rfl⟩ : syracuseStep 2510369 = 1882777) B1882777
theorem B1175099 : Blo 1174404 1175099 := bstep (se 1 (by rfl) ⟨881324, by rfl⟩ : syracuseStep 1175099 = 1762649) B1762649
theorem B11300471 : Blo 1174404 11300471 := bstep (se 1 (by rfl) ⟨8475353, by rfl⟩ : syracuseStep 11300471 = 16950707) B16950707
theorem B1175175 : Blo 1174404 1175175 := bstep (se 1 (by rfl) ⟨881381, by rfl⟩ : syracuseStep 1175175 = 1762763) B1762763
theorem B2510471 : Blo 1174404 2510471 := bstep (se 1 (by rfl) ⟨1882853, by rfl⟩ : syracuseStep 2510471 = 3765707) B3765707
theorem B1175183 : Blo 1174404 1175183 := bstep (se 1 (by rfl) ⟨881387, by rfl⟩ : syracuseStep 1175183 = 1762775) B1762775
theorem B1486507 : Blo 1174404 1486507 := bstep (se 1 (by rfl) ⟨1114880, by rfl⟩ : syracuseStep 1486507 = 2229761) B2229761
theorem B1674923 : Blo 1174404 1674923 := bstep (se 1 (by rfl) ⟨1256192, by rfl⟩ : syracuseStep 1674923 = 2512385) B2512385
theorem B1175227 : Blo 1174404 1175227 := bstep (se 1 (by rfl) ⟨881420, by rfl⟩ : syracuseStep 1175227 = 1762841) B1762841
theorem B8474341 : Blo 1174404 8474341 := bstep (se 4 (by rfl) ⟨794469, by rfl⟩ : syracuseStep 8474341 = 1588939) B1588939
theorem B1175303 : Blo 1174404 1175303 := bstep (se 1 (by rfl) ⟨881477, by rfl⟩ : syracuseStep 1175303 = 1762955) B1762955
theorem B2543375 : Blo 1174404 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B1175311 : Blo 1174404 1175311 := bstep (se 1 (by rfl) ⟨881483, by rfl⟩ : syracuseStep 1175311 = 1762967) B1762967
theorem B3968783 : Blo 1174404 3968783 := bstep (se 1 (by rfl) ⟨2976587, by rfl⟩ : syracuseStep 3968783 = 5953175) B5953175
theorem B2232107 : Blo 1174404 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B6696755 : Blo 1174404 6696755 := bstep (se 1 (by rfl) ⟨5022566, by rfl⟩ : syracuseStep 6696755 = 10045133) B10045133
theorem B1175355 : Blo 1174404 1175355 := bstep (se 1 (by rfl) ⟨881516, by rfl⟩ : syracuseStep 1175355 = 1763033) B1763033
theorem B1175431 : Blo 1174404 1175431 := bstep (se 1 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 1175431 = 1763147) B1763147
theorem B1322887 : Blo 1174404 1322887 := bstep (se 1 (by rfl) ⟨992165, by rfl⟩ : syracuseStep 1322887 = 1984331) B1984331
theorem B1175439 : Blo 1174404 1175439 := bstep (se 1 (by rfl) ⟨881579, by rfl⟩ : syracuseStep 1175439 = 1763159) B1763159
theorem B1175483 : Blo 1174404 1175483 := bstep (se 1 (by rfl) ⟨881612, by rfl⟩ : syracuseStep 1175483 = 1763225) B1763225
theorem B1175559 : Blo 1174404 1175559 := bstep (se 1 (by rfl) ⟨881669, by rfl⟩ : syracuseStep 1175559 = 1763339) B1763339
theorem B1175567 : Blo 1174404 1175567 := bstep (se 1 (by rfl) ⟨881675, by rfl⟩ : syracuseStep 1175567 = 1763351) B1763351
theorem B2232335 : Blo 1174404 2232335 := bstep (se 1 (by rfl) ⟨1674251, by rfl⟩ : syracuseStep 2232335 = 3348503) B3348503
theorem B3969053 : Blo 1174404 3969053 := bstep (se 3 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 3969053 = 1488395) B1488395
theorem B1175611 : Blo 1174404 1175611 := bstep (se 1 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 1175611 = 1763417) B1763417
theorem B1323067 : Blo 1174404 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B5951555 : Blo 1174404 5951555 := bstep (se 1 (by rfl) ⟨4463666, by rfl⟩ : syracuseStep 5951555 = 8927333) B8927333
theorem B1175687 : Blo 1174404 1175687 := bstep (se 1 (by rfl) ⟨881765, by rfl⟩ : syracuseStep 1175687 = 1763531) B1763531
theorem B1175695 : Blo 1174404 1175695 := bstep (se 1 (by rfl) ⟨881771, by rfl⟩ : syracuseStep 1175695 = 1763543) B1763543
theorem B1175739 : Blo 1174404 1175739 := bstep (se 1 (by rfl) ⟨881804, by rfl⟩ : syracuseStep 1175739 = 1763609) B1763609
theorem B1175815 : Blo 1174404 1175815 := bstep (se 1 (by rfl) ⟨881861, by rfl⟩ : syracuseStep 1175815 = 1763723) B1763723
theorem B3346703 : Blo 1174404 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B1175823 : Blo 1174404 1175823 := bstep (se 1 (by rfl) ⟨881867, by rfl⟩ : syracuseStep 1175823 = 1763735) B1763735
theorem B1175867 : Blo 1174404 1175867 := bstep (se 1 (by rfl) ⟨881900, by rfl⟩ : syracuseStep 1175867 = 1763801) B1763801
theorem B108532061 : Blo 1174404 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B5951879 : Blo 1174404 5951879 := bstep (se 1 (by rfl) ⟨4463909, by rfl⟩ : syracuseStep 5951879 = 8927819) B8927819
theorem B1175943 : Blo 1174404 1175943 := bstep (se 1 (by rfl) ⟨881957, by rfl⟩ : syracuseStep 1175943 = 1763915) B1763915
theorem B1175951 : Blo 1174404 1175951 := bstep (se 1 (by rfl) ⟨881963, by rfl⟩ : syracuseStep 1175951 = 1763927) B1763927
theorem B10039697 : Blo 1174404 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B1175995 : Blo 1174404 1175995 := bstep (se 1 (by rfl) ⟨881996, by rfl⟩ : syracuseStep 1175995 = 1763993) B1763993
theorem B2118089 : Blo 1174404 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B1176071 : Blo 1174404 1176071 := bstep (se 1 (by rfl) ⟨882053, by rfl⟩ : syracuseStep 1176071 = 1764107) B1764107
theorem B1176079 : Blo 1174404 1176079 := bstep (se 1 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 1176079 = 1764119) B1764119
theorem B5722667 : Blo 1174404 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B1176123 : Blo 1174404 1176123 := bstep (se 1 (by rfl) ⟨882092, by rfl⟩ : syracuseStep 1176123 = 1764185) B1764185
theorem B1487479 : Blo 1174404 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B1176199 : Blo 1174404 1176199 := bstep (se 1 (by rfl) ⟨882149, by rfl⟩ : syracuseStep 1176199 = 1764299) B1764299
theorem B1176207 : Blo 1174404 1176207 := bstep (se 1 (by rfl) ⟨882155, by rfl⟩ : syracuseStep 1176207 = 1764311) B1764311
theorem B2642579 : Blo 1174404 2642579 := bstep (se 1 (by rfl) ⟨1981934, by rfl⟩ : syracuseStep 2642579 = 3963869) B3963869
theorem B1176251 : Blo 1174404 1176251 := bstep (se 1 (by rfl) ⟨882188, by rfl⟩ : syracuseStep 1176251 = 1764377) B1764377
theorem B7525057 : Blo 1174404 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B2642633 : Blo 1174404 2642633 := bstep (se 2 (by rfl) ⟨990987, by rfl⟩ : syracuseStep 2642633 = 1981975) B1981975
theorem B1176327 : Blo 1174404 1176327 := bstep (se 1 (by rfl) ⟨882245, by rfl⟩ : syracuseStep 1176327 = 1764491) B1764491
theorem B1176335 : Blo 1174404 1176335 := bstep (se 1 (by rfl) ⟨882251, by rfl⟩ : syracuseStep 1176335 = 1764503) B1764503
theorem B12071717 : Blo 1174404 12071717 := bstep (se 4 (by rfl) ⟨1131723, by rfl⟩ : syracuseStep 12071717 = 2263447) B2263447
theorem B1176379 : Blo 1174404 1176379 := bstep (se 1 (by rfl) ⟨882284, by rfl⟩ : syracuseStep 1176379 = 1764569) B1764569
theorem B1487803 : Blo 1174404 1487803 := bstep (se 1 (by rfl) ⟨1115852, by rfl⟩ : syracuseStep 1487803 = 2231705) B2231705
theorem B3814411 : Blo 1174404 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B20345867 : Blo 1174404 20345867 := bstep (se 1 (by rfl) ⟨15259400, by rfl⟩ : syracuseStep 20345867 = 30518801) B30518801
theorem B10040381 : Blo 1174404 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B6698213 : Blo 1174404 6698213 := bstep (se 4 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 6698213 = 1255915) B1255915
theorem B5231873 : Blo 1174404 5231873 := bstep (se 2 (by rfl) ⟨1961952, by rfl⟩ : syracuseStep 5231873 = 3923905) B3923905
theorem B3347831 : Blo 1174404 3347831 := bstep (se 1 (by rfl) ⟨2510873, by rfl⟩ : syracuseStep 3347831 = 5021747) B5021747
theorem B2643335 : Blo 1174404 2643335 := bstep (se 1 (by rfl) ⟨1982501, by rfl⟩ : syracuseStep 2643335 = 3965003) B3965003
theorem B38155805 : Blo 1174404 38155805 := bstep (se 3 (by rfl) ⟨7154213, by rfl⟩ : syracuseStep 38155805 = 14308427) B14308427
theorem B2643515 : Blo 1174404 2643515 := bstep (se 1 (by rfl) ⟨1982636, by rfl⟩ : syracuseStep 2643515 = 3965273) B3965273
theorem B2381447 : Blo 1174404 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B2643641 : Blo 1174404 2643641 := bstep (se 2 (by rfl) ⟨991365, by rfl⟩ : syracuseStep 2643641 = 1982731) B1982731
theorem B12891955 : Blo 1174404 12891955 := bstep (se 1 (by rfl) ⟨9668966, by rfl⟩ : syracuseStep 12891955 = 19337933) B19337933
theorem B4233019 : Blo 1174404 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B3176279 : Blo 1174404 3176279 := bstep (se 1 (by rfl) ⟨2382209, by rfl⟩ : syracuseStep 3176279 = 4764419) B4764419
theorem B1488775 : Blo 1174404 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B3766169 : Blo 1174404 3766169 := bstep (se 2 (by rfl) ⟨1412313, by rfl⟩ : syracuseStep 3766169 = 2824627) B2824627
theorem B2643983 : Blo 1174404 2643983 := bstep (se 1 (by rfl) ⟨1982987, by rfl⟩ : syracuseStep 2643983 = 3965975) B3965975
theorem B2644001 : Blo 1174404 2644001 := bstep (se 2 (by rfl) ⟨991500, by rfl⟩ : syracuseStep 2644001 = 1983001) B1983001
theorem B1587529 : Blo 1174404 1587529 := bstep (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) B1190647
theorem B2644343 : Blo 1174404 2644343 := bstep (se 1 (by rfl) ⟨1983257, by rfl⟩ : syracuseStep 2644343 = 3966515) B3966515
theorem B5945885 : Blo 1174404 5945885 := bstep (se 3 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 5945885 = 2229707) B2229707
theorem B2644523 : Blo 1174404 2644523 := bstep (se 1 (by rfl) ⟨1983392, by rfl⟩ : syracuseStep 2644523 = 3966785) B3966785
theorem B6355543 : Blo 1174404 6355543 := bstep (se 1 (by rfl) ⟨4766657, by rfl⟩ : syracuseStep 6355543 = 9533315) B9533315
theorem B12057265 : Blo 1174404 12057265 := bstep (se 2 (by rfl) ⟨4521474, by rfl⟩ : syracuseStep 12057265 = 9042949) B9042949
theorem B3963707 : Blo 1174404 3963707 := bstep (se 1 (by rfl) ⟨2972780, by rfl⟩ : syracuseStep 3963707 = 5945561) B5945561
theorem B6691673 : Blo 1174404 6691673 := bstep (se 2 (by rfl) ⟨2509377, by rfl⟩ : syracuseStep 6691673 = 5018755) B5018755
theorem B2644883 : Blo 1174404 2644883 := bstep (se 1 (by rfl) ⟨1983662, by rfl⟩ : syracuseStep 2644883 = 3967325) B3967325
theorem B4463545 : Blo 1174404 4463545 := bstep (se 2 (by rfl) ⟨1673829, by rfl⟩ : syracuseStep 4463545 = 3347659) B3347659
theorem B2644937 : Blo 1174404 2644937 := bstep (se 2 (by rfl) ⟨991851, by rfl⟩ : syracuseStep 2644937 = 1983703) B1983703
theorem B3349505 : Blo 1174404 3349505 := bstep (se 2 (by rfl) ⟨1256064, by rfl⟩ : syracuseStep 3349505 = 2512129) B2512129
theorem B5946371 : Blo 1174404 5946371 := bstep (se 1 (by rfl) ⟨4459778, by rfl⟩ : syracuseStep 5946371 = 8919557) B8919557
theorem B97876997 : Blo 1174404 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B3349619 : Blo 1174404 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B3964193 : Blo 1174404 3964193 := bstep (se 2 (by rfl) ⟨1486572, by rfl⟩ : syracuseStep 3964193 = 2973145) B2973145
theorem B6692129 : Blo 1174404 6692129 := bstep (se 2 (by rfl) ⟨2509548, by rfl⟩ : syracuseStep 6692129 = 5019097) B5019097
theorem B2825587 : Blo 1174404 2825587 := bstep (se 1 (by rfl) ⟨2119190, by rfl⟩ : syracuseStep 2825587 = 4238381) B4238381
theorem B6790547 : Blo 1174404 6790547 := bstep (se 1 (by rfl) ⟨5092910, by rfl⟩ : syracuseStep 6790547 = 10185821) B10185821
theorem B3349961 : Blo 1174404 3349961 := bstep (se 2 (by rfl) ⟨1256235, by rfl⟩ : syracuseStep 3349961 = 2512471) B2512471
theorem B8920529 : Blo 1174404 8920529 := bstep (se 2 (by rfl) ⟨3345198, by rfl⟩ : syracuseStep 8920529 = 6690397) B6690397
theorem B6692381 : Blo 1174404 6692381 := bstep (se 3 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 6692381 = 2509643) B2509643
theorem B114392675 : Blo 1174404 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B2645639 : Blo 1174404 2645639 := bstep (se 1 (by rfl) ⟨1984229, by rfl⟩ : syracuseStep 2645639 = 3968459) B3968459
theorem B1982137 : Blo 1174404 1982137 := bstep (se 2 (by rfl) ⟨743301, by rfl⟩ : syracuseStep 1982137 = 1486603) B1486603
theorem B12066497 : Blo 1174404 12066497 := bstep (se 2 (by rfl) ⟨4524936, by rfl⟩ : syracuseStep 12066497 = 9049873) B9049873
theorem B10862351 : Blo 1174404 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B5021473 : Blo 1174404 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B14286629 : Blo 1174404 14286629 := bstep (se 4 (by rfl) ⟨1339371, by rfl⟩ : syracuseStep 14286629 = 2678743) B2678743
theorem B2645819 : Blo 1174404 2645819 := bstep (se 1 (by rfl) ⟨1984364, by rfl⟩ : syracuseStep 2645819 = 3968729) B3968729
theorem B3964787 : Blo 1174404 3964787 := bstep (se 1 (by rfl) ⟨2973590, by rfl⟩ : syracuseStep 3964787 = 5947181) B5947181
theorem B5955443 : Blo 1174404 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B2645945 : Blo 1174404 2645945 := bstep (se 2 (by rfl) ⟨992229, by rfl⟩ : syracuseStep 2645945 = 1984459) B1984459
theorem B2646035 : Blo 1174404 2646035 := bstep (se 1 (by rfl) ⟨1984526, by rfl⟩ : syracuseStep 2646035 = 3969053) B3969053
theorem B7536797 : Blo 1174404 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B32162021 : Blo 1174404 32162021 := bstep (se 4 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 32162021 = 6030379) B6030379
theorem B1982711 : Blo 1174404 1982711 := bstep (se 1 (by rfl) ⟨1487033, by rfl⟩ : syracuseStep 1982711 = 2974067) B2974067
theorem B6693131 : Blo 1174404 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B1761641 : Blo 1174404 1761641 := bstep (se 2 (by rfl) ⟨660615, by rfl⟩ : syracuseStep 1761641 = 1321231) B1321231
theorem B2646377 : Blo 1174404 2646377 := bstep (se 2 (by rfl) ⟨992391, by rfl⟩ : syracuseStep 2646377 = 1984783) B1984783
theorem B3965327 : Blo 1174404 3965327 := bstep (se 1 (by rfl) ⟨2973995, by rfl⟩ : syracuseStep 3965327 = 5947991) B5947991
theorem B1761719 : Blo 1174404 1761719 := bstep (se 1 (by rfl) ⟨1321289, by rfl⟩ : syracuseStep 1761719 = 2642579) B2642579
theorem B1761755 : Blo 1174404 1761755 := bstep (se 1 (by rfl) ⟨1321316, by rfl⟩ : syracuseStep 1761755 = 2642633) B2642633
theorem B3179047 : Blo 1174404 3179047 := bstep (se 1 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 3179047 = 4768571) B4768571
theorem B1983055 : Blo 1174404 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B3965651 : Blo 1174404 3965651 := bstep (se 1 (by rfl) ⟨2974238, by rfl⟩ : syracuseStep 3965651 = 5948477) B5948477
theorem B6693587 : Blo 1174404 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B4465475 : Blo 1174404 4465475 := bstep (se 1 (by rfl) ⟨3349106, by rfl⟩ : syracuseStep 4465475 = 6698213) B6698213
theorem B1983305 : Blo 1174404 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B1762223 : Blo 1174404 1762223 := bstep (se 1 (by rfl) ⟨1321667, by rfl⟩ : syracuseStep 1762223 = 2643335) B2643335
theorem B33883055 : Blo 1174404 33883055 := bstep (se 1 (by rfl) ⟨25412291, by rfl⟩ : syracuseStep 33883055 = 50824583) B50824583
theorem B1672201 : Blo 1174404 1672201 := bstep (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) B1254151
theorem B1762313 : Blo 1174404 1762313 := bstep (se 2 (by rfl) ⟨660867, by rfl⟩ : syracuseStep 1762313 = 1321735) B1321735
theorem B25437203 : Blo 1174404 25437203 := bstep (se 1 (by rfl) ⟨19077902, by rfl⟩ : syracuseStep 25437203 = 38155805) B38155805
theorem B1762343 : Blo 1174404 1762343 := bstep (se 1 (by rfl) ⟨1321757, by rfl⟩ : syracuseStep 1762343 = 2643515) B2643515
theorem B1762427 : Blo 1174404 1762427 := bstep (se 1 (by rfl) ⟨1321820, by rfl⟩ : syracuseStep 1762427 = 2643641) B2643641
theorem B15262937 : Blo 1174404 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B1762553 : Blo 1174404 1762553 := bstep (se 2 (by rfl) ⟨660957, by rfl⟩ : syracuseStep 1762553 = 1321915) B1321915
theorem B1983737 : Blo 1174404 1983737 := bstep (se 2 (by rfl) ⟨743901, by rfl⟩ : syracuseStep 1983737 = 1487803) B1487803
theorem B1762655 : Blo 1174404 1762655 := bstep (se 1 (by rfl) ⟨1321991, by rfl⟩ : syracuseStep 1762655 = 2643983) B2643983
theorem B1762667 : Blo 1174404 1762667 := bstep (se 1 (by rfl) ⟨1322000, by rfl⟩ : syracuseStep 1762667 = 2644001) B2644001
theorem B1983919 : Blo 1174404 1983919 := bstep (se 1 (by rfl) ⟨1487939, by rfl⟩ : syracuseStep 1983919 = 2975879) B2975879
theorem B1984007 : Blo 1174404 1984007 := bstep (se 1 (by rfl) ⟨1488005, by rfl⟩ : syracuseStep 1984007 = 2976011) B2976011
theorem B1762895 : Blo 1174404 1762895 := bstep (se 1 (by rfl) ⟨1322171, by rfl⟩ : syracuseStep 1762895 = 2644343) B2644343
theorem B9528965 : Blo 1174404 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B6350525 : Blo 1174404 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B6694589 : Blo 1174404 6694589 := bstep (se 3 (by rfl) ⟨1255235, by rfl⟩ : syracuseStep 6694589 = 2510471) B2510471
theorem B1763015 : Blo 1174404 1763015 := bstep (se 1 (by rfl) ⟨1322261, by rfl⟩ : syracuseStep 1763015 = 2644523) B2644523
theorem B4466461 : Blo 1174404 4466461 := bstep (se 3 (by rfl) ⟨837461, by rfl⟩ : syracuseStep 4466461 = 1674923) B1674923
theorem B1984351 : Blo 1174404 1984351 := bstep (se 1 (by rfl) ⟨1488263, by rfl⟩ : syracuseStep 1984351 = 2976527) B2976527
theorem B1763177 : Blo 1174404 1763177 := bstep (se 2 (by rfl) ⟨661191, by rfl⟩ : syracuseStep 1763177 = 1322383) B1322383
theorem B3966839 : Blo 1174404 3966839 := bstep (se 1 (by rfl) ⟨2975129, by rfl⟩ : syracuseStep 3966839 = 5950259) B5950259
theorem B1763255 : Blo 1174404 1763255 := bstep (se 1 (by rfl) ⟨1322441, by rfl⟩ : syracuseStep 1763255 = 2644883) B2644883
theorem B1984439 : Blo 1174404 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B1763291 : Blo 1174404 1763291 := bstep (se 1 (by rfl) ⟨1322468, by rfl⟩ : syracuseStep 1763291 = 2644937) B2644937
theorem B65251331 : Blo 1174404 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B11290661 : Blo 1174404 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B3868729 : Blo 1174404 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B3967055 : Blo 1174404 3967055 := bstep (se 1 (by rfl) ⟨2975291, by rfl⟩ : syracuseStep 3967055 = 5950583) B5950583
theorem B1673465 : Blo 1174404 1673465 := bstep (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) B1255099
theorem B11299121 : Blo 1174404 11299121 := bstep (se 2 (by rfl) ⟨4237170, by rfl⟩ : syracuseStep 11299121 = 8474341) B8474341
theorem B1673579 : Blo 1174404 1673579 := bstep (se 1 (by rfl) ⟨1255184, by rfl⟩ : syracuseStep 1673579 = 2510369) B2510369
theorem B6695297 : Blo 1174404 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B76261783 : Blo 1174404 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B17189273 : Blo 1174404 17189273 := bstep (se 2 (by rfl) ⟨6445977, by rfl⟩ : syracuseStep 17189273 = 12891955) B12891955
theorem B1763759 : Blo 1174404 1763759 := bstep (se 1 (by rfl) ⟨1322819, by rfl⟩ : syracuseStep 1763759 = 2645639) B2645639
theorem B3967433 : Blo 1174404 3967433 := bstep (se 2 (by rfl) ⟨1487787, by rfl⟩ : syracuseStep 3967433 = 2975575) B2975575
theorem B1763849 : Blo 1174404 1763849 := bstep (se 2 (by rfl) ⟨661443, by rfl⟩ : syracuseStep 1763849 = 1322887) B1322887
theorem B1985033 : Blo 1174404 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B1763879 : Blo 1174404 1763879 := bstep (se 1 (by rfl) ⟨1322909, by rfl⟩ : syracuseStep 1763879 = 2645819) B2645819
theorem B1763963 : Blo 1174404 1763963 := bstep (se 1 (by rfl) ⟨1322972, by rfl⟩ : syracuseStep 1763963 = 2645945) B2645945
theorem B3967703 : Blo 1174404 3967703 := bstep (se 1 (by rfl) ⟨2975777, by rfl⟩ : syracuseStep 3967703 = 5951555) B5951555
theorem B1764089 : Blo 1174404 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B11299661 : Blo 1174404 11299661 := bstep (se 3 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 11299661 = 4237373) B4237373
theorem B2231135 : Blo 1174404 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B1764191 : Blo 1174404 1764191 := bstep (se 1 (by rfl) ⟨1323143, by rfl⟩ : syracuseStep 1764191 = 2646287) B2646287
theorem B1764203 : Blo 1174404 1764203 := bstep (se 1 (by rfl) ⟨1323152, by rfl⟩ : syracuseStep 1764203 = 2646305) B2646305
theorem B19049363 : Blo 1174404 19049363 := bstep (se 1 (by rfl) ⟨14287022, by rfl⟩ : syracuseStep 19049363 = 28574045) B28574045
theorem B72354707 : Blo 1174404 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B3345313 : Blo 1174404 3345313 := bstep (se 2 (by rfl) ⟨1254492, by rfl⟩ : syracuseStep 3345313 = 2508985) B2508985
theorem B1174447 : Blo 1174404 1174447 := bstep (se 1 (by rfl) ⟨880835, by rfl⟩ : syracuseStep 1174447 = 1761671) B1761671
theorem B3967919 : Blo 1174404 3967919 := bstep (se 1 (by rfl) ⟨2975939, by rfl⟩ : syracuseStep 3967919 = 5951879) B5951879
theorem B1174471 : Blo 1174404 1174471 := bstep (se 1 (by rfl) ⟨880853, by rfl⟩ : syracuseStep 1174471 = 1761707) B1761707
theorem B1174491 : Blo 1174404 1174491 := bstep (se 1 (by rfl) ⟨880868, by rfl⟩ : syracuseStep 1174491 = 1761737) B1761737
theorem B1174567 : Blo 1174404 1174567 := bstep (se 1 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 1174567 = 1761851) B1761851
theorem B1322023 : Blo 1174404 1322023 := bstep (se 1 (by rfl) ⟨991517, by rfl⟩ : syracuseStep 1322023 = 1983035) B1983035
theorem B1174607 : Blo 1174404 1174607 := bstep (se 1 (by rfl) ⟨880955, by rfl⟩ : syracuseStep 1174607 = 1761911) B1761911
theorem B1764431 : Blo 1174404 1764431 := bstep (se 1 (by rfl) ⟨1323323, by rfl⟩ : syracuseStep 1764431 = 2646647) B2646647
theorem B1174623 : Blo 1174404 1174623 := bstep (se 1 (by rfl) ⟨880967, by rfl⟩ : syracuseStep 1174623 = 1761935) B1761935
theorem B1191007 : Blo 1174404 1191007 := bstep (se 1 (by rfl) ⟨893255, by rfl⟩ : syracuseStep 1191007 = 1786511) B1786511
theorem B2116705 : Blo 1174404 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B1174651 : Blo 1174404 1174651 := bstep (se 1 (by rfl) ⟨880988, by rfl⟩ : syracuseStep 1174651 = 1761977) B1761977
theorem B1174703 : Blo 1174404 1174703 := bstep (se 1 (by rfl) ⟨881027, by rfl⟩ : syracuseStep 1174703 = 1762055) B1762055
theorem B50834627 : Blo 1174404 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B8047811 : Blo 1174404 8047811 := bstep (se 1 (by rfl) ⟨6035858, by rfl⟩ : syracuseStep 8047811 = 12071717) B12071717
theorem B1174727 : Blo 1174404 1174727 := bstep (se 1 (by rfl) ⟨881045, by rfl⟩ : syracuseStep 1174727 = 1762091) B1762091
theorem B1764551 : Blo 1174404 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B1174747 : Blo 1174404 1174747 := bstep (se 1 (by rfl) ⟨881060, by rfl⟩ : syracuseStep 1174747 = 1762121) B1762121
theorem B2231545 : Blo 1174404 2231545 := bstep (se 2 (by rfl) ⟨836829, by rfl⟩ : syracuseStep 2231545 = 1673659) B1673659
theorem B1174823 : Blo 1174404 1174823 := bstep (se 1 (by rfl) ⟨881117, by rfl⟩ : syracuseStep 1174823 = 1762235) B1762235
theorem B1174863 : Blo 1174404 1174863 := bstep (se 1 (by rfl) ⟨881147, by rfl⟩ : syracuseStep 1174863 = 1762295) B1762295
theorem B3763543 : Blo 1174404 3763543 := bstep (se 1 (by rfl) ⟨2822657, by rfl⟩ : syracuseStep 3763543 = 5645315) B5645315
theorem B1174879 : Blo 1174404 1174879 := bstep (se 1 (by rfl) ⟨881159, by rfl⟩ : syracuseStep 1174879 = 1762319) B1762319
theorem B1174907 : Blo 1174404 1174907 := bstep (se 1 (by rfl) ⟨881180, by rfl⟩ : syracuseStep 1174907 = 1762361) B1762361
theorem B1174959 : Blo 1174404 1174959 := bstep (se 1 (by rfl) ⟨881219, by rfl⟩ : syracuseStep 1174959 = 1762439) B1762439
theorem B1174983 : Blo 1174404 1174983 := bstep (se 1 (by rfl) ⟨881237, by rfl⟩ : syracuseStep 1174983 = 1762475) B1762475
theorem B8474057 : Blo 1174404 8474057 := bstep (se 2 (by rfl) ⟨3177771, by rfl⟩ : syracuseStep 8474057 = 6355543) B6355543
theorem B1175003 : Blo 1174404 1175003 := bstep (se 1 (by rfl) ⟨881252, by rfl⟩ : syracuseStep 1175003 = 1762505) B1762505
theorem B1175079 : Blo 1174404 1175079 := bstep (se 1 (by rfl) ⟨881309, by rfl⟩ : syracuseStep 1175079 = 1762619) B1762619
theorem B16076353 : Blo 1174404 16076353 := bstep (se 2 (by rfl) ⟨6028632, by rfl⟩ : syracuseStep 16076353 = 12057265) B12057265
theorem B1175119 : Blo 1174404 1175119 := bstep (se 1 (by rfl) ⟨881339, by rfl⟩ : syracuseStep 1175119 = 1762679) B1762679
theorem B2231887 : Blo 1174404 2231887 := bstep (se 1 (by rfl) ⟨1673915, by rfl⟩ : syracuseStep 2231887 = 3347831) B3347831
theorem B1175135 : Blo 1174404 1175135 := bstep (se 1 (by rfl) ⟨881351, by rfl⟩ : syracuseStep 1175135 = 1762703) B1762703
theorem B4460129 : Blo 1174404 4460129 := bstep (se 2 (by rfl) ⟨1672548, by rfl⟩ : syracuseStep 4460129 = 3345097) B3345097
theorem B1175163 : Blo 1174404 1175163 := bstep (se 1 (by rfl) ⟨881372, by rfl⟩ : syracuseStep 1175163 = 1762745) B1762745
theorem B1175215 : Blo 1174404 1175215 := bstep (se 1 (by rfl) ⟨881411, by rfl⟩ : syracuseStep 1175215 = 1762823) B1762823
theorem B1175239 : Blo 1174404 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B1175259 : Blo 1174404 1175259 := bstep (se 1 (by rfl) ⟨881444, by rfl⟩ : syracuseStep 1175259 = 1762889) B1762889
theorem B1175335 : Blo 1174404 1175335 := bstep (se 1 (by rfl) ⟨881501, by rfl⟩ : syracuseStep 1175335 = 1763003) B1763003
theorem B2232137 : Blo 1174404 2232137 := bstep (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) B1674103
theorem B1175375 : Blo 1174404 1175375 := bstep (se 1 (by rfl) ⟨881531, by rfl⟩ : syracuseStep 1175375 = 1763063) B1763063
theorem B1175391 : Blo 1174404 1175391 := bstep (se 1 (by rfl) ⟨881543, by rfl⟩ : syracuseStep 1175391 = 1763087) B1763087
theorem B2977631 : Blo 1174404 2977631 := bstep (se 1 (by rfl) ⟨2233223, by rfl⟩ : syracuseStep 2977631 = 4466447) B4466447
theorem B5648237 : Blo 1174404 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B1175419 : Blo 1174404 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B2117519 : Blo 1174404 2117519 := bstep (se 1 (by rfl) ⟨1588139, by rfl⟩ : syracuseStep 2117519 = 3176279) B3176279
theorem B5951393 : Blo 1174404 5951393 := bstep (se 2 (by rfl) ⟨2231772, by rfl⟩ : syracuseStep 5951393 = 4463545) B4463545
theorem B1175471 : Blo 1174404 1175471 := bstep (se 1 (by rfl) ⟨881603, by rfl⟩ : syracuseStep 1175471 = 1763207) B1763207
theorem B1486775 : Blo 1174404 1486775 := bstep (se 1 (by rfl) ⟨1115081, by rfl⟩ : syracuseStep 1486775 = 2230163) B2230163
theorem B2510779 : Blo 1174404 2510779 := bstep (se 1 (by rfl) ⟨1883084, by rfl⟩ : syracuseStep 2510779 = 3766169) B3766169
theorem B1175495 : Blo 1174404 1175495 := bstep (se 1 (by rfl) ⟨881621, by rfl⟩ : syracuseStep 1175495 = 1763243) B1763243
theorem B1175515 : Blo 1174404 1175515 := bstep (se 1 (by rfl) ⟨881636, by rfl⟩ : syracuseStep 1175515 = 1763273) B1763273
theorem B1175591 : Blo 1174404 1175591 := bstep (se 1 (by rfl) ⟨881693, by rfl⟩ : syracuseStep 1175591 = 1763387) B1763387
theorem B1486927 : Blo 1174404 1486927 := bstep (se 1 (by rfl) ⟨1115195, by rfl⟩ : syracuseStep 1486927 = 2230391) B2230391
theorem B1175631 : Blo 1174404 1175631 := bstep (se 1 (by rfl) ⟨881723, by rfl⟩ : syracuseStep 1175631 = 1763447) B1763447
theorem B7147601 : Blo 1174404 7147601 := bstep (se 2 (by rfl) ⟨2680350, by rfl⟩ : syracuseStep 7147601 = 5360701) B5360701
theorem B1175647 : Blo 1174404 1175647 := bstep (se 1 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 1175647 = 1763471) B1763471
theorem B1175675 : Blo 1174404 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B3346589 : Blo 1174404 3346589 := bstep (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) B1254971
theorem B15265955 : Blo 1174404 15265955 := bstep (se 1 (by rfl) ⟨11449466, by rfl⟩ : syracuseStep 15265955 = 22898933) B22898933
theorem B1175727 : Blo 1174404 1175727 := bstep (se 1 (by rfl) ⟨881795, by rfl⟩ : syracuseStep 1175727 = 1763591) B1763591
theorem B1175751 : Blo 1174404 1175751 := bstep (se 1 (by rfl) ⟨881813, by rfl⟩ : syracuseStep 1175751 = 1763627) B1763627
theorem B1175771 : Blo 1174404 1175771 := bstep (se 1 (by rfl) ⟨881828, by rfl⟩ : syracuseStep 1175771 = 1763657) B1763657
theorem B1175847 : Blo 1174404 1175847 := bstep (se 1 (by rfl) ⟨881885, by rfl⟩ : syracuseStep 1175847 = 1763771) B1763771
theorem B1175887 : Blo 1174404 1175887 := bstep (se 1 (by rfl) ⟨881915, by rfl⟩ : syracuseStep 1175887 = 1763831) B1763831
theorem B1175903 : Blo 1174404 1175903 := bstep (se 1 (by rfl) ⟨881927, by rfl⟩ : syracuseStep 1175903 = 1763855) B1763855
theorem B1175931 : Blo 1174404 1175931 := bstep (se 1 (by rfl) ⟨881948, by rfl⟩ : syracuseStep 1175931 = 1763897) B1763897
theorem B1175983 : Blo 1174404 1175983 := bstep (se 1 (by rfl) ⟨881987, by rfl⟩ : syracuseStep 1175983 = 1763975) B1763975
theorem B1176007 : Blo 1174404 1176007 := bstep (se 1 (by rfl) ⟨882005, by rfl⟩ : syracuseStep 1176007 = 1764011) B1764011
theorem B1176027 : Blo 1174404 1176027 := bstep (se 1 (by rfl) ⟨882020, by rfl⟩ : syracuseStep 1176027 = 1764041) B1764041
theorem B15692291 : Blo 1174404 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B3576329 : Blo 1174404 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B16937495 : Blo 1174404 16937495 := bstep (se 1 (by rfl) ⟨12703121, by rfl⟩ : syracuseStep 16937495 = 25406243) B25406243
theorem B6697505 : Blo 1174404 6697505 := bstep (se 2 (by rfl) ⟨2511564, by rfl⟩ : syracuseStep 6697505 = 5023129) B5023129
theorem B2642471 : Blo 1174404 2642471 := bstep (se 1 (by rfl) ⟨1981853, by rfl⟩ : syracuseStep 2642471 = 3963707) B3963707
theorem B1176103 : Blo 1174404 1176103 := bstep (se 1 (by rfl) ⟨882077, by rfl⟩ : syracuseStep 1176103 = 1764155) B1764155
theorem B4461115 : Blo 1174404 4461115 := bstep (se 1 (by rfl) ⟨3345836, by rfl⟩ : syracuseStep 4461115 = 6691673) B6691673
theorem B1176143 : Blo 1174404 1176143 := bstep (se 1 (by rfl) ⟨882107, by rfl⟩ : syracuseStep 1176143 = 1764215) B1764215
theorem B1176159 : Blo 1174404 1176159 := bstep (se 1 (by rfl) ⟨882119, by rfl⟩ : syracuseStep 1176159 = 1764239) B1764239
theorem B15069797 : Blo 1174404 15069797 := bstep (se 4 (by rfl) ⟨1412793, by rfl⟩ : syracuseStep 15069797 = 2825587) B2825587
theorem B1176187 : Blo 1174404 1176187 := bstep (se 1 (by rfl) ⟨882140, by rfl⟩ : syracuseStep 1176187 = 1764281) B1764281
theorem B3764875 : Blo 1174404 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B2233003 : Blo 1174404 2233003 := bstep (se 1 (by rfl) ⟨1674752, by rfl⟩ : syracuseStep 2233003 = 3349505) B3349505
theorem B1176239 : Blo 1174404 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B6689465 : Blo 1174404 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B1176263 : Blo 1174404 1176263 := bstep (se 1 (by rfl) ⟨882197, by rfl⟩ : syracuseStep 1176263 = 1764395) B1764395
theorem B1176283 : Blo 1174404 1176283 := bstep (se 1 (by rfl) ⟨882212, by rfl⟩ : syracuseStep 1176283 = 1764425) B1764425
theorem B2233079 : Blo 1174404 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B38097677 : Blo 1174404 38097677 := bstep (se 3 (by rfl) ⟨7143314, by rfl⟩ : syracuseStep 38097677 = 14286629) B14286629
theorem B1176359 : Blo 1174404 1176359 := bstep (se 1 (by rfl) ⟨882269, by rfl⟩ : syracuseStep 1176359 = 1764539) B1764539
theorem B1176399 : Blo 1174404 1176399 := bstep (se 1 (by rfl) ⟨882299, by rfl⟩ : syracuseStep 1176399 = 1764599) B1764599
theorem B2642795 : Blo 1174404 2642795 := bstep (se 1 (by rfl) ⟨1982096, by rfl⟩ : syracuseStep 2642795 = 3964193) B3964193
theorem B4461419 : Blo 1174404 4461419 := bstep (se 1 (by rfl) ⟨3346064, by rfl⟩ : syracuseStep 4461419 = 6692129) B6692129
theorem B2642849 : Blo 1174404 2642849 := bstep (se 2 (by rfl) ⟨991068, by rfl⟩ : syracuseStep 2642849 = 1982137) B1982137
theorem B4527031 : Blo 1174404 4527031 := bstep (se 1 (by rfl) ⟨3395273, by rfl⟩ : syracuseStep 4527031 = 6790547) B6790547
theorem B2233307 : Blo 1174404 2233307 := bstep (se 1 (by rfl) ⟨1674980, by rfl⟩ : syracuseStep 2233307 = 3349961) B3349961
theorem B4461587 : Blo 1174404 4461587 := bstep (se 1 (by rfl) ⟨3346190, by rfl⟩ : syracuseStep 4461587 = 6692381) B6692381
theorem B7533647 : Blo 1174404 7533647 := bstep (se 1 (by rfl) ⟨5650235, by rfl⟩ : syracuseStep 7533647 = 11300471) B11300471
theorem B38122589 : Blo 1174404 38122589 := bstep (se 3 (by rfl) ⟨7147985, by rfl⟩ : syracuseStep 38122589 = 14295971) B14295971
theorem B8926361 : Blo 1174404 8926361 := bstep (se 2 (by rfl) ⟨3347385, by rfl⟩ : syracuseStep 8926361 = 6694771) B6694771
theorem B1488071 : Blo 1174404 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B2643191 : Blo 1174404 2643191 := bstep (se 1 (by rfl) ⟨1982393, by rfl⟩ : syracuseStep 2643191 = 3964787) B3964787
theorem B3970295 : Blo 1174404 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B1488223 : Blo 1174404 1488223 := bstep (se 1 (by rfl) ⟨1116167, by rfl⟩ : syracuseStep 1488223 = 2232335) B2232335
theorem B1611343 : Blo 1174404 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B3815111 : Blo 1174404 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B2643785 : Blo 1174404 2643785 := bstep (se 2 (by rfl) ⟨991419, by rfl⟩ : syracuseStep 2643785 = 1982839) B1982839
theorem B6035309 : Blo 1174404 6035309 := bstep (se 3 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 6035309 = 2263241) B2263241
theorem B18102209 : Blo 1174404 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B13563911 : Blo 1174404 13563911 := bstep (se 1 (by rfl) ⟨10172933, by rfl⟩ : syracuseStep 13563911 = 20345867) B20345867
theorem B3487915 : Blo 1174404 3487915 := bstep (se 1 (by rfl) ⟨2615936, by rfl⟩ : syracuseStep 3487915 = 5231873) B5231873
theorem B10033409 : Blo 1174404 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B5028157 : Blo 1174404 5028157 := bstep (se 3 (by rfl) ⟨942779, by rfl⟩ : syracuseStep 5028157 = 1885559) B1885559
theorem B2644577 : Blo 1174404 2644577 := bstep (se 2 (by rfl) ⟨991716, by rfl⟩ : syracuseStep 2644577 = 1983433) B1983433
theorem B5085881 : Blo 1174404 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B27532021 : Blo 1174404 27532021 := bstep (se 5 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 27532021 = 2581127) B2581127
theorem B2644919 : Blo 1174404 2644919 := bstep (se 1 (by rfl) ⟨1983689, by rfl⟩ : syracuseStep 2644919 = 3967379) B3967379
theorem B3963923 : Blo 1174404 3963923 := bstep (se 1 (by rfl) ⟨2972942, by rfl⟩ : syracuseStep 3963923 = 5945885) B5945885
theorem B8928305 : Blo 1174404 8928305 := bstep (se 2 (by rfl) ⟨3348114, by rfl⟩ : syracuseStep 8928305 = 6696229) B6696229
theorem B8477891 : Blo 1174404 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B8592655 : Blo 1174404 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B13393187 : Blo 1174404 13393187 := bstep (se 1 (by rfl) ⟨10044890, by rfl⟩ : syracuseStep 13393187 = 20089781) B20089781
theorem B3964247 : Blo 1174404 3964247 := bstep (se 1 (by rfl) ⟨2973185, by rfl⟩ : syracuseStep 3964247 = 5946371) B5946371
theorem B2645513 : Blo 1174404 2645513 := bstep (se 2 (by rfl) ⟨992067, by rfl⟩ : syracuseStep 2645513 = 1984135) B1984135
theorem B1982009 : Blo 1174404 1982009 := bstep (se 2 (by rfl) ⟨743253, by rfl⟩ : syracuseStep 1982009 = 1486507) B1486507
theorem B54320705 : Blo 1174404 54320705 := bstep (se 2 (by rfl) ⟨20370264, by rfl⟩ : syracuseStep 54320705 = 40740529) B40740529
theorem B2973307 : Blo 1174404 2973307 := bstep (se 1 (by rfl) ⟨2229980, by rfl⟩ : syracuseStep 2973307 = 4459961) B4459961
theorem B5947019 : Blo 1174404 5947019 := bstep (se 1 (by rfl) ⟨4460264, by rfl⟩ : syracuseStep 5947019 = 8920529) B8920529
theorem B10182365 : Blo 1174404 10182365 := bstep (se 3 (by rfl) ⟨1909193, by rfl⟩ : syracuseStep 10182365 = 3818387) B3818387
theorem B5644025 : Blo 1174404 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B8044331 : Blo 1174404 8044331 := bstep (se 1 (by rfl) ⟨6033248, by rfl⟩ : syracuseStep 8044331 = 12066497) B12066497
theorem B7241567 : Blo 1174404 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B1695583 : Blo 1174404 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B2645855 : Blo 1174404 2645855 := bstep (se 1 (by rfl) ⟨1984391, by rfl⟩ : syracuseStep 2645855 = 3968783) B3968783
theorem B4464503 : Blo 1174404 4464503 := bstep (se 1 (by rfl) ⟨3348377, by rfl⟩ : syracuseStep 4464503 = 6696755) B6696755
theorem B1982569 : Blo 1174404 1982569 := bstep (se 2 (by rfl) ⟨743463, by rfl⟩ : syracuseStep 1982569 = 1486927) B1486927
theorem B10461527 : Blo 1174404 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B2384219 : Blo 1174404 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B4465003 : Blo 1174404 4465003 := bstep (se 1 (by rfl) ⟨3348752, by rfl⟩ : syracuseStep 4465003 = 6697505) B6697505
theorem B1761647 : Blo 1174404 1761647 := bstep (se 1 (by rfl) ⟨1321235, by rfl⟩ : syracuseStep 1761647 = 2642471) B2642471
theorem B1761863 : Blo 1174404 1761863 := bstep (se 1 (by rfl) ⟨1321397, by rfl⟩ : syracuseStep 1761863 = 2642795) B2642795
theorem B2974279 : Blo 1174404 2974279 := bstep (se 1 (by rfl) ⟨2230709, by rfl⟩ : syracuseStep 2974279 = 4461419) B4461419
theorem B1761899 : Blo 1174404 1761899 := bstep (se 1 (by rfl) ⟨1321424, by rfl⟩ : syracuseStep 1761899 = 2642849) B2642849
theorem B2974391 : Blo 1174404 2974391 := bstep (se 1 (by rfl) ⟨2230793, by rfl⟩ : syracuseStep 2974391 = 4461587) B4461587
theorem B16958135 : Blo 1174404 16958135 := bstep (se 1 (by rfl) ⟨12718601, by rfl⟩ : syracuseStep 16958135 = 25437203) B25437203
theorem B5022431 : Blo 1174404 5022431 := bstep (se 1 (by rfl) ⟨3766823, by rfl⟩ : syracuseStep 5022431 = 7533647) B7533647
theorem B5948153 : Blo 1174404 5948153 := bstep (se 2 (by rfl) ⟨2230557, by rfl⟩ : syracuseStep 5948153 = 4461115) B4461115
theorem B10175291 : Blo 1174404 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1762127 : Blo 1174404 1762127 := bstep (se 1 (by rfl) ⟨1321595, by rfl⟩ : syracuseStep 1762127 = 2643191) B2643191
theorem B2646863 : Blo 1174404 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B36709361 : Blo 1174404 36709361 := bstep (se 2 (by rfl) ⟨13766010, by rfl⟩ : syracuseStep 36709361 = 27532021) B27532021
theorem B1762523 : Blo 1174404 1762523 := bstep (se 1 (by rfl) ⟨1321892, by rfl⟩ : syracuseStep 1762523 = 2643785) B2643785
theorem B4023539 : Blo 1174404 4023539 := bstep (se 1 (by rfl) ⟨3017654, by rfl⟩ : syracuseStep 4023539 = 6035309) B6035309
theorem B43500887 : Blo 1174404 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B2229601 : Blo 1174404 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B1762697 : Blo 1174404 1762697 := bstep (se 2 (by rfl) ⟨661011, by rfl⟩ : syracuseStep 1762697 = 1322023) B1322023
theorem B2975393 : Blo 1174404 2975393 := bstep (se 2 (by rfl) ⟨1115772, by rfl⟩ : syracuseStep 2975393 = 2231545) B2231545
theorem B1763051 : Blo 1174404 1763051 := bstep (se 1 (by rfl) ⟨1322288, by rfl⟩ : syracuseStep 1763051 = 2644577) B2644577
theorem B1984297 : Blo 1174404 1984297 := bstep (se 2 (by rfl) ⟨744111, by rfl⟩ : syracuseStep 1984297 = 1488223) B1488223
theorem B12699575 : Blo 1174404 12699575 := bstep (se 1 (by rfl) ⟨9524681, by rfl⟩ : syracuseStep 12699575 = 19049363) B19049363
theorem B48236471 : Blo 1174404 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B1763279 : Blo 1174404 1763279 := bstep (se 1 (by rfl) ⟨1322459, by rfl⟩ : syracuseStep 1763279 = 2644919) B2644919
theorem B2975849 : Blo 1174404 2975849 := bstep (se 2 (by rfl) ⟨1115943, by rfl⟩ : syracuseStep 2975849 = 2231887) B2231887
theorem B2148457 : Blo 1174404 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B19310845 : Blo 1174404 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B1763675 : Blo 1174404 1763675 := bstep (se 1 (by rfl) ⟨1322756, by rfl⟩ : syracuseStep 1763675 = 2645513) B2645513
theorem B1321339 : Blo 1174404 1321339 := bstep (se 1 (by rfl) ⟨991004, by rfl⟩ : syracuseStep 1321339 = 1982009) B1982009
theorem B3762683 : Blo 1174404 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B1763903 : Blo 1174404 1763903 := bstep (se 1 (by rfl) ⟨1322927, by rfl⟩ : syracuseStep 1763903 = 2645855) B2645855
theorem B1985087 : Blo 1174404 1985087 := bstep (se 1 (by rfl) ⟨1488815, by rfl⟩ : syracuseStep 1985087 = 2977631) B2977631
theorem B2976335 : Blo 1174404 2976335 := bstep (se 1 (by rfl) ⟨2232251, by rfl⟩ : syracuseStep 2976335 = 4464503) B4464503
theorem B1411679 : Blo 1174404 1411679 := bstep (se 1 (by rfl) ⟨1058759, by rfl⟩ : syracuseStep 1411679 = 2117519) B2117519
theorem B3967595 : Blo 1174404 3967595 := bstep (se 1 (by rfl) ⟨2975696, by rfl⟩ : syracuseStep 3967595 = 5951393) B5951393
theorem B1764023 : Blo 1174404 1764023 := bstep (se 1 (by rfl) ⟨1323017, by rfl⟩ : syracuseStep 1764023 = 2646035) B2646035
theorem B2231059 : Blo 1174404 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B5024531 : Blo 1174404 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B21441347 : Blo 1174404 21441347 := bstep (se 1 (by rfl) ⟨16081010, by rfl⟩ : syracuseStep 21441347 = 32162021) B32162021
theorem B1321807 : Blo 1174404 1321807 := bstep (se 1 (by rfl) ⟨991355, by rfl⟩ : syracuseStep 1321807 = 1982711) B1982711
theorem B1174427 : Blo 1174404 1174427 := bstep (se 1 (by rfl) ⟨880820, by rfl⟩ : syracuseStep 1174427 = 1761641) B1761641
theorem B1764251 : Blo 1174404 1764251 := bstep (se 1 (by rfl) ⟨1323188, by rfl⟩ : syracuseStep 1764251 = 2646377) B2646377
theorem B1174479 : Blo 1174404 1174479 := bstep (se 1 (by rfl) ⟨880859, by rfl⟩ : syracuseStep 1174479 = 1761719) B1761719
theorem B1174503 : Blo 1174404 1174503 := bstep (se 1 (by rfl) ⟨880877, by rfl⟩ : syracuseStep 1174503 = 1761755) B1761755
theorem B11291663 : Blo 1174404 11291663 := bstep (se 1 (by rfl) ⟨8468747, by rfl⟩ : syracuseStep 11291663 = 16937495) B16937495
theorem B10046531 : Blo 1174404 10046531 := bstep (se 1 (by rfl) ⟨7534898, by rfl⟩ : syracuseStep 10046531 = 15069797) B15069797
theorem B6704209 : Blo 1174404 6704209 := bstep (se 2 (by rfl) ⟨2514078, by rfl⟩ : syracuseStep 6704209 = 5028157) B5028157
theorem B40709213 : Blo 1174404 40709213 := bstep (se 3 (by rfl) ⟨7632977, by rfl⟩ : syracuseStep 40709213 = 15265955) B15265955
theorem B4459643 : Blo 1174404 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B25398451 : Blo 1174404 25398451 := bstep (se 1 (by rfl) ⟨19048838, by rfl⟩ : syracuseStep 25398451 = 38097677) B38097677
theorem B3968189 : Blo 1174404 3968189 := bstep (se 3 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 3968189 = 1488071) B1488071
theorem B101682377 : Blo 1174404 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B2976983 : Blo 1174404 2976983 := bstep (se 1 (by rfl) ⟨2232737, by rfl⟩ : syracuseStep 2976983 = 4465475) B4465475
theorem B1322203 : Blo 1174404 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B1174815 : Blo 1174404 1174815 := bstep (se 1 (by rfl) ⟨881111, by rfl⟩ : syracuseStep 1174815 = 1762223) B1762223
theorem B22588703 : Blo 1174404 22588703 := bstep (se 1 (by rfl) ⟨16941527, by rfl⟩ : syracuseStep 22588703 = 33883055) B33883055
theorem B1174875 : Blo 1174404 1174875 := bstep (se 1 (by rfl) ⟨881156, by rfl⟩ : syracuseStep 1174875 = 1762313) B1762313
theorem B1174895 : Blo 1174404 1174895 := bstep (se 1 (by rfl) ⟨881171, by rfl⟩ : syracuseStep 1174895 = 1762343) B1762343
theorem B4238729 : Blo 1174404 4238729 := bstep (se 2 (by rfl) ⟨1589523, by rfl⟩ : syracuseStep 4238729 = 3179047) B3179047
theorem B25415059 : Blo 1174404 25415059 := bstep (se 1 (by rfl) ⟨19061294, by rfl⟩ : syracuseStep 25415059 = 38122589) B38122589
theorem B1174951 : Blo 1174404 1174951 := bstep (se 1 (by rfl) ⟨881213, by rfl⟩ : syracuseStep 1174951 = 1762427) B1762427
theorem B5950907 : Blo 1174404 5950907 := bstep (se 1 (by rfl) ⟨4463180, by rfl⟩ : syracuseStep 5950907 = 8926361) B8926361
theorem B1175035 : Blo 1174404 1175035 := bstep (se 1 (by rfl) ⟨881276, by rfl⟩ : syracuseStep 1175035 = 1762553) B1762553
theorem B1322491 : Blo 1174404 1322491 := bstep (se 1 (by rfl) ⟨991868, by rfl⟩ : syracuseStep 1322491 = 1983737) B1983737
theorem B2977337 : Blo 1174404 2977337 := bstep (se 2 (by rfl) ⟨1116501, by rfl⟩ : syracuseStep 2977337 = 2233003) B2233003
theorem B1175103 : Blo 1174404 1175103 := bstep (se 1 (by rfl) ⟨881327, by rfl⟩ : syracuseStep 1175103 = 1762655) B1762655
theorem B1175111 : Blo 1174404 1175111 := bstep (se 1 (by rfl) ⟨881333, by rfl⟩ : syracuseStep 1175111 = 1762667) B1762667
theorem B1322671 : Blo 1174404 1322671 := bstep (se 1 (by rfl) ⟨992003, by rfl⟩ : syracuseStep 1322671 = 1984007) B1984007
theorem B1175263 : Blo 1174404 1175263 := bstep (se 1 (by rfl) ⟨881447, by rfl⟩ : syracuseStep 1175263 = 1762895) B1762895
theorem B45838061 : Blo 1174404 45838061 := bstep (se 3 (by rfl) ⟨8594636, by rfl⟩ : syracuseStep 45838061 = 17189273) B17189273
theorem B6352643 : Blo 1174404 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B2543407 : Blo 1174404 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B1175343 : Blo 1174404 1175343 := bstep (se 1 (by rfl) ⟨881507, by rfl⟩ : syracuseStep 1175343 = 1763015) B1763015
theorem B4460417 : Blo 1174404 4460417 := bstep (se 2 (by rfl) ⟨1672656, by rfl⟩ : syracuseStep 4460417 = 3345313) B3345313
theorem B1175451 : Blo 1174404 1175451 := bstep (se 1 (by rfl) ⟨881588, by rfl⟩ : syracuseStep 1175451 = 1763177) B1763177
theorem B1175503 : Blo 1174404 1175503 := bstep (se 1 (by rfl) ⟨881627, by rfl⟩ : syracuseStep 1175503 = 1763255) B1763255
theorem B1322959 : Blo 1174404 1322959 := bstep (se 1 (by rfl) ⟨992219, by rfl⟩ : syracuseStep 1322959 = 1984439) B1984439
theorem B1175527 : Blo 1174404 1175527 := bstep (se 1 (by rfl) ⟨881645, by rfl⟩ : syracuseStep 1175527 = 1763291) B1763291
theorem B2822273 : Blo 1174404 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B6688939 : Blo 1174404 6688939 := bstep (se 1 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 6688939 = 10033409) B10033409
theorem B7532747 : Blo 1174404 7532747 := bstep (se 1 (by rfl) ⟨5649560, by rfl⟩ : syracuseStep 7532747 = 11299121) B11299121
theorem B1175839 : Blo 1174404 1175839 := bstep (se 1 (by rfl) ⟨881879, by rfl⟩ : syracuseStep 1175839 = 1763759) B1763759
theorem B1175899 : Blo 1174404 1175899 := bstep (se 1 (by rfl) ⟨881924, by rfl⟩ : syracuseStep 1175899 = 1763849) B1763849
theorem B1323355 : Blo 1174404 1323355 := bstep (se 1 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 1323355 = 1985033) B1985033
theorem B11456873 : Blo 1174404 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B1175919 : Blo 1174404 1175919 := bstep (se 1 (by rfl) ⟨881939, by rfl⟩ : syracuseStep 1175919 = 1763879) B1763879
theorem B1175975 : Blo 1174404 1175975 := bstep (se 1 (by rfl) ⟨881981, by rfl⟩ : syracuseStep 1175975 = 1763963) B1763963
theorem B5018057 : Blo 1174404 5018057 := bstep (se 2 (by rfl) ⟨1881771, by rfl⟩ : syracuseStep 5018057 = 3763543) B3763543
theorem B1176059 : Blo 1174404 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B7533107 : Blo 1174404 7533107 := bstep (se 1 (by rfl) ⟨5649830, by rfl⟩ : syracuseStep 7533107 = 11299661) B11299661
theorem B1487423 : Blo 1174404 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B1176127 : Blo 1174404 1176127 := bstep (se 1 (by rfl) ⟨882095, by rfl⟩ : syracuseStep 1176127 = 1764191) B1764191
theorem B1176135 : Blo 1174404 1176135 := bstep (se 1 (by rfl) ⟨882101, by rfl⟩ : syracuseStep 1176135 = 1764203) B1764203
theorem B193090229 : Blo 1174404 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B2642615 : Blo 1174404 2642615 := bstep (se 1 (by rfl) ⟨1981961, by rfl⟩ : syracuseStep 2642615 = 3963923) B3963923
theorem B5952203 : Blo 1174404 5952203 := bstep (se 1 (by rfl) ⟨4464152, by rfl⟩ : syracuseStep 5952203 = 8928305) B8928305
theorem B1176287 : Blo 1174404 1176287 := bstep (se 1 (by rfl) ⟨882215, by rfl⟩ : syracuseStep 1176287 = 1764431) B1764431
theorem B21435137 : Blo 1174404 21435137 := bstep (se 2 (by rfl) ⟨8038176, by rfl⟩ : syracuseStep 21435137 = 16076353) B16076353
theorem B21451549 : Blo 1174404 21451549 := bstep (se 3 (by rfl) ⟨4022165, by rfl⟩ : syracuseStep 21451549 = 8044331) B8044331
theorem B1176367 : Blo 1174404 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B5952365 : Blo 1174404 5952365 := bstep (se 3 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 5952365 = 2232137) B2232137
theorem B2642831 : Blo 1174404 2642831 := bstep (se 1 (by rfl) ⟨1982123, by rfl⟩ : syracuseStep 2642831 = 3964247) B3964247
theorem B5649371 : Blo 1174404 5649371 := bstep (se 1 (by rfl) ⟨4237028, by rfl⟩ : syracuseStep 5649371 = 8474057) B8474057
theorem B36213803 : Blo 1174404 36213803 := bstep (se 1 (by rfl) ⟨27160352, by rfl⟩ : syracuseStep 36213803 = 54320705) B54320705
theorem B6788243 : Blo 1174404 6788243 := bstep (se 1 (by rfl) ⟨5091182, by rfl⟩ : syracuseStep 6788243 = 10182365) B10182365
theorem B3765491 : Blo 1174404 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B3347705 : Blo 1174404 3347705 := bstep (se 2 (by rfl) ⟨1255389, by rfl⟩ : syracuseStep 3347705 = 2510779) B2510779
theorem B4765067 : Blo 1174404 4765067 := bstep (se 1 (by rfl) ⟨3573800, by rfl⟩ : syracuseStep 4765067 = 7147601) B7147601
theorem B4462087 : Blo 1174404 4462087 := bstep (se 1 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 4462087 = 6693131) B6693131
theorem B4650553 : Blo 1174404 4650553 := bstep (se 2 (by rfl) ⟨1743957, by rfl⟩ : syracuseStep 4650553 = 3487915) B3487915
theorem B2643551 : Blo 1174404 2643551 := bstep (se 1 (by rfl) ⟨1982663, by rfl⟩ : syracuseStep 2643551 = 3965327) B3965327
theorem B20633221 : Blo 1174404 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B2643767 : Blo 1174404 2643767 := bstep (se 1 (by rfl) ⟨1982825, by rfl⟩ : syracuseStep 2643767 = 3965651) B3965651
theorem B4462391 : Blo 1174404 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B1488719 : Blo 1174404 1488719 := bstep (se 1 (by rfl) ⟨1116539, by rfl⟩ : syracuseStep 1488719 = 2233079) B2233079
theorem B1488871 : Blo 1174404 1488871 := bstep (se 1 (by rfl) ⟨1116653, by rfl⟩ : syracuseStep 1488871 = 2233307) B2233307
theorem B4462573 : Blo 1174404 4462573 := bstep (se 3 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 4462573 = 1673465) B1673465
theorem B2644073 : Blo 1174404 2644073 := bstep (se 2 (by rfl) ⟨991527, by rfl⟩ : syracuseStep 2644073 = 1983055) B1983055
theorem B5019833 : Blo 1174404 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B4462877 : Blo 1174404 4462877 := bstep (se 3 (by rfl) ⟨836789, by rfl⟩ : syracuseStep 4462877 = 1673579) B1673579
theorem B4233683 : Blo 1174404 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B4463059 : Blo 1174404 4463059 := bstep (se 1 (by rfl) ⟨3347294, by rfl⟩ : syracuseStep 4463059 = 6694589) B6694589
theorem B6036041 : Blo 1174404 6036041 := bstep (se 2 (by rfl) ⟨2263515, by rfl⟩ : syracuseStep 6036041 = 4527031) B4527031
theorem B2644559 : Blo 1174404 2644559 := bstep (se 1 (by rfl) ⟨1983419, by rfl⟩ : syracuseStep 2644559 = 3966839) B3966839
theorem B9042607 : Blo 1174404 9042607 := bstep (se 1 (by rfl) ⟨6781955, by rfl⟩ : syracuseStep 9042607 = 13563911) B13563911
theorem B7527107 : Blo 1174404 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B2644703 : Blo 1174404 2644703 := bstep (se 1 (by rfl) ⟨1983527, by rfl⟩ : syracuseStep 2644703 = 3967055) B3967055
theorem B1588009 : Blo 1174404 1588009 := bstep (se 2 (by rfl) ⟨595503, by rfl⟩ : syracuseStep 1588009 = 1191007) B1191007
theorem B4463531 : Blo 1174404 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B2644955 : Blo 1174404 2644955 := bstep (se 1 (by rfl) ⟨1983716, by rfl⟩ : syracuseStep 2644955 = 3967433) B3967433
theorem B3390587 : Blo 1174404 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2645135 : Blo 1174404 2645135 := bstep (se 1 (by rfl) ⟨1983851, by rfl⟩ : syracuseStep 2645135 = 3967703) B3967703
theorem B9043109 : Blo 1174404 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B2645225 : Blo 1174404 2645225 := bstep (se 2 (by rfl) ⟨991959, by rfl⟩ : syracuseStep 2645225 = 1983919) B1983919
theorem B2645279 : Blo 1174404 2645279 := bstep (se 1 (by rfl) ⟨1983959, by rfl⟩ : syracuseStep 2645279 = 3967919) B3967919
theorem B33889751 : Blo 1174404 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B5651927 : Blo 1174404 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B5365207 : Blo 1174404 5365207 := bstep (se 1 (by rfl) ⟨4023905, by rfl⟩ : syracuseStep 5365207 = 8047811) B8047811
theorem B3964409 : Blo 1174404 3964409 := bstep (se 2 (by rfl) ⟨1486653, by rfl⟩ : syracuseStep 3964409 = 2973307) B2973307
theorem B8928791 : Blo 1174404 8928791 := bstep (se 1 (by rfl) ⟨6696593, by rfl⟩ : syracuseStep 8928791 = 13393187) B13393187
theorem B5955281 : Blo 1174404 5955281 := bstep (se 2 (by rfl) ⟨2233230, by rfl⟩ : syracuseStep 5955281 = 4466461) B4466461
theorem B2973419 : Blo 1174404 2973419 := bstep (se 1 (by rfl) ⟨2230064, by rfl⟩ : syracuseStep 2973419 = 4460129) B4460129
theorem B3964679 : Blo 1174404 3964679 := bstep (se 1 (by rfl) ⟨2973509, by rfl⟩ : syracuseStep 3964679 = 5947019) B5947019
theorem B2645801 : Blo 1174404 2645801 := bstep (se 2 (by rfl) ⟨992175, by rfl⟩ : syracuseStep 2645801 = 1984351) B1984351
theorem B3964733 : Blo 1174404 3964733 := bstep (se 3 (by rfl) ⟨743387, by rfl⟩ : syracuseStep 3964733 = 1486775) B1486775
theorem B5021831 : Blo 1174404 5021831 := bstep (se 1 (by rfl) ⟨3766373, by rfl⟩ : syracuseStep 5021831 = 7532747) B7532747
theorem B25747793 : Blo 1174404 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B5022071 : Blo 1174404 5022071 := bstep (se 1 (by rfl) ⟨3766553, by rfl⟩ : syracuseStep 5022071 = 7533107) B7533107
theorem B1761743 : Blo 1174404 1761743 := bstep (se 1 (by rfl) ⟨1321307, by rfl⟩ : syracuseStep 1761743 = 2642615) B2642615
theorem B1982927 : Blo 1174404 1982927 := bstep (se 1 (by rfl) ⟨1487195, by rfl⟩ : syracuseStep 1982927 = 2974391) B2974391
theorem B11305423 : Blo 1174404 11305423 := bstep (se 1 (by rfl) ⟨8479067, by rfl⟩ : syracuseStep 11305423 = 16958135) B16958135
theorem B1761785 : Blo 1174404 1761785 := bstep (se 2 (by rfl) ⟨660669, by rfl⟩ : syracuseStep 1761785 = 1321339) B1321339
theorem B3965435 : Blo 1174404 3965435 := bstep (se 1 (by rfl) ⟨2974076, by rfl⟩ : syracuseStep 3965435 = 5948153) B5948153
theorem B6783527 : Blo 1174404 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1761887 : Blo 1174404 1761887 := bstep (se 1 (by rfl) ⟨1321415, by rfl⟩ : syracuseStep 1761887 = 2642831) B2642831
theorem B24142535 : Blo 1174404 24142535 := bstep (se 1 (by rfl) ⟨18106901, by rfl⟩ : syracuseStep 24142535 = 36213803) B36213803
theorem B3965705 : Blo 1174404 3965705 := bstep (se 2 (by rfl) ⟨1487139, by rfl⟩ : syracuseStep 3965705 = 2974279) B2974279
theorem B29000591 : Blo 1174404 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B6357917 : Blo 1174404 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B48227237 : Blo 1174404 48227237 := bstep (se 4 (by rfl) ⟨4521303, by rfl⟩ : syracuseStep 48227237 = 9042607) B9042607
theorem B2974745 : Blo 1174404 2974745 := bstep (se 2 (by rfl) ⟨1115529, by rfl⟩ : syracuseStep 2974745 = 2231059) B2231059
theorem B1762367 : Blo 1174404 1762367 := bstep (se 1 (by rfl) ⟨1321775, by rfl⟩ : syracuseStep 1762367 = 2643551) B2643551
theorem B1762409 : Blo 1174404 1762409 := bstep (se 2 (by rfl) ⟨660903, by rfl⟩ : syracuseStep 1762409 = 1321807) B1321807
theorem B1983595 : Blo 1174404 1983595 := bstep (se 1 (by rfl) ⟨1487696, by rfl⟩ : syracuseStep 1983595 = 2975393) B2975393
theorem B1762511 : Blo 1174404 1762511 := bstep (se 1 (by rfl) ⟨1321883, by rfl⟩ : syracuseStep 1762511 = 2643767) B2643767
theorem B2974927 : Blo 1174404 2974927 := bstep (se 1 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 2974927 = 4462391) B4462391
theorem B1762715 : Blo 1174404 1762715 := bstep (se 1 (by rfl) ⟨1322036, by rfl⟩ : syracuseStep 1762715 = 2644073) B2644073
theorem B1983899 : Blo 1174404 1983899 := bstep (se 1 (by rfl) ⟨1487924, by rfl⟩ : syracuseStep 1983899 = 2975849) B2975849
theorem B8938945 : Blo 1174404 8938945 := bstep (se 2 (by rfl) ⟨3352104, by rfl⟩ : syracuseStep 8938945 = 6704209) B6704209
theorem B3966461 : Blo 1174404 3966461 := bstep (se 3 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 3966461 = 1487423) B1487423
theorem B2975251 : Blo 1174404 2975251 := bstep (se 1 (by rfl) ⟨2231438, by rfl⟩ : syracuseStep 2975251 = 4462877) B4462877
theorem B1762937 : Blo 1174404 1762937 := bstep (se 2 (by rfl) ⟨661101, by rfl⟩ : syracuseStep 1762937 = 1322203) B1322203
theorem B2508455 : Blo 1174404 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B4024027 : Blo 1174404 4024027 := bstep (se 1 (by rfl) ⟨3018020, by rfl⟩ : syracuseStep 4024027 = 6036041) B6036041
theorem B1763039 : Blo 1174404 1763039 := bstep (se 1 (by rfl) ⟨1322279, by rfl⟩ : syracuseStep 1763039 = 2644559) B2644559
theorem B1984223 : Blo 1174404 1984223 := bstep (se 1 (by rfl) ⟨1488167, by rfl⟩ : syracuseStep 1984223 = 2976335) B2976335
theorem B1763135 : Blo 1174404 1763135 := bstep (se 1 (by rfl) ⟨1322351, by rfl⟩ : syracuseStep 1763135 = 2644703) B2644703
theorem B20072285 : Blo 1174404 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B2975687 : Blo 1174404 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B7153609 : Blo 1174404 7153609 := bstep (se 2 (by rfl) ⟨2682603, by rfl⟩ : syracuseStep 7153609 = 5365207) B5365207
theorem B1763303 : Blo 1174404 1763303 := bstep (se 1 (by rfl) ⟨1322477, by rfl⟩ : syracuseStep 1763303 = 2644955) B2644955
theorem B1763321 : Blo 1174404 1763321 := bstep (se 2 (by rfl) ⟨661245, by rfl⟩ : syracuseStep 1763321 = 1322491) B1322491
theorem B5949449 : Blo 1174404 5949449 := bstep (se 2 (by rfl) ⟨2231043, by rfl⟩ : syracuseStep 5949449 = 4462087) B4462087
theorem B1763423 : Blo 1174404 1763423 := bstep (se 1 (by rfl) ⟨1322567, by rfl⟩ : syracuseStep 1763423 = 2645135) B2645135
theorem B1984655 : Blo 1174404 1984655 := bstep (se 1 (by rfl) ⟨1488491, by rfl⟩ : syracuseStep 1984655 = 2976983) B2976983
theorem B1763483 : Blo 1174404 1763483 := bstep (se 1 (by rfl) ⟨1322612, by rfl⟩ : syracuseStep 1763483 = 2645225) B2645225
theorem B27510961 : Blo 1174404 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B15059135 : Blo 1174404 15059135 := bstep (se 1 (by rfl) ⟨11294351, by rfl⟩ : syracuseStep 15059135 = 22588703) B22588703
theorem B1763519 : Blo 1174404 1763519 := bstep (se 1 (by rfl) ⟨1322639, by rfl⟩ : syracuseStep 1763519 = 2645279) B2645279
theorem B1763561 : Blo 1174404 1763561 := bstep (se 2 (by rfl) ⟨661335, by rfl⟩ : syracuseStep 1763561 = 1322671) B1322671
theorem B3967271 : Blo 1174404 3967271 := bstep (se 1 (by rfl) ⟨2975453, by rfl⟩ : syracuseStep 3967271 = 5950907) B5950907
theorem B1984891 : Blo 1174404 1984891 := bstep (se 1 (by rfl) ⟨1488668, by rfl⟩ : syracuseStep 1984891 = 2977337) B2977337
theorem B30558707 : Blo 1174404 30558707 := bstep (se 1 (by rfl) ⟨22919030, by rfl⟩ : syracuseStep 30558707 = 45838061) B45838061
theorem B1763867 : Blo 1174404 1763867 := bstep (se 1 (by rfl) ⟨1322900, by rfl⟩ : syracuseStep 1763867 = 2645801) B2645801
theorem B1763945 : Blo 1174404 1763945 := bstep (se 2 (by rfl) ⟨661479, by rfl⟩ : syracuseStep 1763945 = 1322959) B1322959
theorem B1985161 : Blo 1174404 1985161 := bstep (se 2 (by rfl) ⟨744435, by rfl⟩ : syracuseStep 1985161 = 1488871) B1488871
theorem B5950097 : Blo 1174404 5950097 := bstep (se 2 (by rfl) ⟨2231286, by rfl⟩ : syracuseStep 5950097 = 4462573) B4462573
theorem B6974351 : Blo 1174404 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B7637915 : Blo 1174404 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B1174431 : Blo 1174404 1174431 := bstep (se 1 (by rfl) ⟨880823, by rfl⟩ : syracuseStep 1174431 = 1761647) B1761647
theorem B3345371 : Blo 1174404 3345371 := bstep (se 1 (by rfl) ⟨2509028, by rfl⟩ : syracuseStep 3345371 = 5018057) B5018057
theorem B1174575 : Blo 1174404 1174575 := bstep (se 1 (by rfl) ⟨880931, by rfl⟩ : syracuseStep 1174575 = 1761863) B1761863
theorem B1174599 : Blo 1174404 1174599 := bstep (se 1 (by rfl) ⟨880949, by rfl⟩ : syracuseStep 1174599 = 1761899) B1761899
theorem B1764473 : Blo 1174404 1764473 := bstep (se 2 (by rfl) ⟨661677, by rfl⟩ : syracuseStep 1764473 = 1323355) B1323355
theorem B3968135 : Blo 1174404 3968135 := bstep (se 1 (by rfl) ⟨2976101, by rfl⟩ : syracuseStep 3968135 = 5952203) B5952203
theorem B14290091 : Blo 1174404 14290091 := bstep (se 1 (by rfl) ⟨10717568, by rfl⟩ : syracuseStep 14290091 = 21435137) B21435137
theorem B1174751 : Blo 1174404 1174751 := bstep (se 1 (by rfl) ⟨881063, by rfl⟩ : syracuseStep 1174751 = 1762127) B1762127
theorem B1764575 : Blo 1174404 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B3968243 : Blo 1174404 3968243 := bstep (se 1 (by rfl) ⟨2976182, by rfl⟩ : syracuseStep 3968243 = 5952365) B5952365
theorem B5950745 : Blo 1174404 5950745 := bstep (se 2 (by rfl) ⟨2231529, by rfl⟩ : syracuseStep 5950745 = 4463059) B4463059
theorem B24472907 : Blo 1174404 24472907 := bstep (se 1 (by rfl) ⟨18354680, by rfl⟩ : syracuseStep 24472907 = 36709361) B36709361
theorem B1175015 : Blo 1174404 1175015 := bstep (se 1 (by rfl) ⟨881261, by rfl⟩ : syracuseStep 1175015 = 1762523) B1762523
theorem B2510327 : Blo 1174404 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B2682359 : Blo 1174404 2682359 := bstep (se 1 (by rfl) ⟨2011769, by rfl⟩ : syracuseStep 2682359 = 4023539) B4023539
theorem B2231803 : Blo 1174404 2231803 := bstep (se 1 (by rfl) ⟨1673852, by rfl⟩ : syracuseStep 2231803 = 3347705) B3347705
theorem B1175131 : Blo 1174404 1175131 := bstep (se 1 (by rfl) ⟨881348, by rfl⟩ : syracuseStep 1175131 = 1762697) B1762697
theorem B28602065 : Blo 1174404 28602065 := bstep (se 2 (by rfl) ⟨10725774, by rfl⟩ : syracuseStep 28602065 = 21451549) B21451549
theorem B2117345 : Blo 1174404 2117345 := bstep (se 2 (by rfl) ⟨794004, by rfl⟩ : syracuseStep 2117345 = 1588009) B1588009
theorem B1175367 : Blo 1174404 1175367 := bstep (se 1 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 1175367 = 1763051) B1763051
theorem B8466383 : Blo 1174404 8466383 := bstep (se 1 (by rfl) ⟨6349787, by rfl⟩ : syracuseStep 8466383 = 12699575) B12699575
theorem B32157647 : Blo 1174404 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B1175519 : Blo 1174404 1175519 := bstep (se 1 (by rfl) ⟨881639, by rfl⟩ : syracuseStep 1175519 = 1763279) B1763279
theorem B3346555 : Blo 1174404 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B1175783 : Blo 1174404 1175783 := bstep (se 1 (by rfl) ⟨881837, by rfl⟩ : syracuseStep 1175783 = 1763675) B1763675
theorem B3764477 : Blo 1174404 3764477 := bstep (se 3 (by rfl) ⟨705839, by rfl⟩ : syracuseStep 3764477 = 1411679) B1411679
theorem B2822455 : Blo 1174404 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B1175935 : Blo 1174404 1175935 := bstep (se 1 (by rfl) ⟨881951, by rfl⟩ : syracuseStep 1175935 = 1763903) B1763903
theorem B1323391 : Blo 1174404 1323391 := bstep (se 1 (by rfl) ⟨992543, by rfl⟩ : syracuseStep 1323391 = 1985087) B1985087
theorem B1176015 : Blo 1174404 1176015 := bstep (se 1 (by rfl) ⟨882011, by rfl⟩ : syracuseStep 1176015 = 1764023) B1764023
theorem B33886745 : Blo 1174404 33886745 := bstep (se 2 (by rfl) ⟨12707529, by rfl⟩ : syracuseStep 33886745 = 25415059) B25415059
theorem B1176167 : Blo 1174404 1176167 := bstep (se 1 (by rfl) ⟨882125, by rfl⟩ : syracuseStep 1176167 = 1764251) B1764251
theorem B6697687 : Blo 1174404 6697687 := bstep (se 1 (by rfl) ⟨5023265, by rfl⟩ : syracuseStep 6697687 = 10046531) B10046531
theorem B3969917 : Blo 1174404 3969917 := bstep (se 3 (by rfl) ⟨744359, by rfl⟩ : syracuseStep 3969917 = 1488719) B1488719
theorem B2642939 : Blo 1174404 2642939 := bstep (se 1 (by rfl) ⟨1982204, by rfl⟩ : syracuseStep 2642939 = 3964409) B3964409
theorem B5952527 : Blo 1174404 5952527 := bstep (se 1 (by rfl) ⟨4464395, by rfl⟩ : syracuseStep 5952527 = 8928791) B8928791
theorem B3970187 : Blo 1174404 3970187 := bstep (se 1 (by rfl) ⟨2977640, by rfl⟩ : syracuseStep 3970187 = 5955281) B5955281
theorem B2643119 : Blo 1174404 2643119 := bstep (se 1 (by rfl) ⟨1982339, by rfl⟩ : syracuseStep 2643119 = 3964679) B3964679
theorem B2643155 : Blo 1174404 2643155 := bstep (se 1 (by rfl) ⟨1982366, by rfl⟩ : syracuseStep 2643155 = 3964733) B3964733
theorem B1881515 : Blo 1174404 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B2643425 : Blo 1174404 2643425 := bstep (se 2 (by rfl) ⟨991284, by rfl⟩ : syracuseStep 2643425 = 1982569) B1982569
theorem B2864609 : Blo 1174404 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B8918585 : Blo 1174404 8918585 := bstep (se 2 (by rfl) ⟨3344469, by rfl⟩ : syracuseStep 8918585 = 6688939) B6688939
theorem B24802949 : Blo 1174404 24802949 := bstep (se 4 (by rfl) ⟨2325276, by rfl⟩ : syracuseStep 24802949 = 4650553) B4650553
theorem B18101981 : Blo 1174404 18101981 := bstep (se 3 (by rfl) ⟨3394121, by rfl⟩ : syracuseStep 18101981 = 6788243) B6788243
theorem B128726819 : Blo 1174404 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B5953337 : Blo 1174404 5953337 := bstep (se 2 (by rfl) ⟨2232501, by rfl⟩ : syracuseStep 5953337 = 4465003) B4465003
theorem B3348287 : Blo 1174404 3348287 := bstep (se 1 (by rfl) ⟨2511215, by rfl⟩ : syracuseStep 3348287 = 5022431) B5022431
theorem B3766247 : Blo 1174404 3766247 := bstep (se 1 (by rfl) ⟨2824685, by rfl⟩ : syracuseStep 3766247 = 5649371) B5649371
theorem B3176711 : Blo 1174404 3176711 := bstep (se 1 (by rfl) ⟨2382533, by rfl⟩ : syracuseStep 3176711 = 4765067) B4765067
theorem B33864601 : Blo 1174404 33864601 := bstep (se 2 (by rfl) ⟨12699225, by rfl⟩ : syracuseStep 33864601 = 25398451) B25398451
theorem B13564837 : Blo 1174404 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B2645063 : Blo 1174404 2645063 := bstep (se 1 (by rfl) ⟨1983797, by rfl⟩ : syracuseStep 2645063 = 3967595) B3967595
theorem B2972801 : Blo 1174404 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B3349687 : Blo 1174404 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B14294231 : Blo 1174404 14294231 := bstep (se 1 (by rfl) ⟨10720673, by rfl⟩ : syracuseStep 14294231 = 21441347) B21441347
theorem B7527775 : Blo 1174404 7527775 := bstep (se 1 (by rfl) ⟨5645831, by rfl⟩ : syracuseStep 7527775 = 11291663) B11291663
theorem B27139475 : Blo 1174404 27139475 := bstep (se 1 (by rfl) ⟨20354606, by rfl⟩ : syracuseStep 27139475 = 40709213) B40709213
theorem B2260391 : Blo 1174404 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B2973095 : Blo 1174404 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B6028739 : Blo 1174404 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B2645459 : Blo 1174404 2645459 := bstep (se 1 (by rfl) ⟨1984094, by rfl⟩ : syracuseStep 2645459 = 3968189) B3968189
theorem B67788251 : Blo 1174404 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B2825819 : Blo 1174404 2825819 := bstep (se 1 (by rfl) ⟨2119364, by rfl⟩ : syracuseStep 2825819 = 4238729) B4238729
theorem B22593167 : Blo 1174404 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B3767951 : Blo 1174404 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2645729 : Blo 1174404 2645729 := bstep (se 2 (by rfl) ⟨992148, by rfl⟩ : syracuseStep 2645729 = 1984297) B1984297
theorem B1982279 : Blo 1174404 1982279 := bstep (se 1 (by rfl) ⟨1486709, by rfl⟩ : syracuseStep 1982279 = 2973419) B2973419
theorem B4235095 : Blo 1174404 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B2973611 : Blo 1174404 2973611 := bstep (se 1 (by rfl) ⟨2230208, by rfl⟩ : syracuseStep 2973611 = 4460417) B4460417
theorem B2646521 : Blo 1174404 2646521 := bstep (se 2 (by rfl) ⟨992445, by rfl⟩ : syracuseStep 2646521 = 1984891) B1984891
theorem B2646611 : Blo 1174404 2646611 := bstep (se 1 (by rfl) ⟨1984958, by rfl⟩ : syracuseStep 2646611 = 3969917) B3969917
theorem B19333727 : Blo 1174404 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B15073897 : Blo 1174404 15073897 := bstep (se 2 (by rfl) ⟨5652711, by rfl⟩ : syracuseStep 15073897 = 11305423) B11305423
theorem B1761959 : Blo 1174404 1761959 := bstep (se 1 (by rfl) ⟨1321469, by rfl⟩ : syracuseStep 1761959 = 2642939) B2642939
theorem B1983163 : Blo 1174404 1983163 := bstep (se 1 (by rfl) ⟨1487372, by rfl⟩ : syracuseStep 1983163 = 2974745) B2974745
theorem B2646791 : Blo 1174404 2646791 := bstep (se 1 (by rfl) ⟨1985093, by rfl⟩ : syracuseStep 2646791 = 3970187) B3970187
theorem B1762079 : Blo 1174404 1762079 := bstep (se 1 (by rfl) ⟨1321559, by rfl⟩ : syracuseStep 1762079 = 2643119) B2643119
theorem B1762103 : Blo 1174404 1762103 := bstep (se 1 (by rfl) ⟨1321577, by rfl⟩ : syracuseStep 1762103 = 2643155) B2643155
theorem B2646881 : Blo 1174404 2646881 := bstep (se 2 (by rfl) ⟨992580, by rfl⟩ : syracuseStep 2646881 = 1985161) B1985161
theorem B8930249 : Blo 1174404 8930249 := bstep (se 2 (by rfl) ⟨3348843, by rfl⟩ : syracuseStep 8930249 = 6697687) B6697687
theorem B1762283 : Blo 1174404 1762283 := bstep (se 1 (by rfl) ⟨1321712, by rfl⟩ : syracuseStep 1762283 = 2643425) B2643425
theorem B1909739 : Blo 1174404 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B12067987 : Blo 1174404 12067987 := bstep (se 1 (by rfl) ⟨9050990, by rfl⟩ : syracuseStep 12067987 = 18101981) B18101981
theorem B1983791 : Blo 1174404 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B3966299 : Blo 1174404 3966299 := bstep (se 1 (by rfl) ⟨2974724, by rfl⟩ : syracuseStep 3966299 = 5949449) B5949449
theorem B18089405 : Blo 1174404 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B4466249 : Blo 1174404 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B3966569 : Blo 1174404 3966569 := bstep (se 2 (by rfl) ⟨1487463, by rfl⟩ : syracuseStep 3966569 = 2974927) B2974927
theorem B3966731 : Blo 1174404 3966731 := bstep (se 1 (by rfl) ⟨2975048, by rfl⟩ : syracuseStep 3966731 = 5950097) B5950097
theorem B10037033 : Blo 1174404 10037033 := bstep (se 2 (by rfl) ⟨3763887, by rfl⟩ : syracuseStep 10037033 = 7527775) B7527775
theorem B2230247 : Blo 1174404 2230247 := bstep (se 1 (by rfl) ⟨1672685, by rfl⟩ : syracuseStep 2230247 = 3345371) B3345371
theorem B2975737 : Blo 1174404 2975737 := bstep (se 2 (by rfl) ⟨1115901, by rfl⟩ : syracuseStep 2975737 = 2231803) B2231803
theorem B3967001 : Blo 1174404 3967001 := bstep (se 2 (by rfl) ⟨1487625, by rfl⟩ : syracuseStep 3967001 = 2975251) B2975251
theorem B1763375 : Blo 1174404 1763375 := bstep (se 1 (by rfl) ⟨1322531, by rfl⟩ : syracuseStep 1763375 = 2645063) B2645063
theorem B9529487 : Blo 1174404 9529487 := bstep (se 1 (by rfl) ⟨7147115, by rfl⟩ : syracuseStep 9529487 = 14294231) B14294231
theorem B3967163 : Blo 1174404 3967163 := bstep (se 1 (by rfl) ⟨2975372, by rfl⟩ : syracuseStep 3967163 = 5950745) B5950745
theorem B1763639 : Blo 1174404 1763639 := bstep (se 1 (by rfl) ⟨1322729, by rfl⟩ : syracuseStep 1763639 = 2645459) B2645459
theorem B1673551 : Blo 1174404 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B1788239 : Blo 1174404 1788239 := bstep (se 1 (by rfl) ⟨1341179, by rfl⟩ : syracuseStep 1788239 = 2682359) B2682359
theorem B20367773 : Blo 1174404 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B5646793 : Blo 1174404 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B1763819 : Blo 1174404 1763819 := bstep (se 1 (by rfl) ⟨1322864, by rfl⟩ : syracuseStep 1763819 = 2645729) B2645729
theorem B1321519 : Blo 1174404 1321519 := bstep (se 1 (by rfl) ⟨991139, by rfl⟩ : syracuseStep 1321519 = 1982279) B1982279
theorem B9538145 : Blo 1174404 9538145 := bstep (se 2 (by rfl) ⟨3576804, by rfl⟩ : syracuseStep 9538145 = 7153609) B7153609
theorem B2509651 : Blo 1174404 2509651 := bstep (se 1 (by rfl) ⟨1882238, by rfl⟩ : syracuseStep 2509651 = 3764477) B3764477
theorem B17165195 : Blo 1174404 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B1174495 : Blo 1174404 1174495 := bstep (se 1 (by rfl) ⟨880871, by rfl⟩ : syracuseStep 1174495 = 1761743) B1761743
theorem B1321951 : Blo 1174404 1321951 := bstep (se 1 (by rfl) ⟨991463, by rfl⟩ : syracuseStep 1321951 = 1982927) B1982927
theorem B1174523 : Blo 1174404 1174523 := bstep (se 1 (by rfl) ⟨880892, by rfl⟩ : syracuseStep 1174523 = 1761785) B1761785
theorem B1174591 : Blo 1174404 1174591 := bstep (se 1 (by rfl) ⟨880943, by rfl⟩ : syracuseStep 1174591 = 1761887) B1761887
theorem B3763273 : Blo 1174404 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B1764521 : Blo 1174404 1764521 := bstep (se 2 (by rfl) ⟨661695, by rfl⟩ : syracuseStep 1764521 = 1323391) B1323391
theorem B4238611 : Blo 1174404 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B3968351 : Blo 1174404 3968351 := bstep (se 1 (by rfl) ⟨2976263, by rfl⟩ : syracuseStep 3968351 = 5952527) B5952527
theorem B1174911 : Blo 1174404 1174911 := bstep (se 1 (by rfl) ⟨881183, by rfl⟩ : syracuseStep 1174911 = 1762367) B1762367
theorem B1174939 : Blo 1174404 1174939 := bstep (se 1 (by rfl) ⟨881204, by rfl⟩ : syracuseStep 1174939 = 1762409) B1762409
theorem B1175007 : Blo 1174404 1175007 := bstep (se 1 (by rfl) ⟨881255, by rfl⟩ : syracuseStep 1175007 = 1762511) B1762511
theorem B1175143 : Blo 1174404 1175143 := bstep (se 1 (by rfl) ⟨881357, by rfl⟩ : syracuseStep 1175143 = 1762715) B1762715
theorem B1322599 : Blo 1174404 1322599 := bstep (se 1 (by rfl) ⟨991949, by rfl⟩ : syracuseStep 1322599 = 1983899) B1983899
theorem B1175291 : Blo 1174404 1175291 := bstep (se 1 (by rfl) ⟨881468, by rfl⟩ : syracuseStep 1175291 = 1762937) B1762937
theorem B16535299 : Blo 1174404 16535299 := bstep (se 1 (by rfl) ⟨12401474, by rfl⟩ : syracuseStep 16535299 = 24802949) B24802949
theorem B5017373 : Blo 1174404 5017373 := bstep (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) B1881515
theorem B1175359 : Blo 1174404 1175359 := bstep (se 1 (by rfl) ⟨881519, by rfl⟩ : syracuseStep 1175359 = 1763039) B1763039
theorem B1322815 : Blo 1174404 1322815 := bstep (se 1 (by rfl) ⟨992111, by rfl⟩ : syracuseStep 1322815 = 1984223) B1984223
theorem B3968891 : Blo 1174404 3968891 := bstep (se 1 (by rfl) ⟨2976668, by rfl⟩ : syracuseStep 3968891 = 5953337) B5953337
theorem B1175423 : Blo 1174404 1175423 := bstep (se 1 (by rfl) ⟨881567, by rfl⟩ : syracuseStep 1175423 = 1763135) B1763135
theorem B2232191 : Blo 1174404 2232191 := bstep (se 1 (by rfl) ⟨1674143, by rfl⟩ : syracuseStep 2232191 = 3348287) B3348287
theorem B13381523 : Blo 1174404 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1175535 : Blo 1174404 1175535 := bstep (se 1 (by rfl) ⟨881651, by rfl⟩ : syracuseStep 1175535 = 1763303) B1763303
theorem B2510831 : Blo 1174404 2510831 := bstep (se 1 (by rfl) ⟨1883123, by rfl⟩ : syracuseStep 2510831 = 3766247) B3766247
theorem B1175547 : Blo 1174404 1175547 := bstep (se 1 (by rfl) ⟨881660, by rfl⟩ : syracuseStep 1175547 = 1763321) B1763321
theorem B1175615 : Blo 1174404 1175615 := bstep (se 1 (by rfl) ⟨881711, by rfl⟩ : syracuseStep 1175615 = 1763423) B1763423
theorem B1323103 : Blo 1174404 1323103 := bstep (se 1 (by rfl) ⟨992327, by rfl⟩ : syracuseStep 1323103 = 1984655) B1984655
theorem B1175655 : Blo 1174404 1175655 := bstep (se 1 (by rfl) ⟨881741, by rfl⟩ : syracuseStep 1175655 = 1763483) B1763483
theorem B10039423 : Blo 1174404 10039423 := bstep (se 1 (by rfl) ⟨7529567, by rfl⟩ : syracuseStep 10039423 = 15059135) B15059135
theorem B1175679 : Blo 1174404 1175679 := bstep (se 1 (by rfl) ⟨881759, by rfl⟩ : syracuseStep 1175679 = 1763519) B1763519
theorem B1175707 : Blo 1174404 1175707 := bstep (se 1 (by rfl) ⟨881780, by rfl⟩ : syracuseStep 1175707 = 1763561) B1763561
theorem B2117807 : Blo 1174404 2117807 := bstep (se 1 (by rfl) ⟨1588355, by rfl⟩ : syracuseStep 2117807 = 3176711) B3176711
theorem B1175911 : Blo 1174404 1175911 := bstep (se 1 (by rfl) ⟨881933, by rfl⟩ : syracuseStep 1175911 = 1763867) B1763867
theorem B1175963 : Blo 1174404 1175963 := bstep (se 1 (by rfl) ⟨881972, by rfl⟩ : syracuseStep 1175963 = 1763945) B1763945
theorem B6689213 : Blo 1174404 6689213 := bstep (se 3 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 6689213 = 2508455) B2508455
theorem B4649567 : Blo 1174404 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B1176315 : Blo 1174404 1176315 := bstep (se 1 (by rfl) ⟨882236, by rfl⟩ : syracuseStep 1176315 = 1764473) B1764473
theorem B1176383 : Blo 1174404 1176383 := bstep (se 1 (by rfl) ⟨882287, by rfl⟩ : syracuseStep 1176383 = 1764575) B1764575
theorem B16315271 : Blo 1174404 16315271 := bstep (se 1 (by rfl) ⟨12236453, by rfl⟩ : syracuseStep 16315271 = 24472907) B24472907
theorem B18092983 : Blo 1174404 18092983 := bstep (se 1 (by rfl) ⟨13569737, by rfl⟩ : syracuseStep 18092983 = 27139475) B27139475
theorem B4019159 : Blo 1174404 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B45192167 : Blo 1174404 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B15062111 : Blo 1174404 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B2511967 : Blo 1174404 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B19068043 : Blo 1174404 19068043 := bstep (se 1 (by rfl) ⟨14301032, by rfl⟩ : syracuseStep 19068043 = 28602065) B28602065
theorem B3347887 : Blo 1174404 3347887 := bstep (se 1 (by rfl) ⟨2510915, by rfl⟩ : syracuseStep 3347887 = 5021831) B5021831
theorem B4462073 : Blo 1174404 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B36681281 : Blo 1174404 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B3348047 : Blo 1174404 3348047 := bstep (se 1 (by rfl) ⟨2511035, by rfl⟩ : syracuseStep 3348047 = 5022071) B5022071
theorem B2643623 : Blo 1174404 2643623 := bstep (se 1 (by rfl) ⟨1982717, by rfl⟩ : syracuseStep 2643623 = 3965435) B3965435
theorem B22591163 : Blo 1174404 22591163 := bstep (se 1 (by rfl) ⟨16943372, by rfl⟩ : syracuseStep 22591163 = 33886745) B33886745
theorem B16095023 : Blo 1174404 16095023 := bstep (se 1 (by rfl) ⟨12071267, by rfl⟩ : syracuseStep 16095023 = 24142535) B24142535
theorem B2643803 : Blo 1174404 2643803 := bstep (se 1 (by rfl) ⟨1982852, by rfl⟩ : syracuseStep 2643803 = 3965705) B3965705
theorem B32151491 : Blo 1174404 32151491 := bstep (se 1 (by rfl) ⟨24113618, by rfl⟩ : syracuseStep 32151491 = 48227237) B48227237
theorem B2644307 : Blo 1174404 2644307 := bstep (se 1 (by rfl) ⟨1983230, by rfl⟩ : syracuseStep 2644307 = 3966461) B3966461
theorem B5945723 : Blo 1174404 5945723 := bstep (se 1 (by rfl) ⟨4459292, by rfl⟩ : syracuseStep 5945723 = 8918585) B8918585
theorem B6027709 : Blo 1174404 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B85817879 : Blo 1174404 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B45152801 : Blo 1174404 45152801 := bstep (se 2 (by rfl) ⟨16932300, by rfl⟩ : syracuseStep 45152801 = 33864601) B33864601
theorem B18086449 : Blo 1174404 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B2644793 : Blo 1174404 2644793 := bstep (se 2 (by rfl) ⟨991797, by rfl⟩ : syracuseStep 2644793 = 1983595) B1983595
theorem B2644847 : Blo 1174404 2644847 := bstep (se 1 (by rfl) ⟨1983635, by rfl⟩ : syracuseStep 2644847 = 3967271) B3967271
theorem B20372471 : Blo 1174404 20372471 := bstep (se 1 (by rfl) ⟨15279353, by rfl⟩ : syracuseStep 20372471 = 30558707) B30558707
theorem B11918593 : Blo 1174404 11918593 := bstep (se 2 (by rfl) ⟨4469472, by rfl⟩ : syracuseStep 11918593 = 8938945) B8938945
theorem B1981867 : Blo 1174404 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B2645423 : Blo 1174404 2645423 := bstep (se 1 (by rfl) ⟨1984067, by rfl⟩ : syracuseStep 2645423 = 3968135) B3968135
theorem B9526727 : Blo 1174404 9526727 := bstep (se 1 (by rfl) ⟨7145045, by rfl⟩ : syracuseStep 9526727 = 14290091) B14290091
theorem B2645495 : Blo 1174404 2645495 := bstep (se 1 (by rfl) ⟨1984121, by rfl⟩ : syracuseStep 2645495 = 3968243) B3968243
theorem B1982063 : Blo 1174404 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B5365369 : Blo 1174404 5365369 := bstep (se 2 (by rfl) ⟨2012013, by rfl⟩ : syracuseStep 5365369 = 4024027) B4024027
theorem B22585013 : Blo 1174404 22585013 := bstep (se 5 (by rfl) ⟨1058672, by rfl⟩ : syracuseStep 22585013 = 2117345) B2117345
theorem B1883879 : Blo 1174404 1883879 := bstep (se 1 (by rfl) ⟨1412909, by rfl⟩ : syracuseStep 1883879 = 2825819) B2825819
theorem B1982407 : Blo 1174404 1982407 := bstep (se 1 (by rfl) ⟨1486805, by rfl⟩ : syracuseStep 1982407 = 2973611) B2973611
theorem B5644255 : Blo 1174404 5644255 := bstep (se 1 (by rfl) ⟨4233191, by rfl⟩ : syracuseStep 5644255 = 8466383) B8466383
theorem B21438431 : Blo 1174404 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B13385897 : Blo 1174404 13385897 := bstep (se 2 (by rfl) ⟨5019711, by rfl⟩ : syracuseStep 13385897 = 10039423) B10039423
theorem B8036945 : Blo 1174404 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B7529057 : Blo 1174404 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B28615301 : Blo 1174404 28615301 := bstep (se 4 (by rfl) ⟨2682684, by rfl⟩ : syracuseStep 28615301 = 5365369) B5365369
theorem B1762025 : Blo 1174404 1762025 := bstep (se 2 (by rfl) ⟨660759, by rfl⟩ : syracuseStep 1762025 = 1321519) B1321519
theorem B12059603 : Blo 1174404 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B2974715 : Blo 1174404 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B24454187 : Blo 1174404 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B1762415 : Blo 1174404 1762415 := bstep (se 1 (by rfl) ⟨1321811, by rfl⟩ : syracuseStep 1762415 = 2643623) B2643623
theorem B1762535 : Blo 1174404 1762535 := bstep (se 1 (by rfl) ⟨1321901, by rfl⟩ : syracuseStep 1762535 = 2643803) B2643803
theorem B1762601 : Blo 1174404 1762601 := bstep (se 2 (by rfl) ⟨660975, by rfl⟩ : syracuseStep 1762601 = 1321951) B1321951
theorem B16090649 : Blo 1174404 16090649 := bstep (se 2 (by rfl) ⟨6033993, by rfl⟩ : syracuseStep 16090649 = 12067987) B12067987
theorem B1762871 : Blo 1174404 1762871 := bstep (se 1 (by rfl) ⟨1322153, by rfl⟩ : syracuseStep 1762871 = 2644307) B2644307
theorem B6358763 : Blo 1174404 6358763 := bstep (se 1 (by rfl) ⟨4769072, by rfl⟩ : syracuseStep 6358763 = 9538145) B9538145
theorem B1763195 : Blo 1174404 1763195 := bstep (se 1 (by rfl) ⟨1322396, by rfl⟩ : syracuseStep 1763195 = 2644793) B2644793
theorem B1763231 : Blo 1174404 1763231 := bstep (se 1 (by rfl) ⟨1322423, by rfl⟩ : syracuseStep 1763231 = 2644847) B2644847
theorem B1763465 : Blo 1174404 1763465 := bstep (se 2 (by rfl) ⟨661299, by rfl⟩ : syracuseStep 1763465 = 1322599) B1322599
theorem B1763615 : Blo 1174404 1763615 := bstep (se 1 (by rfl) ⟨1322711, by rfl⟩ : syracuseStep 1763615 = 2645423) B2645423
theorem B6351151 : Blo 1174404 6351151 := bstep (se 1 (by rfl) ⟨4763363, by rfl⟩ : syracuseStep 6351151 = 9526727) B9526727
theorem B1763663 : Blo 1174404 1763663 := bstep (se 1 (by rfl) ⟨1322747, by rfl⟩ : syracuseStep 1763663 = 2645495) B2645495
theorem B22047065 : Blo 1174404 22047065 := bstep (se 2 (by rfl) ⟨8267649, by rfl⟩ : syracuseStep 22047065 = 16535299) B16535299
theorem B1321375 : Blo 1174404 1321375 := bstep (se 1 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 1321375 = 1982063) B1982063
theorem B1763753 : Blo 1174404 1763753 := bstep (se 2 (by rfl) ⟨661407, by rfl⟩ : syracuseStep 1763753 = 1322815) B1322815
theorem B1255919 : Blo 1174404 1255919 := bstep (se 1 (by rfl) ⟨941939, by rfl⟩ : syracuseStep 1255919 = 1883879) B1883879
theorem B3344915 : Blo 1174404 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B10717757 : Blo 1174404 10717757 := bstep (se 3 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 10717757 = 4019159) B4019159
theorem B1673887 : Blo 1174404 1673887 := bstep (se 1 (by rfl) ⟨1255415, by rfl⟩ : syracuseStep 1673887 = 2510831) B2510831
theorem B3967649 : Blo 1174404 3967649 := bstep (se 2 (by rfl) ⟨1487868, by rfl⟩ : syracuseStep 3967649 = 2975737) B2975737
theorem B1411871 : Blo 1174404 1411871 := bstep (se 1 (by rfl) ⟨1058903, by rfl⟩ : syracuseStep 1411871 = 2117807) B2117807
theorem B1764137 : Blo 1174404 1764137 := bstep (se 2 (by rfl) ⟨661551, by rfl⟩ : syracuseStep 1764137 = 1323103) B1323103
theorem B4459475 : Blo 1174404 4459475 := bstep (se 1 (by rfl) ⟨3344606, by rfl⟩ : syracuseStep 4459475 = 6689213) B6689213
theorem B1764347 : Blo 1174404 1764347 := bstep (se 1 (by rfl) ⟨1323260, by rfl⟩ : syracuseStep 1764347 = 2646521) B2646521
theorem B1764407 : Blo 1174404 1764407 := bstep (se 1 (by rfl) ⟨1323305, by rfl⟩ : syracuseStep 1764407 = 2646611) B2646611
theorem B12889151 : Blo 1174404 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B2231401 : Blo 1174404 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B1174639 : Blo 1174404 1174639 := bstep (se 1 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 1174639 = 1761959) B1761959
theorem B1764527 : Blo 1174404 1764527 := bstep (se 1 (by rfl) ⟨1323395, by rfl⟩ : syracuseStep 1764527 = 2646791) B2646791
theorem B1174719 : Blo 1174404 1174719 := bstep (se 1 (by rfl) ⟨881039, by rfl⟩ : syracuseStep 1174719 = 1762079) B1762079
theorem B1174735 : Blo 1174404 1174735 := bstep (se 1 (by rfl) ⟨881051, by rfl⟩ : syracuseStep 1174735 = 1762103) B1762103
theorem B1764587 : Blo 1174404 1764587 := bstep (se 1 (by rfl) ⟨1323440, by rfl⟩ : syracuseStep 1764587 = 2646881) B2646881
theorem B1174855 : Blo 1174404 1174855 := bstep (se 1 (by rfl) ⟨881141, by rfl⟩ : syracuseStep 1174855 = 1762283) B1762283
theorem B1273159 : Blo 1174404 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B20098529 : Blo 1174404 20098529 := bstep (se 2 (by rfl) ⟨7536948, by rfl⟩ : syracuseStep 20098529 = 15073897) B15073897
theorem B1322527 : Blo 1174404 1322527 := bstep (se 1 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 1322527 = 1983791) B1983791
theorem B2977499 : Blo 1174404 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B2232031 : Blo 1174404 2232031 := bstep (se 1 (by rfl) ⟨1674023, by rfl⟩ : syracuseStep 2232031 = 3348047) B3348047
theorem B3346201 : Blo 1174404 3346201 := bstep (se 2 (by rfl) ⟨1254825, by rfl⟩ : syracuseStep 3346201 = 2509651) B2509651
theorem B15060775 : Blo 1174404 15060775 := bstep (se 1 (by rfl) ⟨11295581, by rfl⟩ : syracuseStep 15060775 = 22591163) B22591163
theorem B21434327 : Blo 1174404 21434327 := bstep (se 1 (by rfl) ⟨16075745, by rfl⟩ : syracuseStep 21434327 = 32151491) B32151491
theorem B1486831 : Blo 1174404 1486831 := bstep (se 1 (by rfl) ⟨1115123, by rfl⟩ : syracuseStep 1486831 = 2230247) B2230247
theorem B63565829 : Blo 1174404 63565829 := bstep (se 4 (by rfl) ⟨5959296, by rfl⟩ : syracuseStep 63565829 = 11918593) B11918593
theorem B1175583 : Blo 1174404 1175583 := bstep (se 1 (by rfl) ⟨881687, by rfl⟩ : syracuseStep 1175583 = 1763375) B1763375
theorem B6352991 : Blo 1174404 6352991 := bstep (se 1 (by rfl) ⟨4764743, by rfl⟩ : syracuseStep 6352991 = 9529487) B9529487
theorem B5017697 : Blo 1174404 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B22605925 : Blo 1174404 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B25424057 : Blo 1174404 25424057 := bstep (se 2 (by rfl) ⟨9534021, by rfl⟩ : syracuseStep 25424057 = 19068043) B19068043
theorem B1175759 : Blo 1174404 1175759 := bstep (se 1 (by rfl) ⟨881819, by rfl⟩ : syracuseStep 1175759 = 1763639) B1763639
theorem B1192159 : Blo 1174404 1192159 := bstep (se 1 (by rfl) ⟨894119, by rfl⟩ : syracuseStep 1192159 = 1788239) B1788239
theorem B12398845 : Blo 1174404 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B13578515 : Blo 1174404 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B1175879 : Blo 1174404 1175879 := bstep (se 1 (by rfl) ⟨881909, by rfl⟩ : syracuseStep 1175879 = 1763819) B1763819
theorem B30101867 : Blo 1174404 30101867 := bstep (se 1 (by rfl) ⟨22576400, by rfl⟩ : syracuseStep 30101867 = 45152801) B45152801
theorem B2642489 : Blo 1174404 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B1176347 : Blo 1174404 1176347 := bstep (se 1 (by rfl) ⟨882260, by rfl⟩ : syracuseStep 1176347 = 1764521) B1764521
theorem B1488127 : Blo 1174404 1488127 := bstep (se 1 (by rfl) ⟨1116095, by rfl⟩ : syracuseStep 1488127 = 2232191) B2232191
theorem B2643209 : Blo 1174404 2643209 := bstep (se 2 (by rfl) ⟨991203, by rfl⟩ : syracuseStep 2643209 = 1982407) B1982407
theorem B7525673 : Blo 1174404 7525673 := bstep (se 2 (by rfl) ⟨2822127, by rfl⟩ : syracuseStep 7525673 = 5644255) B5644255
theorem B14292287 : Blo 1174404 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B10876847 : Blo 1174404 10876847 := bstep (se 1 (by rfl) ⟨8157635, by rfl⟩ : syracuseStep 10876847 = 16315271) B16315271
theorem B5953499 : Blo 1174404 5953499 := bstep (se 1 (by rfl) ⟨4465124, by rfl⟩ : syracuseStep 5953499 = 8930249) B8930249
theorem B30128111 : Blo 1174404 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B10041407 : Blo 1174404 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B24115265 : Blo 1174404 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B2644199 : Blo 1174404 2644199 := bstep (se 1 (by rfl) ⟨1983149, by rfl⟩ : syracuseStep 2644199 = 3966299) B3966299
theorem B2644217 : Blo 1174404 2644217 := bstep (se 2 (by rfl) ⟨991581, by rfl⟩ : syracuseStep 2644217 = 1983163) B1983163
theorem B2644379 : Blo 1174404 2644379 := bstep (se 1 (by rfl) ⟨1983284, by rfl⟩ : syracuseStep 2644379 = 3966569) B3966569
theorem B2644487 : Blo 1174404 2644487 := bstep (se 1 (by rfl) ⟨1983365, by rfl⟩ : syracuseStep 2644487 = 3966731) B3966731
theorem B6691355 : Blo 1174404 6691355 := bstep (se 1 (by rfl) ⟨5018516, by rfl⟩ : syracuseStep 6691355 = 10037033) B10037033
theorem B10730015 : Blo 1174404 10730015 := bstep (se 1 (by rfl) ⟨8047511, by rfl⟩ : syracuseStep 10730015 = 16095023) B16095023
theorem B24123977 : Blo 1174404 24123977 := bstep (se 2 (by rfl) ⟨9046491, by rfl⟩ : syracuseStep 24123977 = 18092983) B18092983
theorem B2644667 : Blo 1174404 2644667 := bstep (se 1 (by rfl) ⟨1983500, by rfl⟩ : syracuseStep 2644667 = 3967001) B3967001
theorem B2644775 : Blo 1174404 2644775 := bstep (se 1 (by rfl) ⟨1983581, by rfl⟩ : syracuseStep 2644775 = 3967163) B3967163
theorem B3349289 : Blo 1174404 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B3963815 : Blo 1174404 3963815 := bstep (se 1 (by rfl) ⟨2972861, by rfl⟩ : syracuseStep 3963815 = 5945723) B5945723
theorem B57211919 : Blo 1174404 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B4463849 : Blo 1174404 4463849 := bstep (se 2 (by rfl) ⟨1673943, by rfl⟩ : syracuseStep 4463849 = 3347887) B3347887
theorem B11443463 : Blo 1174404 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B13581647 : Blo 1174404 13581647 := bstep (se 1 (by rfl) ⟨10186235, by rfl⟩ : syracuseStep 13581647 = 20372471) B20372471
theorem B2645567 : Blo 1174404 2645567 := bstep (se 1 (by rfl) ⟨1984175, by rfl⟩ : syracuseStep 2645567 = 3968351) B3968351
theorem B15056675 : Blo 1174404 15056675 := bstep (se 1 (by rfl) ⟨11292506, by rfl⟩ : syracuseStep 15056675 = 22585013) B22585013
theorem B2645927 : Blo 1174404 2645927 := bstep (se 1 (by rfl) ⟨1984445, by rfl⟩ : syracuseStep 2645927 = 3968891) B3968891
theorem B8921015 : Blo 1174404 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B42377219 : Blo 1174404 42377219 := bstep (se 1 (by rfl) ⟨31782914, by rfl⟩ : syracuseStep 42377219 = 63565829) B63565829
theorem B4235327 : Blo 1174404 4235327 := bstep (se 1 (by rfl) ⟨3176495, by rfl⟩ : syracuseStep 4235327 = 6352991) B6352991
theorem B16949371 : Blo 1174404 16949371 := bstep (se 1 (by rfl) ⟨12712028, by rfl⟩ : syracuseStep 16949371 = 25424057) B25424057
theorem B9052343 : Blo 1174404 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B1589545 : Blo 1174404 1589545 := bstep (se 2 (by rfl) ⟨596079, by rfl⟩ : syracuseStep 1589545 = 1192159) B1192159
theorem B16531793 : Blo 1174404 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B1761659 : Blo 1174404 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B5357963 : Blo 1174404 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1761833 : Blo 1174404 1761833 := bstep (se 2 (by rfl) ⟨660687, by rfl⟩ : syracuseStep 1761833 = 1321375) B1321375
theorem B1983143 : Blo 1174404 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B16302791 : Blo 1174404 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B1762139 : Blo 1174404 1762139 := bstep (se 1 (by rfl) ⟨1321604, by rfl⟩ : syracuseStep 1762139 = 2643209) B2643209
theorem B9528191 : Blo 1174404 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B6694271 : Blo 1174404 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B2975201 : Blo 1174404 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1762799 : Blo 1174404 1762799 := bstep (se 1 (by rfl) ⟨1322099, by rfl⟩ : syracuseStep 1762799 = 2644199) B2644199
theorem B1762811 : Blo 1174404 1762811 := bstep (se 1 (by rfl) ⟨1322108, by rfl⟩ : syracuseStep 1762811 = 2644217) B2644217
theorem B14698043 : Blo 1174404 14698043 := bstep (se 1 (by rfl) ⟨11023532, by rfl⟩ : syracuseStep 14698043 = 22047065) B22047065
theorem B1762919 : Blo 1174404 1762919 := bstep (se 1 (by rfl) ⟨1322189, by rfl⟩ : syracuseStep 1762919 = 2644379) B2644379
theorem B1984169 : Blo 1174404 1984169 := bstep (se 2 (by rfl) ⟨744063, by rfl⟩ : syracuseStep 1984169 = 1488127) B1488127
theorem B1762991 : Blo 1174404 1762991 := bstep (se 1 (by rfl) ⟨1322243, by rfl⟩ : syracuseStep 1762991 = 2644487) B2644487
theorem B2229943 : Blo 1174404 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B7153343 : Blo 1174404 7153343 := bstep (se 1 (by rfl) ⟨5365007, by rfl⟩ : syracuseStep 7153343 = 10730015) B10730015
theorem B7145171 : Blo 1174404 7145171 := bstep (se 1 (by rfl) ⟨5358878, by rfl⟩ : syracuseStep 7145171 = 10717757) B10717757
theorem B16082651 : Blo 1174404 16082651 := bstep (se 1 (by rfl) ⟨12061988, by rfl⟩ : syracuseStep 16082651 = 24123977) B24123977
theorem B1697545 : Blo 1174404 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B1763111 : Blo 1174404 1763111 := bstep (se 1 (by rfl) ⟨1322333, by rfl⟩ : syracuseStep 1763111 = 2644667) B2644667
theorem B1763183 : Blo 1174404 1763183 := bstep (se 1 (by rfl) ⟨1322387, by rfl⟩ : syracuseStep 1763183 = 2644775) B2644775
theorem B1763369 : Blo 1174404 1763369 := bstep (se 2 (by rfl) ⟨661263, by rfl⟩ : syracuseStep 1763369 = 1322527) B1322527
theorem B2975899 : Blo 1174404 2975899 := bstep (se 1 (by rfl) ⟨2231924, by rfl⟩ : syracuseStep 2975899 = 4463849) B4463849
theorem B7628975 : Blo 1174404 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B9054431 : Blo 1174404 9054431 := bstep (se 1 (by rfl) ⟨6790823, by rfl⟩ : syracuseStep 9054431 = 13581647) B13581647
theorem B2976041 : Blo 1174404 2976041 := bstep (se 2 (by rfl) ⟨1116015, by rfl⟩ : syracuseStep 2976041 = 2232031) B2232031
theorem B1763711 : Blo 1174404 1763711 := bstep (se 1 (by rfl) ⟨1322783, by rfl⟩ : syracuseStep 1763711 = 2645567) B2645567
theorem B20081033 : Blo 1174404 20081033 := bstep (se 2 (by rfl) ⟨7530387, by rfl⟩ : syracuseStep 20081033 = 15060775) B15060775
theorem B1984999 : Blo 1174404 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B10037783 : Blo 1174404 10037783 := bstep (se 1 (by rfl) ⟨7528337, by rfl⟩ : syracuseStep 10037783 = 15056675) B15056675
theorem B1763951 : Blo 1174404 1763951 := bstep (se 1 (by rfl) ⟨1322963, by rfl⟩ : syracuseStep 1763951 = 2645927) B2645927
theorem B14289551 : Blo 1174404 14289551 := bstep (se 1 (by rfl) ⟨10717163, by rfl⟩ : syracuseStep 14289551 = 21434327) B21434327
theorem B3345131 : Blo 1174404 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B8923931 : Blo 1174404 8923931 := bstep (se 1 (by rfl) ⟨6692948, by rfl⟩ : syracuseStep 8923931 = 13385897) B13385897
theorem B30141233 : Blo 1174404 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B1174683 : Blo 1174404 1174683 := bstep (se 1 (by rfl) ⟨881012, by rfl⟩ : syracuseStep 1174683 = 1762025) B1762025
theorem B8039735 : Blo 1174404 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1174943 : Blo 1174404 1174943 := bstep (se 1 (by rfl) ⟨881207, by rfl⟩ : syracuseStep 1174943 = 1762415) B1762415
theorem B1175023 : Blo 1174404 1175023 := bstep (se 1 (by rfl) ⟨881267, by rfl⟩ : syracuseStep 1175023 = 1762535) B1762535
theorem B5017115 : Blo 1174404 5017115 := bstep (se 1 (by rfl) ⟨3762836, by rfl⟩ : syracuseStep 5017115 = 7525673) B7525673
theorem B1175067 : Blo 1174404 1175067 := bstep (se 1 (by rfl) ⟨881300, by rfl⟩ : syracuseStep 1175067 = 1762601) B1762601
theorem B2231849 : Blo 1174404 2231849 := bstep (se 2 (by rfl) ⟨836943, by rfl⟩ : syracuseStep 2231849 = 1673887) B1673887
theorem B10727099 : Blo 1174404 10727099 := bstep (se 1 (by rfl) ⟨8045324, by rfl⟩ : syracuseStep 10727099 = 16090649) B16090649
theorem B1175247 : Blo 1174404 1175247 := bstep (se 1 (by rfl) ⟨881435, by rfl⟩ : syracuseStep 1175247 = 1762871) B1762871
theorem B1175463 : Blo 1174404 1175463 := bstep (se 1 (by rfl) ⟨881597, by rfl⟩ : syracuseStep 1175463 = 1763195) B1763195
theorem B1175487 : Blo 1174404 1175487 := bstep (se 1 (by rfl) ⟨881615, by rfl⟩ : syracuseStep 1175487 = 1763231) B1763231
theorem B3968999 : Blo 1174404 3968999 := bstep (se 1 (by rfl) ⟨2976749, by rfl⟩ : syracuseStep 3968999 = 5953499) B5953499
theorem B16076843 : Blo 1174404 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B1175643 : Blo 1174404 1175643 := bstep (se 1 (by rfl) ⟨881732, by rfl⟩ : syracuseStep 1175643 = 1763465) B1763465
theorem B1175743 : Blo 1174404 1175743 := bstep (se 1 (by rfl) ⟨881807, by rfl⟩ : syracuseStep 1175743 = 1763615) B1763615
theorem B1175775 : Blo 1174404 1175775 := bstep (se 1 (by rfl) ⟨881831, by rfl⟩ : syracuseStep 1175775 = 1763663) B1763663
theorem B1175835 : Blo 1174404 1175835 := bstep (se 1 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 1175835 = 1763753) B1763753
theorem B4460903 : Blo 1174404 4460903 := bstep (se 1 (by rfl) ⟨3345677, by rfl⟩ : syracuseStep 4460903 = 6691355) B6691355
theorem B1176091 : Blo 1174404 1176091 := bstep (se 1 (by rfl) ⟨882068, by rfl⟩ : syracuseStep 1176091 = 1764137) B1764137
theorem B2232859 : Blo 1174404 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B2642543 : Blo 1174404 2642543 := bstep (se 1 (by rfl) ⟨1981907, by rfl⟩ : syracuseStep 2642543 = 3963815) B3963815
theorem B1176231 : Blo 1174404 1176231 := bstep (se 1 (by rfl) ⟨882173, by rfl⟩ : syracuseStep 1176231 = 1764347) B1764347
theorem B1176271 : Blo 1174404 1176271 := bstep (se 1 (by rfl) ⟨882203, by rfl⟩ : syracuseStep 1176271 = 1764407) B1764407
theorem B3764989 : Blo 1174404 3764989 := bstep (se 3 (by rfl) ⟨705935, by rfl⟩ : syracuseStep 3764989 = 1411871) B1411871
theorem B1176351 : Blo 1174404 1176351 := bstep (se 1 (by rfl) ⟨882263, by rfl⟩ : syracuseStep 1176351 = 1764527) B1764527
theorem B1176391 : Blo 1174404 1176391 := bstep (se 1 (by rfl) ⟨882293, by rfl⟩ : syracuseStep 1176391 = 1764587) B1764587
theorem B13399019 : Blo 1174404 13399019 := bstep (se 1 (by rfl) ⟨10049264, by rfl⟩ : syracuseStep 13399019 = 20098529) B20098529
theorem B4461601 : Blo 1174404 4461601 := bstep (se 2 (by rfl) ⟨1673100, by rfl⟩ : syracuseStep 4461601 = 3346201) B3346201
theorem B29004925 : Blo 1174404 29004925 := bstep (se 3 (by rfl) ⟨5438423, by rfl⟩ : syracuseStep 29004925 = 10876847) B10876847
theorem B20067911 : Blo 1174404 20067911 := bstep (se 1 (by rfl) ⟨15050933, by rfl⟩ : syracuseStep 20067911 = 30101867) B30101867
theorem B8468201 : Blo 1174404 8468201 := bstep (se 2 (by rfl) ⟨3175575, by rfl⟩ : syracuseStep 8468201 = 6351151) B6351151
theorem B5019371 : Blo 1174404 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B19076867 : Blo 1174404 19076867 := bstep (se 1 (by rfl) ⟨14307650, by rfl⟩ : syracuseStep 19076867 = 28615301) B28615301
theorem B3349117 : Blo 1174404 3349117 := bstep (se 3 (by rfl) ⟨627959, by rfl⟩ : syracuseStep 3349117 = 1255919) B1255919
theorem B20085407 : Blo 1174404 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B2645099 : Blo 1174404 2645099 := bstep (se 1 (by rfl) ⟨1983824, by rfl⟩ : syracuseStep 2645099 = 3967649) B3967649
theorem B16956701 : Blo 1174404 16956701 := bstep (se 3 (by rfl) ⟨3179381, by rfl⟩ : syracuseStep 16956701 = 6358763) B6358763
theorem B2972983 : Blo 1174404 2972983 := bstep (se 1 (by rfl) ⟨2229737, by rfl⟩ : syracuseStep 2972983 = 4459475) B4459475
theorem B38141279 : Blo 1174404 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B8592767 : Blo 1174404 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B5947343 : Blo 1174404 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B1982441 : Blo 1174404 1982441 := bstep (se 2 (by rfl) ⟨743415, by rfl⟩ : syracuseStep 1982441 = 1486831) B1486831
theorem B2973935 : Blo 1174404 2973935 := bstep (se 1 (by rfl) ⟨2230451, by rfl⟩ : syracuseStep 2973935 = 4460903) B4460903
theorem B3571975 : Blo 1174404 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B1761695 : Blo 1174404 1761695 := bstep (se 1 (by rfl) ⟨1321271, by rfl⟩ : syracuseStep 1761695 = 2642543) B2642543
theorem B2646665 : Blo 1174404 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B4465489 : Blo 1174404 4465489 := bstep (se 2 (by rfl) ⟨1674558, by rfl⟩ : syracuseStep 4465489 = 3349117) B3349117
theorem B1983467 : Blo 1174404 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B9798695 : Blo 1174404 9798695 := bstep (se 1 (by rfl) ⟨7349021, by rfl⟩ : syracuseStep 9798695 = 14698043) B14698043
theorem B13378607 : Blo 1174404 13378607 := bstep (se 1 (by rfl) ⟨10033955, by rfl⟩ : syracuseStep 13378607 = 20067911) B20067911
theorem B4768895 : Blo 1174404 4768895 := bstep (se 1 (by rfl) ⟨3576671, by rfl⟩ : syracuseStep 4768895 = 7153343) B7153343
theorem B5645467 : Blo 1174404 5645467 := bstep (se 1 (by rfl) ⟨4234100, by rfl⟩ : syracuseStep 5645467 = 8468201) B8468201
theorem B5948801 : Blo 1174404 5948801 := bstep (se 2 (by rfl) ⟨2230800, by rfl⟩ : syracuseStep 5948801 = 4461601) B4461601
theorem B1984027 : Blo 1174404 1984027 := bstep (se 1 (by rfl) ⟨1488020, by rfl⟩ : syracuseStep 1984027 = 2976041) B2976041
theorem B13387355 : Blo 1174404 13387355 := bstep (se 1 (by rfl) ⟨10040516, by rfl⟩ : syracuseStep 13387355 = 20081033) B20081033
theorem B2230087 : Blo 1174404 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B5949287 : Blo 1174404 5949287 := bstep (se 1 (by rfl) ⟨4461965, by rfl⟩ : syracuseStep 5949287 = 8923931) B8923931
theorem B1763399 : Blo 1174404 1763399 := bstep (se 1 (by rfl) ⟨1322549, by rfl⟩ : syracuseStep 1763399 = 2645099) B2645099
theorem B5359823 : Blo 1174404 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B5728511 : Blo 1174404 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B2263393 : Blo 1174404 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B3344743 : Blo 1174404 3344743 := bstep (se 1 (by rfl) ⟨2508557, by rfl⟩ : syracuseStep 3344743 = 5017115) B5017115
theorem B1321627 : Blo 1174404 1321627 := bstep (se 1 (by rfl) ⟨991220, by rfl⟩ : syracuseStep 1321627 = 1982441) B1982441
theorem B10717895 : Blo 1174404 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B3967865 : Blo 1174404 3967865 := bstep (se 2 (by rfl) ⟨1487949, by rfl⟩ : syracuseStep 3967865 = 2975899) B2975899
theorem B11021195 : Blo 1174404 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B1174439 : Blo 1174404 1174439 := bstep (se 1 (by rfl) ⟨880829, by rfl⟩ : syracuseStep 1174439 = 1761659) B1761659
theorem B1174555 : Blo 1174404 1174555 := bstep (se 1 (by rfl) ⟨880916, by rfl⟩ : syracuseStep 1174555 = 1761833) B1761833
theorem B1322095 : Blo 1174404 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B1174759 : Blo 1174404 1174759 := bstep (se 1 (by rfl) ⟨881069, by rfl⟩ : syracuseStep 1174759 = 1762139) B1762139
theorem B6352127 : Blo 1174404 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B8932679 : Blo 1174404 8932679 := bstep (se 1 (by rfl) ⟨6699509, by rfl⟩ : syracuseStep 8932679 = 13399019) B13399019
theorem B2977145 : Blo 1174404 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B1175199 : Blo 1174404 1175199 := bstep (se 1 (by rfl) ⟨881399, by rfl⟩ : syracuseStep 1175199 = 1762799) B1762799
theorem B1175207 : Blo 1174404 1175207 := bstep (se 1 (by rfl) ⟨881405, by rfl⟩ : syracuseStep 1175207 = 1762811) B1762811
theorem B1175279 : Blo 1174404 1175279 := bstep (se 1 (by rfl) ⟨881459, by rfl⟩ : syracuseStep 1175279 = 1762919) B1762919
theorem B1322779 : Blo 1174404 1322779 := bstep (se 1 (by rfl) ⟨992084, by rfl⟩ : syracuseStep 1322779 = 1984169) B1984169
theorem B1175327 : Blo 1174404 1175327 := bstep (se 1 (by rfl) ⟨881495, by rfl⟩ : syracuseStep 1175327 = 1762991) B1762991
theorem B4763447 : Blo 1174404 4763447 := bstep (se 1 (by rfl) ⟨3572585, by rfl⟩ : syracuseStep 4763447 = 7145171) B7145171
theorem B3346247 : Blo 1174404 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B12717911 : Blo 1174404 12717911 := bstep (se 1 (by rfl) ⟨9538433, by rfl⟩ : syracuseStep 12717911 = 19076867) B19076867
theorem B1175407 : Blo 1174404 1175407 := bstep (se 1 (by rfl) ⟨881555, by rfl⟩ : syracuseStep 1175407 = 1763111) B1763111
theorem B1175455 : Blo 1174404 1175455 := bstep (se 1 (by rfl) ⟨881591, by rfl⟩ : syracuseStep 1175455 = 1763183) B1763183
theorem B1175579 : Blo 1174404 1175579 := bstep (se 1 (by rfl) ⟨881684, by rfl⟩ : syracuseStep 1175579 = 1763369) B1763369
theorem B1175807 : Blo 1174404 1175807 := bstep (se 1 (by rfl) ⟨881855, by rfl⟩ : syracuseStep 1175807 = 1763711) B1763711
theorem B1175967 : Blo 1174404 1175967 := bstep (se 1 (by rfl) ⟨881975, by rfl⟩ : syracuseStep 1175967 = 1763951) B1763951
theorem B13390271 : Blo 1174404 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B1487899 : Blo 1174404 1487899 := bstep (se 1 (by rfl) ⟨1115924, by rfl⟩ : syracuseStep 1487899 = 2231849) B2231849
theorem B28251479 : Blo 1174404 28251479 := bstep (se 1 (by rfl) ⟨21188609, by rfl⟩ : syracuseStep 28251479 = 42377219) B42377219
theorem B2823551 : Blo 1174404 2823551 := bstep (se 1 (by rfl) ⟨2117663, by rfl⟩ : syracuseStep 2823551 = 4235327) B4235327
theorem B6034895 : Blo 1174404 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B22599161 : Blo 1174404 22599161 := bstep (se 2 (by rfl) ⟨8474685, by rfl⟩ : syracuseStep 22599161 = 16949371) B16949371
theorem B2119393 : Blo 1174404 2119393 := bstep (se 2 (by rfl) ⟨794772, by rfl⟩ : syracuseStep 2119393 = 1589545) B1589545
theorem B10868527 : Blo 1174404 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B4462847 : Blo 1174404 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B5019985 : Blo 1174404 5019985 := bstep (se 2 (by rfl) ⟨1882494, by rfl⟩ : syracuseStep 5019985 = 3764989) B3764989
theorem B10721767 : Blo 1174404 10721767 := bstep (se 1 (by rfl) ⟨8041325, by rfl⟩ : syracuseStep 10721767 = 16082651) B16082651
theorem B5085983 : Blo 1174404 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B6036287 : Blo 1174404 6036287 := bstep (se 1 (by rfl) ⟨4527215, by rfl⟩ : syracuseStep 6036287 = 9054431) B9054431
theorem B38673233 : Blo 1174404 38673233 := bstep (se 2 (by rfl) ⟨14502462, by rfl⟩ : syracuseStep 38673233 = 29004925) B29004925
theorem B6691855 : Blo 1174404 6691855 := bstep (se 1 (by rfl) ⟨5018891, by rfl⟩ : syracuseStep 6691855 = 10037783) B10037783
theorem B3963977 : Blo 1174404 3963977 := bstep (se 2 (by rfl) ⟨1486491, by rfl⟩ : syracuseStep 3963977 = 2972983) B2972983
theorem B9526367 : Blo 1174404 9526367 := bstep (se 1 (by rfl) ⟨7144775, by rfl⟩ : syracuseStep 9526367 = 14289551) B14289551
theorem B20094155 : Blo 1174404 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B11304467 : Blo 1174404 11304467 := bstep (se 1 (by rfl) ⟨8478350, by rfl⟩ : syracuseStep 11304467 = 16956701) B16956701
theorem B25427519 : Blo 1174404 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B2973257 : Blo 1174404 2973257 := bstep (se 2 (by rfl) ⟨1114971, by rfl⟩ : syracuseStep 2973257 = 2229943) B2229943
theorem B7151399 : Blo 1174404 7151399 := bstep (se 1 (by rfl) ⟨5363549, by rfl⟩ : syracuseStep 7151399 = 10727099) B10727099
theorem B3964895 : Blo 1174404 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B2645999 : Blo 1174404 2645999 := bstep (se 1 (by rfl) ⟨1984499, by rfl⟩ : syracuseStep 2645999 = 3968999) B3968999
theorem B1982623 : Blo 1174404 1982623 := bstep (se 1 (by rfl) ⟨1486967, by rfl⟩ : syracuseStep 1982623 = 2973935) B2973935
theorem B25403645 : Blo 1174404 25403645 := bstep (se 3 (by rfl) ⟨4763183, by rfl⟩ : syracuseStep 25403645 = 9526367) B9526367
theorem B6693313 : Blo 1174404 6693313 := bstep (se 2 (by rfl) ⟨2509992, by rfl⟩ : syracuseStep 6693313 = 5019985) B5019985
theorem B14295689 : Blo 1174404 14295689 := bstep (se 2 (by rfl) ⟨5360883, by rfl⟩ : syracuseStep 14295689 = 10721767) B10721767
theorem B3179263 : Blo 1174404 3179263 := bstep (se 1 (by rfl) ⟨2384447, by rfl⟩ : syracuseStep 3179263 = 4768895) B4768895
theorem B1762169 : Blo 1174404 1762169 := bstep (se 2 (by rfl) ⟨660813, by rfl⟩ : syracuseStep 1762169 = 1321627) B1321627
theorem B18834319 : Blo 1174404 18834319 := bstep (se 1 (by rfl) ⟨14125739, by rfl⟩ : syracuseStep 18834319 = 28251479) B28251479
theorem B3965867 : Blo 1174404 3965867 := bstep (se 1 (by rfl) ⟨2974400, by rfl⟩ : syracuseStep 3965867 = 5948801) B5948801
theorem B4023263 : Blo 1174404 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B15066107 : Blo 1174404 15066107 := bstep (se 1 (by rfl) ⟨11299580, by rfl⟩ : syracuseStep 15066107 = 22599161) B22599161
theorem B3966191 : Blo 1174404 3966191 := bstep (se 1 (by rfl) ⟨2974643, by rfl⟩ : syracuseStep 3966191 = 5949287) B5949287
theorem B8922473 : Blo 1174404 8922473 := bstep (se 2 (by rfl) ⟨3345927, by rfl⟩ : syracuseStep 8922473 = 6691855) B6691855
theorem B1983865 : Blo 1174404 1983865 := bstep (se 2 (by rfl) ⟨743949, by rfl⟩ : syracuseStep 1983865 = 1487899) B1487899
theorem B3573215 : Blo 1174404 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1762793 : Blo 1174404 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B2975231 : Blo 1174404 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B3819007 : Blo 1174404 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B7145263 : Blo 1174404 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B25782155 : Blo 1174404 25782155 := bstep (se 1 (by rfl) ⟨19336616, by rfl⟩ : syracuseStep 25782155 = 38673233) B38673233
theorem B13396103 : Blo 1174404 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B1984763 : Blo 1174404 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B1763705 : Blo 1174404 1763705 := bstep (se 2 (by rfl) ⟨661389, by rfl⟩ : syracuseStep 1763705 = 1322779) B1322779
theorem B16951679 : Blo 1174404 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B2230831 : Blo 1174404 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B1763999 : Blo 1174404 1763999 := bstep (se 1 (by rfl) ⟨1322999, by rfl⟩ : syracuseStep 1763999 = 2645999) B2645999
theorem B1174463 : Blo 1174404 1174463 := bstep (se 1 (by rfl) ⟨880847, by rfl⟩ : syracuseStep 1174463 = 1761695) B1761695
theorem B4762633 : Blo 1174404 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B1764443 : Blo 1174404 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B3017857 : Blo 1174404 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B4459657 : Blo 1174404 4459657 := bstep (se 2 (by rfl) ⟨1672371, by rfl⟩ : syracuseStep 4459657 = 3344743) B3344743
theorem B1322311 : Blo 1174404 1322311 := bstep (se 1 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 1322311 = 1983467) B1983467
theorem B6532463 : Blo 1174404 6532463 := bstep (se 1 (by rfl) ⟨4899347, by rfl⟩ : syracuseStep 6532463 = 9798695) B9798695
theorem B8924903 : Blo 1174404 8924903 := bstep (se 1 (by rfl) ⟨6693677, by rfl⟩ : syracuseStep 8924903 = 13387355) B13387355
theorem B1175599 : Blo 1174404 1175599 := bstep (se 1 (by rfl) ⟨881699, by rfl⟩ : syracuseStep 1175599 = 1763399) B1763399
theorem B2642651 : Blo 1174404 2642651 := bstep (se 1 (by rfl) ⟨1981988, by rfl⟩ : syracuseStep 2642651 = 3963977) B3963977
theorem B29389853 : Blo 1174404 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B3175631 : Blo 1174404 3175631 := bstep (se 1 (by rfl) ⟨2381723, by rfl⟩ : syracuseStep 3175631 = 4763447) B4763447
theorem B2643263 : Blo 1174404 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B8926847 : Blo 1174404 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B8919071 : Blo 1174404 8919071 := bstep (se 1 (by rfl) ⟨6689303, by rfl⟩ : syracuseStep 8919071 = 13378607) B13378607
theorem B1882367 : Blo 1174404 1882367 := bstep (se 1 (by rfl) ⟨1411775, by rfl⟩ : syracuseStep 1882367 = 2823551) B2823551
theorem B5953985 : Blo 1174404 5953985 := bstep (se 2 (by rfl) ⟨2232744, by rfl⟩ : syracuseStep 5953985 = 4465489) B4465489
theorem B7527289 : Blo 1174404 7527289 := bstep (se 2 (by rfl) ⟨2822733, by rfl⟩ : syracuseStep 7527289 = 5645467) B5645467
theorem B3390655 : Blo 1174404 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B2645243 : Blo 1174404 2645243 := bstep (se 1 (by rfl) ⟨1983932, by rfl⟩ : syracuseStep 2645243 = 3967865) B3967865
theorem B2645369 : Blo 1174404 2645369 := bstep (se 2 (by rfl) ⟨992013, by rfl⟩ : syracuseStep 2645369 = 1984027) B1984027
theorem B16096765 : Blo 1174404 16096765 := bstep (se 3 (by rfl) ⟨3018143, by rfl⟩ : syracuseStep 16096765 = 6036287) B6036287
theorem B4234751 : Blo 1174404 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B5955119 : Blo 1174404 5955119 := bstep (se 1 (by rfl) ⟨4466339, by rfl⟩ : syracuseStep 5955119 = 8932679) B8932679
theorem B2825857 : Blo 1174404 2825857 := bstep (se 2 (by rfl) ⟨1059696, by rfl⟩ : syracuseStep 2825857 = 2119393) B2119393
theorem B7536311 : Blo 1174404 7536311 := bstep (se 1 (by rfl) ⟨5652233, by rfl⟩ : syracuseStep 7536311 = 11304467) B11304467
theorem B1982171 : Blo 1174404 1982171 := bstep (se 1 (by rfl) ⟨1486628, by rfl⟩ : syracuseStep 1982171 = 2973257) B2973257
theorem B14491369 : Blo 1174404 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B2973449 : Blo 1174404 2973449 := bstep (se 2 (by rfl) ⟨1115043, by rfl⟩ : syracuseStep 2973449 = 2230087) B2230087
theorem B4767599 : Blo 1174404 4767599 := bstep (se 1 (by rfl) ⟨3575699, by rfl⟩ : syracuseStep 4767599 = 7151399) B7151399
theorem B8478607 : Blo 1174404 8478607 := bstep (se 1 (by rfl) ⟨6358955, by rfl⟩ : syracuseStep 8478607 = 12717911) B12717911
theorem B1761767 : Blo 1174404 1761767 := bstep (se 1 (by rfl) ⟨1321325, by rfl⟩ : syracuseStep 1761767 = 2642651) B2642651
theorem B10044071 : Blo 1174404 10044071 := bstep (se 1 (by rfl) ⟨7533053, by rfl⟩ : syracuseStep 10044071 = 15066107) B15066107
theorem B2974441 : Blo 1174404 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B1762175 : Blo 1174404 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B5948315 : Blo 1174404 5948315 := bstep (se 1 (by rfl) ⟨4461236, by rfl⟩ : syracuseStep 5948315 = 8922473) B8922473
theorem B1983487 : Blo 1174404 1983487 := bstep (se 1 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 1983487 = 2975231) B2975231
theorem B10036385 : Blo 1174404 10036385 := bstep (se 2 (by rfl) ⟨3763644, by rfl⟩ : syracuseStep 10036385 = 7527289) B7527289
theorem B17188103 : Blo 1174404 17188103 := bstep (se 1 (by rfl) ⟨12891077, by rfl⟩ : syracuseStep 17188103 = 25782155) B25782155
theorem B6350177 : Blo 1174404 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B8930735 : Blo 1174404 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B1254911 : Blo 1174404 1254911 := bstep (se 1 (by rfl) ⟨941183, by rfl⟩ : syracuseStep 1254911 = 1882367) B1882367
theorem B4023809 : Blo 1174404 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B1763081 : Blo 1174404 1763081 := bstep (se 2 (by rfl) ⟨661155, by rfl⟩ : syracuseStep 1763081 = 1322311) B1322311
theorem B1763495 : Blo 1174404 1763495 := bstep (se 1 (by rfl) ⟨1322621, by rfl⟩ : syracuseStep 1763495 = 2645243) B2645243
theorem B1763579 : Blo 1174404 1763579 := bstep (se 1 (by rfl) ⟨1322684, by rfl⟩ : syracuseStep 1763579 = 2645369) B2645369
theorem B5024207 : Blo 1174404 5024207 := bstep (se 1 (by rfl) ⟨3768155, by rfl⟩ : syracuseStep 5024207 = 7536311) B7536311
theorem B1321447 : Blo 1174404 1321447 := bstep (se 1 (by rfl) ⟨991085, by rfl⟩ : syracuseStep 1321447 = 1982171) B1982171
theorem B5949935 : Blo 1174404 5949935 := bstep (se 1 (by rfl) ⟨4462451, by rfl⟩ : syracuseStep 5949935 = 8924903) B8924903
theorem B20368037 : Blo 1174404 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B16935763 : Blo 1174404 16935763 := bstep (se 1 (by rfl) ⟨12701822, by rfl⟩ : syracuseStep 16935763 = 25403645) B25403645
theorem B9530459 : Blo 1174404 9530459 := bstep (se 1 (by rfl) ⟨7147844, by rfl⟩ : syracuseStep 9530459 = 14295689) B14295689
theorem B1174779 : Blo 1174404 1174779 := bstep (se 1 (by rfl) ⟨881084, by rfl⟩ : syracuseStep 1174779 = 1762169) B1762169
theorem B8924417 : Blo 1174404 8924417 := bstep (se 2 (by rfl) ⟨3346656, by rfl⟩ : syracuseStep 8924417 = 6693313) B6693313
theorem B2682175 : Blo 1174404 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B2117087 : Blo 1174404 2117087 := bstep (se 1 (by rfl) ⟨1587815, by rfl⟩ : syracuseStep 2117087 = 3175631) B3175631
theorem B1175195 : Blo 1174404 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B4239017 : Blo 1174404 4239017 := bstep (se 2 (by rfl) ⟨1589631, by rfl⟩ : syracuseStep 4239017 = 3179263) B3179263
theorem B5951231 : Blo 1174404 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B25112425 : Blo 1174404 25112425 := bstep (se 2 (by rfl) ⟨9417159, by rfl⟩ : syracuseStep 25112425 = 18834319) B18834319
theorem B1323175 : Blo 1174404 1323175 := bstep (se 1 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 1323175 = 1984763) B1984763
theorem B1175803 : Blo 1174404 1175803 := bstep (se 1 (by rfl) ⟨881852, by rfl⟩ : syracuseStep 1175803 = 1763705) B1763705
theorem B11301119 : Blo 1174404 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B3969323 : Blo 1174404 3969323 := bstep (se 1 (by rfl) ⟨2976992, by rfl⟩ : syracuseStep 3969323 = 5953985) B5953985
theorem B1175999 : Blo 1174404 1175999 := bstep (se 1 (by rfl) ⟨881999, by rfl⟩ : syracuseStep 1175999 = 1763999) B1763999
theorem B1176295 : Blo 1174404 1176295 := bstep (se 1 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 1176295 = 1764443) B1764443
theorem B4354975 : Blo 1174404 4354975 := bstep (se 1 (by rfl) ⟨3266231, by rfl⟩ : syracuseStep 4354975 = 6532463) B6532463
theorem B19321825 : Blo 1174404 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B2823167 : Blo 1174404 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B3970079 : Blo 1174404 3970079 := bstep (se 1 (by rfl) ⟨2977559, by rfl⟩ : syracuseStep 3970079 = 5955119) B5955119
theorem B2643497 : Blo 1174404 2643497 := bstep (se 2 (by rfl) ⟨991311, by rfl⟩ : syracuseStep 2643497 = 1982623) B1982623
theorem B2643911 : Blo 1174404 2643911 := bstep (se 1 (by rfl) ⟨1982933, by rfl⟩ : syracuseStep 2643911 = 3965867) B3965867
theorem B19593235 : Blo 1174404 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B2644127 : Blo 1174404 2644127 := bstep (se 1 (by rfl) ⟨1983095, by rfl⟩ : syracuseStep 2644127 = 3966191) B3966191
theorem B2382143 : Blo 1174404 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B5946047 : Blo 1174404 5946047 := bstep (se 1 (by rfl) ⟨4459535, by rfl⟩ : syracuseStep 5946047 = 8919071) B8919071
theorem B5946209 : Blo 1174404 5946209 := bstep (se 2 (by rfl) ⟨2229828, by rfl⟩ : syracuseStep 5946209 = 4459657) B4459657
theorem B4520873 : Blo 1174404 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B2645153 : Blo 1174404 2645153 := bstep (se 2 (by rfl) ⟨991932, by rfl⟩ : syracuseStep 2645153 = 1983865) B1983865
theorem B21462353 : Blo 1174404 21462353 := bstep (se 2 (by rfl) ⟨8048382, by rfl⟩ : syracuseStep 21462353 = 16096765) B16096765
theorem B3767809 : Blo 1174404 3767809 := bstep (se 2 (by rfl) ⟨1412928, by rfl⟩ : syracuseStep 3767809 = 2825857) B2825857
theorem B9527017 : Blo 1174404 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B1982299 : Blo 1174404 1982299 := bstep (se 1 (by rfl) ⟨1486724, by rfl⟩ : syracuseStep 1982299 = 2973449) B2973449
theorem B11304809 : Blo 1174404 11304809 := bstep (se 2 (by rfl) ⟨4239303, by rfl⟩ : syracuseStep 11304809 = 8478607) B8478607
theorem B3178399 : Blo 1174404 3178399 := bstep (se 1 (by rfl) ⟨2383799, by rfl⟩ : syracuseStep 3178399 = 4767599) B4767599
theorem B104497253 : Blo 1174404 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B2646215 : Blo 1174404 2646215 := bstep (se 1 (by rfl) ⟨1984661, by rfl⟩ : syracuseStep 2646215 = 3969323) B3969323
theorem B3965543 : Blo 1174404 3965543 := bstep (se 1 (by rfl) ⟨2974157, by rfl⟩ : syracuseStep 3965543 = 5948315) B5948315
theorem B1761929 : Blo 1174404 1761929 := bstep (se 2 (by rfl) ⟨660723, by rfl⟩ : syracuseStep 1761929 = 1321447) B1321447
theorem B45834941 : Blo 1174404 45834941 := bstep (se 3 (by rfl) ⟨8594051, by rfl⟩ : syracuseStep 45834941 = 17188103) B17188103
theorem B2646719 : Blo 1174404 2646719 := bstep (se 1 (by rfl) ⟨1985039, by rfl⟩ : syracuseStep 2646719 = 3970079) B3970079
theorem B16933805 : Blo 1174404 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B3965921 : Blo 1174404 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B1762331 : Blo 1174404 1762331 := bstep (se 1 (by rfl) ⟨1321748, by rfl⟩ : syracuseStep 1762331 = 2643497) B2643497
theorem B1762607 : Blo 1174404 1762607 := bstep (se 1 (by rfl) ⟨1321955, by rfl⟩ : syracuseStep 1762607 = 2643911) B2643911
theorem B1762751 : Blo 1174404 1762751 := bstep (se 1 (by rfl) ⟨1322063, by rfl⟩ : syracuseStep 1762751 = 2644127) B2644127
theorem B3966623 : Blo 1174404 3966623 := bstep (se 1 (by rfl) ⟨2974967, by rfl⟩ : syracuseStep 3966623 = 5949935) B5949935
theorem B5023745 : Blo 1174404 5023745 := bstep (se 2 (by rfl) ⟨1883904, by rfl⟩ : syracuseStep 5023745 = 3767809) B3767809
theorem B1763435 : Blo 1174404 1763435 := bstep (se 1 (by rfl) ⟨1322576, by rfl⟩ : syracuseStep 1763435 = 2645153) B2645153
theorem B23226533 : Blo 1174404 23226533 := bstep (se 4 (by rfl) ⟨2177487, by rfl⟩ : syracuseStep 23226533 = 4354975) B4354975
theorem B5949611 : Blo 1174404 5949611 := bstep (se 1 (by rfl) ⟨4462208, by rfl⟩ : syracuseStep 5949611 = 8924417) B8924417
theorem B1411391 : Blo 1174404 1411391 := bstep (se 1 (by rfl) ⟨1058543, by rfl⟩ : syracuseStep 1411391 = 2117087) B2117087
theorem B33483233 : Blo 1174404 33483233 := bstep (se 2 (by rfl) ⟨12556212, by rfl⟩ : syracuseStep 33483233 = 25112425) B25112425
theorem B3967487 : Blo 1174404 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B4237865 : Blo 1174404 4237865 := bstep (se 2 (by rfl) ⟨1589199, by rfl⟩ : syracuseStep 4237865 = 3178399) B3178399
theorem B1764233 : Blo 1174404 1764233 := bstep (se 2 (by rfl) ⟨661587, by rfl⟩ : syracuseStep 1764233 = 1323175) B1323175
theorem B1174511 : Blo 1174404 1174511 := bstep (se 1 (by rfl) ⟨880883, by rfl⟩ : syracuseStep 1174511 = 1761767) B1761767
theorem B6696047 : Blo 1174404 6696047 := bstep (se 1 (by rfl) ⟨5022035, by rfl⟩ : syracuseStep 6696047 = 10044071) B10044071
theorem B1174783 : Blo 1174404 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B6352381 : Blo 1174404 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B2682539 : Blo 1174404 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B22581017 : Blo 1174404 22581017 := bstep (se 2 (by rfl) ⟨8467881, by rfl⟩ : syracuseStep 22581017 = 16935763) B16935763
theorem B1175387 : Blo 1174404 1175387 := bstep (se 1 (by rfl) ⟨881540, by rfl⟩ : syracuseStep 1175387 = 1763081) B1763081
theorem B3346429 : Blo 1174404 3346429 := bstep (se 3 (by rfl) ⟨627455, by rfl⟩ : syracuseStep 3346429 = 1254911) B1254911
theorem B1175663 : Blo 1174404 1175663 := bstep (se 1 (by rfl) ⟨881747, by rfl⟩ : syracuseStep 1175663 = 1763495) B1763495
theorem B1175719 : Blo 1174404 1175719 := bstep (se 1 (by rfl) ⟨881789, by rfl⟩ : syracuseStep 1175719 = 1763579) B1763579
theorem B3576233 : Blo 1174404 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B13578691 : Blo 1174404 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B6353639 : Blo 1174404 6353639 := bstep (se 1 (by rfl) ⟨4765229, by rfl⟩ : syracuseStep 6353639 = 9530459) B9530459
theorem B14308235 : Blo 1174404 14308235 := bstep (se 1 (by rfl) ⟨10731176, by rfl⟩ : syracuseStep 14308235 = 21462353) B21462353
theorem B12702689 : Blo 1174404 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B12055661 : Blo 1174404 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B2643065 : Blo 1174404 2643065 := bstep (se 2 (by rfl) ⟨991149, by rfl⟩ : syracuseStep 2643065 = 1982299) B1982299
theorem B7534079 : Blo 1174404 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B1882111 : Blo 1174404 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B6690923 : Blo 1174404 6690923 := bstep (se 1 (by rfl) ⟨5018192, by rfl⟩ : syracuseStep 6690923 = 10036385) B10036385
theorem B5953823 : Blo 1174404 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B25762433 : Blo 1174404 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B2644649 : Blo 1174404 2644649 := bstep (se 2 (by rfl) ⟨991743, by rfl⟩ : syracuseStep 2644649 = 1983487) B1983487
theorem B3349471 : Blo 1174404 3349471 := bstep (se 1 (by rfl) ⟨2512103, by rfl⟩ : syracuseStep 3349471 = 5024207) B5024207
theorem B3964031 : Blo 1174404 3964031 := bstep (se 1 (by rfl) ⟨2973023, by rfl⟩ : syracuseStep 3964031 = 5946047) B5946047
theorem B3964139 : Blo 1174404 3964139 := bstep (se 1 (by rfl) ⟨2973104, by rfl⟩ : syracuseStep 3964139 = 5946209) B5946209
theorem B2826011 : Blo 1174404 2826011 := bstep (se 1 (by rfl) ⟨2119508, by rfl⟩ : syracuseStep 2826011 = 4239017) B4239017
theorem B7536539 : Blo 1174404 7536539 := bstep (se 1 (by rfl) ⟨5652404, by rfl⟩ : syracuseStep 7536539 = 11304809) B11304809
theorem B69664835 : Blo 1174404 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B2384155 : Blo 1174404 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B4235759 : Blo 1174404 4235759 := bstep (se 1 (by rfl) ⟨3176819, by rfl⟩ : syracuseStep 4235759 = 6353639) B6353639
theorem B18104921 : Blo 1174404 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B11289203 : Blo 1174404 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B8037107 : Blo 1174404 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B1762043 : Blo 1174404 1762043 := bstep (se 1 (by rfl) ⟨1321532, by rfl⟩ : syracuseStep 1762043 = 2643065) B2643065
theorem B5022719 : Blo 1174404 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B4465961 : Blo 1174404 4465961 := bstep (se 2 (by rfl) ⟨1674735, by rfl⟩ : syracuseStep 4465961 = 3349471) B3349471
theorem B15484355 : Blo 1174404 15484355 := bstep (se 1 (by rfl) ⟨11613266, by rfl⟩ : syracuseStep 15484355 = 23226533) B23226533
theorem B3966407 : Blo 1174404 3966407 := bstep (se 1 (by rfl) ⟨2974805, by rfl⟩ : syracuseStep 3966407 = 5949611) B5949611
theorem B68699821 : Blo 1174404 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B1763099 : Blo 1174404 1763099 := bstep (se 1 (by rfl) ⟨1322324, by rfl⟩ : syracuseStep 1763099 = 2644649) B2644649
theorem B122226509 : Blo 1174404 122226509 := bstep (se 3 (by rfl) ⟨22917470, by rfl⟩ : syracuseStep 122226509 = 45834941) B45834941
theorem B1788359 : Blo 1174404 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B5024359 : Blo 1174404 5024359 := bstep (se 1 (by rfl) ⟨3768269, by rfl⟩ : syracuseStep 5024359 = 7536539) B7536539
theorem B2509481 : Blo 1174404 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B1764143 : Blo 1174404 1764143 := bstep (se 1 (by rfl) ⟨1323107, by rfl⟩ : syracuseStep 1764143 = 2646215) B2646215
theorem B1174619 : Blo 1174404 1174619 := bstep (se 1 (by rfl) ⟨880964, by rfl⟩ : syracuseStep 1174619 = 1761929) B1761929
theorem B1764479 : Blo 1174404 1764479 := bstep (se 1 (by rfl) ⟨1323359, by rfl⟩ : syracuseStep 1764479 = 2646719) B2646719
theorem B9538823 : Blo 1174404 9538823 := bstep (se 1 (by rfl) ⟨7154117, by rfl⟩ : syracuseStep 9538823 = 14308235) B14308235
theorem B1174887 : Blo 1174404 1174887 := bstep (se 1 (by rfl) ⟨881165, by rfl⟩ : syracuseStep 1174887 = 1762331) B1762331
theorem B3763709 : Blo 1174404 3763709 := bstep (se 3 (by rfl) ⟨705695, by rfl⟩ : syracuseStep 3763709 = 1411391) B1411391
theorem B1175071 : Blo 1174404 1175071 := bstep (se 1 (by rfl) ⟨881303, by rfl⟩ : syracuseStep 1175071 = 1762607) B1762607
theorem B1175167 : Blo 1174404 1175167 := bstep (se 1 (by rfl) ⟨881375, by rfl⟩ : syracuseStep 1175167 = 1762751) B1762751
theorem B4460615 : Blo 1174404 4460615 := bstep (se 1 (by rfl) ⟨3345461, by rfl⟩ : syracuseStep 4460615 = 6690923) B6690923
theorem B1175623 : Blo 1174404 1175623 := bstep (se 1 (by rfl) ⟨881717, by rfl⟩ : syracuseStep 1175623 = 1763435) B1763435
theorem B3969215 : Blo 1174404 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B1176155 : Blo 1174404 1176155 := bstep (se 1 (by rfl) ⟨882116, by rfl⟩ : syracuseStep 1176155 = 1764233) B1764233
theorem B2642687 : Blo 1174404 2642687 := bstep (se 1 (by rfl) ⟨1982015, by rfl⟩ : syracuseStep 2642687 = 3964031) B3964031
theorem B2642759 : Blo 1174404 2642759 := bstep (se 1 (by rfl) ⟨1982069, by rfl⟩ : syracuseStep 2642759 = 3964139) B3964139
theorem B15054011 : Blo 1174404 15054011 := bstep (se 1 (by rfl) ⟨11290508, by rfl⟩ : syracuseStep 15054011 = 22581017) B22581017
theorem B4461905 : Blo 1174404 4461905 := bstep (se 2 (by rfl) ⟨1673214, by rfl⟩ : syracuseStep 4461905 = 3346429) B3346429
theorem B2643695 : Blo 1174404 2643695 := bstep (se 1 (by rfl) ⟨1982771, by rfl⟩ : syracuseStep 2643695 = 3965543) B3965543
theorem B8468459 : Blo 1174404 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B2643947 : Blo 1174404 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2644415 : Blo 1174404 2644415 := bstep (se 1 (by rfl) ⟨1983311, by rfl⟩ : syracuseStep 2644415 = 3966623) B3966623
theorem B3349163 : Blo 1174404 3349163 := bstep (se 1 (by rfl) ⟨2511872, by rfl⟩ : syracuseStep 3349163 = 5023745) B5023745
theorem B22322155 : Blo 1174404 22322155 := bstep (se 1 (by rfl) ⟨16741616, by rfl⟩ : syracuseStep 22322155 = 33483233) B33483233
theorem B2644991 : Blo 1174404 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B2825243 : Blo 1174404 2825243 := bstep (se 1 (by rfl) ⟨2118932, by rfl⟩ : syracuseStep 2825243 = 4237865) B4237865
theorem B8469841 : Blo 1174404 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B4464031 : Blo 1174404 4464031 := bstep (se 1 (by rfl) ⟨3348023, by rfl⟩ : syracuseStep 4464031 = 6696047) B6696047
theorem B1884007 : Blo 1174404 1884007 := bstep (se 1 (by rfl) ⟨1413005, by rfl⟩ : syracuseStep 1884007 = 2826011) B2826011
theorem B2973743 : Blo 1174404 2973743 := bstep (se 1 (by rfl) ⟨2230307, by rfl⟩ : syracuseStep 2973743 = 4460615) B4460615
theorem B2646143 : Blo 1174404 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B3178873 : Blo 1174404 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B5358071 : Blo 1174404 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B1761791 : Blo 1174404 1761791 := bstep (se 1 (by rfl) ⟨1321343, by rfl⟩ : syracuseStep 1761791 = 2642687) B2642687
theorem B1761839 : Blo 1174404 1761839 := bstep (se 1 (by rfl) ⟨1321379, by rfl⟩ : syracuseStep 1761839 = 2642759) B2642759
theorem B25436861 : Blo 1174404 25436861 := bstep (se 3 (by rfl) ⟨4769411, by rfl⟩ : syracuseStep 25436861 = 9538823) B9538823
theorem B10036007 : Blo 1174404 10036007 := bstep (se 1 (by rfl) ⟨7527005, by rfl⟩ : syracuseStep 10036007 = 15054011) B15054011
theorem B2974603 : Blo 1174404 2974603 := bstep (se 1 (by rfl) ⟨2230952, by rfl⟩ : syracuseStep 2974603 = 4461905) B4461905
theorem B10322903 : Blo 1174404 10322903 := bstep (se 1 (by rfl) ⟨7742177, by rfl⟩ : syracuseStep 10322903 = 15484355) B15484355
theorem B1762463 : Blo 1174404 1762463 := bstep (se 1 (by rfl) ⟨1321847, by rfl⟩ : syracuseStep 1762463 = 2643695) B2643695
theorem B4768957 : Blo 1174404 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B29762873 : Blo 1174404 29762873 := bstep (se 2 (by rfl) ⟨11161077, by rfl⟩ : syracuseStep 29762873 = 22322155) B22322155
theorem B5645639 : Blo 1174404 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B1762631 : Blo 1174404 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B1762943 : Blo 1174404 1762943 := bstep (se 1 (by rfl) ⟨1322207, by rfl⟩ : syracuseStep 1762943 = 2644415) B2644415
theorem B1672987 : Blo 1174404 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B1763327 : Blo 1174404 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B2509139 : Blo 1174404 2509139 := bstep (se 1 (by rfl) ⟨1881854, by rfl⟩ : syracuseStep 2509139 = 3763709) B3763709
theorem B46443223 : Blo 1174404 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B12069947 : Blo 1174404 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B1174695 : Blo 1174404 1174695 := bstep (se 1 (by rfl) ⟨881021, by rfl⟩ : syracuseStep 1174695 = 1762043) B1762043
theorem B2977307 : Blo 1174404 2977307 := bstep (se 1 (by rfl) ⟨2232980, by rfl⟩ : syracuseStep 2977307 = 4465961) B4465961
theorem B1175399 : Blo 1174404 1175399 := bstep (se 1 (by rfl) ⟨881549, by rfl⟩ : syracuseStep 1175399 = 1763099) B1763099
theorem B11293121 : Blo 1174404 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B2232775 : Blo 1174404 2232775 := bstep (se 1 (by rfl) ⟨1674581, by rfl⟩ : syracuseStep 2232775 = 3349163) B3349163
theorem B1176095 : Blo 1174404 1176095 := bstep (se 1 (by rfl) ⟨882071, by rfl⟩ : syracuseStep 1176095 = 1764143) B1764143
theorem B5952041 : Blo 1174404 5952041 := bstep (se 2 (by rfl) ⟨2232015, by rfl⟩ : syracuseStep 5952041 = 4464031) B4464031
theorem B1176319 : Blo 1174404 1176319 := bstep (se 1 (by rfl) ⟨882239, by rfl⟩ : syracuseStep 1176319 = 1764479) B1764479
theorem B91599761 : Blo 1174404 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B2512009 : Blo 1174404 2512009 := bstep (se 2 (by rfl) ⟨942003, by rfl⟩ : syracuseStep 2512009 = 1884007) B1884007
theorem B2823839 : Blo 1174404 2823839 := bstep (se 1 (by rfl) ⟨2117879, by rfl⟩ : syracuseStep 2823839 = 4235759) B4235759
theorem B7526135 : Blo 1174404 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B3348479 : Blo 1174404 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B6699145 : Blo 1174404 6699145 := bstep (se 2 (by rfl) ⟨2512179, by rfl⟩ : syracuseStep 6699145 = 5024359) B5024359
theorem B2644271 : Blo 1174404 2644271 := bstep (se 1 (by rfl) ⟨1983203, by rfl⟩ : syracuseStep 2644271 = 3966407) B3966407
theorem B81484339 : Blo 1174404 81484339 := bstep (se 1 (by rfl) ⟨61113254, by rfl⟩ : syracuseStep 81484339 = 122226509) B122226509
theorem B1883495 : Blo 1174404 1883495 := bstep (se 1 (by rfl) ⟨1412621, by rfl⟩ : syracuseStep 1883495 = 2825243) B2825243
theorem B1982495 : Blo 1174404 1982495 := bstep (se 1 (by rfl) ⟨1486871, by rfl⟩ : syracuseStep 1982495 = 2973743) B2973743
theorem B3572047 : Blo 1174404 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B16957907 : Blo 1174404 16957907 := bstep (se 1 (by rfl) ⟨12718430, by rfl⟩ : syracuseStep 16957907 = 25436861) B25436861
theorem B8929277 : Blo 1174404 8929277 := bstep (se 3 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 8929277 = 3348479) B3348479
theorem B6881935 : Blo 1174404 6881935 := bstep (se 1 (by rfl) ⟨5161451, by rfl⟩ : syracuseStep 6881935 = 10322903) B10322903
theorem B19841915 : Blo 1174404 19841915 := bstep (se 1 (by rfl) ⟨14881436, by rfl⟩ : syracuseStep 19841915 = 29762873) B29762873
theorem B61924297 : Blo 1174404 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B30114989 : Blo 1174404 30114989 := bstep (se 3 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 30114989 = 11293121) B11293121
theorem B3966137 : Blo 1174404 3966137 := bstep (se 2 (by rfl) ⟨1487301, by rfl⟩ : syracuseStep 3966137 = 2974603) B2974603
theorem B1762847 : Blo 1174404 1762847 := bstep (se 1 (by rfl) ⟨1322135, by rfl⟩ : syracuseStep 1762847 = 2644271) B2644271
theorem B1672759 : Blo 1174404 1672759 := bstep (se 1 (by rfl) ⟨1254569, by rfl⟩ : syracuseStep 1672759 = 2509139) B2509139
theorem B6358609 : Blo 1174404 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B8046631 : Blo 1174404 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B1255663 : Blo 1174404 1255663 := bstep (se 1 (by rfl) ⟨941747, by rfl⟩ : syracuseStep 1255663 = 1883495) B1883495
theorem B1984871 : Blo 1174404 1984871 := bstep (se 1 (by rfl) ⟨1488653, by rfl⟩ : syracuseStep 1984871 = 2977307) B2977307
theorem B2230649 : Blo 1174404 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B1764095 : Blo 1174404 1764095 := bstep (se 1 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 1764095 = 2646143) B2646143
theorem B8932193 : Blo 1174404 8932193 := bstep (se 2 (by rfl) ⟨3349572, by rfl⟩ : syracuseStep 8932193 = 6699145) B6699145
theorem B1174527 : Blo 1174404 1174527 := bstep (se 1 (by rfl) ⟨880895, by rfl⟩ : syracuseStep 1174527 = 1761791) B1761791
theorem B3968027 : Blo 1174404 3968027 := bstep (se 1 (by rfl) ⟨2976020, by rfl⟩ : syracuseStep 3968027 = 5952041) B5952041
theorem B1174559 : Blo 1174404 1174559 := bstep (se 1 (by rfl) ⟨880919, by rfl⟩ : syracuseStep 1174559 = 1761839) B1761839
theorem B4238497 : Blo 1174404 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B2977033 : Blo 1174404 2977033 := bstep (se 2 (by rfl) ⟨1116387, by rfl⟩ : syracuseStep 2977033 = 2232775) B2232775
theorem B61066507 : Blo 1174404 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B108645785 : Blo 1174404 108645785 := bstep (se 2 (by rfl) ⟨40742169, by rfl⟩ : syracuseStep 108645785 = 81484339) B81484339
theorem B1174975 : Blo 1174404 1174975 := bstep (se 1 (by rfl) ⟨881231, by rfl⟩ : syracuseStep 1174975 = 1762463) B1762463
theorem B3763759 : Blo 1174404 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B1175087 : Blo 1174404 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B1175295 : Blo 1174404 1175295 := bstep (se 1 (by rfl) ⟨881471, by rfl⟩ : syracuseStep 1175295 = 1762943) B1762943
theorem B5017423 : Blo 1174404 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B1175551 : Blo 1174404 1175551 := bstep (se 1 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 1175551 = 1763327) B1763327
theorem B6690671 : Blo 1174404 6690671 := bstep (se 1 (by rfl) ⟨5018003, by rfl⟩ : syracuseStep 6690671 = 10036007) B10036007
theorem B1882559 : Blo 1174404 1882559 := bstep (se 1 (by rfl) ⟨1411919, by rfl⟩ : syracuseStep 1882559 = 2823839) B2823839
theorem B3349345 : Blo 1174404 3349345 := bstep (se 2 (by rfl) ⟨1256004, by rfl⟩ : syracuseStep 3349345 = 2512009) B2512009
theorem B11305271 : Blo 1174404 11305271 := bstep (se 1 (by rfl) ⟨8478953, by rfl⟩ : syracuseStep 11305271 = 16957907) B16957907
theorem B9175913 : Blo 1174404 9175913 := bstep (se 2 (by rfl) ⟨3440967, by rfl⟩ : syracuseStep 9175913 = 6881935) B6881935
theorem B4465793 : Blo 1174404 4465793 := bstep (se 2 (by rfl) ⟨1674672, by rfl⟩ : syracuseStep 4465793 = 3349345) B3349345
theorem B81422009 : Blo 1174404 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B2230345 : Blo 1174404 2230345 := bstep (se 2 (by rfl) ⟨836379, by rfl⟩ : syracuseStep 2230345 = 1672759) B1672759
theorem B1321663 : Blo 1174404 1321663 := bstep (se 1 (by rfl) ⟨991247, by rfl⟩ : syracuseStep 1321663 = 1982495) B1982495
theorem B1674217 : Blo 1174404 1674217 := bstep (se 2 (by rfl) ⟨627831, by rfl⟩ : syracuseStep 1674217 = 1255663) B1255663
theorem B4762729 : Blo 1174404 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B1175231 : Blo 1174404 1175231 := bstep (se 1 (by rfl) ⟨881423, by rfl⟩ : syracuseStep 1175231 = 1762847) B1762847
theorem B4460447 : Blo 1174404 4460447 := bstep (se 1 (by rfl) ⟨3345335, by rfl⟩ : syracuseStep 4460447 = 6690671) B6690671
theorem B1323247 : Blo 1174404 1323247 := bstep (se 1 (by rfl) ⟨992435, by rfl⟩ : syracuseStep 1323247 = 1984871) B1984871
theorem B1487099 : Blo 1174404 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B3969377 : Blo 1174404 3969377 := bstep (se 2 (by rfl) ⟨1488516, by rfl⟩ : syracuseStep 3969377 = 2977033) B2977033
theorem B1176063 : Blo 1174404 1176063 := bstep (se 1 (by rfl) ⟨882047, by rfl⟩ : syracuseStep 1176063 = 1764095) B1764095
theorem B5018345 : Blo 1174404 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B72430523 : Blo 1174404 72430523 := bstep (se 1 (by rfl) ⟨54322892, by rfl⟩ : syracuseStep 72430523 = 108645785) B108645785
theorem B6689897 : Blo 1174404 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B5952851 : Blo 1174404 5952851 := bstep (se 1 (by rfl) ⟨4464638, by rfl⟩ : syracuseStep 5952851 = 8929277) B8929277
theorem B42915365 : Blo 1174404 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B13227943 : Blo 1174404 13227943 := bstep (se 1 (by rfl) ⟨9920957, by rfl⟩ : syracuseStep 13227943 = 19841915) B19841915
theorem B20076659 : Blo 1174404 20076659 := bstep (se 1 (by rfl) ⟨15057494, by rfl⟩ : syracuseStep 20076659 = 30114989) B30114989
theorem B2644091 : Blo 1174404 2644091 := bstep (se 1 (by rfl) ⟨1983068, by rfl⟩ : syracuseStep 2644091 = 3966137) B3966137
theorem B5020157 : Blo 1174404 5020157 := bstep (se 3 (by rfl) ⟨941279, by rfl⟩ : syracuseStep 5020157 = 1882559) B1882559
theorem B82565729 : Blo 1174404 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B5651329 : Blo 1174404 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B5954795 : Blo 1174404 5954795 := bstep (se 1 (by rfl) ⟨4466096, by rfl⟩ : syracuseStep 5954795 = 8932193) B8932193
theorem B2645351 : Blo 1174404 2645351 := bstep (se 1 (by rfl) ⟨1984013, by rfl⟩ : syracuseStep 2645351 = 3968027) B3968027
theorem B8478145 : Blo 1174404 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B2973793 : Blo 1174404 2973793 := bstep (se 2 (by rfl) ⟨1115172, by rfl⟩ : syracuseStep 2973793 = 2230345) B2230345
theorem B7536847 : Blo 1174404 7536847 := bstep (se 1 (by rfl) ⟨5652635, by rfl⟩ : syracuseStep 7536847 = 11305271) B11305271
theorem B2646251 : Blo 1174404 2646251 := bstep (se 1 (by rfl) ⟨1984688, by rfl⟩ : syracuseStep 2646251 = 3969377) B3969377
theorem B3965597 : Blo 1174404 3965597 := bstep (se 3 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 3965597 = 1487099) B1487099
theorem B1762217 : Blo 1174404 1762217 := bstep (se 2 (by rfl) ⟨660831, by rfl⟩ : syracuseStep 1762217 = 1321663) B1321663
theorem B54281339 : Blo 1174404 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B1762727 : Blo 1174404 1762727 := bstep (se 1 (by rfl) ⟨1322045, by rfl⟩ : syracuseStep 1762727 = 2644091) B2644091
theorem B55043819 : Blo 1174404 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B1763567 : Blo 1174404 1763567 := bstep (se 1 (by rfl) ⟨1322675, by rfl⟩ : syracuseStep 1763567 = 2645351) B2645351
theorem B1764329 : Blo 1174404 1764329 := bstep (se 2 (by rfl) ⟨661623, by rfl⟩ : syracuseStep 1764329 = 1323247) B1323247
theorem B3345563 : Blo 1174404 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B48287015 : Blo 1174404 48287015 := bstep (se 1 (by rfl) ⟨36215261, by rfl⟩ : syracuseStep 48287015 = 72430523) B72430523
theorem B4459931 : Blo 1174404 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B2977195 : Blo 1174404 2977195 := bstep (se 1 (by rfl) ⟨2232896, by rfl⟩ : syracuseStep 2977195 = 4465793) B4465793
theorem B3968567 : Blo 1174404 3968567 := bstep (se 1 (by rfl) ⟨2976425, by rfl⟩ : syracuseStep 3968567 = 5952851) B5952851
theorem B28610243 : Blo 1174404 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B2232289 : Blo 1174404 2232289 := bstep (se 2 (by rfl) ⟨837108, by rfl⟩ : syracuseStep 2232289 = 1674217) B1674217
theorem B3346771 : Blo 1174404 3346771 := bstep (se 1 (by rfl) ⟨2510078, by rfl⟩ : syracuseStep 3346771 = 5020157) B5020157
theorem B3969863 : Blo 1174404 3969863 := bstep (se 1 (by rfl) ⟨2977397, by rfl⟩ : syracuseStep 3969863 = 5954795) B5954795
theorem B25401221 : Blo 1174404 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B6117275 : Blo 1174404 6117275 := bstep (se 1 (by rfl) ⟨4587956, by rfl⟩ : syracuseStep 6117275 = 9175913) B9175913
theorem B7535105 : Blo 1174404 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B13384439 : Blo 1174404 13384439 := bstep (se 1 (by rfl) ⟨10038329, by rfl⟩ : syracuseStep 13384439 = 20076659) B20076659
theorem B11304193 : Blo 1174404 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B17637257 : Blo 1174404 17637257 := bstep (se 2 (by rfl) ⟨6613971, by rfl⟩ : syracuseStep 17637257 = 13227943) B13227943
theorem B2973631 : Blo 1174404 2973631 := bstep (se 1 (by rfl) ⟨2230223, by rfl⟩ : syracuseStep 2973631 = 4460447) B4460447
theorem B3965057 : Blo 1174404 3965057 := bstep (se 2 (by rfl) ⟨1486896, by rfl⟩ : syracuseStep 3965057 = 2973793) B2973793
theorem B8921501 : Blo 1174404 8921501 := bstep (se 3 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 8921501 = 3345563) B3345563
theorem B2646575 : Blo 1174404 2646575 := bstep (se 1 (by rfl) ⟨1984931, by rfl⟩ : syracuseStep 2646575 = 3969863) B3969863
theorem B16934147 : Blo 1174404 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B5023403 : Blo 1174404 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B8922959 : Blo 1174404 8922959 := bstep (se 1 (by rfl) ⟨6692219, by rfl⟩ : syracuseStep 8922959 = 13384439) B13384439
theorem B19073495 : Blo 1174404 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B11758171 : Blo 1174404 11758171 := bstep (se 1 (by rfl) ⟨8818628, by rfl⟩ : syracuseStep 11758171 = 17637257) B17637257
theorem B2976385 : Blo 1174404 2976385 := bstep (se 2 (by rfl) ⟨1116144, by rfl⟩ : syracuseStep 2976385 = 2232289) B2232289
theorem B1764167 : Blo 1174404 1764167 := bstep (se 1 (by rfl) ⟨1323125, by rfl⟩ : syracuseStep 1764167 = 2646251) B2646251
theorem B1174811 : Blo 1174404 1174811 := bstep (se 1 (by rfl) ⟨881108, by rfl⟩ : syracuseStep 1174811 = 1762217) B1762217
theorem B36187559 : Blo 1174404 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B1175151 : Blo 1174404 1175151 := bstep (se 1 (by rfl) ⟨881363, by rfl⟩ : syracuseStep 1175151 = 1762727) B1762727
theorem B36695879 : Blo 1174404 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B1175711 : Blo 1174404 1175711 := bstep (se 1 (by rfl) ⟨881783, by rfl⟩ : syracuseStep 1175711 = 1763567) B1763567
theorem B3969593 : Blo 1174404 3969593 := bstep (se 2 (by rfl) ⟨1488597, by rfl⟩ : syracuseStep 3969593 = 2977195) B2977195
theorem B1176219 : Blo 1174404 1176219 := bstep (se 1 (by rfl) ⟨882164, by rfl⟩ : syracuseStep 1176219 = 1764329) B1764329
theorem B32191343 : Blo 1174404 32191343 := bstep (se 1 (by rfl) ⟨24143507, by rfl⟩ : syracuseStep 32191343 = 48287015) B48287015
theorem B10049129 : Blo 1174404 10049129 := bstep (se 2 (by rfl) ⟨3768423, by rfl⟩ : syracuseStep 10049129 = 7536847) B7536847
theorem B2643731 : Blo 1174404 2643731 := bstep (se 1 (by rfl) ⟨1982798, by rfl⟩ : syracuseStep 2643731 = 3965597) B3965597
theorem B4462361 : Blo 1174404 4462361 := bstep (se 2 (by rfl) ⟨1673385, by rfl⟩ : syracuseStep 4462361 = 3346771) B3346771
theorem B4078183 : Blo 1174404 4078183 := bstep (se 1 (by rfl) ⟨3058637, by rfl⟩ : syracuseStep 4078183 = 6117275) B6117275
theorem B15072257 : Blo 1174404 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B2973287 : Blo 1174404 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B2645711 : Blo 1174404 2645711 := bstep (se 1 (by rfl) ⟨1984283, by rfl⟩ : syracuseStep 2645711 = 3968567) B3968567
theorem B3964841 : Blo 1174404 3964841 := bstep (se 2 (by rfl) ⟨1486815, by rfl⟩ : syracuseStep 3964841 = 2973631) B2973631
theorem B5947667 : Blo 1174404 5947667 := bstep (se 1 (by rfl) ⟨4460750, by rfl⟩ : syracuseStep 5947667 = 8921501) B8921501
theorem B2646395 : Blo 1174404 2646395 := bstep (se 1 (by rfl) ⟨1984796, by rfl⟩ : syracuseStep 2646395 = 3969593) B3969593
theorem B11289431 : Blo 1174404 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B1762487 : Blo 1174404 1762487 := bstep (se 1 (by rfl) ⟨1321865, by rfl⟩ : syracuseStep 1762487 = 2643731) B2643731
theorem B2974907 : Blo 1174404 2974907 := bstep (se 1 (by rfl) ⟨2231180, by rfl⟩ : syracuseStep 2974907 = 4462361) B4462361
theorem B5948639 : Blo 1174404 5948639 := bstep (se 1 (by rfl) ⟨4461479, by rfl⟩ : syracuseStep 5948639 = 8922959) B8922959
theorem B12715663 : Blo 1174404 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B1763807 : Blo 1174404 1763807 := bstep (se 1 (by rfl) ⟨1322855, by rfl⟩ : syracuseStep 1763807 = 2645711) B2645711
theorem B24463919 : Blo 1174404 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B1764383 : Blo 1174404 1764383 := bstep (se 1 (by rfl) ⟨1323287, by rfl⟩ : syracuseStep 1764383 = 2646575) B2646575
theorem B3968513 : Blo 1174404 3968513 := bstep (se 2 (by rfl) ⟨1488192, by rfl⟩ : syracuseStep 3968513 = 2976385) B2976385
theorem B1176111 : Blo 1174404 1176111 := bstep (se 1 (by rfl) ⟨882083, by rfl⟩ : syracuseStep 1176111 = 1764167) B1764167
theorem B10048171 : Blo 1174404 10048171 := bstep (se 1 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 10048171 = 15072257) B15072257
theorem B2643227 : Blo 1174404 2643227 := bstep (se 1 (by rfl) ⟨1982420, by rfl⟩ : syracuseStep 2643227 = 3964841) B3964841
theorem B2643371 : Blo 1174404 2643371 := bstep (se 1 (by rfl) ⟨1982528, by rfl⟩ : syracuseStep 2643371 = 3965057) B3965057
theorem B21460895 : Blo 1174404 21460895 := bstep (se 1 (by rfl) ⟨16095671, by rfl⟩ : syracuseStep 21460895 = 32191343) B32191343
theorem B15677561 : Blo 1174404 15677561 := bstep (se 2 (by rfl) ⟨5879085, by rfl⟩ : syracuseStep 15677561 = 11758171) B11758171
theorem B5437577 : Blo 1174404 5437577 := bstep (se 2 (by rfl) ⟨2039091, by rfl⟩ : syracuseStep 5437577 = 4078183) B4078183
theorem B6699419 : Blo 1174404 6699419 := bstep (se 1 (by rfl) ⟨5024564, by rfl⟩ : syracuseStep 6699419 = 10049129) B10049129
theorem B3348935 : Blo 1174404 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B24125039 : Blo 1174404 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B1982191 : Blo 1174404 1982191 := bstep (se 1 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 1982191 = 2973287) B2973287
theorem B3965111 : Blo 1174404 3965111 := bstep (se 1 (by rfl) ⟨2973833, by rfl⟩ : syracuseStep 3965111 = 5947667) B5947667
theorem B14500205 : Blo 1174404 14500205 := bstep (se 3 (by rfl) ⟨2718788, by rfl⟩ : syracuseStep 14500205 = 5437577) B5437577
theorem B1983271 : Blo 1174404 1983271 := bstep (se 1 (by rfl) ⟨1487453, by rfl⟩ : syracuseStep 1983271 = 2974907) B2974907
theorem B3965759 : Blo 1174404 3965759 := bstep (se 1 (by rfl) ⟨2974319, by rfl⟩ : syracuseStep 3965759 = 5948639) B5948639
theorem B1762151 : Blo 1174404 1762151 := bstep (se 1 (by rfl) ⟨1321613, by rfl⟩ : syracuseStep 1762151 = 2643227) B2643227
theorem B1762247 : Blo 1174404 1762247 := bstep (se 1 (by rfl) ⟨1321685, by rfl⟩ : syracuseStep 1762247 = 2643371) B2643371
theorem B4466279 : Blo 1174404 4466279 := bstep (se 1 (by rfl) ⟨3349709, by rfl⟩ : syracuseStep 4466279 = 6699419) B6699419
theorem B16083359 : Blo 1174404 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B1764263 : Blo 1174404 1764263 := bstep (se 1 (by rfl) ⟨1323197, by rfl⟩ : syracuseStep 1764263 = 2646395) B2646395
theorem B41806829 : Blo 1174404 41806829 := bstep (se 3 (by rfl) ⟨7838780, by rfl⟩ : syracuseStep 41806829 = 15677561) B15677561
theorem B1174991 : Blo 1174404 1174991 := bstep (se 1 (by rfl) ⟨881243, by rfl⟩ : syracuseStep 1174991 = 1762487) B1762487
theorem B13397561 : Blo 1174404 13397561 := bstep (se 2 (by rfl) ⟨5024085, by rfl⟩ : syracuseStep 13397561 = 10048171) B10048171
theorem B14307263 : Blo 1174404 14307263 := bstep (se 1 (by rfl) ⟨10730447, by rfl⟩ : syracuseStep 14307263 = 21460895) B21460895
theorem B2232623 : Blo 1174404 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B1175871 : Blo 1174404 1175871 := bstep (se 1 (by rfl) ⟨881903, by rfl⟩ : syracuseStep 1175871 = 1763807) B1763807
theorem B1176255 : Blo 1174404 1176255 := bstep (se 1 (by rfl) ⟨882191, by rfl⟩ : syracuseStep 1176255 = 1764383) B1764383
theorem B16954217 : Blo 1174404 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B2642921 : Blo 1174404 2642921 := bstep (se 2 (by rfl) ⟨991095, by rfl⟩ : syracuseStep 2642921 = 1982191) B1982191
theorem B7526287 : Blo 1174404 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B16309279 : Blo 1174404 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B2645675 : Blo 1174404 2645675 := bstep (se 1 (by rfl) ⟨1984256, by rfl⟩ : syracuseStep 2645675 = 3968513) B3968513
theorem B9666803 : Blo 1174404 9666803 := bstep (se 1 (by rfl) ⟨7250102, by rfl⟩ : syracuseStep 9666803 = 14500205) B14500205
theorem B1761947 : Blo 1174404 1761947 := bstep (se 1 (by rfl) ⟨1321460, by rfl⟩ : syracuseStep 1761947 = 2642921) B2642921
theorem B27871219 : Blo 1174404 27871219 := bstep (se 1 (by rfl) ⟨20903414, by rfl⟩ : syracuseStep 27871219 = 41806829) B41806829
theorem B8931707 : Blo 1174404 8931707 := bstep (se 1 (by rfl) ⟨6698780, by rfl⟩ : syracuseStep 8931707 = 13397561) B13397561
theorem B1763783 : Blo 1174404 1763783 := bstep (se 1 (by rfl) ⟨1322837, by rfl⟩ : syracuseStep 1763783 = 2645675) B2645675
theorem B9538175 : Blo 1174404 9538175 := bstep (se 1 (by rfl) ⟨7153631, by rfl⟩ : syracuseStep 9538175 = 14307263) B14307263
theorem B1174767 : Blo 1174404 1174767 := bstep (se 1 (by rfl) ⟨881075, by rfl⟩ : syracuseStep 1174767 = 1762151) B1762151
theorem B1174831 : Blo 1174404 1174831 := bstep (se 1 (by rfl) ⟨881123, by rfl⟩ : syracuseStep 1174831 = 1762247) B1762247
theorem B2977519 : Blo 1174404 2977519 := bstep (se 1 (by rfl) ⟨2233139, by rfl⟩ : syracuseStep 2977519 = 4466279) B4466279
theorem B21745705 : Blo 1174404 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B1176175 : Blo 1174404 1176175 := bstep (se 1 (by rfl) ⟨882131, by rfl⟩ : syracuseStep 1176175 = 1764263) B1764263
theorem B2643407 : Blo 1174404 2643407 := bstep (se 1 (by rfl) ⟨1982555, by rfl⟩ : syracuseStep 2643407 = 3965111) B3965111
theorem B2643839 : Blo 1174404 2643839 := bstep (se 1 (by rfl) ⟨1982879, by rfl⟩ : syracuseStep 2643839 = 3965759) B3965759
theorem B11302811 : Blo 1174404 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B5953661 : Blo 1174404 5953661 := bstep (se 3 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 5953661 = 2232623) B2232623
theorem B2644361 : Blo 1174404 2644361 := bstep (se 2 (by rfl) ⟨991635, by rfl⟩ : syracuseStep 2644361 = 1983271) B1983271
theorem B10722239 : Blo 1174404 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B10035049 : Blo 1174404 10035049 := bstep (se 2 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 10035049 = 7526287) B7526287
theorem B1762271 : Blo 1174404 1762271 := bstep (se 1 (by rfl) ⟨1321703, by rfl⟩ : syracuseStep 1762271 = 2643407) B2643407
theorem B1762559 : Blo 1174404 1762559 := bstep (se 1 (by rfl) ⟨1321919, by rfl⟩ : syracuseStep 1762559 = 2643839) B2643839
theorem B1762907 : Blo 1174404 1762907 := bstep (se 1 (by rfl) ⟨1322180, by rfl⟩ : syracuseStep 1762907 = 2644361) B2644361
theorem B6358783 : Blo 1174404 6358783 := bstep (se 1 (by rfl) ⟨4769087, by rfl⟩ : syracuseStep 6358783 = 9538175) B9538175
theorem B13380065 : Blo 1174404 13380065 := bstep (se 2 (by rfl) ⟨5017524, by rfl⟩ : syracuseStep 13380065 = 10035049) B10035049
theorem B37161625 : Blo 1174404 37161625 := bstep (se 2 (by rfl) ⟨13935609, by rfl⟩ : syracuseStep 37161625 = 27871219) B27871219
theorem B28994273 : Blo 1174404 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B1174631 : Blo 1174404 1174631 := bstep (se 1 (by rfl) ⟨880973, by rfl⟩ : syracuseStep 1174631 = 1761947) B1761947
theorem B3969107 : Blo 1174404 3969107 := bstep (se 1 (by rfl) ⟨2976830, by rfl⟩ : syracuseStep 3969107 = 5953661) B5953661
theorem B1175855 : Blo 1174404 1175855 := bstep (se 1 (by rfl) ⟨881891, by rfl⟩ : syracuseStep 1175855 = 1763783) B1763783
theorem B7148159 : Blo 1174404 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B3970025 : Blo 1174404 3970025 := bstep (se 2 (by rfl) ⟨1488759, by rfl⟩ : syracuseStep 3970025 = 2977519) B2977519
theorem B6444535 : Blo 1174404 6444535 := bstep (se 1 (by rfl) ⟨4833401, by rfl⟩ : syracuseStep 6444535 = 9666803) B9666803
theorem B7535207 : Blo 1174404 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B5954471 : Blo 1174404 5954471 := bstep (se 1 (by rfl) ⟨4465853, by rfl⟩ : syracuseStep 5954471 = 8931707) B8931707
theorem B2646071 : Blo 1174404 2646071 := bstep (se 1 (by rfl) ⟨1984553, by rfl⟩ : syracuseStep 2646071 = 3969107) B3969107
theorem B2646683 : Blo 1174404 2646683 := bstep (se 1 (by rfl) ⟨1985012, by rfl⟩ : syracuseStep 2646683 = 3970025) B3970025
theorem B5023471 : Blo 1174404 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B1174847 : Blo 1174404 1174847 := bstep (se 1 (by rfl) ⟨881135, by rfl⟩ : syracuseStep 1174847 = 1762271) B1762271
theorem B1175039 : Blo 1174404 1175039 := bstep (se 1 (by rfl) ⟨881279, by rfl⟩ : syracuseStep 1175039 = 1762559) B1762559
theorem B49548833 : Blo 1174404 49548833 := bstep (se 2 (by rfl) ⟨18580812, by rfl⟩ : syracuseStep 49548833 = 37161625) B37161625
theorem B1175271 : Blo 1174404 1175271 := bstep (se 1 (by rfl) ⟨881453, by rfl⟩ : syracuseStep 1175271 = 1762907) B1762907
theorem B19329515 : Blo 1174404 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B3969647 : Blo 1174404 3969647 := bstep (se 1 (by rfl) ⟨2977235, by rfl⟩ : syracuseStep 3969647 = 5954471) B5954471
theorem B4765439 : Blo 1174404 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B8920043 : Blo 1174404 8920043 := bstep (se 1 (by rfl) ⟨6690032, by rfl⟩ : syracuseStep 8920043 = 13380065) B13380065
theorem B8592713 : Blo 1174404 8592713 := bstep (se 2 (by rfl) ⟨3222267, by rfl⟩ : syracuseStep 8592713 = 6444535) B6444535
theorem B8478377 : Blo 1174404 8478377 := bstep (se 2 (by rfl) ⟨3179391, by rfl⟩ : syracuseStep 8478377 = 6358783) B6358783
theorem B12886343 : Blo 1174404 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B2646431 : Blo 1174404 2646431 := bstep (se 1 (by rfl) ⟨1984823, by rfl⟩ : syracuseStep 2646431 = 3969647) B3969647
theorem B12707837 : Blo 1174404 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B5728475 : Blo 1174404 5728475 := bstep (se 1 (by rfl) ⟨4296356, by rfl⟩ : syracuseStep 5728475 = 8592713) B8592713
theorem B33032555 : Blo 1174404 33032555 := bstep (se 1 (by rfl) ⟨24774416, by rfl⟩ : syracuseStep 33032555 = 49548833) B49548833
theorem B1764047 : Blo 1174404 1764047 := bstep (se 1 (by rfl) ⟨1323035, by rfl⟩ : syracuseStep 1764047 = 2646071) B2646071
theorem B1764455 : Blo 1174404 1764455 := bstep (se 1 (by rfl) ⟨1323341, by rfl⟩ : syracuseStep 1764455 = 2646683) B2646683
theorem B6697961 : Blo 1174404 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B5946695 : Blo 1174404 5946695 := bstep (se 1 (by rfl) ⟨4460021, by rfl⟩ : syracuseStep 5946695 = 8920043) B8920043
theorem B5652251 : Blo 1174404 5652251 := bstep (se 1 (by rfl) ⟨4239188, by rfl⟩ : syracuseStep 5652251 = 8478377) B8478377
theorem B4465307 : Blo 1174404 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B8471891 : Blo 1174404 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B3818983 : Blo 1174404 3818983 := bstep (se 1 (by rfl) ⟨2864237, by rfl⟩ : syracuseStep 3818983 = 5728475) B5728475
theorem B22021703 : Blo 1174404 22021703 := bstep (se 1 (by rfl) ⟨16516277, by rfl⟩ : syracuseStep 22021703 = 33032555) B33032555
theorem B1764287 : Blo 1174404 1764287 := bstep (se 1 (by rfl) ⟨1323215, by rfl⟩ : syracuseStep 1764287 = 2646431) B2646431
theorem B1176031 : Blo 1174404 1176031 := bstep (se 1 (by rfl) ⟨882023, by rfl⟩ : syracuseStep 1176031 = 1764047) B1764047
theorem B1176303 : Blo 1174404 1176303 := bstep (se 1 (by rfl) ⟨882227, by rfl⟩ : syracuseStep 1176303 = 1764455) B1764455
theorem B8590895 : Blo 1174404 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B3964463 : Blo 1174404 3964463 := bstep (se 1 (by rfl) ⟨2973347, by rfl⟩ : syracuseStep 3964463 = 5946695) B5946695
theorem B3768167 : Blo 1174404 3768167 := bstep (se 1 (by rfl) ⟨2826125, by rfl⟩ : syracuseStep 3768167 = 5652251) B5652251
theorem B5727263 : Blo 1174404 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B14681135 : Blo 1174404 14681135 := bstep (se 1 (by rfl) ⟨11010851, by rfl⟩ : syracuseStep 14681135 = 22021703) B22021703
theorem B2976871 : Blo 1174404 2976871 := bstep (se 1 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 2976871 = 4465307) B4465307
theorem B1176191 : Blo 1174404 1176191 := bstep (se 1 (by rfl) ⟨882143, by rfl⟩ : syracuseStep 1176191 = 1764287) B1764287
theorem B5091977 : Blo 1174404 5091977 := bstep (se 2 (by rfl) ⟨1909491, by rfl⟩ : syracuseStep 5091977 = 3818983) B3818983
theorem B10048445 : Blo 1174404 10048445 := bstep (se 3 (by rfl) ⟨1884083, by rfl⟩ : syracuseStep 10048445 = 3768167) B3768167
theorem B2642975 : Blo 1174404 2642975 := bstep (se 1 (by rfl) ⟨1982231, by rfl⟩ : syracuseStep 2642975 = 3964463) B3964463
theorem B22591709 : Blo 1174404 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B39149693 : Blo 1174404 39149693 := bstep (se 3 (by rfl) ⟨7340567, by rfl⟩ : syracuseStep 39149693 = 14681135) B14681135
theorem B1761983 : Blo 1174404 1761983 := bstep (se 1 (by rfl) ⟨1321487, by rfl⟩ : syracuseStep 1761983 = 2642975) B2642975
theorem B15272701 : Blo 1174404 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B3969161 : Blo 1174404 3969161 := bstep (se 2 (by rfl) ⟨1488435, by rfl⟩ : syracuseStep 3969161 = 2976871) B2976871
theorem B15061139 : Blo 1174404 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B13578605 : Blo 1174404 13578605 := bstep (se 3 (by rfl) ⟨2545988, by rfl⟩ : syracuseStep 13578605 = 5091977) B5091977
theorem B6698963 : Blo 1174404 6698963 := bstep (se 1 (by rfl) ⟨5024222, by rfl⟩ : syracuseStep 6698963 = 10048445) B10048445
theorem B26099795 : Blo 1174404 26099795 := bstep (se 1 (by rfl) ⟨19574846, by rfl⟩ : syracuseStep 26099795 = 39149693) B39149693
theorem B2646107 : Blo 1174404 2646107 := bstep (se 1 (by rfl) ⟨1984580, by rfl⟩ : syracuseStep 2646107 = 3969161) B3969161
theorem B9052403 : Blo 1174404 9052403 := bstep (se 1 (by rfl) ⟨6789302, by rfl⟩ : syracuseStep 9052403 = 13578605) B13578605
theorem B4465975 : Blo 1174404 4465975 := bstep (se 1 (by rfl) ⟨3349481, by rfl⟩ : syracuseStep 4465975 = 6698963) B6698963
theorem B81454405 : Blo 1174404 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B1174655 : Blo 1174404 1174655 := bstep (se 1 (by rfl) ⟨880991, by rfl⟩ : syracuseStep 1174655 = 1761983) B1761983
theorem B10040759 : Blo 1174404 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B17399863 : Blo 1174404 17399863 := bstep (se 1 (by rfl) ⟨13049897, by rfl⟩ : syracuseStep 17399863 = 26099795) B26099795
theorem B6693839 : Blo 1174404 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B1764071 : Blo 1174404 1764071 := bstep (se 1 (by rfl) ⟨1323053, by rfl⟩ : syracuseStep 1764071 = 2646107) B2646107
theorem B108605873 : Blo 1174404 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B24139741 : Blo 1174404 24139741 := bstep (se 3 (by rfl) ⟨4526201, by rfl⟩ : syracuseStep 24139741 = 9052403) B9052403
theorem B5954633 : Blo 1174404 5954633 := bstep (se 2 (by rfl) ⟨2232987, by rfl⟩ : syracuseStep 5954633 = 4465975) B4465975
theorem B23199817 : Blo 1174404 23199817 := bstep (se 2 (by rfl) ⟨8699931, by rfl⟩ : syracuseStep 23199817 = 17399863) B17399863
theorem B72403915 : Blo 1174404 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B1176047 : Blo 1174404 1176047 := bstep (se 1 (by rfl) ⟨882035, by rfl⟩ : syracuseStep 1176047 = 1764071) B1764071
theorem B3969755 : Blo 1174404 3969755 := bstep (se 1 (by rfl) ⟨2977316, by rfl⟩ : syracuseStep 3969755 = 5954633) B5954633
theorem B4462559 : Blo 1174404 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B32186321 : Blo 1174404 32186321 := bstep (se 2 (by rfl) ⟨12069870, by rfl⟩ : syracuseStep 32186321 = 24139741) B24139741
theorem B30933089 : Blo 1174404 30933089 := bstep (se 2 (by rfl) ⟨11599908, by rfl⟩ : syracuseStep 30933089 = 23199817) B23199817
theorem B2646503 : Blo 1174404 2646503 := bstep (se 1 (by rfl) ⟨1984877, by rfl⟩ : syracuseStep 2646503 = 3969755) B3969755
theorem B2975039 : Blo 1174404 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B21457547 : Blo 1174404 21457547 := bstep (se 1 (by rfl) ⟨16093160, by rfl⟩ : syracuseStep 21457547 = 32186321) B32186321
theorem B96538553 : Blo 1174404 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B1983359 : Blo 1174404 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B14305031 : Blo 1174404 14305031 := bstep (se 1 (by rfl) ⟨10728773, by rfl⟩ : syracuseStep 14305031 = 21457547) B21457547
theorem B64359035 : Blo 1174404 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B20622059 : Blo 1174404 20622059 := bstep (se 1 (by rfl) ⟨15466544, by rfl⟩ : syracuseStep 20622059 = 30933089) B30933089
theorem B1764335 : Blo 1174404 1764335 := bstep (se 1 (by rfl) ⟨1323251, by rfl⟩ : syracuseStep 1764335 = 2646503) B2646503
theorem B9536687 : Blo 1174404 9536687 := bstep (se 1 (by rfl) ⟨7152515, by rfl⟩ : syracuseStep 9536687 = 14305031) B14305031
theorem B13748039 : Blo 1174404 13748039 := bstep (se 1 (by rfl) ⟨10311029, by rfl⟩ : syracuseStep 13748039 = 20622059) B20622059
theorem B1322239 : Blo 1174404 1322239 := bstep (se 1 (by rfl) ⟨991679, by rfl⟩ : syracuseStep 1322239 = 1983359) B1983359
theorem B42906023 : Blo 1174404 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B1176223 : Blo 1174404 1176223 := bstep (se 1 (by rfl) ⟨882167, by rfl⟩ : syracuseStep 1176223 = 1764335) B1764335
theorem B6357791 : Blo 1174404 6357791 := bstep (se 1 (by rfl) ⟨4768343, by rfl⟩ : syracuseStep 6357791 = 9536687) B9536687
theorem B1762985 : Blo 1174404 1762985 := bstep (se 2 (by rfl) ⟨661119, by rfl⟩ : syracuseStep 1762985 = 1322239) B1322239
theorem B28604015 : Blo 1174404 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B9165359 : Blo 1174404 9165359 := bstep (se 1 (by rfl) ⟨6874019, by rfl⟩ : syracuseStep 9165359 = 13748039) B13748039
theorem B4238527 : Blo 1174404 4238527 := bstep (se 1 (by rfl) ⟨3178895, by rfl⟩ : syracuseStep 4238527 = 6357791) B6357791
theorem B1175323 : Blo 1174404 1175323 := bstep (se 1 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 1175323 = 1762985) B1762985
theorem B19069343 : Blo 1174404 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B6110239 : Blo 1174404 6110239 := bstep (se 1 (by rfl) ⟨4582679, by rfl⟩ : syracuseStep 6110239 = 9165359) B9165359
theorem B8146985 : Blo 1174404 8146985 := bstep (se 2 (by rfl) ⟨3055119, by rfl⟩ : syracuseStep 8146985 = 6110239) B6110239
theorem B5651369 : Blo 1174404 5651369 := bstep (se 2 (by rfl) ⟨2119263, by rfl⟩ : syracuseStep 5651369 = 4238527) B4238527
theorem B12712895 : Blo 1174404 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B21725293 : Blo 1174404 21725293 := bstep (se 3 (by rfl) ⟨4073492, by rfl⟩ : syracuseStep 21725293 = 8146985) B8146985
theorem B8475263 : Blo 1174404 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B3767579 : Blo 1174404 3767579 := bstep (se 1 (by rfl) ⟨2825684, by rfl⟩ : syracuseStep 3767579 = 5651369) B5651369
theorem B28967057 : Blo 1174404 28967057 := bstep (se 2 (by rfl) ⟨10862646, by rfl⟩ : syracuseStep 28967057 = 21725293) B21725293
theorem B2511719 : Blo 1174404 2511719 := bstep (se 1 (by rfl) ⟨1883789, by rfl⟩ : syracuseStep 2511719 = 3767579) B3767579
theorem B5650175 : Blo 1174404 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B15067133 : Blo 1174404 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B19311371 : Blo 1174404 19311371 := bstep (se 1 (by rfl) ⟨14483528, by rfl⟩ : syracuseStep 19311371 = 28967057) B28967057
theorem B1674479 : Blo 1174404 1674479 := bstep (se 1 (by rfl) ⟨1255859, by rfl⟩ : syracuseStep 1674479 = 2511719) B2511719
theorem B4465277 : Blo 1174404 4465277 := bstep (se 3 (by rfl) ⟨837239, by rfl⟩ : syracuseStep 4465277 = 1674479) B1674479
theorem B10044755 : Blo 1174404 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B12874247 : Blo 1174404 12874247 := bstep (se 1 (by rfl) ⟨9655685, by rfl⟩ : syracuseStep 12874247 = 19311371) B19311371
theorem B2976851 : Blo 1174404 2976851 := bstep (se 1 (by rfl) ⟨2232638, by rfl⟩ : syracuseStep 2976851 = 4465277) B4465277
theorem B6696503 : Blo 1174404 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B8582831 : Blo 1174404 8582831 := bstep (se 1 (by rfl) ⟨6437123, by rfl⟩ : syracuseStep 8582831 = 12874247) B12874247
theorem B1984567 : Blo 1174404 1984567 := bstep (se 1 (by rfl) ⟨1488425, by rfl⟩ : syracuseStep 1984567 = 2976851) B2976851
theorem B5721887 : Blo 1174404 5721887 := bstep (se 1 (by rfl) ⟨4291415, by rfl⟩ : syracuseStep 5721887 = 8582831) B8582831
theorem B4464335 : Blo 1174404 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B2646089 : Blo 1174404 2646089 := bstep (se 2 (by rfl) ⟨992283, by rfl⟩ : syracuseStep 2646089 = 1984567) B1984567
theorem B2976223 : Blo 1174404 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B15258365 : Blo 1174404 15258365 := bstep (se 3 (by rfl) ⟨2860943, by rfl⟩ : syracuseStep 15258365 = 5721887) B5721887
theorem B1764059 : Blo 1174404 1764059 := bstep (se 1 (by rfl) ⟨1323044, by rfl⟩ : syracuseStep 1764059 = 2646089) B2646089
theorem B3968297 : Blo 1174404 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B10172243 : Blo 1174404 10172243 := bstep (se 1 (by rfl) ⟨7629182, by rfl⟩ : syracuseStep 10172243 = 15258365) B15258365
theorem B1176039 : Blo 1174404 1176039 := bstep (se 1 (by rfl) ⟨882029, by rfl⟩ : syracuseStep 1176039 = 1764059) B1764059
theorem B6781495 : Blo 1174404 6781495 := bstep (se 1 (by rfl) ⟨5086121, by rfl⟩ : syracuseStep 6781495 = 10172243) B10172243
theorem B2645531 : Blo 1174404 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B1763687 : Blo 1174404 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531
theorem B9041993 : Blo 1174404 9041993 := bstep (se 2 (by rfl) ⟨3390747, by rfl⟩ : syracuseStep 9041993 = 6781495) B6781495
theorem B1175791 : Blo 1174404 1175791 := bstep (se 1 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 1175791 = 1763687) B1763687
theorem B6027995 : Blo 1174404 6027995 := bstep (se 1 (by rfl) ⟨4520996, by rfl⟩ : syracuseStep 6027995 = 9041993) B9041993
theorem B4018663 : Blo 1174404 4018663 := bstep (se 1 (by rfl) ⟨3013997, by rfl⟩ : syracuseStep 4018663 = 6027995) B6027995
theorem B5358217 : Blo 1174404 5358217 := bstep (se 2 (by rfl) ⟨2009331, by rfl⟩ : syracuseStep 5358217 = 4018663) B4018663
theorem B7144289 : Blo 1174404 7144289 := bstep (se 2 (by rfl) ⟨2679108, by rfl⟩ : syracuseStep 7144289 = 5358217) B5358217
theorem B4762859 : Blo 1174404 4762859 := bstep (se 1 (by rfl) ⟨3572144, by rfl⟩ : syracuseStep 4762859 = 7144289) B7144289
theorem B12700957 : Blo 1174404 12700957 := bstep (se 3 (by rfl) ⟨2381429, by rfl⟩ : syracuseStep 12700957 = 4762859) B4762859
theorem B16934609 : Blo 1174404 16934609 := bstep (se 2 (by rfl) ⟨6350478, by rfl⟩ : syracuseStep 16934609 = 12700957) B12700957
theorem B11289739 : Blo 1174404 11289739 := bstep (se 1 (by rfl) ⟨8467304, by rfl⟩ : syracuseStep 11289739 = 16934609) B16934609
theorem B15052985 : Blo 1174404 15052985 := bstep (se 2 (by rfl) ⟨5644869, by rfl⟩ : syracuseStep 15052985 = 11289739) B11289739
theorem B10035323 : Blo 1174404 10035323 := bstep (se 1 (by rfl) ⟨7526492, by rfl⟩ : syracuseStep 10035323 = 15052985) B15052985
theorem B6690215 : Blo 1174404 6690215 := bstep (se 1 (by rfl) ⟨5017661, by rfl⟩ : syracuseStep 6690215 = 10035323) B10035323
theorem B4460143 : Blo 1174404 4460143 := bstep (se 1 (by rfl) ⟨3345107, by rfl⟩ : syracuseStep 4460143 = 6690215) B6690215
theorem B5946857 : Blo 1174404 5946857 := bstep (se 2 (by rfl) ⟨2230071, by rfl⟩ : syracuseStep 5946857 = 4460143) B4460143
theorem B3964571 : Blo 1174404 3964571 := bstep (se 1 (by rfl) ⟨2973428, by rfl⟩ : syracuseStep 3964571 = 5946857) B5946857
theorem B2643047 : Blo 1174404 2643047 := bstep (se 1 (by rfl) ⟨1982285, by rfl⟩ : syracuseStep 2643047 = 3964571) B3964571
theorem B1762031 : Blo 1174404 1762031 := bstep (se 1 (by rfl) ⟨1321523, by rfl⟩ : syracuseStep 1762031 = 2643047) B2643047
theorem B1174687 : Blo 1174404 1174687 := bstep (se 1 (by rfl) ⟨881015, by rfl⟩ : syracuseStep 1174687 = 1762031) B1762031

theorem C0 (j : ℕ) (h1 : 293601 ≤ j) (h2 : j ≤ 294100) : Blo 1174404 (4 * j + 3) := by
  interval_cases j
  · exact B1174407
  · exact B1174411
  · exact B1174415
  · exact B1174419
  · exact B1174423
  · exact B1174427
  · exact B1174431
  · exact B1174435
  · exact B1174439
  · exact B1174443
  · exact B1174447
  · exact B1174451
  · exact B1174455
  · exact B1174459
  · exact B1174463
  · exact B1174467
  · exact B1174471
  · exact B1174475
  · exact B1174479
  · exact B1174483
  · exact B1174487
  · exact B1174491
  · exact B1174495
  · exact B1174499
  · exact B1174503
  · exact B1174507
  · exact B1174511
  · exact B1174515
  · exact B1174519
  · exact B1174523
  · exact B1174527
  · exact B1174531
  · exact B1174535
  · exact B1174539
  · exact B1174543
  · exact B1174547
  · exact B1174551
  · exact B1174555
  · exact B1174559
  · exact B1174563
  · exact B1174567
  · exact B1174571
  · exact B1174575
  · exact B1174579
  · exact B1174583
  · exact B1174587
  · exact B1174591
  · exact B1174595
  · exact B1174599
  · exact B1174603
  · exact B1174607
  · exact B1174611
  · exact B1174615
  · exact B1174619
  · exact B1174623
  · exact B1174627
  · exact B1174631
  · exact B1174635
  · exact B1174639
  · exact B1174643
  · exact B1174647
  · exact B1174651
  · exact B1174655
  · exact B1174659
  · exact B1174663
  · exact B1174667
  · exact B1174671
  · exact B1174675
  · exact B1174679
  · exact B1174683
  · exact B1174687
  · exact B1174691
  · exact B1174695
  · exact B1174699
  · exact B1174703
  · exact B1174707
  · exact B1174711
  · exact B1174715
  · exact B1174719
  · exact B1174723
  · exact B1174727
  · exact B1174731
  · exact B1174735
  · exact B1174739
  · exact B1174743
  · exact B1174747
  · exact B1174751
  · exact B1174755
  · exact B1174759
  · exact B1174763
  · exact B1174767
  · exact B1174771
  · exact B1174775
  · exact B1174779
  · exact B1174783
  · exact B1174787
  · exact B1174791
  · exact B1174795
  · exact B1174799
  · exact B1174803
  · exact B1174807
  · exact B1174811
  · exact B1174815
  · exact B1174819
  · exact B1174823
  · exact B1174827
  · exact B1174831
  · exact B1174835
  · exact B1174839
  · exact B1174843
  · exact B1174847
  · exact B1174851
  · exact B1174855
  · exact B1174859
  · exact B1174863
  · exact B1174867
  · exact B1174871
  · exact B1174875
  · exact B1174879
  · exact B1174883
  · exact B1174887
  · exact B1174891
  · exact B1174895
  · exact B1174899
  · exact B1174903
  · exact B1174907
  · exact B1174911
  · exact B1174915
  · exact B1174919
  · exact B1174923
  · exact B1174927
  · exact B1174931
  · exact B1174935
  · exact B1174939
  · exact B1174943
  · exact B1174947
  · exact B1174951
  · exact B1174955
  · exact B1174959
  · exact B1174963
  · exact B1174967
  · exact B1174971
  · exact B1174975
  · exact B1174979
  · exact B1174983
  · exact B1174987
  · exact B1174991
  · exact B1174995
  · exact B1174999
  · exact B1175003
  · exact B1175007
  · exact B1175011
  · exact B1175015
  · exact B1175019
  · exact B1175023
  · exact B1175027
  · exact B1175031
  · exact B1175035
  · exact B1175039
  · exact B1175043
  · exact B1175047
  · exact B1175051
  · exact B1175055
  · exact B1175059
  · exact B1175063
  · exact B1175067
  · exact B1175071
  · exact B1175075
  · exact B1175079
  · exact B1175083
  · exact B1175087
  · exact B1175091
  · exact B1175095
  · exact B1175099
  · exact B1175103
  · exact B1175107
  · exact B1175111
  · exact B1175115
  · exact B1175119
  · exact B1175123
  · exact B1175127
  · exact B1175131
  · exact B1175135
  · exact B1175139
  · exact B1175143
  · exact B1175147
  · exact B1175151
  · exact B1175155
  · exact B1175159
  · exact B1175163
  · exact B1175167
  · exact B1175171
  · exact B1175175
  · exact B1175179
  · exact B1175183
  · exact B1175187
  · exact B1175191
  · exact B1175195
  · exact B1175199
  · exact B1175203
  · exact B1175207
  · exact B1175211
  · exact B1175215
  · exact B1175219
  · exact B1175223
  · exact B1175227
  · exact B1175231
  · exact B1175235
  · exact B1175239
  · exact B1175243
  · exact B1175247
  · exact B1175251
  · exact B1175255
  · exact B1175259
  · exact B1175263
  · exact B1175267
  · exact B1175271
  · exact B1175275
  · exact B1175279
  · exact B1175283
  · exact B1175287
  · exact B1175291
  · exact B1175295
  · exact B1175299
  · exact B1175303
  · exact B1175307
  · exact B1175311
  · exact B1175315
  · exact B1175319
  · exact B1175323
  · exact B1175327
  · exact B1175331
  · exact B1175335
  · exact B1175339
  · exact B1175343
  · exact B1175347
  · exact B1175351
  · exact B1175355
  · exact B1175359
  · exact B1175363
  · exact B1175367
  · exact B1175371
  · exact B1175375
  · exact B1175379
  · exact B1175383
  · exact B1175387
  · exact B1175391
  · exact B1175395
  · exact B1175399
  · exact B1175403
  · exact B1175407
  · exact B1175411
  · exact B1175415
  · exact B1175419
  · exact B1175423
  · exact B1175427
  · exact B1175431
  · exact B1175435
  · exact B1175439
  · exact B1175443
  · exact B1175447
  · exact B1175451
  · exact B1175455
  · exact B1175459
  · exact B1175463
  · exact B1175467
  · exact B1175471
  · exact B1175475
  · exact B1175479
  · exact B1175483
  · exact B1175487
  · exact B1175491
  · exact B1175495
  · exact B1175499
  · exact B1175503
  · exact B1175507
  · exact B1175511
  · exact B1175515
  · exact B1175519
  · exact B1175523
  · exact B1175527
  · exact B1175531
  · exact B1175535
  · exact B1175539
  · exact B1175543
  · exact B1175547
  · exact B1175551
  · exact B1175555
  · exact B1175559
  · exact B1175563
  · exact B1175567
  · exact B1175571
  · exact B1175575
  · exact B1175579
  · exact B1175583
  · exact B1175587
  · exact B1175591
  · exact B1175595
  · exact B1175599
  · exact B1175603
  · exact B1175607
  · exact B1175611
  · exact B1175615
  · exact B1175619
  · exact B1175623
  · exact B1175627
  · exact B1175631
  · exact B1175635
  · exact B1175639
  · exact B1175643
  · exact B1175647
  · exact B1175651
  · exact B1175655
  · exact B1175659
  · exact B1175663
  · exact B1175667
  · exact B1175671
  · exact B1175675
  · exact B1175679
  · exact B1175683
  · exact B1175687
  · exact B1175691
  · exact B1175695
  · exact B1175699
  · exact B1175703
  · exact B1175707
  · exact B1175711
  · exact B1175715
  · exact B1175719
  · exact B1175723
  · exact B1175727
  · exact B1175731
  · exact B1175735
  · exact B1175739
  · exact B1175743
  · exact B1175747
  · exact B1175751
  · exact B1175755
  · exact B1175759
  · exact B1175763
  · exact B1175767
  · exact B1175771
  · exact B1175775
  · exact B1175779
  · exact B1175783
  · exact B1175787
  · exact B1175791
  · exact B1175795
  · exact B1175799
  · exact B1175803
  · exact B1175807
  · exact B1175811
  · exact B1175815
  · exact B1175819
  · exact B1175823
  · exact B1175827
  · exact B1175831
  · exact B1175835
  · exact B1175839
  · exact B1175843
  · exact B1175847
  · exact B1175851
  · exact B1175855
  · exact B1175859
  · exact B1175863
  · exact B1175867
  · exact B1175871
  · exact B1175875
  · exact B1175879
  · exact B1175883
  · exact B1175887
  · exact B1175891
  · exact B1175895
  · exact B1175899
  · exact B1175903
  · exact B1175907
  · exact B1175911
  · exact B1175915
  · exact B1175919
  · exact B1175923
  · exact B1175927
  · exact B1175931
  · exact B1175935
  · exact B1175939
  · exact B1175943
  · exact B1175947
  · exact B1175951
  · exact B1175955
  · exact B1175959
  · exact B1175963
  · exact B1175967
  · exact B1175971
  · exact B1175975
  · exact B1175979
  · exact B1175983
  · exact B1175987
  · exact B1175991
  · exact B1175995
  · exact B1175999
  · exact B1176003
  · exact B1176007
  · exact B1176011
  · exact B1176015
  · exact B1176019
  · exact B1176023
  · exact B1176027
  · exact B1176031
  · exact B1176035
  · exact B1176039
  · exact B1176043
  · exact B1176047
  · exact B1176051
  · exact B1176055
  · exact B1176059
  · exact B1176063
  · exact B1176067
  · exact B1176071
  · exact B1176075
  · exact B1176079
  · exact B1176083
  · exact B1176087
  · exact B1176091
  · exact B1176095
  · exact B1176099
  · exact B1176103
  · exact B1176107
  · exact B1176111
  · exact B1176115
  · exact B1176119
  · exact B1176123
  · exact B1176127
  · exact B1176131
  · exact B1176135
  · exact B1176139
  · exact B1176143
  · exact B1176147
  · exact B1176151
  · exact B1176155
  · exact B1176159
  · exact B1176163
  · exact B1176167
  · exact B1176171
  · exact B1176175
  · exact B1176179
  · exact B1176183
  · exact B1176187
  · exact B1176191
  · exact B1176195
  · exact B1176199
  · exact B1176203
  · exact B1176207
  · exact B1176211
  · exact B1176215
  · exact B1176219
  · exact B1176223
  · exact B1176227
  · exact B1176231
  · exact B1176235
  · exact B1176239
  · exact B1176243
  · exact B1176247
  · exact B1176251
  · exact B1176255
  · exact B1176259
  · exact B1176263
  · exact B1176267
  · exact B1176271
  · exact B1176275
  · exact B1176279
  · exact B1176283
  · exact B1176287
  · exact B1176291
  · exact B1176295
  · exact B1176299
  · exact B1176303
  · exact B1176307
  · exact B1176311
  · exact B1176315
  · exact B1176319
  · exact B1176323
  · exact B1176327
  · exact B1176331
  · exact B1176335
  · exact B1176339
  · exact B1176343
  · exact B1176347
  · exact B1176351
  · exact B1176355
  · exact B1176359
  · exact B1176363
  · exact B1176367
  · exact B1176371
  · exact B1176375
  · exact B1176379
  · exact B1176383
  · exact B1176387
  · exact B1176391
  · exact B1176395
  · exact B1176399
  · exact B1176403

theorem solution (m : ℕ) (hlo : 1174404 ≤ m) (hhi : m ≤ 1176404) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 293601 ≤ j := by omega
    have hj2 : j ≤ 294100 := by omega
    have hb : Blo 1174404 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
