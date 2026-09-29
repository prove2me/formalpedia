-- Prove2me | solution 1 for syracuse_descends_range_1623010_1624510
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:13:33.110392+00:00
-- url     : https://prove2.me/submissions/9114b470-d606-4109-80ef-ff64d543f03a

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


theorem B3702797 : Blo 1623010 3702797 := bbase (se 3 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 3702797 = 1388549) (by norm_num)
theorem B1826833 : Blo 1623010 1826833 := bbase (se 2 (by rfl) ⟨685062, by rfl⟩ : syracuseStep 1826833 = 1370125) (by norm_num)
theorem B1826869 : Blo 1623010 1826869 := bbase (se 5 (by rfl) ⟨85634, by rfl⟩ : syracuseStep 1826869 = 171269) (by norm_num)
theorem B3653693 : Blo 1623010 3653693 := bbase (se 3 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 3653693 = 1370135) (by norm_num)
theorem B2195525 : Blo 1623010 2195525 := bbase (se 4 (by rfl) ⟨205830, by rfl⟩ : syracuseStep 2195525 = 411661) (by norm_num)
theorem B1826905 : Blo 1623010 1826905 := bbase (se 2 (by rfl) ⟨685089, by rfl⟩ : syracuseStep 1826905 = 1370179) (by norm_num)
theorem B1826941 : Blo 1623010 1826941 := bbase (se 3 (by rfl) ⟨342551, by rfl⟩ : syracuseStep 1826941 = 685103) (by norm_num)
theorem B3653765 : Blo 1623010 3653765 := bbase (se 4 (by rfl) ⟨342540, by rfl⟩ : syracuseStep 3653765 = 685081) (by norm_num)
theorem B8896661 : Blo 1623010 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B1826977 : Blo 1623010 1826977 := bbase (se 2 (by rfl) ⟨685116, by rfl⟩ : syracuseStep 1826977 = 1370233) (by norm_num)
theorem B1827013 : Blo 1623010 1827013 := bbase (se 4 (by rfl) ⟨171282, by rfl⟩ : syracuseStep 1827013 = 342565) (by norm_num)
theorem B3653837 : Blo 1623010 3653837 := bbase (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) (by norm_num)
theorem B1827049 : Blo 1623010 1827049 := bbase (se 2 (by rfl) ⟨685143, by rfl⟩ : syracuseStep 1827049 = 1370287) (by norm_num)
theorem B1827085 : Blo 1623010 1827085 := bbase (se 3 (by rfl) ⟨342578, by rfl⟩ : syracuseStep 1827085 = 685157) (by norm_num)
theorem B3653909 : Blo 1623010 3653909 := bbase (se 6 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 3653909 = 171277) (by norm_num)
theorem B1950001 : Blo 1623010 1950001 := bbase (se 2 (by rfl) ⟨731250, by rfl⟩ : syracuseStep 1950001 = 1462501) (by norm_num)
theorem B1827121 : Blo 1623010 1827121 := bbase (se 2 (by rfl) ⟨685170, by rfl⟩ : syracuseStep 1827121 = 1370341) (by norm_num)
theorem B1827157 : Blo 1623010 1827157 := bbase (se 10 (by rfl) ⟨2676, by rfl⟩ : syracuseStep 1827157 = 5353) (by norm_num)
theorem B3653981 : Blo 1623010 3653981 := bbase (se 3 (by rfl) ⟨685121, by rfl⟩ : syracuseStep 3653981 = 1370243) (by norm_num)
theorem B12329333 : Blo 1623010 12329333 := bbase (se 5 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 12329333 = 1155875) (by norm_num)
theorem B1827193 : Blo 1623010 1827193 := bbase (se 2 (by rfl) ⟨685197, by rfl⟩ : syracuseStep 1827193 = 1370395) (by norm_num)
theorem B5480837 : Blo 1623010 5480837 := bbase (se 4 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 5480837 = 1027657) (by norm_num)
theorem B1827229 : Blo 1623010 1827229 := bbase (se 3 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 1827229 = 685211) (by norm_num)
theorem B3654053 : Blo 1623010 3654053 := bbase (se 4 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 3654053 = 685135) (by norm_num)
theorem B1827265 : Blo 1623010 1827265 := bbase (se 2 (by rfl) ⟨685224, by rfl⟩ : syracuseStep 1827265 = 1370449) (by norm_num)
theorem B1827301 : Blo 1623010 1827301 := bbase (se 4 (by rfl) ⟨171309, by rfl⟩ : syracuseStep 1827301 = 342619) (by norm_num)
theorem B3654125 : Blo 1623010 3654125 := bbase (se 3 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 3654125 = 1370297) (by norm_num)
theorem B1827337 : Blo 1623010 1827337 := bbase (se 2 (by rfl) ⟨685251, by rfl⟩ : syracuseStep 1827337 = 1370503) (by norm_num)
theorem B3899917 : Blo 1623010 3899917 := bbase (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) (by norm_num)
theorem B8217125 : Blo 1623010 8217125 := bbase (se 4 (by rfl) ⟨770355, by rfl⟩ : syracuseStep 8217125 = 1540711) (by norm_num)
theorem B1827373 : Blo 1623010 1827373 := bbase (se 3 (by rfl) ⟨342632, by rfl⟩ : syracuseStep 1827373 = 685265) (by norm_num)
theorem B3654197 : Blo 1623010 3654197 := bbase (se 5 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 3654197 = 342581) (by norm_num)
theorem B1827409 : Blo 1623010 1827409 := bbase (se 2 (by rfl) ⟨685278, by rfl⟩ : syracuseStep 1827409 = 1370557) (by norm_num)
theorem B1827445 : Blo 1623010 1827445 := bbase (se 5 (by rfl) ⟨85661, by rfl⟩ : syracuseStep 1827445 = 171323) (by norm_num)
theorem B3654269 : Blo 1623010 3654269 := bbase (se 3 (by rfl) ⟨685175, by rfl⟩ : syracuseStep 3654269 = 1370351) (by norm_num)
theorem B1827481 : Blo 1623010 1827481 := bbase (se 2 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 1827481 = 1370611) (by norm_num)
theorem B9249461 : Blo 1623010 9249461 := bbase (se 5 (by rfl) ⟨433568, by rfl⟩ : syracuseStep 9249461 = 867137) (by norm_num)
theorem B1827517 : Blo 1623010 1827517 := bbase (se 3 (by rfl) ⟨342659, by rfl⟩ : syracuseStep 1827517 = 685319) (by norm_num)
theorem B2966213 : Blo 1623010 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B3654341 : Blo 1623010 3654341 := bbase (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) (by norm_num)
theorem B3089117 : Blo 1623010 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B1827553 : Blo 1623010 1827553 := bbase (se 2 (by rfl) ⟨685332, by rfl⟩ : syracuseStep 1827553 = 1370665) (by norm_num)
theorem B2310925 : Blo 1623010 2310925 := bbase (se 3 (by rfl) ⟨433298, by rfl⟩ : syracuseStep 2310925 = 866597) (by norm_num)
theorem B3654413 : Blo 1623010 3654413 := bbase (se 3 (by rfl) ⟨685202, by rfl⟩ : syracuseStep 3654413 = 1370405) (by norm_num)
theorem B5481269 : Blo 1623010 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B3654485 : Blo 1623010 3654485 := bbase (se 9 (by rfl) ⟨10706, by rfl⟩ : syracuseStep 3654485 = 21413) (by norm_num)
theorem B3900253 : Blo 1623010 3900253 := bbase (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) (by norm_num)
theorem B2311021 : Blo 1623010 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B3654557 : Blo 1623010 3654557 := bbase (se 3 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 3654557 = 1370459) (by norm_num)
theorem B3654629 : Blo 1623010 3654629 := bbase (se 4 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 3654629 = 685243) (by norm_num)
theorem B3654701 : Blo 1623010 3654701 := bbase (se 3 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 3654701 = 1370513) (by norm_num)
theorem B3654773 : Blo 1623010 3654773 := bbase (se 5 (by rfl) ⟨171317, by rfl⟩ : syracuseStep 3654773 = 342635) (by norm_num)
theorem B1950905 : Blo 1623010 1950905 := bbase (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) (by norm_num)
theorem B3654845 : Blo 1623010 3654845 := bbase (se 3 (by rfl) ⟨685283, by rfl⟩ : syracuseStep 3654845 = 1370567) (by norm_num)
theorem B5481701 : Blo 1623010 5481701 := bbase (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) (by norm_num)
theorem B3654917 : Blo 1623010 3654917 := bbase (se 4 (by rfl) ⟨342648, by rfl⟩ : syracuseStep 3654917 = 685297) (by norm_num)
theorem B3654989 : Blo 1623010 3654989 := bbase (se 3 (by rfl) ⟨685310, by rfl⟩ : syracuseStep 3654989 = 1370621) (by norm_num)
theorem B11863381 : Blo 1623010 11863381 := bbase (se 12 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 11863381 = 8689) (by norm_num)
theorem B2311517 : Blo 1623010 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B3655061 : Blo 1623010 3655061 := bbase (se 6 (by rfl) ⟨85665, by rfl⟩ : syracuseStep 3655061 = 171331) (by norm_num)
theorem B1951165 : Blo 1623010 1951165 := bbase (se 3 (by rfl) ⟨365843, by rfl⟩ : syracuseStep 1951165 = 731687) (by norm_num)
theorem B3900869 : Blo 1623010 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B2434517 : Blo 1623010 2434517 := bbase (se 7 (by rfl) ⟨28529, by rfl⟩ : syracuseStep 2434517 = 57059) (by norm_num)
theorem B3655133 : Blo 1623010 3655133 := bbase (se 3 (by rfl) ⟨685337, by rfl⟩ : syracuseStep 3655133 = 1370675) (by norm_num)
theorem B2434541 : Blo 1623010 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B2434565 : Blo 1623010 2434565 := bbase (se 4 (by rfl) ⟨228240, by rfl⟩ : syracuseStep 2434565 = 456481) (by norm_num)
theorem B2434589 : Blo 1623010 2434589 := bbase (se 3 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 2434589 = 912971) (by norm_num)
theorem B2434613 : Blo 1623010 2434613 := bbase (se 5 (by rfl) ⟨114122, by rfl⟩ : syracuseStep 2434613 = 228245) (by norm_num)
theorem B3466805 : Blo 1623010 3466805 := bbase (se 5 (by rfl) ⟨162506, by rfl⟩ : syracuseStep 3466805 = 325013) (by norm_num)
theorem B2434637 : Blo 1623010 2434637 := bbase (se 3 (by rfl) ⟨456494, by rfl⟩ : syracuseStep 2434637 = 912989) (by norm_num)
theorem B5203541 : Blo 1623010 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B2434661 : Blo 1623010 2434661 := bbase (se 4 (by rfl) ⟨228249, by rfl⟩ : syracuseStep 2434661 = 456499) (by norm_num)
theorem B2672237 : Blo 1623010 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B2434685 : Blo 1623010 2434685 := bbase (se 3 (by rfl) ⟨456503, by rfl⟩ : syracuseStep 2434685 = 913007) (by norm_num)
theorem B1951357 : Blo 1623010 1951357 := bbase (se 3 (by rfl) ⟨365879, by rfl⟩ : syracuseStep 1951357 = 731759) (by norm_num)
theorem B2434709 : Blo 1623010 2434709 := bbase (se 6 (by rfl) ⟨57063, by rfl⟩ : syracuseStep 2434709 = 114127) (by norm_num)
theorem B1951381 : Blo 1623010 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B1951385 : Blo 1623010 1951385 := bbase (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) (by norm_num)
theorem B5482133 : Blo 1623010 5482133 := bbase (se 6 (by rfl) ⟨128487, by rfl⟩ : syracuseStep 5482133 = 256975) (by norm_num)
theorem B2434733 : Blo 1623010 2434733 := bbase (se 3 (by rfl) ⟨456512, by rfl⟩ : syracuseStep 2434733 = 913025) (by norm_num)
theorem B3081901 : Blo 1623010 3081901 := bbase (se 3 (by rfl) ⟨577856, by rfl⟩ : syracuseStep 3081901 = 1155713) (by norm_num)
theorem B2434757 : Blo 1623010 2434757 := bbase (se 4 (by rfl) ⟨228258, by rfl⟩ : syracuseStep 2434757 = 456517) (by norm_num)
theorem B2434781 : Blo 1623010 2434781 := bbase (se 3 (by rfl) ⟨456521, by rfl⟩ : syracuseStep 2434781 = 913043) (by norm_num)
theorem B2434805 : Blo 1623010 2434805 := bbase (se 5 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 2434805 = 228263) (by norm_num)
theorem B2434829 : Blo 1623010 2434829 := bbase (se 3 (by rfl) ⟨456530, by rfl⟩ : syracuseStep 2434829 = 913061) (by norm_num)
theorem B2434853 : Blo 1623010 2434853 := bbase (se 4 (by rfl) ⟨228267, by rfl⟩ : syracuseStep 2434853 = 456535) (by norm_num)
theorem B3467045 : Blo 1623010 3467045 := bbase (se 4 (by rfl) ⟨325035, by rfl⟩ : syracuseStep 3467045 = 650071) (by norm_num)
theorem B8218421 : Blo 1623010 8218421 := bbase (se 5 (by rfl) ⟨385238, by rfl⟩ : syracuseStep 8218421 = 770477) (by norm_num)
theorem B2434877 : Blo 1623010 2434877 := bbase (se 3 (by rfl) ⟨456539, by rfl⟩ : syracuseStep 2434877 = 913079) (by norm_num)
theorem B3082045 : Blo 1623010 3082045 := bbase (se 3 (by rfl) ⟨577883, by rfl⟩ : syracuseStep 3082045 = 1155767) (by norm_num)
theorem B2434901 : Blo 1623010 2434901 := bbase (se 9 (by rfl) ⟨7133, by rfl⟩ : syracuseStep 2434901 = 14267) (by norm_num)
theorem B8898389 : Blo 1623010 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B9250645 : Blo 1623010 9250645 := bbase (se 9 (by rfl) ⟨27101, by rfl⟩ : syracuseStep 9250645 = 54203) (by norm_num)
theorem B2434925 : Blo 1623010 2434925 := bbase (se 3 (by rfl) ⟨456548, by rfl⟩ : syracuseStep 2434925 = 913097) (by norm_num)
theorem B3901301 : Blo 1623010 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B13018997 : Blo 1623010 13018997 := bbase (se 5 (by rfl) ⟨610265, by rfl⟩ : syracuseStep 13018997 = 1220531) (by norm_num)
theorem B2434949 : Blo 1623010 2434949 := bbase (se 4 (by rfl) ⟨228276, by rfl⟩ : syracuseStep 2434949 = 456553) (by norm_num)
theorem B2312069 : Blo 1623010 2312069 := bbase (se 4 (by rfl) ⟨216756, by rfl⟩ : syracuseStep 2312069 = 433513) (by norm_num)
theorem B2434973 : Blo 1623010 2434973 := bbase (se 3 (by rfl) ⟨456557, by rfl⟩ : syracuseStep 2434973 = 913115) (by norm_num)
theorem B2434997 : Blo 1623010 2434997 := bbase (se 5 (by rfl) ⟨114140, by rfl⟩ : syracuseStep 2434997 = 228281) (by norm_num)
theorem B2435021 : Blo 1623010 2435021 := bbase (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) (by norm_num)
theorem B6162389 : Blo 1623010 6162389 := bbase (se 7 (by rfl) ⟨72215, by rfl⟩ : syracuseStep 6162389 = 144431) (by norm_num)
theorem B3082205 : Blo 1623010 3082205 := bbase (se 3 (by rfl) ⟨577913, by rfl⟩ : syracuseStep 3082205 = 1155827) (by norm_num)
theorem B2435045 : Blo 1623010 2435045 := bbase (se 4 (by rfl) ⟨228285, by rfl⟩ : syracuseStep 2435045 = 456571) (by norm_num)
theorem B2435069 : Blo 1623010 2435069 := bbase (se 3 (by rfl) ⟨456575, by rfl⟩ : syracuseStep 2435069 = 913151) (by norm_num)
theorem B2435093 : Blo 1623010 2435093 := bbase (se 6 (by rfl) ⟨57072, by rfl⟩ : syracuseStep 2435093 = 114145) (by norm_num)
theorem B2435117 : Blo 1623010 2435117 := bbase (se 3 (by rfl) ⟨456584, by rfl⟩ : syracuseStep 2435117 = 913169) (by norm_num)
theorem B2435141 : Blo 1623010 2435141 := bbase (se 4 (by rfl) ⟨228294, by rfl⟩ : syracuseStep 2435141 = 456589) (by norm_num)
theorem B5482565 : Blo 1623010 5482565 := bbase (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) (by norm_num)
theorem B2435165 : Blo 1623010 2435165 := bbase (se 3 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 2435165 = 913187) (by norm_num)
theorem B3082349 : Blo 1623010 3082349 := bbase (se 3 (by rfl) ⟨577940, by rfl⟩ : syracuseStep 3082349 = 1155881) (by norm_num)
theorem B4622453 : Blo 1623010 4622453 := bbase (se 5 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 4622453 = 433355) (by norm_num)
theorem B2435189 : Blo 1623010 2435189 := bbase (se 5 (by rfl) ⟨114149, by rfl⟩ : syracuseStep 2435189 = 228299) (by norm_num)
theorem B2435213 : Blo 1623010 2435213 := bbase (se 3 (by rfl) ⟨456602, by rfl⟩ : syracuseStep 2435213 = 913205) (by norm_num)
theorem B2435237 : Blo 1623010 2435237 := bbase (se 4 (by rfl) ⟨228303, by rfl⟩ : syracuseStep 2435237 = 456607) (by norm_num)
theorem B2435261 : Blo 1623010 2435261 := bbase (se 3 (by rfl) ⟨456611, by rfl⟩ : syracuseStep 2435261 = 913223) (by norm_num)
theorem B2435285 : Blo 1623010 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B26699989 : Blo 1623010 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B2435309 : Blo 1623010 2435309 := bbase (se 3 (by rfl) ⟨456620, by rfl⟩ : syracuseStep 2435309 = 913241) (by norm_num)
theorem B2435333 : Blo 1623010 2435333 := bbase (se 4 (by rfl) ⟨228312, by rfl⟩ : syracuseStep 2435333 = 456625) (by norm_num)
theorem B2435357 : Blo 1623010 2435357 := bbase (se 3 (by rfl) ⟨456629, by rfl⟩ : syracuseStep 2435357 = 913259) (by norm_num)
theorem B3467549 : Blo 1623010 3467549 := bbase (se 3 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 3467549 = 1300331) (by norm_num)
theorem B3467557 : Blo 1623010 3467557 := bbase (se 4 (by rfl) ⟨325083, by rfl⟩ : syracuseStep 3467557 = 650167) (by norm_num)
theorem B2435381 : Blo 1623010 2435381 := bbase (se 5 (by rfl) ⟨114158, by rfl⟩ : syracuseStep 2435381 = 228317) (by norm_num)
theorem B2468165 : Blo 1623010 2468165 := bbase (se 4 (by rfl) ⟨231390, by rfl⟩ : syracuseStep 2468165 = 462781) (by norm_num)
theorem B2435405 : Blo 1623010 2435405 := bbase (se 3 (by rfl) ⟨456638, by rfl⟩ : syracuseStep 2435405 = 913277) (by norm_num)
theorem B2435429 : Blo 1623010 2435429 := bbase (se 4 (by rfl) ⟨228321, by rfl⟩ : syracuseStep 2435429 = 456643) (by norm_num)
theorem B3123581 : Blo 1623010 3123581 := bbase (se 3 (by rfl) ⟨585671, by rfl⟩ : syracuseStep 3123581 = 1171343) (by norm_num)
theorem B2435453 : Blo 1623010 2435453 := bbase (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) (by norm_num)
theorem B3082637 : Blo 1623010 3082637 := bbase (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) (by norm_num)
theorem B2435477 : Blo 1623010 2435477 := bbase (se 6 (by rfl) ⟨57081, by rfl⟩ : syracuseStep 2435477 = 114163) (by norm_num)
theorem B2435501 : Blo 1623010 2435501 := bbase (se 3 (by rfl) ⟨456656, by rfl⟩ : syracuseStep 2435501 = 913313) (by norm_num)
theorem B2435525 : Blo 1623010 2435525 := bbase (se 4 (by rfl) ⟨228330, by rfl⟩ : syracuseStep 2435525 = 456661) (by norm_num)
theorem B2435549 : Blo 1623010 2435549 := bbase (se 3 (by rfl) ⟨456665, by rfl⟩ : syracuseStep 2435549 = 913331) (by norm_num)
theorem B3901925 : Blo 1623010 3901925 := bbase (se 4 (by rfl) ⟨365805, by rfl⟩ : syracuseStep 3901925 = 731611) (by norm_num)
theorem B2435573 : Blo 1623010 2435573 := bbase (se 5 (by rfl) ⟨114167, by rfl⟩ : syracuseStep 2435573 = 228335) (by norm_num)
theorem B2435597 : Blo 1623010 2435597 := bbase (se 3 (by rfl) ⟨456674, by rfl⟩ : syracuseStep 2435597 = 913349) (by norm_num)
theorem B2435621 : Blo 1623010 2435621 := bbase (se 4 (by rfl) ⟨228339, by rfl⟩ : syracuseStep 2435621 = 456679) (by norm_num)
theorem B3082789 : Blo 1623010 3082789 := bbase (se 4 (by rfl) ⟨289011, by rfl⟩ : syracuseStep 3082789 = 578023) (by norm_num)
theorem B2435645 : Blo 1623010 2435645 := bbase (se 3 (by rfl) ⟨456683, by rfl⟩ : syracuseStep 2435645 = 913367) (by norm_num)
theorem B2435669 : Blo 1623010 2435669 := bbase (se 8 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 2435669 = 28543) (by norm_num)
theorem B10693205 : Blo 1623010 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B2435693 : Blo 1623010 2435693 := bbase (se 3 (by rfl) ⟨456692, by rfl⟩ : syracuseStep 2435693 = 913385) (by norm_num)
theorem B2312821 : Blo 1623010 2312821 := bbase (se 5 (by rfl) ⟨108413, by rfl⟩ : syracuseStep 2312821 = 216827) (by norm_num)
theorem B2435717 : Blo 1623010 2435717 := bbase (se 4 (by rfl) ⟨228348, by rfl⟩ : syracuseStep 2435717 = 456697) (by norm_num)
theorem B2435741 : Blo 1623010 2435741 := bbase (se 3 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 2435741 = 913403) (by norm_num)
theorem B2435765 : Blo 1623010 2435765 := bbase (se 5 (by rfl) ⟨114176, by rfl⟩ : syracuseStep 2435765 = 228353) (by norm_num)
theorem B2738893 : Blo 1623010 2738893 := bbase (se 3 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 2738893 = 1027085) (by norm_num)
theorem B2435789 : Blo 1623010 2435789 := bbase (se 3 (by rfl) ⟨456710, by rfl⟩ : syracuseStep 2435789 = 913421) (by norm_num)
theorem B2435813 : Blo 1623010 2435813 := bbase (se 4 (by rfl) ⟨228357, by rfl⟩ : syracuseStep 2435813 = 456715) (by norm_num)
theorem B2435837 : Blo 1623010 2435837 := bbase (se 3 (by rfl) ⟨456719, by rfl⟩ : syracuseStep 2435837 = 913439) (by norm_num)
theorem B6933269 : Blo 1623010 6933269 := bbase (se 6 (by rfl) ⟨162498, by rfl⟩ : syracuseStep 6933269 = 324997) (by norm_num)
theorem B2435861 : Blo 1623010 2435861 := bbase (se 6 (by rfl) ⟨57090, by rfl⟩ : syracuseStep 2435861 = 114181) (by norm_num)
theorem B2738981 : Blo 1623010 2738981 := bbase (se 4 (by rfl) ⟨256779, by rfl⟩ : syracuseStep 2738981 = 513559) (by norm_num)
theorem B2435885 : Blo 1623010 2435885 := bbase (se 3 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 2435885 = 913457) (by norm_num)
theorem B1690417 : Blo 1623010 1690417 := bbase (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) (by norm_num)
theorem B2435909 : Blo 1623010 2435909 := bbase (se 4 (by rfl) ⟨228366, by rfl⟩ : syracuseStep 2435909 = 456733) (by norm_num)
theorem B3083093 : Blo 1623010 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B2435933 : Blo 1623010 2435933 := bbase (se 3 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 2435933 = 913475) (by norm_num)
theorem B2435957 : Blo 1623010 2435957 := bbase (se 5 (by rfl) ⟨114185, by rfl⟩ : syracuseStep 2435957 = 228371) (by norm_num)
theorem B2435981 : Blo 1623010 2435981 := bbase (se 3 (by rfl) ⟨456746, by rfl⟩ : syracuseStep 2435981 = 913493) (by norm_num)
theorem B2739109 : Blo 1623010 2739109 := bbase (se 4 (by rfl) ⟨256791, by rfl⟩ : syracuseStep 2739109 = 513583) (by norm_num)
theorem B2436005 : Blo 1623010 2436005 := bbase (se 4 (by rfl) ⟨228375, by rfl⟩ : syracuseStep 2436005 = 456751) (by norm_num)
theorem B2436029 : Blo 1623010 2436029 := bbase (se 3 (by rfl) ⟨456755, by rfl⟩ : syracuseStep 2436029 = 913511) (by norm_num)
theorem B2436053 : Blo 1623010 2436053 := bbase (se 7 (by rfl) ⟨28547, by rfl⟩ : syracuseStep 2436053 = 57095) (by norm_num)
theorem B2436077 : Blo 1623010 2436077 := bbase (se 3 (by rfl) ⟨456764, by rfl⟩ : syracuseStep 2436077 = 913529) (by norm_num)
theorem B2739197 : Blo 1623010 2739197 := bbase (se 3 (by rfl) ⟨513599, by rfl⟩ : syracuseStep 2739197 = 1027199) (by norm_num)
theorem B6933509 : Blo 1623010 6933509 := bbase (se 4 (by rfl) ⟨650016, by rfl⟩ : syracuseStep 6933509 = 1300033) (by norm_num)
theorem B2436101 : Blo 1623010 2436101 := bbase (se 4 (by rfl) ⟨228384, by rfl⟩ : syracuseStep 2436101 = 456769) (by norm_num)
theorem B2436125 : Blo 1623010 2436125 := bbase (se 3 (by rfl) ⟨456773, by rfl⟩ : syracuseStep 2436125 = 913547) (by norm_num)
theorem B2436149 : Blo 1623010 2436149 := bbase (se 5 (by rfl) ⟨114194, by rfl⟩ : syracuseStep 2436149 = 228389) (by norm_num)
theorem B8219717 : Blo 1623010 8219717 := bbase (se 4 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 8219717 = 1541197) (by norm_num)
theorem B2436173 : Blo 1623010 2436173 := bbase (se 3 (by rfl) ⟨456782, by rfl⟩ : syracuseStep 2436173 = 913565) (by norm_num)
theorem B5270629 : Blo 1623010 5270629 := bbase (se 4 (by rfl) ⟨494121, by rfl⟩ : syracuseStep 5270629 = 988243) (by norm_num)
theorem B2436197 : Blo 1623010 2436197 := bbase (se 4 (by rfl) ⟨228393, by rfl⟩ : syracuseStep 2436197 = 456787) (by norm_num)
theorem B6163573 : Blo 1623010 6163573 := bbase (se 5 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 6163573 = 577835) (by norm_num)
theorem B2739325 : Blo 1623010 2739325 := bbase (se 3 (by rfl) ⟨513623, by rfl⟩ : syracuseStep 2739325 = 1027247) (by norm_num)
theorem B2436221 : Blo 1623010 2436221 := bbase (se 3 (by rfl) ⟨456791, by rfl⟩ : syracuseStep 2436221 = 913583) (by norm_num)
theorem B2436245 : Blo 1623010 2436245 := bbase (se 6 (by rfl) ⟨57099, by rfl⟩ : syracuseStep 2436245 = 114199) (by norm_num)
theorem B2436269 : Blo 1623010 2436269 := bbase (se 3 (by rfl) ⟨456800, by rfl⟩ : syracuseStep 2436269 = 913601) (by norm_num)
theorem B2436293 : Blo 1623010 2436293 := bbase (se 4 (by rfl) ⟨228402, by rfl⟩ : syracuseStep 2436293 = 456805) (by norm_num)
theorem B2739413 : Blo 1623010 2739413 := bbase (se 7 (by rfl) ⟨32102, by rfl⟩ : syracuseStep 2739413 = 64205) (by norm_num)
theorem B2436317 : Blo 1623010 2436317 := bbase (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) (by norm_num)
theorem B5270773 : Blo 1623010 5270773 := bbase (se 5 (by rfl) ⟨247067, by rfl⟩ : syracuseStep 5270773 = 494135) (by norm_num)
theorem B2436341 : Blo 1623010 2436341 := bbase (se 5 (by rfl) ⟨114203, by rfl⟩ : syracuseStep 2436341 = 228407) (by norm_num)
theorem B2436365 : Blo 1623010 2436365 := bbase (se 3 (by rfl) ⟨456818, by rfl⟩ : syracuseStep 2436365 = 913637) (by norm_num)
theorem B4623637 : Blo 1623010 4623637 := bbase (se 6 (by rfl) ⟨108366, by rfl⟩ : syracuseStep 4623637 = 216733) (by norm_num)
theorem B2436389 : Blo 1623010 2436389 := bbase (se 4 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 2436389 = 456823) (by norm_num)
theorem B2436413 : Blo 1623010 2436413 := bbase (se 3 (by rfl) ⟨456827, by rfl⟩ : syracuseStep 2436413 = 913655) (by norm_num)
theorem B2739541 : Blo 1623010 2739541 := bbase (se 11 (by rfl) ⟨2006, by rfl⟩ : syracuseStep 2739541 = 4013) (by norm_num)
theorem B2436437 : Blo 1623010 2436437 := bbase (se 11 (by rfl) ⟨1784, by rfl⟩ : syracuseStep 2436437 = 3569) (by norm_num)
theorem B2436461 : Blo 1623010 2436461 := bbase (se 3 (by rfl) ⟨456836, by rfl⟩ : syracuseStep 2436461 = 913673) (by norm_num)
theorem B2600309 : Blo 1623010 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B2436485 : Blo 1623010 2436485 := bbase (se 4 (by rfl) ⟨228420, by rfl⟩ : syracuseStep 2436485 = 456841) (by norm_num)
theorem B3468685 : Blo 1623010 3468685 := bbase (se 3 (by rfl) ⟨650378, by rfl⟩ : syracuseStep 3468685 = 1300757) (by norm_num)
theorem B2436509 : Blo 1623010 2436509 := bbase (se 3 (by rfl) ⟨456845, by rfl⟩ : syracuseStep 2436509 = 913691) (by norm_num)
theorem B6163877 : Blo 1623010 6163877 := bbase (se 4 (by rfl) ⟨577863, by rfl⟩ : syracuseStep 6163877 = 1155727) (by norm_num)
theorem B2739629 : Blo 1623010 2739629 := bbase (se 3 (by rfl) ⟨513680, by rfl⟩ : syracuseStep 2739629 = 1027361) (by norm_num)
theorem B4623797 : Blo 1623010 4623797 := bbase (se 5 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 4623797 = 433481) (by norm_num)
theorem B2436533 : Blo 1623010 2436533 := bbase (se 5 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 2436533 = 228425) (by norm_num)
theorem B2436557 : Blo 1623010 2436557 := bbase (se 3 (by rfl) ⟨456854, by rfl⟩ : syracuseStep 2436557 = 913709) (by norm_num)
theorem B5852645 : Blo 1623010 5852645 := bbase (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) (by norm_num)
theorem B2436581 : Blo 1623010 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B2436605 : Blo 1623010 2436605 := bbase (se 3 (by rfl) ⟨456863, by rfl⟩ : syracuseStep 2436605 = 913727) (by norm_num)
theorem B3124757 : Blo 1623010 3124757 := bbase (se 6 (by rfl) ⟨73236, by rfl⟩ : syracuseStep 3124757 = 146473) (by norm_num)
theorem B2436629 : Blo 1623010 2436629 := bbase (se 6 (by rfl) ⟨57108, by rfl⟩ : syracuseStep 2436629 = 114217) (by norm_num)
theorem B2739757 : Blo 1623010 2739757 := bbase (se 3 (by rfl) ⟨513704, by rfl⟩ : syracuseStep 2739757 = 1027409) (by norm_num)
theorem B2436653 : Blo 1623010 2436653 := bbase (se 3 (by rfl) ⟨456872, by rfl⟩ : syracuseStep 2436653 = 913745) (by norm_num)
theorem B3083845 : Blo 1623010 3083845 := bbase (se 4 (by rfl) ⟨289110, by rfl⟩ : syracuseStep 3083845 = 578221) (by norm_num)
theorem B2436677 : Blo 1623010 2436677 := bbase (se 4 (by rfl) ⟨228438, by rfl⟩ : syracuseStep 2436677 = 456877) (by norm_num)
theorem B2436701 : Blo 1623010 2436701 := bbase (se 3 (by rfl) ⟨456881, by rfl⟩ : syracuseStep 2436701 = 913763) (by norm_num)
theorem B2436725 : Blo 1623010 2436725 := bbase (se 5 (by rfl) ⟨114221, by rfl⟩ : syracuseStep 2436725 = 228443) (by norm_num)
theorem B2739845 : Blo 1623010 2739845 := bbase (se 4 (by rfl) ⟨256860, by rfl⟩ : syracuseStep 2739845 = 513721) (by norm_num)
theorem B2436749 : Blo 1623010 2436749 := bbase (se 3 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 2436749 = 913781) (by norm_num)
theorem B4624037 : Blo 1623010 4624037 := bbase (se 4 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 4624037 = 867007) (by norm_num)
theorem B3083989 : Blo 1623010 3083989 := bbase (se 7 (by rfl) ⟨36140, by rfl⟩ : syracuseStep 3083989 = 72281) (by norm_num)
theorem B2739973 : Blo 1623010 2739973 := bbase (se 4 (by rfl) ⟨256872, by rfl⟩ : syracuseStep 2739973 = 513745) (by norm_num)
theorem B3469061 : Blo 1623010 3469061 := bbase (se 4 (by rfl) ⟨325224, by rfl⟩ : syracuseStep 3469061 = 650449) (by norm_num)
theorem B2600765 : Blo 1623010 2600765 := bbase (se 3 (by rfl) ⟨487643, by rfl⟩ : syracuseStep 2600765 = 975287) (by norm_num)
theorem B2740061 : Blo 1623010 2740061 := bbase (se 3 (by rfl) ⟨513761, by rfl⟩ : syracuseStep 2740061 = 1027523) (by norm_num)
theorem B4624229 : Blo 1623010 4624229 := bbase (se 4 (by rfl) ⟨433521, by rfl⟩ : syracuseStep 4624229 = 867043) (by norm_num)
theorem B10407797 : Blo 1623010 10407797 := bbase (se 5 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 10407797 = 975731) (by norm_num)
theorem B2740189 : Blo 1623010 2740189 := bbase (se 3 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 2740189 = 1027571) (by norm_num)
theorem B21082133 : Blo 1623010 21082133 := bbase (se 6 (by rfl) ⟨494112, by rfl⟩ : syracuseStep 21082133 = 988225) (by norm_num)
theorem B6582293 : Blo 1623010 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B2740277 : Blo 1623010 2740277 := bbase (se 5 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 2740277 = 256901) (by norm_num)
theorem B4108421 : Blo 1623010 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2740405 : Blo 1623010 2740405 := bbase (se 5 (by rfl) ⟨128456, by rfl⟩ : syracuseStep 2740405 = 256913) (by norm_num)
theorem B2740493 : Blo 1623010 2740493 := bbase (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) (by norm_num)
theorem B8335685 : Blo 1623010 8335685 := bbase (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) (by norm_num)
theorem B8221013 : Blo 1623010 8221013 := bbase (se 10 (by rfl) ⟨12042, by rfl⟩ : syracuseStep 8221013 = 24085) (by norm_num)
theorem B2740621 : Blo 1623010 2740621 := bbase (se 3 (by rfl) ⟨513866, by rfl⟩ : syracuseStep 2740621 = 1027733) (by norm_num)
theorem B5853637 : Blo 1623010 5853637 := bbase (se 4 (by rfl) ⟨548778, by rfl⟩ : syracuseStep 5853637 = 1097557) (by norm_num)
theorem B4108765 : Blo 1623010 4108765 := bbase (se 3 (by rfl) ⟨770393, by rfl⟩ : syracuseStep 4108765 = 1540787) (by norm_num)
theorem B2740709 : Blo 1623010 2740709 := bbase (se 4 (by rfl) ⟨256941, by rfl⟩ : syracuseStep 2740709 = 513883) (by norm_num)
theorem B12497429 : Blo 1623010 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B4108877 : Blo 1623010 4108877 := bbase (se 3 (by rfl) ⟨770414, by rfl⟩ : syracuseStep 4108877 = 1540829) (by norm_num)
theorem B2740837 : Blo 1623010 2740837 := bbase (se 4 (by rfl) ⟨256953, by rfl⟩ : syracuseStep 2740837 = 513907) (by norm_num)
theorem B13873781 : Blo 1623010 13873781 := bbase (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) (by norm_num)
theorem B1733249 : Blo 1623010 1733249 := bbase (se 2 (by rfl) ⟨649968, by rfl⟩ : syracuseStep 1733249 = 1299937) (by norm_num)
theorem B2740925 : Blo 1623010 2740925 := bbase (se 3 (by rfl) ⟨513923, by rfl⟩ : syracuseStep 2740925 = 1027847) (by norm_num)
theorem B1757953 : Blo 1623010 1757953 := bbase (se 2 (by rfl) ⟨659232, by rfl⟩ : syracuseStep 1757953 = 1318465) (by norm_num)
theorem B4109069 : Blo 1623010 4109069 := bbase (se 3 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 4109069 = 1540901) (by norm_num)
theorem B1733437 : Blo 1623010 1733437 := bbase (se 3 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 1733437 = 650039) (by norm_num)
theorem B2741053 : Blo 1623010 2741053 := bbase (se 3 (by rfl) ⟨513947, by rfl⟩ : syracuseStep 2741053 = 1027895) (by norm_num)
theorem B4625221 : Blo 1623010 4625221 := bbase (se 4 (by rfl) ⟨433614, by rfl⟩ : syracuseStep 4625221 = 867229) (by norm_num)
theorem B3953485 : Blo 1623010 3953485 := bbase (se 3 (by rfl) ⟨741278, by rfl⟩ : syracuseStep 3953485 = 1482557) (by norm_num)
theorem B47469397 : Blo 1623010 47469397 := bbase (se 9 (by rfl) ⟨139070, by rfl⟩ : syracuseStep 47469397 = 278141) (by norm_num)
theorem B2741141 : Blo 1623010 2741141 := bbase (se 6 (by rfl) ⟨64245, by rfl⟩ : syracuseStep 2741141 = 128491) (by norm_num)
theorem B2225053 : Blo 1623010 2225053 := bbase (se 3 (by rfl) ⟨417197, by rfl⟩ : syracuseStep 2225053 = 834395) (by norm_num)
theorem B14062517 : Blo 1623010 14062517 := bbase (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) (by norm_num)
theorem B2741269 : Blo 1623010 2741269 := bbase (se 6 (by rfl) ⟨64248, by rfl⟩ : syracuseStep 2741269 = 128497) (by norm_num)
theorem B13169749 : Blo 1623010 13169749 := bbase (se 8 (by rfl) ⟨77166, by rfl⟩ : syracuseStep 13169749 = 154333) (by norm_num)
theorem B4109413 : Blo 1623010 4109413 := bbase (se 4 (by rfl) ⟨385257, by rfl⟩ : syracuseStep 4109413 = 770515) (by norm_num)
theorem B2741357 : Blo 1623010 2741357 := bbase (se 3 (by rfl) ⟨514004, by rfl⟩ : syracuseStep 2741357 = 1028009) (by norm_num)
theorem B4109525 : Blo 1623010 4109525 := bbase (se 7 (by rfl) ⟨48158, by rfl⟩ : syracuseStep 4109525 = 96317) (by norm_num)
theorem B6935797 : Blo 1623010 6935797 := bbase (se 5 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 6935797 = 650231) (by norm_num)
theorem B25335125 : Blo 1623010 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B4109717 : Blo 1623010 4109717 := bbase (se 6 (by rfl) ⟨96321, by rfl⟩ : syracuseStep 4109717 = 192643) (by norm_num)
theorem B5477813 : Blo 1623010 5477813 := bbase (se 5 (by rfl) ⟨256772, by rfl⟩ : syracuseStep 5477813 = 513545) (by norm_num)
theorem B6165989 : Blo 1623010 6165989 := bbase (se 4 (by rfl) ⟨578061, by rfl⟩ : syracuseStep 6165989 = 1156123) (by norm_num)
theorem B8222309 : Blo 1623010 8222309 := bbase (se 4 (by rfl) ⟨770841, by rfl⟩ : syracuseStep 8222309 = 1541683) (by norm_num)
theorem B1734257 : Blo 1623010 1734257 := bbase (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) (by norm_num)
theorem B10401493 : Blo 1623010 10401493 := bbase (se 7 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 10401493 = 243785) (by norm_num)
theorem B4110061 : Blo 1623010 4110061 := bbase (se 3 (by rfl) ⟨770636, by rfl⟩ : syracuseStep 4110061 = 1541273) (by norm_num)
theorem B6166277 : Blo 1623010 6166277 := bbase (se 4 (by rfl) ⟨578088, by rfl⟩ : syracuseStep 6166277 = 1156177) (by norm_num)
theorem B4110173 : Blo 1623010 4110173 := bbase (se 3 (by rfl) ⟨770657, by rfl⟩ : syracuseStep 4110173 = 1541315) (by norm_num)
theorem B5478245 : Blo 1623010 5478245 := bbase (se 4 (by rfl) ⟨513585, by rfl⟩ : syracuseStep 5478245 = 1027171) (by norm_num)
theorem B11704277 : Blo 1623010 11704277 := bbase (se 7 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 11704277 = 274319) (by norm_num)
theorem B4110365 : Blo 1623010 4110365 := bbase (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) (by norm_num)
theorem B1734701 : Blo 1623010 1734701 := bbase (se 3 (by rfl) ⟨325256, by rfl⟩ : syracuseStep 1734701 = 650513) (by norm_num)
theorem B2054261 : Blo 1623010 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B2054317 : Blo 1623010 2054317 := bbase (se 3 (by rfl) ⟨385184, by rfl⟩ : syracuseStep 2054317 = 770369) (by norm_num)
theorem B3651821 : Blo 1623010 3651821 := bbase (se 3 (by rfl) ⟨684716, by rfl⟩ : syracuseStep 3651821 = 1369433) (by norm_num)
theorem B2054413 : Blo 1623010 2054413 := bbase (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) (by norm_num)
theorem B5478677 : Blo 1623010 5478677 := bbase (se 6 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 5478677 = 256813) (by norm_num)
theorem B16668949 : Blo 1623010 16668949 := bbase (se 6 (by rfl) ⟨390678, by rfl⟩ : syracuseStep 16668949 = 781357) (by norm_num)
theorem B3651893 : Blo 1623010 3651893 := bbase (se 5 (by rfl) ⟨171182, by rfl⟩ : syracuseStep 3651893 = 342365) (by norm_num)
theorem B4110709 : Blo 1623010 4110709 := bbase (se 5 (by rfl) ⟨192689, by rfl⟩ : syracuseStep 4110709 = 385379) (by norm_num)
theorem B3651965 : Blo 1623010 3651965 := bbase (se 3 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 3651965 = 1369487) (by norm_num)
theorem B2054585 : Blo 1623010 2054585 := bbase (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) (by norm_num)
theorem B3652037 : Blo 1623010 3652037 := bbase (se 4 (by rfl) ⟨342378, by rfl⟩ : syracuseStep 3652037 = 684757) (by norm_num)
theorem B4110821 : Blo 1623010 4110821 := bbase (se 4 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 4110821 = 770779) (by norm_num)
theorem B2054641 : Blo 1623010 2054641 := bbase (se 2 (by rfl) ⟨770490, by rfl⟩ : syracuseStep 2054641 = 1540981) (by norm_num)
theorem B3652109 : Blo 1623010 3652109 := bbase (se 3 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 3652109 = 1369541) (by norm_num)
theorem B2054737 : Blo 1623010 2054737 := bbase (se 2 (by rfl) ⟨770526, by rfl⟩ : syracuseStep 2054737 = 1541053) (by norm_num)
theorem B3652181 : Blo 1623010 3652181 := bbase (se 8 (by rfl) ⟨21399, by rfl⟩ : syracuseStep 3652181 = 42799) (by norm_num)
theorem B3652253 : Blo 1623010 3652253 := bbase (se 3 (by rfl) ⟨684797, by rfl⟩ : syracuseStep 3652253 = 1369595) (by norm_num)
theorem B4111013 : Blo 1623010 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B5479109 : Blo 1623010 5479109 := bbase (se 4 (by rfl) ⟨513666, by rfl⟩ : syracuseStep 5479109 = 1027333) (by norm_num)
theorem B6937285 : Blo 1623010 6937285 := bbase (se 4 (by rfl) ⟨650370, by rfl⟩ : syracuseStep 6937285 = 1300741) (by norm_num)
theorem B6937301 : Blo 1623010 6937301 := bbase (se 7 (by rfl) ⟨81296, by rfl⟩ : syracuseStep 6937301 = 162593) (by norm_num)
theorem B3652325 : Blo 1623010 3652325 := bbase (se 4 (by rfl) ⟨342405, by rfl⟩ : syracuseStep 3652325 = 684811) (by norm_num)
theorem B3291877 : Blo 1623010 3291877 := bbase (se 4 (by rfl) ⟨308613, by rfl⟩ : syracuseStep 3291877 = 617227) (by norm_num)
theorem B2054909 : Blo 1623010 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B5929733 : Blo 1623010 5929733 := bbase (se 4 (by rfl) ⟨555912, by rfl⟩ : syracuseStep 5929733 = 1111825) (by norm_num)
theorem B5200645 : Blo 1623010 5200645 := bbase (se 4 (by rfl) ⟨487560, by rfl⟩ : syracuseStep 5200645 = 975121) (by norm_num)
theorem B3652397 : Blo 1623010 3652397 := bbase (se 3 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 3652397 = 1369649) (by norm_num)
theorem B2054965 : Blo 1623010 2054965 := bbase (se 5 (by rfl) ⟨96326, by rfl⟩ : syracuseStep 2054965 = 192653) (by norm_num)
theorem B3652469 : Blo 1623010 3652469 := bbase (se 5 (by rfl) ⟨171209, by rfl⟩ : syracuseStep 3652469 = 342419) (by norm_num)
theorem B8223605 : Blo 1623010 8223605 := bbase (se 5 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 8223605 = 770963) (by norm_num)
theorem B3701629 : Blo 1623010 3701629 := bbase (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) (by norm_num)
theorem B2055061 : Blo 1623010 2055061 := bbase (se 6 (by rfl) ⟨48165, by rfl⟩ : syracuseStep 2055061 = 96331) (by norm_num)
theorem B6167461 : Blo 1623010 6167461 := bbase (se 4 (by rfl) ⟨578199, by rfl⟩ : syracuseStep 6167461 = 1156399) (by norm_num)
theorem B3652541 : Blo 1623010 3652541 := bbase (se 3 (by rfl) ⟨684851, by rfl⟩ : syracuseStep 3652541 = 1369703) (by norm_num)
theorem B4111357 : Blo 1623010 4111357 := bbase (se 3 (by rfl) ⟨770879, by rfl⟩ : syracuseStep 4111357 = 1541759) (by norm_num)
theorem B3652613 : Blo 1623010 3652613 := bbase (se 4 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 3652613 = 684865) (by norm_num)
theorem B1784849 : Blo 1623010 1784849 := bbase (se 2 (by rfl) ⟨669318, by rfl⟩ : syracuseStep 1784849 = 1338637) (by norm_num)
theorem B2055233 : Blo 1623010 2055233 := bbase (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) (by norm_num)
theorem B3652685 : Blo 1623010 3652685 := bbase (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) (by norm_num)
theorem B3955805 : Blo 1623010 3955805 := bbase (se 3 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 3955805 = 1483427) (by norm_num)
theorem B1825897 : Blo 1623010 1825897 := bbase (se 2 (by rfl) ⟨684711, by rfl⟩ : syracuseStep 1825897 = 1369423) (by norm_num)
theorem B4111469 : Blo 1623010 4111469 := bbase (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) (by norm_num)
theorem B5479541 : Blo 1623010 5479541 := bbase (se 5 (by rfl) ⟨256853, by rfl⟩ : syracuseStep 5479541 = 513707) (by norm_num)
theorem B2055289 : Blo 1623010 2055289 := bbase (se 2 (by rfl) ⟨770733, by rfl⟩ : syracuseStep 2055289 = 1541467) (by norm_num)
theorem B1825933 : Blo 1623010 1825933 := bbase (se 3 (by rfl) ⟨342362, by rfl⟩ : syracuseStep 1825933 = 684725) (by norm_num)
theorem B3652757 : Blo 1623010 3652757 := bbase (se 6 (by rfl) ⟨85611, by rfl⟩ : syracuseStep 3652757 = 171223) (by norm_num)
theorem B1825969 : Blo 1623010 1825969 := bbase (se 2 (by rfl) ⟨684738, by rfl⟩ : syracuseStep 1825969 = 1369477) (by norm_num)
theorem B1826005 : Blo 1623010 1826005 := bbase (se 7 (by rfl) ⟨21398, by rfl⟩ : syracuseStep 1826005 = 42797) (by norm_num)
theorem B6167765 : Blo 1623010 6167765 := bbase (se 7 (by rfl) ⟨72278, by rfl⟩ : syracuseStep 6167765 = 144557) (by norm_num)
theorem B2055385 : Blo 1623010 2055385 := bbase (se 2 (by rfl) ⟨770769, by rfl⟩ : syracuseStep 2055385 = 1541539) (by norm_num)
theorem B3652829 : Blo 1623010 3652829 := bbase (se 3 (by rfl) ⟨684905, by rfl⟩ : syracuseStep 3652829 = 1369811) (by norm_num)
theorem B1826041 : Blo 1623010 1826041 := bbase (se 2 (by rfl) ⟨684765, by rfl⟩ : syracuseStep 1826041 = 1369531) (by norm_num)
theorem B3702029 : Blo 1623010 3702029 := bbase (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) (by norm_num)
theorem B1826077 : Blo 1623010 1826077 := bbase (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) (by norm_num)
theorem B3652901 : Blo 1623010 3652901 := bbase (se 4 (by rfl) ⟨342459, by rfl⟩ : syracuseStep 3652901 = 684919) (by norm_num)
theorem B4111661 : Blo 1623010 4111661 := bbase (se 3 (by rfl) ⟨770936, by rfl⟩ : syracuseStep 4111661 = 1541873) (by norm_num)
theorem B1826113 : Blo 1623010 1826113 := bbase (se 2 (by rfl) ⟨684792, by rfl⟩ : syracuseStep 1826113 = 1369585) (by norm_num)
theorem B2194757 : Blo 1623010 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B7806293 : Blo 1623010 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B1826149 : Blo 1623010 1826149 := bbase (se 4 (by rfl) ⟨171201, by rfl⟩ : syracuseStep 1826149 = 342403) (by norm_num)
theorem B3652973 : Blo 1623010 3652973 := bbase (se 3 (by rfl) ⟨684932, by rfl⟩ : syracuseStep 3652973 = 1369865) (by norm_num)
theorem B2055557 : Blo 1623010 2055557 := bbase (se 4 (by rfl) ⟨192708, by rfl⟩ : syracuseStep 2055557 = 385417) (by norm_num)
theorem B1826185 : Blo 1623010 1826185 := bbase (se 2 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 1826185 = 1369639) (by norm_num)
theorem B1826221 : Blo 1623010 1826221 := bbase (se 3 (by rfl) ⟨342416, by rfl⟩ : syracuseStep 1826221 = 684833) (by norm_num)
theorem B3653045 : Blo 1623010 3653045 := bbase (se 5 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 3653045 = 342473) (by norm_num)
theorem B2055613 : Blo 1623010 2055613 := bbase (se 3 (by rfl) ⟨385427, by rfl⟩ : syracuseStep 2055613 = 770855) (by norm_num)
theorem B1826257 : Blo 1623010 1826257 := bbase (se 2 (by rfl) ⟨684846, by rfl⟩ : syracuseStep 1826257 = 1369693) (by norm_num)
theorem B1826293 : Blo 1623010 1826293 := bbase (se 5 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 1826293 = 171215) (by norm_num)
theorem B15605237 : Blo 1623010 15605237 := bbase (se 5 (by rfl) ⟨731495, by rfl⟩ : syracuseStep 15605237 = 1462991) (by norm_num)
theorem B3653117 : Blo 1623010 3653117 := bbase (se 3 (by rfl) ⟨684959, by rfl⟩ : syracuseStep 3653117 = 1369919) (by norm_num)
theorem B13876757 : Blo 1623010 13876757 := bbase (se 6 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 13876757 = 650473) (by norm_num)
theorem B1826329 : Blo 1623010 1826329 := bbase (se 2 (by rfl) ⟨684873, by rfl⟩ : syracuseStep 1826329 = 1369747) (by norm_num)
theorem B2055709 : Blo 1623010 2055709 := bbase (se 3 (by rfl) ⟨385445, by rfl⟩ : syracuseStep 2055709 = 770891) (by norm_num)
theorem B5479973 : Blo 1623010 5479973 := bbase (se 4 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 5479973 = 1027495) (by norm_num)
theorem B1826365 : Blo 1623010 1826365 := bbase (se 3 (by rfl) ⟨342443, by rfl⟩ : syracuseStep 1826365 = 684887) (by norm_num)
theorem B3653189 : Blo 1623010 3653189 := bbase (se 4 (by rfl) ⟨342486, by rfl⟩ : syracuseStep 3653189 = 684973) (by norm_num)
theorem B1826401 : Blo 1623010 1826401 := bbase (se 2 (by rfl) ⟨684900, by rfl⟩ : syracuseStep 1826401 = 1369801) (by norm_num)
theorem B14810741 : Blo 1623010 14810741 := bbase (se 5 (by rfl) ⟨694253, by rfl⟩ : syracuseStep 14810741 = 1388507) (by norm_num)
theorem B1826437 : Blo 1623010 1826437 := bbase (se 4 (by rfl) ⟨171228, by rfl⟩ : syracuseStep 1826437 = 342457) (by norm_num)
theorem B4112005 : Blo 1623010 4112005 := bbase (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) (by norm_num)
theorem B3653261 : Blo 1623010 3653261 := bbase (se 3 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 3653261 = 1369973) (by norm_num)
theorem B1826473 : Blo 1623010 1826473 := bbase (se 2 (by rfl) ⟨684927, by rfl⟩ : syracuseStep 1826473 = 1369855) (by norm_num)
theorem B2055881 : Blo 1623010 2055881 := bbase (se 2 (by rfl) ⟨770955, by rfl⟩ : syracuseStep 2055881 = 1541911) (by norm_num)
theorem B1826509 : Blo 1623010 1826509 := bbase (se 3 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 1826509 = 684941) (by norm_num)
theorem B2637517 : Blo 1623010 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B3653333 : Blo 1623010 3653333 := bbase (se 7 (by rfl) ⟨42812, by rfl⟩ : syracuseStep 3653333 = 85625) (by norm_num)
theorem B1851121 : Blo 1623010 1851121 := bbase (se 2 (by rfl) ⟨694170, by rfl⟩ : syracuseStep 1851121 = 1388341) (by norm_num)
theorem B1826545 : Blo 1623010 1826545 := bbase (se 2 (by rfl) ⟨684954, by rfl⟩ : syracuseStep 1826545 = 1369909) (by norm_num)
theorem B2055937 : Blo 1623010 2055937 := bbase (se 2 (by rfl) ⟨770976, by rfl⟩ : syracuseStep 2055937 = 1541953) (by norm_num)
theorem B1826581 : Blo 1623010 1826581 := bbase (se 6 (by rfl) ⟨42810, by rfl⟩ : syracuseStep 1826581 = 85621) (by norm_num)
theorem B3653405 : Blo 1623010 3653405 := bbase (se 3 (by rfl) ⟨685013, by rfl⟩ : syracuseStep 3653405 = 1370027) (by norm_num)
theorem B1826617 : Blo 1623010 1826617 := bbase (se 2 (by rfl) ⟨684981, by rfl⟩ : syracuseStep 1826617 = 1369963) (by norm_num)
theorem B3702613 : Blo 1623010 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B1826653 : Blo 1623010 1826653 := bbase (se 3 (by rfl) ⟨342497, by rfl⟩ : syracuseStep 1826653 = 684995) (by norm_num)
theorem B3653477 : Blo 1623010 3653477 := bbase (se 4 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 3653477 = 685027) (by norm_num)
theorem B3383165 : Blo 1623010 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B1826689 : Blo 1623010 1826689 := bbase (se 2 (by rfl) ⟨685008, by rfl⟩ : syracuseStep 1826689 = 1370017) (by norm_num)
theorem B1826725 : Blo 1623010 1826725 := bbase (se 4 (by rfl) ⟨171255, by rfl⟩ : syracuseStep 1826725 = 342511) (by norm_num)
theorem B3653549 : Blo 1623010 3653549 := bbase (se 3 (by rfl) ⟨685040, by rfl⟩ : syracuseStep 3653549 = 1370081) (by norm_num)
theorem B3702725 : Blo 1623010 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B1826761 : Blo 1623010 1826761 := bbase (se 2 (by rfl) ⟨685035, by rfl⟩ : syracuseStep 1826761 = 1370071) (by norm_num)
theorem B5480405 : Blo 1623010 5480405 := bbase (se 7 (by rfl) ⟨64223, by rfl⟩ : syracuseStep 5480405 = 128447) (by norm_num)
theorem B1826797 : Blo 1623010 1826797 := bbase (se 3 (by rfl) ⟨342524, by rfl⟩ : syracuseStep 1826797 = 685049) (by norm_num)
theorem B3653621 : Blo 1623010 3653621 := bbase (se 5 (by rfl) ⟨171263, by rfl⟩ : syracuseStep 3653621 = 342527) (by norm_num)
theorem B1826851 : Blo 1623010 1826851 := bstep (se 1 (by rfl) ⟨1370138, by rfl⟩ : syracuseStep 1826851 = 2740277) B2740277
theorem B4759597 : Blo 1623010 4759597 := bstep (se 3 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 4759597 = 1784849) B1784849
theorem B5931107 : Blo 1623010 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B5480621 : Blo 1623010 5480621 := bstep (se 3 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 5480621 = 2055233) B2055233
theorem B1826995 : Blo 1623010 1826995 := bstep (se 1 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 1826995 = 2740493) B2740493
theorem B5480675 : Blo 1623010 5480675 := bstep (se 1 (by rfl) ⟨4110506, by rfl⟩ : syracuseStep 5480675 = 8221013) B8221013
theorem B3653873 : Blo 1623010 3653873 := bstep (se 2 (by rfl) ⟨1370202, by rfl⟩ : syracuseStep 3653873 = 2740405) B2740405
theorem B3653891 : Blo 1623010 3653891 := bstep (se 1 (by rfl) ⟨2740418, by rfl⟩ : syracuseStep 3653891 = 5480837) B5480837
theorem B1827139 : Blo 1623010 1827139 := bstep (se 1 (by rfl) ⟨1370354, by rfl⟩ : syracuseStep 1827139 = 2740709) B2740709
theorem B22225265 : Blo 1623010 22225265 := bstep (se 2 (by rfl) ⟨8334474, by rfl⟩ : syracuseStep 22225265 = 16668949) B16668949
theorem B9249187 : Blo 1623010 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B1827283 : Blo 1623010 1827283 := bstep (se 1 (by rfl) ⟨1370462, by rfl⟩ : syracuseStep 1827283 = 2740925) B2740925
theorem B5202413 : Blo 1623010 5202413 := bstep (se 3 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 5202413 = 1950905) B1950905
theorem B5480945 : Blo 1623010 5480945 := bstep (se 2 (by rfl) ⟨2055354, by rfl⟩ : syracuseStep 5480945 = 4110709) B4110709
theorem B3654161 : Blo 1623010 3654161 := bstep (se 2 (by rfl) ⟨1370310, by rfl⟩ : syracuseStep 3654161 = 2740621) B2740621
theorem B3654179 : Blo 1623010 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B1827427 : Blo 1623010 1827427 := bstep (se 1 (by rfl) ⟨1370570, by rfl⟩ : syracuseStep 1827427 = 2741141) B2741141
theorem B9872077 : Blo 1623010 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B1827571 : Blo 1623010 1827571 := bstep (se 1 (by rfl) ⟨1370678, by rfl⟩ : syracuseStep 1827571 = 2741357) B2741357
theorem B3654449 : Blo 1623010 3654449 := bstep (se 2 (by rfl) ⟨1370418, by rfl⟩ : syracuseStep 3654449 = 2740837) B2740837
theorem B3654467 : Blo 1623010 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B9249713 : Blo 1623010 9249713 := bstep (se 2 (by rfl) ⟨3468642, by rfl⟩ : syracuseStep 9249713 = 6937285) B6937285
theorem B1623011 : Blo 1623010 1623011 := bstep (se 1 (by rfl) ⟨1217258, by rfl⟩ : syracuseStep 1623011 = 2434517) B2434517
theorem B1623027 : Blo 1623010 1623027 := bstep (se 1 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 1623027 = 2434541) B2434541
theorem B1623043 : Blo 1623010 1623043 := bstep (se 1 (by rfl) ⟨1217282, by rfl⟩ : syracuseStep 1623043 = 2434565) B2434565
theorem B5481485 : Blo 1623010 5481485 := bstep (se 3 (by rfl) ⟨1027778, by rfl⟩ : syracuseStep 5481485 = 2055557) B2055557
theorem B3081233 : Blo 1623010 3081233 := bstep (se 2 (by rfl) ⟨1155462, by rfl⟩ : syracuseStep 3081233 = 2310925) B2310925
theorem B1623059 : Blo 1623010 1623059 := bstep (se 1 (by rfl) ⟨1217294, by rfl⟩ : syracuseStep 1623059 = 2434589) B2434589
theorem B1623075 : Blo 1623010 1623075 := bstep (se 1 (by rfl) ⟨1217306, by rfl⟩ : syracuseStep 1623075 = 2434613) B2434613
theorem B1623091 : Blo 1623010 1623091 := bstep (se 1 (by rfl) ⟨1217318, by rfl⟩ : syracuseStep 1623091 = 2434637) B2434637
theorem B2253889 : Blo 1623010 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B1623107 : Blo 1623010 1623107 := bstep (se 1 (by rfl) ⟨1217330, by rfl⟩ : syracuseStep 1623107 = 2434661) B2434661
theorem B5481539 : Blo 1623010 5481539 := bstep (se 1 (by rfl) ⟨4111154, by rfl⟩ : syracuseStep 5481539 = 8222309) B8222309
theorem B2311249 : Blo 1623010 2311249 := bstep (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) B1733437
theorem B3654737 : Blo 1623010 3654737 := bstep (se 2 (by rfl) ⟨1370526, by rfl⟩ : syracuseStep 3654737 = 2741053) B2741053
theorem B1623123 : Blo 1623010 1623123 := bstep (se 1 (by rfl) ⟨1217342, by rfl⟩ : syracuseStep 1623123 = 2434685) B2434685
theorem B1623139 : Blo 1623010 1623139 := bstep (se 1 (by rfl) ⟨1217354, by rfl⟩ : syracuseStep 1623139 = 2434709) B2434709
theorem B3654755 : Blo 1623010 3654755 := bstep (se 1 (by rfl) ⟨2741066, by rfl⟩ : syracuseStep 3654755 = 5482133) B5482133
theorem B63292529 : Blo 1623010 63292529 := bstep (se 2 (by rfl) ⟨23734698, by rfl⟩ : syracuseStep 63292529 = 47469397) B47469397
theorem B1623155 : Blo 1623010 1623155 := bstep (se 1 (by rfl) ⟨1217366, by rfl⟩ : syracuseStep 1623155 = 2434733) B2434733
theorem B1623171 : Blo 1623010 1623171 := bstep (se 1 (by rfl) ⟨1217378, by rfl⟩ : syracuseStep 1623171 = 2434757) B2434757
theorem B1623187 : Blo 1623010 1623187 := bstep (se 1 (by rfl) ⟨1217390, by rfl⟩ : syracuseStep 1623187 = 2434781) B2434781
theorem B1623203 : Blo 1623010 1623203 := bstep (se 1 (by rfl) ⟨1217402, by rfl⟩ : syracuseStep 1623203 = 2434805) B2434805
theorem B1623219 : Blo 1623010 1623219 := bstep (se 1 (by rfl) ⟨1217414, by rfl⟩ : syracuseStep 1623219 = 2434829) B2434829
theorem B1623235 : Blo 1623010 1623235 := bstep (se 1 (by rfl) ⟨1217426, by rfl⟩ : syracuseStep 1623235 = 2434853) B2434853
theorem B2311363 : Blo 1623010 2311363 := bstep (se 1 (by rfl) ⟨1733522, by rfl⟩ : syracuseStep 2311363 = 3467045) B3467045
theorem B2966737 : Blo 1623010 2966737 := bstep (se 2 (by rfl) ⟨1112526, by rfl⟩ : syracuseStep 2966737 = 2225053) B2225053
theorem B1623251 : Blo 1623010 1623251 := bstep (se 1 (by rfl) ⟨1217438, by rfl⟩ : syracuseStep 1623251 = 2434877) B2434877
theorem B1623267 : Blo 1623010 1623267 := bstep (se 1 (by rfl) ⟨1217450, by rfl⟩ : syracuseStep 1623267 = 2434901) B2434901
theorem B5932259 : Blo 1623010 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B1623283 : Blo 1623010 1623283 := bstep (se 1 (by rfl) ⟨1217462, by rfl⟩ : syracuseStep 1623283 = 2434925) B2434925
theorem B1623299 : Blo 1623010 1623299 := bstep (se 1 (by rfl) ⟨1217474, by rfl⟩ : syracuseStep 1623299 = 2434949) B2434949
theorem B1623315 : Blo 1623010 1623315 := bstep (se 1 (by rfl) ⟨1217486, by rfl⟩ : syracuseStep 1623315 = 2434973) B2434973
theorem B1623331 : Blo 1623010 1623331 := bstep (se 1 (by rfl) ⟨1217498, by rfl⟩ : syracuseStep 1623331 = 2434997) B2434997
theorem B1623347 : Blo 1623010 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B1623363 : Blo 1623010 1623363 := bstep (se 1 (by rfl) ⟨1217522, by rfl⟩ : syracuseStep 1623363 = 2435045) B2435045
theorem B5481809 : Blo 1623010 5481809 := bstep (se 2 (by rfl) ⟨2055678, by rfl⟩ : syracuseStep 5481809 = 4111357) B4111357
theorem B1623379 : Blo 1623010 1623379 := bstep (se 1 (by rfl) ⟨1217534, by rfl⟩ : syracuseStep 1623379 = 2435069) B2435069
theorem B1623395 : Blo 1623010 1623395 := bstep (se 1 (by rfl) ⟨1217546, by rfl⟩ : syracuseStep 1623395 = 2435093) B2435093
theorem B3655025 : Blo 1623010 3655025 := bstep (se 2 (by rfl) ⟨1370634, by rfl⟩ : syracuseStep 3655025 = 2741269) B2741269
theorem B1623411 : Blo 1623010 1623411 := bstep (se 1 (by rfl) ⟨1217558, by rfl⟩ : syracuseStep 1623411 = 2435117) B2435117
theorem B1623427 : Blo 1623010 1623427 := bstep (se 1 (by rfl) ⟨1217570, by rfl⟩ : syracuseStep 1623427 = 2435141) B2435141
theorem B3655043 : Blo 1623010 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B33326477 : Blo 1623010 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B8332685 : Blo 1623010 8332685 := bstep (se 3 (by rfl) ⟨1562378, by rfl⟩ : syracuseStep 8332685 = 3124757) B3124757
theorem B1623443 : Blo 1623010 1623443 := bstep (se 1 (by rfl) ⟨1217582, by rfl⟩ : syracuseStep 1623443 = 2435165) B2435165
theorem B3081635 : Blo 1623010 3081635 := bstep (se 1 (by rfl) ⟨2311226, by rfl⟩ : syracuseStep 3081635 = 4622453) B4622453
theorem B1623459 : Blo 1623010 1623459 := bstep (se 1 (by rfl) ⟨1217594, by rfl⟩ : syracuseStep 1623459 = 2435189) B2435189
theorem B1623475 : Blo 1623010 1623475 := bstep (se 1 (by rfl) ⟨1217606, by rfl⟩ : syracuseStep 1623475 = 2435213) B2435213
theorem B1623491 : Blo 1623010 1623491 := bstep (se 1 (by rfl) ⟨1217618, by rfl⟩ : syracuseStep 1623491 = 2435237) B2435237
theorem B1623507 : Blo 1623010 1623507 := bstep (se 1 (by rfl) ⟨1217630, by rfl⟩ : syracuseStep 1623507 = 2435261) B2435261
theorem B2434529 : Blo 1623010 2434529 := bstep (se 2 (by rfl) ⟨912948, by rfl⟩ : syracuseStep 2434529 = 1825897) B1825897
theorem B1623523 : Blo 1623010 1623523 := bstep (se 1 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 1623523 = 2435285) B2435285
theorem B8218097 : Blo 1623010 8218097 := bstep (se 2 (by rfl) ⟨3081786, by rfl⟩ : syracuseStep 8218097 = 6163573) B6163573
theorem B2434547 : Blo 1623010 2434547 := bstep (se 1 (by rfl) ⟨1825910, by rfl⟩ : syracuseStep 2434547 = 3651821) B3651821
theorem B1623539 : Blo 1623010 1623539 := bstep (se 1 (by rfl) ⟨1217654, by rfl⟩ : syracuseStep 1623539 = 2435309) B2435309
theorem B1623555 : Blo 1623010 1623555 := bstep (se 1 (by rfl) ⟨1217666, by rfl⟩ : syracuseStep 1623555 = 2435333) B2435333
theorem B2434577 : Blo 1623010 2434577 := bstep (se 2 (by rfl) ⟨912966, by rfl⟩ : syracuseStep 2434577 = 1825933) B1825933
theorem B1623571 : Blo 1623010 1623571 := bstep (se 1 (by rfl) ⟨1217678, by rfl⟩ : syracuseStep 1623571 = 2435357) B2435357
theorem B2434595 : Blo 1623010 2434595 := bstep (se 1 (by rfl) ⟨1825946, by rfl⟩ : syracuseStep 2434595 = 3651893) B3651893
theorem B1623587 : Blo 1623010 1623587 := bstep (se 1 (by rfl) ⟨1217690, by rfl⟩ : syracuseStep 1623587 = 2435381) B2435381
theorem B1623603 : Blo 1623010 1623603 := bstep (se 1 (by rfl) ⟨1217702, by rfl⟩ : syracuseStep 1623603 = 2435405) B2435405
theorem B2434625 : Blo 1623010 2434625 := bstep (se 2 (by rfl) ⟨912984, by rfl⟩ : syracuseStep 2434625 = 1825969) B1825969
theorem B1623619 : Blo 1623010 1623619 := bstep (se 1 (by rfl) ⟨1217714, by rfl⟩ : syracuseStep 1623619 = 2435429) B2435429
theorem B2434643 : Blo 1623010 2434643 := bstep (se 1 (by rfl) ⟨1825982, by rfl⟩ : syracuseStep 2434643 = 3651965) B3651965
theorem B1623635 : Blo 1623010 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B1623651 : Blo 1623010 1623651 := bstep (se 1 (by rfl) ⟨1217738, by rfl⟩ : syracuseStep 1623651 = 2435477) B2435477
theorem B2434673 : Blo 1623010 2434673 := bstep (se 2 (by rfl) ⟨913002, by rfl⟩ : syracuseStep 2434673 = 1826005) B1826005
theorem B1623667 : Blo 1623010 1623667 := bstep (se 1 (by rfl) ⟨1217750, by rfl⟩ : syracuseStep 1623667 = 2435501) B2435501
theorem B2434691 : Blo 1623010 2434691 := bstep (se 1 (by rfl) ⟨1826018, by rfl⟩ : syracuseStep 2434691 = 3652037) B3652037
theorem B1623683 : Blo 1623010 1623683 := bstep (se 1 (by rfl) ⟨1217762, by rfl⟩ : syracuseStep 1623683 = 2435525) B2435525
theorem B1623699 : Blo 1623010 1623699 := bstep (se 1 (by rfl) ⟨1217774, by rfl⟩ : syracuseStep 1623699 = 2435549) B2435549
theorem B2434721 : Blo 1623010 2434721 := bstep (se 2 (by rfl) ⟨913020, by rfl⟩ : syracuseStep 2434721 = 1826041) B1826041
theorem B1623715 : Blo 1623010 1623715 := bstep (se 1 (by rfl) ⟨1217786, by rfl⟩ : syracuseStep 1623715 = 2435573) B2435573
theorem B4621997 : Blo 1623010 4621997 := bstep (se 3 (by rfl) ⟨866624, by rfl⟩ : syracuseStep 4621997 = 1733249) B1733249
theorem B2434739 : Blo 1623010 2434739 := bstep (se 1 (by rfl) ⟨1826054, by rfl⟩ : syracuseStep 2434739 = 3652109) B3652109
theorem B1623731 : Blo 1623010 1623731 := bstep (se 1 (by rfl) ⟨1217798, by rfl⟩ : syracuseStep 1623731 = 2435597) B2435597
theorem B1623747 : Blo 1623010 1623747 := bstep (se 1 (by rfl) ⟨1217810, by rfl⟩ : syracuseStep 1623747 = 2435621) B2435621
theorem B2434769 : Blo 1623010 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B1623763 : Blo 1623010 1623763 := bstep (se 1 (by rfl) ⟨1217822, by rfl⟩ : syracuseStep 1623763 = 2435645) B2435645
theorem B2434787 : Blo 1623010 2434787 := bstep (se 1 (by rfl) ⟨1826090, by rfl⟩ : syracuseStep 2434787 = 3652181) B3652181
theorem B1623779 : Blo 1623010 1623779 := bstep (se 1 (by rfl) ⟨1217834, by rfl⟩ : syracuseStep 1623779 = 2435669) B2435669
theorem B7128803 : Blo 1623010 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B5203693 : Blo 1623010 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B1623795 : Blo 1623010 1623795 := bstep (se 1 (by rfl) ⟨1217846, by rfl⟩ : syracuseStep 1623795 = 2435693) B2435693
theorem B2434817 : Blo 1623010 2434817 := bstep (se 2 (by rfl) ⟨913056, by rfl⟩ : syracuseStep 2434817 = 1826113) B1826113
theorem B1623811 : Blo 1623010 1623811 := bstep (se 1 (by rfl) ⟨1217858, by rfl⟩ : syracuseStep 1623811 = 2435717) B2435717
theorem B2434835 : Blo 1623010 2434835 := bstep (se 1 (by rfl) ⟨1826126, by rfl⟩ : syracuseStep 2434835 = 3652253) B3652253
theorem B1623827 : Blo 1623010 1623827 := bstep (se 1 (by rfl) ⟨1217870, by rfl⟩ : syracuseStep 1623827 = 2435741) B2435741
theorem B1623843 : Blo 1623010 1623843 := bstep (se 1 (by rfl) ⟨1217882, by rfl⟩ : syracuseStep 1623843 = 2435765) B2435765
theorem B2434865 : Blo 1623010 2434865 := bstep (se 2 (by rfl) ⟨913074, by rfl⟩ : syracuseStep 2434865 = 1826149) B1826149
theorem B1623859 : Blo 1623010 1623859 := bstep (se 1 (by rfl) ⟨1217894, by rfl⟩ : syracuseStep 1623859 = 2435789) B2435789
theorem B2434883 : Blo 1623010 2434883 := bstep (se 1 (by rfl) ⟨1826162, by rfl⟩ : syracuseStep 2434883 = 3652325) B3652325
theorem B1623875 : Blo 1623010 1623875 := bstep (se 1 (by rfl) ⟨1217906, by rfl⟩ : syracuseStep 1623875 = 2435813) B2435813
theorem B1623891 : Blo 1623010 1623891 := bstep (se 1 (by rfl) ⟨1217918, by rfl⟩ : syracuseStep 1623891 = 2435837) B2435837
theorem B2434913 : Blo 1623010 2434913 := bstep (se 2 (by rfl) ⟨913092, by rfl⟩ : syracuseStep 2434913 = 1826185) B1826185
theorem B4622179 : Blo 1623010 4622179 := bstep (se 1 (by rfl) ⟨3466634, by rfl⟩ : syracuseStep 4622179 = 6933269) B6933269
theorem B1623907 : Blo 1623010 1623907 := bstep (se 1 (by rfl) ⟨1217930, by rfl⟩ : syracuseStep 1623907 = 2435861) B2435861
theorem B5482349 : Blo 1623010 5482349 := bstep (se 3 (by rfl) ⟨1027940, by rfl⟩ : syracuseStep 5482349 = 2055881) B2055881
theorem B2434931 : Blo 1623010 2434931 := bstep (se 1 (by rfl) ⟨1826198, by rfl⟩ : syracuseStep 2434931 = 3652397) B3652397
theorem B1623923 : Blo 1623010 1623923 := bstep (se 1 (by rfl) ⟨1217942, by rfl⟩ : syracuseStep 1623923 = 2435885) B2435885
theorem B1623939 : Blo 1623010 1623939 := bstep (se 1 (by rfl) ⟨1217954, by rfl⟩ : syracuseStep 1623939 = 2435909) B2435909
theorem B2434961 : Blo 1623010 2434961 := bstep (se 2 (by rfl) ⟨913110, by rfl⟩ : syracuseStep 2434961 = 1826221) B1826221
theorem B1623955 : Blo 1623010 1623955 := bstep (se 1 (by rfl) ⟨1217966, by rfl⟩ : syracuseStep 1623955 = 2435933) B2435933
theorem B2434979 : Blo 1623010 2434979 := bstep (se 1 (by rfl) ⟨1826234, by rfl⟩ : syracuseStep 2434979 = 3652469) B3652469
theorem B1623971 : Blo 1623010 1623971 := bstep (se 1 (by rfl) ⟨1217978, by rfl⟩ : syracuseStep 1623971 = 2435957) B2435957
theorem B5482403 : Blo 1623010 5482403 := bstep (se 1 (by rfl) ⟨4111802, by rfl⟩ : syracuseStep 5482403 = 8223605) B8223605
theorem B1623987 : Blo 1623010 1623987 := bstep (se 1 (by rfl) ⟨1217990, by rfl⟩ : syracuseStep 1623987 = 2435981) B2435981
theorem B2435009 : Blo 1623010 2435009 := bstep (se 2 (by rfl) ⟨913128, by rfl⟩ : syracuseStep 2435009 = 1826257) B1826257
theorem B1624003 : Blo 1623010 1624003 := bstep (se 1 (by rfl) ⟨1218002, by rfl⟩ : syracuseStep 1624003 = 2436005) B2436005
theorem B2435027 : Blo 1623010 2435027 := bstep (se 1 (by rfl) ⟨1826270, by rfl⟩ : syracuseStep 2435027 = 3652541) B3652541
theorem B1624019 : Blo 1623010 1624019 := bstep (se 1 (by rfl) ⟨1218014, by rfl⟩ : syracuseStep 1624019 = 2436029) B2436029
theorem B1624035 : Blo 1623010 1624035 := bstep (se 1 (by rfl) ⟨1218026, by rfl⟩ : syracuseStep 1624035 = 2436053) B2436053
theorem B2435057 : Blo 1623010 2435057 := bstep (se 2 (by rfl) ⟨913146, by rfl⟩ : syracuseStep 2435057 = 1826293) B1826293
theorem B1624051 : Blo 1623010 1624051 := bstep (se 1 (by rfl) ⟨1218038, by rfl⟩ : syracuseStep 1624051 = 2436077) B2436077
theorem B4622339 : Blo 1623010 4622339 := bstep (se 1 (by rfl) ⟨3466754, by rfl⟩ : syracuseStep 4622339 = 6933509) B6933509
theorem B2435075 : Blo 1623010 2435075 := bstep (se 1 (by rfl) ⟨1826306, by rfl⟩ : syracuseStep 2435075 = 3652613) B3652613
theorem B1624067 : Blo 1623010 1624067 := bstep (se 1 (by rfl) ⟨1218050, by rfl⟩ : syracuseStep 1624067 = 2436101) B2436101
theorem B15812621 : Blo 1623010 15812621 := bstep (se 3 (by rfl) ⟨2964866, by rfl⟩ : syracuseStep 15812621 = 5929733) B5929733
theorem B1624083 : Blo 1623010 1624083 := bstep (se 1 (by rfl) ⟨1218062, by rfl⟩ : syracuseStep 1624083 = 2436125) B2436125
theorem B2435105 : Blo 1623010 2435105 := bstep (se 2 (by rfl) ⟨913164, by rfl⟩ : syracuseStep 2435105 = 1826329) B1826329
theorem B1624099 : Blo 1623010 1624099 := bstep (se 1 (by rfl) ⟨1218074, by rfl⟩ : syracuseStep 1624099 = 2436149) B2436149
theorem B2435123 : Blo 1623010 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B1624115 : Blo 1623010 1624115 := bstep (se 1 (by rfl) ⟨1218086, by rfl⟩ : syracuseStep 1624115 = 2436173) B2436173
theorem B1624131 : Blo 1623010 1624131 := bstep (se 1 (by rfl) ⟨1218098, by rfl⟩ : syracuseStep 1624131 = 2436197) B2436197
theorem B2435153 : Blo 1623010 2435153 := bstep (se 2 (by rfl) ⟨913182, by rfl⟩ : syracuseStep 2435153 = 1826365) B1826365
theorem B1624147 : Blo 1623010 1624147 := bstep (se 1 (by rfl) ⟨1218110, by rfl⟩ : syracuseStep 1624147 = 2436221) B2436221
theorem B2435171 : Blo 1623010 2435171 := bstep (se 1 (by rfl) ⟨1826378, by rfl⟩ : syracuseStep 2435171 = 3652757) B3652757
theorem B1624163 : Blo 1623010 1624163 := bstep (se 1 (by rfl) ⟨1218122, by rfl⟩ : syracuseStep 1624163 = 2436245) B2436245
theorem B1624179 : Blo 1623010 1624179 := bstep (se 1 (by rfl) ⟨1218134, by rfl⟩ : syracuseStep 1624179 = 2436269) B2436269
theorem B2435201 : Blo 1623010 2435201 := bstep (se 2 (by rfl) ⟨913200, by rfl⟩ : syracuseStep 2435201 = 1826401) B1826401
theorem B1624195 : Blo 1623010 1624195 := bstep (se 1 (by rfl) ⟨1218146, by rfl⟩ : syracuseStep 1624195 = 2436293) B2436293
theorem B2435219 : Blo 1623010 2435219 := bstep (se 1 (by rfl) ⟨1826414, by rfl⟩ : syracuseStep 2435219 = 3652829) B3652829
theorem B1624211 : Blo 1623010 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B1624227 : Blo 1623010 1624227 := bstep (se 1 (by rfl) ⟨1218170, by rfl⟩ : syracuseStep 1624227 = 2436341) B2436341
theorem B2435249 : Blo 1623010 2435249 := bstep (se 2 (by rfl) ⟨913218, by rfl⟩ : syracuseStep 2435249 = 1826437) B1826437
theorem B1624243 : Blo 1623010 1624243 := bstep (se 1 (by rfl) ⟨1218182, by rfl⟩ : syracuseStep 1624243 = 2436365) B2436365
theorem B5482673 : Blo 1623010 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B2435267 : Blo 1623010 2435267 := bstep (se 1 (by rfl) ⟨1826450, by rfl⟩ : syracuseStep 2435267 = 3652901) B3652901
theorem B1624259 : Blo 1623010 1624259 := bstep (se 1 (by rfl) ⟨1218194, by rfl⟩ : syracuseStep 1624259 = 2436389) B2436389
theorem B1624275 : Blo 1623010 1624275 := bstep (se 1 (by rfl) ⟨1218206, by rfl⟩ : syracuseStep 1624275 = 2436413) B2436413
theorem B2435297 : Blo 1623010 2435297 := bstep (se 2 (by rfl) ⟨913236, by rfl⟩ : syracuseStep 2435297 = 1826473) B1826473
theorem B1624291 : Blo 1623010 1624291 := bstep (se 1 (by rfl) ⟨1218218, by rfl⟩ : syracuseStep 1624291 = 2436437) B2436437
theorem B5204195 : Blo 1623010 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B2435315 : Blo 1623010 2435315 := bstep (se 1 (by rfl) ⟨1826486, by rfl⟩ : syracuseStep 2435315 = 3652973) B3652973
theorem B1624307 : Blo 1623010 1624307 := bstep (se 1 (by rfl) ⟨1218230, by rfl⟩ : syracuseStep 1624307 = 2436461) B2436461
theorem B1624323 : Blo 1623010 1624323 := bstep (se 1 (by rfl) ⟨1218242, by rfl⟩ : syracuseStep 1624323 = 2436485) B2436485
theorem B12331277 : Blo 1623010 12331277 := bstep (se 3 (by rfl) ⟨2312114, by rfl⟩ : syracuseStep 12331277 = 4624229) B4624229
theorem B2435345 : Blo 1623010 2435345 := bstep (se 2 (by rfl) ⟨913254, by rfl⟩ : syracuseStep 2435345 = 1826509) B1826509
theorem B3516689 : Blo 1623010 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B1624339 : Blo 1623010 1624339 := bstep (se 1 (by rfl) ⟨1218254, by rfl⟩ : syracuseStep 1624339 = 2436509) B2436509
theorem B2435363 : Blo 1623010 2435363 := bstep (se 1 (by rfl) ⟨1826522, by rfl⟩ : syracuseStep 2435363 = 3653045) B3653045
theorem B3082531 : Blo 1623010 3082531 := bstep (se 1 (by rfl) ⟨2311898, by rfl⟩ : syracuseStep 3082531 = 4623797) B4623797
theorem B1624355 : Blo 1623010 1624355 := bstep (se 1 (by rfl) ⟨1218266, by rfl⟩ : syracuseStep 1624355 = 2436533) B2436533
theorem B1624371 : Blo 1623010 1624371 := bstep (se 1 (by rfl) ⟨1218278, by rfl⟩ : syracuseStep 1624371 = 2436557) B2436557
theorem B2468161 : Blo 1623010 2468161 := bstep (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) B1851121
theorem B2435393 : Blo 1623010 2435393 := bstep (se 2 (by rfl) ⟨913272, by rfl⟩ : syracuseStep 2435393 = 1826545) B1826545
theorem B3901763 : Blo 1623010 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B1624387 : Blo 1623010 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B9021773 : Blo 1623010 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B2435411 : Blo 1623010 2435411 := bstep (se 1 (by rfl) ⟨1826558, by rfl⟩ : syracuseStep 2435411 = 3653117) B3653117
theorem B1624403 : Blo 1623010 1624403 := bstep (se 1 (by rfl) ⟨1218302, by rfl⟩ : syracuseStep 1624403 = 2436605) B2436605
theorem B9251171 : Blo 1623010 9251171 := bstep (se 1 (by rfl) ⟨6938378, by rfl⟩ : syracuseStep 9251171 = 13876757) B13876757
theorem B1624419 : Blo 1623010 1624419 := bstep (se 1 (by rfl) ⟨1218314, by rfl⟩ : syracuseStep 1624419 = 2436629) B2436629
theorem B2435441 : Blo 1623010 2435441 := bstep (se 2 (by rfl) ⟨913290, by rfl⟩ : syracuseStep 2435441 = 1826581) B1826581
theorem B1624435 : Blo 1623010 1624435 := bstep (se 1 (by rfl) ⟨1218326, by rfl⟩ : syracuseStep 1624435 = 2436653) B2436653
theorem B2435459 : Blo 1623010 2435459 := bstep (se 1 (by rfl) ⟨1826594, by rfl⟩ : syracuseStep 2435459 = 3653189) B3653189
theorem B1624451 : Blo 1623010 1624451 := bstep (se 1 (by rfl) ⟨1218338, by rfl⟩ : syracuseStep 1624451 = 2436677) B2436677
theorem B1624467 : Blo 1623010 1624467 := bstep (se 1 (by rfl) ⟨1218350, by rfl⟩ : syracuseStep 1624467 = 2436701) B2436701
theorem B2435489 : Blo 1623010 2435489 := bstep (se 2 (by rfl) ⟨913308, by rfl⟩ : syracuseStep 2435489 = 1826617) B1826617
theorem B9873827 : Blo 1623010 9873827 := bstep (se 1 (by rfl) ⟨7405370, by rfl⟩ : syracuseStep 9873827 = 14810741) B14810741
theorem B1624483 : Blo 1623010 1624483 := bstep (se 1 (by rfl) ⟨1218362, by rfl⟩ : syracuseStep 1624483 = 2436725) B2436725
theorem B2435507 : Blo 1623010 2435507 := bstep (se 1 (by rfl) ⟨1826630, by rfl⟩ : syracuseStep 2435507 = 3653261) B3653261
theorem B1624499 : Blo 1623010 1624499 := bstep (se 1 (by rfl) ⟨1218374, by rfl⟩ : syracuseStep 1624499 = 2436749) B2436749
theorem B3082691 : Blo 1623010 3082691 := bstep (se 1 (by rfl) ⟨2312018, by rfl⟩ : syracuseStep 3082691 = 4624037) B4624037
theorem B2435537 : Blo 1623010 2435537 := bstep (se 2 (by rfl) ⟨913326, by rfl⟩ : syracuseStep 2435537 = 1826653) B1826653
theorem B2435555 : Blo 1623010 2435555 := bstep (se 1 (by rfl) ⟨1826666, by rfl⟩ : syracuseStep 2435555 = 3653333) B3653333
theorem B2435585 : Blo 1623010 2435585 := bstep (se 2 (by rfl) ⟨913344, by rfl⟩ : syracuseStep 2435585 = 1826689) B1826689
theorem B2312707 : Blo 1623010 2312707 := bstep (se 1 (by rfl) ⟨1734530, by rfl⟩ : syracuseStep 2312707 = 3469061) B3469061
theorem B2435603 : Blo 1623010 2435603 := bstep (se 1 (by rfl) ⟨1826702, by rfl⟩ : syracuseStep 2435603 = 3653405) B3653405
theorem B2435633 : Blo 1623010 2435633 := bstep (se 2 (by rfl) ⟨913362, by rfl⟩ : syracuseStep 2435633 = 1826725) B1826725
theorem B2435651 : Blo 1623010 2435651 := bstep (se 1 (by rfl) ⟨1826738, by rfl⟩ : syracuseStep 2435651 = 3653477) B3653477
theorem B2435681 : Blo 1623010 2435681 := bstep (se 2 (by rfl) ⟨913380, by rfl⟩ : syracuseStep 2435681 = 1826761) B1826761
theorem B2435699 : Blo 1623010 2435699 := bstep (se 1 (by rfl) ⟨1826774, by rfl⟩ : syracuseStep 2435699 = 3653549) B3653549
theorem B2468483 : Blo 1623010 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B2435729 : Blo 1623010 2435729 := bstep (se 2 (by rfl) ⟨913398, by rfl⟩ : syracuseStep 2435729 = 1826797) B1826797
theorem B2435747 : Blo 1623010 2435747 := bstep (se 1 (by rfl) ⟨1826810, by rfl⟩ : syracuseStep 2435747 = 3653621) B3653621
theorem B2468531 : Blo 1623010 2468531 := bstep (se 1 (by rfl) ⟨1851398, by rfl⟩ : syracuseStep 2468531 = 3702797) B3702797
theorem B2435777 : Blo 1623010 2435777 := bstep (se 2 (by rfl) ⟨913416, by rfl⟩ : syracuseStep 2435777 = 1826833) B1826833
theorem B2435795 : Blo 1623010 2435795 := bstep (se 1 (by rfl) ⟨1826846, by rfl⟩ : syracuseStep 2435795 = 3653693) B3653693
theorem B2435825 : Blo 1623010 2435825 := bstep (se 2 (by rfl) ⟨913434, by rfl⟩ : syracuseStep 2435825 = 1826869) B1826869
theorem B2738947 : Blo 1623010 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B2435843 : Blo 1623010 2435843 := bstep (se 1 (by rfl) ⟨1826882, by rfl⟩ : syracuseStep 2435843 = 3653765) B3653765
theorem B2435873 : Blo 1623010 2435873 := bstep (se 2 (by rfl) ⟨913452, by rfl⟩ : syracuseStep 2435873 = 1826905) B1826905
theorem B2435891 : Blo 1623010 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B2435921 : Blo 1623010 2435921 := bstep (se 2 (by rfl) ⟨913470, by rfl⟩ : syracuseStep 2435921 = 1826941) B1826941
theorem B2435939 : Blo 1623010 2435939 := bstep (se 1 (by rfl) ⟨1826954, by rfl⟩ : syracuseStep 2435939 = 3653909) B3653909
theorem B2435969 : Blo 1623010 2435969 := bstep (se 2 (by rfl) ⟨913488, by rfl⟩ : syracuseStep 2435969 = 1826977) B1826977
theorem B5557123 : Blo 1623010 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B2739089 : Blo 1623010 2739089 := bstep (se 2 (by rfl) ⟨1027158, by rfl⟩ : syracuseStep 2739089 = 2054317) B2054317
theorem B2435987 : Blo 1623010 2435987 := bstep (se 1 (by rfl) ⟨1826990, by rfl⟩ : syracuseStep 2435987 = 3653981) B3653981
theorem B8219555 : Blo 1623010 8219555 := bstep (se 1 (by rfl) ⟨6164666, by rfl⟩ : syracuseStep 8219555 = 12329333) B12329333
theorem B2436017 : Blo 1623010 2436017 := bstep (se 2 (by rfl) ⟨913506, by rfl⟩ : syracuseStep 2436017 = 1827013) B1827013
theorem B2436035 : Blo 1623010 2436035 := bstep (se 1 (by rfl) ⟨1827026, by rfl⟩ : syracuseStep 2436035 = 3654053) B3654053
theorem B2436065 : Blo 1623010 2436065 := bstep (se 2 (by rfl) ⟨913524, by rfl⟩ : syracuseStep 2436065 = 1827049) B1827049
theorem B2436083 : Blo 1623010 2436083 := bstep (se 1 (by rfl) ⟨1827062, by rfl⟩ : syracuseStep 2436083 = 3654125) B3654125
theorem B2739217 : Blo 1623010 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B2436113 : Blo 1623010 2436113 := bstep (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) B1827085
theorem B2436131 : Blo 1623010 2436131 := bstep (se 1 (by rfl) ⟨1827098, by rfl⟩ : syracuseStep 2436131 = 3654197) B3654197
theorem B4623409 : Blo 1623010 4623409 := bstep (se 2 (by rfl) ⟨1733778, by rfl⟩ : syracuseStep 4623409 = 3467557) B3467557
theorem B2739251 : Blo 1623010 2739251 := bstep (se 1 (by rfl) ⟨2054438, by rfl⟩ : syracuseStep 2739251 = 4108877) B4108877
theorem B2436161 : Blo 1623010 2436161 := bstep (se 2 (by rfl) ⟨913560, by rfl⟩ : syracuseStep 2436161 = 1827121) B1827121
theorem B2436179 : Blo 1623010 2436179 := bstep (se 1 (by rfl) ⟨1827134, by rfl⟩ : syracuseStep 2436179 = 3654269) B3654269
theorem B2436209 : Blo 1623010 2436209 := bstep (se 2 (by rfl) ⟨913578, by rfl⟩ : syracuseStep 2436209 = 1827157) B1827157
theorem B2436227 : Blo 1623010 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B2436257 : Blo 1623010 2436257 := bstep (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) B1827193
theorem B2739379 : Blo 1623010 2739379 := bstep (se 1 (by rfl) ⟨2054534, by rfl⟩ : syracuseStep 2739379 = 4109069) B4109069
theorem B2436275 : Blo 1623010 2436275 := bstep (se 1 (by rfl) ⟨1827206, by rfl⟩ : syracuseStep 2436275 = 3654413) B3654413
theorem B2436305 : Blo 1623010 2436305 := bstep (se 2 (by rfl) ⟨913614, by rfl⟩ : syracuseStep 2436305 = 1827229) B1827229
theorem B2436323 : Blo 1623010 2436323 := bstep (se 1 (by rfl) ⟨1827242, by rfl⟩ : syracuseStep 2436323 = 3654485) B3654485
theorem B2436353 : Blo 1623010 2436353 := bstep (se 2 (by rfl) ⟨913632, by rfl⟩ : syracuseStep 2436353 = 1827265) B1827265
theorem B2436371 : Blo 1623010 2436371 := bstep (se 1 (by rfl) ⟨1827278, by rfl⟩ : syracuseStep 2436371 = 3654557) B3654557
theorem B9375011 : Blo 1623010 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B2436401 : Blo 1623010 2436401 := bstep (se 2 (by rfl) ⟨913650, by rfl⟩ : syracuseStep 2436401 = 1827301) B1827301
theorem B2739521 : Blo 1623010 2739521 := bstep (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) B2054641
theorem B2436419 : Blo 1623010 2436419 := bstep (se 1 (by rfl) ⟨1827314, by rfl⟩ : syracuseStep 2436419 = 3654629) B3654629
theorem B2436449 : Blo 1623010 2436449 := bstep (se 2 (by rfl) ⟨913668, by rfl⟩ : syracuseStep 2436449 = 1827337) B1827337
theorem B2436467 : Blo 1623010 2436467 := bstep (se 1 (by rfl) ⟨1827350, by rfl⟩ : syracuseStep 2436467 = 3654701) B3654701
theorem B2436497 : Blo 1623010 2436497 := bstep (se 2 (by rfl) ⟨913686, by rfl⟩ : syracuseStep 2436497 = 1827373) B1827373
theorem B2436515 : Blo 1623010 2436515 := bstep (se 1 (by rfl) ⟨1827386, by rfl⟩ : syracuseStep 2436515 = 3654773) B3654773
theorem B2739649 : Blo 1623010 2739649 := bstep (se 2 (by rfl) ⟨1027368, by rfl⟩ : syracuseStep 2739649 = 2054737) B2054737
theorem B2436545 : Blo 1623010 2436545 := bstep (se 2 (by rfl) ⟨913704, by rfl⟩ : syracuseStep 2436545 = 1827409) B1827409
theorem B10407365 : Blo 1623010 10407365 := bstep (se 4 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 10407365 = 1951381) B1951381
theorem B2436563 : Blo 1623010 2436563 := bstep (se 1 (by rfl) ⟨1827422, by rfl⟩ : syracuseStep 2436563 = 3654845) B3654845
theorem B2739683 : Blo 1623010 2739683 := bstep (se 1 (by rfl) ⟨2054762, by rfl⟩ : syracuseStep 2739683 = 4109525) B4109525
theorem B3083761 : Blo 1623010 3083761 := bstep (se 2 (by rfl) ⟨1156410, by rfl⟩ : syracuseStep 3083761 = 2312821) B2312821
theorem B2436593 : Blo 1623010 2436593 := bstep (se 2 (by rfl) ⟨913722, by rfl⟩ : syracuseStep 2436593 = 1827445) B1827445
theorem B2436611 : Blo 1623010 2436611 := bstep (se 1 (by rfl) ⟨1827458, by rfl⟩ : syracuseStep 2436611 = 3654917) B3654917
theorem B6581773 : Blo 1623010 6581773 := bstep (se 3 (by rfl) ⟨1234082, by rfl⟩ : syracuseStep 6581773 = 2468165) B2468165
theorem B2436641 : Blo 1623010 2436641 := bstep (se 2 (by rfl) ⟨913740, by rfl⟩ : syracuseStep 2436641 = 1827481) B1827481
theorem B2436659 : Blo 1623010 2436659 := bstep (se 1 (by rfl) ⟨1827494, by rfl⟩ : syracuseStep 2436659 = 3654989) B3654989
theorem B6164045 : Blo 1623010 6164045 := bstep (se 3 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 6164045 = 2311517) B2311517
theorem B2436689 : Blo 1623010 2436689 := bstep (se 2 (by rfl) ⟨913758, by rfl⟩ : syracuseStep 2436689 = 1827517) B1827517
theorem B2739811 : Blo 1623010 2739811 := bstep (se 1 (by rfl) ⟨2054858, by rfl⟩ : syracuseStep 2739811 = 4109717) B4109717
theorem B2436707 : Blo 1623010 2436707 := bstep (se 1 (by rfl) ⟨1827530, by rfl⟩ : syracuseStep 2436707 = 3655061) B3655061
theorem B2436737 : Blo 1623010 2436737 := bstep (se 2 (by rfl) ⟨913776, by rfl⟩ : syracuseStep 2436737 = 1827553) B1827553
theorem B2600579 : Blo 1623010 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B6934157 : Blo 1623010 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B2436755 : Blo 1623010 2436755 := bstep (se 1 (by rfl) ⟨1827566, by rfl⟩ : syracuseStep 2436755 = 3655133) B3655133
theorem B6934193 : Blo 1623010 6934193 := bstep (se 2 (by rfl) ⟨2600322, by rfl⟩ : syracuseStep 6934193 = 5200645) B5200645
theorem B8220365 : Blo 1623010 8220365 := bstep (se 3 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 8220365 = 3082637) B3082637
theorem B3469027 : Blo 1623010 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B2739953 : Blo 1623010 2739953 := bstep (se 2 (by rfl) ⟨1027482, by rfl⟩ : syracuseStep 2739953 = 2054965) B2054965
theorem B5271313 : Blo 1623010 5271313 := bstep (se 2 (by rfl) ⟨1976742, by rfl⟩ : syracuseStep 5271313 = 3953485) B3953485
theorem B4935505 : Blo 1623010 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B2740081 : Blo 1623010 2740081 := bstep (se 2 (by rfl) ⟨1027530, by rfl⟩ : syracuseStep 2740081 = 2055061) B2055061
theorem B2740115 : Blo 1623010 2740115 := bstep (se 1 (by rfl) ⟨2055086, by rfl⟩ : syracuseStep 2740115 = 4110173) B4110173
theorem B2600867 : Blo 1623010 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B8679331 : Blo 1623010 8679331 := bstep (se 1 (by rfl) ⟨6509498, by rfl⟩ : syracuseStep 8679331 = 13018997) B13018997
theorem B4108259 : Blo 1623010 4108259 := bstep (se 1 (by rfl) ⟨3081194, by rfl⟩ : syracuseStep 4108259 = 6162389) B6162389
theorem B7802851 : Blo 1623010 7802851 := bstep (se 1 (by rfl) ⟨5852138, by rfl⟩ : syracuseStep 7802851 = 11704277) B11704277
theorem B9375749 : Blo 1623010 9375749 := bstep (se 4 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 9375749 = 1757953) B1757953
theorem B2740243 : Blo 1623010 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B17559665 : Blo 1623010 17559665 := bstep (se 2 (by rfl) ⟨6584874, by rfl⟩ : syracuseStep 17559665 = 13169749) B13169749
theorem B9244813 : Blo 1623010 9244813 := bstep (se 3 (by rfl) ⟨1733402, by rfl⟩ : syracuseStep 9244813 = 3466805) B3466805
theorem B2740385 : Blo 1623010 2740385 := bstep (se 2 (by rfl) ⟨1027644, by rfl⟩ : syracuseStep 2740385 = 2055289) B2055289
theorem B10400005 : Blo 1623010 10400005 := bstep (se 4 (by rfl) ⟨975000, by rfl⟩ : syracuseStep 10400005 = 1950001) B1950001
theorem B2740513 : Blo 1623010 2740513 := bstep (se 2 (by rfl) ⟨1027692, by rfl⟩ : syracuseStep 2740513 = 2055385) B2055385
theorem B4624685 : Blo 1623010 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B2601283 : Blo 1623010 2601283 := bstep (se 1 (by rfl) ⟨1950962, by rfl⟩ : syracuseStep 2601283 = 3901925) B3901925
theorem B2740547 : Blo 1623010 2740547 := bstep (se 1 (by rfl) ⟨2055410, by rfl⟩ : syracuseStep 2740547 = 4110821) B4110821
theorem B6164849 : Blo 1623010 6164849 := bstep (se 2 (by rfl) ⟨2311818, by rfl⟩ : syracuseStep 6164849 = 4623637) B4623637
theorem B2740675 : Blo 1623010 2740675 := bstep (se 1 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 2740675 = 4111013) B4111013
theorem B4624867 : Blo 1623010 4624867 := bstep (se 1 (by rfl) ⟨3468650, by rfl⟩ : syracuseStep 4624867 = 6937301) B6937301
theorem B7909901 : Blo 1623010 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B4624913 : Blo 1623010 4624913 := bstep (se 2 (by rfl) ⟨1734342, by rfl⟩ : syracuseStep 4624913 = 3468685) B3468685
theorem B12325445 : Blo 1623010 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B8237645 : Blo 1623010 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B2601553 : Blo 1623010 2601553 := bstep (se 2 (by rfl) ⟨975582, by rfl⟩ : syracuseStep 2601553 = 1951165) B1951165
theorem B2740817 : Blo 1623010 2740817 := bstep (se 2 (by rfl) ⟨1027806, by rfl⟩ : syracuseStep 2740817 = 2055613) B2055613
theorem B2740945 : Blo 1623010 2740945 := bstep (se 2 (by rfl) ⟨1027854, by rfl⟩ : syracuseStep 2740945 = 2055709) B2055709
theorem B2740979 : Blo 1623010 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B2601809 : Blo 1623010 2601809 := bstep (se 2 (by rfl) ⟨975678, by rfl⟩ : syracuseStep 2601809 = 1951357) B1951357
theorem B2741107 : Blo 1623010 2741107 := bstep (se 1 (by rfl) ⟨2055830, by rfl⟩ : syracuseStep 2741107 = 4111661) B4111661
theorem B4109201 : Blo 1623010 4109201 := bstep (se 2 (by rfl) ⟨1540950, by rfl⟩ : syracuseStep 4109201 = 3081901) B3081901
theorem B4109251 : Blo 1623010 4109251 := bstep (se 1 (by rfl) ⟨3081938, by rfl⟩ : syracuseStep 4109251 = 6163877) B6163877
theorem B2741249 : Blo 1623010 2741249 := bstep (se 2 (by rfl) ⟨1027968, by rfl⟩ : syracuseStep 2741249 = 2055937) B2055937
theorem B6165517 : Blo 1623010 6165517 := bstep (se 3 (by rfl) ⟨1156034, by rfl⟩ : syracuseStep 6165517 = 2312069) B2312069
theorem B4109393 : Blo 1623010 4109393 := bstep (se 2 (by rfl) ⟨1541022, by rfl⟩ : syracuseStep 4109393 = 3082045) B3082045
theorem B4936817 : Blo 1623010 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B12334193 : Blo 1623010 12334193 := bstep (se 2 (by rfl) ⟨4625322, by rfl⟩ : syracuseStep 12334193 = 9250645) B9250645
theorem B1733843 : Blo 1623010 1733843 := bstep (se 1 (by rfl) ⟨1300382, by rfl⟩ : syracuseStep 1733843 = 2600765) B2600765
theorem B4388195 : Blo 1623010 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B56219021 : Blo 1623010 56219021 := bstep (se 3 (by rfl) ⟨10541066, by rfl⟩ : syracuseStep 56219021 = 21082133) B21082133
theorem B5854733 : Blo 1623010 5854733 := bstep (se 3 (by rfl) ⟨1097762, by rfl⟩ : syracuseStep 5854733 = 2195525) B2195525
theorem B35599985 : Blo 1623010 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B5478029 : Blo 1623010 5478029 := bstep (se 3 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 5478029 = 2054261) B2054261
theorem B5478083 : Blo 1623010 5478083 := bstep (se 1 (by rfl) ⟨4108562, by rfl⟩ : syracuseStep 5478083 = 8217125) B8217125
theorem B6166307 : Blo 1623010 6166307 := bstep (se 1 (by rfl) ⟨4624730, by rfl⟩ : syracuseStep 6166307 = 9249461) B9249461
theorem B18503477 : Blo 1623010 18503477 := bstep (se 5 (by rfl) ⟨867350, by rfl⟩ : syracuseStep 18503477 = 1734701) B1734701
theorem B7804849 : Blo 1623010 7804849 := bstep (se 2 (by rfl) ⟨2926818, by rfl⟩ : syracuseStep 7804849 = 5853637) B5853637
theorem B5478353 : Blo 1623010 5478353 := bstep (se 2 (by rfl) ⟨2054382, by rfl⟩ : syracuseStep 5478353 = 4108765) B4108765
theorem B5199889 : Blo 1623010 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B4110385 : Blo 1623010 4110385 := bstep (se 2 (by rfl) ⟨1541394, by rfl⟩ : syracuseStep 4110385 = 3082789) B3082789
theorem B23410741 : Blo 1623010 23410741 := bstep (se 5 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 23410741 = 2194757) B2194757
theorem B9246797 : Blo 1623010 9246797 := bstep (se 3 (by rfl) ⟨1733774, by rfl⟩ : syracuseStep 9246797 = 3467549) B3467549
theorem B16890083 : Blo 1623010 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B3651857 : Blo 1623010 3651857 := bstep (se 2 (by rfl) ⟨1369446, by rfl⟩ : syracuseStep 3651857 = 2738893) B2738893
theorem B3651875 : Blo 1623010 3651875 := bstep (se 1 (by rfl) ⟨2738906, by rfl⟩ : syracuseStep 3651875 = 5477813) B5477813
theorem B4389169 : Blo 1623010 4389169 := bstep (se 2 (by rfl) ⟨1645938, by rfl⟩ : syracuseStep 4389169 = 3291877) B3291877
theorem B4110659 : Blo 1623010 4110659 := bstep (se 1 (by rfl) ⟨3082994, by rfl⟩ : syracuseStep 4110659 = 6165989) B6165989
theorem B8329549 : Blo 1623010 8329549 := bstep (se 3 (by rfl) ⟨1561790, by rfl⟩ : syracuseStep 8329549 = 3123581) B3123581
theorem B6166961 : Blo 1623010 6166961 := bstep (se 2 (by rfl) ⟨2312610, by rfl⟩ : syracuseStep 6166961 = 4625221) B4625221
theorem B5200337 : Blo 1623010 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B5478893 : Blo 1623010 5478893 := bstep (se 3 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 5478893 = 2054585) B2054585
theorem B4110851 : Blo 1623010 4110851 := bstep (se 1 (by rfl) ⟨3083138, by rfl⟩ : syracuseStep 4110851 = 6166277) B6166277
theorem B5478947 : Blo 1623010 5478947 := bstep (se 1 (by rfl) ⟨4109210, by rfl⟩ : syracuseStep 5478947 = 8218421) B8218421
theorem B3652145 : Blo 1623010 3652145 := bstep (se 2 (by rfl) ⟨1369554, by rfl⟩ : syracuseStep 3652145 = 2739109) B2739109
theorem B8223281 : Blo 1623010 8223281 := bstep (se 2 (by rfl) ⟨3083730, by rfl⟩ : syracuseStep 8223281 = 6167461) B6167461
theorem B3652163 : Blo 1623010 3652163 := bstep (se 1 (by rfl) ⟨2739122, by rfl⟩ : syracuseStep 3652163 = 5478245) B5478245
theorem B2054803 : Blo 1623010 2054803 := bstep (se 1 (by rfl) ⟨1541102, by rfl⟩ : syracuseStep 2054803 = 3082205) B3082205
theorem B2054899 : Blo 1623010 2054899 := bstep (se 1 (by rfl) ⟨1541174, by rfl⟩ : syracuseStep 2054899 = 3082349) B3082349
theorem B7027505 : Blo 1623010 7027505 := bstep (se 2 (by rfl) ⟨2635314, by rfl⟩ : syracuseStep 7027505 = 5270629) B5270629
theorem B5479217 : Blo 1623010 5479217 := bstep (se 2 (by rfl) ⟨2054706, by rfl⟩ : syracuseStep 5479217 = 4109413) B4109413
theorem B3652433 : Blo 1623010 3652433 := bstep (se 2 (by rfl) ⟨1369662, by rfl⟩ : syracuseStep 3652433 = 2739325) B2739325
theorem B3652451 : Blo 1623010 3652451 := bstep (se 1 (by rfl) ⟨2739338, by rfl⟩ : syracuseStep 3652451 = 5478677) B5478677
theorem B7125965 : Blo 1623010 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B7027697 : Blo 1623010 7027697 := bstep (se 2 (by rfl) ⟨2635386, by rfl⟩ : syracuseStep 7027697 = 5270773) B5270773
theorem B9247729 : Blo 1623010 9247729 := bstep (se 2 (by rfl) ⟨3467898, by rfl⟩ : syracuseStep 9247729 = 6935797) B6935797
theorem B15817841 : Blo 1623010 15817841 := bstep (se 2 (by rfl) ⟨5931690, by rfl⟩ : syracuseStep 15817841 = 11863381) B11863381
theorem B3652721 : Blo 1623010 3652721 := bstep (se 2 (by rfl) ⟨1369770, by rfl⟩ : syracuseStep 3652721 = 2739541) B2739541
theorem B3652739 : Blo 1623010 3652739 := bstep (se 1 (by rfl) ⟨2739554, by rfl⟩ : syracuseStep 3652739 = 5479109) B5479109
theorem B1825987 : Blo 1623010 1825987 := bstep (se 1 (by rfl) ⟨1369490, by rfl⟩ : syracuseStep 1825987 = 2738981) B2738981
theorem B2055395 : Blo 1623010 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B5479757 : Blo 1623010 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B1826131 : Blo 1623010 1826131 := bstep (se 1 (by rfl) ⟨1369598, by rfl⟩ : syracuseStep 1826131 = 2739197) B2739197
theorem B5479811 : Blo 1623010 5479811 := bstep (se 1 (by rfl) ⟨4109858, by rfl⟩ : syracuseStep 5479811 = 8219717) B8219717
theorem B3653009 : Blo 1623010 3653009 := bstep (se 2 (by rfl) ⟨1369878, by rfl⟩ : syracuseStep 3653009 = 2739757) B2739757
theorem B2637203 : Blo 1623010 2637203 := bstep (se 1 (by rfl) ⟨1977902, by rfl⟩ : syracuseStep 2637203 = 3955805) B3955805
theorem B3653027 : Blo 1623010 3653027 := bstep (se 1 (by rfl) ⟨2739770, by rfl⟩ : syracuseStep 3653027 = 5479541) B5479541
theorem B4111793 : Blo 1623010 4111793 := bstep (se 2 (by rfl) ⟨1541922, by rfl⟩ : syracuseStep 4111793 = 3083845) B3083845
theorem B1826275 : Blo 1623010 1826275 := bstep (se 1 (by rfl) ⟨1369706, by rfl⟩ : syracuseStep 1826275 = 2739413) B2739413
theorem B4111843 : Blo 1623010 4111843 := bstep (se 1 (by rfl) ⟨3083882, by rfl⟩ : syracuseStep 4111843 = 6167765) B6167765
theorem B13868657 : Blo 1623010 13868657 := bstep (se 2 (by rfl) ⟨5200746, by rfl⟩ : syracuseStep 13868657 = 10401493) B10401493
theorem B4111985 : Blo 1623010 4111985 := bstep (se 2 (by rfl) ⟨1541994, by rfl⟩ : syracuseStep 4111985 = 3083989) B3083989
theorem B1826419 : Blo 1623010 1826419 := bstep (se 1 (by rfl) ⟨1369814, by rfl⟩ : syracuseStep 1826419 = 2739629) B2739629
theorem B5480081 : Blo 1623010 5480081 := bstep (se 2 (by rfl) ⟨2055030, by rfl⟩ : syracuseStep 5480081 = 4110061) B4110061
theorem B10403491 : Blo 1623010 10403491 := bstep (se 1 (by rfl) ⟨7802618, by rfl⟩ : syracuseStep 10403491 = 15605237) B15605237
theorem B3653297 : Blo 1623010 3653297 := bstep (se 2 (by rfl) ⟨1369986, by rfl⟩ : syracuseStep 3653297 = 2739973) B2739973
theorem B3653315 : Blo 1623010 3653315 := bstep (se 1 (by rfl) ⟨2739986, by rfl⟩ : syracuseStep 3653315 = 5479973) B5479973
theorem B1826563 : Blo 1623010 1826563 := bstep (se 1 (by rfl) ⟨1369922, by rfl⟩ : syracuseStep 1826563 = 2739845) B2739845
theorem B1826707 : Blo 1623010 1826707 := bstep (se 1 (by rfl) ⟨1370030, by rfl⟩ : syracuseStep 1826707 = 2740061) B2740061
theorem B6938531 : Blo 1623010 6938531 := bstep (se 1 (by rfl) ⟨5203898, by rfl⟩ : syracuseStep 6938531 = 10407797) B10407797
theorem B3653585 : Blo 1623010 3653585 := bstep (se 2 (by rfl) ⟨1370094, by rfl⟩ : syracuseStep 3653585 = 2740189) B2740189
theorem B3653603 : Blo 1623010 3653603 := bstep (se 1 (by rfl) ⟨2740202, by rfl⟩ : syracuseStep 3653603 = 5480405) B5480405
theorem B6250499 : Blo 1623010 6250499 := bstep (se 1 (by rfl) ⟨4687874, by rfl⟩ : syracuseStep 6250499 = 9375749) B9375749
theorem B3653657 : Blo 1623010 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B5480513 : Blo 1623010 5480513 := bstep (se 2 (by rfl) ⟨2055192, by rfl⟩ : syracuseStep 5480513 = 4110385) B4110385
theorem B11706443 : Blo 1623010 11706443 := bstep (se 1 (by rfl) ⟨8779832, by rfl⟩ : syracuseStep 11706443 = 17559665) B17559665
theorem B1826923 : Blo 1623010 1826923 := bstep (se 1 (by rfl) ⟨1370192, by rfl⟩ : syracuseStep 1826923 = 2740385) B2740385
theorem B3653747 : Blo 1623010 3653747 := bstep (se 1 (by rfl) ⟨2740310, by rfl⟩ : syracuseStep 3653747 = 5480621) B5480621
theorem B3653783 : Blo 1623010 3653783 := bstep (se 1 (by rfl) ⟨2740337, by rfl⟩ : syracuseStep 3653783 = 5480675) B5480675
theorem B1827031 : Blo 1623010 1827031 := bstep (se 1 (by rfl) ⟨1370273, by rfl⟩ : syracuseStep 1827031 = 2740547) B2740547
theorem B3653963 : Blo 1623010 3653963 := bstep (se 1 (by rfl) ⟨2740472, by rfl⟩ : syracuseStep 3653963 = 5480945) B5480945
theorem B3654017 : Blo 1623010 3654017 := bstep (se 2 (by rfl) ⟨1370256, by rfl⟩ : syracuseStep 3654017 = 2740513) B2740513
theorem B8216963 : Blo 1623010 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B1827211 : Blo 1623010 1827211 := bstep (se 1 (by rfl) ⟨1370408, by rfl⟩ : syracuseStep 1827211 = 2740817) B2740817
theorem B1827319 : Blo 1623010 1827319 := bstep (se 1 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 1827319 = 2740979) B2740979
theorem B3654233 : Blo 1623010 3654233 := bstep (se 2 (by rfl) ⟨1370337, by rfl⟩ : syracuseStep 3654233 = 2740675) B2740675
theorem B5481053 : Blo 1623010 5481053 := bstep (se 3 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 5481053 = 2055395) B2055395
theorem B1827499 : Blo 1623010 1827499 := bstep (se 1 (by rfl) ⟨1370624, by rfl⟩ : syracuseStep 1827499 = 2741249) B2741249
theorem B3654323 : Blo 1623010 3654323 := bstep (se 1 (by rfl) ⟨2740742, by rfl⟩ : syracuseStep 3654323 = 5481485) B5481485
theorem B3654359 : Blo 1623010 3654359 := bstep (se 1 (by rfl) ⟨2740769, by rfl⟩ : syracuseStep 3654359 = 5481539) B5481539
theorem B3654539 : Blo 1623010 3654539 := bstep (se 1 (by rfl) ⟨2740904, by rfl⟩ : syracuseStep 3654539 = 5481809) B5481809
theorem B37479347 : Blo 1623010 37479347 := bstep (se 1 (by rfl) ⟨28109510, by rfl⟩ : syracuseStep 37479347 = 56219021) B56219021
theorem B22217651 : Blo 1623010 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B5555123 : Blo 1623010 5555123 := bstep (se 1 (by rfl) ⟨4166342, by rfl⟩ : syracuseStep 5555123 = 8332685) B8332685
theorem B3654593 : Blo 1623010 3654593 := bstep (se 2 (by rfl) ⟨1370472, by rfl⟩ : syracuseStep 3654593 = 2740945) B2740945
theorem B1623019 : Blo 1623010 1623019 := bstep (se 1 (by rfl) ⟨1217264, by rfl⟩ : syracuseStep 1623019 = 2434529) B2434529
theorem B1623031 : Blo 1623010 1623031 := bstep (se 1 (by rfl) ⟨1217273, by rfl⟩ : syracuseStep 1623031 = 2434547) B2434547
theorem B1623051 : Blo 1623010 1623051 := bstep (se 1 (by rfl) ⟨1217288, by rfl⟩ : syracuseStep 1623051 = 2434577) B2434577
theorem B1623063 : Blo 1623010 1623063 := bstep (se 1 (by rfl) ⟨1217297, by rfl⟩ : syracuseStep 1623063 = 2434595) B2434595
theorem B1623083 : Blo 1623010 1623083 := bstep (se 1 (by rfl) ⟨1217312, by rfl⟩ : syracuseStep 1623083 = 2434625) B2434625
theorem B1623095 : Blo 1623010 1623095 := bstep (se 1 (by rfl) ⟨1217321, by rfl⟩ : syracuseStep 1623095 = 2434643) B2434643
theorem B1623115 : Blo 1623010 1623115 := bstep (se 1 (by rfl) ⟨1217336, by rfl⟩ : syracuseStep 1623115 = 2434673) B2434673
theorem B23733323 : Blo 1623010 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B1623127 : Blo 1623010 1623127 := bstep (se 1 (by rfl) ⟨1217345, by rfl⟩ : syracuseStep 1623127 = 2434691) B2434691
theorem B1623147 : Blo 1623010 1623147 := bstep (se 1 (by rfl) ⟨1217360, by rfl⟩ : syracuseStep 1623147 = 2434721) B2434721
theorem B3081331 : Blo 1623010 3081331 := bstep (se 1 (by rfl) ⟨2310998, by rfl⟩ : syracuseStep 3081331 = 4621997) B4621997
theorem B1623159 : Blo 1623010 1623159 := bstep (se 1 (by rfl) ⟨1217369, by rfl⟩ : syracuseStep 1623159 = 2434739) B2434739
theorem B1623179 : Blo 1623010 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B1623191 : Blo 1623010 1623191 := bstep (se 1 (by rfl) ⟨1217393, by rfl⟩ : syracuseStep 1623191 = 2434787) B2434787
theorem B4752535 : Blo 1623010 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B3654809 : Blo 1623010 3654809 := bstep (se 2 (by rfl) ⟨1370553, by rfl⟩ : syracuseStep 3654809 = 2741107) B2741107
theorem B1623211 : Blo 1623010 1623211 := bstep (se 1 (by rfl) ⟨1217408, by rfl⟩ : syracuseStep 1623211 = 2434817) B2434817
theorem B1623223 : Blo 1623010 1623223 := bstep (se 1 (by rfl) ⟨1217417, by rfl⟩ : syracuseStep 1623223 = 2434835) B2434835
theorem B1623243 : Blo 1623010 1623243 := bstep (se 1 (by rfl) ⟨1217432, by rfl⟩ : syracuseStep 1623243 = 2434865) B2434865
theorem B1623255 : Blo 1623010 1623255 := bstep (se 1 (by rfl) ⟨1217441, by rfl⟩ : syracuseStep 1623255 = 2434883) B2434883
theorem B1623275 : Blo 1623010 1623275 := bstep (se 1 (by rfl) ⟨1217456, by rfl⟩ : syracuseStep 1623275 = 2434913) B2434913
theorem B3654899 : Blo 1623010 3654899 := bstep (se 1 (by rfl) ⟨2741174, by rfl⟩ : syracuseStep 3654899 = 5482349) B5482349
theorem B1623287 : Blo 1623010 1623287 := bstep (se 1 (by rfl) ⟨1217465, by rfl⟩ : syracuseStep 1623287 = 2434931) B2434931
theorem B1623307 : Blo 1623010 1623307 := bstep (se 1 (by rfl) ⟨1217480, by rfl⟩ : syracuseStep 1623307 = 2434961) B2434961
theorem B1623319 : Blo 1623010 1623319 := bstep (se 1 (by rfl) ⟨1217489, by rfl⟩ : syracuseStep 1623319 = 2434979) B2434979
theorem B3654935 : Blo 1623010 3654935 := bstep (se 1 (by rfl) ⟨2741201, by rfl⟩ : syracuseStep 3654935 = 5482403) B5482403
theorem B1623339 : Blo 1623010 1623339 := bstep (se 1 (by rfl) ⟨1217504, by rfl⟩ : syracuseStep 1623339 = 2435009) B2435009
theorem B1623351 : Blo 1623010 1623351 := bstep (se 1 (by rfl) ⟨1217513, by rfl⟩ : syracuseStep 1623351 = 2435027) B2435027
theorem B12330305 : Blo 1623010 12330305 := bstep (se 2 (by rfl) ⟨4623864, by rfl⟩ : syracuseStep 12330305 = 9247729) B9247729
theorem B1623371 : Blo 1623010 1623371 := bstep (se 1 (by rfl) ⟨1217528, by rfl⟩ : syracuseStep 1623371 = 2435057) B2435057
theorem B3081559 : Blo 1623010 3081559 := bstep (se 1 (by rfl) ⟨2311169, by rfl⟩ : syracuseStep 3081559 = 4622339) B4622339
theorem B1623383 : Blo 1623010 1623383 := bstep (se 1 (by rfl) ⟨1217537, by rfl⟩ : syracuseStep 1623383 = 2435075) B2435075
theorem B1623403 : Blo 1623010 1623403 := bstep (se 1 (by rfl) ⟨1217552, by rfl⟩ : syracuseStep 1623403 = 2435105) B2435105
theorem B1623415 : Blo 1623010 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B1623435 : Blo 1623010 1623435 := bstep (se 1 (by rfl) ⟨1217576, by rfl⟩ : syracuseStep 1623435 = 2435153) B2435153
theorem B1623447 : Blo 1623010 1623447 := bstep (se 1 (by rfl) ⟨1217585, by rfl⟩ : syracuseStep 1623447 = 2435171) B2435171
theorem B1623467 : Blo 1623010 1623467 := bstep (se 1 (by rfl) ⟨1217600, by rfl⟩ : syracuseStep 1623467 = 2435201) B2435201
theorem B1623479 : Blo 1623010 1623479 := bstep (se 1 (by rfl) ⟨1217609, by rfl⟩ : syracuseStep 1623479 = 2435219) B2435219
theorem B3081665 : Blo 1623010 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B1623499 : Blo 1623010 1623499 := bstep (se 1 (by rfl) ⟨1217624, by rfl⟩ : syracuseStep 1623499 = 2435249) B2435249
theorem B3655115 : Blo 1623010 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B1623511 : Blo 1623010 1623511 := bstep (se 1 (by rfl) ⟨1217633, by rfl⟩ : syracuseStep 1623511 = 2435267) B2435267
theorem B1623531 : Blo 1623010 1623531 := bstep (se 1 (by rfl) ⟨1217648, by rfl⟩ : syracuseStep 1623531 = 2435297) B2435297
theorem B1623543 : Blo 1623010 1623543 := bstep (se 1 (by rfl) ⟨1217657, by rfl⟩ : syracuseStep 1623543 = 2435315) B2435315
theorem B2434571 : Blo 1623010 2434571 := bstep (se 1 (by rfl) ⟨1825928, by rfl⟩ : syracuseStep 2434571 = 3651857) B3651857
theorem B1623563 : Blo 1623010 1623563 := bstep (se 1 (by rfl) ⟨1217672, by rfl⟩ : syracuseStep 1623563 = 2435345) B2435345
theorem B2344459 : Blo 1623010 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B2434583 : Blo 1623010 2434583 := bstep (se 1 (by rfl) ⟨1825937, by rfl⟩ : syracuseStep 2434583 = 3651875) B3651875
theorem B1623575 : Blo 1623010 1623575 := bstep (se 1 (by rfl) ⟨1217681, by rfl⟩ : syracuseStep 1623575 = 2435363) B2435363
theorem B1623595 : Blo 1623010 1623595 := bstep (se 1 (by rfl) ⟨1217696, by rfl⟩ : syracuseStep 1623595 = 2435393) B2435393
theorem B6014515 : Blo 1623010 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B1623607 : Blo 1623010 1623607 := bstep (se 1 (by rfl) ⟨1217705, by rfl⟩ : syracuseStep 1623607 = 2435411) B2435411
theorem B1623627 : Blo 1623010 1623627 := bstep (se 1 (by rfl) ⟨1217720, by rfl⟩ : syracuseStep 1623627 = 2435441) B2435441
theorem B1623639 : Blo 1623010 1623639 := bstep (se 1 (by rfl) ⟨1217729, by rfl⟩ : syracuseStep 1623639 = 2435459) B2435459
theorem B2434649 : Blo 1623010 2434649 := bstep (se 2 (by rfl) ⟨912993, by rfl⟩ : syracuseStep 2434649 = 1825987) B1825987
theorem B3081817 : Blo 1623010 3081817 := bstep (se 2 (by rfl) ⟨1155681, by rfl⟩ : syracuseStep 3081817 = 2311363) B2311363
theorem B1623659 : Blo 1623010 1623659 := bstep (se 1 (by rfl) ⟨1217744, by rfl⟩ : syracuseStep 1623659 = 2435489) B2435489
theorem B1623671 : Blo 1623010 1623671 := bstep (se 1 (by rfl) ⟨1217753, by rfl⟩ : syracuseStep 1623671 = 2435507) B2435507
theorem B3466891 : Blo 1623010 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B1623691 : Blo 1623010 1623691 := bstep (se 1 (by rfl) ⟨1217768, by rfl⟩ : syracuseStep 1623691 = 2435537) B2435537
theorem B1623703 : Blo 1623010 1623703 := bstep (se 1 (by rfl) ⟨1217777, by rfl⟩ : syracuseStep 1623703 = 2435555) B2435555
theorem B1623723 : Blo 1623010 1623723 := bstep (se 1 (by rfl) ⟨1217792, by rfl⟩ : syracuseStep 1623723 = 2435585) B2435585
theorem B1623735 : Blo 1623010 1623735 := bstep (se 1 (by rfl) ⟨1217801, by rfl⟩ : syracuseStep 1623735 = 2435603) B2435603
theorem B2434763 : Blo 1623010 2434763 := bstep (se 1 (by rfl) ⟨1826072, by rfl⟩ : syracuseStep 2434763 = 3652145) B3652145
theorem B1623755 : Blo 1623010 1623755 := bstep (se 1 (by rfl) ⟨1217816, by rfl⟩ : syracuseStep 1623755 = 2435633) B2435633
theorem B5482187 : Blo 1623010 5482187 := bstep (se 1 (by rfl) ⟨4111640, by rfl⟩ : syracuseStep 5482187 = 8223281) B8223281
theorem B2434775 : Blo 1623010 2434775 := bstep (se 1 (by rfl) ⟨1826081, by rfl⟩ : syracuseStep 2434775 = 3652163) B3652163
theorem B1623767 : Blo 1623010 1623767 := bstep (se 1 (by rfl) ⟨1217825, by rfl⟩ : syracuseStep 1623767 = 2435651) B2435651
theorem B1623787 : Blo 1623010 1623787 := bstep (se 1 (by rfl) ⟨1217840, by rfl⟩ : syracuseStep 1623787 = 2435681) B2435681
theorem B1623799 : Blo 1623010 1623799 := bstep (se 1 (by rfl) ⟨1217849, by rfl⟩ : syracuseStep 1623799 = 2435699) B2435699
theorem B1623819 : Blo 1623010 1623819 := bstep (se 1 (by rfl) ⟨1217864, by rfl⟩ : syracuseStep 1623819 = 2435729) B2435729
theorem B1623831 : Blo 1623010 1623831 := bstep (se 1 (by rfl) ⟨1217873, by rfl⟩ : syracuseStep 1623831 = 2435747) B2435747
theorem B2434841 : Blo 1623010 2434841 := bstep (se 2 (by rfl) ⟨913065, by rfl⟩ : syracuseStep 2434841 = 1826131) B1826131
theorem B1623851 : Blo 1623010 1623851 := bstep (se 1 (by rfl) ⟨1217888, by rfl⟩ : syracuseStep 1623851 = 2435777) B2435777
theorem B1623863 : Blo 1623010 1623863 := bstep (se 1 (by rfl) ⟨1217897, by rfl⟩ : syracuseStep 1623863 = 2435795) B2435795
theorem B1623883 : Blo 1623010 1623883 := bstep (se 1 (by rfl) ⟨1217912, by rfl⟩ : syracuseStep 1623883 = 2435825) B2435825
theorem B1623895 : Blo 1623010 1623895 := bstep (se 1 (by rfl) ⟨1217921, by rfl⟩ : syracuseStep 1623895 = 2435843) B2435843
theorem B1623915 : Blo 1623010 1623915 := bstep (se 1 (by rfl) ⟨1217936, by rfl⟩ : syracuseStep 1623915 = 2435873) B2435873
theorem B1623927 : Blo 1623010 1623927 := bstep (se 1 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 1623927 = 2435891) B2435891
theorem B2434955 : Blo 1623010 2434955 := bstep (se 1 (by rfl) ⟨1826216, by rfl⟩ : syracuseStep 2434955 = 3652433) B3652433
theorem B1623947 : Blo 1623010 1623947 := bstep (se 1 (by rfl) ⟨1217960, by rfl⟩ : syracuseStep 1623947 = 2435921) B2435921
theorem B2434967 : Blo 1623010 2434967 := bstep (se 1 (by rfl) ⟨1826225, by rfl⟩ : syracuseStep 2434967 = 3652451) B3652451
theorem B1623959 : Blo 1623010 1623959 := bstep (se 1 (by rfl) ⟨1217969, by rfl⟩ : syracuseStep 1623959 = 2435939) B2435939
theorem B1623979 : Blo 1623010 1623979 := bstep (se 1 (by rfl) ⟨1217984, by rfl⟩ : syracuseStep 1623979 = 2435969) B2435969
theorem B1623991 : Blo 1623010 1623991 := bstep (se 1 (by rfl) ⟨1217993, by rfl⟩ : syracuseStep 1623991 = 2435987) B2435987
theorem B1624011 : Blo 1623010 1624011 := bstep (se 1 (by rfl) ⟨1218008, by rfl⟩ : syracuseStep 1624011 = 2436017) B2436017
theorem B2435033 : Blo 1623010 2435033 := bstep (se 2 (by rfl) ⟨913137, by rfl⟩ : syracuseStep 2435033 = 1826275) B1826275
theorem B1624023 : Blo 1623010 1624023 := bstep (se 1 (by rfl) ⟨1218017, by rfl⟩ : syracuseStep 1624023 = 2436035) B2436035
theorem B5482457 : Blo 1623010 5482457 := bstep (se 2 (by rfl) ⟨2055921, by rfl⟩ : syracuseStep 5482457 = 4111843) B4111843
theorem B1624043 : Blo 1623010 1624043 := bstep (se 1 (by rfl) ⟨1218032, by rfl⟩ : syracuseStep 1624043 = 2436065) B2436065
theorem B1624055 : Blo 1623010 1624055 := bstep (se 1 (by rfl) ⟨1218041, by rfl⟩ : syracuseStep 1624055 = 2436083) B2436083
theorem B1624075 : Blo 1623010 1624075 := bstep (se 1 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 1624075 = 2436113) B2436113
theorem B8775697 : Blo 1623010 8775697 := bstep (se 2 (by rfl) ⟨3290886, by rfl⟩ : syracuseStep 8775697 = 6581773) B6581773
theorem B1624087 : Blo 1623010 1624087 := bstep (se 1 (by rfl) ⟨1218065, by rfl⟩ : syracuseStep 1624087 = 2436131) B2436131
theorem B1624107 : Blo 1623010 1624107 := bstep (se 1 (by rfl) ⟨1218080, by rfl⟩ : syracuseStep 1624107 = 2436161) B2436161
theorem B1624119 : Blo 1623010 1624119 := bstep (se 1 (by rfl) ⟨1218089, by rfl⟩ : syracuseStep 1624119 = 2436179) B2436179
theorem B2435147 : Blo 1623010 2435147 := bstep (se 1 (by rfl) ⟨1826360, by rfl⟩ : syracuseStep 2435147 = 3652721) B3652721
theorem B10545227 : Blo 1623010 10545227 := bstep (se 1 (by rfl) ⟨7908920, by rfl⟩ : syracuseStep 10545227 = 15817841) B15817841
theorem B1624139 : Blo 1623010 1624139 := bstep (se 1 (by rfl) ⟨1218104, by rfl⟩ : syracuseStep 1624139 = 2436209) B2436209
theorem B2435159 : Blo 1623010 2435159 := bstep (se 1 (by rfl) ⟨1826369, by rfl⟩ : syracuseStep 2435159 = 3652739) B3652739
theorem B1624151 : Blo 1623010 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B1624171 : Blo 1623010 1624171 := bstep (se 1 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 1624171 = 2436257) B2436257
theorem B1624183 : Blo 1623010 1624183 := bstep (se 1 (by rfl) ⟨1218137, by rfl⟩ : syracuseStep 1624183 = 2436275) B2436275
theorem B1624203 : Blo 1623010 1624203 := bstep (se 1 (by rfl) ⟨1218152, by rfl⟩ : syracuseStep 1624203 = 2436305) B2436305
theorem B1624215 : Blo 1623010 1624215 := bstep (se 1 (by rfl) ⟨1218161, by rfl⟩ : syracuseStep 1624215 = 2436323) B2436323
theorem B2435225 : Blo 1623010 2435225 := bstep (se 2 (by rfl) ⟨913209, by rfl⟩ : syracuseStep 2435225 = 1826419) B1826419
theorem B1624235 : Blo 1623010 1624235 := bstep (se 1 (by rfl) ⟨1218176, by rfl⟩ : syracuseStep 1624235 = 2436353) B2436353
theorem B1624247 : Blo 1623010 1624247 := bstep (se 1 (by rfl) ⟨1218185, by rfl⟩ : syracuseStep 1624247 = 2436371) B2436371
theorem B1624267 : Blo 1623010 1624267 := bstep (se 1 (by rfl) ⟨1218200, by rfl⟩ : syracuseStep 1624267 = 2436401) B2436401
theorem B1624279 : Blo 1623010 1624279 := bstep (se 1 (by rfl) ⟨1218209, by rfl⟩ : syracuseStep 1624279 = 2436419) B2436419
theorem B13871321 : Blo 1623010 13871321 := bstep (se 2 (by rfl) ⟨5201745, by rfl⟩ : syracuseStep 13871321 = 10403491) B10403491
theorem B1624299 : Blo 1623010 1624299 := bstep (se 1 (by rfl) ⟨1218224, by rfl⟩ : syracuseStep 1624299 = 2436449) B2436449
theorem B1624311 : Blo 1623010 1624311 := bstep (se 1 (by rfl) ⟨1218233, by rfl⟩ : syracuseStep 1624311 = 2436467) B2436467
theorem B2435339 : Blo 1623010 2435339 := bstep (se 1 (by rfl) ⟨1826504, by rfl⟩ : syracuseStep 2435339 = 3653009) B3653009
theorem B1624331 : Blo 1623010 1624331 := bstep (se 1 (by rfl) ⟨1218248, by rfl⟩ : syracuseStep 1624331 = 2436497) B2436497
theorem B2435351 : Blo 1623010 2435351 := bstep (se 1 (by rfl) ⟨1826513, by rfl⟩ : syracuseStep 2435351 = 3653027) B3653027
theorem B1624343 : Blo 1623010 1624343 := bstep (se 1 (by rfl) ⟨1218257, by rfl⟩ : syracuseStep 1624343 = 2436515) B2436515
theorem B1624363 : Blo 1623010 1624363 := bstep (se 1 (by rfl) ⟨1218272, by rfl⟩ : syracuseStep 1624363 = 2436545) B2436545
theorem B1624375 : Blo 1623010 1624375 := bstep (se 1 (by rfl) ⟨1218281, by rfl⟩ : syracuseStep 1624375 = 2436563) B2436563
theorem B1624395 : Blo 1623010 1624395 := bstep (se 1 (by rfl) ⟨1218296, by rfl⟩ : syracuseStep 1624395 = 2436593) B2436593
theorem B1624407 : Blo 1623010 1624407 := bstep (se 1 (by rfl) ⟨1218305, by rfl⟩ : syracuseStep 1624407 = 2436611) B2436611
theorem B2435417 : Blo 1623010 2435417 := bstep (se 2 (by rfl) ⟨913281, by rfl⟩ : syracuseStep 2435417 = 1826563) B1826563
theorem B1624427 : Blo 1623010 1624427 := bstep (se 1 (by rfl) ⟨1218320, by rfl⟩ : syracuseStep 1624427 = 2436641) B2436641
theorem B1624439 : Blo 1623010 1624439 := bstep (se 1 (by rfl) ⟨1218329, by rfl⟩ : syracuseStep 1624439 = 2436659) B2436659
theorem B1624459 : Blo 1623010 1624459 := bstep (se 1 (by rfl) ⟨1218344, by rfl⟩ : syracuseStep 1624459 = 2436689) B2436689
theorem B1624471 : Blo 1623010 1624471 := bstep (se 1 (by rfl) ⟨1218353, by rfl⟩ : syracuseStep 1624471 = 2436707) B2436707
theorem B1624491 : Blo 1623010 1624491 := bstep (se 1 (by rfl) ⟨1218368, by rfl⟩ : syracuseStep 1624491 = 2436737) B2436737
theorem B4622771 : Blo 1623010 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B1624503 : Blo 1623010 1624503 := bstep (se 1 (by rfl) ⟨1218377, by rfl⟩ : syracuseStep 1624503 = 2436755) B2436755
theorem B6580673 : Blo 1623010 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B4622795 : Blo 1623010 4622795 := bstep (se 1 (by rfl) ⟨3467096, by rfl⟩ : syracuseStep 4622795 = 6934193) B6934193
theorem B2435531 : Blo 1623010 2435531 := bstep (se 1 (by rfl) ⟨1826648, by rfl⟩ : syracuseStep 2435531 = 3653297) B3653297
theorem B2435543 : Blo 1623010 2435543 := bstep (se 1 (by rfl) ⟨1826657, by rfl⟩ : syracuseStep 2435543 = 3653315) B3653315
theorem B6162905 : Blo 1623010 6162905 := bstep (se 2 (by rfl) ⟨2311089, by rfl⟩ : syracuseStep 6162905 = 4622179) B4622179
theorem B2435609 : Blo 1623010 2435609 := bstep (se 2 (by rfl) ⟨913353, by rfl⟩ : syracuseStep 2435609 = 1826707) B1826707
theorem B10406465 : Blo 1623010 10406465 := bstep (se 2 (by rfl) ⟨3902424, by rfl⟩ : syracuseStep 10406465 = 7804849) B7804849
theorem B2435723 : Blo 1623010 2435723 := bstep (se 1 (by rfl) ⟨1826792, by rfl⟩ : syracuseStep 2435723 = 3653585) B3653585
theorem B2738839 : Blo 1623010 2738839 := bstep (se 1 (by rfl) ⟨2054129, by rfl⟩ : syracuseStep 2738839 = 4108259) B4108259
theorem B2435735 : Blo 1623010 2435735 := bstep (se 1 (by rfl) ⟨1826801, by rfl⟩ : syracuseStep 2435735 = 3653603) B3653603
theorem B6933185 : Blo 1623010 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B2435801 : Blo 1623010 2435801 := bstep (se 2 (by rfl) ⟨913425, by rfl⟩ : syracuseStep 2435801 = 1826851) B1826851
theorem B31214321 : Blo 1623010 31214321 := bstep (se 2 (by rfl) ⟨11705370, by rfl⟩ : syracuseStep 31214321 = 23410741) B23410741
theorem B2435915 : Blo 1623010 2435915 := bstep (se 1 (by rfl) ⟨1826936, by rfl⟩ : syracuseStep 2435915 = 3653873) B3653873
theorem B2435927 : Blo 1623010 2435927 := bstep (se 1 (by rfl) ⟨1826945, by rfl⟩ : syracuseStep 2435927 = 3653891) B3653891
theorem B3083123 : Blo 1623010 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B2435993 : Blo 1623010 2435993 := bstep (se 2 (by rfl) ⟨913497, by rfl⟩ : syracuseStep 2435993 = 1826995) B1826995
theorem B3468275 : Blo 1623010 3468275 := bstep (se 1 (by rfl) ⟨2601206, by rfl⟩ : syracuseStep 3468275 = 5202413) B5202413
theorem B2436107 : Blo 1623010 2436107 := bstep (se 1 (by rfl) ⟨1827080, by rfl⟩ : syracuseStep 2436107 = 3654161) B3654161
theorem B3083275 : Blo 1623010 3083275 := bstep (se 1 (by rfl) ⟨2312456, by rfl⟩ : syracuseStep 3083275 = 4624913) B4624913
theorem B2436119 : Blo 1623010 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B5491763 : Blo 1623010 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B5852225 : Blo 1623010 5852225 := bstep (se 2 (by rfl) ⟨2194584, by rfl⟩ : syracuseStep 5852225 = 4389169) B4389169
theorem B3468377 : Blo 1623010 3468377 := bstep (se 2 (by rfl) ⟨1300641, by rfl⟩ : syracuseStep 3468377 = 2601283) B2601283
theorem B2436185 : Blo 1623010 2436185 := bstep (se 2 (by rfl) ⟨913569, by rfl⟩ : syracuseStep 2436185 = 1827139) B1827139
theorem B2436299 : Blo 1623010 2436299 := bstep (se 1 (by rfl) ⟨1827224, by rfl⟩ : syracuseStep 2436299 = 3654449) B3654449
theorem B2436311 : Blo 1623010 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B12332249 : Blo 1623010 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B4623581 : Blo 1623010 4623581 := bstep (se 3 (by rfl) ⟨866921, by rfl⟩ : syracuseStep 4623581 = 1733843) B1733843
theorem B2739467 : Blo 1623010 2739467 := bstep (se 1 (by rfl) ⟨2054600, by rfl⟩ : syracuseStep 2739467 = 4109201) B4109201
theorem B2436377 : Blo 1623010 2436377 := bstep (se 2 (by rfl) ⟨913641, by rfl⟩ : syracuseStep 2436377 = 1827283) B1827283
theorem B3083609 : Blo 1623010 3083609 := bstep (se 2 (by rfl) ⟨1156353, by rfl⟩ : syracuseStep 3083609 = 2312707) B2312707
theorem B2739595 : Blo 1623010 2739595 := bstep (se 1 (by rfl) ⟨2054696, by rfl⟩ : syracuseStep 2739595 = 4109393) B4109393
theorem B2436491 : Blo 1623010 2436491 := bstep (se 1 (by rfl) ⟨1827368, by rfl⟩ : syracuseStep 2436491 = 3654737) B3654737
theorem B2436503 : Blo 1623010 2436503 := bstep (se 1 (by rfl) ⟨1827377, by rfl⟩ : syracuseStep 2436503 = 3654755) B3654755
theorem B3468737 : Blo 1623010 3468737 := bstep (se 2 (by rfl) ⟨1300776, by rfl⟩ : syracuseStep 3468737 = 2601553) B2601553
theorem B2436569 : Blo 1623010 2436569 := bstep (se 2 (by rfl) ⟨913713, by rfl⟩ : syracuseStep 2436569 = 1827427) B1827427
theorem B2739737 : Blo 1623010 2739737 := bstep (se 2 (by rfl) ⟨1027401, by rfl⟩ : syracuseStep 2739737 = 2054803) B2054803
theorem B2436683 : Blo 1623010 2436683 := bstep (se 1 (by rfl) ⟨1827512, by rfl⟩ : syracuseStep 2436683 = 3655025) B3655025
theorem B2436695 : Blo 1623010 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B11701853 : Blo 1623010 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B2739865 : Blo 1623010 2739865 := bstep (se 2 (by rfl) ⟨1027449, by rfl⟩ : syracuseStep 2739865 = 2054899) B2054899
theorem B2436761 : Blo 1623010 2436761 := bstep (se 2 (by rfl) ⟨913785, by rfl⟩ : syracuseStep 2436761 = 1827571) B1827571
theorem B3903155 : Blo 1623010 3903155 := bstep (se 1 (by rfl) ⟨2927366, by rfl⟩ : syracuseStep 3903155 = 5854733) B5854733
theorem B7032541 : Blo 1623010 7032541 := bstep (se 3 (by rfl) ⟨1318601, by rfl⟩ : syracuseStep 7032541 = 2637203) B2637203
theorem B7409497 : Blo 1623010 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B8220689 : Blo 1623010 8220689 := bstep (se 2 (by rfl) ⟨3082758, by rfl⟩ : syracuseStep 8220689 = 6165517) B6165517
theorem B6164531 : Blo 1623010 6164531 := bstep (se 1 (by rfl) ⟨4623398, by rfl⟩ : syracuseStep 6164531 = 9246797) B9246797
theorem B6164545 : Blo 1623010 6164545 := bstep (se 2 (by rfl) ⟨2311704, by rfl⟩ : syracuseStep 6164545 = 4623409) B4623409
theorem B11260055 : Blo 1623010 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B3469463 : Blo 1623010 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B8220851 : Blo 1623010 8220851 := bstep (se 1 (by rfl) ⟨6165638, by rfl⟩ : syracuseStep 8220851 = 12331277) B12331277
theorem B2601175 : Blo 1623010 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2740439 : Blo 1623010 2740439 := bstep (se 1 (by rfl) ⟨2055329, by rfl⟩ : syracuseStep 2740439 = 4110659) B4110659
theorem B6582551 : Blo 1623010 6582551 := bstep (se 1 (by rfl) ⟨4936913, by rfl⟩ : syracuseStep 6582551 = 9873827) B9873827
theorem B2740567 : Blo 1623010 2740567 := bstep (se 1 (by rfl) ⟨2055425, by rfl⟩ : syracuseStep 2740567 = 4110851) B4110851
theorem B46289765 : Blo 1623010 46289765 := bstep (se 4 (by rfl) ⟨4339665, by rfl⟩ : syracuseStep 46289765 = 8679331) B8679331
theorem B2741195 : Blo 1623010 2741195 := bstep (se 1 (by rfl) ⟨2055896, by rfl⟩ : syracuseStep 2741195 = 4111793) B4111793
theorem B4625369 : Blo 1623010 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B4109363 : Blo 1623010 4109363 := bstep (se 1 (by rfl) ⟨3082022, by rfl⟩ : syracuseStep 4109363 = 6164045) B6164045
theorem B9245771 : Blo 1623010 9245771 := bstep (se 1 (by rfl) ⟨6934328, by rfl⟩ : syracuseStep 9245771 = 13868657) B13868657
theorem B2741323 : Blo 1623010 2741323 := bstep (se 1 (by rfl) ⟨2055992, by rfl⟩ : syracuseStep 2741323 = 4111985) B4111985
theorem B1733719 : Blo 1623010 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B6935645 : Blo 1623010 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B4625687 : Blo 1623010 4625687 := bstep (se 1 (by rfl) ⟨3469265, by rfl⟩ : syracuseStep 4625687 = 6938531) B6938531
theorem B6346129 : Blo 1623010 6346129 := bstep (se 2 (by rfl) ⟨2379798, by rfl⟩ : syracuseStep 6346129 = 4759597) B4759597
theorem B3954071 : Blo 1623010 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B12326417 : Blo 1623010 12326417 := bstep (se 2 (by rfl) ⟨4622406, by rfl⟩ : syracuseStep 12326417 = 9244813) B9244813
theorem B4109899 : Blo 1623010 4109899 := bstep (se 1 (by rfl) ⟨3082424, by rfl⟩ : syracuseStep 4109899 = 6164849) B6164849
theorem B14816843 : Blo 1623010 14816843 := bstep (se 1 (by rfl) ⟨11112632, by rfl⟩ : syracuseStep 14816843 = 22225265) B22225265
theorem B13866673 : Blo 1623010 13866673 := bstep (se 2 (by rfl) ⟨5200002, by rfl⟩ : syracuseStep 13866673 = 10400005) B10400005
theorem B5273267 : Blo 1623010 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B4110041 : Blo 1623010 4110041 := bstep (se 2 (by rfl) ⟨1541265, by rfl⟩ : syracuseStep 4110041 = 3082531) B3082531
theorem B3290881 : Blo 1623010 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B11106065 : Blo 1623010 11106065 := bstep (se 2 (by rfl) ⟨4164774, by rfl⟩ : syracuseStep 11106065 = 8329549) B8329549
theorem B1734539 : Blo 1623010 1734539 := bstep (se 1 (by rfl) ⟨1300904, by rfl⟩ : syracuseStep 1734539 = 2601809) B2601809
theorem B6166475 : Blo 1623010 6166475 := bstep (se 1 (by rfl) ⟨4624856, by rfl⟩ : syracuseStep 6166475 = 9249713) B9249713
theorem B6166489 : Blo 1623010 6166489 := bstep (se 2 (by rfl) ⟨2312433, by rfl⟩ : syracuseStep 6166489 = 4624867) B4624867
theorem B2054155 : Blo 1623010 2054155 := bstep (se 1 (by rfl) ⟨1540616, by rfl⟩ : syracuseStep 2054155 = 3081233) B3081233
theorem B3291211 : Blo 1623010 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B42195019 : Blo 1623010 42195019 := bstep (se 1 (by rfl) ⟨31646264, by rfl⟩ : syracuseStep 42195019 = 63292529) B63292529
theorem B8222795 : Blo 1623010 8222795 := bstep (se 1 (by rfl) ⟨6167096, by rfl⟩ : syracuseStep 8222795 = 12334193) B12334193
theorem B3954839 : Blo 1623010 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B13162769 : Blo 1623010 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B2054423 : Blo 1623010 2054423 := bstep (se 1 (by rfl) ⟨1540817, by rfl⟩ : syracuseStep 2054423 = 3081635) B3081635
theorem B5478731 : Blo 1623010 5478731 := bstep (se 1 (by rfl) ⟨4109048, by rfl⟩ : syracuseStep 5478731 = 8218097) B8218097
theorem B3651929 : Blo 1623010 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B3652019 : Blo 1623010 3652019 := bstep (se 1 (by rfl) ⟨2739014, by rfl⟩ : syracuseStep 3652019 = 5478029) B5478029
theorem B3652055 : Blo 1623010 3652055 := bstep (se 1 (by rfl) ⟨2739041, by rfl⟩ : syracuseStep 3652055 = 5478083) B5478083
theorem B4110871 : Blo 1623010 4110871 := bstep (se 1 (by rfl) ⟨3083153, by rfl⟩ : syracuseStep 4110871 = 6166307) B6166307
theorem B12335651 : Blo 1623010 12335651 := bstep (se 1 (by rfl) ⟨9251738, by rfl⟩ : syracuseStep 12335651 = 18503477) B18503477
theorem B27753029 : Blo 1623010 27753029 := bstep (se 4 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 27753029 = 5203693) B5203693
theorem B5479001 : Blo 1623010 5479001 := bstep (se 2 (by rfl) ⟨2054625, by rfl⟩ : syracuseStep 5479001 = 4109251) B4109251
theorem B3652235 : Blo 1623010 3652235 := bstep (se 1 (by rfl) ⟨2739176, by rfl⟩ : syracuseStep 3652235 = 5478353) B5478353
theorem B10541747 : Blo 1623010 10541747 := bstep (se 1 (by rfl) ⟨7906310, by rfl⟩ : syracuseStep 10541747 = 15812621) B15812621
theorem B3652289 : Blo 1623010 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B3005185 : Blo 1623010 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B6167447 : Blo 1623010 6167447 := bstep (se 1 (by rfl) ⟨4625585, by rfl⟩ : syracuseStep 6167447 = 9251171) B9251171
theorem B3652505 : Blo 1623010 3652505 := bstep (se 2 (by rfl) ⟨1369689, by rfl⟩ : syracuseStep 3652505 = 2739379) B2739379
theorem B3955649 : Blo 1623010 3955649 := bstep (se 2 (by rfl) ⟨1483368, by rfl⟩ : syracuseStep 3955649 = 2966737) B2966737
theorem B4111307 : Blo 1623010 4111307 := bstep (se 1 (by rfl) ⟨3083480, by rfl⟩ : syracuseStep 4111307 = 6166961) B6166961
theorem B2055127 : Blo 1623010 2055127 := bstep (se 1 (by rfl) ⟨1541345, by rfl⟩ : syracuseStep 2055127 = 3082691) B3082691
theorem B3652595 : Blo 1623010 3652595 := bstep (se 1 (by rfl) ⟨2739446, by rfl⟩ : syracuseStep 3652595 = 5478893) B5478893
theorem B3652631 : Blo 1623010 3652631 := bstep (se 1 (by rfl) ⟨2739473, by rfl⟩ : syracuseStep 3652631 = 5478947) B5478947
theorem B1645655 : Blo 1623010 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1645687 : Blo 1623010 1645687 := bstep (se 1 (by rfl) ⟨1234265, by rfl⟩ : syracuseStep 1645687 = 2468531) B2468531
theorem B4685003 : Blo 1623010 4685003 := bstep (se 1 (by rfl) ⟨3513752, by rfl⟩ : syracuseStep 4685003 = 7027505) B7027505
theorem B3652811 : Blo 1623010 3652811 := bstep (se 1 (by rfl) ⟨2739608, by rfl⟩ : syracuseStep 3652811 = 5479217) B5479217
theorem B3652865 : Blo 1623010 3652865 := bstep (se 2 (by rfl) ⟨1369824, by rfl⟩ : syracuseStep 3652865 = 2739649) B2739649
theorem B1826059 : Blo 1623010 1826059 := bstep (se 1 (by rfl) ⟨1369544, by rfl⟩ : syracuseStep 1826059 = 2739089) B2739089
theorem B5479703 : Blo 1623010 5479703 := bstep (se 1 (by rfl) ⟨4109777, by rfl⟩ : syracuseStep 5479703 = 8219555) B8219555
theorem B4750643 : Blo 1623010 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B4111681 : Blo 1623010 4111681 := bstep (se 2 (by rfl) ⟨1541880, by rfl⟩ : syracuseStep 4111681 = 3083761) B3083761
theorem B4685131 : Blo 1623010 4685131 := bstep (se 1 (by rfl) ⟨3513848, by rfl⟩ : syracuseStep 4685131 = 7027697) B7027697
theorem B1826167 : Blo 1623010 1826167 := bstep (se 1 (by rfl) ⟨1369625, by rfl⟩ : syracuseStep 1826167 = 2739251) B2739251
theorem B3653081 : Blo 1623010 3653081 := bstep (se 2 (by rfl) ⟨1369905, by rfl⟩ : syracuseStep 3653081 = 2739811) B2739811
theorem B6250007 : Blo 1623010 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B1826347 : Blo 1623010 1826347 := bstep (se 1 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 1826347 = 2739521) B2739521
theorem B3653171 : Blo 1623010 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B3653207 : Blo 1623010 3653207 := bstep (se 1 (by rfl) ⟨2739905, by rfl⟩ : syracuseStep 3653207 = 5479811) B5479811
theorem B6938243 : Blo 1623010 6938243 := bstep (se 1 (by rfl) ⟨5203682, by rfl⟩ : syracuseStep 6938243 = 10407365) B10407365
theorem B1826455 : Blo 1623010 1826455 := bstep (se 1 (by rfl) ⟨1369841, by rfl⟩ : syracuseStep 1826455 = 2739683) B2739683
theorem B7028417 : Blo 1623010 7028417 := bstep (se 2 (by rfl) ⟨2635656, by rfl⟩ : syracuseStep 7028417 = 5271313) B5271313
theorem B3653387 : Blo 1623010 3653387 := bstep (se 1 (by rfl) ⟨2740040, by rfl⟩ : syracuseStep 3653387 = 5480081) B5480081
theorem B5480243 : Blo 1623010 5480243 := bstep (se 1 (by rfl) ⟨4110182, by rfl⟩ : syracuseStep 5480243 = 8220365) B8220365
theorem B3653441 : Blo 1623010 3653441 := bstep (se 2 (by rfl) ⟨1370040, by rfl⟩ : syracuseStep 3653441 = 2740081) B2740081
theorem B1826635 : Blo 1623010 1826635 := bstep (se 1 (by rfl) ⟨1369976, by rfl⟩ : syracuseStep 1826635 = 2739953) B2739953
theorem B1826743 : Blo 1623010 1826743 := bstep (se 1 (by rfl) ⟨1370057, by rfl⟩ : syracuseStep 1826743 = 2740115) B2740115
theorem B10403801 : Blo 1623010 10403801 := bstep (se 2 (by rfl) ⟨3901425, by rfl⟩ : syracuseStep 10403801 = 7802851) B7802851
theorem B5480459 : Blo 1623010 5480459 := bstep (se 1 (by rfl) ⟨4110344, by rfl⟩ : syracuseStep 5480459 = 8220689) B8220689
theorem B3653675 : Blo 1623010 3653675 := bstep (se 1 (by rfl) ⟨2740256, by rfl⟩ : syracuseStep 3653675 = 5480513) B5480513
theorem B5480567 : Blo 1623010 5480567 := bstep (se 1 (by rfl) ⟨4110425, by rfl⟩ : syracuseStep 5480567 = 8220851) B8220851
theorem B1826959 : Blo 1623010 1826959 := bstep (se 1 (by rfl) ⟨1370219, by rfl⟩ : syracuseStep 1826959 = 2740439) B2740439
theorem B9249005 : Blo 1623010 9249005 := bstep (se 3 (by rfl) ⟨1734188, by rfl⟩ : syracuseStep 9249005 = 3468377) B3468377
theorem B70213877 : Blo 1623010 70213877 := bstep (se 5 (by rfl) ⟨3291275, by rfl⟩ : syracuseStep 70213877 = 6582551) B6582551
theorem B3654035 : Blo 1623010 3654035 := bstep (se 1 (by rfl) ⟨2740526, by rfl⟩ : syracuseStep 3654035 = 5481053) B5481053
theorem B3654089 : Blo 1623010 3654089 := bstep (se 2 (by rfl) ⟨1370283, by rfl⟩ : syracuseStep 3654089 = 2740567) B2740567
theorem B24986231 : Blo 1623010 24986231 := bstep (se 1 (by rfl) ⟨18739673, by rfl⟩ : syracuseStep 24986231 = 37479347) B37479347
theorem B14811767 : Blo 1623010 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B3703415 : Blo 1623010 3703415 := bstep (se 1 (by rfl) ⟨2777561, by rfl⟩ : syracuseStep 3703415 = 5555123) B5555123
theorem B1827463 : Blo 1623010 1827463 := bstep (se 1 (by rfl) ⟨1370597, by rfl⟩ : syracuseStep 1827463 = 2741195) B2741195
theorem B5481161 : Blo 1623010 5481161 := bstep (se 2 (by rfl) ⟨2055435, by rfl⟩ : syracuseStep 5481161 = 4110871) B4110871
theorem B4006913 : Blo 1623010 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B1623047 : Blo 1623010 1623047 := bstep (se 1 (by rfl) ⟨1217285, by rfl⟩ : syracuseStep 1623047 = 2434571) B2434571
theorem B8217611 : Blo 1623010 8217611 := bstep (se 1 (by rfl) ⟨6163208, by rfl⟩ : syracuseStep 8217611 = 12326417) B12326417
theorem B1623055 : Blo 1623010 1623055 := bstep (se 1 (by rfl) ⟨1217291, by rfl⟩ : syracuseStep 1623055 = 2434583) B2434583
theorem B1623099 : Blo 1623010 1623099 := bstep (se 1 (by rfl) ⟨1217324, by rfl⟩ : syracuseStep 1623099 = 2434649) B2434649
theorem B1623175 : Blo 1623010 1623175 := bstep (se 1 (by rfl) ⟨1217381, by rfl⟩ : syracuseStep 1623175 = 2434763) B2434763
theorem B3654791 : Blo 1623010 3654791 := bstep (se 1 (by rfl) ⟨2741093, by rfl⟩ : syracuseStep 3654791 = 5482187) B5482187
theorem B1623183 : Blo 1623010 1623183 := bstep (se 1 (by rfl) ⟨1217387, by rfl⟩ : syracuseStep 1623183 = 2434775) B2434775
theorem B8217773 : Blo 1623010 8217773 := bstep (se 3 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 8217773 = 3081665) B3081665
theorem B1623227 : Blo 1623010 1623227 := bstep (se 1 (by rfl) ⟨1217420, by rfl⟩ : syracuseStep 1623227 = 2434841) B2434841
theorem B1623303 : Blo 1623010 1623303 := bstep (se 1 (by rfl) ⟨1217477, by rfl⟩ : syracuseStep 1623303 = 2434955) B2434955
theorem B1623311 : Blo 1623010 1623311 := bstep (se 1 (by rfl) ⟨1217483, by rfl⟩ : syracuseStep 1623311 = 2434967) B2434967
theorem B1623355 : Blo 1623010 1623355 := bstep (se 1 (by rfl) ⟨1217516, by rfl⟩ : syracuseStep 1623355 = 2435033) B2435033
theorem B3654971 : Blo 1623010 3654971 := bstep (se 1 (by rfl) ⟨2741228, by rfl⟩ : syracuseStep 3654971 = 5482457) B5482457
theorem B1623431 : Blo 1623010 1623431 := bstep (se 1 (by rfl) ⟨1217573, by rfl⟩ : syracuseStep 1623431 = 2435147) B2435147
theorem B7030151 : Blo 1623010 7030151 := bstep (se 1 (by rfl) ⟨5272613, by rfl⟩ : syracuseStep 7030151 = 10545227) B10545227
theorem B5481863 : Blo 1623010 5481863 := bstep (se 1 (by rfl) ⟨4111397, by rfl⟩ : syracuseStep 5481863 = 8222795) B8222795
theorem B1623439 : Blo 1623010 1623439 := bstep (se 1 (by rfl) ⟨1217579, by rfl⟩ : syracuseStep 1623439 = 2435159) B2435159
theorem B3655097 : Blo 1623010 3655097 := bstep (se 2 (by rfl) ⟨1370661, by rfl⟩ : syracuseStep 3655097 = 2741323) B2741323
theorem B1623483 : Blo 1623010 1623483 := bstep (se 1 (by rfl) ⟨1217612, by rfl⟩ : syracuseStep 1623483 = 2435225) B2435225
theorem B2311625 : Blo 1623010 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B1623559 : Blo 1623010 1623559 := bstep (se 1 (by rfl) ⟨1217669, by rfl⟩ : syracuseStep 1623559 = 2435339) B2435339
theorem B8775179 : Blo 1623010 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1623567 : Blo 1623010 1623567 := bstep (se 1 (by rfl) ⟨1217675, by rfl⟩ : syracuseStep 1623567 = 2435351) B2435351
theorem B2434619 : Blo 1623010 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B1623611 : Blo 1623010 1623611 := bstep (se 1 (by rfl) ⟨1217708, by rfl⟩ : syracuseStep 1623611 = 2435417) B2435417
theorem B2434679 : Blo 1623010 2434679 := bstep (se 1 (by rfl) ⟨1826009, by rfl⟩ : syracuseStep 2434679 = 3652019) B3652019
theorem B3081863 : Blo 1623010 3081863 := bstep (se 1 (by rfl) ⟨2311397, by rfl⟩ : syracuseStep 3081863 = 4622795) B4622795
theorem B1623687 : Blo 1623010 1623687 := bstep (se 1 (by rfl) ⟨1217765, by rfl⟩ : syracuseStep 1623687 = 2435531) B2435531
theorem B2434703 : Blo 1623010 2434703 := bstep (se 1 (by rfl) ⟨1826027, by rfl⟩ : syracuseStep 2434703 = 3652055) B3652055
theorem B1623695 : Blo 1623010 1623695 := bstep (se 1 (by rfl) ⟨1217771, by rfl⟩ : syracuseStep 1623695 = 2435543) B2435543
theorem B2434745 : Blo 1623010 2434745 := bstep (se 2 (by rfl) ⟨913029, by rfl⟩ : syracuseStep 2434745 = 1826059) B1826059
theorem B1623739 : Blo 1623010 1623739 := bstep (se 1 (by rfl) ⟨1217804, by rfl⟩ : syracuseStep 1623739 = 2435609) B2435609
theorem B24987365 : Blo 1623010 24987365 := bstep (se 4 (by rfl) ⟨2342565, by rfl⟩ : syracuseStep 24987365 = 4685131) B4685131
theorem B5482241 : Blo 1623010 5482241 := bstep (se 2 (by rfl) ⟨2055840, by rfl⟩ : syracuseStep 5482241 = 4111681) B4111681
theorem B2434823 : Blo 1623010 2434823 := bstep (se 1 (by rfl) ⟨1826117, by rfl⟩ : syracuseStep 2434823 = 3652235) B3652235
theorem B1623815 : Blo 1623010 1623815 := bstep (se 1 (by rfl) ⟨1217861, by rfl⟩ : syracuseStep 1623815 = 2435723) B2435723
theorem B1623823 : Blo 1623010 1623823 := bstep (se 1 (by rfl) ⟨1217867, by rfl⟩ : syracuseStep 1623823 = 2435735) B2435735
theorem B4622123 : Blo 1623010 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B2434859 : Blo 1623010 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B1623867 : Blo 1623010 1623867 := bstep (se 1 (by rfl) ⟨1217900, by rfl⟩ : syracuseStep 1623867 = 2435801) B2435801
theorem B2434889 : Blo 1623010 2434889 := bstep (se 2 (by rfl) ⟨913083, by rfl⟩ : syracuseStep 2434889 = 1826167) B1826167
theorem B20809547 : Blo 1623010 20809547 := bstep (se 1 (by rfl) ⟨15607160, by rfl⟩ : syracuseStep 20809547 = 31214321) B31214321
theorem B1623943 : Blo 1623010 1623943 := bstep (se 1 (by rfl) ⟨1217957, by rfl⟩ : syracuseStep 1623943 = 2435915) B2435915
theorem B1623951 : Blo 1623010 1623951 := bstep (se 1 (by rfl) ⟨1217963, by rfl⟩ : syracuseStep 1623951 = 2435927) B2435927
theorem B2435003 : Blo 1623010 2435003 := bstep (se 1 (by rfl) ⟨1826252, by rfl⟩ : syracuseStep 2435003 = 3652505) B3652505
theorem B1623995 : Blo 1623010 1623995 := bstep (se 1 (by rfl) ⟨1217996, by rfl⟩ : syracuseStep 1623995 = 2435993) B2435993
theorem B2435063 : Blo 1623010 2435063 := bstep (se 1 (by rfl) ⟨1826297, by rfl⟩ : syracuseStep 2435063 = 3652595) B3652595
theorem B2312183 : Blo 1623010 2312183 := bstep (se 1 (by rfl) ⟨1734137, by rfl⟩ : syracuseStep 2312183 = 3468275) B3468275
theorem B1624071 : Blo 1623010 1624071 := bstep (se 1 (by rfl) ⟨1218053, by rfl⟩ : syracuseStep 1624071 = 2436107) B2436107
theorem B2435087 : Blo 1623010 2435087 := bstep (se 1 (by rfl) ⟨1826315, by rfl⟩ : syracuseStep 2435087 = 3652631) B3652631
theorem B1624079 : Blo 1623010 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B3901483 : Blo 1623010 3901483 := bstep (se 1 (by rfl) ⟨2926112, by rfl⟩ : syracuseStep 3901483 = 5852225) B5852225
theorem B2435129 : Blo 1623010 2435129 := bstep (se 2 (by rfl) ⟨913173, by rfl⟩ : syracuseStep 2435129 = 1826347) B1826347
theorem B1624123 : Blo 1623010 1624123 := bstep (se 1 (by rfl) ⟨1218092, by rfl⟩ : syracuseStep 1624123 = 2436185) B2436185
theorem B3123335 : Blo 1623010 3123335 := bstep (se 1 (by rfl) ⟨2342501, by rfl⟩ : syracuseStep 3123335 = 4685003) B4685003
theorem B2435207 : Blo 1623010 2435207 := bstep (se 1 (by rfl) ⟨1826405, by rfl⟩ : syracuseStep 2435207 = 3652811) B3652811
theorem B1624199 : Blo 1623010 1624199 := bstep (se 1 (by rfl) ⟨1218149, by rfl⟩ : syracuseStep 1624199 = 2436299) B2436299
theorem B1624207 : Blo 1623010 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B3082387 : Blo 1623010 3082387 := bstep (se 1 (by rfl) ⟨2311790, by rfl⟩ : syracuseStep 3082387 = 4623581) B4623581
theorem B2435243 : Blo 1623010 2435243 := bstep (se 1 (by rfl) ⟨1826432, by rfl⟩ : syracuseStep 2435243 = 3652865) B3652865
theorem B4622521 : Blo 1623010 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B1624251 : Blo 1623010 1624251 := bstep (se 1 (by rfl) ⟨1218188, by rfl⟩ : syracuseStep 1624251 = 2436377) B2436377
theorem B2435273 : Blo 1623010 2435273 := bstep (se 2 (by rfl) ⟨913227, by rfl⟩ : syracuseStep 2435273 = 1826455) B1826455
theorem B1624327 : Blo 1623010 1624327 := bstep (se 1 (by rfl) ⟨1218245, by rfl⟩ : syracuseStep 1624327 = 2436491) B2436491
theorem B123439373 : Blo 1623010 123439373 := bstep (se 3 (by rfl) ⟨23144882, by rfl⟩ : syracuseStep 123439373 = 46289765) B46289765
theorem B1624335 : Blo 1623010 1624335 := bstep (se 1 (by rfl) ⟨1218251, by rfl⟩ : syracuseStep 1624335 = 2436503) B2436503
theorem B2312491 : Blo 1623010 2312491 := bstep (se 1 (by rfl) ⟨1734368, by rfl⟩ : syracuseStep 2312491 = 3468737) B3468737
theorem B2435387 : Blo 1623010 2435387 := bstep (se 1 (by rfl) ⟨1826540, by rfl⟩ : syracuseStep 2435387 = 3653081) B3653081
theorem B1624379 : Blo 1623010 1624379 := bstep (se 1 (by rfl) ⟨1218284, by rfl⟩ : syracuseStep 1624379 = 2436569) B2436569
theorem B2435447 : Blo 1623010 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B1624455 : Blo 1623010 1624455 := bstep (se 1 (by rfl) ⟨1218341, by rfl⟩ : syracuseStep 1624455 = 2436683) B2436683
theorem B2435471 : Blo 1623010 2435471 := bstep (se 1 (by rfl) ⟨1826603, by rfl⟩ : syracuseStep 2435471 = 3653207) B3653207
theorem B1624463 : Blo 1623010 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B7801235 : Blo 1623010 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B2435513 : Blo 1623010 2435513 := bstep (se 2 (by rfl) ⟨913317, by rfl⟩ : syracuseStep 2435513 = 1826635) B1826635
theorem B1624507 : Blo 1623010 1624507 := bstep (se 1 (by rfl) ⟨1218380, by rfl⟩ : syracuseStep 1624507 = 2436761) B2436761
theorem B2435591 : Blo 1623010 2435591 := bstep (se 1 (by rfl) ⟨1826693, by rfl⟩ : syracuseStep 2435591 = 3653387) B3653387
theorem B2435627 : Blo 1623010 2435627 := bstep (se 1 (by rfl) ⟨1826720, by rfl⟩ : syracuseStep 2435627 = 3653441) B3653441
theorem B2435657 : Blo 1623010 2435657 := bstep (se 2 (by rfl) ⟨913371, by rfl⟩ : syracuseStep 2435657 = 1826743) B1826743
theorem B2738873 : Blo 1623010 2738873 := bstep (se 2 (by rfl) ⟨1027077, by rfl⟩ : syracuseStep 2738873 = 2054155) B2054155
theorem B2435771 : Blo 1623010 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B11700929 : Blo 1623010 11700929 := bstep (se 2 (by rfl) ⟨4387848, by rfl⟩ : syracuseStep 11700929 = 8775697) B8775697
theorem B2435831 : Blo 1623010 2435831 := bstep (se 1 (by rfl) ⟨1826873, by rfl⟩ : syracuseStep 2435831 = 3653747) B3653747
theorem B8219393 : Blo 1623010 8219393 := bstep (se 2 (by rfl) ⟨3082272, by rfl⟩ : syracuseStep 8219393 = 6164545) B6164545
theorem B7506703 : Blo 1623010 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B2435855 : Blo 1623010 2435855 := bstep (se 1 (by rfl) ⟨1826891, by rfl⟩ : syracuseStep 2435855 = 3653783) B3653783
theorem B2312975 : Blo 1623010 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B2435897 : Blo 1623010 2435897 := bstep (se 2 (by rfl) ⟨913461, by rfl⟩ : syracuseStep 2435897 = 1826923) B1826923
theorem B2435975 : Blo 1623010 2435975 := bstep (se 1 (by rfl) ⟨1826981, by rfl⟩ : syracuseStep 2435975 = 3653963) B3653963
theorem B2436011 : Blo 1623010 2436011 := bstep (se 1 (by rfl) ⟨1827008, by rfl⟩ : syracuseStep 2436011 = 3654017) B3654017
theorem B3468233 : Blo 1623010 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B2436041 : Blo 1623010 2436041 := bstep (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) B1827031
theorem B2436155 : Blo 1623010 2436155 := bstep (se 1 (by rfl) ⟨1827116, by rfl⟩ : syracuseStep 2436155 = 3654233) B3654233
theorem B10546237 : Blo 1623010 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B2436215 : Blo 1623010 2436215 := bstep (se 1 (by rfl) ⟨1827161, by rfl⟩ : syracuseStep 2436215 = 3654323) B3654323
theorem B2436239 : Blo 1623010 2436239 := bstep (se 1 (by rfl) ⟨1827179, by rfl⟩ : syracuseStep 2436239 = 3654359) B3654359
theorem B2436281 : Blo 1623010 2436281 := bstep (se 2 (by rfl) ⟨913605, by rfl⟩ : syracuseStep 2436281 = 1827211) B1827211
theorem B2436359 : Blo 1623010 2436359 := bstep (se 1 (by rfl) ⟨1827269, by rfl⟩ : syracuseStep 2436359 = 3654539) B3654539
theorem B8776997 : Blo 1623010 8776997 := bstep (se 4 (by rfl) ⟨822843, by rfl⟩ : syracuseStep 8776997 = 1645687) B1645687
theorem B2436395 : Blo 1623010 2436395 := bstep (se 1 (by rfl) ⟨1827296, by rfl⟩ : syracuseStep 2436395 = 3654593) B3654593
theorem B3083579 : Blo 1623010 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B2436425 : Blo 1623010 2436425 := bstep (se 2 (by rfl) ⟨913659, by rfl⟩ : syracuseStep 2436425 = 1827319) B1827319
theorem B2739575 : Blo 1623010 2739575 := bstep (se 1 (by rfl) ⟨2054681, by rfl⟩ : syracuseStep 2739575 = 4109363) B4109363
theorem B6163847 : Blo 1623010 6163847 := bstep (se 1 (by rfl) ⟨4622885, by rfl⟩ : syracuseStep 6163847 = 9245771) B9245771
theorem B15822215 : Blo 1623010 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B4623763 : Blo 1623010 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B2436539 : Blo 1623010 2436539 := bstep (se 1 (by rfl) ⟨1827404, by rfl⟩ : syracuseStep 2436539 = 3654809) B3654809
theorem B2436599 : Blo 1623010 2436599 := bstep (se 1 (by rfl) ⟨1827449, by rfl⟩ : syracuseStep 2436599 = 3654899) B3654899
theorem B2436623 : Blo 1623010 2436623 := bstep (se 1 (by rfl) ⟨1827467, by rfl⟩ : syracuseStep 2436623 = 3654935) B3654935
theorem B8220203 : Blo 1623010 8220203 := bstep (se 1 (by rfl) ⟨6165152, by rfl⟩ : syracuseStep 8220203 = 12330305) B12330305
theorem B2436665 : Blo 1623010 2436665 := bstep (se 2 (by rfl) ⟨913749, by rfl⟩ : syracuseStep 2436665 = 1827499) B1827499
theorem B2436743 : Blo 1623010 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B2740027 : Blo 1623010 2740027 := bstep (se 1 (by rfl) ⟨2055020, by rfl⟩ : syracuseStep 2740027 = 4110041) B4110041
theorem B2740169 : Blo 1623010 2740169 := bstep (se 2 (by rfl) ⟨1027563, by rfl⟩ : syracuseStep 2740169 = 2055127) B2055127
theorem B4108441 : Blo 1623010 4108441 := bstep (se 2 (by rfl) ⟨1540665, by rfl⟩ : syracuseStep 4108441 = 3081331) B3081331
theorem B6336713 : Blo 1623010 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B4387115 : Blo 1623010 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B4108603 : Blo 1623010 4108603 := bstep (se 1 (by rfl) ⟨3081452, by rfl⟩ : syracuseStep 4108603 = 6162905) B6162905
theorem B18502019 : Blo 1623010 18502019 := bstep (se 1 (by rfl) ⟨13876514, by rfl⟩ : syracuseStep 18502019 = 27753029) B27753029
theorem B4108745 : Blo 1623010 4108745 := bstep (se 2 (by rfl) ⟨1540779, by rfl⟩ : syracuseStep 4108745 = 3081559) B3081559
theorem B14062045 : Blo 1623010 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B2740871 : Blo 1623010 2740871 := bstep (se 1 (by rfl) ⟨2055653, by rfl⟩ : syracuseStep 2740871 = 4111307) B4111307
theorem B3125945 : Blo 1623010 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B4109089 : Blo 1623010 4109089 := bstep (se 2 (by rfl) ⟨1540908, by rfl⟩ : syracuseStep 4109089 = 3081817) B3081817
theorem B8221499 : Blo 1623010 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B3167095 : Blo 1623010 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B9376721 : Blo 1623010 9376721 := bstep (se 2 (by rfl) ⟨3516270, by rfl⟩ : syracuseStep 9376721 = 7032541) B7032541
theorem B8221661 : Blo 1623010 8221661 := bstep (se 3 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 8221661 = 3083123) B3083123
theorem B4387841 : Blo 1623010 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B4166671 : Blo 1623010 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B4625437 : Blo 1623010 4625437 := bstep (se 3 (by rfl) ⟨867269, by rfl⟩ : syracuseStep 4625437 = 1734539) B1734539
theorem B4625495 : Blo 1623010 4625495 := bstep (se 1 (by rfl) ⟨3469121, by rfl⟩ : syracuseStep 4625495 = 6938243) B6938243
theorem B2602103 : Blo 1623010 2602103 := bstep (se 1 (by rfl) ⟨1951577, by rfl⟩ : syracuseStep 2602103 = 3903155) B3903155
theorem B10548397 : Blo 1623010 10548397 := bstep (se 3 (by rfl) ⟨1977824, by rfl⟩ : syracuseStep 10548397 = 3955649) B3955649
theorem B8221985 : Blo 1623010 8221985 := bstep (se 2 (by rfl) ⟨3083244, by rfl⟩ : syracuseStep 8221985 = 6166489) B6166489
theorem B6935867 : Blo 1623010 6935867 := bstep (se 1 (by rfl) ⟨5201900, by rfl⟩ : syracuseStep 6935867 = 10403801) B10403801
theorem B4166999 : Blo 1623010 4166999 := bstep (se 1 (by rfl) ⟨3125249, by rfl⟩ : syracuseStep 4166999 = 6250499) B6250499
theorem B4109687 : Blo 1623010 4109687 := bstep (se 1 (by rfl) ⟨3082265, by rfl⟩ : syracuseStep 4109687 = 6164531) B6164531
theorem B7804295 : Blo 1623010 7804295 := bstep (se 1 (by rfl) ⟨5853221, by rfl⟩ : syracuseStep 7804295 = 11706443) B11706443
theorem B56260025 : Blo 1623010 56260025 := bstep (se 2 (by rfl) ⟨21097509, by rfl⟩ : syracuseStep 56260025 = 42195019) B42195019
theorem B4388413 : Blo 1623010 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B5477975 : Blo 1623010 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B17553125 : Blo 1623010 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B5478461 : Blo 1623010 5478461 := bstep (se 3 (by rfl) ⟨1027211, by rfl⟩ : syracuseStep 5478461 = 2054423) B2054423
theorem B12335165 : Blo 1623010 12335165 := bstep (se 3 (by rfl) ⟨2312843, by rfl⟩ : syracuseStep 12335165 = 4625687) B4625687
theorem B3651785 : Blo 1623010 3651785 := bstep (se 2 (by rfl) ⟨1369419, by rfl⟩ : syracuseStep 3651785 = 2738839) B2738839
theorem B8222957 : Blo 1623010 8222957 := bstep (se 3 (by rfl) ⟨1541804, by rfl⟩ : syracuseStep 8222957 = 3083609) B3083609
theorem B2636047 : Blo 1623010 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B9877895 : Blo 1623010 9877895 := bstep (se 1 (by rfl) ⟨7408421, by rfl⟩ : syracuseStep 9877895 = 14816843) B14816843
theorem B12327389 : Blo 1623010 12327389 := bstep (se 3 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 12327389 = 4622771) B4622771
theorem B7404043 : Blo 1623010 7404043 := bstep (se 1 (by rfl) ⟨5553032, by rfl⟩ : syracuseStep 7404043 = 11106065) B11106065
theorem B4110983 : Blo 1623010 4110983 := bstep (se 1 (by rfl) ⟨3083237, by rfl⟩ : syracuseStep 4110983 = 6166475) B6166475
theorem B4111033 : Blo 1623010 4111033 := bstep (se 2 (by rfl) ⟨1541637, by rfl⟩ : syracuseStep 4111033 = 3083275) B3083275
theorem B9247547 : Blo 1623010 9247547 := bstep (se 1 (by rfl) ⟨6935660, by rfl⟩ : syracuseStep 9247547 = 13871321) B13871321
theorem B3652487 : Blo 1623010 3652487 := bstep (se 1 (by rfl) ⟨2739365, by rfl⟩ : syracuseStep 3652487 = 5478731) B5478731
theorem B8223767 : Blo 1623010 8223767 := bstep (se 1 (by rfl) ⟨6167825, by rfl⟩ : syracuseStep 8223767 = 12335651) B12335651
theorem B6937643 : Blo 1623010 6937643 := bstep (se 1 (by rfl) ⟨5203232, by rfl⟩ : syracuseStep 6937643 = 10406465) B10406465
theorem B3652667 : Blo 1623010 3652667 := bstep (se 1 (by rfl) ⟨2739500, by rfl⟩ : syracuseStep 3652667 = 5479001) B5479001
theorem B7027831 : Blo 1623010 7027831 := bstep (se 1 (by rfl) ⟨5270873, by rfl⟩ : syracuseStep 7027831 = 10541747) B10541747
theorem B3652793 : Blo 1623010 3652793 := bstep (se 2 (by rfl) ⟨1369797, by rfl⟩ : syracuseStep 3652793 = 2739595) B2739595
theorem B8461505 : Blo 1623010 8461505 := bstep (se 2 (by rfl) ⟨3173064, by rfl⟩ : syracuseStep 8461505 = 6346129) B6346129
theorem B4111631 : Blo 1623010 4111631 := bstep (se 1 (by rfl) ⟨3083723, by rfl⟩ : syracuseStep 4111631 = 6167447) B6167447
theorem B3661175 : Blo 1623010 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B8019353 : Blo 1623010 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B5479865 : Blo 1623010 5479865 := bstep (se 2 (by rfl) ⟨2054949, by rfl⟩ : syracuseStep 5479865 = 4109899) B4109899
theorem B1826311 : Blo 1623010 1826311 := bstep (se 1 (by rfl) ⟨1369733, by rfl⟩ : syracuseStep 1826311 = 2739467) B2739467
theorem B3653135 : Blo 1623010 3653135 := bstep (se 1 (by rfl) ⟨2739851, by rfl⟩ : syracuseStep 3653135 = 5479703) B5479703
theorem B3653153 : Blo 1623010 3653153 := bstep (se 2 (by rfl) ⟨1369932, by rfl⟩ : syracuseStep 3653153 = 2739865) B2739865
theorem B18488897 : Blo 1623010 18488897 := bstep (se 2 (by rfl) ⟨6933336, by rfl⟩ : syracuseStep 18488897 = 13866673) B13866673
theorem B1826491 : Blo 1623010 1826491 := bstep (se 1 (by rfl) ⟨1369868, by rfl⟩ : syracuseStep 1826491 = 2739737) B2739737
theorem B9879329 : Blo 1623010 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B4685611 : Blo 1623010 4685611 := bstep (se 1 (by rfl) ⟨3514208, by rfl⟩ : syracuseStep 4685611 = 7028417) B7028417
theorem B3653495 : Blo 1623010 3653495 := bstep (se 1 (by rfl) ⟨2740121, by rfl⟩ : syracuseStep 3653495 = 5480243) B5480243
theorem B3653639 : Blo 1623010 3653639 := bstep (se 1 (by rfl) ⟨2740229, by rfl⟩ : syracuseStep 3653639 = 5480459) B5480459
theorem B5201977 : Blo 1623010 5201977 := bstep (se 2 (by rfl) ⟨1950741, by rfl⟩ : syracuseStep 5201977 = 3901483) B3901483
theorem B3653711 : Blo 1623010 3653711 := bstep (se 1 (by rfl) ⟨2740283, by rfl⟩ : syracuseStep 3653711 = 5480567) B5480567
theorem B46809251 : Blo 1623010 46809251 := bstep (se 1 (by rfl) ⟨35106938, by rfl⟩ : syracuseStep 46809251 = 70213877) B70213877
theorem B2924743 : Blo 1623010 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B6938941 : Blo 1623010 6938941 := bstep (se 3 (by rfl) ⟨1301051, by rfl⟩ : syracuseStep 6938941 = 2602103) B2602103
theorem B1827247 : Blo 1623010 1827247 := bstep (se 1 (by rfl) ⟨1370435, by rfl⟩ : syracuseStep 1827247 = 2740871) B2740871
theorem B3654107 : Blo 1623010 3654107 := bstep (se 1 (by rfl) ⟨2740580, by rfl⟩ : syracuseStep 3654107 = 5481161) B5481161
theorem B5480999 : Blo 1623010 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B6251147 : Blo 1623010 6251147 := bstep (se 1 (by rfl) ⟨4688360, by rfl⟩ : syracuseStep 6251147 = 9376721) B9376721
theorem B5481107 : Blo 1623010 5481107 := bstep (se 1 (by rfl) ⟨4110830, by rfl⟩ : syracuseStep 5481107 = 8221661) B8221661
theorem B2925227 : Blo 1623010 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B9872057 : Blo 1623010 9872057 := bstep (se 2 (by rfl) ⟨3702021, by rfl⟩ : syracuseStep 9872057 = 7404043) B7404043
theorem B5481323 : Blo 1623010 5481323 := bstep (se 1 (by rfl) ⟨4110992, by rfl⟩ : syracuseStep 5481323 = 8221985) B8221985
theorem B2777999 : Blo 1623010 2777999 := bstep (se 1 (by rfl) ⟨2083499, by rfl⟩ : syracuseStep 2777999 = 4166999) B4166999
theorem B5481377 : Blo 1623010 5481377 := bstep (se 2 (by rfl) ⟨2055516, by rfl⟩ : syracuseStep 5481377 = 4111033) B4111033
theorem B4686767 : Blo 1623010 4686767 := bstep (se 1 (by rfl) ⟨3515075, by rfl⟩ : syracuseStep 4686767 = 7030151) B7030151
theorem B5202863 : Blo 1623010 5202863 := bstep (se 1 (by rfl) ⟨3902147, by rfl⟩ : syracuseStep 5202863 = 7804295) B7804295
theorem B3654575 : Blo 1623010 3654575 := bstep (se 1 (by rfl) ⟨2740931, by rfl⟩ : syracuseStep 3654575 = 5481863) B5481863
theorem B5850119 : Blo 1623010 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B1623079 : Blo 1623010 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B1623119 : Blo 1623010 1623119 := bstep (se 1 (by rfl) ⟨1217339, by rfl⟩ : syracuseStep 1623119 = 2434679) B2434679
theorem B1623135 : Blo 1623010 1623135 := bstep (se 1 (by rfl) ⟨1217351, by rfl⟩ : syracuseStep 1623135 = 2434703) B2434703
theorem B1623163 : Blo 1623010 1623163 := bstep (se 1 (by rfl) ⟨1217372, by rfl⟩ : syracuseStep 1623163 = 2434745) B2434745
theorem B3654827 : Blo 1623010 3654827 := bstep (se 1 (by rfl) ⟨2741120, by rfl⟩ : syracuseStep 3654827 = 5482241) B5482241
theorem B1623215 : Blo 1623010 1623215 := bstep (se 1 (by rfl) ⟨1217411, by rfl⟩ : syracuseStep 1623215 = 2434823) B2434823
theorem B3081415 : Blo 1623010 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B1623239 : Blo 1623010 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B1623259 : Blo 1623010 1623259 := bstep (se 1 (by rfl) ⟨1217444, by rfl⟩ : syracuseStep 1623259 = 2434889) B2434889
theorem B1623335 : Blo 1623010 1623335 := bstep (se 1 (by rfl) ⟨1217501, by rfl⟩ : syracuseStep 1623335 = 2435003) B2435003
theorem B1623375 : Blo 1623010 1623375 := bstep (se 1 (by rfl) ⟨1217531, by rfl⟩ : syracuseStep 1623375 = 2435063) B2435063
theorem B1623391 : Blo 1623010 1623391 := bstep (se 1 (by rfl) ⟨1217543, by rfl⟩ : syracuseStep 1623391 = 2435087) B2435087
theorem B5555561 : Blo 1623010 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B1623419 : Blo 1623010 1623419 := bstep (se 1 (by rfl) ⟨1217564, by rfl⟩ : syracuseStep 1623419 = 2435129) B2435129
theorem B14058917 : Blo 1623010 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B2082223 : Blo 1623010 2082223 := bstep (se 1 (by rfl) ⟨1561667, by rfl⟩ : syracuseStep 2082223 = 3123335) B3123335
theorem B1623471 : Blo 1623010 1623471 := bstep (se 1 (by rfl) ⟨1217603, by rfl⟩ : syracuseStep 1623471 = 2435207) B2435207
theorem B1623495 : Blo 1623010 1623495 := bstep (se 1 (by rfl) ⟨1217621, by rfl⟩ : syracuseStep 1623495 = 2435243) B2435243
theorem B2434523 : Blo 1623010 2434523 := bstep (se 1 (by rfl) ⟨1825892, by rfl⟩ : syracuseStep 2434523 = 3651785) B3651785
theorem B1623515 : Blo 1623010 1623515 := bstep (se 1 (by rfl) ⟨1217636, by rfl⟩ : syracuseStep 1623515 = 2435273) B2435273
theorem B5481971 : Blo 1623010 5481971 := bstep (se 1 (by rfl) ⟨4111478, by rfl⟩ : syracuseStep 5481971 = 8222957) B8222957
theorem B1623591 : Blo 1623010 1623591 := bstep (se 1 (by rfl) ⟨1217693, by rfl⟩ : syracuseStep 1623591 = 2435387) B2435387
theorem B1623631 : Blo 1623010 1623631 := bstep (se 1 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 1623631 = 2435447) B2435447
theorem B1623647 : Blo 1623010 1623647 := bstep (se 1 (by rfl) ⟨1217735, by rfl⟩ : syracuseStep 1623647 = 2435471) B2435471
theorem B1623675 : Blo 1623010 1623675 := bstep (se 1 (by rfl) ⟨1217756, by rfl⟩ : syracuseStep 1623675 = 2435513) B2435513
theorem B8218259 : Blo 1623010 8218259 := bstep (se 1 (by rfl) ⟨6163694, by rfl⟩ : syracuseStep 8218259 = 12327389) B12327389
theorem B1623727 : Blo 1623010 1623727 := bstep (se 1 (by rfl) ⟨1217795, by rfl⟩ : syracuseStep 1623727 = 2435591) B2435591
theorem B1623751 : Blo 1623010 1623751 := bstep (se 1 (by rfl) ⟨1217813, by rfl⟩ : syracuseStep 1623751 = 2435627) B2435627
theorem B1623771 : Blo 1623010 1623771 := bstep (se 1 (by rfl) ⟨1217828, by rfl⟩ : syracuseStep 1623771 = 2435657) B2435657
theorem B1623847 : Blo 1623010 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B7800619 : Blo 1623010 7800619 := bstep (se 1 (by rfl) ⟨5850464, by rfl⟩ : syracuseStep 7800619 = 11700929) B11700929
theorem B1623887 : Blo 1623010 1623887 := bstep (se 1 (by rfl) ⟨1217915, by rfl⟩ : syracuseStep 1623887 = 2435831) B2435831
theorem B1623903 : Blo 1623010 1623903 := bstep (se 1 (by rfl) ⟨1217927, by rfl⟩ : syracuseStep 1623903 = 2435855) B2435855
theorem B1623931 : Blo 1623010 1623931 := bstep (se 1 (by rfl) ⟨1217948, by rfl⟩ : syracuseStep 1623931 = 2435897) B2435897
theorem B2434991 : Blo 1623010 2434991 := bstep (se 1 (by rfl) ⟨1826243, by rfl⟩ : syracuseStep 2434991 = 3652487) B3652487
theorem B1623983 : Blo 1623010 1623983 := bstep (se 1 (by rfl) ⟨1217987, by rfl⟩ : syracuseStep 1623983 = 2435975) B2435975
theorem B1624007 : Blo 1623010 1624007 := bstep (se 1 (by rfl) ⟨1218005, by rfl⟩ : syracuseStep 1624007 = 2436011) B2436011
theorem B2312155 : Blo 1623010 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B1624027 : Blo 1623010 1624027 := bstep (se 1 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 1624027 = 2436041) B2436041
theorem B2435081 : Blo 1623010 2435081 := bstep (se 2 (by rfl) ⟨913155, by rfl⟩ : syracuseStep 2435081 = 1826311) B1826311
theorem B5482511 : Blo 1623010 5482511 := bstep (se 1 (by rfl) ⟨4111883, by rfl⟩ : syracuseStep 5482511 = 8223767) B8223767
theorem B2435111 : Blo 1623010 2435111 := bstep (se 1 (by rfl) ⟨1826333, by rfl⟩ : syracuseStep 2435111 = 3652667) B3652667
theorem B1624103 : Blo 1623010 1624103 := bstep (se 1 (by rfl) ⟨1218077, by rfl⟩ : syracuseStep 1624103 = 2436155) B2436155
theorem B1624143 : Blo 1623010 1624143 := bstep (se 1 (by rfl) ⟨1218107, by rfl⟩ : syracuseStep 1624143 = 2436215) B2436215
theorem B5851217 : Blo 1623010 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B1624159 : Blo 1623010 1624159 := bstep (se 1 (by rfl) ⟨1218119, by rfl⟩ : syracuseStep 1624159 = 2436239) B2436239
theorem B2435195 : Blo 1623010 2435195 := bstep (se 1 (by rfl) ⟨1826396, by rfl⟩ : syracuseStep 2435195 = 3652793) B3652793
theorem B1624187 : Blo 1623010 1624187 := bstep (se 1 (by rfl) ⟨1218140, by rfl⟩ : syracuseStep 1624187 = 2436281) B2436281
theorem B1624239 : Blo 1623010 1624239 := bstep (se 1 (by rfl) ⟨1218179, by rfl⟩ : syracuseStep 1624239 = 2436359) B2436359
theorem B5851331 : Blo 1623010 5851331 := bstep (se 1 (by rfl) ⟨4388498, by rfl⟩ : syracuseStep 5851331 = 8776997) B8776997
theorem B1624263 : Blo 1623010 1624263 := bstep (se 1 (by rfl) ⟨1218197, by rfl⟩ : syracuseStep 1624263 = 2436395) B2436395
theorem B1624283 : Blo 1623010 1624283 := bstep (se 1 (by rfl) ⟨1218212, by rfl⟩ : syracuseStep 1624283 = 2436425) B2436425
theorem B2435321 : Blo 1623010 2435321 := bstep (se 2 (by rfl) ⟨913245, by rfl⟩ : syracuseStep 2435321 = 1826491) B1826491
theorem B1624359 : Blo 1623010 1624359 := bstep (se 1 (by rfl) ⟨1218269, by rfl⟩ : syracuseStep 1624359 = 2436539) B2436539
theorem B1624399 : Blo 1623010 1624399 := bstep (se 1 (by rfl) ⟨1218299, by rfl⟩ : syracuseStep 1624399 = 2436599) B2436599
theorem B2435423 : Blo 1623010 2435423 := bstep (se 1 (by rfl) ⟨1826567, by rfl⟩ : syracuseStep 2435423 = 3653135) B3653135
theorem B1624415 : Blo 1623010 1624415 := bstep (se 1 (by rfl) ⟨1218311, by rfl⟩ : syracuseStep 1624415 = 2436623) B2436623
theorem B2435435 : Blo 1623010 2435435 := bstep (se 1 (by rfl) ⟨1826576, by rfl⟩ : syracuseStep 2435435 = 3653153) B3653153
theorem B1624443 : Blo 1623010 1624443 := bstep (se 1 (by rfl) ⟨1218332, by rfl⟩ : syracuseStep 1624443 = 2436665) B2436665
theorem B1624495 : Blo 1623010 1624495 := bstep (se 1 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 1624495 = 2436743) B2436743
theorem B2435663 : Blo 1623010 2435663 := bstep (se 1 (by rfl) ⟨1826747, by rfl⟩ : syracuseStep 2435663 = 3653495) B3653495
theorem B42740405 : Blo 1623010 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B2435783 : Blo 1623010 2435783 := bstep (se 1 (by rfl) ⟨1826837, by rfl⟩ : syracuseStep 2435783 = 3653675) B3653675
theorem B2435945 : Blo 1623010 2435945 := bstep (se 2 (by rfl) ⟨913479, by rfl⟩ : syracuseStep 2435945 = 1826959) B1826959
theorem B6163361 : Blo 1623010 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B2436023 : Blo 1623010 2436023 := bstep (se 1 (by rfl) ⟨1827017, by rfl⟩ : syracuseStep 2436023 = 3654035) B3654035
theorem B2739163 : Blo 1623010 2739163 := bstep (se 1 (by rfl) ⟨2054372, by rfl⟩ : syracuseStep 2739163 = 4108745) B4108745
theorem B2436059 : Blo 1623010 2436059 := bstep (se 1 (by rfl) ⟨1827044, by rfl⟩ : syracuseStep 2436059 = 3654089) B3654089
theorem B3083321 : Blo 1623010 3083321 := bstep (se 2 (by rfl) ⟨1156245, by rfl⟩ : syracuseStep 3083321 = 2312491) B2312491
theorem B16657487 : Blo 1623010 16657487 := bstep (se 1 (by rfl) ⟨12493115, by rfl⟩ : syracuseStep 16657487 = 24986231) B24986231
theorem B9874511 : Blo 1623010 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B2083963 : Blo 1623010 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B22564013 : Blo 1623010 22564013 := bstep (se 3 (by rfl) ⟨4230752, by rfl⟩ : syracuseStep 22564013 = 8461505) B8461505
theorem B3083663 : Blo 1623010 3083663 := bstep (se 1 (by rfl) ⟨2312747, by rfl⟩ : syracuseStep 3083663 = 4625495) B4625495
theorem B2436527 : Blo 1623010 2436527 := bstep (se 1 (by rfl) ⟨1827395, by rfl⟩ : syracuseStep 2436527 = 3654791) B3654791
theorem B2436617 : Blo 1623010 2436617 := bstep (se 2 (by rfl) ⟨913731, by rfl⟩ : syracuseStep 2436617 = 1827463) B1827463
theorem B4623911 : Blo 1623010 4623911 := bstep (se 1 (by rfl) ⟨3467933, by rfl⟩ : syracuseStep 4623911 = 6935867) B6935867
theorem B2436647 : Blo 1623010 2436647 := bstep (se 1 (by rfl) ⟨1827485, by rfl⟩ : syracuseStep 2436647 = 3654971) B3654971
theorem B2739791 : Blo 1623010 2739791 := bstep (se 1 (by rfl) ⟨2054843, by rfl⟩ : syracuseStep 2739791 = 4109687) B4109687
theorem B37506683 : Blo 1623010 37506683 := bstep (se 1 (by rfl) ⟨28130012, by rfl⟩ : syracuseStep 37506683 = 56260025) B56260025
theorem B2436731 : Blo 1623010 2436731 := bstep (se 1 (by rfl) ⟨1827548, by rfl⟩ : syracuseStep 2436731 = 3655097) B3655097
theorem B16658243 : Blo 1623010 16658243 := bstep (se 1 (by rfl) ⟨12493682, by rfl⟩ : syracuseStep 16658243 = 24987365) B24987365
theorem B11702083 : Blo 1623010 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B4222793 : Blo 1623010 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B6164333 : Blo 1623010 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B13873031 : Blo 1623010 13873031 := bstep (se 1 (by rfl) ⟨10404773, by rfl⟩ : syracuseStep 13873031 = 20809547) B20809547
theorem B14061649 : Blo 1623010 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B82292915 : Blo 1623010 82292915 := bstep (se 1 (by rfl) ⟨61719686, by rfl⟩ : syracuseStep 82292915 = 123439373) B123439373
theorem B9875773 : Blo 1623010 9875773 := bstep (se 3 (by rfl) ⟨1851707, by rfl⟩ : syracuseStep 9875773 = 3703415) B3703415
theorem B2740655 : Blo 1623010 2740655 := bstep (se 1 (by rfl) ⟨2055491, by rfl⟩ : syracuseStep 2740655 = 4110983) B4110983
theorem B6165017 : Blo 1623010 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B6165031 : Blo 1623010 6165031 := bstep (se 1 (by rfl) ⟨4623773, by rfl⟩ : syracuseStep 6165031 = 9247547) B9247547
theorem B4625095 : Blo 1623010 4625095 := bstep (se 1 (by rfl) ⟨3468821, by rfl⟩ : syracuseStep 4625095 = 6937643) B6937643
theorem B2741087 : Blo 1623010 2741087 := bstep (se 1 (by rfl) ⟨2055815, by rfl⟩ : syracuseStep 2741087 = 4111631) B4111631
theorem B4109231 : Blo 1623010 4109231 := bstep (se 1 (by rfl) ⟨3081923, by rfl⟩ : syracuseStep 4109231 = 6163847) B6163847
theorem B10548143 : Blo 1623010 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B5346235 : Blo 1623010 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B12325931 : Blo 1623010 12325931 := bstep (se 1 (by rfl) ⟨9244448, by rfl⟩ : syracuseStep 12325931 = 18488897) B18488897
theorem B6247481 : Blo 1623010 6247481 := bstep (se 2 (by rfl) ⟨2342805, by rfl⟩ : syracuseStep 6247481 = 4685611) B4685611
theorem B6165821 : Blo 1623010 6165821 := bstep (se 3 (by rfl) ⟨1156091, by rfl⟩ : syracuseStep 6165821 = 2312183) B2312183
theorem B6166003 : Blo 1623010 6166003 := bstep (se 1 (by rfl) ⟨4624502, by rfl⟩ : syracuseStep 6166003 = 9249005) B9249005
theorem B4109849 : Blo 1623010 4109849 := bstep (se 2 (by rfl) ⟨1541193, by rfl⟩ : syracuseStep 4109849 = 3082387) B3082387
theorem B5477921 : Blo 1623010 5477921 := bstep (se 2 (by rfl) ⟨2054220, by rfl⟩ : syracuseStep 5477921 = 4108441) B4108441
theorem B12334679 : Blo 1623010 12334679 := bstep (se 1 (by rfl) ⟨9251009, by rfl⟩ : syracuseStep 12334679 = 18502019) B18502019
theorem B5478137 : Blo 1623010 5478137 := bstep (se 2 (by rfl) ⟨2054301, by rfl⟩ : syracuseStep 5478137 = 4108603) B4108603
theorem B16897901 : Blo 1623010 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B18749393 : Blo 1623010 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B5478407 : Blo 1623010 5478407 := bstep (se 1 (by rfl) ⟨4108805, by rfl⟩ : syracuseStep 5478407 = 8217611) B8217611
theorem B5478515 : Blo 1623010 5478515 := bstep (se 1 (by rfl) ⟨4108886, by rfl⟩ : syracuseStep 5478515 = 8217773) B8217773
theorem B10008937 : Blo 1623010 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B5478785 : Blo 1623010 5478785 := bstep (se 2 (by rfl) ⟨2054544, by rfl⟩ : syracuseStep 5478785 = 4109089) B4109089
theorem B3651983 : Blo 1623010 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B2054575 : Blo 1623010 2054575 := bstep (se 1 (by rfl) ⟨1540931, by rfl⟩ : syracuseStep 2054575 = 3081863) B3081863
theorem B6167249 : Blo 1623010 6167249 := bstep (se 2 (by rfl) ⟨2312718, by rfl⟩ : syracuseStep 6167249 = 4625437) B4625437
theorem B3652307 : Blo 1623010 3652307 := bstep (se 1 (by rfl) ⟨2739230, by rfl⟩ : syracuseStep 3652307 = 5478461) B5478461
theorem B8223443 : Blo 1623010 8223443 := bstep (se 1 (by rfl) ⟨6167582, by rfl⟩ : syracuseStep 8223443 = 12335165) B12335165
theorem B9370441 : Blo 1623010 9370441 := bstep (se 2 (by rfl) ⟨3513915, by rfl⟩ : syracuseStep 9370441 = 7027831) B7027831
theorem B14064529 : Blo 1623010 14064529 := bstep (se 2 (by rfl) ⟨5274198, by rfl⟩ : syracuseStep 14064529 = 10548397) B10548397
theorem B6585263 : Blo 1623010 6585263 := bstep (se 1 (by rfl) ⟨4938947, by rfl⟩ : syracuseStep 6585263 = 9877895) B9877895
theorem B5200823 : Blo 1623010 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B1825915 : Blo 1623010 1825915 := bstep (se 1 (by rfl) ⟨1369436, by rfl⟩ : syracuseStep 1825915 = 2738873) B2738873
theorem B5479595 : Blo 1623010 5479595 := bstep (se 1 (by rfl) ⟨4109696, by rfl⟩ : syracuseStep 5479595 = 8219393) B8219393
theorem B6167933 : Blo 1623010 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B2055719 : Blo 1623010 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B1826383 : Blo 1623010 1826383 := bstep (se 1 (by rfl) ⟨1369787, by rfl⟩ : syracuseStep 1826383 = 2739575) B2739575
theorem B2440783 : Blo 1623010 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B3653243 : Blo 1623010 3653243 := bstep (se 1 (by rfl) ⟨2739932, by rfl⟩ : syracuseStep 3653243 = 5479865) B5479865
theorem B5480135 : Blo 1623010 5480135 := bstep (se 1 (by rfl) ⟨4110101, by rfl⟩ : syracuseStep 5480135 = 8220203) B8220203
theorem B3653369 : Blo 1623010 3653369 := bstep (se 2 (by rfl) ⟨1370013, by rfl⟩ : syracuseStep 3653369 = 2740027) B2740027
theorem B6586219 : Blo 1623010 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B1826779 : Blo 1623010 1826779 := bstep (se 1 (by rfl) ⟨1370084, by rfl⟩ : syracuseStep 1826779 = 2740169) B2740169
theorem B54861943 : Blo 1623010 54861943 := bstep (se 1 (by rfl) ⟨41146457, by rfl⟩ : syracuseStep 54861943 = 82292915) B82292915
theorem B3899657 : Blo 1623010 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B1827103 : Blo 1623010 1827103 := bstep (se 1 (by rfl) ⟨1370327, by rfl⟩ : syracuseStep 1827103 = 2740655) B2740655
theorem B3653999 : Blo 1623010 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B13017509 : Blo 1623010 13017509 := bstep (se 4 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 13017509 = 2440783) B2440783
theorem B3654071 : Blo 1623010 3654071 := bstep (se 1 (by rfl) ⟨2740553, by rfl⟩ : syracuseStep 3654071 = 5481107) B5481107
theorem B1950151 : Blo 1623010 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B60170701 : Blo 1623010 60170701 := bstep (se 3 (by rfl) ⟨11282006, by rfl⟩ : syracuseStep 60170701 = 22564013) B22564013
theorem B13345249 : Blo 1623010 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B1827391 : Blo 1623010 1827391 := bstep (se 1 (by rfl) ⟨1370543, by rfl⟩ : syracuseStep 1827391 = 2741087) B2741087
theorem B3654215 : Blo 1623010 3654215 := bstep (se 1 (by rfl) ⟨2740661, by rfl⟩ : syracuseStep 3654215 = 5481323) B5481323
theorem B3654251 : Blo 1623010 3654251 := bstep (se 1 (by rfl) ⟨2740688, by rfl⟩ : syracuseStep 3654251 = 5481377) B5481377
theorem B3900079 : Blo 1623010 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B8217287 : Blo 1623010 8217287 := bstep (se 1 (by rfl) ⟨6162965, by rfl⟩ : syracuseStep 8217287 = 12325931) B12325931
theorem B9372611 : Blo 1623010 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B1623015 : Blo 1623010 1623015 := bstep (se 1 (by rfl) ⟨1217261, by rfl⟩ : syracuseStep 1623015 = 2434523) B2434523
theorem B3654647 : Blo 1623010 3654647 := bstep (se 1 (by rfl) ⟨2740985, by rfl⟩ : syracuseStep 3654647 = 5481971) B5481971
theorem B12493921 : Blo 1623010 12493921 := bstep (se 2 (by rfl) ⟨4685220, by rfl⟩ : syracuseStep 12493921 = 9370441) B9370441
theorem B18752705 : Blo 1623010 18752705 := bstep (se 2 (by rfl) ⟨7032264, by rfl⟩ : syracuseStep 18752705 = 14064529) B14064529
theorem B7128313 : Blo 1623010 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B1623327 : Blo 1623010 1623327 := bstep (se 1 (by rfl) ⟨1217495, by rfl⟩ : syracuseStep 1623327 = 2434991) B2434991
theorem B1623387 : Blo 1623010 1623387 := bstep (se 1 (by rfl) ⟨1217540, by rfl⟩ : syracuseStep 1623387 = 2435081) B2435081
theorem B3655007 : Blo 1623010 3655007 := bstep (se 1 (by rfl) ⟨2741255, by rfl⟩ : syracuseStep 3655007 = 5482511) B5482511
theorem B1623407 : Blo 1623010 1623407 := bstep (se 1 (by rfl) ⟨1217555, by rfl⟩ : syracuseStep 1623407 = 2435111) B2435111
theorem B3900811 : Blo 1623010 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1623463 : Blo 1623010 1623463 := bstep (se 1 (by rfl) ⟨1217597, by rfl⟩ : syracuseStep 1623463 = 2435195) B2435195
theorem B5481917 : Blo 1623010 5481917 := bstep (se 3 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 5481917 = 2055719) B2055719
theorem B3900887 : Blo 1623010 3900887 := bstep (se 1 (by rfl) ⟨2925665, by rfl⟩ : syracuseStep 3900887 = 5851331) B5851331
theorem B2434553 : Blo 1623010 2434553 := bstep (se 2 (by rfl) ⟨912957, by rfl⟩ : syracuseStep 2434553 = 1825915) B1825915
theorem B1623547 : Blo 1623010 1623547 := bstep (se 1 (by rfl) ⟨1217660, by rfl⟩ : syracuseStep 1623547 = 2435321) B2435321
theorem B2778617 : Blo 1623010 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B1623615 : Blo 1623010 1623615 := bstep (se 1 (by rfl) ⟨1217711, by rfl⟩ : syracuseStep 1623615 = 2435423) B2435423
theorem B1623623 : Blo 1623010 1623623 := bstep (se 1 (by rfl) ⟨1217717, by rfl⟩ : syracuseStep 1623623 = 2435435) B2435435
theorem B2434655 : Blo 1623010 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B100017821 : Blo 1623010 100017821 := bstep (se 3 (by rfl) ⟨18753341, by rfl⟩ : syracuseStep 100017821 = 37506683) B37506683
theorem B1623775 : Blo 1623010 1623775 := bstep (se 1 (by rfl) ⟨1217831, by rfl⟩ : syracuseStep 1623775 = 2435663) B2435663
theorem B28493603 : Blo 1623010 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B1623855 : Blo 1623010 1623855 := bstep (se 1 (by rfl) ⟨1217891, by rfl⟩ : syracuseStep 1623855 = 2435783) B2435783
theorem B2434871 : Blo 1623010 2434871 := bstep (se 1 (by rfl) ⟨1826153, by rfl⟩ : syracuseStep 2434871 = 3652307) B3652307
theorem B5482295 : Blo 1623010 5482295 := bstep (se 1 (by rfl) ⟨4111721, by rfl⟩ : syracuseStep 5482295 = 8223443) B8223443
theorem B1623963 : Blo 1623010 1623963 := bstep (se 1 (by rfl) ⟨1217972, by rfl⟩ : syracuseStep 1623963 = 2435945) B2435945
theorem B3467215 : Blo 1623010 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B1624015 : Blo 1623010 1624015 := bstep (se 1 (by rfl) ⟨1218011, by rfl⟩ : syracuseStep 1624015 = 2436023) B2436023
theorem B1624039 : Blo 1623010 1624039 := bstep (se 1 (by rfl) ⟨1218029, by rfl⟩ : syracuseStep 1624039 = 2436059) B2436059
theorem B2435177 : Blo 1623010 2435177 := bstep (se 2 (by rfl) ⟨913191, by rfl⟩ : syracuseStep 2435177 = 1826383) B1826383
theorem B1624351 : Blo 1623010 1624351 := bstep (se 1 (by rfl) ⟨1218263, by rfl⟩ : syracuseStep 1624351 = 2436527) B2436527
theorem B1624411 : Blo 1623010 1624411 := bstep (se 1 (by rfl) ⟨1218308, by rfl⟩ : syracuseStep 1624411 = 2436617) B2436617
theorem B3082607 : Blo 1623010 3082607 := bstep (se 1 (by rfl) ⟨2311955, by rfl⟩ : syracuseStep 3082607 = 4623911) B4623911
theorem B1624431 : Blo 1623010 1624431 := bstep (se 1 (by rfl) ⟨1218323, by rfl⟩ : syracuseStep 1624431 = 2436647) B2436647
theorem B7407997 : Blo 1623010 7407997 := bstep (se 3 (by rfl) ⟨1388999, by rfl⟩ : syracuseStep 7407997 = 2777999) B2777999
theorem B2435495 : Blo 1623010 2435495 := bstep (se 1 (by rfl) ⟨1826621, by rfl⟩ : syracuseStep 2435495 = 3653243) B3653243
theorem B1624487 : Blo 1623010 1624487 := bstep (se 1 (by rfl) ⟨1218365, by rfl⟩ : syracuseStep 1624487 = 2436731) B2436731
theorem B2435579 : Blo 1623010 2435579 := bstep (se 1 (by rfl) ⟨1826684, by rfl⟩ : syracuseStep 2435579 = 3653369) B3653369
theorem B2435705 : Blo 1623010 2435705 := bstep (se 2 (by rfl) ⟨913389, by rfl⟩ : syracuseStep 2435705 = 1826779) B1826779
theorem B3082873 : Blo 1623010 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B2435759 : Blo 1623010 2435759 := bstep (se 1 (by rfl) ⟨1826819, by rfl⟩ : syracuseStep 2435759 = 3653639) B3653639
theorem B2435807 : Blo 1623010 2435807 := bstep (se 1 (by rfl) ⟨1826855, by rfl⟩ : syracuseStep 2435807 = 3653711) B3653711
theorem B31206167 : Blo 1623010 31206167 := bstep (se 1 (by rfl) ⟨23404625, by rfl⟩ : syracuseStep 31206167 = 46809251) B46809251
theorem B2436071 : Blo 1623010 2436071 := bstep (se 1 (by rfl) ⟨1827053, by rfl⟩ : syracuseStep 2436071 = 3654107) B3654107
theorem B13167697 : Blo 1623010 13167697 := bstep (se 2 (by rfl) ⟨4937886, by rfl⟩ : syracuseStep 13167697 = 9875773) B9875773
theorem B9251921 : Blo 1623010 9251921 := bstep (se 2 (by rfl) ⟨3469470, by rfl⟩ : syracuseStep 9251921 = 6938941) B6938941
theorem B6581371 : Blo 1623010 6581371 := bstep (se 1 (by rfl) ⟨4936028, by rfl⟩ : syracuseStep 6581371 = 9872057) B9872057
theorem B2739433 : Blo 1623010 2739433 := bstep (se 2 (by rfl) ⟨1027287, by rfl⟩ : syracuseStep 2739433 = 2054575) B2054575
theorem B2436329 : Blo 1623010 2436329 := bstep (se 2 (by rfl) ⟨913623, by rfl⟩ : syracuseStep 2436329 = 1827247) B1827247
theorem B2739487 : Blo 1623010 2739487 := bstep (se 1 (by rfl) ⟨2054615, by rfl⟩ : syracuseStep 2739487 = 4109231) B4109231
theorem B3124511 : Blo 1623010 3124511 := bstep (se 1 (by rfl) ⟨2343383, by rfl⟩ : syracuseStep 3124511 = 4686767) B4686767
theorem B3468575 : Blo 1623010 3468575 := bstep (se 1 (by rfl) ⟨2601431, by rfl⟩ : syracuseStep 3468575 = 5202863) B5202863
theorem B7032095 : Blo 1623010 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B2436383 : Blo 1623010 2436383 := bstep (se 1 (by rfl) ⟨1827287, by rfl⟩ : syracuseStep 2436383 = 3654575) B3654575
theorem B8220041 : Blo 1623010 8220041 := bstep (se 2 (by rfl) ⟨3082515, by rfl⟩ : syracuseStep 8220041 = 6165031) B6165031
theorem B2436551 : Blo 1623010 2436551 := bstep (se 1 (by rfl) ⟨1827413, by rfl⟩ : syracuseStep 2436551 = 3654827) B3654827
theorem B14814829 : Blo 1623010 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B2739899 : Blo 1623010 2739899 := bstep (se 1 (by rfl) ⟨2054924, by rfl⟩ : syracuseStep 2739899 = 4109849) B4109849
theorem B4108553 : Blo 1623010 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B4108907 : Blo 1623010 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B8221337 : Blo 1623010 8221337 := bstep (se 2 (by rfl) ⟨3083001, by rfl⟩ : syracuseStep 8221337 = 6166003) B6166003
theorem B11104991 : Blo 1623010 11104991 := bstep (se 1 (by rfl) ⟨8328743, by rfl⟩ : syracuseStep 11104991 = 16657487) B16657487
theorem B6583007 : Blo 1623010 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B11260781 : Blo 1623010 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B45061069 : Blo 1623010 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B10400825 : Blo 1623010 10400825 := bstep (se 2 (by rfl) ⟨3900309, by rfl⟩ : syracuseStep 10400825 = 7800619) B7800619
theorem B15602777 : Blo 1623010 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B11105495 : Blo 1623010 11105495 := bstep (se 1 (by rfl) ⟨8329121, by rfl⟩ : syracuseStep 11105495 = 16658243) B16658243
theorem B4109555 : Blo 1623010 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B6935969 : Blo 1623010 6935969 := bstep (se 2 (by rfl) ⟨2600988, by rfl⟩ : syracuseStep 6935969 = 5201977) B5201977
theorem B18748865 : Blo 1623010 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B4110011 : Blo 1623010 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B4167431 : Blo 1623010 4167431 := bstep (se 1 (by rfl) ⟨3125573, by rfl⟩ : syracuseStep 4167431 = 6251147) B6251147
theorem B66639797 : Blo 1623010 66639797 := bstep (se 5 (by rfl) ⟨3123740, by rfl⟩ : syracuseStep 66639797 = 6247481) B6247481
theorem B4110547 : Blo 1623010 4110547 := bstep (se 1 (by rfl) ⟨3082910, by rfl⟩ : syracuseStep 4110547 = 6165821) B6165821
theorem B6166793 : Blo 1623010 6166793 := bstep (se 2 (by rfl) ⟨2312547, by rfl⟩ : syracuseStep 6166793 = 4625095) B4625095
theorem B3651947 : Blo 1623010 3651947 := bstep (se 1 (by rfl) ⟨2738960, by rfl⟩ : syracuseStep 3651947 = 5477921) B5477921
theorem B8223119 : Blo 1623010 8223119 := bstep (se 1 (by rfl) ⟨6167339, by rfl⟩ : syracuseStep 8223119 = 12334679) B12334679
theorem B5478839 : Blo 1623010 5478839 := bstep (se 1 (by rfl) ⟨4109129, by rfl⟩ : syracuseStep 5478839 = 8218259) B8218259
theorem B3652091 : Blo 1623010 3652091 := bstep (se 1 (by rfl) ⟨2739068, by rfl⟩ : syracuseStep 3652091 = 5478137) B5478137
theorem B3652217 : Blo 1623010 3652217 := bstep (se 2 (by rfl) ⟨1369581, by rfl⟩ : syracuseStep 3652217 = 2739163) B2739163
theorem B12499595 : Blo 1623010 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B3652271 : Blo 1623010 3652271 := bstep (se 1 (by rfl) ⟨2739203, by rfl⟩ : syracuseStep 3652271 = 5478407) B5478407
theorem B3652343 : Blo 1623010 3652343 := bstep (se 1 (by rfl) ⟨2739257, by rfl⟩ : syracuseStep 3652343 = 5478515) B5478515
theorem B3652523 : Blo 1623010 3652523 := bstep (se 1 (by rfl) ⟨2739392, by rfl⟩ : syracuseStep 3652523 = 5478785) B5478785
theorem B4111499 : Blo 1623010 4111499 := bstep (se 1 (by rfl) ⟨3083624, by rfl⟩ : syracuseStep 4111499 = 6167249) B6167249
theorem B2776297 : Blo 1623010 2776297 := bstep (se 2 (by rfl) ⟨1041111, by rfl⟩ : syracuseStep 2776297 = 2082223) B2082223
theorem B4390175 : Blo 1623010 4390175 := bstep (se 1 (by rfl) ⟨3292631, by rfl⟩ : syracuseStep 4390175 = 6585263) B6585263
theorem B2055547 : Blo 1623010 2055547 := bstep (se 1 (by rfl) ⟨1541660, by rfl⟩ : syracuseStep 2055547 = 3083321) B3083321
theorem B3653063 : Blo 1623010 3653063 := bstep (se 1 (by rfl) ⟨2739797, by rfl⟩ : syracuseStep 3653063 = 5479595) B5479595
theorem B4111955 : Blo 1623010 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B2055775 : Blo 1623010 2055775 := bstep (se 1 (by rfl) ⟨1541831, by rfl⟩ : syracuseStep 2055775 = 3083663) B3083663
theorem B1826527 : Blo 1623010 1826527 := bstep (se 1 (by rfl) ⟨1369895, by rfl⟩ : syracuseStep 1826527 = 2739791) B2739791
theorem B3653423 : Blo 1623010 3653423 := bstep (se 1 (by rfl) ⟨2740067, by rfl⟩ : syracuseStep 3653423 = 5480135) B5480135
theorem B8781625 : Blo 1623010 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B9248687 : Blo 1623010 9248687 := bstep (se 1 (by rfl) ⟨6936515, by rfl⟩ : syracuseStep 9248687 = 13873031) B13873031
theorem B5480729 : Blo 1623010 5480729 := bstep (se 2 (by rfl) ⟨2055273, by rfl⟩ : syracuseStep 5480729 = 4110547) B4110547
theorem B5480891 : Blo 1623010 5480891 := bstep (se 1 (by rfl) ⟨4110668, by rfl⟩ : syracuseStep 5480891 = 8221337) B8221337
theorem B17793665 : Blo 1623010 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B12501803 : Blo 1623010 12501803 := bstep (se 1 (by rfl) ⟨9376352, by rfl⟩ : syracuseStep 12501803 = 18752705) B18752705
theorem B20800421 : Blo 1623010 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B3654611 : Blo 1623010 3654611 := bstep (se 1 (by rfl) ⟨2740958, by rfl⟩ : syracuseStep 3654611 = 5481917) B5481917
theorem B1623035 : Blo 1623010 1623035 := bstep (se 1 (by rfl) ⟨1217276, by rfl⟩ : syracuseStep 1623035 = 2434553) B2434553
theorem B1852411 : Blo 1623010 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B1623103 : Blo 1623010 1623103 := bstep (se 1 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 1623103 = 2434655) B2434655
theorem B49996973 : Blo 1623010 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B1623247 : Blo 1623010 1623247 := bstep (se 1 (by rfl) ⟨1217435, by rfl⟩ : syracuseStep 1623247 = 2434871) B2434871
theorem B3654863 : Blo 1623010 3654863 := bstep (se 1 (by rfl) ⟨2741147, by rfl⟩ : syracuseStep 3654863 = 5482295) B5482295
theorem B60081425 : Blo 1623010 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B44426531 : Blo 1623010 44426531 := bstep (se 1 (by rfl) ⟨33319898, by rfl⟩ : syracuseStep 44426531 = 66639797) B66639797
theorem B1623451 : Blo 1623010 1623451 := bstep (se 1 (by rfl) ⟨1217588, by rfl⟩ : syracuseStep 1623451 = 2435177) B2435177
theorem B17556929 : Blo 1623010 17556929 := bstep (se 2 (by rfl) ⟨6583848, by rfl⟩ : syracuseStep 17556929 = 13167697) B13167697
theorem B8775161 : Blo 1623010 8775161 := bstep (se 2 (by rfl) ⟨3290685, by rfl⟩ : syracuseStep 8775161 = 6581371) B6581371
theorem B2434631 : Blo 1623010 2434631 := bstep (se 1 (by rfl) ⟨1825973, by rfl⟩ : syracuseStep 2434631 = 3651947) B3651947
theorem B5482079 : Blo 1623010 5482079 := bstep (se 1 (by rfl) ⟨4111559, by rfl⟩ : syracuseStep 5482079 = 8223119) B8223119
theorem B1623663 : Blo 1623010 1623663 := bstep (se 1 (by rfl) ⟨1217747, by rfl⟩ : syracuseStep 1623663 = 2435495) B2435495
theorem B2434727 : Blo 1623010 2434727 := bstep (se 1 (by rfl) ⟨1826045, by rfl⟩ : syracuseStep 2434727 = 3652091) B3652091
theorem B1623719 : Blo 1623010 1623719 := bstep (se 1 (by rfl) ⟨1217789, by rfl⟩ : syracuseStep 1623719 = 2435579) B2435579
theorem B2434811 : Blo 1623010 2434811 := bstep (se 1 (by rfl) ⟨1826108, by rfl⟩ : syracuseStep 2434811 = 3652217) B3652217
theorem B1623803 : Blo 1623010 1623803 := bstep (se 1 (by rfl) ⟨1217852, by rfl⟩ : syracuseStep 1623803 = 2435705) B2435705
theorem B8333063 : Blo 1623010 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B2434847 : Blo 1623010 2434847 := bstep (se 1 (by rfl) ⟨1826135, by rfl⟩ : syracuseStep 2434847 = 3652271) B3652271
theorem B1623839 : Blo 1623010 1623839 := bstep (se 1 (by rfl) ⟨1217879, by rfl⟩ : syracuseStep 1623839 = 2435759) B2435759
theorem B1623871 : Blo 1623010 1623871 := bstep (se 1 (by rfl) ⟨1217903, by rfl⟩ : syracuseStep 1623871 = 2435807) B2435807
theorem B2434895 : Blo 1623010 2434895 := bstep (se 1 (by rfl) ⟨1826171, by rfl⟩ : syracuseStep 2434895 = 3652343) B3652343
theorem B2435015 : Blo 1623010 2435015 := bstep (se 1 (by rfl) ⟨1826261, by rfl⟩ : syracuseStep 2435015 = 3652523) B3652523
theorem B1624047 : Blo 1623010 1624047 := bstep (se 1 (by rfl) ⟨1218035, by rfl⟩ : syracuseStep 1624047 = 2436071) B2436071
theorem B19753105 : Blo 1623010 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B1624219 : Blo 1623010 1624219 := bstep (se 1 (by rfl) ⟨1218164, by rfl⟩ : syracuseStep 1624219 = 2436329) B2436329
theorem B2083007 : Blo 1623010 2083007 := bstep (se 1 (by rfl) ⟨1562255, by rfl⟩ : syracuseStep 2083007 = 3124511) B3124511
theorem B2312383 : Blo 1623010 2312383 := bstep (se 1 (by rfl) ⟨1734287, by rfl⟩ : syracuseStep 2312383 = 3468575) B3468575
theorem B4688063 : Blo 1623010 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B2926783 : Blo 1623010 2926783 := bstep (se 1 (by rfl) ⟨2195087, by rfl⟩ : syracuseStep 2926783 = 4390175) B4390175
theorem B1624255 : Blo 1623010 1624255 := bstep (se 1 (by rfl) ⟨1218191, by rfl⟩ : syracuseStep 1624255 = 2436383) B2436383
theorem B2435369 : Blo 1623010 2435369 := bstep (se 2 (by rfl) ⟨913263, by rfl⟩ : syracuseStep 2435369 = 1826527) B1826527
theorem B2435375 : Blo 1623010 2435375 := bstep (se 1 (by rfl) ⟨1826531, by rfl⟩ : syracuseStep 2435375 = 3653063) B3653063
theorem B1624367 : Blo 1623010 1624367 := bstep (se 1 (by rfl) ⟨1218275, by rfl⟩ : syracuseStep 1624367 = 2436551) B2436551
theorem B11708833 : Blo 1623010 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B18491813 : Blo 1623010 18491813 := bstep (se 4 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 18491813 = 3467215) B3467215
theorem B2435615 : Blo 1623010 2435615 := bstep (se 1 (by rfl) ⟨1826711, by rfl⟩ : syracuseStep 2435615 = 3653423) B3653423
theorem B44452597 : Blo 1623010 44452597 := bstep (se 5 (by rfl) ⟨2083715, by rfl⟩ : syracuseStep 44452597 = 4167431) B4167431
theorem B73149257 : Blo 1623010 73149257 := bstep (se 2 (by rfl) ⟨27430971, by rfl⟩ : syracuseStep 73149257 = 54861943) B54861943
theorem B2599771 : Blo 1623010 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B2739035 : Blo 1623010 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B2435999 : Blo 1623010 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B8678339 : Blo 1623010 8678339 := bstep (se 1 (by rfl) ⟨6508754, by rfl⟩ : syracuseStep 8678339 = 13017509) B13017509
theorem B2436047 : Blo 1623010 2436047 := bstep (se 1 (by rfl) ⟨1827035, by rfl⟩ : syracuseStep 2436047 = 3654071) B3654071
theorem B2436137 : Blo 1623010 2436137 := bstep (se 2 (by rfl) ⟨913551, by rfl⟩ : syracuseStep 2436137 = 1827103) B1827103
theorem B2436143 : Blo 1623010 2436143 := bstep (se 1 (by rfl) ⟨1827107, by rfl⟩ : syracuseStep 2436143 = 3654215) B3654215
theorem B2739271 : Blo 1623010 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B2436167 : Blo 1623010 2436167 := bstep (se 1 (by rfl) ⟨1827125, by rfl⟩ : syracuseStep 2436167 = 3654251) B3654251
theorem B7507187 : Blo 1623010 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B2600201 : Blo 1623010 2600201 := bstep (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) B1950151
theorem B80227601 : Blo 1623010 80227601 := bstep (se 2 (by rfl) ⟨30085350, by rfl⟩ : syracuseStep 80227601 = 60170701) B60170701
theorem B2436431 : Blo 1623010 2436431 := bstep (se 1 (by rfl) ⟨1827323, by rfl⟩ : syracuseStep 2436431 = 3654647) B3654647
theorem B2436521 : Blo 1623010 2436521 := bstep (se 2 (by rfl) ⟨913695, by rfl⟩ : syracuseStep 2436521 = 1827391) B1827391
theorem B2739703 : Blo 1623010 2739703 := bstep (se 1 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 2739703 = 4109555) B4109555
theorem B2436671 : Blo 1623010 2436671 := bstep (se 1 (by rfl) ⟨1827503, by rfl⟩ : syracuseStep 2436671 = 3655007) B3655007
theorem B4623979 : Blo 1623010 4623979 := bstep (se 1 (by rfl) ⟨3467984, by rfl⟩ : syracuseStep 4623979 = 6935969) B6935969
theorem B2600591 : Blo 1623010 2600591 := bstep (se 1 (by rfl) ⟨1950443, by rfl⟩ : syracuseStep 2600591 = 3900887) B3900887
theorem B66678547 : Blo 1623010 66678547 := bstep (se 1 (by rfl) ⟨50008910, by rfl⟩ : syracuseStep 66678547 = 100017821) B100017821
theorem B2740007 : Blo 1623010 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B16658561 : Blo 1623010 16658561 := bstep (se 2 (by rfl) ⟨6246960, by rfl⟩ : syracuseStep 16658561 = 12493921) B12493921
theorem B2740729 : Blo 1623010 2740729 := bstep (se 2 (by rfl) ⟨1027773, by rfl⟩ : syracuseStep 2740729 = 2055547) B2055547
theorem B20804111 : Blo 1623010 20804111 := bstep (se 1 (by rfl) ⟨15603083, by rfl⟩ : syracuseStep 20804111 = 31206167) B31206167
theorem B2740999 : Blo 1623010 2740999 := bstep (se 1 (by rfl) ⟨2055749, by rfl⟩ : syracuseStep 2740999 = 4111499) B4111499
theorem B2741033 : Blo 1623010 2741033 := bstep (se 2 (by rfl) ⟨1027887, by rfl⟩ : syracuseStep 2741033 = 2055775) B2055775
theorem B2741303 : Blo 1623010 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B6165791 : Blo 1623010 6165791 := bstep (se 1 (by rfl) ⟨4624343, by rfl⟩ : syracuseStep 6165791 = 9248687) B9248687
theorem B27735533 : Blo 1623010 27735533 := bstep (se 3 (by rfl) ⟨5200412, by rfl⟩ : syracuseStep 27735533 = 10400825) B10400825
theorem B5478191 : Blo 1623010 5478191 := bstep (se 1 (by rfl) ⟨4108643, by rfl⟩ : syracuseStep 5478191 = 8217287) B8217287
theorem B7403327 : Blo 1623010 7403327 := bstep (se 1 (by rfl) ⟨5552495, by rfl⟩ : syracuseStep 7403327 = 11104991) B11104991
theorem B4388671 : Blo 1623010 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B10401851 : Blo 1623010 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B7403663 : Blo 1623010 7403663 := bstep (se 1 (by rfl) ⟨5552747, by rfl⟩ : syracuseStep 7403663 = 11105495) B11105495
theorem B4110497 : Blo 1623010 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B18995735 : Blo 1623010 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B38017669 : Blo 1623010 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B4111195 : Blo 1623010 4111195 := bstep (se 1 (by rfl) ⟨3083396, by rfl⟩ : syracuseStep 4111195 = 6166793) B6166793
theorem B2055071 : Blo 1623010 2055071 := bstep (se 1 (by rfl) ⟨1541303, by rfl⟩ : syracuseStep 2055071 = 3082607) B3082607
theorem B3652559 : Blo 1623010 3652559 := bstep (se 1 (by rfl) ⟨2739419, by rfl⟩ : syracuseStep 3652559 = 5478839) B5478839
theorem B3701729 : Blo 1623010 3701729 := bstep (se 2 (by rfl) ⟨1388148, by rfl⟩ : syracuseStep 3701729 = 2776297) B2776297
theorem B3652577 : Blo 1623010 3652577 := bstep (se 2 (by rfl) ⟨1369716, by rfl⟩ : syracuseStep 3652577 = 2739433) B2739433
theorem B3652649 : Blo 1623010 3652649 := bstep (se 2 (by rfl) ⟨1369743, by rfl⟩ : syracuseStep 3652649 = 2739487) B2739487
theorem B5201081 : Blo 1623010 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B39509317 : Blo 1623010 39509317 := bstep (se 4 (by rfl) ⟨3703998, by rfl⟩ : syracuseStep 39509317 = 7407997) B7407997
theorem B6167947 : Blo 1623010 6167947 := bstep (se 1 (by rfl) ⟨4625960, by rfl⟩ : syracuseStep 6167947 = 9251921) B9251921
theorem B5480027 : Blo 1623010 5480027 := bstep (se 1 (by rfl) ⟨4110020, by rfl⟩ : syracuseStep 5480027 = 8220041) B8220041
theorem B1826599 : Blo 1623010 1826599 := bstep (se 1 (by rfl) ⟨1369949, by rfl⟩ : syracuseStep 1826599 = 2739899) B2739899
theorem B24993629 : Blo 1623010 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B3653819 : Blo 1623010 3653819 := bstep (se 1 (by rfl) ⟨2740364, by rfl⟩ : syracuseStep 3653819 = 5480729) B5480729
theorem B26337473 : Blo 1623010 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B3653927 : Blo 1623010 3653927 := bstep (se 1 (by rfl) ⟨2740445, by rfl⟩ : syracuseStep 3653927 = 5480891) B5480891
theorem B13869407 : Blo 1623010 13869407 := bstep (se 1 (by rfl) ⟨10402055, by rfl⟩ : syracuseStep 13869407 = 20804111) B20804111
theorem B11862443 : Blo 1623010 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B133325261 : Blo 1623010 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B5554685 : Blo 1623010 5554685 := bstep (se 3 (by rfl) ⟨1041503, by rfl⟩ : syracuseStep 5554685 = 2083007) B2083007
theorem B1827355 : Blo 1623010 1827355 := bstep (se 1 (by rfl) ⟨1370516, by rfl⟩ : syracuseStep 1827355 = 2741033) B2741033
theorem B3654305 : Blo 1623010 3654305 := bstep (se 2 (by rfl) ⟨1370364, by rfl⟩ : syracuseStep 3654305 = 2740729) B2740729
theorem B1827535 : Blo 1623010 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B59270129 : Blo 1623010 59270129 := bstep (se 2 (by rfl) ⟨22226298, by rfl⟩ : syracuseStep 59270129 = 44452597) B44452597
theorem B18490355 : Blo 1623010 18490355 := bstep (se 1 (by rfl) ⟨13867766, by rfl⟩ : syracuseStep 18490355 = 27735533) B27735533
theorem B5850107 : Blo 1623010 5850107 := bstep (se 1 (by rfl) ⟨4387580, by rfl⟩ : syracuseStep 5850107 = 8775161) B8775161
theorem B3654665 : Blo 1623010 3654665 := bstep (se 2 (by rfl) ⟨1370499, by rfl⟩ : syracuseStep 3654665 = 2740999) B2740999
theorem B1623087 : Blo 1623010 1623087 := bstep (se 1 (by rfl) ⟨1217315, by rfl⟩ : syracuseStep 1623087 = 2434631) B2434631
theorem B3654719 : Blo 1623010 3654719 := bstep (se 1 (by rfl) ⟨2741039, by rfl⟩ : syracuseStep 3654719 = 5482079) B5482079
theorem B1623151 : Blo 1623010 1623151 := bstep (se 1 (by rfl) ⟨1217363, by rfl⟩ : syracuseStep 1623151 = 2434727) B2434727
theorem B3466361 : Blo 1623010 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B5481593 : Blo 1623010 5481593 := bstep (se 2 (by rfl) ⟨2055597, by rfl⟩ : syracuseStep 5481593 = 4111195) B4111195
theorem B1623207 : Blo 1623010 1623207 := bstep (se 1 (by rfl) ⟨1217405, by rfl⟩ : syracuseStep 1623207 = 2434811) B2434811
theorem B5555375 : Blo 1623010 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B1623231 : Blo 1623010 1623231 := bstep (se 1 (by rfl) ⟨1217423, by rfl⟩ : syracuseStep 1623231 = 2434847) B2434847
theorem B1623263 : Blo 1623010 1623263 := bstep (se 1 (by rfl) ⟨1217447, by rfl⟩ : syracuseStep 1623263 = 2434895) B2434895
theorem B1623343 : Blo 1623010 1623343 := bstep (se 1 (by rfl) ⟨1217507, by rfl⟩ : syracuseStep 1623343 = 2435015) B2435015
theorem B1623579 : Blo 1623010 1623579 := bstep (se 1 (by rfl) ⟨1217684, by rfl⟩ : syracuseStep 1623579 = 2435369) B2435369
theorem B1623583 : Blo 1623010 1623583 := bstep (se 1 (by rfl) ⟨1217687, by rfl⟩ : syracuseStep 1623583 = 2435375) B2435375
theorem B23406245 : Blo 1623010 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B1623743 : Blo 1623010 1623743 := bstep (se 1 (by rfl) ⟨1217807, by rfl⟩ : syracuseStep 1623743 = 2435615) B2435615
theorem B1623999 : Blo 1623010 1623999 := bstep (se 1 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 1623999 = 2435999) B2435999
theorem B5785559 : Blo 1623010 5785559 := bstep (se 1 (by rfl) ⟨4339169, by rfl⟩ : syracuseStep 5785559 = 8678339) B8678339
theorem B2435039 : Blo 1623010 2435039 := bstep (se 1 (by rfl) ⟨1826279, by rfl⟩ : syracuseStep 2435039 = 3652559) B3652559
theorem B1624031 : Blo 1623010 1624031 := bstep (se 1 (by rfl) ⟨1218023, by rfl⟩ : syracuseStep 1624031 = 2436047) B2436047
theorem B2467819 : Blo 1623010 2467819 := bstep (se 1 (by rfl) ⟨1850864, by rfl⟩ : syracuseStep 2467819 = 3701729) B3701729
theorem B2435051 : Blo 1623010 2435051 := bstep (se 1 (by rfl) ⟨1826288, by rfl⟩ : syracuseStep 2435051 = 3652577) B3652577
theorem B2435099 : Blo 1623010 2435099 := bstep (se 1 (by rfl) ⟨1826324, by rfl⟩ : syracuseStep 2435099 = 3652649) B3652649
theorem B1624091 : Blo 1623010 1624091 := bstep (se 1 (by rfl) ⟨1218068, by rfl⟩ : syracuseStep 1624091 = 2436137) B2436137
theorem B1624095 : Blo 1623010 1624095 := bstep (se 1 (by rfl) ⟨1218071, by rfl⟩ : syracuseStep 1624095 = 2436143) B2436143
theorem B1624111 : Blo 1623010 1624111 := bstep (se 1 (by rfl) ⟨1218083, by rfl⟩ : syracuseStep 1624111 = 2436167) B2436167
theorem B3467387 : Blo 1623010 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B1624287 : Blo 1623010 1624287 := bstep (se 1 (by rfl) ⟨1218215, by rfl⟩ : syracuseStep 1624287 = 2436431) B2436431
theorem B1624347 : Blo 1623010 1624347 := bstep (se 1 (by rfl) ⟨1218260, by rfl⟩ : syracuseStep 1624347 = 2436521) B2436521
theorem B1624447 : Blo 1623010 1624447 := bstep (se 1 (by rfl) ⟨1218335, by rfl⟩ : syracuseStep 1624447 = 2436671) B2436671
theorem B2435465 : Blo 1623010 2435465 := bstep (se 2 (by rfl) ⟨913299, by rfl⟩ : syracuseStep 2435465 = 1826599) B1826599
theorem B3083177 : Blo 1623010 3083177 := bstep (se 2 (by rfl) ⟨1156191, by rfl⟩ : syracuseStep 3083177 = 2312383) B2312383
theorem B8334535 : Blo 1623010 8334535 := bstep (se 1 (by rfl) ⟨6250901, by rfl⟩ : syracuseStep 8334535 = 12501803) B12501803
theorem B2436407 : Blo 1623010 2436407 := bstep (se 1 (by rfl) ⟨1827305, by rfl⟩ : syracuseStep 2436407 = 3654611) B3654611
theorem B6933869 : Blo 1623010 6933869 := bstep (se 3 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 6933869 = 2600201) B2600201
theorem B2436575 : Blo 1623010 2436575 := bstep (se 1 (by rfl) ⟨1827431, by rfl⟩ : syracuseStep 2436575 = 3654863) B3654863
theorem B40054283 : Blo 1623010 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B29617687 : Blo 1623010 29617687 := bstep (se 1 (by rfl) ⟨22213265, by rfl⟩ : syracuseStep 29617687 = 44426531) B44426531
theorem B15609509 : Blo 1623010 15609509 := bstep (se 4 (by rfl) ⟨1463391, by rfl⟩ : syracuseStep 15609509 = 2926783) B2926783
theorem B4935551 : Blo 1623010 4935551 := bstep (se 1 (by rfl) ⟨3701663, by rfl⟩ : syracuseStep 4935551 = 7403327) B7403327
theorem B2469881 : Blo 1623010 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B6934567 : Blo 1623010 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B4935775 : Blo 1623010 4935775 := bstep (se 1 (by rfl) ⟨3701831, by rfl⟩ : syracuseStep 4935775 = 7403663) B7403663
theorem B2740331 : Blo 1623010 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B3125375 : Blo 1623010 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B6934909 : Blo 1623010 6934909 := bstep (se 3 (by rfl) ⟨1300295, by rfl⟩ : syracuseStep 6934909 = 2600591) B2600591
theorem B52679089 : Blo 1623010 52679089 := bstep (se 2 (by rfl) ⟨19754658, by rfl⟩ : syracuseStep 52679089 = 39509317) B39509317
theorem B6165305 : Blo 1623010 6165305 := bstep (se 2 (by rfl) ⟨2311989, by rfl⟩ : syracuseStep 6165305 = 4623979) B4623979
theorem B88904729 : Blo 1623010 88904729 := bstep (se 2 (by rfl) ⟨33339273, by rfl⟩ : syracuseStep 88904729 = 66678547) B66678547
theorem B11105707 : Blo 1623010 11105707 := bstep (se 1 (by rfl) ⟨8329280, by rfl⟩ : syracuseStep 11105707 = 16658561) B16658561
theorem B15611777 : Blo 1623010 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B13866947 : Blo 1623010 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B50690225 : Blo 1623010 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B4110527 : Blo 1623010 4110527 := bstep (se 1 (by rfl) ⟨3082895, by rfl⟩ : syracuseStep 4110527 = 6165791) B6165791
theorem B11704619 : Blo 1623010 11704619 := bstep (se 1 (by rfl) ⟨8778464, by rfl⟩ : syracuseStep 11704619 = 17556929) B17556929
theorem B3652127 : Blo 1623010 3652127 := bstep (se 1 (by rfl) ⟨2739095, by rfl⟩ : syracuseStep 3652127 = 5478191) B5478191
theorem B3652361 : Blo 1623010 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B12327875 : Blo 1623010 12327875 := bstep (se 1 (by rfl) ⟨9245906, by rfl⟩ : syracuseStep 12327875 = 18491813) B18491813
theorem B12663823 : Blo 1623010 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B8223929 : Blo 1623010 8223929 := bstep (se 2 (by rfl) ⟨3083973, by rfl⟩ : syracuseStep 8223929 = 6167947) B6167947
theorem B48766171 : Blo 1623010 48766171 := bstep (se 1 (by rfl) ⟨36574628, by rfl⟩ : syracuseStep 48766171 = 73149257) B73149257
theorem B1826023 : Blo 1623010 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B3652937 : Blo 1623010 3652937 := bstep (se 2 (by rfl) ⟨1369851, by rfl⟩ : syracuseStep 3652937 = 2739703) B2739703
theorem B5004791 : Blo 1623010 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B53485067 : Blo 1623010 53485067 := bstep (se 1 (by rfl) ⟨40113800, by rfl⟩ : syracuseStep 53485067 = 80227601) B80227601
theorem B3653351 : Blo 1623010 3653351 := bstep (se 1 (by rfl) ⟨2740013, by rfl⟩ : syracuseStep 3653351 = 5480027) B5480027
theorem B5480189 : Blo 1623010 5480189 := bstep (se 3 (by rfl) ⟨1027535, by rfl⟩ : syracuseStep 5480189 = 2055071) B2055071
theorem B1826671 : Blo 1623010 1826671 := bstep (se 1 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 1826671 = 2740007) B2740007
theorem B16662419 : Blo 1623010 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B1826887 : Blo 1623010 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B88883507 : Blo 1623010 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B3703123 : Blo 1623010 3703123 := bstep (se 1 (by rfl) ⟨2777342, by rfl⟩ : syracuseStep 3703123 = 5554685) B5554685
theorem B70238785 : Blo 1623010 70238785 := bstep (se 2 (by rfl) ⟨26339544, by rfl⟩ : syracuseStep 70238785 = 52679089) B52679089
theorem B3900071 : Blo 1623010 3900071 := bstep (se 1 (by rfl) ⟨2925053, by rfl⟩ : syracuseStep 3900071 = 5850107) B5850107
theorem B59269819 : Blo 1623010 59269819 := bstep (se 1 (by rfl) ⟨44452364, by rfl⟩ : syracuseStep 59269819 = 88904729) B88904729
theorem B3654395 : Blo 1623010 3654395 := bstep (se 1 (by rfl) ⟨2740796, by rfl⟩ : syracuseStep 3654395 = 5481593) B5481593
theorem B31212317 : Blo 1623010 31212317 := bstep (se 3 (by rfl) ⟨5852309, by rfl⟩ : syracuseStep 31212317 = 11704619) B11704619
theorem B3703583 : Blo 1623010 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B1623359 : Blo 1623010 1623359 := bstep (se 1 (by rfl) ⟨1217519, by rfl⟩ : syracuseStep 1623359 = 2435039) B2435039
theorem B1623367 : Blo 1623010 1623367 := bstep (se 1 (by rfl) ⟨1217525, by rfl⟩ : syracuseStep 1623367 = 2435051) B2435051
theorem B1623399 : Blo 1623010 1623399 := bstep (se 1 (by rfl) ⟨1217549, by rfl⟩ : syracuseStep 1623399 = 2435099) B2435099
theorem B16885097 : Blo 1623010 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B2311591 : Blo 1623010 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B33793483 : Blo 1623010 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B1623643 : Blo 1623010 1623643 := bstep (se 1 (by rfl) ⟨1217732, by rfl⟩ : syracuseStep 1623643 = 2435465) B2435465
theorem B65021561 : Blo 1623010 65021561 := bstep (se 2 (by rfl) ⟨24383085, by rfl⟩ : syracuseStep 65021561 = 48766171) B48766171
theorem B2434697 : Blo 1623010 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B2434751 : Blo 1623010 2434751 := bstep (se 1 (by rfl) ⟨1826063, by rfl⟩ : syracuseStep 2434751 = 3652127) B3652127
theorem B2434907 : Blo 1623010 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B8218583 : Blo 1623010 8218583 := bstep (se 1 (by rfl) ⟨6163937, by rfl⟩ : syracuseStep 8218583 = 12327875) B12327875
theorem B5482619 : Blo 1623010 5482619 := bstep (se 1 (by rfl) ⟨4111964, by rfl⟩ : syracuseStep 5482619 = 8223929) B8223929
theorem B1624271 : Blo 1623010 1624271 := bstep (se 1 (by rfl) ⟨1218203, by rfl⟩ : syracuseStep 1624271 = 2436407) B2436407
theorem B2435291 : Blo 1623010 2435291 := bstep (se 1 (by rfl) ⟨1826468, by rfl⟩ : syracuseStep 2435291 = 3652937) B3652937
theorem B1646587 : Blo 1623010 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B4622579 : Blo 1623010 4622579 := bstep (se 1 (by rfl) ⟨3466934, by rfl⟩ : syracuseStep 4622579 = 6933869) B6933869
theorem B1624383 : Blo 1623010 1624383 := bstep (se 1 (by rfl) ⟨1218287, by rfl⟩ : syracuseStep 1624383 = 2436575) B2436575
theorem B3336527 : Blo 1623010 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B10406339 : Blo 1623010 10406339 := bstep (se 1 (by rfl) ⟨7804754, by rfl⟩ : syracuseStep 10406339 = 15609509) B15609509
theorem B2435561 : Blo 1623010 2435561 := bstep (se 2 (by rfl) ⟨913335, by rfl⟩ : syracuseStep 2435561 = 1826671) B1826671
theorem B2435567 : Blo 1623010 2435567 := bstep (se 1 (by rfl) ⟨1826675, by rfl⟩ : syracuseStep 2435567 = 3653351) B3653351
theorem B2083583 : Blo 1623010 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B2435879 : Blo 1623010 2435879 := bstep (se 1 (by rfl) ⟨1826909, by rfl⟩ : syracuseStep 2435879 = 3653819) B3653819
theorem B6581033 : Blo 1623010 6581033 := bstep (se 2 (by rfl) ⟨2467887, by rfl⟩ : syracuseStep 6581033 = 4935775) B4935775
theorem B17558315 : Blo 1623010 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B2435951 : Blo 1623010 2435951 := bstep (se 1 (by rfl) ⟨1826963, by rfl⟩ : syracuseStep 2435951 = 3653927) B3653927
theorem B7908295 : Blo 1623010 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B9243629 : Blo 1623010 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B2436203 : Blo 1623010 2436203 := bstep (se 1 (by rfl) ⟨1827152, by rfl⟩ : syracuseStep 2436203 = 3654305) B3654305
theorem B39513419 : Blo 1623010 39513419 := bstep (se 1 (by rfl) ⟨29635064, by rfl⟩ : syracuseStep 39513419 = 59270129) B59270129
theorem B2436443 : Blo 1623010 2436443 := bstep (se 1 (by rfl) ⟨1827332, by rfl⟩ : syracuseStep 2436443 = 3654665) B3654665
theorem B2436473 : Blo 1623010 2436473 := bstep (se 2 (by rfl) ⟨913677, by rfl⟩ : syracuseStep 2436473 = 1827355) B1827355
theorem B2436479 : Blo 1623010 2436479 := bstep (se 1 (by rfl) ⟨1827359, by rfl⟩ : syracuseStep 2436479 = 3654719) B3654719
theorem B2436713 : Blo 1623010 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B10407851 : Blo 1623010 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B9244631 : Blo 1623010 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B142626845 : Blo 1623010 142626845 := bstep (se 3 (by rfl) ⟨26742533, by rfl⟩ : syracuseStep 142626845 = 53485067) B53485067
theorem B2740351 : Blo 1623010 2740351 := bstep (se 1 (by rfl) ⟨2055263, by rfl⟩ : syracuseStep 2740351 = 4110527) B4110527
theorem B11112713 : Blo 1623010 11112713 := bstep (se 2 (by rfl) ⟨4167267, by rfl⟩ : syracuseStep 11112713 = 8334535) B8334535
theorem B14807609 : Blo 1623010 14807609 := bstep (se 2 (by rfl) ⟨5552853, by rfl⟩ : syracuseStep 14807609 = 11105707) B11105707
theorem B39490249 : Blo 1623010 39490249 := bstep (se 2 (by rfl) ⟨14808843, by rfl⟩ : syracuseStep 39490249 = 29617687) B29617687
theorem B13161469 : Blo 1623010 13161469 := bstep (se 3 (by rfl) ⟨2467775, by rfl⟩ : syracuseStep 13161469 = 4935551) B4935551
theorem B26702855 : Blo 1623010 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B3290425 : Blo 1623010 3290425 := bstep (se 2 (by rfl) ⟨1233909, by rfl⟩ : syracuseStep 3290425 = 2467819) B2467819
theorem B9246089 : Blo 1623010 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B9246271 : Blo 1623010 9246271 := bstep (se 1 (by rfl) ⟨6934703, by rfl⟩ : syracuseStep 9246271 = 13869407) B13869407
theorem B9246545 : Blo 1623010 9246545 := bstep (se 2 (by rfl) ⟨3467454, by rfl⟩ : syracuseStep 9246545 = 6934909) B6934909
theorem B4110203 : Blo 1623010 4110203 := bstep (se 1 (by rfl) ⟨3082652, by rfl⟩ : syracuseStep 4110203 = 6165305) B6165305
theorem B12326903 : Blo 1623010 12326903 := bstep (se 1 (by rfl) ⟨9245177, by rfl⟩ : syracuseStep 12326903 = 18490355) B18490355
theorem B15604163 : Blo 1623010 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B3857039 : Blo 1623010 3857039 := bstep (se 1 (by rfl) ⟨2892779, by rfl⟩ : syracuseStep 3857039 = 5785559) B5785559
theorem B2055451 : Blo 1623010 2055451 := bstep (se 1 (by rfl) ⟨1541588, by rfl⟩ : syracuseStep 2055451 = 3083177) B3083177
theorem B3653459 : Blo 1623010 3653459 := bstep (se 1 (by rfl) ⟨2740094, by rfl⟩ : syracuseStep 3653459 = 5480189) B5480189
theorem B11108279 : Blo 1623010 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B380338253 : Blo 1623010 380338253 := bstep (se 3 (by rfl) ⟨71313422, by rfl⟩ : syracuseStep 380338253 = 142626845) B142626845
theorem B3653801 : Blo 1623010 3653801 := bstep (se 2 (by rfl) ⟨1370175, by rfl⟩ : syracuseStep 3653801 = 2740351) B2740351
theorem B9871739 : Blo 1623010 9871739 := bstep (se 1 (by rfl) ⟨7403804, by rfl⟩ : syracuseStep 9871739 = 14807609) B14807609
theorem B20808211 : Blo 1623010 20808211 := bstep (se 1 (by rfl) ⟨15606158, by rfl⟩ : syracuseStep 20808211 = 31212317) B31212317
theorem B17801903 : Blo 1623010 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B93651713 : Blo 1623010 93651713 := bstep (se 2 (by rfl) ⟨35119392, by rfl⟩ : syracuseStep 93651713 = 70238785) B70238785
theorem B11256731 : Blo 1623010 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B1623131 : Blo 1623010 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B1623167 : Blo 1623010 1623167 := bstep (se 1 (by rfl) ⟨1217375, by rfl⟩ : syracuseStep 1623167 = 2434751) B2434751
theorem B1623271 : Blo 1623010 1623271 := bstep (se 1 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 1623271 = 2434907) B2434907
theorem B10544393 : Blo 1623010 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B8217935 : Blo 1623010 8217935 := bstep (se 1 (by rfl) ⟨6163451, by rfl⟩ : syracuseStep 8217935 = 12326903) B12326903
theorem B17548625 : Blo 1623010 17548625 := bstep (se 2 (by rfl) ⟨6580734, by rfl⟩ : syracuseStep 17548625 = 13161469) B13161469
theorem B3655079 : Blo 1623010 3655079 := bstep (se 1 (by rfl) ⟨2741309, by rfl⟩ : syracuseStep 3655079 = 5482619) B5482619
theorem B1623527 : Blo 1623010 1623527 := bstep (se 1 (by rfl) ⟨1217645, by rfl⟩ : syracuseStep 1623527 = 2435291) B2435291
theorem B3081719 : Blo 1623010 3081719 := bstep (se 1 (by rfl) ⟨2311289, by rfl⟩ : syracuseStep 3081719 = 4622579) B4622579
theorem B17548933 : Blo 1623010 17548933 := bstep (se 4 (by rfl) ⟨1645212, by rfl⟩ : syracuseStep 17548933 = 3290425) B3290425
theorem B1623707 : Blo 1623010 1623707 := bstep (se 1 (by rfl) ⟨1217780, by rfl⟩ : syracuseStep 1623707 = 2435561) B2435561
theorem B1623711 : Blo 1623010 1623711 := bstep (se 1 (by rfl) ⟨1217783, by rfl⟩ : syracuseStep 1623711 = 2435567) B2435567
theorem B1623919 : Blo 1623010 1623919 := bstep (se 1 (by rfl) ⟨1217939, by rfl⟩ : syracuseStep 1623919 = 2435879) B2435879
theorem B3082121 : Blo 1623010 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B1623967 : Blo 1623010 1623967 := bstep (se 1 (by rfl) ⟨1217975, by rfl⟩ : syracuseStep 1623967 = 2435951) B2435951
theorem B45057977 : Blo 1623010 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B6162419 : Blo 1623010 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B5556221 : Blo 1623010 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B1624135 : Blo 1623010 1624135 := bstep (se 1 (by rfl) ⟨1218101, by rfl⟩ : syracuseStep 1624135 = 2436203) B2436203
theorem B1624295 : Blo 1623010 1624295 := bstep (se 1 (by rfl) ⟨1218221, by rfl⟩ : syracuseStep 1624295 = 2436443) B2436443
theorem B1624315 : Blo 1623010 1624315 := bstep (se 1 (by rfl) ⟨1218236, by rfl⟩ : syracuseStep 1624315 = 2436473) B2436473
theorem B1624319 : Blo 1623010 1624319 := bstep (se 1 (by rfl) ⟨1218239, by rfl⟩ : syracuseStep 1624319 = 2436479) B2436479
theorem B1624475 : Blo 1623010 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B2435639 : Blo 1623010 2435639 := bstep (se 1 (by rfl) ⟨1826729, by rfl⟩ : syracuseStep 2435639 = 3653459) B3653459
theorem B6163087 : Blo 1623010 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B2435849 : Blo 1623010 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B7408475 : Blo 1623010 7408475 := bstep (se 1 (by rfl) ⟨5556356, by rfl⟩ : syracuseStep 7408475 = 11112713) B11112713
theorem B2600047 : Blo 1623010 2600047 := bstep (se 1 (by rfl) ⟨1950035, by rfl⟩ : syracuseStep 2600047 = 3900071) B3900071
theorem B2436263 : Blo 1623010 2436263 := bstep (se 1 (by rfl) ⟨1827197, by rfl⟩ : syracuseStep 2436263 = 3654395) B3654395
theorem B2469055 : Blo 1623010 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B237022685 : Blo 1623010 237022685 := bstep (se 3 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 237022685 = 88883507) B88883507
theorem B6164059 : Blo 1623010 6164059 := bstep (se 1 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 6164059 = 9246089) B9246089
theorem B52653665 : Blo 1623010 52653665 := bstep (se 2 (by rfl) ⟨19745124, by rfl⟩ : syracuseStep 52653665 = 39490249) B39490249
theorem B43347707 : Blo 1623010 43347707 := bstep (se 1 (by rfl) ⟨32510780, by rfl⟩ : syracuseStep 43347707 = 65021561) B65021561
theorem B6164363 : Blo 1623010 6164363 := bstep (se 1 (by rfl) ⟨4623272, by rfl⟩ : syracuseStep 6164363 = 9246545) B9246545
theorem B2740135 : Blo 1623010 2740135 := bstep (se 1 (by rfl) ⟨2055101, by rfl⟩ : syracuseStep 2740135 = 4110203) B4110203
theorem B2224351 : Blo 1623010 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B2740601 : Blo 1623010 2740601 := bstep (se 2 (by rfl) ⟨1027725, by rfl⟩ : syracuseStep 2740601 = 2055451) B2055451
theorem B4387355 : Blo 1623010 4387355 := bstep (se 1 (by rfl) ⟨3290516, by rfl⟩ : syracuseStep 4387355 = 6581033) B6581033
theorem B26342279 : Blo 1623010 26342279 := bstep (se 1 (by rfl) ⟨19756709, by rfl⟩ : syracuseStep 26342279 = 39513419) B39513419
theorem B79026425 : Blo 1623010 79026425 := bstep (se 2 (by rfl) ⟨29634909, by rfl⟩ : syracuseStep 79026425 = 59269819) B59269819
theorem B5479055 : Blo 1623010 5479055 := bstep (se 1 (by rfl) ⟨4109291, by rfl⟩ : syracuseStep 5479055 = 8218583) B8218583
theorem B10402775 : Blo 1623010 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B6937559 : Blo 1623010 6937559 := bstep (se 1 (by rfl) ⟨5203169, by rfl⟩ : syracuseStep 6937559 = 10406339) B10406339
theorem B2571359 : Blo 1623010 2571359 := bstep (se 1 (by rfl) ⟨1928519, by rfl⟩ : syracuseStep 2571359 = 3857039) B3857039
theorem B19749989 : Blo 1623010 19749989 := bstep (se 4 (by rfl) ⟨1851561, by rfl⟩ : syracuseStep 19749989 = 3703123) B3703123
theorem B11705543 : Blo 1623010 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B12328361 : Blo 1623010 12328361 := bstep (se 2 (by rfl) ⟨4623135, by rfl⟩ : syracuseStep 12328361 = 9246271) B9246271
theorem B6938567 : Blo 1623010 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B7405519 : Blo 1623010 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B8781797 : Blo 1623010 8781797 := bstep (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) B1646587
theorem B253558835 : Blo 1623010 253558835 := bstep (se 1 (by rfl) ⟨190169126, by rfl⟩ : syracuseStep 253558835 = 380338253) B380338253
theorem B1827067 : Blo 1623010 1827067 := bstep (se 1 (by rfl) ⟨1370300, by rfl⟩ : syracuseStep 1827067 = 2740601) B2740601
theorem B6856957 : Blo 1623010 6856957 := bstep (se 3 (by rfl) ⟨1285679, by rfl⟩ : syracuseStep 6856957 = 2571359) B2571359
theorem B2965801 : Blo 1623010 2965801 := bstep (se 2 (by rfl) ⟨1112175, by rfl⟩ : syracuseStep 2965801 = 2224351) B2224351
theorem B2924903 : Blo 1623010 2924903 := bstep (se 1 (by rfl) ⟨2193677, by rfl⟩ : syracuseStep 2924903 = 4387355) B4387355
theorem B7504487 : Blo 1623010 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B7029595 : Blo 1623010 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B8217449 : Blo 1623010 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B11699083 : Blo 1623010 11699083 := bstep (se 1 (by rfl) ⟨8774312, by rfl⟩ : syracuseStep 11699083 = 17548625) B17548625
theorem B3704147 : Blo 1623010 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B3466729 : Blo 1623010 3466729 := bstep (se 2 (by rfl) ⟨1300023, by rfl⟩ : syracuseStep 3466729 = 2600047) B2600047
theorem B52684283 : Blo 1623010 52684283 := bstep (se 1 (by rfl) ⟨39513212, by rfl⟩ : syracuseStep 52684283 = 79026425) B79026425
theorem B1623759 : Blo 1623010 1623759 := bstep (se 1 (by rfl) ⟨1217819, by rfl⟩ : syracuseStep 1623759 = 2435639) B2435639
theorem B1623899 : Blo 1623010 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B13166659 : Blo 1623010 13166659 := bstep (se 1 (by rfl) ⟨9874994, by rfl⟩ : syracuseStep 13166659 = 19749989) B19749989
theorem B1624175 : Blo 1623010 1624175 := bstep (se 1 (by rfl) ⟨1218131, by rfl⟩ : syracuseStep 1624175 = 2436263) B2436263
theorem B8218745 : Blo 1623010 8218745 := bstep (se 2 (by rfl) ⟨3082029, by rfl⟩ : syracuseStep 8218745 = 6164059) B6164059
theorem B23398577 : Blo 1623010 23398577 := bstep (se 2 (by rfl) ⟨8774466, by rfl⟩ : syracuseStep 23398577 = 17548933) B17548933
theorem B8218907 : Blo 1623010 8218907 := bstep (se 1 (by rfl) ⟨6164180, by rfl⟩ : syracuseStep 8218907 = 12328361) B12328361
theorem B9874025 : Blo 1623010 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B2435867 : Blo 1623010 2435867 := bstep (se 1 (by rfl) ⟨1826900, by rfl⟩ : syracuseStep 2435867 = 3653801) B3653801
theorem B6581159 : Blo 1623010 6581159 := bstep (se 1 (by rfl) ⟨4935869, by rfl⟩ : syracuseStep 6581159 = 9871739) B9871739
theorem B62434475 : Blo 1623010 62434475 := bstep (se 1 (by rfl) ⟨46825856, by rfl⟩ : syracuseStep 62434475 = 93651713) B93651713
theorem B2436719 : Blo 1623010 2436719 := bstep (se 1 (by rfl) ⟨1827539, by rfl⟩ : syracuseStep 2436719 = 3655079) B3655079
theorem B4108279 : Blo 1623010 4108279 := bstep (se 1 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 4108279 = 6162419) B6162419
theorem B6935183 : Blo 1623010 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B4625039 : Blo 1623010 4625039 := bstep (se 1 (by rfl) ⟨3468779, by rfl⟩ : syracuseStep 4625039 = 6937559) B6937559
theorem B7803695 : Blo 1623010 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B28898471 : Blo 1623010 28898471 := bstep (se 1 (by rfl) ⟨21673853, by rfl⟩ : syracuseStep 28898471 = 43347707) B43347707
theorem B4109575 : Blo 1623010 4109575 := bstep (se 1 (by rfl) ⟨3082181, by rfl⟩ : syracuseStep 4109575 = 6164363) B6164363
theorem B4625711 : Blo 1623010 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B5854531 : Blo 1623010 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B17561519 : Blo 1623010 17561519 := bstep (se 1 (by rfl) ⟨13171139, by rfl⟩ : syracuseStep 17561519 = 26342279) B26342279
theorem B27744281 : Blo 1623010 27744281 := bstep (se 2 (by rfl) ⟨10404105, by rfl⟩ : syracuseStep 27744281 = 20808211) B20808211
theorem B5478623 : Blo 1623010 5478623 := bstep (se 1 (by rfl) ⟨4108967, by rfl⟩ : syracuseStep 5478623 = 8217935) B8217935
theorem B2054479 : Blo 1623010 2054479 := bstep (se 1 (by rfl) ⟨1540859, by rfl⟩ : syracuseStep 2054479 = 3081719) B3081719
theorem B2054747 : Blo 1623010 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B30038651 : Blo 1623010 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B3292073 : Blo 1623010 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B3652703 : Blo 1623010 3652703 := bstep (se 1 (by rfl) ⟨2739527, by rfl⟩ : syracuseStep 3652703 = 5479055) B5479055
theorem B47471741 : Blo 1623010 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B4938983 : Blo 1623010 4938983 := bstep (se 1 (by rfl) ⟨3704237, by rfl⟩ : syracuseStep 4938983 = 7408475) B7408475
theorem B158015123 : Blo 1623010 158015123 := bstep (se 1 (by rfl) ⟨118511342, by rfl⟩ : syracuseStep 158015123 = 237022685) B237022685
theorem B35102443 : Blo 1623010 35102443 := bstep (se 1 (by rfl) ⟨26326832, by rfl⟩ : syracuseStep 35102443 = 52653665) B52653665
theorem B3653513 : Blo 1623010 3653513 := bstep (se 2 (by rfl) ⟨1370067, by rfl⟩ : syracuseStep 3653513 = 2740135) B2740135
theorem B17555545 : Blo 1623010 17555545 := bstep (se 2 (by rfl) ⟨6583329, by rfl⟩ : syracuseStep 17555545 = 13166659) B13166659
theorem B1949935 : Blo 1623010 1949935 := bstep (se 1 (by rfl) ⟨1462451, by rfl⟩ : syracuseStep 1949935 = 2924903) B2924903
theorem B77062589 : Blo 1623010 77062589 := bstep (se 3 (by rfl) ⟨14449235, by rfl⟩ : syracuseStep 77062589 = 28898471) B28898471
theorem B5202463 : Blo 1623010 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B11707679 : Blo 1623010 11707679 := bstep (se 1 (by rfl) ⟨8780759, by rfl⟩ : syracuseStep 11707679 = 17561519) B17561519
theorem B36570437 : Blo 1623010 36570437 := bstep (se 4 (by rfl) ⟨3428478, by rfl⟩ : syracuseStep 36570437 = 6856957) B6856957
theorem B15599051 : Blo 1623010 15599051 := bstep (se 1 (by rfl) ⟨11699288, by rfl⟩ : syracuseStep 15599051 = 23398577) B23398577
theorem B1623911 : Blo 1623010 1623911 := bstep (se 1 (by rfl) ⟨1217933, by rfl⟩ : syracuseStep 1623911 = 2435867) B2435867
theorem B4622305 : Blo 1623010 4622305 := bstep (se 2 (by rfl) ⟨1733364, by rfl⟩ : syracuseStep 4622305 = 3466729) B3466729
theorem B2435135 : Blo 1623010 2435135 := bstep (se 1 (by rfl) ⟨1826351, by rfl⟩ : syracuseStep 2435135 = 3652703) B3652703
theorem B31647827 : Blo 1623010 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B46803257 : Blo 1623010 46803257 := bstep (se 2 (by rfl) ⟨17551221, by rfl⟩ : syracuseStep 46803257 = 35102443) B35102443
theorem B1624479 : Blo 1623010 1624479 := bstep (se 1 (by rfl) ⟨1218359, by rfl⟩ : syracuseStep 1624479 = 2436719) B2436719
theorem B105343415 : Blo 1623010 105343415 := bstep (se 1 (by rfl) ⟨79007561, by rfl⟩ : syracuseStep 105343415 = 158015123) B158015123
theorem B2435675 : Blo 1623010 2435675 := bstep (se 1 (by rfl) ⟨1826756, by rfl⟩ : syracuseStep 2435675 = 3653513) B3653513
theorem B2436089 : Blo 1623010 2436089 := bstep (se 2 (by rfl) ⟨913533, by rfl⟩ : syracuseStep 2436089 = 1827067) B1827067
theorem B4623455 : Blo 1623010 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B3083359 : Blo 1623010 3083359 := bstep (se 1 (by rfl) ⟨2312519, by rfl⟩ : syracuseStep 3083359 = 4625039) B4625039
theorem B2739305 : Blo 1623010 2739305 := bstep (se 2 (by rfl) ⟨1027239, by rfl⟩ : syracuseStep 2739305 = 2054479) B2054479
theorem B3083807 : Blo 1623010 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B2469431 : Blo 1623010 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B35122855 : Blo 1623010 35122855 := bstep (se 1 (by rfl) ⟨26342141, by rfl⟩ : syracuseStep 35122855 = 52684283) B52684283
theorem B6582683 : Blo 1623010 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B20025767 : Blo 1623010 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B37491173 : Blo 1623010 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B4387439 : Blo 1623010 4387439 := bstep (se 1 (by rfl) ⟨3290579, by rfl⟩ : syracuseStep 4387439 = 6581159) B6581159
theorem B62395109 : Blo 1623010 62395109 := bstep (se 4 (by rfl) ⟨5849541, by rfl⟩ : syracuseStep 62395109 = 11699083) B11699083
theorem B5477705 : Blo 1623010 5477705 := bstep (se 2 (by rfl) ⟨2054139, by rfl⟩ : syracuseStep 5477705 = 4108279) B4108279
theorem B169039223 : Blo 1623010 169039223 := bstep (se 1 (by rfl) ⟨126779417, by rfl⟩ : syracuseStep 169039223 = 253558835) B253558835
theorem B3954401 : Blo 1623010 3954401 := bstep (se 2 (by rfl) ⟨1482900, by rfl⟩ : syracuseStep 3954401 = 2965801) B2965801
theorem B5002991 : Blo 1623010 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B5478299 : Blo 1623010 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B18496187 : Blo 1623010 18496187 := bstep (se 1 (by rfl) ⟨13872140, by rfl⟩ : syracuseStep 18496187 = 27744281) B27744281
theorem B5479163 : Blo 1623010 5479163 := bstep (se 1 (by rfl) ⟨4109372, by rfl⟩ : syracuseStep 5479163 = 8218745) B8218745
theorem B3652415 : Blo 1623010 3652415 := bstep (se 1 (by rfl) ⟨2739311, by rfl⟩ : syracuseStep 3652415 = 5478623) B5478623
theorem B5479271 : Blo 1623010 5479271 := bstep (se 1 (by rfl) ⟨4109453, by rfl⟩ : syracuseStep 5479271 = 8218907) B8218907
theorem B5479325 : Blo 1623010 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B5479433 : Blo 1623010 5479433 := bstep (se 2 (by rfl) ⟨2054787, by rfl⟩ : syracuseStep 5479433 = 4109575) B4109575
theorem B7806041 : Blo 1623010 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B2194715 : Blo 1623010 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B41622983 : Blo 1623010 41622983 := bstep (se 1 (by rfl) ⟨31217237, by rfl⟩ : syracuseStep 41622983 = 62434475) B62434475
theorem B3292655 : Blo 1623010 3292655 := bstep (se 1 (by rfl) ⟨2469491, by rfl⟩ : syracuseStep 3292655 = 4938983) B4938983
theorem B24994115 : Blo 1623010 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B2924959 : Blo 1623010 2924959 := bstep (se 1 (by rfl) ⟨2193719, by rfl⟩ : syracuseStep 2924959 = 4387439) B4387439
theorem B24380291 : Blo 1623010 24380291 := bstep (se 1 (by rfl) ⟨18285218, by rfl⟩ : syracuseStep 24380291 = 36570437) B36570437
theorem B3335327 : Blo 1623010 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B1623423 : Blo 1623010 1623423 := bstep (se 1 (by rfl) ⟨1217567, by rfl⟩ : syracuseStep 1623423 = 2435135) B2435135
theorem B1623783 : Blo 1623010 1623783 := bstep (se 1 (by rfl) ⟨1217837, by rfl⟩ : syracuseStep 1623783 = 2435675) B2435675
theorem B12330791 : Blo 1623010 12330791 := bstep (se 1 (by rfl) ⟨9248093, by rfl⟩ : syracuseStep 12330791 = 18496187) B18496187
theorem B2434943 : Blo 1623010 2434943 := bstep (se 1 (by rfl) ⟨1826207, by rfl⟩ : syracuseStep 2434943 = 3652415) B3652415
theorem B1624059 : Blo 1623010 1624059 := bstep (se 1 (by rfl) ⟨1218044, by rfl⟩ : syracuseStep 1624059 = 2436089) B2436089
theorem B5204027 : Blo 1623010 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B3082303 : Blo 1623010 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B27748655 : Blo 1623010 27748655 := bstep (se 1 (by rfl) ⟨20811491, by rfl⟩ : syracuseStep 27748655 = 41622983) B41622983
theorem B6163073 : Blo 1623010 6163073 := bstep (se 2 (by rfl) ⟨2311152, by rfl⟩ : syracuseStep 6163073 = 4622305) B4622305
theorem B23407393 : Blo 1623010 23407393 := bstep (se 2 (by rfl) ⟨8777772, by rfl⟩ : syracuseStep 23407393 = 17555545) B17555545
theorem B51375059 : Blo 1623010 51375059 := bstep (se 1 (by rfl) ⟨38531294, by rfl⟩ : syracuseStep 51375059 = 77062589) B77062589
theorem B2599913 : Blo 1623010 2599913 := bstep (se 2 (by rfl) ⟨974967, by rfl⟩ : syracuseStep 2599913 = 1949935) B1949935
theorem B5852573 : Blo 1623010 5852573 := bstep (se 3 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 5852573 = 2194715) B2194715
theorem B112692815 : Blo 1623010 112692815 := bstep (se 1 (by rfl) ⟨84519611, by rfl⟩ : syracuseStep 112692815 = 169039223) B169039223
theorem B10399367 : Blo 1623010 10399367 := bstep (se 1 (by rfl) ⟨7799525, by rfl⟩ : syracuseStep 10399367 = 15599051) B15599051
theorem B21098551 : Blo 1623010 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B46830473 : Blo 1623010 46830473 := bstep (se 2 (by rfl) ⟨17561427, by rfl⟩ : syracuseStep 46830473 = 35122855) B35122855
theorem B4388455 : Blo 1623010 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B13350511 : Blo 1623010 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B41596739 : Blo 1623010 41596739 := bstep (se 1 (by rfl) ⟨31197554, by rfl⟩ : syracuseStep 41596739 = 62395109) B62395109
theorem B6936617 : Blo 1623010 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B7805119 : Blo 1623010 7805119 := bstep (se 1 (by rfl) ⟨5853839, by rfl⟩ : syracuseStep 7805119 = 11707679) B11707679
theorem B3651803 : Blo 1623010 3651803 := bstep (se 1 (by rfl) ⟨2738852, by rfl⟩ : syracuseStep 3651803 = 5477705) B5477705
theorem B3652199 : Blo 1623010 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B8780413 : Blo 1623010 8780413 := bstep (se 3 (by rfl) ⟨1646327, by rfl⟩ : syracuseStep 8780413 = 3292655) B3292655
theorem B4111145 : Blo 1623010 4111145 := bstep (se 2 (by rfl) ⟨1541679, by rfl⟩ : syracuseStep 4111145 = 3083359) B3083359
theorem B31202171 : Blo 1623010 31202171 := bstep (se 1 (by rfl) ⟨23401628, by rfl⟩ : syracuseStep 31202171 = 46803257) B46803257
theorem B70228943 : Blo 1623010 70228943 := bstep (se 1 (by rfl) ⟨52671707, by rfl⟩ : syracuseStep 70228943 = 105343415) B105343415
theorem B3652775 : Blo 1623010 3652775 := bstep (se 1 (by rfl) ⟨2739581, by rfl⟩ : syracuseStep 3652775 = 5479163) B5479163
theorem B3652847 : Blo 1623010 3652847 := bstep (se 1 (by rfl) ⟨2739635, by rfl⟩ : syracuseStep 3652847 = 5479271) B5479271
theorem B3652883 : Blo 1623010 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B3652955 : Blo 1623010 3652955 := bstep (se 1 (by rfl) ⟨2739716, by rfl⟩ : syracuseStep 3652955 = 5479433) B5479433
theorem B1826203 : Blo 1623010 1826203 := bstep (se 1 (by rfl) ⟨1369652, by rfl⟩ : syracuseStep 1826203 = 2739305) B2739305
theorem B42180277 : Blo 1623010 42180277 := bstep (se 5 (by rfl) ⟨1977200, by rfl⟩ : syracuseStep 42180277 = 3954401) B3954401
theorem B2055871 : Blo 1623010 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B1646287 : Blo 1623010 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B28131401 : Blo 1623010 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B18497645 : Blo 1623010 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B13877405 : Blo 1623010 13877405 := bstep (se 3 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 13877405 = 5204027) B5204027
theorem B16662743 : Blo 1623010 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B3899945 : Blo 1623010 3899945 := bstep (se 2 (by rfl) ⟨1462479, by rfl⟩ : syracuseStep 3899945 = 2924959) B2924959
theorem B31220315 : Blo 1623010 31220315 := bstep (se 1 (by rfl) ⟨23415236, by rfl⟩ : syracuseStep 31220315 = 46830473) B46830473
theorem B11707217 : Blo 1623010 11707217 := bstep (se 2 (by rfl) ⟨4390206, by rfl⟩ : syracuseStep 11707217 = 8780413) B8780413
theorem B27731159 : Blo 1623010 27731159 := bstep (se 1 (by rfl) ⟨20798369, by rfl⟩ : syracuseStep 27731159 = 41596739) B41596739
theorem B1623295 : Blo 1623010 1623295 := bstep (se 1 (by rfl) ⟨1217471, by rfl⟩ : syracuseStep 1623295 = 2434943) B2434943
theorem B2434535 : Blo 1623010 2434535 := bstep (se 1 (by rfl) ⟨1825901, by rfl⟩ : syracuseStep 2434535 = 3651803) B3651803
theorem B18499103 : Blo 1623010 18499103 := bstep (se 1 (by rfl) ⟨13874327, by rfl⟩ : syracuseStep 18499103 = 27748655) B27748655
theorem B2434799 : Blo 1623010 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B2434937 : Blo 1623010 2434937 := bstep (se 2 (by rfl) ⟨913101, by rfl⟩ : syracuseStep 2434937 = 1826203) B1826203
theorem B20801447 : Blo 1623010 20801447 := bstep (se 1 (by rfl) ⟨15601085, by rfl⟩ : syracuseStep 20801447 = 31202171) B31202171
theorem B46819295 : Blo 1623010 46819295 := bstep (se 1 (by rfl) ⟨35114471, by rfl⟩ : syracuseStep 46819295 = 70228943) B70228943
theorem B2435183 : Blo 1623010 2435183 := bstep (se 1 (by rfl) ⟨1826387, by rfl⟩ : syracuseStep 2435183 = 3652775) B3652775
theorem B5851273 : Blo 1623010 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B2435231 : Blo 1623010 2435231 := bstep (se 1 (by rfl) ⟨1826423, by rfl⟩ : syracuseStep 2435231 = 3652847) B3652847
theorem B2435255 : Blo 1623010 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B2435303 : Blo 1623010 2435303 := bstep (se 1 (by rfl) ⟨1826477, by rfl⟩ : syracuseStep 2435303 = 3652955) B3652955
theorem B56240369 : Blo 1623010 56240369 := bstep (se 2 (by rfl) ⟨21090138, by rfl⟩ : syracuseStep 56240369 = 42180277) B42180277
theorem B3901715 : Blo 1623010 3901715 := bstep (se 1 (by rfl) ⟨2926286, by rfl⟩ : syracuseStep 3901715 = 5852573) B5852573
theorem B65014109 : Blo 1623010 65014109 := bstep (se 3 (by rfl) ⟨12190145, by rfl⟩ : syracuseStep 65014109 = 24380291) B24380291
theorem B6932911 : Blo 1623010 6932911 := bstep (se 1 (by rfl) ⟨5199683, by rfl⟩ : syracuseStep 6932911 = 10399367) B10399367
theorem B10406825 : Blo 1623010 10406825 := bstep (se 2 (by rfl) ⟨3902559, by rfl⟩ : syracuseStep 10406825 = 7805119) B7805119
theorem B2223551 : Blo 1623010 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B8220527 : Blo 1623010 8220527 := bstep (se 1 (by rfl) ⟨6165395, by rfl⟩ : syracuseStep 8220527 = 12330791) B12330791
theorem B4108715 : Blo 1623010 4108715 := bstep (se 1 (by rfl) ⟨3081536, by rfl⟩ : syracuseStep 4108715 = 6163073) B6163073
theorem B2740763 : Blo 1623010 2740763 := bstep (se 1 (by rfl) ⟨2055572, by rfl⟩ : syracuseStep 2740763 = 4111145) B4111145
theorem B1733275 : Blo 1623010 1733275 := bstep (se 1 (by rfl) ⟨1299956, by rfl⟩ : syracuseStep 1733275 = 2599913) B2599913
theorem B2741161 : Blo 1623010 2741161 := bstep (se 2 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 2741161 = 2055871) B2055871
theorem B4109737 : Blo 1623010 4109737 := bstep (se 2 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 4109737 = 3082303) B3082303
theorem B31209857 : Blo 1623010 31209857 := bstep (se 2 (by rfl) ⟨11703696, by rfl⟩ : syracuseStep 31209857 = 23407393) B23407393
theorem B8780197 : Blo 1623010 8780197 := bstep (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) B1646287
theorem B34250039 : Blo 1623010 34250039 := bstep (se 1 (by rfl) ⟨25687529, by rfl⟩ : syracuseStep 34250039 = 51375059) B51375059
theorem B17800681 : Blo 1623010 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B75128543 : Blo 1623010 75128543 := bstep (se 1 (by rfl) ⟨56346407, by rfl⟩ : syracuseStep 75128543 = 112692815) B112692815
theorem B11108495 : Blo 1623010 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B1827175 : Blo 1623010 1827175 := bstep (se 1 (by rfl) ⟨1370381, by rfl⟩ : syracuseStep 1827175 = 2740763) B2740763
theorem B11706929 : Blo 1623010 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B2311033 : Blo 1623010 2311033 := bstep (se 2 (by rfl) ⟨866637, by rfl⟩ : syracuseStep 2311033 = 1733275) B1733275
theorem B1623023 : Blo 1623010 1623023 := bstep (se 1 (by rfl) ⟨1217267, by rfl⟩ : syracuseStep 1623023 = 2434535) B2434535
theorem B1623199 : Blo 1623010 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B3654881 : Blo 1623010 3654881 := bstep (se 2 (by rfl) ⟨1370580, by rfl⟩ : syracuseStep 3654881 = 2741161) B2741161
theorem B1623291 : Blo 1623010 1623291 := bstep (se 1 (by rfl) ⟨1217468, by rfl⟩ : syracuseStep 1623291 = 2434937) B2434937
theorem B31212863 : Blo 1623010 31212863 := bstep (se 1 (by rfl) ⟨23409647, by rfl⟩ : syracuseStep 31212863 = 46819295) B46819295
theorem B1623455 : Blo 1623010 1623455 := bstep (se 1 (by rfl) ⟨1217591, by rfl⟩ : syracuseStep 1623455 = 2435183) B2435183
theorem B1623487 : Blo 1623010 1623487 := bstep (se 1 (by rfl) ⟨1217615, by rfl⟩ : syracuseStep 1623487 = 2435231) B2435231
theorem B1623503 : Blo 1623010 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B1623535 : Blo 1623010 1623535 := bstep (se 1 (by rfl) ⟨1217651, by rfl⟩ : syracuseStep 1623535 = 2435303) B2435303
theorem B23734241 : Blo 1623010 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B22833359 : Blo 1623010 22833359 := bstep (se 1 (by rfl) ⟨17125019, by rfl⟩ : syracuseStep 22833359 = 34250039) B34250039
theorem B18754267 : Blo 1623010 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B12331763 : Blo 1623010 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B9251603 : Blo 1623010 9251603 := bstep (se 1 (by rfl) ⟨6938702, by rfl⟩ : syracuseStep 9251603 = 13877405) B13877405
theorem B7801697 : Blo 1623010 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B2739143 : Blo 1623010 2739143 := bstep (se 1 (by rfl) ⟨2054357, by rfl⟩ : syracuseStep 2739143 = 4108715) B4108715
theorem B9243881 : Blo 1623010 9243881 := bstep (se 2 (by rfl) ⟨3466455, by rfl⟩ : syracuseStep 9243881 = 6932911) B6932911
theorem B12332735 : Blo 1623010 12332735 := bstep (se 1 (by rfl) ⟨9249551, by rfl⟩ : syracuseStep 12332735 = 18499103) B18499103
theorem B10399853 : Blo 1623010 10399853 := bstep (se 3 (by rfl) ⟨1949972, by rfl⟩ : syracuseStep 10399853 = 3899945) B3899945
theorem B2601143 : Blo 1623010 2601143 := bstep (se 1 (by rfl) ⟨1950857, by rfl⟩ : syracuseStep 2601143 = 3901715) B3901715
theorem B20813543 : Blo 1623010 20813543 := bstep (se 1 (by rfl) ⟨15610157, by rfl⟩ : syracuseStep 20813543 = 31220315) B31220315
theorem B7804811 : Blo 1623010 7804811 := bstep (se 1 (by rfl) ⟨5853608, by rfl⟩ : syracuseStep 7804811 = 11707217) B11707217
theorem B18487439 : Blo 1623010 18487439 := bstep (se 1 (by rfl) ⟨13865579, by rfl⟩ : syracuseStep 18487439 = 27731159) B27731159
theorem B5929469 : Blo 1623010 5929469 := bstep (se 3 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 5929469 = 2223551) B2223551
theorem B13867631 : Blo 1623010 13867631 := bstep (se 1 (by rfl) ⟨10400723, by rfl⟩ : syracuseStep 13867631 = 20801447) B20801447
theorem B37493579 : Blo 1623010 37493579 := bstep (se 1 (by rfl) ⟨28120184, by rfl⟩ : syracuseStep 37493579 = 56240369) B56240369
theorem B43342739 : Blo 1623010 43342739 := bstep (se 1 (by rfl) ⟨32507054, by rfl⟩ : syracuseStep 43342739 = 65014109) B65014109
theorem B20806571 : Blo 1623010 20806571 := bstep (se 1 (by rfl) ⟨15604928, by rfl⟩ : syracuseStep 20806571 = 31209857) B31209857
theorem B5479649 : Blo 1623010 5479649 := bstep (se 2 (by rfl) ⟨2054868, by rfl⟩ : syracuseStep 5479649 = 4109737) B4109737
theorem B6937883 : Blo 1623010 6937883 := bstep (se 1 (by rfl) ⟨5203412, by rfl⟩ : syracuseStep 6937883 = 10406825) B10406825
theorem B50085695 : Blo 1623010 50085695 := bstep (se 1 (by rfl) ⟨37564271, by rfl⟩ : syracuseStep 50085695 = 75128543) B75128543
theorem B5480351 : Blo 1623010 5480351 := bstep (se 1 (by rfl) ⟨4110263, by rfl⟩ : syracuseStep 5480351 = 8220527) B8220527
theorem B7405663 : Blo 1623010 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B20808575 : Blo 1623010 20808575 := bstep (se 1 (by rfl) ⟨15606431, by rfl⟩ : syracuseStep 20808575 = 31212863) B31212863
theorem B3081377 : Blo 1623010 3081377 := bstep (se 2 (by rfl) ⟨1155516, by rfl⟩ : syracuseStep 3081377 = 2311033) B2311033
theorem B5203207 : Blo 1623010 5203207 := bstep (se 1 (by rfl) ⟨3902405, by rfl⟩ : syracuseStep 5203207 = 7804811) B7804811
theorem B15222239 : Blo 1623010 15222239 := bstep (se 1 (by rfl) ⟨11416679, by rfl⟩ : syracuseStep 15222239 = 22833359) B22833359
theorem B24995719 : Blo 1623010 24995719 := bstep (se 1 (by rfl) ⟨18746789, by rfl⟩ : syracuseStep 24995719 = 37493579) B37493579
theorem B28895159 : Blo 1623010 28895159 := bstep (se 1 (by rfl) ⟨21671369, by rfl⟩ : syracuseStep 28895159 = 43342739) B43342739
theorem B13871047 : Blo 1623010 13871047 := bstep (se 1 (by rfl) ⟨10403285, by rfl⟩ : syracuseStep 13871047 = 20806571) B20806571
theorem B6162587 : Blo 1623010 6162587 := bstep (se 1 (by rfl) ⟨4621940, by rfl⟩ : syracuseStep 6162587 = 9243881) B9243881
theorem B6933235 : Blo 1623010 6933235 := bstep (se 1 (by rfl) ⟨5199926, by rfl⟩ : syracuseStep 6933235 = 10399853) B10399853
theorem B2436233 : Blo 1623010 2436233 := bstep (se 2 (by rfl) ⟨913587, by rfl⟩ : syracuseStep 2436233 = 1827175) B1827175
theorem B2436587 : Blo 1623010 2436587 := bstep (se 1 (by rfl) ⟨1827440, by rfl⟩ : syracuseStep 2436587 = 3654881) B3654881
theorem B25005689 : Blo 1623010 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B15822827 : Blo 1623010 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B12324959 : Blo 1623010 12324959 := bstep (se 1 (by rfl) ⟨9243719, by rfl⟩ : syracuseStep 12324959 = 18487439) B18487439
theorem B3952979 : Blo 1623010 3952979 := bstep (se 1 (by rfl) ⟨2964734, by rfl⟩ : syracuseStep 3952979 = 5929469) B5929469
theorem B9245087 : Blo 1623010 9245087 := bstep (se 1 (by rfl) ⟨6933815, by rfl⟩ : syracuseStep 9245087 = 13867631) B13867631
theorem B8221175 : Blo 1623010 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B4625255 : Blo 1623010 4625255 := bstep (se 1 (by rfl) ⟨3468941, by rfl⟩ : syracuseStep 4625255 = 6937883) B6937883
theorem B8221823 : Blo 1623010 8221823 := bstep (se 1 (by rfl) ⟨6166367, by rfl⟩ : syracuseStep 8221823 = 12332735) B12332735
theorem B1734095 : Blo 1623010 1734095 := bstep (se 1 (by rfl) ⟨1300571, by rfl⟩ : syracuseStep 1734095 = 2601143) B2601143
theorem B7804619 : Blo 1623010 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B13875695 : Blo 1623010 13875695 := bstep (se 1 (by rfl) ⟨10406771, by rfl⟩ : syracuseStep 13875695 = 20813543) B20813543
theorem B6167735 : Blo 1623010 6167735 := bstep (se 1 (by rfl) ⟨4625801, by rfl⟩ : syracuseStep 6167735 = 9251603) B9251603
theorem B5201131 : Blo 1623010 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B1826095 : Blo 1623010 1826095 := bstep (se 1 (by rfl) ⟨1369571, by rfl⟩ : syracuseStep 1826095 = 2739143) B2739143
theorem B3653099 : Blo 1623010 3653099 := bstep (se 1 (by rfl) ⟨2739824, by rfl⟩ : syracuseStep 3653099 = 5479649) B5479649
theorem B33390463 : Blo 1623010 33390463 := bstep (se 1 (by rfl) ⟨25042847, by rfl⟩ : syracuseStep 33390463 = 50085695) B50085695
theorem B3653567 : Blo 1623010 3653567 := bstep (se 1 (by rfl) ⟨2740175, by rfl⟩ : syracuseStep 3653567 = 5480351) B5480351
theorem B8216639 : Blo 1623010 8216639 := bstep (se 1 (by rfl) ⟨6162479, by rfl⟩ : syracuseStep 8216639 = 12324959) B12324959
theorem B5480783 : Blo 1623010 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B5481215 : Blo 1623010 5481215 := bstep (se 1 (by rfl) ⟨4110911, by rfl⟩ : syracuseStep 5481215 = 8221823) B8221823
theorem B5203079 : Blo 1623010 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B9250463 : Blo 1623010 9250463 := bstep (se 1 (by rfl) ⟨6937847, by rfl⟩ : syracuseStep 9250463 = 13875695) B13875695
theorem B2434793 : Blo 1623010 2434793 := bstep (se 2 (by rfl) ⟨913047, by rfl⟩ : syracuseStep 2434793 = 1826095) B1826095
theorem B1624155 : Blo 1623010 1624155 := bstep (se 1 (by rfl) ⟨1218116, by rfl⟩ : syracuseStep 1624155 = 2436233) B2436233
theorem B2435399 : Blo 1623010 2435399 := bstep (se 1 (by rfl) ⟨1826549, by rfl⟩ : syracuseStep 2435399 = 3653099) B3653099
theorem B1624391 : Blo 1623010 1624391 := bstep (se 1 (by rfl) ⟨1218293, by rfl⟩ : syracuseStep 1624391 = 2436587) B2436587
theorem B33327625 : Blo 1623010 33327625 := bstep (se 2 (by rfl) ⟨12497859, by rfl⟩ : syracuseStep 33327625 = 24995719) B24995719
theorem B2435711 : Blo 1623010 2435711 := bstep (se 1 (by rfl) ⟨1826783, by rfl⟩ : syracuseStep 2435711 = 3653567) B3653567
theorem B9874217 : Blo 1623010 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B6163391 : Blo 1623010 6163391 := bstep (se 1 (by rfl) ⟨4622543, by rfl⟩ : syracuseStep 6163391 = 9245087) B9245087
theorem B3083503 : Blo 1623010 3083503 := bstep (se 1 (by rfl) ⟨2312627, by rfl⟩ : syracuseStep 3083503 = 4625255) B4625255
theorem B13872383 : Blo 1623010 13872383 := bstep (se 1 (by rfl) ⟨10404287, by rfl⟩ : syracuseStep 13872383 = 20808575) B20808575
theorem B9244313 : Blo 1623010 9244313 := bstep (se 2 (by rfl) ⟨3466617, by rfl⟩ : syracuseStep 9244313 = 6933235) B6933235
theorem B4624253 : Blo 1623010 4624253 := bstep (se 3 (by rfl) ⟨867047, by rfl⟩ : syracuseStep 4624253 = 1734095) B1734095
theorem B19263439 : Blo 1623010 19263439 := bstep (se 1 (by rfl) ⟨14447579, by rfl⟩ : syracuseStep 19263439 = 28895159) B28895159
theorem B4108391 : Blo 1623010 4108391 := bstep (se 1 (by rfl) ⟨3081293, by rfl⟩ : syracuseStep 4108391 = 6162587) B6162587
theorem B6934841 : Blo 1623010 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B44520617 : Blo 1623010 44520617 := bstep (se 2 (by rfl) ⟨16695231, by rfl⟩ : syracuseStep 44520617 = 33390463) B33390463
theorem B18494729 : Blo 1623010 18494729 := bstep (se 2 (by rfl) ⟨6935523, by rfl⟩ : syracuseStep 18494729 = 13871047) B13871047
theorem B10548551 : Blo 1623010 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B2635319 : Blo 1623010 2635319 := bstep (se 1 (by rfl) ⟨1976489, by rfl⟩ : syracuseStep 2635319 = 3952979) B3952979
theorem B2054251 : Blo 1623010 2054251 := bstep (se 1 (by rfl) ⟨1540688, by rfl⟩ : syracuseStep 2054251 = 3081377) B3081377
theorem B10148159 : Blo 1623010 10148159 := bstep (se 1 (by rfl) ⟨7611119, by rfl⟩ : syracuseStep 10148159 = 15222239) B15222239
theorem B6937609 : Blo 1623010 6937609 := bstep (se 2 (by rfl) ⟨2601603, by rfl⟩ : syracuseStep 6937609 = 5203207) B5203207
theorem B4111823 : Blo 1623010 4111823 := bstep (se 1 (by rfl) ⟨3083867, by rfl⟩ : syracuseStep 4111823 = 6167735) B6167735
theorem B16670459 : Blo 1623010 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B3653855 : Blo 1623010 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B3654143 : Blo 1623010 3654143 := bstep (se 1 (by rfl) ⟨2740607, by rfl⟩ : syracuseStep 3654143 = 5481215) B5481215
theorem B29680411 : Blo 1623010 29680411 := bstep (se 1 (by rfl) ⟨22260308, by rfl⟩ : syracuseStep 29680411 = 44520617) B44520617
theorem B12329819 : Blo 1623010 12329819 := bstep (se 1 (by rfl) ⟨9247364, by rfl⟩ : syracuseStep 12329819 = 18494729) B18494729
theorem B1623195 : Blo 1623010 1623195 := bstep (se 1 (by rfl) ⟨1217396, by rfl⟩ : syracuseStep 1623195 = 2434793) B2434793
theorem B9250145 : Blo 1623010 9250145 := bstep (se 2 (by rfl) ⟨3468804, by rfl⟩ : syracuseStep 9250145 = 6937609) B6937609
theorem B1623599 : Blo 1623010 1623599 := bstep (se 1 (by rfl) ⟨1217699, by rfl⟩ : syracuseStep 1623599 = 2435399) B2435399
theorem B1623807 : Blo 1623010 1623807 := bstep (se 1 (by rfl) ⟨1217855, by rfl⟩ : syracuseStep 1623807 = 2435711) B2435711
theorem B102738341 : Blo 1623010 102738341 := bstep (se 4 (by rfl) ⟨9631719, by rfl⟩ : syracuseStep 102738341 = 19263439) B19263439
theorem B6162875 : Blo 1623010 6162875 := bstep (se 1 (by rfl) ⟨4622156, by rfl⟩ : syracuseStep 6162875 = 9244313) B9244313
theorem B3082835 : Blo 1623010 3082835 := bstep (se 1 (by rfl) ⟨2312126, by rfl⟩ : syracuseStep 3082835 = 4624253) B4624253
theorem B2738927 : Blo 1623010 2738927 := bstep (se 1 (by rfl) ⟨2054195, by rfl⟩ : syracuseStep 2738927 = 4108391) B4108391
theorem B2739001 : Blo 1623010 2739001 := bstep (se 2 (by rfl) ⟨1027125, by rfl⟩ : syracuseStep 2739001 = 2054251) B2054251
theorem B4623227 : Blo 1623010 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B44436833 : Blo 1623010 44436833 := bstep (se 2 (by rfl) ⟨16663812, by rfl⟩ : syracuseStep 44436833 = 33327625) B33327625
theorem B3468719 : Blo 1623010 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B7032367 : Blo 1623010 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B1756879 : Blo 1623010 1756879 := bstep (se 1 (by rfl) ⟨1317659, by rfl⟩ : syracuseStep 1756879 = 2635319) B2635319
theorem B6582811 : Blo 1623010 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B4108927 : Blo 1623010 4108927 := bstep (se 1 (by rfl) ⟨3081695, by rfl⟩ : syracuseStep 4108927 = 6163391) B6163391
theorem B44454557 : Blo 1623010 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B2741215 : Blo 1623010 2741215 := bstep (se 1 (by rfl) ⟨2055911, by rfl⟩ : syracuseStep 2741215 = 4111823) B4111823
theorem B5477759 : Blo 1623010 5477759 := bstep (se 1 (by rfl) ⟨4108319, by rfl⟩ : syracuseStep 5477759 = 8216639) B8216639
theorem B6166975 : Blo 1623010 6166975 := bstep (se 1 (by rfl) ⟨4625231, by rfl⟩ : syracuseStep 6166975 = 9250463) B9250463
theorem B6765439 : Blo 1623010 6765439 := bstep (se 1 (by rfl) ⟨5074079, by rfl⟩ : syracuseStep 6765439 = 10148159) B10148159
theorem B4111337 : Blo 1623010 4111337 := bstep (se 2 (by rfl) ⟨1541751, by rfl⟩ : syracuseStep 4111337 = 3083503) B3083503
theorem B9248255 : Blo 1623010 9248255 := bstep (se 1 (by rfl) ⟨6936191, by rfl⟩ : syracuseStep 9248255 = 13872383) B13872383
theorem B9020585 : Blo 1623010 9020585 := bstep (se 2 (by rfl) ⟨3382719, by rfl⟩ : syracuseStep 9020585 = 6765439) B6765439
theorem B3654953 : Blo 1623010 3654953 := bstep (se 2 (by rfl) ⟨1370607, by rfl⟩ : syracuseStep 3654953 = 2741215) B2741215
theorem B37480085 : Blo 1623010 37480085 := bstep (se 6 (by rfl) ⟨878439, by rfl⟩ : syracuseStep 37480085 = 1756879) B1756879
theorem B3082151 : Blo 1623010 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B29624555 : Blo 1623010 29624555 := bstep (se 1 (by rfl) ⟨22218416, by rfl⟩ : syracuseStep 29624555 = 44436833) B44436833
theorem B2312479 : Blo 1623010 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B2435903 : Blo 1623010 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B2436095 : Blo 1623010 2436095 := bstep (se 1 (by rfl) ⟨1827071, by rfl⟩ : syracuseStep 2436095 = 3654143) B3654143
theorem B8219879 : Blo 1623010 8219879 := bstep (se 1 (by rfl) ⟨6164909, by rfl⟩ : syracuseStep 8219879 = 12329819) B12329819
theorem B8777081 : Blo 1623010 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B4108583 : Blo 1623010 4108583 := bstep (se 1 (by rfl) ⟨3081437, by rfl⟩ : syracuseStep 4108583 = 6162875) B6162875
theorem B2740891 : Blo 1623010 2740891 := bstep (se 1 (by rfl) ⟨2055668, by rfl⟩ : syracuseStep 2740891 = 4111337) B4111337
theorem B9376489 : Blo 1623010 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B6165503 : Blo 1623010 6165503 := bstep (se 1 (by rfl) ⟨4624127, by rfl⟩ : syracuseStep 6165503 = 9248255) B9248255
theorem B29636371 : Blo 1623010 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B8222633 : Blo 1623010 8222633 := bstep (se 2 (by rfl) ⟨3083487, by rfl⟩ : syracuseStep 8222633 = 6166975) B6166975
theorem B5478569 : Blo 1623010 5478569 := bstep (se 2 (by rfl) ⟨2054463, by rfl⟩ : syracuseStep 5478569 = 4108927) B4108927
theorem B6166763 : Blo 1623010 6166763 := bstep (se 1 (by rfl) ⟨4625072, by rfl⟩ : syracuseStep 6166763 = 9250145) B9250145
theorem B3651839 : Blo 1623010 3651839 := bstep (se 1 (by rfl) ⟨2738879, by rfl⟩ : syracuseStep 3651839 = 5477759) B5477759
theorem B39573881 : Blo 1623010 39573881 := bstep (se 2 (by rfl) ⟨14840205, by rfl⟩ : syracuseStep 39573881 = 29680411) B29680411
theorem B3652001 : Blo 1623010 3652001 := bstep (se 2 (by rfl) ⟨1369500, by rfl⟩ : syracuseStep 3652001 = 2739001) B2739001
theorem B68492227 : Blo 1623010 68492227 := bstep (se 1 (by rfl) ⟨51369170, by rfl⟩ : syracuseStep 68492227 = 102738341) B102738341
theorem B2055223 : Blo 1623010 2055223 := bstep (se 1 (by rfl) ⟨1541417, by rfl⟩ : syracuseStep 2055223 = 3082835) B3082835
theorem B1825951 : Blo 1623010 1825951 := bstep (se 1 (by rfl) ⟨1369463, by rfl⟩ : syracuseStep 1825951 = 2738927) B2738927
theorem B6013723 : Blo 1623010 6013723 := bstep (se 1 (by rfl) ⟨4510292, by rfl⟩ : syracuseStep 6013723 = 9020585) B9020585
theorem B3654521 : Blo 1623010 3654521 := bstep (se 2 (by rfl) ⟨1370445, by rfl⟩ : syracuseStep 3654521 = 2740891) B2740891
theorem B24986723 : Blo 1623010 24986723 := bstep (se 1 (by rfl) ⟨18740042, by rfl⟩ : syracuseStep 24986723 = 37480085) B37480085
theorem B5481755 : Blo 1623010 5481755 := bstep (se 1 (by rfl) ⟨4111316, by rfl⟩ : syracuseStep 5481755 = 8222633) B8222633
theorem B2434559 : Blo 1623010 2434559 := bstep (se 1 (by rfl) ⟨1825919, by rfl⟩ : syracuseStep 2434559 = 3651839) B3651839
theorem B2434601 : Blo 1623010 2434601 := bstep (se 2 (by rfl) ⟨912975, by rfl⟩ : syracuseStep 2434601 = 1825951) B1825951
theorem B2434667 : Blo 1623010 2434667 := bstep (se 1 (by rfl) ⟨1826000, by rfl⟩ : syracuseStep 2434667 = 3652001) B3652001
theorem B1623935 : Blo 1623010 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B1624063 : Blo 1623010 1624063 := bstep (se 1 (by rfl) ⟨1218047, by rfl⟩ : syracuseStep 1624063 = 2436095) B2436095
theorem B5851387 : Blo 1623010 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B8219069 : Blo 1623010 8219069 := bstep (se 3 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 8219069 = 3082151) B3082151
theorem B2739055 : Blo 1623010 2739055 := bstep (se 1 (by rfl) ⟨2054291, by rfl⟩ : syracuseStep 2739055 = 4108583) B4108583
theorem B2436635 : Blo 1623010 2436635 := bstep (se 1 (by rfl) ⟨1827476, by rfl⟩ : syracuseStep 2436635 = 3654953) B3654953
theorem B50007941 : Blo 1623010 50007941 := bstep (se 4 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 50007941 = 9376489) B9376489
theorem B2740297 : Blo 1623010 2740297 := bstep (se 2 (by rfl) ⟨1027611, by rfl⟩ : syracuseStep 2740297 = 2055223) B2055223
theorem B12333221 : Blo 1623010 12333221 := bstep (se 4 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 12333221 = 2312479) B2312479
theorem B26382587 : Blo 1623010 26382587 := bstep (se 1 (by rfl) ⟨19786940, by rfl⟩ : syracuseStep 26382587 = 39573881) B39573881
theorem B39515161 : Blo 1623010 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B4110335 : Blo 1623010 4110335 := bstep (se 1 (by rfl) ⟨3082751, by rfl⟩ : syracuseStep 4110335 = 6165503) B6165503
theorem B91322969 : Blo 1623010 91322969 := bstep (se 2 (by rfl) ⟨34246113, by rfl⟩ : syracuseStep 91322969 = 68492227) B68492227
theorem B3652379 : Blo 1623010 3652379 := bstep (se 1 (by rfl) ⟨2739284, by rfl⟩ : syracuseStep 3652379 = 5478569) B5478569
theorem B19749703 : Blo 1623010 19749703 := bstep (se 1 (by rfl) ⟨14812277, by rfl⟩ : syracuseStep 19749703 = 29624555) B29624555
theorem B4111175 : Blo 1623010 4111175 := bstep (se 1 (by rfl) ⟨3083381, by rfl⟩ : syracuseStep 4111175 = 6166763) B6166763
theorem B5479919 : Blo 1623010 5479919 := bstep (se 1 (by rfl) ⟨4109939, by rfl⟩ : syracuseStep 5479919 = 8219879) B8219879
theorem B3653729 : Blo 1623010 3653729 := bstep (se 2 (by rfl) ⟨1370148, by rfl⟩ : syracuseStep 3653729 = 2740297) B2740297
theorem B3654503 : Blo 1623010 3654503 := bstep (se 1 (by rfl) ⟨2740877, by rfl⟩ : syracuseStep 3654503 = 5481755) B5481755
theorem B1623039 : Blo 1623010 1623039 := bstep (se 1 (by rfl) ⟨1217279, by rfl⟩ : syracuseStep 1623039 = 2434559) B2434559
theorem B1623067 : Blo 1623010 1623067 := bstep (se 1 (by rfl) ⟨1217300, by rfl⟩ : syracuseStep 1623067 = 2434601) B2434601
theorem B1623111 : Blo 1623010 1623111 := bstep (se 1 (by rfl) ⟨1217333, by rfl⟩ : syracuseStep 1623111 = 2434667) B2434667
theorem B2434919 : Blo 1623010 2434919 := bstep (se 1 (by rfl) ⟨1826189, by rfl⟩ : syracuseStep 2434919 = 3652379) B3652379
theorem B1624423 : Blo 1623010 1624423 := bstep (se 1 (by rfl) ⟨1218317, by rfl⟩ : syracuseStep 1624423 = 2436635) B2436635
theorem B281414261 : Blo 1623010 281414261 := bstep (se 5 (by rfl) ⟨13191293, by rfl⟩ : syracuseStep 281414261 = 26382587) B26382587
theorem B7801849 : Blo 1623010 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B2436347 : Blo 1623010 2436347 := bstep (se 1 (by rfl) ⟨1827260, by rfl⟩ : syracuseStep 2436347 = 3654521) B3654521
theorem B26332937 : Blo 1623010 26332937 := bstep (se 2 (by rfl) ⟨9874851, by rfl⟩ : syracuseStep 26332937 = 19749703) B19749703
theorem B2740223 : Blo 1623010 2740223 := bstep (se 1 (by rfl) ⟨2055167, by rfl⟩ : syracuseStep 2740223 = 4110335) B4110335
theorem B52686881 : Blo 1623010 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B243527917 : Blo 1623010 243527917 := bstep (se 3 (by rfl) ⟨45661484, by rfl⟩ : syracuseStep 243527917 = 91322969) B91322969
theorem B2740783 : Blo 1623010 2740783 := bstep (se 1 (by rfl) ⟨2055587, by rfl⟩ : syracuseStep 2740783 = 4111175) B4111175
theorem B33338627 : Blo 1623010 33338627 := bstep (se 1 (by rfl) ⟨25003970, by rfl⟩ : syracuseStep 33338627 = 50007941) B50007941
theorem B8222147 : Blo 1623010 8222147 := bstep (se 1 (by rfl) ⟨6166610, by rfl⟩ : syracuseStep 8222147 = 12333221) B12333221
theorem B66631261 : Blo 1623010 66631261 := bstep (se 3 (by rfl) ⟨12493361, by rfl⟩ : syracuseStep 66631261 = 24986723) B24986723
theorem B8018297 : Blo 1623010 8018297 := bstep (se 2 (by rfl) ⟨3006861, by rfl⟩ : syracuseStep 8018297 = 6013723) B6013723
theorem B3652073 : Blo 1623010 3652073 := bstep (se 2 (by rfl) ⟨1369527, by rfl⟩ : syracuseStep 3652073 = 2739055) B2739055
theorem B5479379 : Blo 1623010 5479379 := bstep (se 1 (by rfl) ⟨4109534, by rfl⟩ : syracuseStep 5479379 = 8219069) B8219069
theorem B3653279 : Blo 1623010 3653279 := bstep (se 1 (by rfl) ⟨2739959, by rfl⟩ : syracuseStep 3653279 = 5479919) B5479919
theorem B3654377 : Blo 1623010 3654377 := bstep (se 2 (by rfl) ⟨1370391, by rfl⟩ : syracuseStep 3654377 = 2740783) B2740783
theorem B22225751 : Blo 1623010 22225751 := bstep (se 1 (by rfl) ⟨16669313, by rfl⟩ : syracuseStep 22225751 = 33338627) B33338627
theorem B5481431 : Blo 1623010 5481431 := bstep (se 1 (by rfl) ⟨4111073, by rfl⟩ : syracuseStep 5481431 = 8222147) B8222147
theorem B1623279 : Blo 1623010 1623279 := bstep (se 1 (by rfl) ⟨1217459, by rfl⟩ : syracuseStep 1623279 = 2434919) B2434919
theorem B2434715 : Blo 1623010 2434715 := bstep (se 1 (by rfl) ⟨1826036, by rfl⟩ : syracuseStep 2434715 = 3652073) B3652073
theorem B1624231 : Blo 1623010 1624231 := bstep (se 1 (by rfl) ⟨1218173, by rfl⟩ : syracuseStep 1624231 = 2436347) B2436347
theorem B2435519 : Blo 1623010 2435519 := bstep (se 1 (by rfl) ⟨1826639, by rfl⟩ : syracuseStep 2435519 = 3653279) B3653279
theorem B41609861 : Blo 1623010 41609861 := bstep (se 4 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 41609861 = 7801849) B7801849
theorem B2435819 : Blo 1623010 2435819 := bstep (se 1 (by rfl) ⟨1826864, by rfl⟩ : syracuseStep 2435819 = 3653729) B3653729
theorem B2436335 : Blo 1623010 2436335 := bstep (se 1 (by rfl) ⟨1827251, by rfl⟩ : syracuseStep 2436335 = 3654503) B3654503
theorem B5345531 : Blo 1623010 5345531 := bstep (se 1 (by rfl) ⟨4009148, by rfl⟩ : syracuseStep 5345531 = 8018297) B8018297
theorem B187609507 : Blo 1623010 187609507 := bstep (se 1 (by rfl) ⟨140707130, by rfl⟩ : syracuseStep 187609507 = 281414261) B281414261
theorem B35124587 : Blo 1623010 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B324703889 : Blo 1623010 324703889 := bstep (se 2 (by rfl) ⟨121763958, by rfl⟩ : syracuseStep 324703889 = 243527917) B243527917
theorem B3652919 : Blo 1623010 3652919 := bstep (se 1 (by rfl) ⟨2739689, by rfl⟩ : syracuseStep 3652919 = 5479379) B5479379
theorem B88841681 : Blo 1623010 88841681 := bstep (se 2 (by rfl) ⟨33315630, by rfl⟩ : syracuseStep 88841681 = 66631261) B66631261
theorem B17555291 : Blo 1623010 17555291 := bstep (se 1 (by rfl) ⟨13166468, by rfl⟩ : syracuseStep 17555291 = 26332937) B26332937
theorem B1826815 : Blo 1623010 1826815 := bstep (se 1 (by rfl) ⟨1370111, by rfl⟩ : syracuseStep 1826815 = 2740223) B2740223
theorem B3563687 : Blo 1623010 3563687 := bstep (se 1 (by rfl) ⟨2672765, by rfl⟩ : syracuseStep 3563687 = 5345531) B5345531
theorem B3654287 : Blo 1623010 3654287 := bstep (se 1 (by rfl) ⟨2740715, by rfl⟩ : syracuseStep 3654287 = 5481431) B5481431
theorem B1623143 : Blo 1623010 1623143 := bstep (se 1 (by rfl) ⟨1217357, by rfl⟩ : syracuseStep 1623143 = 2434715) B2434715
theorem B1623679 : Blo 1623010 1623679 := bstep (se 1 (by rfl) ⟨1217759, by rfl⟩ : syracuseStep 1623679 = 2435519) B2435519
theorem B27739907 : Blo 1623010 27739907 := bstep (se 1 (by rfl) ⟨20804930, by rfl⟩ : syracuseStep 27739907 = 41609861) B41609861
theorem B1623879 : Blo 1623010 1623879 := bstep (se 1 (by rfl) ⟨1217909, by rfl⟩ : syracuseStep 1623879 = 2435819) B2435819
theorem B1624223 : Blo 1623010 1624223 := bstep (se 1 (by rfl) ⟨1218167, by rfl⟩ : syracuseStep 1624223 = 2436335) B2436335
theorem B2435279 : Blo 1623010 2435279 := bstep (se 1 (by rfl) ⟨1826459, by rfl⟩ : syracuseStep 2435279 = 3652919) B3652919
theorem B2435753 : Blo 1623010 2435753 := bstep (se 2 (by rfl) ⟨913407, by rfl⟩ : syracuseStep 2435753 = 1826815) B1826815
theorem B2436251 : Blo 1623010 2436251 := bstep (se 1 (by rfl) ⟨1827188, by rfl⟩ : syracuseStep 2436251 = 3654377) B3654377
theorem B23416391 : Blo 1623010 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B216469259 : Blo 1623010 216469259 := bstep (se 1 (by rfl) ⟨162351944, by rfl⟩ : syracuseStep 216469259 = 324703889) B324703889
theorem B1000584037 : Blo 1623010 1000584037 := bstep (se 4 (by rfl) ⟨93804753, by rfl⟩ : syracuseStep 1000584037 = 187609507) B187609507
theorem B11703527 : Blo 1623010 11703527 := bstep (se 1 (by rfl) ⟨8777645, by rfl⟩ : syracuseStep 11703527 = 17555291) B17555291
theorem B14817167 : Blo 1623010 14817167 := bstep (se 1 (by rfl) ⟨11112875, by rfl⟩ : syracuseStep 14817167 = 22225751) B22225751
theorem B59227787 : Blo 1623010 59227787 := bstep (se 1 (by rfl) ⟨44420840, by rfl⟩ : syracuseStep 59227787 = 88841681) B88841681
theorem B9503165 : Blo 1623010 9503165 := bstep (se 3 (by rfl) ⟨1781843, by rfl⟩ : syracuseStep 9503165 = 3563687) B3563687
theorem B1623519 : Blo 1623010 1623519 := bstep (se 1 (by rfl) ⟨1217639, by rfl⟩ : syracuseStep 1623519 = 2435279) B2435279
theorem B1623835 : Blo 1623010 1623835 := bstep (se 1 (by rfl) ⟨1217876, by rfl⟩ : syracuseStep 1623835 = 2435753) B2435753
theorem B1624167 : Blo 1623010 1624167 := bstep (se 1 (by rfl) ⟨1218125, by rfl⟩ : syracuseStep 1624167 = 2436251) B2436251
theorem B144312839 : Blo 1623010 144312839 := bstep (se 1 (by rfl) ⟨108234629, by rfl⟩ : syracuseStep 144312839 = 216469259) B216469259
theorem B2436191 : Blo 1623010 2436191 := bstep (se 1 (by rfl) ⟨1827143, by rfl⟩ : syracuseStep 2436191 = 3654287) B3654287
theorem B7802351 : Blo 1623010 7802351 := bstep (se 1 (by rfl) ⟨5851763, by rfl⟩ : syracuseStep 7802351 = 11703527) B11703527
theorem B1334112049 : Blo 1623010 1334112049 := bstep (se 2 (by rfl) ⟨500292018, by rfl⟩ : syracuseStep 1334112049 = 1000584037) B1000584037
theorem B18493271 : Blo 1623010 18493271 := bstep (se 1 (by rfl) ⟨13869953, by rfl⟩ : syracuseStep 18493271 = 27739907) B27739907
theorem B15610927 : Blo 1623010 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B9878111 : Blo 1623010 9878111 := bstep (se 1 (by rfl) ⟨7408583, by rfl⟩ : syracuseStep 9878111 = 14817167) B14817167
theorem B39485191 : Blo 1623010 39485191 := bstep (se 1 (by rfl) ⟨29613893, by rfl⟩ : syracuseStep 39485191 = 59227787) B59227787
theorem B96208559 : Blo 1623010 96208559 := bstep (se 1 (by rfl) ⟨72156419, by rfl⟩ : syracuseStep 96208559 = 144312839) B144312839
theorem B1624127 : Blo 1623010 1624127 := bstep (se 1 (by rfl) ⟨1218095, by rfl⟩ : syracuseStep 1624127 = 2436191) B2436191
theorem B6335443 : Blo 1623010 6335443 := bstep (se 1 (by rfl) ⟨4751582, by rfl⟩ : syracuseStep 6335443 = 9503165) B9503165
theorem B52646921 : Blo 1623010 52646921 := bstep (se 2 (by rfl) ⟨19742595, by rfl⟩ : syracuseStep 52646921 = 39485191) B39485191
theorem B1778816065 : Blo 1623010 1778816065 := bstep (se 2 (by rfl) ⟨667056024, by rfl⟩ : syracuseStep 1778816065 = 1334112049) B1334112049
theorem B20814569 : Blo 1623010 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B6585407 : Blo 1623010 6585407 := bstep (se 1 (by rfl) ⟨4939055, by rfl⟩ : syracuseStep 6585407 = 9878111) B9878111
theorem B5201567 : Blo 1623010 5201567 := bstep (se 1 (by rfl) ⟨3901175, by rfl⟩ : syracuseStep 5201567 = 7802351) B7802351
theorem B12328847 : Blo 1623010 12328847 := bstep (se 1 (by rfl) ⟨9246635, by rfl⟩ : syracuseStep 12328847 = 18493271) B18493271
theorem B8447257 : Blo 1623010 8447257 := bstep (se 2 (by rfl) ⟨3167721, by rfl⟩ : syracuseStep 8447257 = 6335443) B6335443
theorem B3467711 : Blo 1623010 3467711 := bstep (se 1 (by rfl) ⟨2600783, by rfl⟩ : syracuseStep 3467711 = 5201567) B5201567
theorem B8219231 : Blo 1623010 8219231 := bstep (se 1 (by rfl) ⟨6164423, by rfl⟩ : syracuseStep 8219231 = 12328847) B12328847
theorem B35097947 : Blo 1623010 35097947 := bstep (se 1 (by rfl) ⟨26323460, by rfl⟩ : syracuseStep 35097947 = 52646921) B52646921
theorem B64139039 : Blo 1623010 64139039 := bstep (se 1 (by rfl) ⟨48104279, by rfl⟩ : syracuseStep 64139039 = 96208559) B96208559
theorem B2371754753 : Blo 1623010 2371754753 := bstep (se 2 (by rfl) ⟨889408032, by rfl⟩ : syracuseStep 2371754753 = 1778816065) B1778816065
theorem B13876379 : Blo 1623010 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B4390271 : Blo 1623010 4390271 := bstep (se 1 (by rfl) ⟨3292703, by rfl⟩ : syracuseStep 4390271 = 6585407) B6585407
theorem B9250919 : Blo 1623010 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B23398631 : Blo 1623010 23398631 := bstep (se 1 (by rfl) ⟨17548973, by rfl⟩ : syracuseStep 23398631 = 35097947) B35097947
theorem B2926847 : Blo 1623010 2926847 := bstep (se 1 (by rfl) ⟨2195135, by rfl⟩ : syracuseStep 2926847 = 4390271) B4390271
theorem B42759359 : Blo 1623010 42759359 := bstep (se 1 (by rfl) ⟨32069519, by rfl⟩ : syracuseStep 42759359 = 64139039) B64139039
theorem B9247229 : Blo 1623010 9247229 := bstep (se 3 (by rfl) ⟨1733855, by rfl⟩ : syracuseStep 9247229 = 3467711) B3467711
theorem B11263009 : Blo 1623010 11263009 := bstep (se 2 (by rfl) ⟨4223628, by rfl⟩ : syracuseStep 11263009 = 8447257) B8447257
theorem B5479487 : Blo 1623010 5479487 := bstep (se 1 (by rfl) ⟨4109615, by rfl⟩ : syracuseStep 5479487 = 8219231) B8219231
theorem B1581169835 : Blo 1623010 1581169835 := bstep (se 1 (by rfl) ⟨1185877376, by rfl⟩ : syracuseStep 1581169835 = 2371754753) B2371754753
theorem B15017345 : Blo 1623010 15017345 := bstep (se 2 (by rfl) ⟨5631504, by rfl⟩ : syracuseStep 15017345 = 11263009) B11263009
theorem B15599087 : Blo 1623010 15599087 := bstep (se 1 (by rfl) ⟨11699315, by rfl⟩ : syracuseStep 15599087 = 23398631) B23398631
theorem B6164819 : Blo 1623010 6164819 := bstep (se 1 (by rfl) ⟨4623614, by rfl⟩ : syracuseStep 6164819 = 9247229) B9247229
theorem B4216452893 : Blo 1623010 4216452893 := bstep (se 3 (by rfl) ⟨790584917, by rfl⟩ : syracuseStep 4216452893 = 1581169835) B1581169835
theorem B7804925 : Blo 1623010 7804925 := bstep (se 3 (by rfl) ⟨1463423, by rfl⟩ : syracuseStep 7804925 = 2926847) B2926847
theorem B28506239 : Blo 1623010 28506239 := bstep (se 1 (by rfl) ⟨21379679, by rfl⟩ : syracuseStep 28506239 = 42759359) B42759359
theorem B6167279 : Blo 1623010 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B3652991 : Blo 1623010 3652991 := bstep (se 1 (by rfl) ⟨2739743, by rfl⟩ : syracuseStep 3652991 = 5479487) B5479487
theorem B10011563 : Blo 1623010 10011563 := bstep (se 1 (by rfl) ⟨7508672, by rfl⟩ : syracuseStep 10011563 = 15017345) B15017345
theorem B5203283 : Blo 1623010 5203283 := bstep (se 1 (by rfl) ⟨3902462, by rfl⟩ : syracuseStep 5203283 = 7804925) B7804925
theorem B2435327 : Blo 1623010 2435327 := bstep (se 1 (by rfl) ⟨1826495, by rfl⟩ : syracuseStep 2435327 = 3652991) B3652991
theorem B10399391 : Blo 1623010 10399391 := bstep (se 1 (by rfl) ⟨7799543, by rfl⟩ : syracuseStep 10399391 = 15599087) B15599087
theorem B4109879 : Blo 1623010 4109879 := bstep (se 1 (by rfl) ⟨3082409, by rfl⟩ : syracuseStep 4109879 = 6164819) B6164819
theorem B2810968595 : Blo 1623010 2810968595 := bstep (se 1 (by rfl) ⟨2108226446, by rfl⟩ : syracuseStep 2810968595 = 4216452893) B4216452893
theorem B19004159 : Blo 1623010 19004159 := bstep (se 1 (by rfl) ⟨14253119, by rfl⟩ : syracuseStep 19004159 = 28506239) B28506239
theorem B4111519 : Blo 1623010 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B1623551 : Blo 1623010 1623551 := bstep (se 1 (by rfl) ⟨1217663, by rfl⟩ : syracuseStep 1623551 = 2435327) B2435327
theorem B5482025 : Blo 1623010 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B1873979063 : Blo 1623010 1873979063 := bstep (se 1 (by rfl) ⟨1405484297, by rfl⟩ : syracuseStep 1873979063 = 2810968595) B2810968595
theorem B50677757 : Blo 1623010 50677757 := bstep (se 3 (by rfl) ⟨9502079, by rfl⟩ : syracuseStep 50677757 = 19004159) B19004159
theorem B6932927 : Blo 1623010 6932927 := bstep (se 1 (by rfl) ⟨5199695, by rfl⟩ : syracuseStep 6932927 = 10399391) B10399391
theorem B2739919 : Blo 1623010 2739919 := bstep (se 1 (by rfl) ⟨2054939, by rfl⟩ : syracuseStep 2739919 = 4109879) B4109879
theorem B6674375 : Blo 1623010 6674375 := bstep (se 1 (by rfl) ⟨5005781, by rfl⟩ : syracuseStep 6674375 = 10011563) B10011563
theorem B13875421 : Blo 1623010 13875421 := bstep (se 3 (by rfl) ⟨2601641, by rfl⟩ : syracuseStep 13875421 = 5203283) B5203283
theorem B3654683 : Blo 1623010 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B4449583 : Blo 1623010 4449583 := bstep (se 1 (by rfl) ⟨3337187, by rfl⟩ : syracuseStep 4449583 = 6674375) B6674375
theorem B33785171 : Blo 1623010 33785171 := bstep (se 1 (by rfl) ⟨25338878, by rfl⟩ : syracuseStep 33785171 = 50677757) B50677757
theorem B4621951 : Blo 1623010 4621951 := bstep (se 1 (by rfl) ⟨3466463, by rfl⟩ : syracuseStep 4621951 = 6932927) B6932927
theorem B18500561 : Blo 1623010 18500561 := bstep (se 2 (by rfl) ⟨6937710, by rfl⟩ : syracuseStep 18500561 = 13875421) B13875421
theorem B1249319375 : Blo 1623010 1249319375 := bstep (se 1 (by rfl) ⟨936989531, by rfl⟩ : syracuseStep 1249319375 = 1873979063) B1873979063
theorem B3653225 : Blo 1623010 3653225 := bstep (se 2 (by rfl) ⟨1369959, by rfl⟩ : syracuseStep 3653225 = 2739919) B2739919
theorem B5932777 : Blo 1623010 5932777 := bstep (se 2 (by rfl) ⟨2224791, by rfl⟩ : syracuseStep 5932777 = 4449583) B4449583
theorem B6162601 : Blo 1623010 6162601 := bstep (se 2 (by rfl) ⟨2310975, by rfl⟩ : syracuseStep 6162601 = 4621951) B4621951
theorem B2435483 : Blo 1623010 2435483 := bstep (se 1 (by rfl) ⟨1826612, by rfl⟩ : syracuseStep 2435483 = 3653225) B3653225
theorem B2436455 : Blo 1623010 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B22523447 : Blo 1623010 22523447 := bstep (se 1 (by rfl) ⟨16892585, by rfl⟩ : syracuseStep 22523447 = 33785171) B33785171
theorem B12333707 : Blo 1623010 12333707 := bstep (se 1 (by rfl) ⟨9250280, by rfl⟩ : syracuseStep 12333707 = 18500561) B18500561
theorem B832879583 : Blo 1623010 832879583 := bstep (se 1 (by rfl) ⟨624659687, by rfl⟩ : syracuseStep 832879583 = 1249319375) B1249319375
theorem B8216801 : Blo 1623010 8216801 := bstep (se 2 (by rfl) ⟨3081300, by rfl⟩ : syracuseStep 8216801 = 6162601) B6162601
theorem B1623655 : Blo 1623010 1623655 := bstep (se 1 (by rfl) ⟨1217741, by rfl⟩ : syracuseStep 1623655 = 2435483) B2435483
theorem B1624303 : Blo 1623010 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B7910369 : Blo 1623010 7910369 := bstep (se 2 (by rfl) ⟨2966388, by rfl⟩ : syracuseStep 7910369 = 5932777) B5932777
theorem B8222471 : Blo 1623010 8222471 := bstep (se 1 (by rfl) ⟨6166853, by rfl⟩ : syracuseStep 8222471 = 12333707) B12333707
theorem B555253055 : Blo 1623010 555253055 := bstep (se 1 (by rfl) ⟨416439791, by rfl⟩ : syracuseStep 555253055 = 832879583) B832879583
theorem B15015631 : Blo 1623010 15015631 := bstep (se 1 (by rfl) ⟨11261723, by rfl⟩ : syracuseStep 15015631 = 22523447) B22523447
theorem B5481647 : Blo 1623010 5481647 := bstep (se 1 (by rfl) ⟨4111235, by rfl⟩ : syracuseStep 5481647 = 8222471) B8222471
theorem B370168703 : Blo 1623010 370168703 := bstep (se 1 (by rfl) ⟨277626527, by rfl⟩ : syracuseStep 370168703 = 555253055) B555253055
theorem B5477867 : Blo 1623010 5477867 := bstep (se 1 (by rfl) ⟨4108400, by rfl⟩ : syracuseStep 5477867 = 8216801) B8216801
theorem B5273579 : Blo 1623010 5273579 := bstep (se 1 (by rfl) ⟨3955184, by rfl⟩ : syracuseStep 5273579 = 7910369) B7910369
theorem B20020841 : Blo 1623010 20020841 := bstep (se 2 (by rfl) ⟨7507815, by rfl⟩ : syracuseStep 20020841 = 15015631) B15015631
theorem B3654431 : Blo 1623010 3654431 := bstep (se 1 (by rfl) ⟨2740823, by rfl⟩ : syracuseStep 3654431 = 5481647) B5481647
theorem B3515719 : Blo 1623010 3515719 := bstep (se 1 (by rfl) ⟨2636789, by rfl⟩ : syracuseStep 3515719 = 5273579) B5273579
theorem B13347227 : Blo 1623010 13347227 := bstep (se 1 (by rfl) ⟨10010420, by rfl⟩ : syracuseStep 13347227 = 20020841) B20020841
theorem B246779135 : Blo 1623010 246779135 := bstep (se 1 (by rfl) ⟨185084351, by rfl⟩ : syracuseStep 246779135 = 370168703) B370168703
theorem B3651911 : Blo 1623010 3651911 := bstep (se 1 (by rfl) ⟨2738933, by rfl⟩ : syracuseStep 3651911 = 5477867) B5477867
theorem B2434607 : Blo 1623010 2434607 := bstep (se 1 (by rfl) ⟨1825955, by rfl⟩ : syracuseStep 2434607 = 3651911) B3651911
theorem B4687625 : Blo 1623010 4687625 := bstep (se 2 (by rfl) ⟨1757859, by rfl⟩ : syracuseStep 4687625 = 3515719) B3515719
theorem B2436287 : Blo 1623010 2436287 := bstep (se 1 (by rfl) ⟨1827215, by rfl⟩ : syracuseStep 2436287 = 3654431) B3654431
theorem B35592605 : Blo 1623010 35592605 := bstep (se 3 (by rfl) ⟨6673613, by rfl⟩ : syracuseStep 35592605 = 13347227) B13347227
theorem B164519423 : Blo 1623010 164519423 := bstep (se 1 (by rfl) ⟨123389567, by rfl⟩ : syracuseStep 164519423 = 246779135) B246779135
theorem B1623071 : Blo 1623010 1623071 := bstep (se 1 (by rfl) ⟨1217303, by rfl⟩ : syracuseStep 1623071 = 2434607) B2434607
theorem B1624191 : Blo 1623010 1624191 := bstep (se 1 (by rfl) ⟨1218143, by rfl⟩ : syracuseStep 1624191 = 2436287) B2436287
theorem B3125083 : Blo 1623010 3125083 := bstep (se 1 (by rfl) ⟨2343812, by rfl⟩ : syracuseStep 3125083 = 4687625) B4687625
theorem B23728403 : Blo 1623010 23728403 := bstep (se 1 (by rfl) ⟨17796302, by rfl⟩ : syracuseStep 23728403 = 35592605) B35592605
theorem B109679615 : Blo 1623010 109679615 := bstep (se 1 (by rfl) ⟨82259711, by rfl⟩ : syracuseStep 109679615 = 164519423) B164519423
theorem B63275741 : Blo 1623010 63275741 := bstep (se 3 (by rfl) ⟨11864201, by rfl⟩ : syracuseStep 63275741 = 23728403) B23728403
theorem B4166777 : Blo 1623010 4166777 := bstep (se 2 (by rfl) ⟨1562541, by rfl⟩ : syracuseStep 4166777 = 3125083) B3125083
theorem B73119743 : Blo 1623010 73119743 := bstep (se 1 (by rfl) ⟨54839807, by rfl⟩ : syracuseStep 73119743 = 109679615) B109679615
theorem B2777851 : Blo 1623010 2777851 := bstep (se 1 (by rfl) ⟨2083388, by rfl⟩ : syracuseStep 2777851 = 4166777) B4166777
theorem B42183827 : Blo 1623010 42183827 := bstep (se 1 (by rfl) ⟨31637870, by rfl⟩ : syracuseStep 42183827 = 63275741) B63275741
theorem B48746495 : Blo 1623010 48746495 := bstep (se 1 (by rfl) ⟨36559871, by rfl⟩ : syracuseStep 48746495 = 73119743) B73119743
theorem B3703801 : Blo 1623010 3703801 := bstep (se 2 (by rfl) ⟨1388925, by rfl⟩ : syracuseStep 3703801 = 2777851) B2777851
theorem B28122551 : Blo 1623010 28122551 := bstep (se 1 (by rfl) ⟨21091913, by rfl⟩ : syracuseStep 28122551 = 42183827) B42183827
theorem B129990653 : Blo 1623010 129990653 := bstep (se 3 (by rfl) ⟨24373247, by rfl⟩ : syracuseStep 129990653 = 48746495) B48746495
theorem B18748367 : Blo 1623010 18748367 := bstep (se 1 (by rfl) ⟨14061275, by rfl⟩ : syracuseStep 18748367 = 28122551) B28122551
theorem B86660435 : Blo 1623010 86660435 := bstep (se 1 (by rfl) ⟨64995326, by rfl⟩ : syracuseStep 86660435 = 129990653) B129990653
theorem B4938401 : Blo 1623010 4938401 := bstep (se 2 (by rfl) ⟨1851900, by rfl⟩ : syracuseStep 4938401 = 3703801) B3703801
theorem B57773623 : Blo 1623010 57773623 := bstep (se 1 (by rfl) ⟨43330217, by rfl⟩ : syracuseStep 57773623 = 86660435) B86660435
theorem B12498911 : Blo 1623010 12498911 := bstep (se 1 (by rfl) ⟨9374183, by rfl⟩ : syracuseStep 12498911 = 18748367) B18748367
theorem B3292267 : Blo 1623010 3292267 := bstep (se 1 (by rfl) ⟨2469200, by rfl⟩ : syracuseStep 3292267 = 4938401) B4938401
theorem B8332607 : Blo 1623010 8332607 := bstep (se 1 (by rfl) ⟨6249455, by rfl⟩ : syracuseStep 8332607 = 12498911) B12498911
theorem B77031497 : Blo 1623010 77031497 := bstep (se 2 (by rfl) ⟨28886811, by rfl⟩ : syracuseStep 77031497 = 57773623) B57773623
theorem B4389689 : Blo 1623010 4389689 := bstep (se 2 (by rfl) ⟨1646133, by rfl⟩ : syracuseStep 4389689 = 3292267) B3292267
theorem B5555071 : Blo 1623010 5555071 := bstep (se 1 (by rfl) ⟨4166303, by rfl⟩ : syracuseStep 5555071 = 8332607) B8332607
theorem B2926459 : Blo 1623010 2926459 := bstep (se 1 (by rfl) ⟨2194844, by rfl⟩ : syracuseStep 2926459 = 4389689) B4389689
theorem B51354331 : Blo 1623010 51354331 := bstep (se 1 (by rfl) ⟨38515748, by rfl⟩ : syracuseStep 51354331 = 77031497) B77031497
theorem B7406761 : Blo 1623010 7406761 := bstep (se 2 (by rfl) ⟨2777535, by rfl⟩ : syracuseStep 7406761 = 5555071) B5555071
theorem B3901945 : Blo 1623010 3901945 := bstep (se 2 (by rfl) ⟨1463229, by rfl⟩ : syracuseStep 3901945 = 2926459) B2926459
theorem B273889765 : Blo 1623010 273889765 := bstep (se 4 (by rfl) ⟨25677165, by rfl⟩ : syracuseStep 273889765 = 51354331) B51354331
theorem B5202593 : Blo 1623010 5202593 := bstep (se 2 (by rfl) ⟨1950972, by rfl⟩ : syracuseStep 5202593 = 3901945) B3901945
theorem B365186353 : Blo 1623010 365186353 := bstep (se 2 (by rfl) ⟨136944882, by rfl⟩ : syracuseStep 365186353 = 273889765) B273889765
theorem B9875681 : Blo 1623010 9875681 := bstep (se 2 (by rfl) ⟨3703380, by rfl⟩ : syracuseStep 9875681 = 7406761) B7406761
theorem B3468395 : Blo 1623010 3468395 := bstep (se 1 (by rfl) ⟨2601296, by rfl⟩ : syracuseStep 3468395 = 5202593) B5202593
theorem B6583787 : Blo 1623010 6583787 := bstep (se 1 (by rfl) ⟨4937840, by rfl⟩ : syracuseStep 6583787 = 9875681) B9875681
theorem B486915137 : Blo 1623010 486915137 := bstep (se 2 (by rfl) ⟨182593176, by rfl⟩ : syracuseStep 486915137 = 365186353) B365186353
theorem B324610091 : Blo 1623010 324610091 := bstep (se 1 (by rfl) ⟨243457568, by rfl⟩ : syracuseStep 324610091 = 486915137) B486915137
theorem B2312263 : Blo 1623010 2312263 := bstep (se 1 (by rfl) ⟨1734197, by rfl⟩ : syracuseStep 2312263 = 3468395) B3468395
theorem B4389191 : Blo 1623010 4389191 := bstep (se 1 (by rfl) ⟨3291893, by rfl⟩ : syracuseStep 4389191 = 6583787) B6583787
theorem B2926127 : Blo 1623010 2926127 := bstep (se 1 (by rfl) ⟨2194595, by rfl⟩ : syracuseStep 2926127 = 4389191) B4389191
theorem B3083017 : Blo 1623010 3083017 := bstep (se 2 (by rfl) ⟨1156131, by rfl⟩ : syracuseStep 3083017 = 2312263) B2312263
theorem B216406727 : Blo 1623010 216406727 := bstep (se 1 (by rfl) ⟨162305045, by rfl⟩ : syracuseStep 216406727 = 324610091) B324610091
theorem B1950751 : Blo 1623010 1950751 := bstep (se 1 (by rfl) ⟨1463063, by rfl⟩ : syracuseStep 1950751 = 2926127) B2926127
theorem B144271151 : Blo 1623010 144271151 := bstep (se 1 (by rfl) ⟨108203363, by rfl⟩ : syracuseStep 144271151 = 216406727) B216406727
theorem B4110689 : Blo 1623010 4110689 := bstep (se 2 (by rfl) ⟨1541508, by rfl⟩ : syracuseStep 4110689 = 3083017) B3083017
theorem B2601001 : Blo 1623010 2601001 := bstep (se 2 (by rfl) ⟨975375, by rfl⟩ : syracuseStep 2601001 = 1950751) B1950751
theorem B2740459 : Blo 1623010 2740459 := bstep (se 1 (by rfl) ⟨2055344, by rfl⟩ : syracuseStep 2740459 = 4110689) B4110689
theorem B96180767 : Blo 1623010 96180767 := bstep (se 1 (by rfl) ⟨72135575, by rfl⟩ : syracuseStep 96180767 = 144271151) B144271151
theorem B3653945 : Blo 1623010 3653945 := bstep (se 2 (by rfl) ⟨1370229, by rfl⟩ : syracuseStep 3653945 = 2740459) B2740459
theorem B64120511 : Blo 1623010 64120511 := bstep (se 1 (by rfl) ⟨48090383, by rfl⟩ : syracuseStep 64120511 = 96180767) B96180767
theorem B13872005 : Blo 1623010 13872005 := bstep (se 4 (by rfl) ⟨1300500, by rfl⟩ : syracuseStep 13872005 = 2601001) B2601001
theorem B42747007 : Blo 1623010 42747007 := bstep (se 1 (by rfl) ⟨32060255, by rfl⟩ : syracuseStep 42747007 = 64120511) B64120511
theorem B2435963 : Blo 1623010 2435963 := bstep (se 1 (by rfl) ⟨1826972, by rfl⟩ : syracuseStep 2435963 = 3653945) B3653945
theorem B9248003 : Blo 1623010 9248003 := bstep (se 1 (by rfl) ⟨6936002, by rfl⟩ : syracuseStep 9248003 = 13872005) B13872005
theorem B1623975 : Blo 1623010 1623975 := bstep (se 1 (by rfl) ⟨1217981, by rfl⟩ : syracuseStep 1623975 = 2435963) B2435963
theorem B56996009 : Blo 1623010 56996009 := bstep (se 2 (by rfl) ⟨21373503, by rfl⟩ : syracuseStep 56996009 = 42747007) B42747007
theorem B6165335 : Blo 1623010 6165335 := bstep (se 1 (by rfl) ⟨4624001, by rfl⟩ : syracuseStep 6165335 = 9248003) B9248003
theorem B607957429 : Blo 1623010 607957429 := bstep (se 5 (by rfl) ⟨28498004, by rfl⟩ : syracuseStep 607957429 = 56996009) B56996009
theorem B4110223 : Blo 1623010 4110223 := bstep (se 1 (by rfl) ⟨3082667, by rfl⟩ : syracuseStep 4110223 = 6165335) B6165335
theorem B810609905 : Blo 1623010 810609905 := bstep (se 2 (by rfl) ⟨303978714, by rfl⟩ : syracuseStep 810609905 = 607957429) B607957429
theorem B5480297 : Blo 1623010 5480297 := bstep (se 2 (by rfl) ⟨2055111, by rfl⟩ : syracuseStep 5480297 = 4110223) B4110223
theorem B540406603 : Blo 1623010 540406603 := bstep (se 1 (by rfl) ⟨405304952, by rfl⟩ : syracuseStep 540406603 = 810609905) B810609905
theorem B3653531 : Blo 1623010 3653531 := bstep (se 1 (by rfl) ⟨2740148, by rfl⟩ : syracuseStep 3653531 = 5480297) B5480297
theorem B2435687 : Blo 1623010 2435687 := bstep (se 1 (by rfl) ⟨1826765, by rfl⟩ : syracuseStep 2435687 = 3653531) B3653531
theorem B720542137 : Blo 1623010 720542137 := bstep (se 2 (by rfl) ⟨270203301, by rfl⟩ : syracuseStep 720542137 = 540406603) B540406603
theorem B1623791 : Blo 1623010 1623791 := bstep (se 1 (by rfl) ⟨1217843, by rfl⟩ : syracuseStep 1623791 = 2435687) B2435687
theorem B960722849 : Blo 1623010 960722849 := bstep (se 2 (by rfl) ⟨360271068, by rfl⟩ : syracuseStep 960722849 = 720542137) B720542137
theorem B640481899 : Blo 1623010 640481899 := bstep (se 1 (by rfl) ⟨480361424, by rfl⟩ : syracuseStep 640481899 = 960722849) B960722849
theorem B853975865 : Blo 1623010 853975865 := bstep (se 2 (by rfl) ⟨320240949, by rfl⟩ : syracuseStep 853975865 = 640481899) B640481899
theorem B569317243 : Blo 1623010 569317243 := bstep (se 1 (by rfl) ⟨426987932, by rfl⟩ : syracuseStep 569317243 = 853975865) B853975865
theorem B759089657 : Blo 1623010 759089657 := bstep (se 2 (by rfl) ⟨284658621, by rfl⟩ : syracuseStep 759089657 = 569317243) B569317243
theorem B506059771 : Blo 1623010 506059771 := bstep (se 1 (by rfl) ⟨379544828, by rfl⟩ : syracuseStep 506059771 = 759089657) B759089657
theorem B674746361 : Blo 1623010 674746361 := bstep (se 2 (by rfl) ⟨253029885, by rfl⟩ : syracuseStep 674746361 = 506059771) B506059771
theorem B449830907 : Blo 1623010 449830907 := bstep (se 1 (by rfl) ⟨337373180, by rfl⟩ : syracuseStep 449830907 = 674746361) B674746361
theorem B299887271 : Blo 1623010 299887271 := bstep (se 1 (by rfl) ⟨224915453, by rfl⟩ : syracuseStep 299887271 = 449830907) B449830907
theorem B199924847 : Blo 1623010 199924847 := bstep (se 1 (by rfl) ⟨149943635, by rfl⟩ : syracuseStep 199924847 = 299887271) B299887271
theorem B133283231 : Blo 1623010 133283231 := bstep (se 1 (by rfl) ⟨99962423, by rfl⟩ : syracuseStep 133283231 = 199924847) B199924847
theorem B88855487 : Blo 1623010 88855487 := bstep (se 1 (by rfl) ⟨66641615, by rfl⟩ : syracuseStep 88855487 = 133283231) B133283231
theorem B59236991 : Blo 1623010 59236991 := bstep (se 1 (by rfl) ⟨44427743, by rfl⟩ : syracuseStep 59236991 = 88855487) B88855487
theorem B39491327 : Blo 1623010 39491327 := bstep (se 1 (by rfl) ⟨29618495, by rfl⟩ : syracuseStep 39491327 = 59236991) B59236991
theorem B26327551 : Blo 1623010 26327551 := bstep (se 1 (by rfl) ⟨19745663, by rfl⟩ : syracuseStep 26327551 = 39491327) B39491327
theorem B35103401 : Blo 1623010 35103401 := bstep (se 2 (by rfl) ⟨13163775, by rfl⟩ : syracuseStep 35103401 = 26327551) B26327551
theorem B23402267 : Blo 1623010 23402267 := bstep (se 1 (by rfl) ⟨17551700, by rfl⟩ : syracuseStep 23402267 = 35103401) B35103401
theorem B15601511 : Blo 1623010 15601511 := bstep (se 1 (by rfl) ⟨11701133, by rfl⟩ : syracuseStep 15601511 = 23402267) B23402267
theorem B10401007 : Blo 1623010 10401007 := bstep (se 1 (by rfl) ⟨7800755, by rfl⟩ : syracuseStep 10401007 = 15601511) B15601511
theorem B13868009 : Blo 1623010 13868009 := bstep (se 2 (by rfl) ⟨5200503, by rfl⟩ : syracuseStep 13868009 = 10401007) B10401007
theorem B9245339 : Blo 1623010 9245339 := bstep (se 1 (by rfl) ⟨6934004, by rfl⟩ : syracuseStep 9245339 = 13868009) B13868009
theorem B6163559 : Blo 1623010 6163559 := bstep (se 1 (by rfl) ⟨4622669, by rfl⟩ : syracuseStep 6163559 = 9245339) B9245339
theorem B4109039 : Blo 1623010 4109039 := bstep (se 1 (by rfl) ⟨3081779, by rfl⟩ : syracuseStep 4109039 = 6163559) B6163559
theorem B2739359 : Blo 1623010 2739359 := bstep (se 1 (by rfl) ⟨2054519, by rfl⟩ : syracuseStep 2739359 = 4109039) B4109039
theorem B1826239 : Blo 1623010 1826239 := bstep (se 1 (by rfl) ⟨1369679, by rfl⟩ : syracuseStep 1826239 = 2739359) B2739359
theorem B2434985 : Blo 1623010 2434985 := bstep (se 2 (by rfl) ⟨913119, by rfl⟩ : syracuseStep 2434985 = 1826239) B1826239
theorem B1623323 : Blo 1623010 1623323 := bstep (se 1 (by rfl) ⟨1217492, by rfl⟩ : syracuseStep 1623323 = 2434985) B2434985

theorem C0 (j : ℕ) (h1 : 405752 ≤ j) (h2 : j ≤ 406126) : Blo 1623010 (4 * j + 3) := by
  interval_cases j
  · exact B1623011
  · exact B1623015
  · exact B1623019
  · exact B1623023
  · exact B1623027
  · exact B1623031
  · exact B1623035
  · exact B1623039
  · exact B1623043
  · exact B1623047
  · exact B1623051
  · exact B1623055
  · exact B1623059
  · exact B1623063
  · exact B1623067
  · exact B1623071
  · exact B1623075
  · exact B1623079
  · exact B1623083
  · exact B1623087
  · exact B1623091
  · exact B1623095
  · exact B1623099
  · exact B1623103
  · exact B1623107
  · exact B1623111
  · exact B1623115
  · exact B1623119
  · exact B1623123
  · exact B1623127
  · exact B1623131
  · exact B1623135
  · exact B1623139
  · exact B1623143
  · exact B1623147
  · exact B1623151
  · exact B1623155
  · exact B1623159
  · exact B1623163
  · exact B1623167
  · exact B1623171
  · exact B1623175
  · exact B1623179
  · exact B1623183
  · exact B1623187
  · exact B1623191
  · exact B1623195
  · exact B1623199
  · exact B1623203
  · exact B1623207
  · exact B1623211
  · exact B1623215
  · exact B1623219
  · exact B1623223
  · exact B1623227
  · exact B1623231
  · exact B1623235
  · exact B1623239
  · exact B1623243
  · exact B1623247
  · exact B1623251
  · exact B1623255
  · exact B1623259
  · exact B1623263
  · exact B1623267
  · exact B1623271
  · exact B1623275
  · exact B1623279
  · exact B1623283
  · exact B1623287
  · exact B1623291
  · exact B1623295
  · exact B1623299
  · exact B1623303
  · exact B1623307
  · exact B1623311
  · exact B1623315
  · exact B1623319
  · exact B1623323
  · exact B1623327
  · exact B1623331
  · exact B1623335
  · exact B1623339
  · exact B1623343
  · exact B1623347
  · exact B1623351
  · exact B1623355
  · exact B1623359
  · exact B1623363
  · exact B1623367
  · exact B1623371
  · exact B1623375
  · exact B1623379
  · exact B1623383
  · exact B1623387
  · exact B1623391
  · exact B1623395
  · exact B1623399
  · exact B1623403
  · exact B1623407
  · exact B1623411
  · exact B1623415
  · exact B1623419
  · exact B1623423
  · exact B1623427
  · exact B1623431
  · exact B1623435
  · exact B1623439
  · exact B1623443
  · exact B1623447
  · exact B1623451
  · exact B1623455
  · exact B1623459
  · exact B1623463
  · exact B1623467
  · exact B1623471
  · exact B1623475
  · exact B1623479
  · exact B1623483
  · exact B1623487
  · exact B1623491
  · exact B1623495
  · exact B1623499
  · exact B1623503
  · exact B1623507
  · exact B1623511
  · exact B1623515
  · exact B1623519
  · exact B1623523
  · exact B1623527
  · exact B1623531
  · exact B1623535
  · exact B1623539
  · exact B1623543
  · exact B1623547
  · exact B1623551
  · exact B1623555
  · exact B1623559
  · exact B1623563
  · exact B1623567
  · exact B1623571
  · exact B1623575
  · exact B1623579
  · exact B1623583
  · exact B1623587
  · exact B1623591
  · exact B1623595
  · exact B1623599
  · exact B1623603
  · exact B1623607
  · exact B1623611
  · exact B1623615
  · exact B1623619
  · exact B1623623
  · exact B1623627
  · exact B1623631
  · exact B1623635
  · exact B1623639
  · exact B1623643
  · exact B1623647
  · exact B1623651
  · exact B1623655
  · exact B1623659
  · exact B1623663
  · exact B1623667
  · exact B1623671
  · exact B1623675
  · exact B1623679
  · exact B1623683
  · exact B1623687
  · exact B1623691
  · exact B1623695
  · exact B1623699
  · exact B1623703
  · exact B1623707
  · exact B1623711
  · exact B1623715
  · exact B1623719
  · exact B1623723
  · exact B1623727
  · exact B1623731
  · exact B1623735
  · exact B1623739
  · exact B1623743
  · exact B1623747
  · exact B1623751
  · exact B1623755
  · exact B1623759
  · exact B1623763
  · exact B1623767
  · exact B1623771
  · exact B1623775
  · exact B1623779
  · exact B1623783
  · exact B1623787
  · exact B1623791
  · exact B1623795
  · exact B1623799
  · exact B1623803
  · exact B1623807
  · exact B1623811
  · exact B1623815
  · exact B1623819
  · exact B1623823
  · exact B1623827
  · exact B1623831
  · exact B1623835
  · exact B1623839
  · exact B1623843
  · exact B1623847
  · exact B1623851
  · exact B1623855
  · exact B1623859
  · exact B1623863
  · exact B1623867
  · exact B1623871
  · exact B1623875
  · exact B1623879
  · exact B1623883
  · exact B1623887
  · exact B1623891
  · exact B1623895
  · exact B1623899
  · exact B1623903
  · exact B1623907
  · exact B1623911
  · exact B1623915
  · exact B1623919
  · exact B1623923
  · exact B1623927
  · exact B1623931
  · exact B1623935
  · exact B1623939
  · exact B1623943
  · exact B1623947
  · exact B1623951
  · exact B1623955
  · exact B1623959
  · exact B1623963
  · exact B1623967
  · exact B1623971
  · exact B1623975
  · exact B1623979
  · exact B1623983
  · exact B1623987
  · exact B1623991
  · exact B1623995
  · exact B1623999
  · exact B1624003
  · exact B1624007
  · exact B1624011
  · exact B1624015
  · exact B1624019
  · exact B1624023
  · exact B1624027
  · exact B1624031
  · exact B1624035
  · exact B1624039
  · exact B1624043
  · exact B1624047
  · exact B1624051
  · exact B1624055
  · exact B1624059
  · exact B1624063
  · exact B1624067
  · exact B1624071
  · exact B1624075
  · exact B1624079
  · exact B1624083
  · exact B1624087
  · exact B1624091
  · exact B1624095
  · exact B1624099
  · exact B1624103
  · exact B1624107
  · exact B1624111
  · exact B1624115
  · exact B1624119
  · exact B1624123
  · exact B1624127
  · exact B1624131
  · exact B1624135
  · exact B1624139
  · exact B1624143
  · exact B1624147
  · exact B1624151
  · exact B1624155
  · exact B1624159
  · exact B1624163
  · exact B1624167
  · exact B1624171
  · exact B1624175
  · exact B1624179
  · exact B1624183
  · exact B1624187
  · exact B1624191
  · exact B1624195
  · exact B1624199
  · exact B1624203
  · exact B1624207
  · exact B1624211
  · exact B1624215
  · exact B1624219
  · exact B1624223
  · exact B1624227
  · exact B1624231
  · exact B1624235
  · exact B1624239
  · exact B1624243
  · exact B1624247
  · exact B1624251
  · exact B1624255
  · exact B1624259
  · exact B1624263
  · exact B1624267
  · exact B1624271
  · exact B1624275
  · exact B1624279
  · exact B1624283
  · exact B1624287
  · exact B1624291
  · exact B1624295
  · exact B1624299
  · exact B1624303
  · exact B1624307
  · exact B1624311
  · exact B1624315
  · exact B1624319
  · exact B1624323
  · exact B1624327
  · exact B1624331
  · exact B1624335
  · exact B1624339
  · exact B1624343
  · exact B1624347
  · exact B1624351
  · exact B1624355
  · exact B1624359
  · exact B1624363
  · exact B1624367
  · exact B1624371
  · exact B1624375
  · exact B1624379
  · exact B1624383
  · exact B1624387
  · exact B1624391
  · exact B1624395
  · exact B1624399
  · exact B1624403
  · exact B1624407
  · exact B1624411
  · exact B1624415
  · exact B1624419
  · exact B1624423
  · exact B1624427
  · exact B1624431
  · exact B1624435
  · exact B1624439
  · exact B1624443
  · exact B1624447
  · exact B1624451
  · exact B1624455
  · exact B1624459
  · exact B1624463
  · exact B1624467
  · exact B1624471
  · exact B1624475
  · exact B1624479
  · exact B1624483
  · exact B1624487
  · exact B1624491
  · exact B1624495
  · exact B1624499
  · exact B1624503
  · exact B1624507

theorem solution (m : ℕ) (hlo : 1623010 ≤ m) (hhi : m ≤ 1624510) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 405752 ≤ j := by omega
    have hj2 : j ≤ 406126 := by omega
    have hb : Blo 1623010 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
