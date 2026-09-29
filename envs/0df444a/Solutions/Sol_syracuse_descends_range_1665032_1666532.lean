-- Prove2me | solution 1 for syracuse_descends_range_1665032_1666532
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:19:49.864818+00:00
-- url     : https://prove2.me/submissions/cd44858c-5961-4561-839c-56f29fbdbc96

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


theorem B2498573 : Blo 1665032 2498573 := bbase (se 3 (by rfl) ⟨468482, by rfl⟩ : syracuseStep 2498573 = 936965) (by norm_num)
theorem B2498597 : Blo 1665032 2498597 := bbase (se 4 (by rfl) ⟨234243, by rfl⟩ : syracuseStep 2498597 = 468487) (by norm_num)
theorem B2498621 : Blo 1665032 2498621 := bbase (se 3 (by rfl) ⟨468491, by rfl⟩ : syracuseStep 2498621 = 936983) (by norm_num)
theorem B2498645 : Blo 1665032 2498645 := bbase (se 8 (by rfl) ⟨14640, by rfl⟩ : syracuseStep 2498645 = 29281) (by norm_num)
theorem B8429669 : Blo 1665032 8429669 := bbase (se 4 (by rfl) ⟨790281, by rfl⟩ : syracuseStep 8429669 = 1580563) (by norm_num)
theorem B2809957 : Blo 1665032 2809957 := bbase (se 4 (by rfl) ⟨263433, by rfl⟩ : syracuseStep 2809957 = 526867) (by norm_num)
theorem B2498669 : Blo 1665032 2498669 := bbase (se 3 (by rfl) ⟨468500, by rfl⟩ : syracuseStep 2498669 = 937001) (by norm_num)
theorem B2498693 : Blo 1665032 2498693 := bbase (se 4 (by rfl) ⟨234252, by rfl⟩ : syracuseStep 2498693 = 468505) (by norm_num)
theorem B2498717 : Blo 1665032 2498717 := bbase (se 3 (by rfl) ⟨468509, by rfl⟩ : syracuseStep 2498717 = 937019) (by norm_num)
theorem B2498741 : Blo 1665032 2498741 := bbase (se 5 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 2498741 = 234257) (by norm_num)
theorem B2810045 : Blo 1665032 2810045 := bbase (se 3 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 2810045 = 1053767) (by norm_num)
theorem B2498765 : Blo 1665032 2498765 := bbase (se 3 (by rfl) ⟨468518, by rfl⟩ : syracuseStep 2498765 = 937037) (by norm_num)
theorem B5619941 : Blo 1665032 5619941 := bbase (se 4 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 5619941 = 1053739) (by norm_num)
theorem B3162341 : Blo 1665032 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B2498789 : Blo 1665032 2498789 := bbase (se 4 (by rfl) ⟨234261, by rfl⟩ : syracuseStep 2498789 = 468523) (by norm_num)
theorem B2498813 : Blo 1665032 2498813 := bbase (se 3 (by rfl) ⟨468527, by rfl⟩ : syracuseStep 2498813 = 937055) (by norm_num)
theorem B4055309 : Blo 1665032 4055309 := bbase (se 3 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 4055309 = 1520741) (by norm_num)
theorem B2498837 : Blo 1665032 2498837 := bbase (se 6 (by rfl) ⟨58566, by rfl⟩ : syracuseStep 2498837 = 117133) (by norm_num)
theorem B2498861 : Blo 1665032 2498861 := bbase (se 3 (by rfl) ⟨468536, by rfl⟩ : syracuseStep 2498861 = 937073) (by norm_num)
theorem B2810173 : Blo 1665032 2810173 := bbase (se 3 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 2810173 = 1053815) (by norm_num)
theorem B2498885 : Blo 1665032 2498885 := bbase (se 4 (by rfl) ⟨234270, by rfl⟩ : syracuseStep 2498885 = 468541) (by norm_num)
theorem B2703709 : Blo 1665032 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B2498909 : Blo 1665032 2498909 := bbase (se 3 (by rfl) ⟨468545, by rfl⟩ : syracuseStep 2498909 = 937091) (by norm_num)
theorem B4809061 : Blo 1665032 4809061 := bbase (se 4 (by rfl) ⟨450849, by rfl⟩ : syracuseStep 4809061 = 901699) (by norm_num)
theorem B2498933 : Blo 1665032 2498933 := bbase (se 5 (by rfl) ⟨117137, by rfl⟩ : syracuseStep 2498933 = 234275) (by norm_num)
theorem B3162493 : Blo 1665032 3162493 := bbase (se 3 (by rfl) ⟨592967, by rfl⟩ : syracuseStep 3162493 = 1185935) (by norm_num)
theorem B2498957 : Blo 1665032 2498957 := bbase (se 3 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 2498957 = 937109) (by norm_num)
theorem B2810261 : Blo 1665032 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B2498981 : Blo 1665032 2498981 := bbase (se 4 (by rfl) ⟨234279, by rfl⟩ : syracuseStep 2498981 = 468559) (by norm_num)
theorem B1687997 : Blo 1665032 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B2499005 : Blo 1665032 2499005 := bbase (se 3 (by rfl) ⟨468563, by rfl⟩ : syracuseStep 2499005 = 937127) (by norm_num)
theorem B2499029 : Blo 1665032 2499029 := bbase (se 7 (by rfl) ⟨29285, by rfl⟩ : syracuseStep 2499029 = 58571) (by norm_num)
theorem B2499053 : Blo 1665032 2499053 := bbase (se 3 (by rfl) ⟨468572, by rfl⟩ : syracuseStep 2499053 = 937145) (by norm_num)
theorem B2499077 : Blo 1665032 2499077 := bbase (se 4 (by rfl) ⟨234288, by rfl⟩ : syracuseStep 2499077 = 468577) (by norm_num)
theorem B2810389 : Blo 1665032 2810389 := bbase (se 6 (by rfl) ⟨65868, by rfl⟩ : syracuseStep 2810389 = 131737) (by norm_num)
theorem B2499101 : Blo 1665032 2499101 := bbase (se 3 (by rfl) ⟨468581, by rfl⟩ : syracuseStep 2499101 = 937163) (by norm_num)
theorem B2499125 : Blo 1665032 2499125 := bbase (se 5 (by rfl) ⟨117146, by rfl⟩ : syracuseStep 2499125 = 234293) (by norm_num)
theorem B2499149 : Blo 1665032 2499149 := bbase (se 3 (by rfl) ⟨468590, by rfl⟩ : syracuseStep 2499149 = 937181) (by norm_num)
theorem B2499173 : Blo 1665032 2499173 := bbase (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) (by norm_num)
theorem B2810477 : Blo 1665032 2810477 := bbase (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) (by norm_num)
theorem B2499197 : Blo 1665032 2499197 := bbase (se 3 (by rfl) ⟨468599, by rfl⟩ : syracuseStep 2499197 = 937199) (by norm_num)
theorem B5620373 : Blo 1665032 5620373 := bbase (se 6 (by rfl) ⟨131727, by rfl⟩ : syracuseStep 5620373 = 263455) (by norm_num)
theorem B2499221 : Blo 1665032 2499221 := bbase (se 6 (by rfl) ⟨58575, by rfl⟩ : syracuseStep 2499221 = 117151) (by norm_num)
theorem B4809365 : Blo 1665032 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B3162797 : Blo 1665032 3162797 := bbase (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) (by norm_num)
theorem B2499245 : Blo 1665032 2499245 := bbase (se 3 (by rfl) ⟨468608, by rfl⟩ : syracuseStep 2499245 = 937217) (by norm_num)
theorem B1802945 : Blo 1665032 1802945 := bbase (se 2 (by rfl) ⟨676104, by rfl⟩ : syracuseStep 1802945 = 1352209) (by norm_num)
theorem B2499269 : Blo 1665032 2499269 := bbase (se 4 (by rfl) ⟨234306, by rfl⟩ : syracuseStep 2499269 = 468613) (by norm_num)
theorem B2499293 : Blo 1665032 2499293 := bbase (se 3 (by rfl) ⟨468617, by rfl⟩ : syracuseStep 2499293 = 937235) (by norm_num)
theorem B2810605 : Blo 1665032 2810605 := bbase (se 3 (by rfl) ⟨526988, by rfl⟩ : syracuseStep 2810605 = 1053977) (by norm_num)
theorem B2499317 : Blo 1665032 2499317 := bbase (se 5 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 2499317 = 234311) (by norm_num)
theorem B1778441 : Blo 1665032 1778441 := bbase (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) (by norm_num)
theorem B2499341 : Blo 1665032 2499341 := bbase (se 3 (by rfl) ⟨468626, by rfl⟩ : syracuseStep 2499341 = 937253) (by norm_num)
theorem B9003797 : Blo 1665032 9003797 := bbase (se 6 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 9003797 = 422053) (by norm_num)
theorem B2499365 : Blo 1665032 2499365 := bbase (se 4 (by rfl) ⟨234315, by rfl⟩ : syracuseStep 2499365 = 468631) (by norm_num)
theorem B2499389 : Blo 1665032 2499389 := bbase (se 3 (by rfl) ⟨468635, by rfl⟩ : syracuseStep 2499389 = 937271) (by norm_num)
theorem B3556165 : Blo 1665032 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B2810693 : Blo 1665032 2810693 := bbase (se 4 (by rfl) ⟨263502, by rfl⟩ : syracuseStep 2810693 = 527005) (by norm_num)
theorem B2499413 : Blo 1665032 2499413 := bbase (se 9 (by rfl) ⟨7322, by rfl⟩ : syracuseStep 2499413 = 14645) (by norm_num)
theorem B2499437 : Blo 1665032 2499437 := bbase (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) (by norm_num)
theorem B2499461 : Blo 1665032 2499461 := bbase (se 4 (by rfl) ⟨234324, by rfl⟩ : syracuseStep 2499461 = 468649) (by norm_num)
theorem B2499485 : Blo 1665032 2499485 := bbase (se 3 (by rfl) ⟨468653, by rfl⟩ : syracuseStep 2499485 = 937307) (by norm_num)
theorem B2499509 : Blo 1665032 2499509 := bbase (se 5 (by rfl) ⟨117164, by rfl⟩ : syracuseStep 2499509 = 234329) (by norm_num)
theorem B2810821 : Blo 1665032 2810821 := bbase (se 4 (by rfl) ⟨263514, by rfl⟩ : syracuseStep 2810821 = 527029) (by norm_num)
theorem B2499533 : Blo 1665032 2499533 := bbase (se 3 (by rfl) ⟨468662, by rfl⟩ : syracuseStep 2499533 = 937325) (by norm_num)
theorem B2499557 : Blo 1665032 2499557 := bbase (se 4 (by rfl) ⟨234333, by rfl⟩ : syracuseStep 2499557 = 468667) (by norm_num)
theorem B2499581 : Blo 1665032 2499581 := bbase (se 3 (by rfl) ⟨468671, by rfl⟩ : syracuseStep 2499581 = 937343) (by norm_num)
theorem B1778689 : Blo 1665032 1778689 := bbase (se 2 (by rfl) ⟨667008, by rfl⟩ : syracuseStep 1778689 = 1334017) (by norm_num)
theorem B2499605 : Blo 1665032 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B2810909 : Blo 1665032 2810909 := bbase (se 3 (by rfl) ⟨527045, by rfl⟩ : syracuseStep 2810909 = 1054091) (by norm_num)
theorem B2499629 : Blo 1665032 2499629 := bbase (se 3 (by rfl) ⟨468680, by rfl⟩ : syracuseStep 2499629 = 937361) (by norm_num)
theorem B5620805 : Blo 1665032 5620805 := bbase (se 4 (by rfl) ⟨526950, by rfl⟩ : syracuseStep 5620805 = 1053901) (by norm_num)
theorem B2499653 : Blo 1665032 2499653 := bbase (se 4 (by rfl) ⟨234342, by rfl⟩ : syracuseStep 2499653 = 468685) (by norm_num)
theorem B2499677 : Blo 1665032 2499677 := bbase (se 3 (by rfl) ⟨468689, by rfl⟩ : syracuseStep 2499677 = 937379) (by norm_num)
theorem B2499701 : Blo 1665032 2499701 := bbase (se 5 (by rfl) ⟨117173, by rfl⟩ : syracuseStep 2499701 = 234347) (by norm_num)
theorem B2499725 : Blo 1665032 2499725 := bbase (se 3 (by rfl) ⟨468698, by rfl⟩ : syracuseStep 2499725 = 937397) (by norm_num)
theorem B6325397 : Blo 1665032 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B2811037 : Blo 1665032 2811037 := bbase (se 3 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 2811037 = 1054139) (by norm_num)
theorem B2499749 : Blo 1665032 2499749 := bbase (se 4 (by rfl) ⟨234351, by rfl⟩ : syracuseStep 2499749 = 468703) (by norm_num)
theorem B3556541 : Blo 1665032 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B2499773 : Blo 1665032 2499773 := bbase (se 3 (by rfl) ⟨468707, by rfl⟩ : syracuseStep 2499773 = 937415) (by norm_num)
theorem B2499797 : Blo 1665032 2499797 := bbase (se 7 (by rfl) ⟨29294, by rfl⟩ : syracuseStep 2499797 = 58589) (by norm_num)
theorem B3204317 : Blo 1665032 3204317 := bbase (se 3 (by rfl) ⟨600809, by rfl⟩ : syracuseStep 3204317 = 1201619) (by norm_num)
theorem B2811125 : Blo 1665032 2811125 := bbase (se 5 (by rfl) ⟨131771, by rfl⟩ : syracuseStep 2811125 = 263543) (by norm_num)
theorem B4744469 : Blo 1665032 4744469 := bbase (se 6 (by rfl) ⟨111198, by rfl⟩ : syracuseStep 4744469 = 222397) (by norm_num)
theorem B8430965 : Blo 1665032 8430965 := bbase (se 5 (by rfl) ⟨395201, by rfl⟩ : syracuseStep 8430965 = 790403) (by norm_num)
theorem B2811253 : Blo 1665032 2811253 := bbase (se 5 (by rfl) ⟨131777, by rfl⟩ : syracuseStep 2811253 = 263555) (by norm_num)
theorem B3163549 : Blo 1665032 3163549 := bbase (se 3 (by rfl) ⟨593165, by rfl⟩ : syracuseStep 3163549 = 1186331) (by norm_num)
theorem B1779121 : Blo 1665032 1779121 := bbase (se 2 (by rfl) ⟨667170, by rfl⟩ : syracuseStep 1779121 = 1334341) (by norm_num)
theorem B6325685 : Blo 1665032 6325685 := bbase (se 5 (by rfl) ⟨296516, by rfl⟩ : syracuseStep 6325685 = 593033) (by norm_num)
theorem B2811341 : Blo 1665032 2811341 := bbase (se 3 (by rfl) ⟨527126, by rfl⟩ : syracuseStep 2811341 = 1054253) (by norm_num)
theorem B5621237 : Blo 1665032 5621237 := bbase (se 5 (by rfl) ⟨263495, by rfl⟩ : syracuseStep 5621237 = 526991) (by norm_num)
theorem B17098229 : Blo 1665032 17098229 := bbase (se 5 (by rfl) ⟨801479, by rfl⟩ : syracuseStep 17098229 = 1602959) (by norm_num)
theorem B1779193 : Blo 1665032 1779193 := bbase (se 2 (by rfl) ⟨667197, by rfl⟩ : syracuseStep 1779193 = 1334395) (by norm_num)
theorem B3163693 : Blo 1665032 3163693 := bbase (se 3 (by rfl) ⟨593192, by rfl⟩ : syracuseStep 3163693 = 1186385) (by norm_num)
theorem B7112245 : Blo 1665032 7112245 := bbase (se 5 (by rfl) ⟨333386, by rfl⟩ : syracuseStep 7112245 = 666773) (by norm_num)
theorem B7112261 : Blo 1665032 7112261 := bbase (se 4 (by rfl) ⟨666774, by rfl⟩ : syracuseStep 7112261 = 1333549) (by norm_num)
theorem B2811469 : Blo 1665032 2811469 := bbase (se 3 (by rfl) ⟨527150, by rfl⟩ : syracuseStep 2811469 = 1054301) (by norm_num)
theorem B2811557 : Blo 1665032 2811557 := bbase (se 4 (by rfl) ⟨263583, by rfl⟩ : syracuseStep 2811557 = 527167) (by norm_num)
theorem B9488117 : Blo 1665032 9488117 := bbase (se 5 (by rfl) ⟨444755, by rfl⟩ : syracuseStep 9488117 = 889511) (by norm_num)
theorem B2811685 : Blo 1665032 2811685 := bbase (se 4 (by rfl) ⟨263595, by rfl⟩ : syracuseStep 2811685 = 527191) (by norm_num)
theorem B1779565 : Blo 1665032 1779565 := bbase (se 3 (by rfl) ⟨333668, by rfl⟩ : syracuseStep 1779565 = 667337) (by norm_num)
theorem B2811773 : Blo 1665032 2811773 := bbase (se 3 (by rfl) ⟨527207, by rfl⟩ : syracuseStep 2811773 = 1054415) (by norm_num)
theorem B2000785 : Blo 1665032 2000785 := bbase (se 2 (by rfl) ⟨750294, by rfl⟩ : syracuseStep 2000785 = 1500589) (by norm_num)
theorem B5621669 : Blo 1665032 5621669 := bbase (se 4 (by rfl) ⟨527031, by rfl⟩ : syracuseStep 5621669 = 1054063) (by norm_num)
theorem B2705357 : Blo 1665032 2705357 := bbase (se 3 (by rfl) ⟨507254, by rfl⟩ : syracuseStep 2705357 = 1014509) (by norm_num)
theorem B2000881 : Blo 1665032 2000881 := bbase (se 2 (by rfl) ⟨750330, by rfl⟩ : syracuseStep 2000881 = 1500661) (by norm_num)
theorem B2811901 : Blo 1665032 2811901 := bbase (se 3 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 2811901 = 1054463) (by norm_num)
theorem B2107397 : Blo 1665032 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B6752261 : Blo 1665032 6752261 := bbase (se 4 (by rfl) ⟨633024, by rfl⟩ : syracuseStep 6752261 = 1266049) (by norm_num)
theorem B8546309 : Blo 1665032 8546309 := bbase (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) (by norm_num)
theorem B2107453 : Blo 1665032 2107453 := bbase (se 3 (by rfl) ⟨395147, by rfl⟩ : syracuseStep 2107453 = 790295) (by norm_num)
theorem B2811989 : Blo 1665032 2811989 := bbase (se 8 (by rfl) ⟨16476, by rfl⟩ : syracuseStep 2811989 = 32953) (by norm_num)
theorem B32032853 : Blo 1665032 32032853 := bbase (se 8 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 32032853 = 375385) (by norm_num)
theorem B2107549 : Blo 1665032 2107549 := bbase (se 3 (by rfl) ⟨395165, by rfl⟩ : syracuseStep 2107549 = 790331) (by norm_num)
theorem B2566325 : Blo 1665032 2566325 := bbase (se 5 (by rfl) ⟨120296, by rfl⟩ : syracuseStep 2566325 = 240593) (by norm_num)
theorem B2812117 : Blo 1665032 2812117 := bbase (se 7 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 2812117 = 65909) (by norm_num)
theorem B2812205 : Blo 1665032 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B4565317 : Blo 1665032 4565317 := bbase (se 4 (by rfl) ⟨427998, by rfl⟩ : syracuseStep 4565317 = 855997) (by norm_num)
theorem B2107721 : Blo 1665032 2107721 := bbase (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) (by norm_num)
theorem B5622101 : Blo 1665032 5622101 := bbase (se 10 (by rfl) ⟨8235, by rfl⟩ : syracuseStep 5622101 = 16471) (by norm_num)
theorem B2107777 : Blo 1665032 2107777 := bbase (se 2 (by rfl) ⟨790416, by rfl⟩ : syracuseStep 2107777 = 1580833) (by norm_num)
theorem B2107873 : Blo 1665032 2107873 := bbase (se 2 (by rfl) ⟨790452, by rfl⟩ : syracuseStep 2107873 = 1580905) (by norm_num)
theorem B10127861 : Blo 1665032 10127861 := bbase (se 5 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 10127861 = 949487) (by norm_num)
theorem B3746357 : Blo 1665032 3746357 := bbase (se 5 (by rfl) ⟨175610, by rfl⟩ : syracuseStep 3746357 = 351221) (by norm_num)
theorem B8006197 : Blo 1665032 8006197 := bbase (se 5 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 8006197 = 750581) (by norm_num)
theorem B6326869 : Blo 1665032 6326869 := bbase (se 8 (by rfl) ⟨37071, by rfl⟩ : syracuseStep 6326869 = 74143) (by norm_num)
theorem B2312813 : Blo 1665032 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B3746429 : Blo 1665032 3746429 := bbase (se 3 (by rfl) ⟨702455, by rfl⟩ : syracuseStep 3746429 = 1404911) (by norm_num)
theorem B8432261 : Blo 1665032 8432261 := bbase (se 4 (by rfl) ⟨790524, by rfl⟩ : syracuseStep 8432261 = 1581049) (by norm_num)
theorem B2108045 : Blo 1665032 2108045 := bbase (se 3 (by rfl) ⟨395258, by rfl⟩ : syracuseStep 2108045 = 790517) (by norm_num)
theorem B11553461 : Blo 1665032 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B3746501 : Blo 1665032 3746501 := bbase (se 4 (by rfl) ⟨351234, by rfl⟩ : syracuseStep 3746501 = 702469) (by norm_num)
theorem B2108101 : Blo 1665032 2108101 := bbase (se 4 (by rfl) ⟨197634, by rfl⟩ : syracuseStep 2108101 = 395269) (by norm_num)
theorem B5622533 : Blo 1665032 5622533 := bbase (se 4 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 5622533 = 1054225) (by norm_num)
theorem B3746573 : Blo 1665032 3746573 := bbase (se 3 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 3746573 = 1404965) (by norm_num)
theorem B2108197 : Blo 1665032 2108197 := bbase (se 4 (by rfl) ⟨197643, by rfl⟩ : syracuseStep 2108197 = 395287) (by norm_num)
theorem B3558181 : Blo 1665032 3558181 := bbase (se 4 (by rfl) ⟨333579, by rfl⟩ : syracuseStep 3558181 = 667159) (by norm_num)
theorem B3746645 : Blo 1665032 3746645 := bbase (se 9 (by rfl) ⟨10976, by rfl⟩ : syracuseStep 3746645 = 21953) (by norm_num)
theorem B3656533 : Blo 1665032 3656533 := bbase (se 9 (by rfl) ⟨10712, by rfl⟩ : syracuseStep 3656533 = 21425) (by norm_num)
theorem B6327173 : Blo 1665032 6327173 := bbase (se 4 (by rfl) ⟨593172, by rfl⟩ : syracuseStep 6327173 = 1186345) (by norm_num)
theorem B3746717 : Blo 1665032 3746717 := bbase (se 3 (by rfl) ⟨702509, by rfl⟩ : syracuseStep 3746717 = 1405019) (by norm_num)
theorem B2108369 : Blo 1665032 2108369 := bbase (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) (by norm_num)
theorem B2001881 : Blo 1665032 2001881 := bbase (se 2 (by rfl) ⟨750705, by rfl⟩ : syracuseStep 2001881 = 1501411) (by norm_num)
theorem B3746789 : Blo 1665032 3746789 := bbase (se 4 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 3746789 = 702523) (by norm_num)
theorem B2108425 : Blo 1665032 2108425 := bbase (se 2 (by rfl) ⟨790659, by rfl⟩ : syracuseStep 2108425 = 1581319) (by norm_num)
theorem B3746861 : Blo 1665032 3746861 := bbase (se 3 (by rfl) ⟨702536, by rfl⟩ : syracuseStep 3746861 = 1405073) (by norm_num)
theorem B2108521 : Blo 1665032 2108521 := bbase (se 2 (by rfl) ⟨790695, by rfl⟩ : syracuseStep 2108521 = 1581391) (by norm_num)
theorem B3746933 : Blo 1665032 3746933 := bbase (se 5 (by rfl) ⟨175637, by rfl⟩ : syracuseStep 3746933 = 351275) (by norm_num)
theorem B5622965 : Blo 1665032 5622965 := bbase (se 5 (by rfl) ⟨263576, by rfl⟩ : syracuseStep 5622965 = 527153) (by norm_num)
theorem B3747005 : Blo 1665032 3747005 := bbase (se 3 (by rfl) ⟨702563, by rfl⟩ : syracuseStep 3747005 = 1405127) (by norm_num)
theorem B3747077 : Blo 1665032 3747077 := bbase (se 4 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 3747077 = 702577) (by norm_num)
theorem B6753557 : Blo 1665032 6753557 := bbase (se 6 (by rfl) ⟨158286, by rfl⟩ : syracuseStep 6753557 = 316573) (by norm_num)
theorem B2108693 : Blo 1665032 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B3747149 : Blo 1665032 3747149 := bbase (se 3 (by rfl) ⟨702590, by rfl⟩ : syracuseStep 3747149 = 1405181) (by norm_num)
theorem B2108749 : Blo 1665032 2108749 := bbase (se 3 (by rfl) ⟨395390, by rfl⟩ : syracuseStep 2108749 = 790781) (by norm_num)
theorem B3747221 : Blo 1665032 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B2108845 : Blo 1665032 2108845 := bbase (se 3 (by rfl) ⟨395408, by rfl⟩ : syracuseStep 2108845 = 790817) (by norm_num)
theorem B7212485 : Blo 1665032 7212485 := bbase (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) (by norm_num)
theorem B3747293 : Blo 1665032 3747293 := bbase (se 3 (by rfl) ⟨702617, by rfl⟩ : syracuseStep 3747293 = 1405235) (by norm_num)
theorem B3747365 : Blo 1665032 3747365 := bbase (se 4 (by rfl) ⟨351315, by rfl⟩ : syracuseStep 3747365 = 702631) (by norm_num)
theorem B2371141 : Blo 1665032 2371141 := bbase (se 4 (by rfl) ⟨222294, by rfl⟩ : syracuseStep 2371141 = 444589) (by norm_num)
theorem B2109017 : Blo 1665032 2109017 := bbase (se 2 (by rfl) ⟨790881, by rfl⟩ : syracuseStep 2109017 = 1581763) (by norm_num)
theorem B5623397 : Blo 1665032 5623397 := bbase (se 4 (by rfl) ⟨527193, by rfl⟩ : syracuseStep 5623397 = 1054387) (by norm_num)
theorem B3747437 : Blo 1665032 3747437 := bbase (se 3 (by rfl) ⟨702644, by rfl⟩ : syracuseStep 3747437 = 1405289) (by norm_num)
theorem B2109073 : Blo 1665032 2109073 := bbase (se 2 (by rfl) ⟨790902, by rfl⟩ : syracuseStep 2109073 = 1581805) (by norm_num)
theorem B3559069 : Blo 1665032 3559069 := bbase (se 3 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 3559069 = 1334651) (by norm_num)
theorem B3747509 : Blo 1665032 3747509 := bbase (se 5 (by rfl) ⟨175664, by rfl⟩ : syracuseStep 3747509 = 351329) (by norm_num)
theorem B2109169 : Blo 1665032 2109169 := bbase (se 2 (by rfl) ⟨790938, by rfl⟩ : syracuseStep 2109169 = 1581877) (by norm_num)
theorem B3747581 : Blo 1665032 3747581 := bbase (se 3 (by rfl) ⟨702671, by rfl⟩ : syracuseStep 3747581 = 1405343) (by norm_num)
theorem B7114517 : Blo 1665032 7114517 := bbase (se 6 (by rfl) ⟨166746, by rfl⟩ : syracuseStep 7114517 = 333493) (by norm_num)
theorem B3747653 : Blo 1665032 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B3747725 : Blo 1665032 3747725 := bbase (se 3 (by rfl) ⟨702698, by rfl⟩ : syracuseStep 3747725 = 1405397) (by norm_num)
theorem B8433557 : Blo 1665032 8433557 := bbase (se 6 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 8433557 = 395323) (by norm_num)
theorem B4214693 : Blo 1665032 4214693 := bbase (se 4 (by rfl) ⟨395127, by rfl⟩ : syracuseStep 4214693 = 790255) (by norm_num)
theorem B3747797 : Blo 1665032 3747797 := bbase (se 7 (by rfl) ⟨43919, by rfl⟩ : syracuseStep 3747797 = 87839) (by norm_num)
theorem B5623829 : Blo 1665032 5623829 := bbase (se 6 (by rfl) ⟨131808, by rfl⟩ : syracuseStep 5623829 = 263617) (by norm_num)
theorem B3747869 : Blo 1665032 3747869 := bbase (se 3 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 3747869 = 1405451) (by norm_num)
theorem B6754373 : Blo 1665032 6754373 := bbase (se 4 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 6754373 = 1266445) (by norm_num)
theorem B3747941 : Blo 1665032 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B3043469 : Blo 1665032 3043469 := bbase (se 3 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 3043469 = 1141301) (by norm_num)
theorem B1781921 : Blo 1665032 1781921 := bbase (se 2 (by rfl) ⟨668220, by rfl⟩ : syracuseStep 1781921 = 1336441) (by norm_num)
theorem B3748013 : Blo 1665032 3748013 := bbase (se 3 (by rfl) ⟨702752, by rfl⟩ : syracuseStep 3748013 = 1405505) (by norm_num)
theorem B3748085 : Blo 1665032 3748085 := bbase (se 5 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 3748085 = 351383) (by norm_num)
theorem B4215037 : Blo 1665032 4215037 := bbase (se 3 (by rfl) ⟨790319, by rfl⟩ : syracuseStep 4215037 = 1580639) (by norm_num)
theorem B3748157 : Blo 1665032 3748157 := bbase (se 3 (by rfl) ⟨702779, by rfl⟩ : syracuseStep 3748157 = 1405559) (by norm_num)
theorem B8335685 : Blo 1665032 8335685 := bbase (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) (by norm_num)
theorem B2371933 : Blo 1665032 2371933 := bbase (se 3 (by rfl) ⟨444737, by rfl⟩ : syracuseStep 2371933 = 889475) (by norm_num)
theorem B4215149 : Blo 1665032 4215149 := bbase (se 3 (by rfl) ⟨790340, by rfl⟩ : syracuseStep 4215149 = 1580681) (by norm_num)
theorem B3748229 : Blo 1665032 3748229 := bbase (se 4 (by rfl) ⟨351396, by rfl⟩ : syracuseStep 3748229 = 702793) (by norm_num)
theorem B4002205 : Blo 1665032 4002205 := bbase (se 3 (by rfl) ⟨750413, by rfl⟩ : syracuseStep 4002205 = 1500827) (by norm_num)
theorem B8114597 : Blo 1665032 8114597 := bbase (se 4 (by rfl) ⟨760743, by rfl⟩ : syracuseStep 8114597 = 1521487) (by norm_num)
theorem B5624261 : Blo 1665032 5624261 := bbase (se 4 (by rfl) ⟨527274, by rfl⟩ : syracuseStep 5624261 = 1054549) (by norm_num)
theorem B3748301 : Blo 1665032 3748301 := bbase (se 3 (by rfl) ⟨702806, by rfl⟩ : syracuseStep 3748301 = 1405613) (by norm_num)
theorem B4002301 : Blo 1665032 4002301 := bbase (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) (by norm_num)
theorem B3748373 : Blo 1665032 3748373 := bbase (se 6 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 3748373 = 175705) (by norm_num)
theorem B4215341 : Blo 1665032 4215341 := bbase (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) (by norm_num)
theorem B3748445 : Blo 1665032 3748445 := bbase (se 3 (by rfl) ⟨702833, by rfl⟩ : syracuseStep 3748445 = 1405667) (by norm_num)
theorem B5337733 : Blo 1665032 5337733 := bbase (se 4 (by rfl) ⟨500412, by rfl⟩ : syracuseStep 5337733 = 1000825) (by norm_num)
theorem B3043997 : Blo 1665032 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B3748517 : Blo 1665032 3748517 := bbase (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) (by norm_num)
theorem B2372269 : Blo 1665032 2372269 := bbase (se 3 (by rfl) ⟨444800, by rfl⟩ : syracuseStep 2372269 = 889601) (by norm_num)
theorem B4002493 : Blo 1665032 4002493 := bbase (se 3 (by rfl) ⟨750467, by rfl⟩ : syracuseStep 4002493 = 1500935) (by norm_num)
theorem B22794965 : Blo 1665032 22794965 := bbase (se 7 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 22794965 = 534257) (by norm_num)
theorem B3748589 : Blo 1665032 3748589 := bbase (se 3 (by rfl) ⟨702860, by rfl⟩ : syracuseStep 3748589 = 1405721) (by norm_num)
theorem B3748661 : Blo 1665032 3748661 := bbase (se 5 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 3748661 = 351437) (by norm_num)
theorem B28840789 : Blo 1665032 28840789 := bbase (se 9 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 28840789 = 168989) (by norm_num)
theorem B9884501 : Blo 1665032 9884501 := bbase (se 9 (by rfl) ⟨28958, by rfl⟩ : syracuseStep 9884501 = 57917) (by norm_num)
theorem B3748733 : Blo 1665032 3748733 := bbase (se 3 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 3748733 = 1405775) (by norm_num)
theorem B4215685 : Blo 1665032 4215685 := bbase (se 4 (by rfl) ⟨395220, by rfl⟩ : syracuseStep 4215685 = 790441) (by norm_num)
theorem B5337989 : Blo 1665032 5337989 := bbase (se 4 (by rfl) ⟨500436, by rfl⟩ : syracuseStep 5337989 = 1000873) (by norm_num)
theorem B2372485 : Blo 1665032 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B3748805 : Blo 1665032 3748805 := bbase (se 4 (by rfl) ⟨351450, by rfl⟩ : syracuseStep 3748805 = 702901) (by norm_num)
theorem B4215797 : Blo 1665032 4215797 := bbase (se 5 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 4215797 = 395231) (by norm_num)
theorem B4002821 : Blo 1665032 4002821 := bbase (se 4 (by rfl) ⟨375264, by rfl⟩ : syracuseStep 4002821 = 750529) (by norm_num)
theorem B3748877 : Blo 1665032 3748877 := bbase (se 3 (by rfl) ⟨702914, by rfl⟩ : syracuseStep 3748877 = 1405829) (by norm_num)
theorem B13505557 : Blo 1665032 13505557 := bbase (se 6 (by rfl) ⟨316536, by rfl⟩ : syracuseStep 13505557 = 633073) (by norm_num)
theorem B3748949 : Blo 1665032 3748949 := bbase (se 8 (by rfl) ⟨21966, by rfl⟩ : syracuseStep 3748949 = 43933) (by norm_num)
theorem B3749021 : Blo 1665032 3749021 := bbase (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) (by norm_num)
theorem B8434853 : Blo 1665032 8434853 := bbase (se 4 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 8434853 = 1581535) (by norm_num)
theorem B4215989 : Blo 1665032 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B3749093 : Blo 1665032 3749093 := bbase (se 4 (by rfl) ⟨351477, by rfl⟩ : syracuseStep 3749093 = 702955) (by norm_num)
theorem B14226677 : Blo 1665032 14226677 := bbase (se 5 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 14226677 = 1333751) (by norm_num)
theorem B1873165 : Blo 1665032 1873165 := bbase (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) (by norm_num)
theorem B3749165 : Blo 1665032 3749165 := bbase (se 3 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 3749165 = 1405937) (by norm_num)
theorem B1873201 : Blo 1665032 1873201 := bbase (se 2 (by rfl) ⟨702450, by rfl⟩ : syracuseStep 1873201 = 1404901) (by norm_num)
theorem B2667829 : Blo 1665032 2667829 := bbase (se 5 (by rfl) ⟨125054, by rfl⟩ : syracuseStep 2667829 = 250109) (by norm_num)
theorem B1873237 : Blo 1665032 1873237 := bbase (se 14 (by rfl) ⟨171, by rfl⟩ : syracuseStep 1873237 = 343) (by norm_num)
theorem B3749237 : Blo 1665032 3749237 := bbase (se 5 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 3749237 = 351491) (by norm_num)
theorem B1873273 : Blo 1665032 1873273 := bbase (se 2 (by rfl) ⟨702477, by rfl⟩ : syracuseStep 1873273 = 1404955) (by norm_num)
theorem B1873309 : Blo 1665032 1873309 := bbase (se 3 (by rfl) ⟨351245, by rfl⟩ : syracuseStep 1873309 = 702491) (by norm_num)
theorem B4003253 : Blo 1665032 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B3749309 : Blo 1665032 3749309 := bbase (se 3 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 3749309 = 1405991) (by norm_num)
theorem B1873345 : Blo 1665032 1873345 := bbase (se 2 (by rfl) ⟨702504, by rfl⟩ : syracuseStep 1873345 = 1405009) (by norm_num)
theorem B1873381 : Blo 1665032 1873381 := bbase (se 4 (by rfl) ⟨175629, by rfl⟩ : syracuseStep 1873381 = 351259) (by norm_num)
theorem B3421685 : Blo 1665032 3421685 := bbase (se 5 (by rfl) ⟨160391, by rfl⟩ : syracuseStep 3421685 = 320783) (by norm_num)
theorem B3749381 : Blo 1665032 3749381 := bbase (se 4 (by rfl) ⟨351504, by rfl⟩ : syracuseStep 3749381 = 703009) (by norm_num)
theorem B1873417 : Blo 1665032 1873417 := bbase (se 2 (by rfl) ⟨702531, by rfl⟩ : syracuseStep 1873417 = 1405063) (by norm_num)
theorem B4216333 : Blo 1665032 4216333 := bbase (se 3 (by rfl) ⟨790562, by rfl⟩ : syracuseStep 4216333 = 1581125) (by norm_num)
theorem B1873453 : Blo 1665032 1873453 := bbase (se 3 (by rfl) ⟨351272, by rfl⟩ : syracuseStep 1873453 = 702545) (by norm_num)
theorem B3749453 : Blo 1665032 3749453 := bbase (se 3 (by rfl) ⟨703022, by rfl⟩ : syracuseStep 3749453 = 1406045) (by norm_num)
theorem B1873489 : Blo 1665032 1873489 := bbase (se 2 (by rfl) ⟨702558, by rfl⟩ : syracuseStep 1873489 = 1405117) (by norm_num)
theorem B1873525 : Blo 1665032 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B4216445 : Blo 1665032 4216445 := bbase (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) (by norm_num)
theorem B9483925 : Blo 1665032 9483925 := bbase (se 6 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 9483925 = 444559) (by norm_num)
theorem B3749525 : Blo 1665032 3749525 := bbase (se 6 (by rfl) ⟨87879, by rfl⟩ : syracuseStep 3749525 = 175759) (by norm_num)
theorem B1873561 : Blo 1665032 1873561 := bbase (se 2 (by rfl) ⟨702585, by rfl⟩ : syracuseStep 1873561 = 1405171) (by norm_num)
theorem B1873597 : Blo 1665032 1873597 := bbase (se 3 (by rfl) ⟨351299, by rfl⟩ : syracuseStep 1873597 = 702599) (by norm_num)
theorem B3749597 : Blo 1665032 3749597 := bbase (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) (by norm_num)
theorem B1873633 : Blo 1665032 1873633 := bbase (se 2 (by rfl) ⟨702612, by rfl⟩ : syracuseStep 1873633 = 1405225) (by norm_num)
theorem B4806373 : Blo 1665032 4806373 := bbase (se 4 (by rfl) ⟨450597, by rfl⟩ : syracuseStep 4806373 = 901195) (by norm_num)
theorem B4273901 : Blo 1665032 4273901 := bbase (se 3 (by rfl) ⟨801356, by rfl⟩ : syracuseStep 4273901 = 1602713) (by norm_num)
theorem B1873669 : Blo 1665032 1873669 := bbase (se 4 (by rfl) ⟨175656, by rfl⟩ : syracuseStep 1873669 = 351313) (by norm_num)
theorem B4003589 : Blo 1665032 4003589 := bbase (se 4 (by rfl) ⟨375336, by rfl⟩ : syracuseStep 4003589 = 750673) (by norm_num)
theorem B3749669 : Blo 1665032 3749669 := bbase (se 4 (by rfl) ⟨351531, by rfl⟩ : syracuseStep 3749669 = 703063) (by norm_num)
theorem B1873705 : Blo 1665032 1873705 := bbase (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) (by norm_num)
theorem B4331317 : Blo 1665032 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B4216637 : Blo 1665032 4216637 := bbase (se 3 (by rfl) ⟨790619, by rfl⟩ : syracuseStep 4216637 = 1581239) (by norm_num)
theorem B1873741 : Blo 1665032 1873741 := bbase (se 3 (by rfl) ⟨351326, by rfl⟩ : syracuseStep 1873741 = 702653) (by norm_num)
theorem B4274005 : Blo 1665032 4274005 := bbase (se 9 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 4274005 = 25043) (by norm_num)
theorem B1873777 : Blo 1665032 1873777 := bbase (se 2 (by rfl) ⟨702666, by rfl⟩ : syracuseStep 1873777 = 1405333) (by norm_num)
theorem B1873813 : Blo 1665032 1873813 := bbase (se 6 (by rfl) ⟨43917, by rfl⟩ : syracuseStep 1873813 = 87835) (by norm_num)
theorem B1873849 : Blo 1665032 1873849 := bbase (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) (by norm_num)
theorem B1873885 : Blo 1665032 1873885 := bbase (se 3 (by rfl) ⟨351353, by rfl⟩ : syracuseStep 1873885 = 702707) (by norm_num)
theorem B1873921 : Blo 1665032 1873921 := bbase (se 2 (by rfl) ⟨702720, by rfl⟩ : syracuseStep 1873921 = 1405441) (by norm_num)
theorem B1873957 : Blo 1665032 1873957 := bbase (se 4 (by rfl) ⟨175683, by rfl⟩ : syracuseStep 1873957 = 351367) (by norm_num)
theorem B1873993 : Blo 1665032 1873993 := bbase (se 2 (by rfl) ⟨702747, by rfl⟩ : syracuseStep 1873993 = 1405495) (by norm_num)
theorem B3799133 : Blo 1665032 3799133 := bbase (se 3 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 3799133 = 1424675) (by norm_num)
theorem B1874029 : Blo 1665032 1874029 := bbase (se 3 (by rfl) ⟨351380, by rfl⟩ : syracuseStep 1874029 = 702761) (by norm_num)
theorem B2136181 : Blo 1665032 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B1874065 : Blo 1665032 1874065 := bbase (se 2 (by rfl) ⟨702774, by rfl⟩ : syracuseStep 1874065 = 1405549) (by norm_num)
theorem B4216981 : Blo 1665032 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B4274333 : Blo 1665032 4274333 := bbase (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) (by norm_num)
theorem B1874101 : Blo 1665032 1874101 := bbase (se 5 (by rfl) ⟨87848, by rfl⟩ : syracuseStep 1874101 = 175697) (by norm_num)
theorem B1874137 : Blo 1665032 1874137 := bbase (se 2 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 1874137 = 1405603) (by norm_num)
theorem B1874173 : Blo 1665032 1874173 := bbase (se 3 (by rfl) ⟨351407, by rfl⟩ : syracuseStep 1874173 = 702815) (by norm_num)
theorem B4217093 : Blo 1665032 4217093 := bbase (se 4 (by rfl) ⟨395352, by rfl⟩ : syracuseStep 4217093 = 790705) (by norm_num)
theorem B1874209 : Blo 1665032 1874209 := bbase (se 2 (by rfl) ⟨702828, by rfl⟩ : syracuseStep 1874209 = 1405657) (by norm_num)
theorem B1874245 : Blo 1665032 1874245 := bbase (se 4 (by rfl) ⟨175710, by rfl⟩ : syracuseStep 1874245 = 351421) (by norm_num)
theorem B10672469 : Blo 1665032 10672469 := bbase (se 10 (by rfl) ⟨15633, by rfl⟩ : syracuseStep 10672469 = 31267) (by norm_num)
theorem B1874281 : Blo 1665032 1874281 := bbase (se 2 (by rfl) ⟨702855, by rfl⟩ : syracuseStep 1874281 = 1405711) (by norm_num)
theorem B1874317 : Blo 1665032 1874317 := bbase (se 3 (by rfl) ⟨351434, by rfl⟩ : syracuseStep 1874317 = 702869) (by norm_num)
theorem B2136469 : Blo 1665032 2136469 := bbase (se 6 (by rfl) ⟨50073, by rfl⟩ : syracuseStep 2136469 = 100147) (by norm_num)
theorem B2251165 : Blo 1665032 2251165 := bbase (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) (by norm_num)
theorem B1874353 : Blo 1665032 1874353 := bbase (se 2 (by rfl) ⟨702882, by rfl⟩ : syracuseStep 1874353 = 1405765) (by norm_num)
theorem B10131893 : Blo 1665032 10131893 := bbase (se 5 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 10131893 = 949865) (by norm_num)
theorem B8436149 : Blo 1665032 8436149 := bbase (se 5 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 8436149 = 790889) (by norm_num)
theorem B2849213 : Blo 1665032 2849213 := bbase (se 3 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 2849213 = 1068455) (by norm_num)
theorem B4217285 : Blo 1665032 4217285 := bbase (se 4 (by rfl) ⟨395370, by rfl⟩ : syracuseStep 4217285 = 790741) (by norm_num)
theorem B1874389 : Blo 1665032 1874389 := bbase (se 7 (by rfl) ⟨21965, by rfl⟩ : syracuseStep 1874389 = 43931) (by norm_num)
theorem B2669021 : Blo 1665032 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B1899001 : Blo 1665032 1899001 := bbase (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) (by norm_num)
theorem B1874425 : Blo 1665032 1874425 := bbase (se 2 (by rfl) ⟨702909, by rfl⟩ : syracuseStep 1874425 = 1405819) (by norm_num)
theorem B1874461 : Blo 1665032 1874461 := bbase (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) (by norm_num)
theorem B1874497 : Blo 1665032 1874497 := bbase (se 2 (by rfl) ⟨702936, by rfl⟩ : syracuseStep 1874497 = 1405873) (by norm_num)
theorem B1874533 : Blo 1665032 1874533 := bbase (se 4 (by rfl) ⟨175737, by rfl⟩ : syracuseStep 1874533 = 351475) (by norm_num)
theorem B2251397 : Blo 1665032 2251397 := bbase (se 4 (by rfl) ⟨211068, by rfl⟩ : syracuseStep 2251397 = 422137) (by norm_num)
theorem B1874569 : Blo 1665032 1874569 := bbase (se 2 (by rfl) ⟨702963, by rfl⟩ : syracuseStep 1874569 = 1405927) (by norm_num)
theorem B2669213 : Blo 1665032 2669213 := bbase (se 3 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 2669213 = 1000955) (by norm_num)
theorem B1874605 : Blo 1665032 1874605 := bbase (se 3 (by rfl) ⟨351488, by rfl⟩ : syracuseStep 1874605 = 702977) (by norm_num)
theorem B1874641 : Blo 1665032 1874641 := bbase (se 2 (by rfl) ⟨702990, by rfl⟩ : syracuseStep 1874641 = 1405981) (by norm_num)
theorem B4741861 : Blo 1665032 4741861 := bbase (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) (by norm_num)
theorem B1874677 : Blo 1665032 1874677 := bbase (se 5 (by rfl) ⟨87875, by rfl⟩ : syracuseStep 1874677 = 175751) (by norm_num)
theorem B1874713 : Blo 1665032 1874713 := bbase (se 2 (by rfl) ⟨703017, by rfl⟩ : syracuseStep 1874713 = 1406035) (by norm_num)
theorem B4217629 : Blo 1665032 4217629 := bbase (se 3 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 4217629 = 1581611) (by norm_num)
theorem B6322981 : Blo 1665032 6322981 := bbase (se 4 (by rfl) ⟨592779, by rfl⟩ : syracuseStep 6322981 = 1185559) (by norm_num)
theorem B1874749 : Blo 1665032 1874749 := bbase (se 3 (by rfl) ⟨351515, by rfl⟩ : syracuseStep 1874749 = 703031) (by norm_num)
theorem B1874785 : Blo 1665032 1874785 := bbase (se 2 (by rfl) ⟨703044, by rfl⟩ : syracuseStep 1874785 = 1406089) (by norm_num)
theorem B1874821 : Blo 1665032 1874821 := bbase (se 4 (by rfl) ⟨175764, by rfl⟩ : syracuseStep 1874821 = 351529) (by norm_num)
theorem B4217741 : Blo 1665032 4217741 := bbase (se 3 (by rfl) ⟨790826, by rfl⟩ : syracuseStep 4217741 = 1581653) (by norm_num)
theorem B4275125 : Blo 1665032 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B2497565 : Blo 1665032 2497565 := bbase (se 3 (by rfl) ⟨468293, by rfl⟩ : syracuseStep 2497565 = 936587) (by norm_num)
theorem B2497589 : Blo 1665032 2497589 := bbase (se 5 (by rfl) ⟨117074, by rfl⟩ : syracuseStep 2497589 = 234149) (by norm_num)
theorem B5135413 : Blo 1665032 5135413 := bbase (se 5 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 5135413 = 481445) (by norm_num)
theorem B2497613 : Blo 1665032 2497613 := bbase (se 3 (by rfl) ⟨468302, by rfl⟩ : syracuseStep 2497613 = 936605) (by norm_num)
theorem B2849869 : Blo 1665032 2849869 := bbase (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) (by norm_num)
theorem B4217933 : Blo 1665032 4217933 := bbase (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) (by norm_num)
theorem B6323285 : Blo 1665032 6323285 := bbase (se 8 (by rfl) ⟨37050, by rfl⟩ : syracuseStep 6323285 = 74101) (by norm_num)
theorem B2497637 : Blo 1665032 2497637 := bbase (se 4 (by rfl) ⟨234153, by rfl⟩ : syracuseStep 2497637 = 468307) (by norm_num)
theorem B2497661 : Blo 1665032 2497661 := bbase (se 3 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 2497661 = 936623) (by norm_num)
theorem B2497685 : Blo 1665032 2497685 := bbase (se 6 (by rfl) ⟨58539, by rfl⟩ : syracuseStep 2497685 = 117079) (by norm_num)
theorem B2497709 : Blo 1665032 2497709 := bbase (se 3 (by rfl) ⟨468320, by rfl⟩ : syracuseStep 2497709 = 936641) (by norm_num)
theorem B2497733 : Blo 1665032 2497733 := bbase (se 4 (by rfl) ⟨234162, by rfl⟩ : syracuseStep 2497733 = 468325) (by norm_num)
theorem B2497757 : Blo 1665032 2497757 := bbase (se 3 (by rfl) ⟨468329, by rfl⟩ : syracuseStep 2497757 = 936659) (by norm_num)
theorem B2497781 : Blo 1665032 2497781 := bbase (se 5 (by rfl) ⟨117083, by rfl⟩ : syracuseStep 2497781 = 234167) (by norm_num)
theorem B16014581 : Blo 1665032 16014581 := bbase (se 5 (by rfl) ⟨750683, by rfl⟩ : syracuseStep 16014581 = 1501367) (by norm_num)
theorem B2497805 : Blo 1665032 2497805 := bbase (se 3 (by rfl) ⟨468338, by rfl⟩ : syracuseStep 2497805 = 936677) (by norm_num)
theorem B2497829 : Blo 1665032 2497829 := bbase (se 4 (by rfl) ⟨234171, by rfl⟩ : syracuseStep 2497829 = 468343) (by norm_num)
theorem B2497853 : Blo 1665032 2497853 := bbase (se 3 (by rfl) ⟨468347, by rfl⟩ : syracuseStep 2497853 = 936695) (by norm_num)
theorem B2497877 : Blo 1665032 2497877 := bbase (se 11 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 2497877 = 3659) (by norm_num)
theorem B2497901 : Blo 1665032 2497901 := bbase (se 3 (by rfl) ⟨468356, by rfl⟩ : syracuseStep 2497901 = 936713) (by norm_num)
theorem B9125237 : Blo 1665032 9125237 := bbase (se 5 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 9125237 = 855491) (by norm_num)
theorem B2497925 : Blo 1665032 2497925 := bbase (se 4 (by rfl) ⟨234180, by rfl⟩ : syracuseStep 2497925 = 468361) (by norm_num)
theorem B2497949 : Blo 1665032 2497949 := bbase (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) (by norm_num)
theorem B4218277 : Blo 1665032 4218277 := bbase (se 4 (by rfl) ⟨395463, by rfl⟩ : syracuseStep 4218277 = 790927) (by norm_num)
theorem B2497973 : Blo 1665032 2497973 := bbase (se 5 (by rfl) ⟨117092, by rfl⟩ : syracuseStep 2497973 = 234185) (by norm_num)
theorem B2497997 : Blo 1665032 2497997 := bbase (se 3 (by rfl) ⟨468374, by rfl⟩ : syracuseStep 2497997 = 936749) (by norm_num)
theorem B2498021 : Blo 1665032 2498021 := bbase (se 4 (by rfl) ⟨234189, by rfl⟩ : syracuseStep 2498021 = 468379) (by norm_num)
theorem B2498045 : Blo 1665032 2498045 := bbase (se 3 (by rfl) ⟨468383, by rfl⟩ : syracuseStep 2498045 = 936767) (by norm_num)
theorem B3161605 : Blo 1665032 3161605 := bbase (se 4 (by rfl) ⟨296400, by rfl⟩ : syracuseStep 3161605 = 592801) (by norm_num)
theorem B2498069 : Blo 1665032 2498069 := bbase (se 6 (by rfl) ⟨58548, by rfl⟩ : syracuseStep 2498069 = 117097) (by norm_num)
theorem B4218389 : Blo 1665032 4218389 := bbase (se 6 (by rfl) ⟨98868, by rfl⟩ : syracuseStep 4218389 = 197737) (by norm_num)
theorem B2498093 : Blo 1665032 2498093 := bbase (se 3 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 2498093 = 936785) (by norm_num)
theorem B2252333 : Blo 1665032 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B2498117 : Blo 1665032 2498117 := bbase (se 4 (by rfl) ⟨234198, by rfl⟩ : syracuseStep 2498117 = 468397) (by norm_num)
theorem B9485909 : Blo 1665032 9485909 := bbase (se 8 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 9485909 = 111163) (by norm_num)
theorem B2137685 : Blo 1665032 2137685 := bbase (se 8 (by rfl) ⟨12525, by rfl⟩ : syracuseStep 2137685 = 25051) (by norm_num)
theorem B2498141 : Blo 1665032 2498141 := bbase (se 3 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 2498141 = 936803) (by norm_num)
theorem B2498165 : Blo 1665032 2498165 := bbase (se 5 (by rfl) ⟨117101, by rfl⟩ : syracuseStep 2498165 = 234203) (by norm_num)
theorem B2498189 : Blo 1665032 2498189 := bbase (se 3 (by rfl) ⟨468410, by rfl⟩ : syracuseStep 2498189 = 936821) (by norm_num)
theorem B3161749 : Blo 1665032 3161749 := bbase (se 6 (by rfl) ⟨74103, by rfl⟩ : syracuseStep 3161749 = 148207) (by norm_num)
theorem B2498213 : Blo 1665032 2498213 := bbase (se 4 (by rfl) ⟨234207, by rfl⟩ : syracuseStep 2498213 = 468415) (by norm_num)
theorem B1900201 : Blo 1665032 1900201 := bbase (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) (by norm_num)
theorem B2498237 : Blo 1665032 2498237 := bbase (se 3 (by rfl) ⟨468419, by rfl⟩ : syracuseStep 2498237 = 936839) (by norm_num)
theorem B1900241 : Blo 1665032 1900241 := bbase (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) (by norm_num)
theorem B2498261 : Blo 1665032 2498261 := bbase (se 7 (by rfl) ⟨29276, by rfl⟩ : syracuseStep 2498261 = 58553) (by norm_num)
theorem B12648149 : Blo 1665032 12648149 := bbase (se 7 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 12648149 = 296441) (by norm_num)
theorem B7118549 : Blo 1665032 7118549 := bbase (se 7 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 7118549 = 166841) (by norm_num)
theorem B2498285 : Blo 1665032 2498285 := bbase (se 3 (by rfl) ⟨468428, by rfl⟩ : syracuseStep 2498285 = 936857) (by norm_num)
theorem B2498309 : Blo 1665032 2498309 := bbase (se 4 (by rfl) ⟨234216, by rfl⟩ : syracuseStep 2498309 = 468433) (by norm_num)
theorem B2498333 : Blo 1665032 2498333 := bbase (se 3 (by rfl) ⟨468437, by rfl⟩ : syracuseStep 2498333 = 936875) (by norm_num)
theorem B5619509 : Blo 1665032 5619509 := bbase (se 5 (by rfl) ⟨263414, by rfl⟩ : syracuseStep 5619509 = 526829) (by norm_num)
theorem B3161909 : Blo 1665032 3161909 := bbase (se 5 (by rfl) ⟨148214, by rfl⟩ : syracuseStep 3161909 = 296429) (by norm_num)
theorem B4742965 : Blo 1665032 4742965 := bbase (se 5 (by rfl) ⟨222326, by rfl⟩ : syracuseStep 4742965 = 444653) (by norm_num)
theorem B2498357 : Blo 1665032 2498357 := bbase (se 5 (by rfl) ⟨117110, by rfl⟩ : syracuseStep 2498357 = 234221) (by norm_num)
theorem B2498381 : Blo 1665032 2498381 := bbase (se 3 (by rfl) ⟨468446, by rfl⟩ : syracuseStep 2498381 = 936893) (by norm_num)
theorem B2498405 : Blo 1665032 2498405 := bbase (se 4 (by rfl) ⟨234225, by rfl⟩ : syracuseStep 2498405 = 468451) (by norm_num)
theorem B2498429 : Blo 1665032 2498429 := bbase (se 3 (by rfl) ⟨468455, by rfl⟩ : syracuseStep 2498429 = 936911) (by norm_num)
theorem B2498453 : Blo 1665032 2498453 := bbase (se 6 (by rfl) ⟨58557, by rfl⟩ : syracuseStep 2498453 = 117115) (by norm_num)
theorem B2498477 : Blo 1665032 2498477 := bbase (se 3 (by rfl) ⟨468464, by rfl⟩ : syracuseStep 2498477 = 936929) (by norm_num)
theorem B3162053 : Blo 1665032 3162053 := bbase (se 4 (by rfl) ⟨296442, by rfl⟩ : syracuseStep 3162053 = 592885) (by norm_num)
theorem B2498501 : Blo 1665032 2498501 := bbase (se 4 (by rfl) ⟨234234, by rfl⟩ : syracuseStep 2498501 = 468469) (by norm_num)
theorem B2498525 : Blo 1665032 2498525 := bbase (se 3 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 2498525 = 936947) (by norm_num)
theorem B2809829 : Blo 1665032 2809829 := bbase (se 4 (by rfl) ⟨263421, by rfl⟩ : syracuseStep 2809829 = 526843) (by norm_num)
theorem B2498549 : Blo 1665032 2498549 := bbase (se 5 (by rfl) ⟨117119, by rfl⟩ : syracuseStep 2498549 = 234239) (by norm_num)
theorem B2498561 : Blo 1665032 2498561 := bstep (se 2 (by rfl) ⟨936960, by rfl⟩ : syracuseStep 2498561 = 1873921) B1873921
theorem B9486341 : Blo 1665032 9486341 := bstep (se 4 (by rfl) ⟨889344, by rfl⟩ : syracuseStep 9486341 = 1778689) B1778689
theorem B5619725 : Blo 1665032 5619725 := bstep (se 3 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 5619725 = 2107397) B2107397
theorem B2498579 : Blo 1665032 2498579 := bstep (se 1 (by rfl) ⟨1873934, by rfl⟩ : syracuseStep 2498579 = 3747869) B3747869
theorem B2498609 : Blo 1665032 2498609 := bstep (se 2 (by rfl) ⟨936978, by rfl⟩ : syracuseStep 2498609 = 1873957) B1873957
theorem B5619779 : Blo 1665032 5619779 := bstep (se 1 (by rfl) ⟨4214834, by rfl⟩ : syracuseStep 5619779 = 8429669) B8429669
theorem B2498627 : Blo 1665032 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B2809937 : Blo 1665032 2809937 := bstep (se 2 (by rfl) ⟨1053726, by rfl⟩ : syracuseStep 2809937 = 2107453) B2107453
theorem B2498657 : Blo 1665032 2498657 := bstep (se 2 (by rfl) ⟨936996, by rfl⟩ : syracuseStep 2498657 = 1873993) B1873993
theorem B2498675 : Blo 1665032 2498675 := bstep (se 1 (by rfl) ⟨1874006, by rfl⟩ : syracuseStep 2498675 = 3748013) B3748013
theorem B2498705 : Blo 1665032 2498705 := bstep (se 2 (by rfl) ⟨937014, by rfl⟩ : syracuseStep 2498705 = 1874029) B1874029
theorem B2498723 : Blo 1665032 2498723 := bstep (se 1 (by rfl) ⟨1874042, by rfl⟩ : syracuseStep 2498723 = 3748085) B3748085
theorem B2703539 : Blo 1665032 2703539 := bstep (se 1 (by rfl) ⟨2027654, by rfl⟩ : syracuseStep 2703539 = 4055309) B4055309
theorem B2498753 : Blo 1665032 2498753 := bstep (se 2 (by rfl) ⟨937032, by rfl⟩ : syracuseStep 2498753 = 1874065) B1874065
theorem B2810065 : Blo 1665032 2810065 := bstep (se 2 (by rfl) ⟨1053774, by rfl⟩ : syracuseStep 2810065 = 2107549) B2107549
theorem B2498771 : Blo 1665032 2498771 := bstep (se 1 (by rfl) ⟨1874078, by rfl⟩ : syracuseStep 2498771 = 3748157) B3748157
theorem B2498801 : Blo 1665032 2498801 := bstep (se 2 (by rfl) ⟨937050, by rfl⟩ : syracuseStep 2498801 = 1874101) B1874101
theorem B2810099 : Blo 1665032 2810099 := bstep (se 1 (by rfl) ⟨2107574, by rfl⟩ : syracuseStep 2810099 = 4215149) B4215149
theorem B2498819 : Blo 1665032 2498819 := bstep (se 1 (by rfl) ⟨1874114, by rfl⟩ : syracuseStep 2498819 = 3748229) B3748229
theorem B2498849 : Blo 1665032 2498849 := bstep (se 2 (by rfl) ⟨937068, by rfl⟩ : syracuseStep 2498849 = 1874137) B1874137
theorem B2498867 : Blo 1665032 2498867 := bstep (se 1 (by rfl) ⟨1874150, by rfl⟩ : syracuseStep 2498867 = 3748301) B3748301
theorem B5620049 : Blo 1665032 5620049 := bstep (se 2 (by rfl) ⟨2107518, by rfl⟩ : syracuseStep 5620049 = 4215037) B4215037
theorem B2498897 : Blo 1665032 2498897 := bstep (se 2 (by rfl) ⟨937086, by rfl⟩ : syracuseStep 2498897 = 1874173) B1874173
theorem B2498915 : Blo 1665032 2498915 := bstep (se 1 (by rfl) ⟨1874186, by rfl⟩ : syracuseStep 2498915 = 3748373) B3748373
theorem B2810227 : Blo 1665032 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B2498945 : Blo 1665032 2498945 := bstep (se 2 (by rfl) ⟨937104, by rfl⟩ : syracuseStep 2498945 = 1874209) B1874209
theorem B2498963 : Blo 1665032 2498963 := bstep (se 1 (by rfl) ⟨1874222, by rfl⟩ : syracuseStep 2498963 = 3748445) B3748445
theorem B4751789 : Blo 1665032 4751789 := bstep (se 3 (by rfl) ⟨890960, by rfl⟩ : syracuseStep 4751789 = 1781921) B1781921
theorem B2498993 : Blo 1665032 2498993 := bstep (se 2 (by rfl) ⟨937122, by rfl⟩ : syracuseStep 2498993 = 1874245) B1874245
theorem B6087089 : Blo 1665032 6087089 := bstep (se 2 (by rfl) ⟨2282658, by rfl⟩ : syracuseStep 6087089 = 4565317) B4565317
theorem B2499011 : Blo 1665032 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B3162577 : Blo 1665032 3162577 := bstep (se 2 (by rfl) ⟨1185966, by rfl⟩ : syracuseStep 3162577 = 2371933) B2371933
theorem B2499041 : Blo 1665032 2499041 := bstep (se 2 (by rfl) ⟨937140, by rfl⟩ : syracuseStep 2499041 = 1874281) B1874281
theorem B15196643 : Blo 1665032 15196643 := bstep (se 1 (by rfl) ⟨11397482, by rfl⟩ : syracuseStep 15196643 = 22794965) B22794965
theorem B2499059 : Blo 1665032 2499059 := bstep (se 1 (by rfl) ⟨1874294, by rfl⟩ : syracuseStep 2499059 = 3748589) B3748589
theorem B2810369 : Blo 1665032 2810369 := bstep (se 2 (by rfl) ⟨1053888, by rfl⟩ : syracuseStep 2810369 = 2107777) B2107777
theorem B2499089 : Blo 1665032 2499089 := bstep (se 2 (by rfl) ⟨937158, by rfl⟩ : syracuseStep 2499089 = 1874317) B1874317
theorem B2499107 : Blo 1665032 2499107 := bstep (se 1 (by rfl) ⟨1874330, by rfl⟩ : syracuseStep 2499107 = 3748661) B3748661
theorem B2499137 : Blo 1665032 2499137 := bstep (se 2 (by rfl) ⟨937176, by rfl⟩ : syracuseStep 2499137 = 1874353) B1874353
theorem B8544845 : Blo 1665032 8544845 := bstep (se 3 (by rfl) ⟨1602158, by rfl⟩ : syracuseStep 8544845 = 3204317) B3204317
theorem B2499155 : Blo 1665032 2499155 := bstep (se 1 (by rfl) ⟨1874366, by rfl⟩ : syracuseStep 2499155 = 3748733) B3748733
theorem B2499185 : Blo 1665032 2499185 := bstep (se 2 (by rfl) ⟨937194, by rfl⟩ : syracuseStep 2499185 = 1874389) B1874389
theorem B2810497 : Blo 1665032 2810497 := bstep (se 2 (by rfl) ⟨1053936, by rfl⟩ : syracuseStep 2810497 = 2107873) B2107873
theorem B2499203 : Blo 1665032 2499203 := bstep (se 1 (by rfl) ⟨1874402, by rfl⟩ : syracuseStep 2499203 = 3748805) B3748805
theorem B2532001 : Blo 1665032 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B2810531 : Blo 1665032 2810531 := bstep (se 1 (by rfl) ⟨2107898, by rfl⟩ : syracuseStep 2810531 = 4215797) B4215797
theorem B2499233 : Blo 1665032 2499233 := bstep (se 2 (by rfl) ⟨937212, by rfl⟩ : syracuseStep 2499233 = 1874425) B1874425
theorem B2499251 : Blo 1665032 2499251 := bstep (se 1 (by rfl) ⟨1874438, by rfl⟩ : syracuseStep 2499251 = 3748877) B3748877
theorem B2499281 : Blo 1665032 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B2499299 : Blo 1665032 2499299 := bstep (se 1 (by rfl) ⟨1874474, by rfl⟩ : syracuseStep 2499299 = 3748949) B3748949
theorem B10674929 : Blo 1665032 10674929 := bstep (se 2 (by rfl) ⟨4003098, by rfl⟩ : syracuseStep 10674929 = 8006197) B8006197
theorem B2499329 : Blo 1665032 2499329 := bstep (se 2 (by rfl) ⟨937248, by rfl⟩ : syracuseStep 2499329 = 1874497) B1874497
theorem B2499347 : Blo 1665032 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B2810659 : Blo 1665032 2810659 := bstep (se 1 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 2810659 = 4215989) B4215989
theorem B2499377 : Blo 1665032 2499377 := bstep (se 2 (by rfl) ⟨937266, by rfl⟩ : syracuseStep 2499377 = 1874533) B1874533
theorem B2499395 : Blo 1665032 2499395 := bstep (se 1 (by rfl) ⟨1874546, by rfl⟩ : syracuseStep 2499395 = 3749093) B3749093
theorem B18981701 : Blo 1665032 18981701 := bstep (se 4 (by rfl) ⟨1779534, by rfl⟩ : syracuseStep 18981701 = 3559069) B3559069
theorem B2499425 : Blo 1665032 2499425 := bstep (se 2 (by rfl) ⟨937284, by rfl⟩ : syracuseStep 2499425 = 1874569) B1874569
theorem B3162979 : Blo 1665032 3162979 := bstep (se 1 (by rfl) ⟨2372234, by rfl⟩ : syracuseStep 3162979 = 4744469) B4744469
theorem B5620589 : Blo 1665032 5620589 := bstep (se 3 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 5620589 = 2107721) B2107721
theorem B2499443 : Blo 1665032 2499443 := bstep (se 1 (by rfl) ⟨1874582, by rfl⟩ : syracuseStep 2499443 = 3749165) B3749165
theorem B3163025 : Blo 1665032 3163025 := bstep (se 2 (by rfl) ⟨1186134, by rfl⟩ : syracuseStep 3163025 = 2372269) B2372269
theorem B2499473 : Blo 1665032 2499473 := bstep (se 2 (by rfl) ⟨937302, by rfl⟩ : syracuseStep 2499473 = 1874605) B1874605
theorem B5620643 : Blo 1665032 5620643 := bstep (se 1 (by rfl) ⟨4215482, by rfl⟩ : syracuseStep 5620643 = 8430965) B8430965
theorem B2499491 : Blo 1665032 2499491 := bstep (se 1 (by rfl) ⟨1874618, by rfl⟩ : syracuseStep 2499491 = 3749237) B3749237
theorem B2810801 : Blo 1665032 2810801 := bstep (se 2 (by rfl) ⟨1054050, by rfl⟩ : syracuseStep 2810801 = 2108101) B2108101
theorem B2499521 : Blo 1665032 2499521 := bstep (se 2 (by rfl) ⟨937320, by rfl⟩ : syracuseStep 2499521 = 1874641) B1874641
theorem B2499539 : Blo 1665032 2499539 := bstep (se 1 (by rfl) ⟨1874654, by rfl⟩ : syracuseStep 2499539 = 3749309) B3749309
theorem B2499569 : Blo 1665032 2499569 := bstep (se 2 (by rfl) ⟨937338, by rfl⟩ : syracuseStep 2499569 = 1874677) B1874677
theorem B2499587 : Blo 1665032 2499587 := bstep (se 1 (by rfl) ⟨1874690, by rfl⟩ : syracuseStep 2499587 = 3749381) B3749381
theorem B2499617 : Blo 1665032 2499617 := bstep (se 2 (by rfl) ⟨937356, by rfl⟩ : syracuseStep 2499617 = 1874713) B1874713
theorem B8430641 : Blo 1665032 8430641 := bstep (se 2 (by rfl) ⟨3161490, by rfl⟩ : syracuseStep 8430641 = 6322981) B6322981
theorem B2810929 : Blo 1665032 2810929 := bstep (se 2 (by rfl) ⟨1054098, by rfl⟩ : syracuseStep 2810929 = 2108197) B2108197
theorem B4744241 : Blo 1665032 4744241 := bstep (se 2 (by rfl) ⟨1779090, by rfl⟩ : syracuseStep 4744241 = 3558181) B3558181
theorem B2499635 : Blo 1665032 2499635 := bstep (se 1 (by rfl) ⟨1874726, by rfl⟩ : syracuseStep 2499635 = 3749453) B3749453
theorem B2499665 : Blo 1665032 2499665 := bstep (se 2 (by rfl) ⟨937374, by rfl⟩ : syracuseStep 2499665 = 1874749) B1874749
theorem B2810963 : Blo 1665032 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B2499683 : Blo 1665032 2499683 := bstep (se 1 (by rfl) ⟨1874762, by rfl⟩ : syracuseStep 2499683 = 3749525) B3749525
theorem B2499713 : Blo 1665032 2499713 := bstep (se 2 (by rfl) ⟨937392, by rfl⟩ : syracuseStep 2499713 = 1874785) B1874785
theorem B2499731 : Blo 1665032 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B6325411 : Blo 1665032 6325411 := bstep (se 1 (by rfl) ⟨4744058, by rfl⟩ : syracuseStep 6325411 = 9488117) B9488117
theorem B5620913 : Blo 1665032 5620913 := bstep (se 2 (by rfl) ⟨2107842, by rfl⟩ : syracuseStep 5620913 = 4215685) B4215685
theorem B3163313 : Blo 1665032 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B2499761 : Blo 1665032 2499761 := bstep (se 2 (by rfl) ⟨937410, by rfl⟩ : syracuseStep 2499761 = 1874821) B1874821
theorem B2499779 : Blo 1665032 2499779 := bstep (se 1 (by rfl) ⟨1874834, by rfl⟩ : syracuseStep 2499779 = 3749669) B3749669
theorem B2811091 : Blo 1665032 2811091 := bstep (se 1 (by rfl) ⟨2108318, by rfl⟩ : syracuseStep 2811091 = 4216637) B4216637
theorem B2811233 : Blo 1665032 2811233 := bstep (se 2 (by rfl) ⟨1054212, by rfl⟩ : syracuseStep 2811233 = 2108425) B2108425
theorem B18007409 : Blo 1665032 18007409 := bstep (se 2 (by rfl) ⟨6752778, by rfl⟩ : syracuseStep 18007409 = 13505557) B13505557
theorem B2532755 : Blo 1665032 2532755 := bstep (se 1 (by rfl) ⟨1899566, by rfl⟩ : syracuseStep 2532755 = 3799133) B3799133
theorem B6006221 : Blo 1665032 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B2811361 : Blo 1665032 2811361 := bstep (se 2 (by rfl) ⟨1054260, by rfl⟩ : syracuseStep 2811361 = 2108521) B2108521
theorem B2811395 : Blo 1665032 2811395 := bstep (se 1 (by rfl) ⟨2108546, by rfl⟩ : syracuseStep 2811395 = 4217093) B4217093
theorem B2811523 : Blo 1665032 2811523 := bstep (se 1 (by rfl) ⟨2108642, by rfl⟩ : syracuseStep 2811523 = 4217285) B4217285
theorem B1779347 : Blo 1665032 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B6751907 : Blo 1665032 6751907 := bstep (se 1 (by rfl) ⟨5063930, by rfl⟩ : syracuseStep 6751907 = 10127861) B10127861
theorem B5621453 : Blo 1665032 5621453 := bstep (se 3 (by rfl) ⟨1054022, by rfl⟩ : syracuseStep 5621453 = 2108045) B2108045
theorem B3557105 : Blo 1665032 3557105 := bstep (se 2 (by rfl) ⟨1333914, by rfl⟩ : syracuseStep 3557105 = 2667829) B2667829
theorem B5621507 : Blo 1665032 5621507 := bstep (se 1 (by rfl) ⟨4216130, by rfl⟩ : syracuseStep 5621507 = 8432261) B8432261
theorem B2811665 : Blo 1665032 2811665 := bstep (se 2 (by rfl) ⟨1054374, by rfl⟩ : syracuseStep 2811665 = 2108749) B2108749
theorem B78006037 : Blo 1665032 78006037 := bstep (se 6 (by rfl) ⟨1828266, by rfl⟩ : syracuseStep 78006037 = 3656533) B3656533
theorem B7702307 : Blo 1665032 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B14419781 : Blo 1665032 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B2811793 : Blo 1665032 2811793 := bstep (se 2 (by rfl) ⟨1054422, by rfl⟩ : syracuseStep 2811793 = 2108845) B2108845
theorem B2811827 : Blo 1665032 2811827 := bstep (se 1 (by rfl) ⟨2108870, by rfl⟩ : syracuseStep 2811827 = 4217741) B4217741
theorem B5621777 : Blo 1665032 5621777 := bstep (se 2 (by rfl) ⟨2108166, by rfl⟩ : syracuseStep 5621777 = 4216333) B4216333
theorem B1665043 : Blo 1665032 1665043 := bstep (se 1 (by rfl) ⟨1248782, by rfl⟩ : syracuseStep 1665043 = 2497565) B2497565
theorem B1665059 : Blo 1665032 1665059 := bstep (se 1 (by rfl) ⟨1248794, by rfl⟩ : syracuseStep 1665059 = 2497589) B2497589
theorem B1665075 : Blo 1665032 1665075 := bstep (se 1 (by rfl) ⟨1248806, by rfl⟩ : syracuseStep 1665075 = 2497613) B2497613
theorem B2811955 : Blo 1665032 2811955 := bstep (se 1 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 2811955 = 4217933) B4217933
theorem B1665091 : Blo 1665032 1665091 := bstep (se 1 (by rfl) ⟨1248818, by rfl⟩ : syracuseStep 1665091 = 2497637) B2497637
theorem B1665107 : Blo 1665032 1665107 := bstep (se 1 (by rfl) ⟨1248830, by rfl⟩ : syracuseStep 1665107 = 2497661) B2497661
theorem B1665123 : Blo 1665032 1665123 := bstep (se 1 (by rfl) ⟨1248842, by rfl⟩ : syracuseStep 1665123 = 2497685) B2497685
theorem B1665139 : Blo 1665032 1665139 := bstep (se 1 (by rfl) ⟨1248854, by rfl⟩ : syracuseStep 1665139 = 2497709) B2497709
theorem B1665155 : Blo 1665032 1665155 := bstep (se 1 (by rfl) ⟨1248866, by rfl⟩ : syracuseStep 1665155 = 2497733) B2497733
theorem B1665171 : Blo 1665032 1665171 := bstep (se 1 (by rfl) ⟨1248878, by rfl⟩ : syracuseStep 1665171 = 2497757) B2497757
theorem B1665187 : Blo 1665032 1665187 := bstep (se 1 (by rfl) ⟨1248890, by rfl⟩ : syracuseStep 1665187 = 2497781) B2497781
theorem B10676387 : Blo 1665032 10676387 := bstep (se 1 (by rfl) ⟨8007290, by rfl⟩ : syracuseStep 10676387 = 16014581) B16014581
theorem B1665203 : Blo 1665032 1665203 := bstep (se 1 (by rfl) ⟨1248902, by rfl⟩ : syracuseStep 1665203 = 2497805) B2497805
theorem B20269237 : Blo 1665032 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B2812097 : Blo 1665032 2812097 := bstep (se 2 (by rfl) ⟨1054536, by rfl⟩ : syracuseStep 2812097 = 2109073) B2109073
theorem B1665219 : Blo 1665032 1665219 := bstep (se 1 (by rfl) ⟨1248914, by rfl⟩ : syracuseStep 1665219 = 2497829) B2497829
theorem B1665235 : Blo 1665032 1665235 := bstep (se 1 (by rfl) ⟨1248926, by rfl⟩ : syracuseStep 1665235 = 2497853) B2497853
theorem B2533601 : Blo 1665032 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B1665251 : Blo 1665032 1665251 := bstep (se 1 (by rfl) ⟨1248938, by rfl⟩ : syracuseStep 1665251 = 2497877) B2497877
theorem B1665267 : Blo 1665032 1665267 := bstep (se 1 (by rfl) ⟨1248950, by rfl⟩ : syracuseStep 1665267 = 2497901) B2497901
theorem B1665283 : Blo 1665032 1665283 := bstep (se 1 (by rfl) ⟨1248962, by rfl⟩ : syracuseStep 1665283 = 2497925) B2497925
theorem B1665299 : Blo 1665032 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B1665315 : Blo 1665032 1665315 := bstep (se 1 (by rfl) ⟨1248986, by rfl⟩ : syracuseStep 1665315 = 2497973) B2497973
theorem B6408497 : Blo 1665032 6408497 := bstep (se 2 (by rfl) ⟨2403186, by rfl⟩ : syracuseStep 6408497 = 4806373) B4806373
theorem B1665331 : Blo 1665032 1665331 := bstep (se 1 (by rfl) ⟨1248998, by rfl⟩ : syracuseStep 1665331 = 2497997) B2497997
theorem B1665347 : Blo 1665032 1665347 := bstep (se 1 (by rfl) ⟨1249010, by rfl⟩ : syracuseStep 1665347 = 2498021) B2498021
theorem B2812225 : Blo 1665032 2812225 := bstep (se 2 (by rfl) ⟨1054584, by rfl⟩ : syracuseStep 2812225 = 2109169) B2109169
theorem B1665363 : Blo 1665032 1665363 := bstep (se 1 (by rfl) ⟨1249022, by rfl⟩ : syracuseStep 1665363 = 2498045) B2498045
theorem B1665379 : Blo 1665032 1665379 := bstep (se 1 (by rfl) ⟨1249034, by rfl⟩ : syracuseStep 1665379 = 2498069) B2498069
theorem B2812259 : Blo 1665032 2812259 := bstep (se 1 (by rfl) ⟨2109194, by rfl⟩ : syracuseStep 2812259 = 4218389) B4218389
theorem B1665395 : Blo 1665032 1665395 := bstep (se 1 (by rfl) ⟨1249046, by rfl⟩ : syracuseStep 1665395 = 2498093) B2498093
theorem B1665411 : Blo 1665032 1665411 := bstep (se 1 (by rfl) ⟨1249058, by rfl⟩ : syracuseStep 1665411 = 2498117) B2498117
theorem B1665427 : Blo 1665032 1665427 := bstep (se 1 (by rfl) ⟨1249070, by rfl⟩ : syracuseStep 1665427 = 2498141) B2498141
theorem B1665443 : Blo 1665032 1665443 := bstep (se 1 (by rfl) ⟨1249082, by rfl⟩ : syracuseStep 1665443 = 2498165) B2498165
theorem B1665459 : Blo 1665032 1665459 := bstep (se 1 (by rfl) ⟨1249094, by rfl⟩ : syracuseStep 1665459 = 2498189) B2498189
theorem B1665475 : Blo 1665032 1665475 := bstep (se 1 (by rfl) ⟨1249106, by rfl⟩ : syracuseStep 1665475 = 2498213) B2498213
theorem B1665491 : Blo 1665032 1665491 := bstep (se 1 (by rfl) ⟨1249118, by rfl⟩ : syracuseStep 1665491 = 2498237) B2498237
theorem B1665507 : Blo 1665032 1665507 := bstep (se 1 (by rfl) ⟨1249130, by rfl⟩ : syracuseStep 1665507 = 2498261) B2498261
theorem B8432099 : Blo 1665032 8432099 := bstep (se 1 (by rfl) ⟨6324074, by rfl⟩ : syracuseStep 8432099 = 12648149) B12648149
theorem B4745699 : Blo 1665032 4745699 := bstep (se 1 (by rfl) ⟨3559274, by rfl⟩ : syracuseStep 4745699 = 7118549) B7118549
theorem B1665523 : Blo 1665032 1665523 := bstep (se 1 (by rfl) ⟨1249142, by rfl⟩ : syracuseStep 1665523 = 2498285) B2498285
theorem B1665539 : Blo 1665032 1665539 := bstep (se 1 (by rfl) ⟨1249154, by rfl⟩ : syracuseStep 1665539 = 2498309) B2498309
theorem B1665555 : Blo 1665032 1665555 := bstep (se 1 (by rfl) ⟨1249166, by rfl⟩ : syracuseStep 1665555 = 2498333) B2498333
theorem B3746339 : Blo 1665032 3746339 := bstep (se 1 (by rfl) ⟨2809754, by rfl⟩ : syracuseStep 3746339 = 5619509) B5619509
theorem B2107939 : Blo 1665032 2107939 := bstep (se 1 (by rfl) ⟨1580954, by rfl⟩ : syracuseStep 2107939 = 3161909) B3161909
theorem B1665571 : Blo 1665032 1665571 := bstep (se 1 (by rfl) ⟨1249178, by rfl⟩ : syracuseStep 1665571 = 2498357) B2498357
theorem B5622317 : Blo 1665032 5622317 := bstep (se 3 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 5622317 = 2108369) B2108369
theorem B1665587 : Blo 1665032 1665587 := bstep (se 1 (by rfl) ⟨1249190, by rfl⟩ : syracuseStep 1665587 = 2498381) B2498381
theorem B1665603 : Blo 1665032 1665603 := bstep (se 1 (by rfl) ⟨1249202, by rfl⟩ : syracuseStep 1665603 = 2498405) B2498405
theorem B1665619 : Blo 1665032 1665619 := bstep (se 1 (by rfl) ⟨1249214, by rfl⟩ : syracuseStep 1665619 = 2498429) B2498429
theorem B1665635 : Blo 1665032 1665635 := bstep (se 1 (by rfl) ⟨1249226, by rfl⟩ : syracuseStep 1665635 = 2498453) B2498453
theorem B5622371 : Blo 1665032 5622371 := bstep (se 1 (by rfl) ⟨4216778, by rfl⟩ : syracuseStep 5622371 = 8433557) B8433557
theorem B1665651 : Blo 1665032 1665651 := bstep (se 1 (by rfl) ⟨1249238, by rfl⟩ : syracuseStep 1665651 = 2498477) B2498477
theorem B2108035 : Blo 1665032 2108035 := bstep (se 1 (by rfl) ⟨1581026, by rfl⟩ : syracuseStep 2108035 = 3162053) B3162053
theorem B1665667 : Blo 1665032 1665667 := bstep (se 1 (by rfl) ⟨1249250, by rfl⟩ : syracuseStep 1665667 = 2498501) B2498501
theorem B1665683 : Blo 1665032 1665683 := bstep (se 1 (by rfl) ⟨1249262, by rfl⟩ : syracuseStep 1665683 = 2498525) B2498525
theorem B1665699 : Blo 1665032 1665699 := bstep (se 1 (by rfl) ⟨1249274, by rfl⟩ : syracuseStep 1665699 = 2498549) B2498549
theorem B1665715 : Blo 1665032 1665715 := bstep (se 1 (by rfl) ⟨1249286, by rfl⟩ : syracuseStep 1665715 = 2498573) B2498573
theorem B1665731 : Blo 1665032 1665731 := bstep (se 1 (by rfl) ⟨1249298, by rfl⟩ : syracuseStep 1665731 = 2498597) B2498597
theorem B1665747 : Blo 1665032 1665747 := bstep (se 1 (by rfl) ⟨1249310, by rfl⟩ : syracuseStep 1665747 = 2498621) B2498621
theorem B1665763 : Blo 1665032 1665763 := bstep (se 1 (by rfl) ⟨1249322, by rfl⟩ : syracuseStep 1665763 = 2498645) B2498645
theorem B1665779 : Blo 1665032 1665779 := bstep (se 1 (by rfl) ⟨1249334, by rfl⟩ : syracuseStep 1665779 = 2498669) B2498669
theorem B1665795 : Blo 1665032 1665795 := bstep (se 1 (by rfl) ⟨1249346, by rfl⟩ : syracuseStep 1665795 = 2498693) B2498693
theorem B1665811 : Blo 1665032 1665811 := bstep (se 1 (by rfl) ⟨1249358, by rfl⟩ : syracuseStep 1665811 = 2498717) B2498717
theorem B1665827 : Blo 1665032 1665827 := bstep (se 1 (by rfl) ⟨1249370, by rfl⟩ : syracuseStep 1665827 = 2498741) B2498741
theorem B3746609 : Blo 1665032 3746609 := bstep (se 2 (by rfl) ⟨1404978, by rfl⟩ : syracuseStep 3746609 = 2809957) B2809957
theorem B1665843 : Blo 1665032 1665843 := bstep (se 1 (by rfl) ⟨1249382, by rfl⟩ : syracuseStep 1665843 = 2498765) B2498765
theorem B3746627 : Blo 1665032 3746627 := bstep (se 1 (by rfl) ⟨2809970, by rfl⟩ : syracuseStep 3746627 = 5619941) B5619941
theorem B1665859 : Blo 1665032 1665859 := bstep (se 1 (by rfl) ⟨1249394, by rfl⟩ : syracuseStep 1665859 = 2498789) B2498789
theorem B1665875 : Blo 1665032 1665875 := bstep (se 1 (by rfl) ⟨1249406, by rfl⟩ : syracuseStep 1665875 = 2498813) B2498813
theorem B1665891 : Blo 1665032 1665891 := bstep (se 1 (by rfl) ⟨1249418, by rfl⟩ : syracuseStep 1665891 = 2498837) B2498837
theorem B5622641 : Blo 1665032 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B1665907 : Blo 1665032 1665907 := bstep (se 1 (by rfl) ⟨1249430, by rfl⟩ : syracuseStep 1665907 = 2498861) B2498861
theorem B5557123 : Blo 1665032 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B1665923 : Blo 1665032 1665923 := bstep (se 1 (by rfl) ⟨1249442, by rfl⟩ : syracuseStep 1665923 = 2498885) B2498885
theorem B1665939 : Blo 1665032 1665939 := bstep (se 1 (by rfl) ⟨1249454, by rfl⟩ : syracuseStep 1665939 = 2498909) B2498909
theorem B1665955 : Blo 1665032 1665955 := bstep (se 1 (by rfl) ⟨1249466, by rfl⟩ : syracuseStep 1665955 = 2498933) B2498933
theorem B1665971 : Blo 1665032 1665971 := bstep (se 1 (by rfl) ⟨1249478, by rfl⟩ : syracuseStep 1665971 = 2498957) B2498957
theorem B5409731 : Blo 1665032 5409731 := bstep (se 1 (by rfl) ⟨4057298, by rfl⟩ : syracuseStep 5409731 = 8114597) B8114597
theorem B1665987 : Blo 1665032 1665987 := bstep (se 1 (by rfl) ⟨1249490, by rfl⟩ : syracuseStep 1665987 = 2498981) B2498981
theorem B1666003 : Blo 1665032 1666003 := bstep (se 1 (by rfl) ⟨1249502, by rfl⟩ : syracuseStep 1666003 = 2499005) B2499005
theorem B1666019 : Blo 1665032 1666019 := bstep (se 1 (by rfl) ⟨1249514, by rfl⟩ : syracuseStep 1666019 = 2499029) B2499029
theorem B1666035 : Blo 1665032 1666035 := bstep (se 1 (by rfl) ⟨1249526, by rfl⟩ : syracuseStep 1666035 = 2499053) B2499053
theorem B1666051 : Blo 1665032 1666051 := bstep (se 1 (by rfl) ⟨1249538, by rfl⟩ : syracuseStep 1666051 = 2499077) B2499077
theorem B1666067 : Blo 1665032 1666067 := bstep (se 1 (by rfl) ⟨1249550, by rfl⟩ : syracuseStep 1666067 = 2499101) B2499101
theorem B1666083 : Blo 1665032 1666083 := bstep (se 1 (by rfl) ⟨1249562, by rfl⟩ : syracuseStep 1666083 = 2499125) B2499125
theorem B1666099 : Blo 1665032 1666099 := bstep (se 1 (by rfl) ⟨1249574, by rfl⟩ : syracuseStep 1666099 = 2499149) B2499149
theorem B1666115 : Blo 1665032 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B15199301 : Blo 1665032 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B3746897 : Blo 1665032 3746897 := bstep (se 2 (by rfl) ⟨1405086, by rfl⟩ : syracuseStep 3746897 = 2810173) B2810173
theorem B1666131 : Blo 1665032 1666131 := bstep (se 1 (by rfl) ⟨1249598, by rfl⟩ : syracuseStep 1666131 = 2499197) B2499197
theorem B3746915 : Blo 1665032 3746915 := bstep (se 1 (by rfl) ⟨2810186, by rfl⟩ : syracuseStep 3746915 = 5620373) B5620373
theorem B1666147 : Blo 1665032 1666147 := bstep (se 1 (by rfl) ⟨1249610, by rfl⟩ : syracuseStep 1666147 = 2499221) B2499221
theorem B3206243 : Blo 1665032 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B2108531 : Blo 1665032 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B1666163 : Blo 1665032 1666163 := bstep (se 1 (by rfl) ⟨1249622, by rfl⟩ : syracuseStep 1666163 = 2499245) B2499245
theorem B1666179 : Blo 1665032 1666179 := bstep (se 1 (by rfl) ⟨1249634, by rfl⟩ : syracuseStep 1666179 = 2499269) B2499269
theorem B6843533 : Blo 1665032 6843533 := bstep (se 3 (by rfl) ⟨1283162, by rfl⟩ : syracuseStep 6843533 = 2566325) B2566325
theorem B1666195 : Blo 1665032 1666195 := bstep (se 1 (by rfl) ⟨1249646, by rfl⟩ : syracuseStep 1666195 = 2499293) B2499293
theorem B1666211 : Blo 1665032 1666211 := bstep (se 1 (by rfl) ⟨1249658, by rfl⟩ : syracuseStep 1666211 = 2499317) B2499317
theorem B1666227 : Blo 1665032 1666227 := bstep (se 1 (by rfl) ⟨1249670, by rfl⟩ : syracuseStep 1666227 = 2499341) B2499341
theorem B1666243 : Blo 1665032 1666243 := bstep (se 1 (by rfl) ⟨1249682, by rfl⟩ : syracuseStep 1666243 = 2499365) B2499365
theorem B3001553 : Blo 1665032 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B5336273 : Blo 1665032 5336273 := bstep (se 2 (by rfl) ⟨2001102, by rfl⟩ : syracuseStep 5336273 = 4002205) B4002205
theorem B1666259 : Blo 1665032 1666259 := bstep (se 1 (by rfl) ⟨1249694, by rfl⟩ : syracuseStep 1666259 = 2499389) B2499389
theorem B1666275 : Blo 1665032 1666275 := bstep (se 1 (by rfl) ⟨1249706, by rfl⟩ : syracuseStep 1666275 = 2499413) B2499413
theorem B6589667 : Blo 1665032 6589667 := bstep (se 1 (by rfl) ⟨4942250, by rfl⟩ : syracuseStep 6589667 = 9884501) B9884501
theorem B1666291 : Blo 1665032 1666291 := bstep (se 1 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 1666291 = 2499437) B2499437
theorem B3558659 : Blo 1665032 3558659 := bstep (se 1 (by rfl) ⟨2668994, by rfl⟩ : syracuseStep 3558659 = 5337989) B5337989
theorem B1666307 : Blo 1665032 1666307 := bstep (se 1 (by rfl) ⟨1249730, by rfl⟩ : syracuseStep 1666307 = 2499461) B2499461
theorem B8432909 : Blo 1665032 8432909 := bstep (se 3 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 8432909 = 3162341) B3162341
theorem B1666323 : Blo 1665032 1666323 := bstep (se 1 (by rfl) ⟨1249742, by rfl⟩ : syracuseStep 1666323 = 2499485) B2499485
theorem B1666339 : Blo 1665032 1666339 := bstep (se 1 (by rfl) ⟨1249754, by rfl⟩ : syracuseStep 1666339 = 2499509) B2499509
theorem B1666355 : Blo 1665032 1666355 := bstep (se 1 (by rfl) ⟨1249766, by rfl⟩ : syracuseStep 1666355 = 2499533) B2499533
theorem B1666371 : Blo 1665032 1666371 := bstep (se 1 (by rfl) ⟨1249778, by rfl⟩ : syracuseStep 1666371 = 2499557) B2499557
theorem B5336401 : Blo 1665032 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B1666387 : Blo 1665032 1666387 := bstep (se 1 (by rfl) ⟨1249790, by rfl⟩ : syracuseStep 1666387 = 2499581) B2499581
theorem B1666403 : Blo 1665032 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B3747185 : Blo 1665032 3747185 := bstep (se 2 (by rfl) ⟨1405194, by rfl⟩ : syracuseStep 3747185 = 2810389) B2810389
theorem B1666419 : Blo 1665032 1666419 := bstep (se 1 (by rfl) ⟨1249814, by rfl⟩ : syracuseStep 1666419 = 2499629) B2499629
theorem B3747203 : Blo 1665032 3747203 := bstep (se 1 (by rfl) ⟨2810402, by rfl⟩ : syracuseStep 3747203 = 5620805) B5620805
theorem B1666435 : Blo 1665032 1666435 := bstep (se 1 (by rfl) ⟨1249826, by rfl⟩ : syracuseStep 1666435 = 2499653) B2499653
theorem B18009485 : Blo 1665032 18009485 := bstep (se 3 (by rfl) ⟨3376778, by rfl⟩ : syracuseStep 18009485 = 6753557) B6753557
theorem B5623181 : Blo 1665032 5623181 := bstep (se 3 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 5623181 = 2108693) B2108693
theorem B1666451 : Blo 1665032 1666451 := bstep (se 1 (by rfl) ⟨1249838, by rfl⟩ : syracuseStep 1666451 = 2499677) B2499677
theorem B1666467 : Blo 1665032 1666467 := bstep (se 1 (by rfl) ⟨1249850, by rfl⟩ : syracuseStep 1666467 = 2499701) B2499701
theorem B1666483 : Blo 1665032 1666483 := bstep (se 1 (by rfl) ⟨1249862, by rfl⟩ : syracuseStep 1666483 = 2499725) B2499725
theorem B5623235 : Blo 1665032 5623235 := bstep (se 1 (by rfl) ⟨4217426, by rfl⟩ : syracuseStep 5623235 = 8434853) B8434853
theorem B1666499 : Blo 1665032 1666499 := bstep (se 1 (by rfl) ⟨1249874, by rfl⟩ : syracuseStep 1666499 = 2499749) B2499749
theorem B2371027 : Blo 1665032 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1666515 : Blo 1665032 1666515 := bstep (se 1 (by rfl) ⟨1249886, by rfl⟩ : syracuseStep 1666515 = 2499773) B2499773
theorem B1666531 : Blo 1665032 1666531 := bstep (se 1 (by rfl) ⟨1249898, by rfl⟩ : syracuseStep 1666531 = 2499797) B2499797
theorem B5336657 : Blo 1665032 5336657 := bstep (se 2 (by rfl) ⟨2001246, by rfl⟩ : syracuseStep 5336657 = 4002493) B4002493
theorem B24333965 : Blo 1665032 24333965 := bstep (se 3 (by rfl) ⟨4562618, by rfl⟩ : syracuseStep 24333965 = 9125237) B9125237
theorem B3747473 : Blo 1665032 3747473 := bstep (se 2 (by rfl) ⟨1405302, by rfl⟩ : syracuseStep 3747473 = 2810605) B2810605
theorem B3747491 : Blo 1665032 3747491 := bstep (se 1 (by rfl) ⟨2810618, by rfl⟩ : syracuseStep 3747491 = 5621237) B5621237
theorem B11398819 : Blo 1665032 11398819 := bstep (se 1 (by rfl) ⟨8549114, by rfl⟩ : syracuseStep 11398819 = 17098229) B17098229
theorem B5623505 : Blo 1665032 5623505 := bstep (se 2 (by rfl) ⟨2108814, by rfl⟩ : syracuseStep 5623505 = 4217629) B4217629
theorem B4501325 : Blo 1665032 4501325 := bstep (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) B1687997
theorem B7597901 : Blo 1665032 7597901 := bstep (se 3 (by rfl) ⟨1424606, by rfl⟩ : syracuseStep 7597901 = 2849213) B2849213
theorem B3747761 : Blo 1665032 3747761 := bstep (se 2 (by rfl) ⟨1405410, by rfl⟩ : syracuseStep 3747761 = 2810821) B2810821
theorem B3747779 : Blo 1665032 3747779 := bstep (se 1 (by rfl) ⟨2810834, by rfl⟩ : syracuseStep 3747779 = 5621669) B5621669
theorem B4501507 : Blo 1665032 4501507 := bstep (se 1 (by rfl) ⟨3376130, by rfl⟩ : syracuseStep 4501507 = 6752261) B6752261
theorem B5697539 : Blo 1665032 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B3748049 : Blo 1665032 3748049 := bstep (se 2 (by rfl) ⟨1405518, by rfl⟩ : syracuseStep 3748049 = 2811037) B2811037
theorem B7114979 : Blo 1665032 7114979 := bstep (se 1 (by rfl) ⟨5336234, by rfl⟩ : syracuseStep 7114979 = 10672469) B10672469
theorem B3748067 : Blo 1665032 3748067 := bstep (se 1 (by rfl) ⟨2811050, by rfl⟩ : syracuseStep 3748067 = 5622101) B5622101
theorem B5624045 : Blo 1665032 5624045 := bstep (se 3 (by rfl) ⟨1054508, by rfl⟩ : syracuseStep 5624045 = 2109017) B2109017
theorem B6754595 : Blo 1665032 6754595 := bstep (se 1 (by rfl) ⟨5065946, by rfl⟩ : syracuseStep 6754595 = 10131893) B10131893
theorem B5624099 : Blo 1665032 5624099 := bstep (se 1 (by rfl) ⟨4218074, by rfl⟩ : syracuseStep 5624099 = 8436149) B8436149
theorem B153817541 : Blo 1665032 153817541 := bstep (se 4 (by rfl) ⟨14420394, by rfl⟩ : syracuseStep 153817541 = 28840789) B28840789
theorem B3748337 : Blo 1665032 3748337 := bstep (se 2 (by rfl) ⟨1405626, by rfl⟩ : syracuseStep 3748337 = 2811253) B2811253
theorem B3748355 : Blo 1665032 3748355 := bstep (se 1 (by rfl) ⟨2811266, by rfl⟩ : syracuseStep 3748355 = 5622533) B5622533
theorem B5624369 : Blo 1665032 5624369 := bstep (se 2 (by rfl) ⟨2109138, by rfl⟩ : syracuseStep 5624369 = 4218277) B4218277
theorem B2372161 : Blo 1665032 2372161 := bstep (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) B1779121
theorem B2372257 : Blo 1665032 2372257 := bstep (se 2 (by rfl) ⟨889596, by rfl⟩ : syracuseStep 2372257 = 1779193) B1779193
theorem B4215473 : Blo 1665032 4215473 := bstep (se 2 (by rfl) ⟨1580802, by rfl⟩ : syracuseStep 4215473 = 3161605) B3161605
theorem B4215523 : Blo 1665032 4215523 := bstep (se 1 (by rfl) ⟨3161642, by rfl⟩ : syracuseStep 4215523 = 6323285) B6323285
theorem B9482993 : Blo 1665032 9482993 := bstep (se 2 (by rfl) ⟨3556122, by rfl⟩ : syracuseStep 9482993 = 7112245) B7112245
theorem B3748625 : Blo 1665032 3748625 := bstep (se 2 (by rfl) ⟨1405734, by rfl⟩ : syracuseStep 3748625 = 2811469) B2811469
theorem B3748643 : Blo 1665032 3748643 := bstep (se 1 (by rfl) ⟨2811482, by rfl⟩ : syracuseStep 3748643 = 5622965) B5622965
theorem B12645233 : Blo 1665032 12645233 := bstep (se 2 (by rfl) ⟨4741962, by rfl⟩ : syracuseStep 12645233 = 9483925) B9483925
theorem B4215665 : Blo 1665032 4215665 := bstep (se 2 (by rfl) ⟨1580874, by rfl⟩ : syracuseStep 4215665 = 3161749) B3161749
theorem B3748913 : Blo 1665032 3748913 := bstep (se 2 (by rfl) ⟨1405842, by rfl⟩ : syracuseStep 3748913 = 2811685) B2811685
theorem B3748931 : Blo 1665032 3748931 := bstep (se 1 (by rfl) ⟨2811698, by rfl⟩ : syracuseStep 3748931 = 5623397) B5623397
theorem B5698673 : Blo 1665032 5698673 := bstep (se 2 (by rfl) ⟨2137002, by rfl⟩ : syracuseStep 5698673 = 4274005) B4274005
theorem B2372753 : Blo 1665032 2372753 := bstep (se 2 (by rfl) ⟨889782, by rfl⟩ : syracuseStep 2372753 = 1779565) B1779565
theorem B2667713 : Blo 1665032 2667713 := bstep (se 2 (by rfl) ⟨1000392, by rfl⟩ : syracuseStep 2667713 = 2000785) B2000785
theorem B7214285 : Blo 1665032 7214285 := bstep (se 3 (by rfl) ⟨1352678, by rfl⟩ : syracuseStep 7214285 = 2705357) B2705357
theorem B5338349 : Blo 1665032 5338349 := bstep (se 3 (by rfl) ⟨1000940, by rfl⟩ : syracuseStep 5338349 = 2001881) B2001881
theorem B10671365 : Blo 1665032 10671365 := bstep (se 4 (by rfl) ⟨1000440, by rfl⟩ : syracuseStep 10671365 = 2000881) B2000881
theorem B1873219 : Blo 1665032 1873219 := bstep (se 1 (by rfl) ⟨1404914, by rfl⟩ : syracuseStep 1873219 = 2809829) B2809829
theorem B3749201 : Blo 1665032 3749201 := bstep (se 2 (by rfl) ⟨1405950, by rfl⟩ : syracuseStep 3749201 = 2811901) B2811901
theorem B3749219 : Blo 1665032 3749219 := bstep (se 1 (by rfl) ⟨2811914, by rfl⟩ : syracuseStep 3749219 = 5623829) B5623829
theorem B4502915 : Blo 1665032 4502915 := bstep (se 1 (by rfl) ⟨3377186, by rfl⟩ : syracuseStep 4502915 = 6754373) B6754373
theorem B2028979 : Blo 1665032 2028979 := bstep (se 1 (by rfl) ⟨1521734, by rfl⟩ : syracuseStep 2028979 = 3043469) B3043469
theorem B18970037 : Blo 1665032 18970037 := bstep (se 5 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 18970037 = 1778441) B1778441
theorem B1873363 : Blo 1665032 1873363 := bstep (se 1 (by rfl) ⟨1405022, by rfl⟩ : syracuseStep 1873363 = 2810045) B2810045
theorem B2848241 : Blo 1665032 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B1873507 : Blo 1665032 1873507 := bstep (se 1 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 1873507 = 2810261) B2810261
theorem B3749489 : Blo 1665032 3749489 := bstep (se 2 (by rfl) ⟨1406058, by rfl⟩ : syracuseStep 3749489 = 2812117) B2812117
theorem B3749507 : Blo 1665032 3749507 := bstep (se 1 (by rfl) ⟨2812130, by rfl⟩ : syracuseStep 3749507 = 5624261) B5624261
theorem B1873651 : Blo 1665032 1873651 := bstep (se 1 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 1873651 = 2810477) B2810477
theorem B2029331 : Blo 1665032 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B6412081 : Blo 1665032 6412081 := bstep (se 2 (by rfl) ⟨2404530, by rfl⟩ : syracuseStep 6412081 = 4809061) B4809061
theorem B4216657 : Blo 1665032 4216657 := bstep (se 2 (by rfl) ⟨1581246, by rfl⟩ : syracuseStep 4216657 = 3162493) B3162493
theorem B6002531 : Blo 1665032 6002531 := bstep (se 1 (by rfl) ⟨4501898, by rfl⟩ : syracuseStep 6002531 = 9003797) B9003797
theorem B2848625 : Blo 1665032 2848625 := bstep (se 2 (by rfl) ⟨1068234, by rfl⟩ : syracuseStep 2848625 = 2136469) B2136469
theorem B1873795 : Blo 1665032 1873795 := bstep (se 1 (by rfl) ⟨1405346, by rfl⟩ : syracuseStep 1873795 = 2810693) B2810693
theorem B2668547 : Blo 1665032 2668547 := bstep (se 1 (by rfl) ⟨2001410, by rfl⟩ : syracuseStep 2668547 = 4002821) B4002821
theorem B1873939 : Blo 1665032 1873939 := bstep (se 1 (by rfl) ⟨1405454, by rfl⟩ : syracuseStep 1873939 = 2810909) B2810909
theorem B4216931 : Blo 1665032 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B8435825 : Blo 1665032 8435825 := bstep (se 2 (by rfl) ⟨3163434, by rfl⟩ : syracuseStep 8435825 = 6326869) B6326869
theorem B9484451 : Blo 1665032 9484451 := bstep (se 1 (by rfl) ⟨7113338, by rfl⟩ : syracuseStep 9484451 = 14226677) B14226677
theorem B1874083 : Blo 1665032 1874083 := bstep (se 1 (by rfl) ⟨1405562, by rfl⟩ : syracuseStep 1874083 = 2811125) B2811125
theorem B7116977 : Blo 1665032 7116977 := bstep (se 2 (by rfl) ⟨2668866, by rfl⟩ : syracuseStep 7116977 = 5337733) B5337733
theorem B4217123 : Blo 1665032 4217123 := bstep (se 1 (by rfl) ⟨3162842, by rfl⟩ : syracuseStep 4217123 = 6325685) B6325685
theorem B2668835 : Blo 1665032 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B6322481 : Blo 1665032 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B1874227 : Blo 1665032 1874227 := bstep (se 1 (by rfl) ⟨1405670, by rfl⟩ : syracuseStep 1874227 = 2811341) B2811341
theorem B4741507 : Blo 1665032 4741507 := bstep (se 1 (by rfl) ⟨3556130, by rfl⟩ : syracuseStep 4741507 = 7112261) B7112261
theorem B4741553 : Blo 1665032 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B1874371 : Blo 1665032 1874371 := bstep (se 1 (by rfl) ⟨1405778, by rfl⟩ : syracuseStep 1874371 = 2811557) B2811557
theorem B2849267 : Blo 1665032 2849267 := bstep (se 1 (by rfl) ⟨2136950, by rfl⟩ : syracuseStep 2849267 = 4273901) B4273901
theorem B2669059 : Blo 1665032 2669059 := bstep (se 1 (by rfl) ⟨2001794, by rfl⟩ : syracuseStep 2669059 = 4003589) B4003589
theorem B1874515 : Blo 1665032 1874515 := bstep (se 1 (by rfl) ⟨1405886, by rfl⟩ : syracuseStep 1874515 = 2811773) B2811773
theorem B9124493 : Blo 1665032 9124493 := bstep (se 3 (by rfl) ⟨1710842, by rfl⟩ : syracuseStep 9124493 = 3421685) B3421685
theorem B1874659 : Blo 1665032 1874659 := bstep (se 1 (by rfl) ⟨1405994, by rfl⟩ : syracuseStep 1874659 = 2811989) B2811989
theorem B21355235 : Blo 1665032 21355235 := bstep (se 1 (by rfl) ⟨16016426, by rfl⟩ : syracuseStep 21355235 = 32032853) B32032853
theorem B6847217 : Blo 1665032 6847217 := bstep (se 2 (by rfl) ⟨2567706, by rfl⟩ : syracuseStep 6847217 = 5135413) B5135413
theorem B2849555 : Blo 1665032 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B1874803 : Blo 1665032 1874803 := bstep (se 1 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 1874803 = 2812205) B2812205
theorem B5700493 : Blo 1665032 5700493 := bstep (se 3 (by rfl) ⟨1068842, by rfl⟩ : syracuseStep 5700493 = 2137685) B2137685
theorem B6167501 : Blo 1665032 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B6003725 : Blo 1665032 6003725 := bstep (se 3 (by rfl) ⟨1125698, by rfl⟩ : syracuseStep 6003725 = 2251397) B2251397
theorem B2497553 : Blo 1665032 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B2497571 : Blo 1665032 2497571 := bstep (se 1 (by rfl) ⟨1873178, by rfl⟩ : syracuseStep 2497571 = 3746357) B3746357
theorem B2497601 : Blo 1665032 2497601 := bstep (se 2 (by rfl) ⟨936600, by rfl⟩ : syracuseStep 2497601 = 1873201) B1873201
theorem B7117901 : Blo 1665032 7117901 := bstep (se 3 (by rfl) ⟨1334606, by rfl⟩ : syracuseStep 7117901 = 2669213) B2669213
theorem B2497619 : Blo 1665032 2497619 := bstep (se 1 (by rfl) ⟨1873214, by rfl⟩ : syracuseStep 2497619 = 3746429) B3746429
theorem B2497649 : Blo 1665032 2497649 := bstep (se 2 (by rfl) ⟨936618, by rfl⟩ : syracuseStep 2497649 = 1873237) B1873237
theorem B2497667 : Blo 1665032 2497667 := bstep (se 1 (by rfl) ⟨1873250, by rfl⟩ : syracuseStep 2497667 = 3746501) B3746501
theorem B2497697 : Blo 1665032 2497697 := bstep (se 2 (by rfl) ⟨936636, by rfl⟩ : syracuseStep 2497697 = 1873273) B1873273
theorem B4807853 : Blo 1665032 4807853 := bstep (se 3 (by rfl) ⟨901472, by rfl⟩ : syracuseStep 4807853 = 1802945) B1802945
theorem B2497715 : Blo 1665032 2497715 := bstep (se 1 (by rfl) ⟨1873286, by rfl⟩ : syracuseStep 2497715 = 3746573) B3746573
theorem B2497745 : Blo 1665032 2497745 := bstep (se 2 (by rfl) ⟨936654, by rfl⟩ : syracuseStep 2497745 = 1873309) B1873309
theorem B4218065 : Blo 1665032 4218065 := bstep (se 2 (by rfl) ⟨1581774, by rfl⟩ : syracuseStep 4218065 = 3163549) B3163549
theorem B2497763 : Blo 1665032 2497763 := bstep (se 1 (by rfl) ⟨1873322, by rfl⟩ : syracuseStep 2497763 = 3746645) B3746645
theorem B2497793 : Blo 1665032 2497793 := bstep (se 2 (by rfl) ⟨936672, by rfl⟩ : syracuseStep 2497793 = 1873345) B1873345
theorem B4218115 : Blo 1665032 4218115 := bstep (se 1 (by rfl) ⟨3163586, by rfl⟩ : syracuseStep 4218115 = 6327173) B6327173
theorem B2497811 : Blo 1665032 2497811 := bstep (se 1 (by rfl) ⟨1873358, by rfl⟩ : syracuseStep 2497811 = 3746717) B3746717
theorem B2850083 : Blo 1665032 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B2497841 : Blo 1665032 2497841 := bstep (se 2 (by rfl) ⟨936690, by rfl⟩ : syracuseStep 2497841 = 1873381) B1873381
theorem B2497859 : Blo 1665032 2497859 := bstep (se 1 (by rfl) ⟨1873394, by rfl⟩ : syracuseStep 2497859 = 3746789) B3746789
theorem B2497889 : Blo 1665032 2497889 := bstep (se 2 (by rfl) ⟨936708, by rfl⟩ : syracuseStep 2497889 = 1873417) B1873417
theorem B2497907 : Blo 1665032 2497907 := bstep (se 1 (by rfl) ⟨1873430, by rfl⟩ : syracuseStep 2497907 = 3746861) B3746861
theorem B2497937 : Blo 1665032 2497937 := bstep (se 2 (by rfl) ⟨936726, by rfl⟩ : syracuseStep 2497937 = 1873453) B1873453
theorem B4218257 : Blo 1665032 4218257 := bstep (se 2 (by rfl) ⟨1581846, by rfl⟩ : syracuseStep 4218257 = 3163693) B3163693
theorem B2497955 : Blo 1665032 2497955 := bstep (se 1 (by rfl) ⟨1873466, by rfl⟩ : syracuseStep 2497955 = 3746933) B3746933
theorem B3161521 : Blo 1665032 3161521 := bstep (se 2 (by rfl) ⟨1185570, by rfl⟩ : syracuseStep 3161521 = 2371141) B2371141
theorem B2497985 : Blo 1665032 2497985 := bstep (se 2 (by rfl) ⟨936744, by rfl⟩ : syracuseStep 2497985 = 1873489) B1873489
theorem B2498003 : Blo 1665032 2498003 := bstep (se 1 (by rfl) ⟨1873502, by rfl⟩ : syracuseStep 2498003 = 3747005) B3747005
theorem B2498033 : Blo 1665032 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B2498051 : Blo 1665032 2498051 := bstep (se 1 (by rfl) ⟨1873538, by rfl⟩ : syracuseStep 2498051 = 3747077) B3747077
theorem B2498081 : Blo 1665032 2498081 := bstep (se 2 (by rfl) ⟨936780, by rfl⟩ : syracuseStep 2498081 = 1873561) B1873561
theorem B2498099 : Blo 1665032 2498099 := bstep (se 1 (by rfl) ⟨1873574, by rfl⟩ : syracuseStep 2498099 = 3747149) B3747149
theorem B2498129 : Blo 1665032 2498129 := bstep (se 2 (by rfl) ⟨936798, by rfl⟩ : syracuseStep 2498129 = 1873597) B1873597
theorem B2498147 : Blo 1665032 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B2498177 : Blo 1665032 2498177 := bstep (se 2 (by rfl) ⟨936816, by rfl⟩ : syracuseStep 2498177 = 1873633) B1873633
theorem B4808323 : Blo 1665032 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B2498195 : Blo 1665032 2498195 := bstep (se 1 (by rfl) ⟨1873646, by rfl⟩ : syracuseStep 2498195 = 3747293) B3747293
theorem B2498225 : Blo 1665032 2498225 := bstep (se 2 (by rfl) ⟨936834, by rfl⟩ : syracuseStep 2498225 = 1873669) B1873669
theorem B2498243 : Blo 1665032 2498243 := bstep (se 1 (by rfl) ⟨1873682, by rfl⟩ : syracuseStep 2498243 = 3747365) B3747365
theorem B2498273 : Blo 1665032 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B6323939 : Blo 1665032 6323939 := bstep (se 1 (by rfl) ⟨4742954, by rfl⟩ : syracuseStep 6323939 = 9485909) B9485909
theorem B5775089 : Blo 1665032 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B6323953 : Blo 1665032 6323953 := bstep (se 2 (by rfl) ⟨2371482, by rfl⟩ : syracuseStep 6323953 = 4742965) B4742965
theorem B2498291 : Blo 1665032 2498291 := bstep (se 1 (by rfl) ⟨1873718, by rfl⟩ : syracuseStep 2498291 = 3747437) B3747437
theorem B2498321 : Blo 1665032 2498321 := bstep (se 2 (by rfl) ⟨936870, by rfl⟩ : syracuseStep 2498321 = 1873741) B1873741
theorem B2498339 : Blo 1665032 2498339 := bstep (se 1 (by rfl) ⟨1873754, by rfl⟩ : syracuseStep 2498339 = 3747509) B3747509
theorem B2498369 : Blo 1665032 2498369 := bstep (se 2 (by rfl) ⟨936888, by rfl⟩ : syracuseStep 2498369 = 1873777) B1873777
theorem B2498387 : Blo 1665032 2498387 := bstep (se 1 (by rfl) ⟨1873790, by rfl⟩ : syracuseStep 2498387 = 3747581) B3747581
theorem B4743011 : Blo 1665032 4743011 := bstep (se 1 (by rfl) ⟨3557258, by rfl⟩ : syracuseStep 4743011 = 7114517) B7114517
theorem B2498417 : Blo 1665032 2498417 := bstep (se 2 (by rfl) ⟨936906, by rfl⟩ : syracuseStep 2498417 = 1873813) B1873813
theorem B2498435 : Blo 1665032 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B2498465 : Blo 1665032 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B2498483 : Blo 1665032 2498483 := bstep (se 1 (by rfl) ⟨1873862, by rfl⟩ : syracuseStep 2498483 = 3747725) B3747725
theorem B2809795 : Blo 1665032 2809795 := bstep (se 1 (by rfl) ⟨2107346, by rfl⟩ : syracuseStep 2809795 = 4214693) B4214693
theorem B2498513 : Blo 1665032 2498513 := bstep (se 2 (by rfl) ⟨936942, by rfl⟩ : syracuseStep 2498513 = 1873885) B1873885
theorem B2498531 : Blo 1665032 2498531 := bstep (se 1 (by rfl) ⟨1873898, by rfl⟩ : syracuseStep 2498531 = 3747797) B3747797
theorem B6324227 : Blo 1665032 6324227 := bstep (se 1 (by rfl) ⟨4743170, by rfl⟩ : syracuseStep 6324227 = 9486341) B9486341
theorem B2498585 : Blo 1665032 2498585 := bstep (se 2 (by rfl) ⟨936969, by rfl⟩ : syracuseStep 2498585 = 1873939) B1873939
theorem B2498699 : Blo 1665032 2498699 := bstep (se 1 (by rfl) ⟨1874024, by rfl⟩ : syracuseStep 2498699 = 3748049) B3748049
theorem B4743319 : Blo 1665032 4743319 := bstep (se 1 (by rfl) ⟨3557489, by rfl⟩ : syracuseStep 4743319 = 7114979) B7114979
theorem B2498711 : Blo 1665032 2498711 := bstep (se 1 (by rfl) ⟨1874033, by rfl⟩ : syracuseStep 2498711 = 3748067) B3748067
theorem B2498777 : Blo 1665032 2498777 := bstep (se 2 (by rfl) ⟨937041, by rfl⟩ : syracuseStep 2498777 = 1874083) B1874083
theorem B27025649 : Blo 1665032 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B2498891 : Blo 1665032 2498891 := bstep (se 1 (by rfl) ⟨1874168, by rfl⟩ : syracuseStep 2498891 = 3748337) B3748337
theorem B2498903 : Blo 1665032 2498903 := bstep (se 1 (by rfl) ⟨1874177, by rfl⟩ : syracuseStep 2498903 = 3748355) B3748355
theorem B2498969 : Blo 1665032 2498969 := bstep (se 2 (by rfl) ⟨937113, by rfl⟩ : syracuseStep 2498969 = 1874227) B1874227
theorem B2810315 : Blo 1665032 2810315 := bstep (se 1 (by rfl) ⟨2107736, by rfl⟩ : syracuseStep 2810315 = 4215473) B4215473
theorem B7209437 : Blo 1665032 7209437 := bstep (se 3 (by rfl) ⟨1351769, by rfl⟩ : syracuseStep 7209437 = 2703539) B2703539
theorem B2499083 : Blo 1665032 2499083 := bstep (se 1 (by rfl) ⟨1874312, by rfl⟩ : syracuseStep 2499083 = 3748625) B3748625
theorem B2499095 : Blo 1665032 2499095 := bstep (se 1 (by rfl) ⟨1874321, by rfl⟩ : syracuseStep 2499095 = 3748643) B3748643
theorem B8430155 : Blo 1665032 8430155 := bstep (se 1 (by rfl) ⟨6322616, by rfl⟩ : syracuseStep 8430155 = 12645233) B12645233
theorem B2810443 : Blo 1665032 2810443 := bstep (se 1 (by rfl) ⟨2107832, by rfl⟩ : syracuseStep 2810443 = 4215665) B4215665
theorem B2499161 : Blo 1665032 2499161 := bstep (se 2 (by rfl) ⟨937185, by rfl⟩ : syracuseStep 2499161 = 1874371) B1874371
theorem B5620427 : Blo 1665032 5620427 := bstep (se 1 (by rfl) ⟨4215320, by rfl⟩ : syracuseStep 5620427 = 8430641) B8430641
theorem B3162827 : Blo 1665032 3162827 := bstep (se 1 (by rfl) ⟨2372120, by rfl⟩ : syracuseStep 3162827 = 4744241) B4744241
theorem B2499275 : Blo 1665032 2499275 := bstep (se 1 (by rfl) ⟨1874456, by rfl⟩ : syracuseStep 2499275 = 3748913) B3748913
theorem B2499287 : Blo 1665032 2499287 := bstep (se 1 (by rfl) ⟨1874465, by rfl⟩ : syracuseStep 2499287 = 3748931) B3748931
theorem B2810585 : Blo 1665032 2810585 := bstep (se 2 (by rfl) ⟨1053969, by rfl⟩ : syracuseStep 2810585 = 2107939) B2107939
theorem B3162881 : Blo 1665032 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B2499353 : Blo 1665032 2499353 := bstep (se 2 (by rfl) ⟨937257, by rfl⟩ : syracuseStep 2499353 = 1874515) B1874515
theorem B17089325 : Blo 1665032 17089325 := bstep (se 3 (by rfl) ⟨3204248, by rfl⟩ : syracuseStep 17089325 = 6408497) B6408497
theorem B2810713 : Blo 1665032 2810713 := bstep (se 2 (by rfl) ⟨1054017, by rfl⟩ : syracuseStep 2810713 = 2108035) B2108035
theorem B3376001 : Blo 1665032 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2499467 : Blo 1665032 2499467 := bstep (se 1 (by rfl) ⟨1874600, by rfl⟩ : syracuseStep 2499467 = 3749201) B3749201
theorem B2499479 : Blo 1665032 2499479 := bstep (se 1 (by rfl) ⟨1874609, by rfl⟩ : syracuseStep 2499479 = 3749219) B3749219
theorem B5620697 : Blo 1665032 5620697 := bstep (se 2 (by rfl) ⟨2107761, by rfl⟩ : syracuseStep 5620697 = 4215523) B4215523
theorem B2499545 : Blo 1665032 2499545 := bstep (se 2 (by rfl) ⟨937329, by rfl⟩ : syracuseStep 2499545 = 1874659) B1874659
theorem B2499659 : Blo 1665032 2499659 := bstep (se 1 (by rfl) ⟨1874744, by rfl⟩ : syracuseStep 2499659 = 3749489) B3749489
theorem B2499671 : Blo 1665032 2499671 := bstep (se 1 (by rfl) ⟨1874753, by rfl⟩ : syracuseStep 2499671 = 3749507) B3749507
theorem B2499737 : Blo 1665032 2499737 := bstep (se 2 (by rfl) ⟨937401, by rfl⟩ : syracuseStep 2499737 = 1874803) B1874803
theorem B7595309 : Blo 1665032 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B1779031 : Blo 1665032 1779031 := bstep (se 1 (by rfl) ⟨1334273, by rfl⟩ : syracuseStep 1779031 = 2668547) B2668547
theorem B2811287 : Blo 1665032 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B4744651 : Blo 1665032 4744651 := bstep (se 1 (by rfl) ⟨3558488, by rfl⟩ : syracuseStep 4744651 = 7116977) B7116977
theorem B1689067 : Blo 1665032 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B2811415 : Blo 1665032 2811415 := bstep (se 1 (by rfl) ⟨2108561, by rfl⟩ : syracuseStep 2811415 = 4217123) B4217123
theorem B5621399 : Blo 1665032 5621399 := bstep (se 1 (by rfl) ⟨4216049, by rfl⟩ : syracuseStep 5621399 = 8432099) B8432099
theorem B3163799 : Blo 1665032 3163799 := bstep (se 1 (by rfl) ⟨2372849, by rfl⟩ : syracuseStep 3163799 = 4745699) B4745699
theorem B4744925 : Blo 1665032 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B4564811 : Blo 1665032 4564811 := bstep (se 1 (by rfl) ⟨3423608, by rfl⟩ : syracuseStep 4564811 = 6847217) B6847217
theorem B3606487 : Blo 1665032 3606487 := bstep (se 1 (by rfl) ⟨2704865, by rfl⟩ : syracuseStep 3606487 = 5409731) B5409731
theorem B1665035 : Blo 1665032 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B1665047 : Blo 1665032 1665047 := bstep (se 1 (by rfl) ⟨1248785, by rfl⟩ : syracuseStep 1665047 = 2497571) B2497571
theorem B1665067 : Blo 1665032 1665067 := bstep (se 1 (by rfl) ⟨1248800, by rfl⟩ : syracuseStep 1665067 = 2497601) B2497601
theorem B4745267 : Blo 1665032 4745267 := bstep (se 1 (by rfl) ⟨3558950, by rfl⟩ : syracuseStep 4745267 = 7117901) B7117901
theorem B1665079 : Blo 1665032 1665079 := bstep (se 1 (by rfl) ⟨1248809, by rfl⟩ : syracuseStep 1665079 = 2497619) B2497619
theorem B1665099 : Blo 1665032 1665099 := bstep (se 1 (by rfl) ⟨1248824, by rfl⟩ : syracuseStep 1665099 = 2497649) B2497649
theorem B1665111 : Blo 1665032 1665111 := bstep (se 1 (by rfl) ⟨1248833, by rfl⟩ : syracuseStep 1665111 = 2497667) B2497667
theorem B1665131 : Blo 1665032 1665131 := bstep (se 1 (by rfl) ⟨1248848, by rfl⟩ : syracuseStep 1665131 = 2497697) B2497697
theorem B3205235 : Blo 1665032 3205235 := bstep (se 1 (by rfl) ⟨2403926, by rfl⟩ : syracuseStep 3205235 = 4807853) B4807853
theorem B1665143 : Blo 1665032 1665143 := bstep (se 1 (by rfl) ⟨1248857, by rfl⟩ : syracuseStep 1665143 = 2497715) B2497715
theorem B1665163 : Blo 1665032 1665163 := bstep (se 1 (by rfl) ⟨1248872, by rfl⟩ : syracuseStep 1665163 = 2497745) B2497745
theorem B2001035 : Blo 1665032 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B3557515 : Blo 1665032 3557515 := bstep (se 1 (by rfl) ⟨2668136, by rfl⟩ : syracuseStep 3557515 = 5336273) B5336273
theorem B2812043 : Blo 1665032 2812043 := bstep (se 1 (by rfl) ⟨2109032, by rfl⟩ : syracuseStep 2812043 = 4218065) B4218065
theorem B1665175 : Blo 1665032 1665175 := bstep (se 1 (by rfl) ⟨1248881, by rfl⟩ : syracuseStep 1665175 = 2497763) B2497763
theorem B4393111 : Blo 1665032 4393111 := bstep (se 1 (by rfl) ⟨3294833, by rfl⟩ : syracuseStep 4393111 = 6589667) B6589667
theorem B1665195 : Blo 1665032 1665195 := bstep (se 1 (by rfl) ⟨1248896, by rfl⟩ : syracuseStep 1665195 = 2497793) B2497793
theorem B5621939 : Blo 1665032 5621939 := bstep (se 1 (by rfl) ⟨4216454, by rfl⟩ : syracuseStep 5621939 = 8432909) B8432909
theorem B1665207 : Blo 1665032 1665207 := bstep (se 1 (by rfl) ⟨1248905, by rfl⟩ : syracuseStep 1665207 = 2497811) B2497811
theorem B1665227 : Blo 1665032 1665227 := bstep (se 1 (by rfl) ⟨1248920, by rfl⟩ : syracuseStep 1665227 = 2497841) B2497841
theorem B1665239 : Blo 1665032 1665239 := bstep (se 1 (by rfl) ⟨1248929, by rfl⟩ : syracuseStep 1665239 = 2497859) B2497859
theorem B15198425 : Blo 1665032 15198425 := bstep (se 2 (by rfl) ⟨5699409, by rfl⟩ : syracuseStep 15198425 = 11398819) B11398819
theorem B1665259 : Blo 1665032 1665259 := bstep (se 1 (by rfl) ⟨1248944, by rfl⟩ : syracuseStep 1665259 = 2497889) B2497889
theorem B1665271 : Blo 1665032 1665271 := bstep (se 1 (by rfl) ⟨1248953, by rfl⟩ : syracuseStep 1665271 = 2497907) B2497907
theorem B1665291 : Blo 1665032 1665291 := bstep (se 1 (by rfl) ⟨1248968, by rfl⟩ : syracuseStep 1665291 = 2497937) B2497937
theorem B2812171 : Blo 1665032 2812171 := bstep (se 1 (by rfl) ⟨2109128, by rfl⟩ : syracuseStep 2812171 = 4218257) B4218257
theorem B1665303 : Blo 1665032 1665303 := bstep (se 1 (by rfl) ⟨1248977, by rfl⟩ : syracuseStep 1665303 = 2497955) B2497955
theorem B1665323 : Blo 1665032 1665323 := bstep (se 1 (by rfl) ⟨1248992, by rfl⟩ : syracuseStep 1665323 = 2497985) B2497985
theorem B1665335 : Blo 1665032 1665335 := bstep (se 1 (by rfl) ⟨1249001, by rfl⟩ : syracuseStep 1665335 = 2498003) B2498003
theorem B8431937 : Blo 1665032 8431937 := bstep (se 2 (by rfl) ⟨3161976, by rfl⟩ : syracuseStep 8431937 = 6323953) B6323953
theorem B1665355 : Blo 1665032 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B1665367 : Blo 1665032 1665367 := bstep (se 1 (by rfl) ⟨1249025, by rfl⟩ : syracuseStep 1665367 = 2498051) B2498051
theorem B1665387 : Blo 1665032 1665387 := bstep (se 1 (by rfl) ⟨1249040, by rfl⟩ : syracuseStep 1665387 = 2498081) B2498081
theorem B104008049 : Blo 1665032 104008049 := bstep (se 2 (by rfl) ⟨39003018, by rfl⟩ : syracuseStep 104008049 = 78006037) B78006037
theorem B1665399 : Blo 1665032 1665399 := bstep (se 1 (by rfl) ⟨1249049, by rfl⟩ : syracuseStep 1665399 = 2498099) B2498099
theorem B1665419 : Blo 1665032 1665419 := bstep (se 1 (by rfl) ⟨1249064, by rfl⟩ : syracuseStep 1665419 = 2498129) B2498129
theorem B3557771 : Blo 1665032 3557771 := bstep (se 1 (by rfl) ⟨2668328, by rfl⟩ : syracuseStep 3557771 = 5336657) B5336657
theorem B1665431 : Blo 1665032 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B1665451 : Blo 1665032 1665451 := bstep (se 1 (by rfl) ⟨1249088, by rfl⟩ : syracuseStep 1665451 = 2498177) B2498177
theorem B16222643 : Blo 1665032 16222643 := bstep (se 1 (by rfl) ⟨12166982, by rfl⟩ : syracuseStep 16222643 = 24333965) B24333965
theorem B1665463 : Blo 1665032 1665463 := bstep (se 1 (by rfl) ⟨1249097, by rfl⟩ : syracuseStep 1665463 = 2498195) B2498195
theorem B5622209 : Blo 1665032 5622209 := bstep (se 2 (by rfl) ⟨2108328, by rfl⟩ : syracuseStep 5622209 = 4216657) B4216657
theorem B1665483 : Blo 1665032 1665483 := bstep (se 1 (by rfl) ⟨1249112, by rfl⟩ : syracuseStep 1665483 = 2498225) B2498225
theorem B1665495 : Blo 1665032 1665495 := bstep (se 1 (by rfl) ⟨1249121, by rfl⟩ : syracuseStep 1665495 = 2498243) B2498243
theorem B1665515 : Blo 1665032 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B1665527 : Blo 1665032 1665527 := bstep (se 1 (by rfl) ⟨1249145, by rfl⟩ : syracuseStep 1665527 = 2498291) B2498291
theorem B1665547 : Blo 1665032 1665547 := bstep (se 1 (by rfl) ⟨1249160, by rfl⟩ : syracuseStep 1665547 = 2498321) B2498321
theorem B1665559 : Blo 1665032 1665559 := bstep (se 1 (by rfl) ⟨1249169, by rfl⟩ : syracuseStep 1665559 = 2498339) B2498339
theorem B1665579 : Blo 1665032 1665579 := bstep (se 1 (by rfl) ⟨1249184, by rfl⟩ : syracuseStep 1665579 = 2498369) B2498369
theorem B3000883 : Blo 1665032 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B5065267 : Blo 1665032 5065267 := bstep (se 1 (by rfl) ⟨3798950, by rfl⟩ : syracuseStep 5065267 = 7597901) B7597901
theorem B1665591 : Blo 1665032 1665591 := bstep (se 1 (by rfl) ⟨1249193, by rfl⟩ : syracuseStep 1665591 = 2498387) B2498387
theorem B1665611 : Blo 1665032 1665611 := bstep (se 1 (by rfl) ⟨1249208, by rfl⟩ : syracuseStep 1665611 = 2498417) B2498417
theorem B1665623 : Blo 1665032 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B3746393 : Blo 1665032 3746393 := bstep (se 2 (by rfl) ⟨1404897, by rfl⟩ : syracuseStep 3746393 = 2809795) B2809795
theorem B1665643 : Blo 1665032 1665643 := bstep (se 1 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 1665643 = 2498465) B2498465
theorem B1665655 : Blo 1665032 1665655 := bstep (se 1 (by rfl) ⟨1249241, by rfl⟩ : syracuseStep 1665655 = 2498483) B2498483
theorem B1665675 : Blo 1665032 1665675 := bstep (se 1 (by rfl) ⟨1249256, by rfl⟩ : syracuseStep 1665675 = 2498513) B2498513
theorem B1665687 : Blo 1665032 1665687 := bstep (se 1 (by rfl) ⟨1249265, by rfl⟩ : syracuseStep 1665687 = 2498531) B2498531
theorem B1665707 : Blo 1665032 1665707 := bstep (se 1 (by rfl) ⟨1249280, by rfl⟩ : syracuseStep 1665707 = 2498561) B2498561
theorem B3746483 : Blo 1665032 3746483 := bstep (se 1 (by rfl) ⟨2809862, by rfl⟩ : syracuseStep 3746483 = 5619725) B5619725
theorem B1665719 : Blo 1665032 1665719 := bstep (se 1 (by rfl) ⟨1249289, by rfl⟩ : syracuseStep 1665719 = 2498579) B2498579
theorem B1665739 : Blo 1665032 1665739 := bstep (se 1 (by rfl) ⟨1249304, by rfl⟩ : syracuseStep 1665739 = 2498609) B2498609
theorem B16009933 : Blo 1665032 16009933 := bstep (se 3 (by rfl) ⟨3001862, by rfl⟩ : syracuseStep 16009933 = 6003725) B6003725
theorem B3746519 : Blo 1665032 3746519 := bstep (se 1 (by rfl) ⟨2809889, by rfl⟩ : syracuseStep 3746519 = 5619779) B5619779
theorem B1665751 : Blo 1665032 1665751 := bstep (se 1 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 1665751 = 2498627) B2498627
theorem B1665771 : Blo 1665032 1665771 := bstep (se 1 (by rfl) ⟨1249328, by rfl⟩ : syracuseStep 1665771 = 2498657) B2498657
theorem B1665783 : Blo 1665032 1665783 := bstep (se 1 (by rfl) ⟨1249337, by rfl⟩ : syracuseStep 1665783 = 2498675) B2498675
theorem B1665803 : Blo 1665032 1665803 := bstep (se 1 (by rfl) ⟨1249352, by rfl⟩ : syracuseStep 1665803 = 2498705) B2498705
theorem B1665815 : Blo 1665032 1665815 := bstep (se 1 (by rfl) ⟨1249361, by rfl⟩ : syracuseStep 1665815 = 2498723) B2498723
theorem B1665835 : Blo 1665032 1665835 := bstep (se 1 (by rfl) ⟨1249376, by rfl⟩ : syracuseStep 1665835 = 2498753) B2498753
theorem B1665847 : Blo 1665032 1665847 := bstep (se 1 (by rfl) ⟨1249385, by rfl⟩ : syracuseStep 1665847 = 2498771) B2498771
theorem B1665867 : Blo 1665032 1665867 := bstep (se 1 (by rfl) ⟨1249400, by rfl⟩ : syracuseStep 1665867 = 2498801) B2498801
theorem B1665879 : Blo 1665032 1665879 := bstep (se 1 (by rfl) ⟨1249409, by rfl⟩ : syracuseStep 1665879 = 2498819) B2498819
theorem B1665899 : Blo 1665032 1665899 := bstep (se 1 (by rfl) ⟨1249424, by rfl⟩ : syracuseStep 1665899 = 2498849) B2498849
theorem B1665911 : Blo 1665032 1665911 := bstep (se 1 (by rfl) ⟨1249433, by rfl⟩ : syracuseStep 1665911 = 2498867) B2498867
theorem B3746699 : Blo 1665032 3746699 := bstep (se 1 (by rfl) ⟨2810024, by rfl⟩ : syracuseStep 3746699 = 5620049) B5620049
theorem B1665931 : Blo 1665032 1665931 := bstep (se 1 (by rfl) ⟨1249448, by rfl⟩ : syracuseStep 1665931 = 2498897) B2498897
theorem B1665943 : Blo 1665032 1665943 := bstep (se 1 (by rfl) ⟨1249457, by rfl⟩ : syracuseStep 1665943 = 2498915) B2498915
theorem B1665963 : Blo 1665032 1665963 := bstep (se 1 (by rfl) ⟨1249472, by rfl⟩ : syracuseStep 1665963 = 2498945) B2498945
theorem B1665975 : Blo 1665032 1665975 := bstep (se 1 (by rfl) ⟨1249481, by rfl⟩ : syracuseStep 1665975 = 2498963) B2498963
theorem B3746753 : Blo 1665032 3746753 := bstep (se 2 (by rfl) ⟨1405032, by rfl⟩ : syracuseStep 3746753 = 2810065) B2810065
theorem B1665995 : Blo 1665032 1665995 := bstep (se 1 (by rfl) ⟨1249496, by rfl⟩ : syracuseStep 1665995 = 2498993) B2498993
theorem B4058059 : Blo 1665032 4058059 := bstep (se 1 (by rfl) ⟨3043544, by rfl⟩ : syracuseStep 4058059 = 6087089) B6087089
theorem B1666007 : Blo 1665032 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B5622749 : Blo 1665032 5622749 := bstep (se 3 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 5622749 = 2108531) B2108531
theorem B1666027 : Blo 1665032 1666027 := bstep (se 1 (by rfl) ⟨1249520, by rfl⟩ : syracuseStep 1666027 = 2499041) B2499041
theorem B1666039 : Blo 1665032 1666039 := bstep (se 1 (by rfl) ⟨1249529, by rfl⟩ : syracuseStep 1666039 = 2499059) B2499059
theorem B1666059 : Blo 1665032 1666059 := bstep (se 1 (by rfl) ⟨1249544, by rfl⟩ : syracuseStep 1666059 = 2499089) B2499089
theorem B1666071 : Blo 1665032 1666071 := bstep (se 1 (by rfl) ⟨1249553, by rfl⟩ : syracuseStep 1666071 = 2499107) B2499107
theorem B1666091 : Blo 1665032 1666091 := bstep (se 1 (by rfl) ⟨1249568, by rfl⟩ : syracuseStep 1666091 = 2499137) B2499137
theorem B6327341 : Blo 1665032 6327341 := bstep (se 3 (by rfl) ⟨1186376, by rfl⟩ : syracuseStep 6327341 = 2372753) B2372753
theorem B5696563 : Blo 1665032 5696563 := bstep (se 1 (by rfl) ⟨4272422, by rfl⟩ : syracuseStep 5696563 = 8544845) B8544845
theorem B1666103 : Blo 1665032 1666103 := bstep (se 1 (by rfl) ⟨1249577, by rfl⟩ : syracuseStep 1666103 = 2499155) B2499155
theorem B1666123 : Blo 1665032 1666123 := bstep (se 1 (by rfl) ⟨1249592, by rfl⟩ : syracuseStep 1666123 = 2499185) B2499185
theorem B1666135 : Blo 1665032 1666135 := bstep (se 1 (by rfl) ⟨1249601, by rfl⟩ : syracuseStep 1666135 = 2499203) B2499203
theorem B28470365 : Blo 1665032 28470365 := bstep (se 3 (by rfl) ⟨5338193, by rfl⟩ : syracuseStep 28470365 = 10676387) B10676387
theorem B1666155 : Blo 1665032 1666155 := bstep (se 1 (by rfl) ⟨1249616, by rfl⟩ : syracuseStep 1666155 = 2499233) B2499233
theorem B1666167 : Blo 1665032 1666167 := bstep (se 1 (by rfl) ⟨1249625, by rfl⟩ : syracuseStep 1666167 = 2499251) B2499251
theorem B1666187 : Blo 1665032 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B1666199 : Blo 1665032 1666199 := bstep (se 1 (by rfl) ⟨1249649, by rfl⟩ : syracuseStep 1666199 = 2499299) B2499299
theorem B3746969 : Blo 1665032 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B7113901 : Blo 1665032 7113901 := bstep (se 3 (by rfl) ⟨1333856, by rfl⟩ : syracuseStep 7113901 = 2667713) B2667713
theorem B1666219 : Blo 1665032 1666219 := bstep (se 1 (by rfl) ⟨1249664, by rfl⟩ : syracuseStep 1666219 = 2499329) B2499329
theorem B1666231 : Blo 1665032 1666231 := bstep (se 1 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 1666231 = 2499347) B2499347
theorem B1666251 : Blo 1665032 1666251 := bstep (se 1 (by rfl) ⟨1249688, by rfl⟩ : syracuseStep 1666251 = 2499377) B2499377
theorem B19238093 : Blo 1665032 19238093 := bstep (se 3 (by rfl) ⟨3607142, by rfl⟩ : syracuseStep 19238093 = 7214285) B7214285
theorem B1666263 : Blo 1665032 1666263 := bstep (se 1 (by rfl) ⟨1249697, by rfl⟩ : syracuseStep 1666263 = 2499395) B2499395
theorem B1666283 : Blo 1665032 1666283 := bstep (se 1 (by rfl) ⟨1249712, by rfl⟩ : syracuseStep 1666283 = 2499425) B2499425
theorem B3747059 : Blo 1665032 3747059 := bstep (se 1 (by rfl) ⟨2810294, by rfl⟩ : syracuseStep 3747059 = 5620589) B5620589
theorem B1666295 : Blo 1665032 1666295 := bstep (se 1 (by rfl) ⟨1249721, by rfl⟩ : syracuseStep 1666295 = 2499443) B2499443
theorem B2108683 : Blo 1665032 2108683 := bstep (se 1 (by rfl) ⟨1581512, by rfl⟩ : syracuseStep 2108683 = 3163025) B3163025
theorem B1666315 : Blo 1665032 1666315 := bstep (se 1 (by rfl) ⟨1249736, by rfl⟩ : syracuseStep 1666315 = 2499473) B2499473
theorem B3747095 : Blo 1665032 3747095 := bstep (se 1 (by rfl) ⟨2810321, by rfl⟩ : syracuseStep 3747095 = 5620643) B5620643
theorem B1666327 : Blo 1665032 1666327 := bstep (se 1 (by rfl) ⟨1249745, by rfl⟩ : syracuseStep 1666327 = 2499491) B2499491
theorem B1666347 : Blo 1665032 1666347 := bstep (se 1 (by rfl) ⟨1249760, by rfl⟩ : syracuseStep 1666347 = 2499521) B2499521
theorem B1666359 : Blo 1665032 1666359 := bstep (se 1 (by rfl) ⟨1249769, by rfl⟩ : syracuseStep 1666359 = 2499539) B2499539
theorem B1666379 : Blo 1665032 1666379 := bstep (se 1 (by rfl) ⟨1249784, by rfl⟩ : syracuseStep 1666379 = 2499569) B2499569
theorem B1666391 : Blo 1665032 1666391 := bstep (se 1 (by rfl) ⟨1249793, by rfl⟩ : syracuseStep 1666391 = 2499587) B2499587
theorem B3558745 : Blo 1665032 3558745 := bstep (se 2 (by rfl) ⟨1334529, by rfl⟩ : syracuseStep 3558745 = 2669059) B2669059
theorem B9489757 : Blo 1665032 9489757 := bstep (se 3 (by rfl) ⟨1779329, by rfl⟩ : syracuseStep 9489757 = 3558659) B3558659
theorem B1666411 : Blo 1665032 1666411 := bstep (se 1 (by rfl) ⟨1249808, by rfl⟩ : syracuseStep 1666411 = 2499617) B2499617
theorem B1666423 : Blo 1665032 1666423 := bstep (se 1 (by rfl) ⟨1249817, by rfl⟩ : syracuseStep 1666423 = 2499635) B2499635
theorem B1666443 : Blo 1665032 1666443 := bstep (se 1 (by rfl) ⟨1249832, by rfl⟩ : syracuseStep 1666443 = 2499665) B2499665
theorem B1666455 : Blo 1665032 1666455 := bstep (se 1 (by rfl) ⟨1249841, by rfl⟩ : syracuseStep 1666455 = 2499683) B2499683
theorem B1666475 : Blo 1665032 1666475 := bstep (se 1 (by rfl) ⟨1249856, by rfl⟩ : syracuseStep 1666475 = 2499713) B2499713
theorem B1666487 : Blo 1665032 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B3747275 : Blo 1665032 3747275 := bstep (se 1 (by rfl) ⟨2810456, by rfl⟩ : syracuseStep 3747275 = 5620913) B5620913
theorem B1666507 : Blo 1665032 1666507 := bstep (se 1 (by rfl) ⟨1249880, by rfl⟩ : syracuseStep 1666507 = 2499761) B2499761
theorem B1666519 : Blo 1665032 1666519 := bstep (se 1 (by rfl) ⟨1249889, by rfl⟩ : syracuseStep 1666519 = 2499779) B2499779
theorem B3558899 : Blo 1665032 3558899 := bstep (se 1 (by rfl) ⟨2669174, by rfl⟩ : syracuseStep 3558899 = 5338349) B5338349
theorem B3747329 : Blo 1665032 3747329 := bstep (se 2 (by rfl) ⟨1405248, by rfl⟩ : syracuseStep 3747329 = 2810497) B2810497
theorem B7114243 : Blo 1665032 7114243 := bstep (se 1 (by rfl) ⟨5335682, by rfl⟩ : syracuseStep 7114243 = 10671365) B10671365
theorem B12652037 : Blo 1665032 12652037 := bstep (se 4 (by rfl) ⟨1186128, by rfl⟩ : syracuseStep 12652037 = 2372257) B2372257
theorem B12004939 : Blo 1665032 12004939 := bstep (se 1 (by rfl) ⟨9003704, by rfl⟩ : syracuseStep 12004939 = 18007409) B18007409
theorem B3001943 : Blo 1665032 3001943 := bstep (se 1 (by rfl) ⟨2251457, by rfl⟩ : syracuseStep 3001943 = 4502915) B4502915
theorem B3747545 : Blo 1665032 3747545 := bstep (se 2 (by rfl) ⟨1405329, by rfl⟩ : syracuseStep 3747545 = 2810659) B2810659
theorem B6754013 : Blo 1665032 6754013 := bstep (se 3 (by rfl) ⟨1266377, by rfl⟩ : syracuseStep 6754013 = 2532755) B2532755
theorem B4501271 : Blo 1665032 4501271 := bstep (se 1 (by rfl) ⟨3375953, by rfl⟩ : syracuseStep 4501271 = 6751907) B6751907
theorem B3747635 : Blo 1665032 3747635 := bstep (se 1 (by rfl) ⟨2810726, by rfl⟩ : syracuseStep 3747635 = 5621453) B5621453
theorem B2371403 : Blo 1665032 2371403 := bstep (se 1 (by rfl) ⟨1778552, by rfl⟩ : syracuseStep 2371403 = 3557105) B3557105
theorem B3747671 : Blo 1665032 3747671 := bstep (se 1 (by rfl) ⟨2810753, by rfl⟩ : syracuseStep 3747671 = 5621507) B5621507
theorem B7409497 : Blo 1665032 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B9613187 : Blo 1665032 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B4001687 : Blo 1665032 4001687 := bstep (se 1 (by rfl) ⟨3001265, by rfl⟩ : syracuseStep 4001687 = 6002531) B6002531
theorem B7598045 : Blo 1665032 7598045 := bstep (se 3 (by rfl) ⟨1424633, by rfl⟩ : syracuseStep 7598045 = 2849267) B2849267
theorem B3747851 : Blo 1665032 3747851 := bstep (se 1 (by rfl) ⟨2810888, by rfl⟩ : syracuseStep 3747851 = 5621777) B5621777
theorem B3747905 : Blo 1665032 3747905 := bstep (se 2 (by rfl) ⟨1405464, by rfl⟩ : syracuseStep 3747905 = 2810929) B2810929
theorem B5623883 : Blo 1665032 5623883 := bstep (se 1 (by rfl) ⟨4217912, by rfl⟩ : syracuseStep 5623883 = 8435825) B8435825
theorem B4214987 : Blo 1665032 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B8433881 : Blo 1665032 8433881 := bstep (se 2 (by rfl) ⟨3162705, by rfl⟩ : syracuseStep 8433881 = 6325411) B6325411
theorem B3748121 : Blo 1665032 3748121 := bstep (se 2 (by rfl) ⟨1405545, by rfl⟩ : syracuseStep 3748121 = 2811091) B2811091
theorem B5624153 : Blo 1665032 5624153 := bstep (se 2 (by rfl) ⟨2109057, by rfl⟩ : syracuseStep 5624153 = 4218115) B4218115
theorem B3748211 : Blo 1665032 3748211 := bstep (se 1 (by rfl) ⟨2811158, by rfl⟩ : syracuseStep 3748211 = 5622317) B5622317
theorem B3748247 : Blo 1665032 3748247 := bstep (se 1 (by rfl) ⟨2811185, by rfl⟩ : syracuseStep 3748247 = 5622371) B5622371
theorem B7115201 : Blo 1665032 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B4215361 : Blo 1665032 4215361 := bstep (se 2 (by rfl) ⟨1580760, by rfl⟩ : syracuseStep 4215361 = 3161521) B3161521
theorem B3748427 : Blo 1665032 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B3748481 : Blo 1665032 3748481 := bstep (se 2 (by rfl) ⟨1405680, by rfl⟩ : syracuseStep 3748481 = 2811361) B2811361
theorem B5411549 : Blo 1665032 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B6411097 : Blo 1665032 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B3748697 : Blo 1665032 3748697 := bstep (se 2 (by rfl) ⟨1405761, by rfl⟩ : syracuseStep 3748697 = 2811523) B2811523
theorem B12006323 : Blo 1665032 12006323 := bstep (se 1 (by rfl) ⟨9004742, by rfl⟩ : syracuseStep 12006323 = 18009485) B18009485
theorem B3748787 : Blo 1665032 3748787 := bstep (se 1 (by rfl) ⟨2811590, by rfl⟩ : syracuseStep 3748787 = 5623181) B5623181
theorem B3748823 : Blo 1665032 3748823 := bstep (se 1 (by rfl) ⟨2811617, by rfl⟩ : syracuseStep 3748823 = 5623235) B5623235
theorem B8549441 : Blo 1665032 8549441 := bstep (se 2 (by rfl) ⟨3206040, by rfl⟩ : syracuseStep 8549441 = 6412081) B6412081
theorem B3749003 : Blo 1665032 3749003 := bstep (se 1 (by rfl) ⟨2811752, by rfl⟩ : syracuseStep 3749003 = 5623505) B5623505
theorem B4215959 : Blo 1665032 4215959 := bstep (se 1 (by rfl) ⟨3161969, by rfl⟩ : syracuseStep 4215959 = 6323939) B6323939
theorem B61600949 : Blo 1665032 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B3749057 : Blo 1665032 3749057 := bstep (se 2 (by rfl) ⟨1405896, by rfl⟩ : syracuseStep 3749057 = 2811793) B2811793
theorem B3798359 : Blo 1665032 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B6002009 : Blo 1665032 6002009 := bstep (se 2 (by rfl) ⟨2250753, by rfl⟩ : syracuseStep 6002009 = 4501507) B4501507
theorem B1873291 : Blo 1665032 1873291 := bstep (se 1 (by rfl) ⟨1404968, by rfl⟩ : syracuseStep 1873291 = 2809937) B2809937
theorem B3749273 : Blo 1665032 3749273 := bstep (se 2 (by rfl) ⟨1405977, by rfl⟩ : syracuseStep 3749273 = 2811955) B2811955
theorem B3749363 : Blo 1665032 3749363 := bstep (se 1 (by rfl) ⟨2812022, by rfl⟩ : syracuseStep 3749363 = 5624045) B5624045
theorem B1873399 : Blo 1665032 1873399 := bstep (se 1 (by rfl) ⟨1405049, by rfl⟩ : syracuseStep 1873399 = 2810099) B2810099
theorem B3749399 : Blo 1665032 3749399 := bstep (se 1 (by rfl) ⟨2812049, by rfl⟩ : syracuseStep 3749399 = 5624099) B5624099
theorem B102545027 : Blo 1665032 102545027 := bstep (se 1 (by rfl) ⟨76908770, by rfl⟩ : syracuseStep 102545027 = 153817541) B153817541
theorem B10131095 : Blo 1665032 10131095 := bstep (se 1 (by rfl) ⟨7598321, by rfl⟩ : syracuseStep 10131095 = 15196643) B15196643
theorem B1873579 : Blo 1665032 1873579 := bstep (se 1 (by rfl) ⟨1405184, by rfl⟩ : syracuseStep 1873579 = 2810369) B2810369
theorem B3749579 : Blo 1665032 3749579 := bstep (se 1 (by rfl) ⟨2812184, by rfl⟩ : syracuseStep 3749579 = 5624369) B5624369
theorem B18249421 : Blo 1665032 18249421 := bstep (se 3 (by rfl) ⟨3421766, by rfl⟩ : syracuseStep 18249421 = 6843533) B6843533
theorem B3749633 : Blo 1665032 3749633 := bstep (se 2 (by rfl) ⟨1406112, by rfl⟩ : syracuseStep 3749633 = 2812225) B2812225
theorem B1873687 : Blo 1665032 1873687 := bstep (se 1 (by rfl) ⟨1405265, by rfl⟩ : syracuseStep 1873687 = 2810531) B2810531
theorem B8435501 : Blo 1665032 8435501 := bstep (se 3 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 8435501 = 3163313) B3163313
theorem B6321995 : Blo 1665032 6321995 := bstep (se 1 (by rfl) ⟨4741496, by rfl⟩ : syracuseStep 6321995 = 9482993) B9482993
theorem B7116619 : Blo 1665032 7116619 := bstep (se 1 (by rfl) ⟨5337464, by rfl⟩ : syracuseStep 7116619 = 10674929) B10674929
theorem B6322009 : Blo 1665032 6322009 := bstep (se 2 (by rfl) ⟨2370753, by rfl⟩ : syracuseStep 6322009 = 4741507) B4741507
theorem B12654467 : Blo 1665032 12654467 := bstep (se 1 (by rfl) ⟨9490850, by rfl⟩ : syracuseStep 12654467 = 18981701) B18981701
theorem B4216769 : Blo 1665032 4216769 := bstep (se 2 (by rfl) ⟨1581288, by rfl⟩ : syracuseStep 4216769 = 3162577) B3162577
theorem B1873867 : Blo 1665032 1873867 := bstep (se 1 (by rfl) ⟨1405400, by rfl⟩ : syracuseStep 1873867 = 2810801) B2810801
theorem B1873975 : Blo 1665032 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B3799115 : Blo 1665032 3799115 := bstep (se 1 (by rfl) ⟨2849336, by rfl⟩ : syracuseStep 3799115 = 5698673) B5698673
theorem B18012253 : Blo 1665032 18012253 := bstep (se 3 (by rfl) ⟨3377297, by rfl⟩ : syracuseStep 18012253 = 6754595) B6754595
theorem B7116893 : Blo 1665032 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B1874155 : Blo 1665032 1874155 := bstep (se 1 (by rfl) ⟨1405616, by rfl⟩ : syracuseStep 1874155 = 2811233) B2811233
theorem B12646691 : Blo 1665032 12646691 := bstep (se 1 (by rfl) ⟨9485018, by rfl⟩ : syracuseStep 12646691 = 18970037) B18970037
theorem B4004147 : Blo 1665032 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B1874263 : Blo 1665032 1874263 := bstep (se 1 (by rfl) ⟨1405697, by rfl⟩ : syracuseStep 1874263 = 2811395) B2811395
theorem B12671437 : Blo 1665032 12671437 := bstep (se 3 (by rfl) ⟨2375894, by rfl⟩ : syracuseStep 12671437 = 4751789) B4751789
theorem B4217305 : Blo 1665032 4217305 := bstep (se 2 (by rfl) ⟨1581489, by rfl⟩ : syracuseStep 4217305 = 3162979) B3162979
theorem B1874443 : Blo 1665032 1874443 := bstep (se 1 (by rfl) ⟨1405832, by rfl⟩ : syracuseStep 1874443 = 2811665) B2811665
theorem B7600657 : Blo 1665032 7600657 := bstep (se 2 (by rfl) ⟨2850246, by rfl⟩ : syracuseStep 7600657 = 5700493) B5700493
theorem B5134871 : Blo 1665032 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B1899083 : Blo 1665032 1899083 := bstep (se 1 (by rfl) ⟨1424312, by rfl⟩ : syracuseStep 1899083 = 2848625) B2848625
theorem B1874551 : Blo 1665032 1874551 := bstep (se 1 (by rfl) ⟨1405913, by rfl⟩ : syracuseStep 1874551 = 2811827) B2811827
theorem B6322967 : Blo 1665032 6322967 := bstep (se 1 (by rfl) ⟨4742225, by rfl⟩ : syracuseStep 6322967 = 9484451) B9484451
theorem B1874731 : Blo 1665032 1874731 := bstep (se 1 (by rfl) ⟨1406048, by rfl⟩ : syracuseStep 1874731 = 2812097) B2812097
theorem B97327925 : Blo 1665032 97327925 := bstep (se 5 (by rfl) ⟨4562246, by rfl⟩ : syracuseStep 97327925 = 9124493) B9124493
theorem B1874839 : Blo 1665032 1874839 := bstep (se 1 (by rfl) ⟨1406129, by rfl⟩ : syracuseStep 1874839 = 2812259) B2812259
theorem B3161035 : Blo 1665032 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B2497559 : Blo 1665032 2497559 := bstep (se 1 (by rfl) ⟨1873169, by rfl⟩ : syracuseStep 2497559 = 3746339) B3746339
theorem B2497625 : Blo 1665032 2497625 := bstep (se 2 (by rfl) ⟨936609, by rfl⟩ : syracuseStep 2497625 = 1873219) B1873219
theorem B14236823 : Blo 1665032 14236823 := bstep (se 1 (by rfl) ⟨10677617, by rfl⟩ : syracuseStep 14236823 = 21355235) B21355235
theorem B1899703 : Blo 1665032 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B2497739 : Blo 1665032 2497739 := bstep (se 1 (by rfl) ⟨1873304, by rfl⟩ : syracuseStep 2497739 = 3746609) B3746609
theorem B2497751 : Blo 1665032 2497751 := bstep (se 1 (by rfl) ⟨1873313, by rfl⟩ : syracuseStep 2497751 = 3746627) B3746627
theorem B2497817 : Blo 1665032 2497817 := bstep (se 2 (by rfl) ⟨936681, by rfl⟩ : syracuseStep 2497817 = 1873363) B1873363
theorem B3161369 : Blo 1665032 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B4111667 : Blo 1665032 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B10132867 : Blo 1665032 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2497931 : Blo 1665032 2497931 := bstep (se 1 (by rfl) ⟨1873448, by rfl⟩ : syracuseStep 2497931 = 3746897) B3746897
theorem B2497943 : Blo 1665032 2497943 := bstep (se 1 (by rfl) ⟨1873457, by rfl⟩ : syracuseStep 2497943 = 3746915) B3746915
theorem B2137495 : Blo 1665032 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B2498009 : Blo 1665032 2498009 := bstep (se 2 (by rfl) ⟨936753, by rfl⟩ : syracuseStep 2498009 = 1873507) B1873507
theorem B1900055 : Blo 1665032 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B2498123 : Blo 1665032 2498123 := bstep (se 1 (by rfl) ⟨1873592, by rfl⟩ : syracuseStep 2498123 = 3747185) B3747185
theorem B2498135 : Blo 1665032 2498135 := bstep (se 1 (by rfl) ⟨1873601, by rfl⟩ : syracuseStep 2498135 = 3747203) B3747203
theorem B10821221 : Blo 1665032 10821221 := bstep (se 4 (by rfl) ⟨1014489, by rfl⟩ : syracuseStep 10821221 = 2028979) B2028979
theorem B2498201 : Blo 1665032 2498201 := bstep (se 2 (by rfl) ⟨936825, by rfl⟩ : syracuseStep 2498201 = 1873651) B1873651
theorem B2498315 : Blo 1665032 2498315 := bstep (se 1 (by rfl) ⟨1873736, by rfl⟩ : syracuseStep 2498315 = 3747473) B3747473
theorem B2498327 : Blo 1665032 2498327 := bstep (se 1 (by rfl) ⟨1873745, by rfl⟩ : syracuseStep 2498327 = 3747491) B3747491
theorem B2498393 : Blo 1665032 2498393 := bstep (se 2 (by rfl) ⟨936897, by rfl⟩ : syracuseStep 2498393 = 1873795) B1873795
theorem B3162007 : Blo 1665032 3162007 := bstep (se 1 (by rfl) ⟨2371505, by rfl⟩ : syracuseStep 3162007 = 4743011) B4743011
theorem B2498507 : Blo 1665032 2498507 := bstep (se 1 (by rfl) ⟨1873880, by rfl⟩ : syracuseStep 2498507 = 3747761) B3747761
theorem B2498519 : Blo 1665032 2498519 := bstep (se 1 (by rfl) ⟨1873889, by rfl⟩ : syracuseStep 2498519 = 3747779) B3747779
theorem B2498567 : Blo 1665032 2498567 := bstep (se 1 (by rfl) ⟨1873925, by rfl⟩ : syracuseStep 2498567 = 3747851) B3747851
theorem B2498603 : Blo 1665032 2498603 := bstep (se 1 (by rfl) ⟨1873952, by rfl⟩ : syracuseStep 2498603 = 3747905) B3747905
theorem B2498633 : Blo 1665032 2498633 := bstep (se 2 (by rfl) ⟨936987, by rfl⟩ : syracuseStep 2498633 = 1873975) B1873975
theorem B2809991 : Blo 1665032 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B4743353 : Blo 1665032 4743353 := bstep (se 2 (by rfl) ⟨1778757, by rfl⟩ : syracuseStep 4743353 = 3557515) B3557515
theorem B2498747 : Blo 1665032 2498747 := bstep (se 1 (by rfl) ⟨1874060, by rfl⟩ : syracuseStep 2498747 = 3748121) B3748121
theorem B6324425 : Blo 1665032 6324425 := bstep (se 2 (by rfl) ⟨2371659, by rfl⟩ : syracuseStep 6324425 = 4743319) B4743319
theorem B5857481 : Blo 1665032 5857481 := bstep (se 2 (by rfl) ⟨2196555, by rfl⟩ : syracuseStep 5857481 = 4393111) B4393111
theorem B2498807 : Blo 1665032 2498807 := bstep (se 1 (by rfl) ⟨1874105, by rfl⟩ : syracuseStep 2498807 = 3748211) B3748211
theorem B2498831 : Blo 1665032 2498831 := bstep (se 1 (by rfl) ⟨1874123, by rfl⟩ : syracuseStep 2498831 = 3748247) B3748247
theorem B4743467 : Blo 1665032 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B2498873 : Blo 1665032 2498873 := bstep (se 2 (by rfl) ⟨937077, by rfl⟩ : syracuseStep 2498873 = 1874155) B1874155
theorem B5620103 : Blo 1665032 5620103 := bstep (se 1 (by rfl) ⟨4215077, by rfl⟩ : syracuseStep 5620103 = 8430155) B8430155
theorem B2498951 : Blo 1665032 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B2498987 : Blo 1665032 2498987 := bstep (se 1 (by rfl) ⟨1874240, by rfl⟩ : syracuseStep 2498987 = 3748481) B3748481
theorem B2499017 : Blo 1665032 2499017 := bstep (se 2 (by rfl) ⟨937131, by rfl⟩ : syracuseStep 2499017 = 1874263) B1874263
theorem B2499131 : Blo 1665032 2499131 := bstep (se 1 (by rfl) ⟨1874348, by rfl⟩ : syracuseStep 2499131 = 3748697) B3748697
theorem B8004215 : Blo 1665032 8004215 := bstep (se 1 (by rfl) ⟨6003161, by rfl⟩ : syracuseStep 8004215 = 12006323) B12006323
theorem B2499191 : Blo 1665032 2499191 := bstep (se 1 (by rfl) ⟨1874393, by rfl⟩ : syracuseStep 2499191 = 3748787) B3748787
theorem B2499215 : Blo 1665032 2499215 := bstep (se 1 (by rfl) ⟨1874411, by rfl⟩ : syracuseStep 2499215 = 3748823) B3748823
theorem B2499257 : Blo 1665032 2499257 := bstep (se 2 (by rfl) ⟨937221, by rfl⟩ : syracuseStep 2499257 = 1874443) B1874443
theorem B10134209 : Blo 1665032 10134209 := bstep (se 2 (by rfl) ⟨3800328, by rfl⟩ : syracuseStep 10134209 = 7600657) B7600657
theorem B8430317 : Blo 1665032 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B5620481 : Blo 1665032 5620481 := bstep (se 2 (by rfl) ⟨2107680, by rfl⟩ : syracuseStep 5620481 = 4215361) B4215361
theorem B2499335 : Blo 1665032 2499335 := bstep (se 1 (by rfl) ⟨1874501, by rfl⟩ : syracuseStep 2499335 = 3749003) B3749003
theorem B2810639 : Blo 1665032 2810639 := bstep (se 1 (by rfl) ⟨2107979, by rfl⟩ : syracuseStep 2810639 = 4215959) B4215959
theorem B41067299 : Blo 1665032 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B2499371 : Blo 1665032 2499371 := bstep (se 1 (by rfl) ⟨1874528, by rfl⟩ : syracuseStep 2499371 = 3749057) B3749057
theorem B2499401 : Blo 1665032 2499401 := bstep (se 2 (by rfl) ⟨937275, by rfl⟩ : syracuseStep 2499401 = 1874551) B1874551
theorem B2532239 : Blo 1665032 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B2499515 : Blo 1665032 2499515 := bstep (se 1 (by rfl) ⟨1874636, by rfl⟩ : syracuseStep 2499515 = 3749273) B3749273
theorem B2499575 : Blo 1665032 2499575 := bstep (se 1 (by rfl) ⟨1874681, by rfl⟩ : syracuseStep 2499575 = 3749363) B3749363
theorem B2499599 : Blo 1665032 2499599 := bstep (se 1 (by rfl) ⟨1874699, by rfl⟩ : syracuseStep 2499599 = 3749399) B3749399
theorem B2499641 : Blo 1665032 2499641 := bstep (se 2 (by rfl) ⟨937365, by rfl⟩ : syracuseStep 2499641 = 1874731) B1874731
theorem B68363351 : Blo 1665032 68363351 := bstep (se 1 (by rfl) ⟨51272513, by rfl⟩ : syracuseStep 68363351 = 102545027) B102545027
theorem B2499719 : Blo 1665032 2499719 := bstep (se 1 (by rfl) ⟨1874789, by rfl⟩ : syracuseStep 2499719 = 3749579) B3749579
theorem B3163283 : Blo 1665032 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B2499755 : Blo 1665032 2499755 := bstep (se 1 (by rfl) ⟨1874816, by rfl⟩ : syracuseStep 2499755 = 3749633) B3749633
theorem B2499785 : Blo 1665032 2499785 := bstep (se 2 (by rfl) ⟨937419, by rfl⟩ : syracuseStep 2499785 = 1874839) B1874839
theorem B2811179 : Blo 1665032 2811179 := bstep (se 1 (by rfl) ⟨2108384, by rfl⟩ : syracuseStep 2811179 = 4216769) B4216769
theorem B3163511 : Blo 1665032 3163511 := bstep (se 1 (by rfl) ⟨2372633, by rfl⟩ : syracuseStep 3163511 = 4745267) B4745267
theorem B2532743 : Blo 1665032 2532743 := bstep (se 1 (by rfl) ⟨1899557, by rfl⟩ : syracuseStep 2532743 = 3799115) B3799115
theorem B4744595 : Blo 1665032 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B7595417 : Blo 1665032 7595417 := bstep (se 2 (by rfl) ⟨2848281, by rfl⟩ : syracuseStep 7595417 = 5696563) B5696563
theorem B8431127 : Blo 1665032 8431127 := bstep (se 1 (by rfl) ⟨6323345, by rfl⟩ : syracuseStep 8431127 = 12646691) B12646691
theorem B5064221 : Blo 1665032 5064221 := bstep (se 3 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 5064221 = 1899083) B1899083
theorem B5621291 : Blo 1665032 5621291 := bstep (se 1 (by rfl) ⟨4215968, by rfl⟩ : syracuseStep 5621291 = 8431937) B8431937
theorem B69338699 : Blo 1665032 69338699 := bstep (se 1 (by rfl) ⟨52004024, by rfl⟩ : syracuseStep 69338699 = 104008049) B104008049
theorem B10815095 : Blo 1665032 10815095 := bstep (se 1 (by rfl) ⟨8111321, by rfl⟩ : syracuseStep 10815095 = 16222643) B16222643
theorem B2811577 : Blo 1665032 2811577 := bstep (se 2 (by rfl) ⟨1054341, by rfl⟩ : syracuseStep 2811577 = 2108683) B2108683
theorem B4744993 : Blo 1665032 4744993 := bstep (se 2 (by rfl) ⟨1779372, by rfl⟩ : syracuseStep 4744993 = 3558745) B3558745
theorem B13510489 : Blo 1665032 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B6326201 : Blo 1665032 6326201 := bstep (se 2 (by rfl) ⟨2372325, by rfl⟩ : syracuseStep 6326201 = 4744651) B4744651
theorem B1665039 : Blo 1665032 1665039 := bstep (se 1 (by rfl) ⟨1248779, by rfl⟩ : syracuseStep 1665039 = 2497559) B2497559
theorem B1665083 : Blo 1665032 1665083 := bstep (se 1 (by rfl) ⟨1248812, by rfl⟩ : syracuseStep 1665083 = 2497625) B2497625
theorem B1665159 : Blo 1665032 1665159 := bstep (se 1 (by rfl) ⟨1248869, by rfl⟩ : syracuseStep 1665159 = 2497739) B2497739
theorem B1665167 : Blo 1665032 1665167 := bstep (se 1 (by rfl) ⟨1248875, by rfl⟩ : syracuseStep 1665167 = 2497751) B2497751
theorem B1665211 : Blo 1665032 1665211 := bstep (se 1 (by rfl) ⟨1248908, by rfl⟩ : syracuseStep 1665211 = 2497817) B2497817
theorem B1665287 : Blo 1665032 1665287 := bstep (se 1 (by rfl) ⟨1248965, by rfl⟩ : syracuseStep 1665287 = 2497931) B2497931
theorem B1665295 : Blo 1665032 1665295 := bstep (se 1 (by rfl) ⟨1248971, by rfl⟩ : syracuseStep 1665295 = 2497943) B2497943
theorem B24332561 : Blo 1665032 24332561 := bstep (se 2 (by rfl) ⟨9124710, by rfl⟩ : syracuseStep 24332561 = 18249421) B18249421
theorem B76900661 : Blo 1665032 76900661 := bstep (se 5 (by rfl) ⟨3604718, by rfl⟩ : syracuseStep 76900661 = 7209437) B7209437
theorem B1665339 : Blo 1665032 1665339 := bstep (se 1 (by rfl) ⟨1249004, by rfl⟩ : syracuseStep 1665339 = 2498009) B2498009
theorem B1665415 : Blo 1665032 1665415 := bstep (se 1 (by rfl) ⟨1249061, by rfl⟩ : syracuseStep 1665415 = 2498123) B2498123
theorem B1665423 : Blo 1665032 1665423 := bstep (se 1 (by rfl) ⟨1249067, by rfl⟩ : syracuseStep 1665423 = 2498135) B2498135
theorem B2001295 : Blo 1665032 2001295 := bstep (se 1 (by rfl) ⟨1500971, by rfl⟩ : syracuseStep 2001295 = 3001943) B3001943
theorem B9488825 : Blo 1665032 9488825 := bstep (se 2 (by rfl) ⟨3558309, by rfl⟩ : syracuseStep 9488825 = 7116619) B7116619
theorem B1665467 : Blo 1665032 1665467 := bstep (se 1 (by rfl) ⟨1249100, by rfl⟩ : syracuseStep 1665467 = 2498201) B2498201
theorem B1665543 : Blo 1665032 1665543 := bstep (se 1 (by rfl) ⟨1249157, by rfl⟩ : syracuseStep 1665543 = 2498315) B2498315
theorem B3000847 : Blo 1665032 3000847 := bstep (se 1 (by rfl) ⟨2250635, by rfl⟩ : syracuseStep 3000847 = 4501271) B4501271
theorem B1665551 : Blo 1665032 1665551 := bstep (se 1 (by rfl) ⟨1249163, by rfl⟩ : syracuseStep 1665551 = 2498327) B2498327
theorem B1665595 : Blo 1665032 1665595 := bstep (se 1 (by rfl) ⟨1249196, by rfl⟩ : syracuseStep 1665595 = 2498393) B2498393
theorem B6408791 : Blo 1665032 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B1665671 : Blo 1665032 1665671 := bstep (se 1 (by rfl) ⟨1249253, by rfl⟩ : syracuseStep 1665671 = 2498507) B2498507
theorem B1665679 : Blo 1665032 1665679 := bstep (se 1 (by rfl) ⟨1249259, by rfl⟩ : syracuseStep 1665679 = 2498519) B2498519
theorem B5065363 : Blo 1665032 5065363 := bstep (se 1 (by rfl) ⟨3799022, by rfl⟩ : syracuseStep 5065363 = 7598045) B7598045
theorem B1665723 : Blo 1665032 1665723 := bstep (se 1 (by rfl) ⟨1249292, by rfl⟩ : syracuseStep 1665723 = 2498585) B2498585
theorem B1665799 : Blo 1665032 1665799 := bstep (se 1 (by rfl) ⟨1249349, by rfl⟩ : syracuseStep 1665799 = 2498699) B2498699
theorem B1665807 : Blo 1665032 1665807 := bstep (se 1 (by rfl) ⟨1249355, by rfl⟩ : syracuseStep 1665807 = 2498711) B2498711
theorem B1665851 : Blo 1665032 1665851 := bstep (se 1 (by rfl) ⟨1249388, by rfl⟩ : syracuseStep 1665851 = 2498777) B2498777
theorem B5622587 : Blo 1665032 5622587 := bstep (se 1 (by rfl) ⟨4216940, by rfl⟩ : syracuseStep 5622587 = 8433881) B8433881
theorem B18017099 : Blo 1665032 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B1665927 : Blo 1665032 1665927 := bstep (se 1 (by rfl) ⟨1249445, by rfl⟩ : syracuseStep 1665927 = 2498891) B2498891
theorem B1665935 : Blo 1665032 1665935 := bstep (se 1 (by rfl) ⟨1249451, by rfl⟩ : syracuseStep 1665935 = 2498903) B2498903
theorem B1665979 : Blo 1665032 1665979 := bstep (se 1 (by rfl) ⟨1249484, by rfl⟩ : syracuseStep 1665979 = 2498969) B2498969
theorem B1666055 : Blo 1665032 1666055 := bstep (se 1 (by rfl) ⟨1249541, by rfl⟩ : syracuseStep 1666055 = 2499083) B2499083
theorem B1666063 : Blo 1665032 1666063 := bstep (se 1 (by rfl) ⟨1249547, by rfl⟩ : syracuseStep 1666063 = 2499095) B2499095
theorem B5336093 : Blo 1665032 5336093 := bstep (se 3 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 5336093 = 2001035) B2001035
theorem B1666107 : Blo 1665032 1666107 := bstep (se 1 (by rfl) ⟨1249580, by rfl⟩ : syracuseStep 1666107 = 2499161) B2499161
theorem B3746951 : Blo 1665032 3746951 := bstep (se 1 (by rfl) ⟨2810213, by rfl⟩ : syracuseStep 3746951 = 5620427) B5620427
theorem B1666183 : Blo 1665032 1666183 := bstep (se 1 (by rfl) ⟨1249637, by rfl⟩ : syracuseStep 1666183 = 2499275) B2499275
theorem B1666191 : Blo 1665032 1666191 := bstep (se 1 (by rfl) ⟨1249643, by rfl⟩ : syracuseStep 1666191 = 2499287) B2499287
theorem B2108587 : Blo 1665032 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B1666235 : Blo 1665032 1666235 := bstep (se 1 (by rfl) ⟨1249676, by rfl⟩ : syracuseStep 1666235 = 2499353) B2499353
theorem B1666311 : Blo 1665032 1666311 := bstep (se 1 (by rfl) ⟨1249733, by rfl⟩ : syracuseStep 1666311 = 2499467) B2499467
theorem B1666319 : Blo 1665032 1666319 := bstep (se 1 (by rfl) ⟨1249739, by rfl⟩ : syracuseStep 1666319 = 2499479) B2499479
theorem B16895249 : Blo 1665032 16895249 := bstep (se 2 (by rfl) ⟨6335718, by rfl⟩ : syracuseStep 16895249 = 12671437) B12671437
theorem B5623073 : Blo 1665032 5623073 := bstep (se 2 (by rfl) ⟨2108652, by rfl⟩ : syracuseStep 5623073 = 4217305) B4217305
theorem B3747131 : Blo 1665032 3747131 := bstep (se 1 (by rfl) ⟨2810348, by rfl⟩ : syracuseStep 3747131 = 5620697) B5620697
theorem B1666363 : Blo 1665032 1666363 := bstep (se 1 (by rfl) ⟨1249772, by rfl⟩ : syracuseStep 1666363 = 2499545) B2499545
theorem B1666439 : Blo 1665032 1666439 := bstep (se 1 (by rfl) ⟨1249829, by rfl⟩ : syracuseStep 1666439 = 2499659) B2499659
theorem B1666447 : Blo 1665032 1666447 := bstep (se 1 (by rfl) ⟨1249835, by rfl⟩ : syracuseStep 1666447 = 2499671) B2499671
theorem B4001177 : Blo 1665032 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B6753689 : Blo 1665032 6753689 := bstep (se 2 (by rfl) ⟨2532633, by rfl⟩ : syracuseStep 6753689 = 5065267) B5065267
theorem B3747257 : Blo 1665032 3747257 := bstep (se 2 (by rfl) ⟨1405221, by rfl⟩ : syracuseStep 3747257 = 2810443) B2810443
theorem B1666491 : Blo 1665032 1666491 := bstep (se 1 (by rfl) ⟨1249868, by rfl⟩ : syracuseStep 1666491 = 2499737) B2499737
theorem B20254157 : Blo 1665032 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B4001339 : Blo 1665032 4001339 := bstep (se 1 (by rfl) ⟨3001004, by rfl⟩ : syracuseStep 4001339 = 6002009) B6002009
theorem B3747599 : Blo 1665032 3747599 := bstep (se 1 (by rfl) ⟨2810699, by rfl⟩ : syracuseStep 3747599 = 5621399) B5621399
theorem B3747617 : Blo 1665032 3747617 := bstep (se 2 (by rfl) ⟨1405356, by rfl⟩ : syracuseStep 3747617 = 2810713) B2810713
theorem B8548129 : Blo 1665032 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B5623667 : Blo 1665032 5623667 := bstep (se 1 (by rfl) ⟨4217750, by rfl⟩ : syracuseStep 5623667 = 8435501) B8435501
theorem B4214663 : Blo 1665032 4214663 := bstep (se 1 (by rfl) ⟨3160997, by rfl⟩ : syracuseStep 4214663 = 6321995) B6321995
theorem B3043207 : Blo 1665032 3043207 := bstep (se 1 (by rfl) ⟨2282405, by rfl⟩ : syracuseStep 3043207 = 4564811) B4564811
theorem B4214713 : Blo 1665032 4214713 := bstep (se 2 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 4214713 = 3161035) B3161035
theorem B5410745 : Blo 1665032 5410745 := bstep (se 2 (by rfl) ⟨2029029, by rfl⟩ : syracuseStep 5410745 = 4058059) B4058059
theorem B13692989 : Blo 1665032 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B5066813 : Blo 1665032 5066813 := bstep (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) B1900055
theorem B3747959 : Blo 1665032 3747959 := bstep (se 1 (by rfl) ⟨2810969, by rfl⟩ : syracuseStep 3747959 = 5621939) B5621939
theorem B2371847 : Blo 1665032 2371847 := bstep (se 1 (by rfl) ⟨1778885, by rfl⟩ : syracuseStep 2371847 = 3557771) B3557771
theorem B3748139 : Blo 1665032 3748139 := bstep (se 1 (by rfl) ⟨2811104, by rfl⟩ : syracuseStep 3748139 = 5622209) B5622209
theorem B2372041 : Blo 1665032 2372041 := bstep (se 2 (by rfl) ⟨889515, by rfl⟩ : syracuseStep 2372041 = 1779031) B1779031
theorem B12653009 : Blo 1665032 12653009 := bstep (se 2 (by rfl) ⟨4744878, by rfl⟩ : syracuseStep 12653009 = 9489757) B9489757
theorem B4215311 : Blo 1665032 4215311 := bstep (se 1 (by rfl) ⟨3161483, by rfl⟩ : syracuseStep 4215311 = 6322967) B6322967
theorem B8434205 : Blo 1665032 8434205 := bstep (se 3 (by rfl) ⟨1581413, by rfl⟩ : syracuseStep 8434205 = 3162827) B3162827
theorem B64885283 : Blo 1665032 64885283 := bstep (se 1 (by rfl) ⟨48663962, by rfl⟩ : syracuseStep 64885283 = 97327925) B97327925
theorem B14430797 : Blo 1665032 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B3748499 : Blo 1665032 3748499 := bstep (se 1 (by rfl) ⟨2811374, by rfl⟩ : syracuseStep 3748499 = 5622749) B5622749
theorem B3748553 : Blo 1665032 3748553 := bstep (se 2 (by rfl) ⟨1405707, by rfl⟩ : syracuseStep 3748553 = 2811415) B2811415
theorem B9491215 : Blo 1665032 9491215 := bstep (se 1 (by rfl) ⟨7118411, by rfl⟩ : syracuseStep 9491215 = 14236823) B14236823
theorem B12825395 : Blo 1665032 12825395 := bstep (se 1 (by rfl) ⟨9619046, by rfl⟩ : syracuseStep 12825395 = 19238093) B19238093
theorem B2741111 : Blo 1665032 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B2372599 : Blo 1665032 2372599 := bstep (se 1 (by rfl) ⟨1779449, by rfl⟩ : syracuseStep 2372599 = 3558899) B3558899
theorem B8434691 : Blo 1665032 8434691 := bstep (se 1 (by rfl) ⟨6326018, by rfl⟩ : syracuseStep 8434691 = 12652037) B12652037
theorem B7214147 : Blo 1665032 7214147 := bstep (se 1 (by rfl) ⟨5410610, by rfl⟩ : syracuseStep 7214147 = 10821221) B10821221
theorem B4502675 : Blo 1665032 4502675 := bstep (se 1 (by rfl) ⟨3377006, by rfl⟩ : syracuseStep 4502675 = 6754013) B6754013
theorem B4216009 : Blo 1665032 4216009 := bstep (se 2 (by rfl) ⟨1581003, by rfl⟩ : syracuseStep 4216009 = 3162007) B3162007
theorem B2667791 : Blo 1665032 2667791 := bstep (se 1 (by rfl) ⟨2000843, by rfl⟩ : syracuseStep 2667791 = 4001687) B4001687
theorem B4216151 : Blo 1665032 4216151 := bstep (se 1 (by rfl) ⟨3162113, by rfl⟩ : syracuseStep 4216151 = 6324227) B6324227
theorem B3749255 : Blo 1665032 3749255 := bstep (se 1 (by rfl) ⟨2811941, by rfl⟩ : syracuseStep 3749255 = 5623883) B5623883
theorem B24016337 : Blo 1665032 24016337 := bstep (se 2 (by rfl) ⟨9006126, by rfl⟩ : syracuseStep 24016337 = 18012253) B18012253
theorem B3749435 : Blo 1665032 3749435 := bstep (se 1 (by rfl) ⟨2812076, by rfl⟩ : syracuseStep 3749435 = 5624153) B5624153
theorem B1873543 : Blo 1665032 1873543 := bstep (se 1 (by rfl) ⟨1405157, by rfl⟩ : syracuseStep 1873543 = 2810315) B2810315
theorem B3749561 : Blo 1665032 3749561 := bstep (se 2 (by rfl) ⟨1406085, by rfl⟩ : syracuseStep 3749561 = 2812171) B2812171
theorem B1873723 : Blo 1665032 1873723 := bstep (se 1 (by rfl) ⟨1405292, by rfl⟩ : syracuseStep 1873723 = 2810585) B2810585
theorem B11392883 : Blo 1665032 11392883 := bstep (se 1 (by rfl) ⟨8544662, by rfl⟩ : syracuseStep 11392883 = 17089325) B17089325
theorem B2250667 : Blo 1665032 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B5699627 : Blo 1665032 5699627 := bstep (se 1 (by rfl) ⟨4274720, by rfl⟩ : syracuseStep 5699627 = 8549441) B8549441
theorem B1874191 : Blo 1665032 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B21346577 : Blo 1665032 21346577 := bstep (se 2 (by rfl) ⟨8004966, by rfl⟩ : syracuseStep 21346577 = 16009933) B16009933
theorem B10131749 : Blo 1665032 10131749 := bstep (se 4 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 10131749 = 1899703) B1899703
theorem B8436311 : Blo 1665032 8436311 := bstep (se 1 (by rfl) ⟨6327233, by rfl⟩ : syracuseStep 8436311 = 12654467) B12654467
theorem B2136823 : Blo 1665032 2136823 := bstep (se 1 (by rfl) ⟨1602617, by rfl⟩ : syracuseStep 2136823 = 3205235) B3205235
theorem B1874695 : Blo 1665032 1874695 := bstep (se 1 (by rfl) ⟨1406021, by rfl⟩ : syracuseStep 1874695 = 2812043) B2812043
theorem B10132283 : Blo 1665032 10132283 := bstep (se 1 (by rfl) ⟨7599212, by rfl⟩ : syracuseStep 10132283 = 15198425) B15198425
theorem B2669431 : Blo 1665032 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B9485201 : Blo 1665032 9485201 := bstep (se 2 (by rfl) ⟨3556950, by rfl⟩ : syracuseStep 9485201 = 7113901) B7113901
theorem B2497595 : Blo 1665032 2497595 := bstep (se 1 (by rfl) ⟨1873196, by rfl⟩ : syracuseStep 2497595 = 3746393) B3746393
theorem B27016253 : Blo 1665032 27016253 := bstep (se 3 (by rfl) ⟨5065547, by rfl⟩ : syracuseStep 27016253 = 10131095) B10131095
theorem B8436797 : Blo 1665032 8436797 := bstep (se 3 (by rfl) ⟨1581899, by rfl⟩ : syracuseStep 8436797 = 3163799) B3163799
theorem B2497655 : Blo 1665032 2497655 := bstep (se 1 (by rfl) ⟨1873241, by rfl⟩ : syracuseStep 2497655 = 3746483) B3746483
theorem B2497679 : Blo 1665032 2497679 := bstep (se 1 (by rfl) ⟨1873259, by rfl⟩ : syracuseStep 2497679 = 3746519) B3746519
theorem B2497721 : Blo 1665032 2497721 := bstep (se 2 (by rfl) ⟨936645, by rfl⟩ : syracuseStep 2497721 = 1873291) B1873291
theorem B2849993 : Blo 1665032 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B2497799 : Blo 1665032 2497799 := bstep (se 1 (by rfl) ⟨1873349, by rfl⟩ : syracuseStep 2497799 = 3746699) B3746699
theorem B2497835 : Blo 1665032 2497835 := bstep (se 1 (by rfl) ⟨1873376, by rfl⟩ : syracuseStep 2497835 = 3746753) B3746753
theorem B2252089 : Blo 1665032 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B2497865 : Blo 1665032 2497865 := bstep (se 2 (by rfl) ⟨936699, by rfl⟩ : syracuseStep 2497865 = 1873399) B1873399
theorem B9485657 : Blo 1665032 9485657 := bstep (se 2 (by rfl) ⟨3557121, by rfl⟩ : syracuseStep 9485657 = 7114243) B7114243
theorem B4218227 : Blo 1665032 4218227 := bstep (se 1 (by rfl) ⟨3163670, by rfl⟩ : syracuseStep 4218227 = 6327341) B6327341
theorem B18980243 : Blo 1665032 18980243 := bstep (se 1 (by rfl) ⟨14235182, by rfl⟩ : syracuseStep 18980243 = 28470365) B28470365
theorem B16006585 : Blo 1665032 16006585 := bstep (se 2 (by rfl) ⟨6002469, by rfl⟩ : syracuseStep 16006585 = 12004939) B12004939
theorem B2497979 : Blo 1665032 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B2498039 : Blo 1665032 2498039 := bstep (se 1 (by rfl) ⟨1873529, by rfl⟩ : syracuseStep 2498039 = 3747059) B3747059
theorem B2498063 : Blo 1665032 2498063 := bstep (se 1 (by rfl) ⟨1873547, by rfl⟩ : syracuseStep 2498063 = 3747095) B3747095
theorem B6323741 : Blo 1665032 6323741 := bstep (se 3 (by rfl) ⟨1185701, by rfl⟩ : syracuseStep 6323741 = 2371403) B2371403
theorem B2498105 : Blo 1665032 2498105 := bstep (se 2 (by rfl) ⟨936789, by rfl⟩ : syracuseStep 2498105 = 1873579) B1873579
theorem B2498183 : Blo 1665032 2498183 := bstep (se 1 (by rfl) ⟨1873637, by rfl⟩ : syracuseStep 2498183 = 3747275) B3747275
theorem B2498219 : Blo 1665032 2498219 := bstep (se 1 (by rfl) ⟨1873664, by rfl⟩ : syracuseStep 2498219 = 3747329) B3747329
theorem B2498249 : Blo 1665032 2498249 := bstep (se 2 (by rfl) ⟨936843, by rfl⟩ : syracuseStep 2498249 = 1873687) B1873687
theorem B8429345 : Blo 1665032 8429345 := bstep (se 2 (by rfl) ⟨3161004, by rfl⟩ : syracuseStep 8429345 = 6322009) B6322009
theorem B9879329 : Blo 1665032 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B19234597 : Blo 1665032 19234597 := bstep (se 4 (by rfl) ⟨1803243, by rfl⟩ : syracuseStep 19234597 = 3606487) B3606487
theorem B2498363 : Blo 1665032 2498363 := bstep (se 1 (by rfl) ⟨1873772, by rfl⟩ : syracuseStep 2498363 = 3747545) B3747545
theorem B2498423 : Blo 1665032 2498423 := bstep (se 1 (by rfl) ⟨1873817, by rfl⟩ : syracuseStep 2498423 = 3747635) B3747635
theorem B2498447 : Blo 1665032 2498447 := bstep (se 1 (by rfl) ⟨1873835, by rfl⟩ : syracuseStep 2498447 = 3747671) B3747671
theorem B2498489 : Blo 1665032 2498489 := bstep (se 2 (by rfl) ⟨936933, by rfl⟩ : syracuseStep 2498489 = 1873867) B1873867
theorem B2498639 : Blo 1665032 2498639 := bstep (se 1 (by rfl) ⟨1873979, by rfl⟩ : syracuseStep 2498639 = 3747959) B3747959
theorem B3162235 : Blo 1665032 3162235 := bstep (se 1 (by rfl) ⟨2371676, by rfl⟩ : syracuseStep 3162235 = 4743353) B4743353
theorem B3162311 : Blo 1665032 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B2498759 : Blo 1665032 2498759 := bstep (se 1 (by rfl) ⟨1874069, by rfl⟩ : syracuseStep 2498759 = 3748139) B3748139
theorem B2810207 : Blo 1665032 2810207 := bstep (se 1 (by rfl) ⟨2107655, by rfl⟩ : syracuseStep 2810207 = 4215311) B4215311
theorem B2498921 : Blo 1665032 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B2498999 : Blo 1665032 2498999 := bstep (se 1 (by rfl) ⟨1874249, by rfl⟩ : syracuseStep 2498999 = 3748499) B3748499
theorem B2499035 : Blo 1665032 2499035 := bstep (se 1 (by rfl) ⟨1874276, by rfl⟩ : syracuseStep 2499035 = 3748553) B3748553
theorem B5620211 : Blo 1665032 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B27378199 : Blo 1665032 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B1827407 : Blo 1665032 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B1688159 : Blo 1665032 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B3162721 : Blo 1665032 3162721 := bstep (se 2 (by rfl) ⟨1186020, by rfl⟩ : syracuseStep 3162721 = 2372041) B2372041
theorem B6324925 : Blo 1665032 6324925 := bstep (se 3 (by rfl) ⟨1185923, by rfl⟩ : syracuseStep 6324925 = 2371847) B2371847
theorem B4809431 : Blo 1665032 4809431 := bstep (se 1 (by rfl) ⟨3607073, by rfl⟩ : syracuseStep 4809431 = 7214147) B7214147
theorem B1778527 : Blo 1665032 1778527 := bstep (se 1 (by rfl) ⟨1333895, by rfl⟩ : syracuseStep 1778527 = 2667791) B2667791
theorem B2810767 : Blo 1665032 2810767 := bstep (se 1 (by rfl) ⟨2108075, by rfl⟩ : syracuseStep 2810767 = 4216151) B4216151
theorem B1688495 : Blo 1665032 1688495 := bstep (se 1 (by rfl) ⟨1266371, by rfl⟩ : syracuseStep 1688495 = 2532743) B2532743
theorem B2499503 : Blo 1665032 2499503 := bstep (se 1 (by rfl) ⟨1874627, by rfl⟩ : syracuseStep 2499503 = 3749255) B3749255
theorem B3163063 : Blo 1665032 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B2499593 : Blo 1665032 2499593 := bstep (se 2 (by rfl) ⟨937347, by rfl⟩ : syracuseStep 2499593 = 1874695) B1874695
theorem B5620751 : Blo 1665032 5620751 := bstep (se 1 (by rfl) ⟨4215563, by rfl⟩ : syracuseStep 5620751 = 8431127) B8431127
theorem B2499623 : Blo 1665032 2499623 := bstep (se 1 (by rfl) ⟨1874717, by rfl⟩ : syracuseStep 2499623 = 3749435) B3749435
theorem B7210063 : Blo 1665032 7210063 := bstep (se 1 (by rfl) ⟨5407547, by rfl⟩ : syracuseStep 7210063 = 10815095) B10815095
theorem B2499707 : Blo 1665032 2499707 := bstep (se 1 (by rfl) ⟨1874780, by rfl⟩ : syracuseStep 2499707 = 3749561) B3749561
theorem B7595255 : Blo 1665032 7595255 := bstep (se 1 (by rfl) ⟨5696441, by rfl⟩ : syracuseStep 7595255 = 11392883) B11392883
theorem B11396389 : Blo 1665032 11396389 := bstep (se 4 (by rfl) ⟨1068411, by rfl⟩ : syracuseStep 11396389 = 2136823) B2136823
theorem B3163465 : Blo 1665032 3163465 := bstep (se 2 (by rfl) ⟨1186299, by rfl⟩ : syracuseStep 3163465 = 2372599) B2372599
theorem B16221707 : Blo 1665032 16221707 := bstep (se 1 (by rfl) ⟨12166280, by rfl⟩ : syracuseStep 16221707 = 24332561) B24332561
theorem B14231051 : Blo 1665032 14231051 := bstep (se 1 (by rfl) ⟨10673288, by rfl⟩ : syracuseStep 14231051 = 21346577) B21346577
theorem B51267107 : Blo 1665032 51267107 := bstep (se 1 (by rfl) ⟨38450330, by rfl⟩ : syracuseStep 51267107 = 76900661) B76900661
theorem B2811449 : Blo 1665032 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B5621345 : Blo 1665032 5621345 := bstep (se 2 (by rfl) ⟨2108004, by rfl⟩ : syracuseStep 5621345 = 4216009) B4216009
theorem B6325883 : Blo 1665032 6325883 := bstep (se 1 (by rfl) ⟨4744412, by rfl⟩ : syracuseStep 6325883 = 9488825) B9488825
theorem B12011141 : Blo 1665032 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B12011399 : Blo 1665032 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B21342113 : Blo 1665032 21342113 := bstep (se 2 (by rfl) ⟨8003292, by rfl⟩ : syracuseStep 21342113 = 16006585) B16006585
theorem B3557395 : Blo 1665032 3557395 := bstep (se 1 (by rfl) ⟨2668046, by rfl⟩ : syracuseStep 3557395 = 5336093) B5336093
theorem B1665063 : Blo 1665032 1665063 := bstep (se 1 (by rfl) ⟨1248797, by rfl⟩ : syracuseStep 1665063 = 2497595) B2497595
theorem B1665103 : Blo 1665032 1665103 := bstep (se 1 (by rfl) ⟨1248827, by rfl⟩ : syracuseStep 1665103 = 2497655) B2497655
theorem B1665119 : Blo 1665032 1665119 := bstep (se 1 (by rfl) ⟨1248839, by rfl⟩ : syracuseStep 1665119 = 2497679) B2497679
theorem B1665147 : Blo 1665032 1665147 := bstep (se 1 (by rfl) ⟨1248860, by rfl⟩ : syracuseStep 1665147 = 2497721) B2497721
theorem B1665199 : Blo 1665032 1665199 := bstep (se 1 (by rfl) ⟨1248899, by rfl⟩ : syracuseStep 1665199 = 2497799) B2497799
theorem B1665223 : Blo 1665032 1665223 := bstep (se 1 (by rfl) ⟨1248917, by rfl⟩ : syracuseStep 1665223 = 2497835) B2497835
theorem B1665243 : Blo 1665032 1665243 := bstep (se 1 (by rfl) ⟨1248932, by rfl⟩ : syracuseStep 1665243 = 2497865) B2497865
theorem B2812151 : Blo 1665032 2812151 := bstep (se 1 (by rfl) ⟨2109113, by rfl⟩ : syracuseStep 2812151 = 4218227) B4218227
theorem B1665319 : Blo 1665032 1665319 := bstep (se 1 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 1665319 = 2497979) B2497979
theorem B13502771 : Blo 1665032 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B1665359 : Blo 1665032 1665359 := bstep (se 1 (by rfl) ⟨1249019, by rfl⟩ : syracuseStep 1665359 = 2498039) B2498039
theorem B1665375 : Blo 1665032 1665375 := bstep (se 1 (by rfl) ⟨1249031, by rfl⟩ : syracuseStep 1665375 = 2498063) B2498063
theorem B1665403 : Blo 1665032 1665403 := bstep (se 1 (by rfl) ⟨1249052, by rfl⟩ : syracuseStep 1665403 = 2498105) B2498105
theorem B11397505 : Blo 1665032 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B6326657 : Blo 1665032 6326657 := bstep (se 2 (by rfl) ⟨2372496, by rfl⟩ : syracuseStep 6326657 = 4744993) B4744993
theorem B1665455 : Blo 1665032 1665455 := bstep (se 1 (by rfl) ⟨1249091, by rfl⟩ : syracuseStep 1665455 = 2498183) B2498183
theorem B1665479 : Blo 1665032 1665479 := bstep (se 1 (by rfl) ⟨1249109, by rfl⟩ : syracuseStep 1665479 = 2498219) B2498219
theorem B1665499 : Blo 1665032 1665499 := bstep (se 1 (by rfl) ⟨1249124, by rfl⟩ : syracuseStep 1665499 = 2498249) B2498249
theorem B4057609 : Blo 1665032 4057609 := bstep (se 2 (by rfl) ⟨1521603, by rfl⟩ : syracuseStep 4057609 = 3043207) B3043207
theorem B1665575 : Blo 1665032 1665575 := bstep (se 1 (by rfl) ⟨1249181, by rfl⟩ : syracuseStep 1665575 = 2498363) B2498363
theorem B3000889 : Blo 1665032 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B1665615 : Blo 1665032 1665615 := bstep (se 1 (by rfl) ⟨1249211, by rfl⟩ : syracuseStep 1665615 = 2498423) B2498423
theorem B1665631 : Blo 1665032 1665631 := bstep (se 1 (by rfl) ⟨1249223, by rfl⟩ : syracuseStep 1665631 = 2498447) B2498447
theorem B1665659 : Blo 1665032 1665659 := bstep (se 1 (by rfl) ⟨1249244, by rfl⟩ : syracuseStep 1665659 = 2498489) B2498489
theorem B3607163 : Blo 1665032 3607163 := bstep (se 1 (by rfl) ⟨2705372, by rfl⟩ : syracuseStep 3607163 = 5410745) B5410745
theorem B1665711 : Blo 1665032 1665711 := bstep (se 1 (by rfl) ⟨1249283, by rfl⟩ : syracuseStep 1665711 = 2498567) B2498567
theorem B1665735 : Blo 1665032 1665735 := bstep (se 1 (by rfl) ⟨1249301, by rfl⟩ : syracuseStep 1665735 = 2498603) B2498603
theorem B9128659 : Blo 1665032 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B3377875 : Blo 1665032 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B1665755 : Blo 1665032 1665755 := bstep (se 1 (by rfl) ⟨1249316, by rfl⟩ : syracuseStep 1665755 = 2498633) B2498633
theorem B1665831 : Blo 1665032 1665831 := bstep (se 1 (by rfl) ⟨1249373, by rfl⟩ : syracuseStep 1665831 = 2498747) B2498747
theorem B1665871 : Blo 1665032 1665871 := bstep (se 1 (by rfl) ⟨1249403, by rfl⟩ : syracuseStep 1665871 = 2498807) B2498807
theorem B1665887 : Blo 1665032 1665887 := bstep (se 1 (by rfl) ⟨1249415, by rfl⟩ : syracuseStep 1665887 = 2498831) B2498831
theorem B1665915 : Blo 1665032 1665915 := bstep (se 1 (by rfl) ⟨1249436, by rfl⟩ : syracuseStep 1665915 = 2498873) B2498873
theorem B3746735 : Blo 1665032 3746735 := bstep (se 1 (by rfl) ⟨2810051, by rfl⟩ : syracuseStep 3746735 = 5620103) B5620103
theorem B1665967 : Blo 1665032 1665967 := bstep (se 1 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 1665967 = 2498951) B2498951
theorem B1665991 : Blo 1665032 1665991 := bstep (se 1 (by rfl) ⟨1249493, by rfl⟩ : syracuseStep 1665991 = 2498987) B2498987
theorem B1666011 : Blo 1665032 1666011 := bstep (se 1 (by rfl) ⟨1249508, by rfl⟩ : syracuseStep 1666011 = 2499017) B2499017
theorem B5622803 : Blo 1665032 5622803 := bstep (se 1 (by rfl) ⟨4217102, by rfl⟩ : syracuseStep 5622803 = 8434205) B8434205
theorem B43256855 : Blo 1665032 43256855 := bstep (se 1 (by rfl) ⟨32442641, by rfl⟩ : syracuseStep 43256855 = 64885283) B64885283
theorem B1666087 : Blo 1665032 1666087 := bstep (se 1 (by rfl) ⟨1249565, by rfl⟩ : syracuseStep 1666087 = 2499131) B2499131
theorem B9620531 : Blo 1665032 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B1666127 : Blo 1665032 1666127 := bstep (se 1 (by rfl) ⟨1249595, by rfl⟩ : syracuseStep 1666127 = 2499191) B2499191
theorem B1666143 : Blo 1665032 1666143 := bstep (se 1 (by rfl) ⟨1249607, by rfl⟩ : syracuseStep 1666143 = 2499215) B2499215
theorem B60796021 : Blo 1665032 60796021 := bstep (se 5 (by rfl) ⟨2849813, by rfl⟩ : syracuseStep 60796021 = 5699627) B5699627
theorem B1666171 : Blo 1665032 1666171 := bstep (se 1 (by rfl) ⟨1249628, by rfl⟩ : syracuseStep 1666171 = 2499257) B2499257
theorem B3746987 : Blo 1665032 3746987 := bstep (se 1 (by rfl) ⟨2810240, by rfl⟩ : syracuseStep 3746987 = 5620481) B5620481
theorem B1666223 : Blo 1665032 1666223 := bstep (se 1 (by rfl) ⟨1249667, by rfl⟩ : syracuseStep 1666223 = 2499335) B2499335
theorem B1666247 : Blo 1665032 1666247 := bstep (se 1 (by rfl) ⟨1249685, by rfl⟩ : syracuseStep 1666247 = 2499371) B2499371
theorem B1666267 : Blo 1665032 1666267 := bstep (se 1 (by rfl) ⟨1249700, by rfl⟩ : syracuseStep 1666267 = 2499401) B2499401
theorem B1666343 : Blo 1665032 1666343 := bstep (se 1 (by rfl) ⟨1249757, by rfl⟩ : syracuseStep 1666343 = 2499515) B2499515
theorem B1666383 : Blo 1665032 1666383 := bstep (se 1 (by rfl) ⟨1249787, by rfl⟩ : syracuseStep 1666383 = 2499575) B2499575
theorem B5623127 : Blo 1665032 5623127 := bstep (se 1 (by rfl) ⟨4217345, by rfl⟩ : syracuseStep 5623127 = 8434691) B8434691
theorem B1666399 : Blo 1665032 1666399 := bstep (se 1 (by rfl) ⟨1249799, by rfl⟩ : syracuseStep 1666399 = 2499599) B2499599
theorem B4001129 : Blo 1665032 4001129 := bstep (se 2 (by rfl) ⟨1500423, by rfl⟩ : syracuseStep 4001129 = 3000847) B3000847
theorem B1666427 : Blo 1665032 1666427 := bstep (se 1 (by rfl) ⟨1249820, by rfl⟩ : syracuseStep 1666427 = 2499641) B2499641
theorem B45575567 : Blo 1665032 45575567 := bstep (se 1 (by rfl) ⟨34181675, by rfl⟩ : syracuseStep 45575567 = 68363351) B68363351
theorem B1666479 : Blo 1665032 1666479 := bstep (se 1 (by rfl) ⟨1249859, by rfl⟩ : syracuseStep 1666479 = 2499719) B2499719
theorem B3001783 : Blo 1665032 3001783 := bstep (se 1 (by rfl) ⟨2251337, by rfl⟩ : syracuseStep 3001783 = 4502675) B4502675
theorem B2108855 : Blo 1665032 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B1666503 : Blo 1665032 1666503 := bstep (se 1 (by rfl) ⟨1249877, by rfl⟩ : syracuseStep 1666503 = 2499755) B2499755
theorem B1666523 : Blo 1665032 1666523 := bstep (se 1 (by rfl) ⟨1249892, by rfl⟩ : syracuseStep 1666523 = 2499785) B2499785
theorem B6753817 : Blo 1665032 6753817 := bstep (se 2 (by rfl) ⟨2532681, by rfl⟩ : syracuseStep 6753817 = 5065363) B5065363
theorem B2109007 : Blo 1665032 2109007 := bstep (se 1 (by rfl) ⟨1581755, by rfl⟩ : syracuseStep 2109007 = 3163511) B3163511
theorem B16010891 : Blo 1665032 16010891 := bstep (se 1 (by rfl) ⟨12008168, by rfl⟩ : syracuseStep 16010891 = 24016337) B24016337
theorem B3747527 : Blo 1665032 3747527 := bstep (se 1 (by rfl) ⟨2810645, by rfl⟩ : syracuseStep 3747527 = 5621291) B5621291
theorem B20254445 : Blo 1665032 20254445 := bstep (se 3 (by rfl) ⟨3797708, by rfl⟩ : syracuseStep 20254445 = 7595417) B7595417
theorem B10669805 : Blo 1665032 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B3559241 : Blo 1665032 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B13504589 : Blo 1665032 13504589 := bstep (se 3 (by rfl) ⟨2532110, by rfl⟩ : syracuseStep 13504589 = 5064221) B5064221
theorem B10670237 : Blo 1665032 10670237 := bstep (se 3 (by rfl) ⟨2000669, by rfl⟩ : syracuseStep 10670237 = 4001339) B4001339
theorem B6754499 : Blo 1665032 6754499 := bstep (se 1 (by rfl) ⟨5065874, by rfl⟩ : syracuseStep 6754499 = 10131749) B10131749
theorem B21344573 : Blo 1665032 21344573 := bstep (se 3 (by rfl) ⟨4002107, by rfl⟩ : syracuseStep 21344573 = 8004215) B8004215
theorem B4272527 : Blo 1665032 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B5624207 : Blo 1665032 5624207 := bstep (se 1 (by rfl) ⟨4218155, by rfl⟩ : syracuseStep 5624207 = 8436311) B8436311
theorem B3748391 : Blo 1665032 3748391 := bstep (se 1 (by rfl) ⟨2811293, by rfl⟩ : syracuseStep 3748391 = 5622587) B5622587
theorem B6754855 : Blo 1665032 6754855 := bstep (se 1 (by rfl) ⟨5066141, by rfl⟩ : syracuseStep 6754855 = 10132283) B10132283
theorem B18010835 : Blo 1665032 18010835 := bstep (se 1 (by rfl) ⟨13508126, by rfl⟩ : syracuseStep 18010835 = 27016253) B27016253
theorem B5624531 : Blo 1665032 5624531 := bstep (se 1 (by rfl) ⟨4218398, by rfl⟩ : syracuseStep 5624531 = 8436797) B8436797
theorem B3748715 : Blo 1665032 3748715 := bstep (se 1 (by rfl) ⟨2811536, by rfl⟩ : syracuseStep 3748715 = 5623073) B5623073
theorem B3748769 : Blo 1665032 3748769 := bstep (se 2 (by rfl) ⟨1405788, by rfl⟩ : syracuseStep 3748769 = 2811577) B2811577
theorem B12653495 : Blo 1665032 12653495 := bstep (se 1 (by rfl) ⟨9490121, by rfl⟩ : syracuseStep 12653495 = 18980243) B18980243
theorem B4502459 : Blo 1665032 4502459 := bstep (se 1 (by rfl) ⟨3376844, by rfl⟩ : syracuseStep 4502459 = 6753689) B6753689
theorem B4215827 : Blo 1665032 4215827 := bstep (se 1 (by rfl) ⟨3161870, by rfl⟩ : syracuseStep 4215827 = 6323741) B6323741
theorem B25646129 : Blo 1665032 25646129 := bstep (se 2 (by rfl) ⟨9617298, by rfl⟩ : syracuseStep 25646129 = 19234597) B19234597
theorem B3749111 : Blo 1665032 3749111 := bstep (se 1 (by rfl) ⟨2811833, by rfl⟩ : syracuseStep 3749111 = 5623667) B5623667
theorem B1873327 : Blo 1665032 1873327 := bstep (se 1 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 1873327 = 2809991) B2809991
theorem B4216283 : Blo 1665032 4216283 := bstep (se 1 (by rfl) ⟨3162212, by rfl⟩ : syracuseStep 4216283 = 6324425) B6324425
theorem B8435339 : Blo 1665032 8435339 := bstep (se 1 (by rfl) ⟨6326504, by rfl⟩ : syracuseStep 8435339 = 12653009) B12653009
theorem B6756139 : Blo 1665032 6756139 := bstep (se 1 (by rfl) ⟨5067104, by rfl⟩ : syracuseStep 6756139 = 10134209) B10134209
theorem B1873759 : Blo 1665032 1873759 := bstep (se 1 (by rfl) ⟨1405319, by rfl⟩ : syracuseStep 1873759 = 2810639) B2810639
theorem B2668393 : Blo 1665032 2668393 := bstep (se 2 (by rfl) ⟨1000647, by rfl⟩ : syracuseStep 2668393 = 2001295) B2001295
theorem B15619949 : Blo 1665032 15619949 := bstep (se 3 (by rfl) ⟨2928740, by rfl⟩ : syracuseStep 15619949 = 5857481) B5857481
theorem B8550263 : Blo 1665032 8550263 := bstep (se 1 (by rfl) ⟨6412697, by rfl⟩ : syracuseStep 8550263 = 12825395) B12825395
theorem B1874119 : Blo 1665032 1874119 := bstep (se 1 (by rfl) ⟨1405589, by rfl⟩ : syracuseStep 1874119 = 2811179) B2811179
theorem B12654953 : Blo 1665032 12654953 := bstep (se 2 (by rfl) ⟨4745607, by rfl⟩ : syracuseStep 12654953 = 9491215) B9491215
theorem B46225799 : Blo 1665032 46225799 := bstep (se 1 (by rfl) ⟨34669349, by rfl⟩ : syracuseStep 46225799 = 69338699) B69338699
theorem B4217467 : Blo 1665032 4217467 := bstep (se 1 (by rfl) ⟨3163100, by rfl⟩ : syracuseStep 4217467 = 6326201) B6326201
theorem B6323467 : Blo 1665032 6323467 := bstep (se 1 (by rfl) ⟨4742600, by rfl⟩ : syracuseStep 6323467 = 9485201) B9485201
theorem B2497967 : Blo 1665032 2497967 := bstep (se 1 (by rfl) ⟨1873475, by rfl⟩ : syracuseStep 2497967 = 3746951) B3746951
theorem B1899995 : Blo 1665032 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B2498057 : Blo 1665032 2498057 := bstep (se 2 (by rfl) ⟨936771, by rfl⟩ : syracuseStep 2498057 = 1873543) B1873543
theorem B11263499 : Blo 1665032 11263499 := bstep (se 1 (by rfl) ⟨8447624, by rfl⟩ : syracuseStep 11263499 = 16895249) B16895249
theorem B2498087 : Blo 1665032 2498087 := bstep (se 1 (by rfl) ⟨1873565, by rfl⟩ : syracuseStep 2498087 = 3747131) B3747131
theorem B6323771 : Blo 1665032 6323771 := bstep (se 1 (by rfl) ⟨4742828, by rfl⟩ : syracuseStep 6323771 = 9485657) B9485657
theorem B2498171 : Blo 1665032 2498171 := bstep (se 1 (by rfl) ⟨1873628, by rfl⟩ : syracuseStep 2498171 = 3747257) B3747257
theorem B2498297 : Blo 1665032 2498297 := bstep (se 2 (by rfl) ⟨936861, by rfl⟩ : syracuseStep 2498297 = 1873723) B1873723
theorem B18013985 : Blo 1665032 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B2498399 : Blo 1665032 2498399 := bstep (se 1 (by rfl) ⟨1873799, by rfl⟩ : syracuseStep 2498399 = 3747599) B3747599
theorem B5619563 : Blo 1665032 5619563 := bstep (se 1 (by rfl) ⟨4214672, by rfl⟩ : syracuseStep 5619563 = 8429345) B8429345
theorem B6586219 : Blo 1665032 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B2498411 : Blo 1665032 2498411 := bstep (se 1 (by rfl) ⟨1873808, by rfl⟩ : syracuseStep 2498411 = 3747617) B3747617
theorem B5619617 : Blo 1665032 5619617 := bstep (se 2 (by rfl) ⟨2107356, by rfl⟩ : syracuseStep 5619617 = 4214713) B4214713
theorem B2809775 : Blo 1665032 2809775 := bstep (se 1 (by rfl) ⟨2107331, by rfl⟩ : syracuseStep 2809775 = 4214663) B4214663
theorem B4743193 : Blo 1665032 4743193 := bstep (se 2 (by rfl) ⟨1778697, by rfl⟩ : syracuseStep 4743193 = 3557395) B3557395
theorem B9003059 : Blo 1665032 9003059 := bstep (se 1 (by rfl) ⟨6752294, by rfl⟩ : syracuseStep 9003059 = 13504589) B13504589
theorem B14229715 : Blo 1665032 14229715 := bstep (se 1 (by rfl) ⟨10672286, by rfl⟩ : syracuseStep 14229715 = 21344573) B21344573
theorem B2498825 : Blo 1665032 2498825 := bstep (se 2 (by rfl) ⟨937059, by rfl⟩ : syracuseStep 2498825 = 1874119) B1874119
theorem B2498927 : Blo 1665032 2498927 := bstep (se 1 (by rfl) ⟨1874195, by rfl⟩ : syracuseStep 2498927 = 3748391) B3748391
theorem B15196673 : Blo 1665032 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B2499143 : Blo 1665032 2499143 := bstep (se 1 (by rfl) ⟨1874357, by rfl⟩ : syracuseStep 2499143 = 3748715) B3748715
theorem B2499179 : Blo 1665032 2499179 := bstep (se 1 (by rfl) ⟨1874384, by rfl⟩ : syracuseStep 2499179 = 3748769) B3748769
theorem B2810551 : Blo 1665032 2810551 := bstep (se 1 (by rfl) ⟨2107913, by rfl⟩ : syracuseStep 2810551 = 4215827) B4215827
theorem B36504265 : Blo 1665032 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B17097419 : Blo 1665032 17097419 := bstep (se 1 (by rfl) ⟨12823064, by rfl⟩ : syracuseStep 17097419 = 25646129) B25646129
theorem B2499407 : Blo 1665032 2499407 := bstep (se 1 (by rfl) ⟨1874555, by rfl⟩ : syracuseStep 2499407 = 3749111) B3749111
theorem B2810855 : Blo 1665032 2810855 := bstep (se 1 (by rfl) ⟨2108141, by rfl⟩ : syracuseStep 2810855 = 4216283) B4216283
theorem B10814471 : Blo 1665032 10814471 := bstep (se 1 (by rfl) ⟨8110853, by rfl⟩ : syracuseStep 10814471 = 16221707) B16221707
theorem B9487367 : Blo 1665032 9487367 := bstep (se 1 (by rfl) ⟨7115525, by rfl⟩ : syracuseStep 9487367 = 14231051) B14231051
theorem B34178071 : Blo 1665032 34178071 := bstep (se 1 (by rfl) ⟨25633553, by rfl⟩ : syracuseStep 34178071 = 51267107) B51267107
theorem B10413299 : Blo 1665032 10413299 := bstep (se 1 (by rfl) ⟨7809974, by rfl⟩ : syracuseStep 10413299 = 15619949) B15619949
theorem B81061361 : Blo 1665032 81061361 := bstep (se 2 (by rfl) ⟨30398010, by rfl⟩ : syracuseStep 81061361 = 60796021) B60796021
theorem B8431289 : Blo 1665032 8431289 := bstep (se 2 (by rfl) ⟨3161733, by rfl⟩ : syracuseStep 8431289 = 6323467) B6323467
theorem B28837903 : Blo 1665032 28837903 := bstep (se 1 (by rfl) ⟨21628427, by rfl⟩ : syracuseStep 28837903 = 43256855) B43256855
theorem B9005089 : Blo 1665032 9005089 := bstep (se 2 (by rfl) ⟨3376908, by rfl⟩ : syracuseStep 9005089 = 6753817) B6753817
theorem B2812009 : Blo 1665032 2812009 := bstep (se 2 (by rfl) ⟨1054503, by rfl⟩ : syracuseStep 2812009 = 2109007) B2109007
theorem B1665311 : Blo 1665032 1665311 := bstep (se 1 (by rfl) ⟨1248983, by rfl⟩ : syracuseStep 1665311 = 2497967) B2497967
theorem B1665371 : Blo 1665032 1665371 := bstep (se 1 (by rfl) ⟨1249028, by rfl⟩ : syracuseStep 1665371 = 2498057) B2498057
theorem B1665391 : Blo 1665032 1665391 := bstep (se 1 (by rfl) ⟨1249043, by rfl⟩ : syracuseStep 1665391 = 2498087) B2498087
theorem B1665447 : Blo 1665032 1665447 := bstep (se 1 (by rfl) ⟨1249085, by rfl⟩ : syracuseStep 1665447 = 2498171) B2498171
theorem B3557857 : Blo 1665032 3557857 := bstep (se 2 (by rfl) ⟨1334196, by rfl⟩ : syracuseStep 3557857 = 2668393) B2668393
theorem B13502963 : Blo 1665032 13502963 := bstep (se 1 (by rfl) ⟨10127222, by rfl⟩ : syracuseStep 13502963 = 20254445) B20254445
theorem B7113203 : Blo 1665032 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B1665531 : Blo 1665032 1665531 := bstep (se 1 (by rfl) ⟨1249148, by rfl⟩ : syracuseStep 1665531 = 2498297) B2498297
theorem B1665599 : Blo 1665032 1665599 := bstep (se 1 (by rfl) ⟨1249199, by rfl⟩ : syracuseStep 1665599 = 2498399) B2498399
theorem B3746375 : Blo 1665032 3746375 := bstep (se 1 (by rfl) ⟨2809781, by rfl⟩ : syracuseStep 3746375 = 5619563) B5619563
theorem B1665607 : Blo 1665032 1665607 := bstep (se 1 (by rfl) ⟨1249205, by rfl⟩ : syracuseStep 1665607 = 2498411) B2498411
theorem B3746411 : Blo 1665032 3746411 := bstep (se 1 (by rfl) ⟨2809808, by rfl⟩ : syracuseStep 3746411 = 5619617) B5619617
theorem B1665759 : Blo 1665032 1665759 := bstep (se 1 (by rfl) ⟨1249319, by rfl⟩ : syracuseStep 1665759 = 2498639) B2498639
theorem B7113491 : Blo 1665032 7113491 := bstep (se 1 (by rfl) ⟨5335118, by rfl⟩ : syracuseStep 7113491 = 10670237) B10670237
theorem B2108207 : Blo 1665032 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B1665839 : Blo 1665032 1665839 := bstep (se 1 (by rfl) ⟨1249379, by rfl⟩ : syracuseStep 1665839 = 2498759) B2498759
theorem B1665947 : Blo 1665032 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B1665999 : Blo 1665032 1665999 := bstep (se 1 (by rfl) ⟨1249499, by rfl⟩ : syracuseStep 1665999 = 2498999) B2498999
theorem B1666023 : Blo 1665032 1666023 := bstep (se 1 (by rfl) ⟨1249517, by rfl⟩ : syracuseStep 1666023 = 2499035) B2499035
theorem B3746807 : Blo 1665032 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B3206287 : Blo 1665032 3206287 := bstep (se 1 (by rfl) ⟨2404715, by rfl⟩ : syracuseStep 3206287 = 4809431) B4809431
theorem B1666335 : Blo 1665032 1666335 := bstep (se 1 (by rfl) ⟨1249751, by rfl⟩ : syracuseStep 1666335 = 2499503) B2499503
theorem B3001639 : Blo 1665032 3001639 := bstep (se 1 (by rfl) ⟨2251229, by rfl⟩ : syracuseStep 3001639 = 4502459) B4502459
theorem B20254013 : Blo 1665032 20254013 := bstep (se 3 (by rfl) ⟨3797627, by rfl⟩ : syracuseStep 20254013 = 7595255) B7595255
theorem B1666395 : Blo 1665032 1666395 := bstep (se 1 (by rfl) ⟨1249796, by rfl⟩ : syracuseStep 1666395 = 2499593) B2499593
theorem B3747167 : Blo 1665032 3747167 := bstep (se 1 (by rfl) ⟨2810375, by rfl⟩ : syracuseStep 3747167 = 5620751) B5620751
theorem B5410145 : Blo 1665032 5410145 := bstep (se 2 (by rfl) ⟨2028804, by rfl⟩ : syracuseStep 5410145 = 4057609) B4057609
theorem B1666415 : Blo 1665032 1666415 := bstep (se 1 (by rfl) ⟨1249811, by rfl⟩ : syracuseStep 1666415 = 2499623) B2499623
theorem B9006473 : Blo 1665032 9006473 := bstep (se 2 (by rfl) ⟨3377427, by rfl⟩ : syracuseStep 9006473 = 6754855) B6754855
theorem B4001185 : Blo 1665032 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B1666471 : Blo 1665032 1666471 := bstep (se 1 (by rfl) ⟨1249853, by rfl⟩ : syracuseStep 1666471 = 2499707) B2499707
theorem B5623289 : Blo 1665032 5623289 := bstep (se 2 (by rfl) ⟨2108733, by rfl⟩ : syracuseStep 5623289 = 4217467) B4217467
theorem B8433233 : Blo 1665032 8433233 := bstep (se 2 (by rfl) ⟨3162462, by rfl⟩ : syracuseStep 8433233 = 6324925) B6324925
theorem B3747563 : Blo 1665032 3747563 := bstep (se 1 (by rfl) ⟨2810672, by rfl⟩ : syracuseStep 3747563 = 5621345) B5621345
theorem B8007427 : Blo 1665032 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B5623559 : Blo 1665032 5623559 := bstep (se 1 (by rfl) ⟨4217669, by rfl⟩ : syracuseStep 5623559 = 8435339) B8435339
theorem B2371369 : Blo 1665032 2371369 := bstep (se 2 (by rfl) ⟨889263, by rfl⟩ : syracuseStep 2371369 = 1778527) B1778527
theorem B5623613 : Blo 1665032 5623613 := bstep (se 3 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 5623613 = 2108855) B2108855
theorem B3747689 : Blo 1665032 3747689 := bstep (se 2 (by rfl) ⟨1405383, by rfl⟩ : syracuseStep 3747689 = 2810767) B2810767
theorem B5066653 : Blo 1665032 5066653 := bstep (se 3 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 5066653 = 1899995) B1899995
theorem B8007599 : Blo 1665032 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B9613417 : Blo 1665032 9613417 := bstep (se 2 (by rfl) ⟨3605031, by rfl⟩ : syracuseStep 9613417 = 7210063) B7210063
theorem B4501757 : Blo 1665032 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B2404775 : Blo 1665032 2404775 := bstep (se 1 (by rfl) ⟨1803581, by rfl⟩ : syracuseStep 2404775 = 3607163) B3607163
theorem B18010613 : Blo 1665032 18010613 := bstep (se 5 (by rfl) ⟨844247, by rfl⟩ : syracuseStep 18010613 = 1688495) B1688495
theorem B4002377 : Blo 1665032 4002377 := bstep (se 2 (by rfl) ⟨1500891, by rfl⟩ : syracuseStep 4002377 = 3001783) B3001783
theorem B3748535 : Blo 1665032 3748535 := bstep (se 1 (by rfl) ⟨2811401, by rfl⟩ : syracuseStep 3748535 = 5622803) B5622803
theorem B3748751 : Blo 1665032 3748751 := bstep (se 1 (by rfl) ⟨2811563, by rfl⟩ : syracuseStep 3748751 = 5623127) B5623127
theorem B2667419 : Blo 1665032 2667419 := bstep (se 1 (by rfl) ⟨2000564, by rfl⟩ : syracuseStep 2667419 = 4001129) B4001129
theorem B7508999 : Blo 1665032 7508999 := bstep (se 1 (by rfl) ⟨5631749, by rfl⟩ : syracuseStep 7508999 = 11263499) B11263499
theorem B4215847 : Blo 1665032 4215847 := bstep (se 1 (by rfl) ⟨3161885, by rfl⟩ : syracuseStep 4215847 = 6323771) B6323771
theorem B9008185 : Blo 1665032 9008185 := bstep (se 2 (by rfl) ⟨3378069, by rfl⟩ : syracuseStep 9008185 = 6756139) B6756139
theorem B2372827 : Blo 1665032 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B1873183 : Blo 1665032 1873183 := bstep (se 1 (by rfl) ⟨1404887, by rfl⟩ : syracuseStep 1873183 = 2809775) B2809775
theorem B4502999 : Blo 1665032 4502999 := bstep (se 1 (by rfl) ⟨3377249, by rfl⟩ : syracuseStep 4502999 = 6754499) B6754499
theorem B4216313 : Blo 1665032 4216313 := bstep (se 2 (by rfl) ⟨1581117, by rfl⟩ : syracuseStep 4216313 = 3162235) B3162235
theorem B1873471 : Blo 1665032 1873471 := bstep (se 1 (by rfl) ⟨1405103, by rfl⟩ : syracuseStep 1873471 = 2810207) B2810207
theorem B3749471 : Blo 1665032 3749471 := bstep (se 1 (by rfl) ⟨2812103, by rfl⟩ : syracuseStep 3749471 = 5624207) B5624207
theorem B12007223 : Blo 1665032 12007223 := bstep (se 1 (by rfl) ⟨9005417, by rfl⟩ : syracuseStep 12007223 = 18010835) B18010835
theorem B3749687 : Blo 1665032 3749687 := bstep (se 1 (by rfl) ⟨2812265, by rfl⟩ : syracuseStep 3749687 = 5624531) B5624531
theorem B8435663 : Blo 1665032 8435663 := bstep (se 1 (by rfl) ⟨6326747, by rfl⟩ : syracuseStep 8435663 = 12653495) B12653495
theorem B4216961 : Blo 1665032 4216961 := bstep (se 2 (by rfl) ⟨1581360, by rfl⟩ : syracuseStep 4216961 = 3162721) B3162721
theorem B12171545 : Blo 1665032 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B4503833 : Blo 1665032 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B1874299 : Blo 1665032 1874299 := bstep (se 1 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 1874299 = 2811449) B2811449
theorem B11393405 : Blo 1665032 11393405 := bstep (se 3 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 11393405 = 4272527) B4272527
theorem B4217255 : Blo 1665032 4217255 := bstep (se 1 (by rfl) ⟨3162941, by rfl⟩ : syracuseStep 4217255 = 6325883) B6325883
theorem B4217417 : Blo 1665032 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B5700175 : Blo 1665032 5700175 := bstep (se 1 (by rfl) ⟨4275131, by rfl⟩ : syracuseStep 5700175 = 8550263) B8550263
theorem B14228075 : Blo 1665032 14228075 := bstep (se 1 (by rfl) ⟨10671056, by rfl⟩ : syracuseStep 14228075 = 21342113) B21342113
theorem B1874767 : Blo 1665032 1874767 := bstep (se 1 (by rfl) ⟨1406075, by rfl⟩ : syracuseStep 1874767 = 2812151) B2812151
theorem B9001847 : Blo 1665032 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B4873085 : Blo 1665032 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B8436635 : Blo 1665032 8436635 := bstep (se 1 (by rfl) ⟨6327476, by rfl⟩ : syracuseStep 8436635 = 12654953) B12654953
theorem B4217771 : Blo 1665032 4217771 := bstep (se 1 (by rfl) ⟨3163328, by rfl⟩ : syracuseStep 4217771 = 6326657) B6326657
theorem B30817199 : Blo 1665032 30817199 := bstep (se 1 (by rfl) ⟨23112899, by rfl⟩ : syracuseStep 30817199 = 46225799) B46225799
theorem B15195185 : Blo 1665032 15195185 := bstep (se 2 (by rfl) ⟨5698194, by rfl⟩ : syracuseStep 15195185 = 11396389) B11396389
theorem B4217953 : Blo 1665032 4217953 := bstep (se 2 (by rfl) ⟨1581732, by rfl⟩ : syracuseStep 4217953 = 3163465) B3163465
theorem B2497769 : Blo 1665032 2497769 := bstep (se 2 (by rfl) ⟨936663, by rfl⟩ : syracuseStep 2497769 = 1873327) B1873327
theorem B2497823 : Blo 1665032 2497823 := bstep (se 1 (by rfl) ⟨1873367, by rfl⟩ : syracuseStep 2497823 = 3746735) B3746735
theorem B6413687 : Blo 1665032 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B2497991 : Blo 1665032 2497991 := bstep (se 1 (by rfl) ⟨1873493, by rfl⟩ : syracuseStep 2497991 = 3746987) B3746987
theorem B30383711 : Blo 1665032 30383711 := bstep (se 1 (by rfl) ⟨22787783, by rfl⟩ : syracuseStep 30383711 = 45575567) B45575567
theorem B10673927 : Blo 1665032 10673927 := bstep (se 1 (by rfl) ⟨8005445, by rfl⟩ : syracuseStep 10673927 = 16010891) B16010891
theorem B2498345 : Blo 1665032 2498345 := bstep (se 2 (by rfl) ⟨936879, by rfl⟩ : syracuseStep 2498345 = 1873759) B1873759
theorem B2498351 : Blo 1665032 2498351 := bstep (se 1 (by rfl) ⟨1873763, by rfl⟩ : syracuseStep 2498351 = 3747527) B3747527
theorem B8781625 : Blo 1665032 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B12009323 : Blo 1665032 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B6324257 : Blo 1665032 6324257 := bstep (se 2 (by rfl) ⟨2371596, by rfl⟩ : syracuseStep 6324257 = 4743193) B4743193
theorem B18972953 : Blo 1665032 18972953 := bstep (se 2 (by rfl) ⟨7114857, by rfl⟩ : syracuseStep 18972953 = 14229715) B14229715
theorem B30400933 : Blo 1665032 30400933 := bstep (se 4 (by rfl) ⟨2850087, by rfl⟩ : syracuseStep 30400933 = 5700175) B5700175
theorem B2499023 : Blo 1665032 2499023 := bstep (se 1 (by rfl) ⟨1874267, by rfl⟩ : syracuseStep 2499023 = 3748535) B3748535
theorem B2499065 : Blo 1665032 2499065 := bstep (se 2 (by rfl) ⟨937149, by rfl⟩ : syracuseStep 2499065 = 1874299) B1874299
theorem B2499167 : Blo 1665032 2499167 := bstep (se 1 (by rfl) ⟨1874375, by rfl⟩ : syracuseStep 2499167 = 3748751) B3748751
theorem B1778279 : Blo 1665032 1778279 := bstep (se 1 (by rfl) ⟨1333709, by rfl⟩ : syracuseStep 1778279 = 2667419) B2667419
theorem B4743809 : Blo 1665032 4743809 := bstep (se 2 (by rfl) ⟨1778928, by rfl⟩ : syracuseStep 4743809 = 3557857) B3557857
theorem B7209647 : Blo 1665032 7209647 := bstep (se 1 (by rfl) ⟨5407235, by rfl⟩ : syracuseStep 7209647 = 10814471) B10814471
theorem B5005999 : Blo 1665032 5005999 := bstep (se 1 (by rfl) ⟨3754499, by rfl⟩ : syracuseStep 5005999 = 7508999) B7508999
theorem B6324911 : Blo 1665032 6324911 := bstep (se 1 (by rfl) ⟨4743683, by rfl⟩ : syracuseStep 6324911 = 9487367) B9487367
theorem B2810875 : Blo 1665032 2810875 := bstep (se 1 (by rfl) ⟨2108156, by rfl⟩ : syracuseStep 2810875 = 4216313) B4216313
theorem B2499647 : Blo 1665032 2499647 := bstep (se 1 (by rfl) ⟨1874735, by rfl⟩ : syracuseStep 2499647 = 3749471) B3749471
theorem B2499689 : Blo 1665032 2499689 := bstep (se 2 (by rfl) ⟨937383, by rfl⟩ : syracuseStep 2499689 = 1874767) B1874767
theorem B5620859 : Blo 1665032 5620859 := bstep (se 1 (by rfl) ⟨4215644, by rfl⟩ : syracuseStep 5620859 = 8431289) B8431289
theorem B8004815 : Blo 1665032 8004815 := bstep (se 1 (by rfl) ⟨6003611, by rfl⟩ : syracuseStep 8004815 = 12007223) B12007223
theorem B2499791 : Blo 1665032 2499791 := bstep (se 1 (by rfl) ⟨1874843, by rfl⟩ : syracuseStep 2499791 = 3749687) B3749687
theorem B5621129 : Blo 1665032 5621129 := bstep (se 2 (by rfl) ⟨2107923, by rfl⟩ : syracuseStep 5621129 = 4215847) B4215847
theorem B12010913 : Blo 1665032 12010913 := bstep (se 2 (by rfl) ⟨4504092, by rfl⟩ : syracuseStep 12010913 = 9008185) B9008185
theorem B2811307 : Blo 1665032 2811307 := bstep (se 1 (by rfl) ⟨2108480, by rfl⟩ : syracuseStep 2811307 = 4216961) B4216961
theorem B7595603 : Blo 1665032 7595603 := bstep (se 1 (by rfl) ⟨5696702, by rfl⟩ : syracuseStep 7595603 = 11393405) B11393405
theorem B2811503 : Blo 1665032 2811503 := bstep (se 1 (by rfl) ⟨2108627, by rfl⟩ : syracuseStep 2811503 = 4217255) B4217255
theorem B3163769 : Blo 1665032 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B2811611 : Blo 1665032 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B5334913 : Blo 1665032 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B2811847 : Blo 1665032 2811847 := bstep (se 1 (by rfl) ⟨2108885, by rfl⟩ : syracuseStep 2811847 = 4217771) B4217771
theorem B5621885 : Blo 1665032 5621885 := bstep (se 3 (by rfl) ⟨1054103, by rfl⟩ : syracuseStep 5621885 = 2108207) B2108207
theorem B1665179 : Blo 1665032 1665179 := bstep (se 1 (by rfl) ⟨1248884, by rfl⟩ : syracuseStep 1665179 = 2497769) B2497769
theorem B1665215 : Blo 1665032 1665215 := bstep (se 1 (by rfl) ⟨1248911, by rfl⟩ : syracuseStep 1665215 = 2497823) B2497823
theorem B13502675 : Blo 1665032 13502675 := bstep (se 1 (by rfl) ⟨10127006, by rfl⟩ : syracuseStep 13502675 = 20254013) B20254013
theorem B3606763 : Blo 1665032 3606763 := bstep (se 1 (by rfl) ⟨2705072, by rfl⟩ : syracuseStep 3606763 = 5410145) B5410145
theorem B1665327 : Blo 1665032 1665327 := bstep (se 1 (by rfl) ⟨1248995, by rfl⟩ : syracuseStep 1665327 = 2497991) B2497991
theorem B10676569 : Blo 1665032 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B5622155 : Blo 1665032 5622155 := bstep (se 1 (by rfl) ⟨4216616, by rfl⟩ : syracuseStep 5622155 = 8433233) B8433233
theorem B11708833 : Blo 1665032 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B1665563 : Blo 1665032 1665563 := bstep (se 1 (by rfl) ⟨1249172, by rfl⟩ : syracuseStep 1665563 = 2498345) B2498345
theorem B1665567 : Blo 1665032 1665567 := bstep (se 1 (by rfl) ⟨1249175, by rfl⟩ : syracuseStep 1665567 = 2498351) B2498351
theorem B8006215 : Blo 1665032 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1665883 : Blo 1665032 1665883 := bstep (se 1 (by rfl) ⟨1249412, by rfl⟩ : syracuseStep 1665883 = 2498825) B2498825
theorem B1665951 : Blo 1665032 1665951 := bstep (se 1 (by rfl) ⟨1249463, by rfl⟩ : syracuseStep 1665951 = 2498927) B2498927
theorem B1666095 : Blo 1665032 1666095 := bstep (se 1 (by rfl) ⟨1249571, by rfl⟩ : syracuseStep 1666095 = 2499143) B2499143
theorem B1666119 : Blo 1665032 1666119 := bstep (se 1 (by rfl) ⟨1249589, by rfl⟩ : syracuseStep 1666119 = 2499179) B2499179
theorem B11398279 : Blo 1665032 11398279 := bstep (se 1 (by rfl) ⟨8548709, by rfl⟩ : syracuseStep 11398279 = 17097419) B17097419
theorem B1666271 : Blo 1665032 1666271 := bstep (se 1 (by rfl) ⟨1249703, by rfl⟩ : syracuseStep 1666271 = 2499407) B2499407
theorem B12004685 : Blo 1665032 12004685 := bstep (se 3 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 12004685 = 4501757) B4501757
theorem B17100197 : Blo 1665032 17100197 := bstep (se 4 (by rfl) ⟨1603143, by rfl⟩ : syracuseStep 17100197 = 3206287) B3206287
theorem B6942199 : Blo 1665032 6942199 := bstep (se 1 (by rfl) ⟨5206649, by rfl⟩ : syracuseStep 6942199 = 10413299) B10413299
theorem B3747401 : Blo 1665032 3747401 := bstep (se 2 (by rfl) ⟨1405275, by rfl⟩ : syracuseStep 3747401 = 2810551) B2810551
theorem B48672353 : Blo 1665032 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B5623775 : Blo 1665032 5623775 := bstep (se 1 (by rfl) ⟨4217831, by rfl⟩ : syracuseStep 5623775 = 8435663) B8435663
theorem B5623937 : Blo 1665032 5623937 := bstep (se 2 (by rfl) ⟨2108976, by rfl⟩ : syracuseStep 5623937 = 4217953) B4217953
theorem B8114363 : Blo 1665032 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B3002555 : Blo 1665032 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B4002185 : Blo 1665032 4002185 := bstep (se 2 (by rfl) ⟨1500819, by rfl⟩ : syracuseStep 4002185 = 3001639) B3001639
theorem B6001231 : Blo 1665032 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B3248723 : Blo 1665032 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B5624423 : Blo 1665032 5624423 := bstep (se 1 (by rfl) ⟨4218317, by rfl⟩ : syracuseStep 5624423 = 8436635) B8436635
theorem B10130123 : Blo 1665032 10130123 := bstep (se 1 (by rfl) ⟨7597592, by rfl⟩ : syracuseStep 10130123 = 15195185) B15195185
theorem B3748859 : Blo 1665032 3748859 := bstep (se 1 (by rfl) ⟨2811644, by rfl⟩ : syracuseStep 3748859 = 5623289) B5623289
theorem B20255807 : Blo 1665032 20255807 := bstep (se 1 (by rfl) ⟨15191855, by rfl⟩ : syracuseStep 20255807 = 30383711) B30383711
theorem B7115951 : Blo 1665032 7115951 := bstep (se 1 (by rfl) ⟨5336963, by rfl⟩ : syracuseStep 7115951 = 10673927) B10673927
theorem B3749039 : Blo 1665032 3749039 := bstep (se 1 (by rfl) ⟨2811779, by rfl⟩ : syracuseStep 3749039 = 5623559) B5623559
theorem B6755537 : Blo 1665032 6755537 := bstep (se 2 (by rfl) ⟨2533326, by rfl⟩ : syracuseStep 6755537 = 5066653) B5066653
theorem B3749075 : Blo 1665032 3749075 := bstep (se 1 (by rfl) ⟨2811806, by rfl⟩ : syracuseStep 3749075 = 5623613) B5623613
theorem B5338399 : Blo 1665032 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B38450537 : Blo 1665032 38450537 := bstep (se 2 (by rfl) ⟨14418951, by rfl⟩ : syracuseStep 38450537 = 28837903) B28837903
theorem B6002039 : Blo 1665032 6002039 := bstep (se 1 (by rfl) ⟨4501529, by rfl⟩ : syracuseStep 6002039 = 9003059) B9003059
theorem B12006785 : Blo 1665032 12006785 := bstep (se 2 (by rfl) ⟨4502544, by rfl⟩ : syracuseStep 12006785 = 9005089) B9005089
theorem B12817889 : Blo 1665032 12817889 := bstep (se 2 (by rfl) ⟨4806708, by rfl⟩ : syracuseStep 12817889 = 9613417) B9613417
theorem B3749345 : Blo 1665032 3749345 := bstep (se 2 (by rfl) ⟨1406004, by rfl⟩ : syracuseStep 3749345 = 2812009) B2812009
theorem B12007075 : Blo 1665032 12007075 := bstep (se 1 (by rfl) ⟨9005306, by rfl⟩ : syracuseStep 12007075 = 18010613) B18010613
theorem B10131115 : Blo 1665032 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B1873903 : Blo 1665032 1873903 := bstep (se 1 (by rfl) ⟨1405427, by rfl⟩ : syracuseStep 1873903 = 2810855) B2810855
theorem B54040907 : Blo 1665032 54040907 := bstep (se 1 (by rfl) ⟨40530680, by rfl⟩ : syracuseStep 54040907 = 81061361) B81061361
theorem B6412733 : Blo 1665032 6412733 := bstep (se 3 (by rfl) ⟨1202387, by rfl⟩ : syracuseStep 6412733 = 2404775) B2404775
theorem B12007997 : Blo 1665032 12007997 := bstep (se 3 (by rfl) ⟨2251499, by rfl⟩ : syracuseStep 12007997 = 4502999) B4502999
theorem B45570761 : Blo 1665032 45570761 := bstep (se 2 (by rfl) ⟨17089035, by rfl⟩ : syracuseStep 45570761 = 34178071) B34178071
theorem B10673005 : Blo 1665032 10673005 := bstep (se 3 (by rfl) ⟨2001188, by rfl⟩ : syracuseStep 10673005 = 4002377) B4002377
theorem B9001975 : Blo 1665032 9001975 := bstep (se 1 (by rfl) ⟨6751481, by rfl⟩ : syracuseStep 9001975 = 13502963) B13502963
theorem B4742135 : Blo 1665032 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B2497577 : Blo 1665032 2497577 := bstep (se 2 (by rfl) ⟨936591, by rfl⟩ : syracuseStep 2497577 = 1873183) B1873183
theorem B2497583 : Blo 1665032 2497583 := bstep (se 1 (by rfl) ⟨1873187, by rfl⟩ : syracuseStep 2497583 = 3746375) B3746375
theorem B2497607 : Blo 1665032 2497607 := bstep (se 1 (by rfl) ⟨1873205, by rfl⟩ : syracuseStep 2497607 = 3746411) B3746411
theorem B9485383 : Blo 1665032 9485383 := bstep (se 1 (by rfl) ⟨7114037, by rfl⟩ : syracuseStep 9485383 = 14228075) B14228075
theorem B4742327 : Blo 1665032 4742327 := bstep (se 1 (by rfl) ⟨3556745, by rfl⟩ : syracuseStep 4742327 = 7113491) B7113491
theorem B20544799 : Blo 1665032 20544799 := bstep (se 1 (by rfl) ⟨15408599, by rfl⟩ : syracuseStep 20544799 = 30817199) B30817199
theorem B2497871 : Blo 1665032 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B2497961 : Blo 1665032 2497961 := bstep (se 2 (by rfl) ⟨936735, by rfl⟩ : syracuseStep 2497961 = 1873471) B1873471
theorem B2498111 : Blo 1665032 2498111 := bstep (se 1 (by rfl) ⟨1873583, by rfl⟩ : syracuseStep 2498111 = 3747167) B3747167
theorem B4275791 : Blo 1665032 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B6004315 : Blo 1665032 6004315 := bstep (se 1 (by rfl) ⟨4503236, by rfl⟩ : syracuseStep 6004315 = 9006473) B9006473
theorem B3161825 : Blo 1665032 3161825 := bstep (se 2 (by rfl) ⟨1185684, by rfl⟩ : syracuseStep 3161825 = 2371369) B2371369
theorem B2498375 : Blo 1665032 2498375 := bstep (se 1 (by rfl) ⟨1873781, by rfl⟩ : syracuseStep 2498375 = 3747563) B3747563
theorem B2498459 : Blo 1665032 2498459 := bstep (se 1 (by rfl) ⟨1873844, by rfl⟩ : syracuseStep 2498459 = 3747689) B3747689
theorem B12648635 : Blo 1665032 12648635 := bstep (se 1 (by rfl) ⟨9486476, by rfl⟩ : syracuseStep 12648635 = 18972953) B18972953
theorem B4809017 : Blo 1665032 4809017 := bstep (se 2 (by rfl) ⟨1803381, by rfl⟩ : syracuseStep 4809017 = 3606763) B3606763
theorem B3162539 : Blo 1665032 3162539 := bstep (se 1 (by rfl) ⟨2371904, by rfl⟩ : syracuseStep 3162539 = 4743809) B4743809
theorem B40534577 : Blo 1665032 40534577 := bstep (se 2 (by rfl) ⟨15200466, by rfl⟩ : syracuseStep 40534577 = 30400933) B30400933
theorem B2499239 : Blo 1665032 2499239 := bstep (se 1 (by rfl) ⟨1874429, by rfl⟩ : syracuseStep 2499239 = 3748859) B3748859
theorem B10674953 : Blo 1665032 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B2499359 : Blo 1665032 2499359 := bstep (se 1 (by rfl) ⟨1874519, by rfl⟩ : syracuseStep 2499359 = 3749039) B3749039
theorem B2499383 : Blo 1665032 2499383 := bstep (se 1 (by rfl) ⟨1874537, by rfl⟩ : syracuseStep 2499383 = 3749075) B3749075
theorem B25633691 : Blo 1665032 25633691 := bstep (se 1 (by rfl) ⟨19225268, by rfl⟩ : syracuseStep 25633691 = 38450537) B38450537
theorem B8004523 : Blo 1665032 8004523 := bstep (se 1 (by rfl) ⟨6003392, by rfl⟩ : syracuseStep 8004523 = 12006785) B12006785
theorem B8545259 : Blo 1665032 8545259 := bstep (se 1 (by rfl) ⟨6408944, by rfl⟩ : syracuseStep 8545259 = 12817889) B12817889
theorem B2499563 : Blo 1665032 2499563 := bstep (se 1 (by rfl) ⟨1874672, by rfl⟩ : syracuseStep 2499563 = 3749345) B3749345
theorem B5063735 : Blo 1665032 5063735 := bstep (se 1 (by rfl) ⟨3797801, by rfl⟩ : syracuseStep 5063735 = 7595603) B7595603
theorem B14230673 : Blo 1665032 14230673 := bstep (se 2 (by rfl) ⟨5336502, by rfl⟩ : syracuseStep 14230673 = 10673005) B10673005
theorem B12002633 : Blo 1665032 12002633 := bstep (se 2 (by rfl) ⟨4500987, by rfl⟩ : syracuseStep 12002633 = 9001975) B9001975
theorem B15197705 : Blo 1665032 15197705 := bstep (se 2 (by rfl) ⟨5699139, by rfl⟩ : syracuseStep 15197705 = 11398279) B11398279
theorem B8005331 : Blo 1665032 8005331 := bstep (se 1 (by rfl) ⟨6003998, by rfl⟩ : syracuseStep 8005331 = 12007997) B12007997
theorem B28452869 : Blo 1665032 28452869 := bstep (se 4 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 28452869 = 5334913) B5334913
theorem B1665051 : Blo 1665032 1665051 := bstep (se 1 (by rfl) ⟨1248788, by rfl⟩ : syracuseStep 1665051 = 2497577) B2497577
theorem B1665055 : Blo 1665032 1665055 := bstep (se 1 (by rfl) ⟨1248791, by rfl⟩ : syracuseStep 1665055 = 2497583) B2497583
theorem B1665071 : Blo 1665032 1665071 := bstep (se 1 (by rfl) ⟨1248803, by rfl⟩ : syracuseStep 1665071 = 2497607) B2497607
theorem B8005753 : Blo 1665032 8005753 := bstep (se 2 (by rfl) ⟨3002157, by rfl⟩ : syracuseStep 8005753 = 6004315) B6004315
theorem B16009433 : Blo 1665032 16009433 := bstep (se 2 (by rfl) ⟨6003537, by rfl⟩ : syracuseStep 16009433 = 12007075) B12007075
theorem B1665247 : Blo 1665032 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B1665307 : Blo 1665032 1665307 := bstep (se 1 (by rfl) ⟨1248980, by rfl⟩ : syracuseStep 1665307 = 2497961) B2497961
theorem B1665407 : Blo 1665032 1665407 := bstep (se 1 (by rfl) ⟨1249055, by rfl⟩ : syracuseStep 1665407 = 2498111) B2498111
theorem B2107883 : Blo 1665032 2107883 := bstep (se 1 (by rfl) ⟨1580912, by rfl⟩ : syracuseStep 2107883 = 3161825) B3161825
theorem B1665583 : Blo 1665032 1665583 := bstep (se 1 (by rfl) ⟨1249187, by rfl⟩ : syracuseStep 1665583 = 2498375) B2498375
theorem B1665639 : Blo 1665032 1665639 := bstep (se 1 (by rfl) ⟨1249229, by rfl⟩ : syracuseStep 1665639 = 2498459) B2498459
theorem B5409575 : Blo 1665032 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B1666015 : Blo 1665032 1666015 := bstep (se 1 (by rfl) ⟨1249511, by rfl⟩ : syracuseStep 1666015 = 2499023) B2499023
theorem B1666043 : Blo 1665032 1666043 := bstep (se 1 (by rfl) ⟨1249532, by rfl⟩ : syracuseStep 1666043 = 2499065) B2499065
theorem B2165815 : Blo 1665032 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B1666111 : Blo 1665032 1666111 := bstep (se 1 (by rfl) ⟨1249583, by rfl⟩ : syracuseStep 1666111 = 2499167) B2499167
theorem B18975869 : Blo 1665032 18975869 := bstep (se 3 (by rfl) ⟨3557975, by rfl⟩ : syracuseStep 18975869 = 7115951) B7115951
theorem B6753415 : Blo 1665032 6753415 := bstep (se 1 (by rfl) ⟨5065061, by rfl⟩ : syracuseStep 6753415 = 10130123) B10130123
theorem B8006813 : Blo 1665032 8006813 := bstep (se 3 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 8006813 = 3002555) B3002555
theorem B13503871 : Blo 1665032 13503871 := bstep (se 1 (by rfl) ⟨10127903, by rfl⟩ : syracuseStep 13503871 = 20255807) B20255807
theorem B1666431 : Blo 1665032 1666431 := bstep (se 1 (by rfl) ⟨1249823, by rfl⟩ : syracuseStep 1666431 = 2499647) B2499647
theorem B1666459 : Blo 1665032 1666459 := bstep (se 1 (by rfl) ⟨1249844, by rfl⟩ : syracuseStep 1666459 = 2499689) B2499689
theorem B3747239 : Blo 1665032 3747239 := bstep (se 1 (by rfl) ⟨2810429, by rfl⟩ : syracuseStep 3747239 = 5620859) B5620859
theorem B5336543 : Blo 1665032 5336543 := bstep (se 1 (by rfl) ⟨4002407, by rfl⟩ : syracuseStep 5336543 = 8004815) B8004815
theorem B1666527 : Blo 1665032 1666527 := bstep (se 1 (by rfl) ⟨1249895, by rfl⟩ : syracuseStep 1666527 = 2499791) B2499791
theorem B3747419 : Blo 1665032 3747419 := bstep (se 1 (by rfl) ⟨2810564, by rfl⟩ : syracuseStep 3747419 = 5621129) B5621129
theorem B8007275 : Blo 1665032 8007275 := bstep (se 1 (by rfl) ⟨6005456, by rfl⟩ : syracuseStep 8007275 = 12010913) B12010913
theorem B2109179 : Blo 1665032 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B3747833 : Blo 1665032 3747833 := bstep (se 2 (by rfl) ⟨1405437, by rfl⟩ : syracuseStep 3747833 = 2810875) B2810875
theorem B3747923 : Blo 1665032 3747923 := bstep (se 1 (by rfl) ⟨2810942, by rfl⟩ : syracuseStep 3747923 = 5621885) B5621885
theorem B3748103 : Blo 1665032 3748103 := bstep (se 1 (by rfl) ⟨2811077, by rfl⟩ : syracuseStep 3748103 = 5622155) B5622155
theorem B30380507 : Blo 1665032 30380507 := bstep (se 1 (by rfl) ⟨22785380, by rfl⟩ : syracuseStep 30380507 = 45570761) B45570761
theorem B3748409 : Blo 1665032 3748409 := bstep (se 2 (by rfl) ⟨1405653, by rfl⟩ : syracuseStep 3748409 = 2811307) B2811307
theorem B11400131 : Blo 1665032 11400131 := bstep (se 1 (by rfl) ⟨8550098, by rfl⟩ : syracuseStep 11400131 = 17100197) B17100197
theorem B3749129 : Blo 1665032 3749129 := bstep (se 2 (by rfl) ⟨1405923, by rfl⟩ : syracuseStep 3749129 = 2811847) B2811847
theorem B3749183 : Blo 1665032 3749183 := bstep (se 1 (by rfl) ⟨2811887, by rfl⟩ : syracuseStep 3749183 = 5623775) B5623775
theorem B4216171 : Blo 1665032 4216171 := bstep (se 1 (by rfl) ⟨3162128, by rfl⟩ : syracuseStep 4216171 = 6324257) B6324257
theorem B3749291 : Blo 1665032 3749291 := bstep (se 1 (by rfl) ⟨2811968, by rfl⟩ : syracuseStep 3749291 = 5623937) B5623937
theorem B2668123 : Blo 1665032 2668123 := bstep (se 1 (by rfl) ⟨2001092, by rfl⟩ : syracuseStep 2668123 = 4002185) B4002185
theorem B3749615 : Blo 1665032 3749615 := bstep (se 1 (by rfl) ⟨2812211, by rfl⟩ : syracuseStep 3749615 = 5624423) B5624423
theorem B4806431 : Blo 1665032 4806431 := bstep (se 1 (by rfl) ⟨3604823, by rfl⟩ : syracuseStep 4806431 = 7209647) B7209647
theorem B4216607 : Blo 1665032 4216607 := bstep (se 1 (by rfl) ⟨3162455, by rfl⟩ : syracuseStep 4216607 = 6324911) B6324911
theorem B14235425 : Blo 1665032 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B12646205 : Blo 1665032 12646205 := bstep (se 3 (by rfl) ⟨2371163, by rfl⟩ : syracuseStep 12646205 = 4742327) B4742327
theorem B15611777 : Blo 1665032 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B8001641 : Blo 1665032 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B4503691 : Blo 1665032 4503691 := bstep (se 1 (by rfl) ⟨3377768, by rfl⟩ : syracuseStep 4503691 = 6755537) B6755537
theorem B6674665 : Blo 1665032 6674665 := bstep (se 2 (by rfl) ⟨2502999, by rfl⟩ : syracuseStep 6674665 = 5005999) B5005999
theorem B16005437 : Blo 1665032 16005437 := bstep (se 3 (by rfl) ⟨3001019, by rfl⟩ : syracuseStep 16005437 = 6002039) B6002039
theorem B1874335 : Blo 1665032 1874335 := bstep (se 1 (by rfl) ⟨1405751, by rfl⟩ : syracuseStep 1874335 = 2811503) B2811503
theorem B1874407 : Blo 1665032 1874407 := bstep (se 1 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 1874407 = 2811611) B2811611
theorem B12647177 : Blo 1665032 12647177 := bstep (se 2 (by rfl) ⟨4742691, by rfl⟩ : syracuseStep 12647177 = 9485383) B9485383
theorem B9001783 : Blo 1665032 9001783 := bstep (se 1 (by rfl) ⟨6751337, by rfl⟩ : syracuseStep 9001783 = 13502675) B13502675
theorem B36027271 : Blo 1665032 36027271 := bstep (se 1 (by rfl) ⟨27020453, by rfl⟩ : syracuseStep 36027271 = 54040907) B54040907
theorem B4742077 : Blo 1665032 4742077 := bstep (se 3 (by rfl) ⟨889139, by rfl⟩ : syracuseStep 4742077 = 1778279) B1778279
theorem B4275155 : Blo 1665032 4275155 := bstep (se 1 (by rfl) ⟨3206366, by rfl⟩ : syracuseStep 4275155 = 6412733) B6412733
theorem B27393065 : Blo 1665032 27393065 := bstep (se 2 (by rfl) ⟨10272399, by rfl⟩ : syracuseStep 27393065 = 20544799) B20544799
theorem B7117865 : Blo 1665032 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B9256265 : Blo 1665032 9256265 := bstep (se 2 (by rfl) ⟨3471099, by rfl⟩ : syracuseStep 9256265 = 6942199) B6942199
theorem B3161423 : Blo 1665032 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B8003123 : Blo 1665032 8003123 := bstep (se 1 (by rfl) ⟨6002342, by rfl⟩ : syracuseStep 8003123 = 12004685) B12004685
theorem B13508153 : Blo 1665032 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B2498267 : Blo 1665032 2498267 := bstep (se 1 (by rfl) ⟨1873700, by rfl⟩ : syracuseStep 2498267 = 3747401) B3747401
theorem B2850527 : Blo 1665032 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B32448235 : Blo 1665032 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B2498537 : Blo 1665032 2498537 := bstep (se 2 (by rfl) ⟨936951, by rfl⟩ : syracuseStep 2498537 = 1873903) B1873903
theorem B2498615 : Blo 1665032 2498615 := bstep (se 1 (by rfl) ⟨1873961, by rfl⟩ : syracuseStep 2498615 = 3747923) B3747923
theorem B10674337 : Blo 1665032 10674337 := bstep (se 2 (by rfl) ⟨4002876, by rfl⟩ : syracuseStep 10674337 = 8005753) B8005753
theorem B2498735 : Blo 1665032 2498735 := bstep (se 1 (by rfl) ⟨1874051, by rfl⟩ : syracuseStep 2498735 = 3748103) B3748103
theorem B2498939 : Blo 1665032 2498939 := bstep (se 1 (by rfl) ⟨1874204, by rfl⟩ : syracuseStep 2498939 = 3748409) B3748409
theorem B14229989 : Blo 1665032 14229989 := bstep (se 4 (by rfl) ⟨1334061, by rfl⟩ : syracuseStep 14229989 = 2668123) B2668123
theorem B2499113 : Blo 1665032 2499113 := bstep (se 2 (by rfl) ⟨937167, by rfl⟩ : syracuseStep 2499113 = 1874335) B1874335
theorem B17089127 : Blo 1665032 17089127 := bstep (se 1 (by rfl) ⟨12816845, by rfl⟩ : syracuseStep 17089127 = 25633691) B25633691
theorem B2499209 : Blo 1665032 2499209 := bstep (se 2 (by rfl) ⟨937203, by rfl⟩ : syracuseStep 2499209 = 1874407) B1874407
theorem B3375823 : Blo 1665032 3375823 := bstep (se 1 (by rfl) ⟨2531867, by rfl⟩ : syracuseStep 3375823 = 5063735) B5063735
theorem B24019685 : Blo 1665032 24019685 := bstep (se 4 (by rfl) ⟨2251845, by rfl⟩ : syracuseStep 24019685 = 4503691) B4503691
theorem B9487115 : Blo 1665032 9487115 := bstep (se 1 (by rfl) ⟨7115336, by rfl⟩ : syracuseStep 9487115 = 14230673) B14230673
theorem B2499419 : Blo 1665032 2499419 := bstep (se 1 (by rfl) ⟨1874564, by rfl⟩ : syracuseStep 2499419 = 3749129) B3749129
theorem B2499455 : Blo 1665032 2499455 := bstep (se 1 (by rfl) ⟨1874591, by rfl⟩ : syracuseStep 2499455 = 3749183) B3749183
theorem B2499527 : Blo 1665032 2499527 := bstep (se 1 (by rfl) ⟨1874645, by rfl⟩ : syracuseStep 2499527 = 3749291) B3749291
theorem B12002377 : Blo 1665032 12002377 := bstep (se 2 (by rfl) ⟨4500891, by rfl⟩ : syracuseStep 12002377 = 9001783) B9001783
theorem B2499743 : Blo 1665032 2499743 := bstep (se 1 (by rfl) ⟨1874807, by rfl⟩ : syracuseStep 2499743 = 3749615) B3749615
theorem B3204287 : Blo 1665032 3204287 := bstep (se 1 (by rfl) ⟨2403215, by rfl⟩ : syracuseStep 3204287 = 4806431) B4806431
theorem B2811071 : Blo 1665032 2811071 := bstep (se 1 (by rfl) ⟨2108303, by rfl⟩ : syracuseStep 2811071 = 4216607) B4216607
theorem B8430803 : Blo 1665032 8430803 := bstep (se 1 (by rfl) ⟨6323102, by rfl⟩ : syracuseStep 8430803 = 12646205) B12646205
theorem B5621021 : Blo 1665032 5621021 := bstep (se 3 (by rfl) ⟨1053941, by rfl⟩ : syracuseStep 5621021 = 2107883) B2107883
theorem B5334427 : Blo 1665032 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B9004553 : Blo 1665032 9004553 := bstep (se 2 (by rfl) ⟨3376707, by rfl⟩ : syracuseStep 9004553 = 6753415) B6753415
theorem B5621561 : Blo 1665032 5621561 := bstep (se 2 (by rfl) ⟨2108085, by rfl⟩ : syracuseStep 5621561 = 4216171) B4216171
theorem B8431451 : Blo 1665032 8431451 := bstep (se 1 (by rfl) ⟨6323588, by rfl⟩ : syracuseStep 8431451 = 12647177) B12647177
theorem B3606383 : Blo 1665032 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B18262043 : Blo 1665032 18262043 := bstep (se 1 (by rfl) ⟨13696532, by rfl⟩ : syracuseStep 18262043 = 27393065) B27393065
theorem B4745243 : Blo 1665032 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B12650579 : Blo 1665032 12650579 := bstep (se 1 (by rfl) ⟨9487934, by rfl⟩ : syracuseStep 12650579 = 18975869) B18975869
theorem B6170843 : Blo 1665032 6170843 := bstep (se 1 (by rfl) ⟨4628132, by rfl⟩ : syracuseStep 6170843 = 9256265) B9256265
theorem B2107615 : Blo 1665032 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B43264313 : Blo 1665032 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B3557695 : Blo 1665032 3557695 := bstep (se 1 (by rfl) ⟨2668271, by rfl⟩ : syracuseStep 3557695 = 5336543) B5336543
theorem B5335415 : Blo 1665032 5335415 := bstep (se 1 (by rfl) ⟨4001561, by rfl⟩ : syracuseStep 5335415 = 8003123) B8003123
theorem B9005435 : Blo 1665032 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B1665511 : Blo 1665032 1665511 := bstep (se 1 (by rfl) ⟨1249133, by rfl⟩ : syracuseStep 1665511 = 2498267) B2498267
theorem B1665691 : Blo 1665032 1665691 := bstep (se 1 (by rfl) ⟨1249268, by rfl⟩ : syracuseStep 1665691 = 2498537) B2498537
theorem B8432423 : Blo 1665032 8432423 := bstep (se 1 (by rfl) ⟨6324317, by rfl⟩ : syracuseStep 8432423 = 12648635) B12648635
theorem B2108359 : Blo 1665032 2108359 := bstep (se 1 (by rfl) ⟨1581269, by rfl⟩ : syracuseStep 2108359 = 3162539) B3162539
theorem B8899553 : Blo 1665032 8899553 := bstep (se 2 (by rfl) ⟨3337332, by rfl⟩ : syracuseStep 8899553 = 6674665) B6674665
theorem B20253671 : Blo 1665032 20253671 := bstep (se 1 (by rfl) ⟨15190253, by rfl⟩ : syracuseStep 20253671 = 30380507) B30380507
theorem B1666159 : Blo 1665032 1666159 := bstep (se 1 (by rfl) ⟨1249619, by rfl⟩ : syracuseStep 1666159 = 2499239) B2499239
theorem B1666239 : Blo 1665032 1666239 := bstep (se 1 (by rfl) ⟨1249679, by rfl⟩ : syracuseStep 1666239 = 2499359) B2499359
theorem B1666255 : Blo 1665032 1666255 := bstep (se 1 (by rfl) ⟨1249691, by rfl⟩ : syracuseStep 1666255 = 2499383) B2499383
theorem B5696839 : Blo 1665032 5696839 := bstep (se 1 (by rfl) ⟨4272629, by rfl⟩ : syracuseStep 5696839 = 8545259) B8545259
theorem B1666375 : Blo 1665032 1666375 := bstep (se 1 (by rfl) ⟨1249781, by rfl⟩ : syracuseStep 1666375 = 2499563) B2499563
theorem B12824045 : Blo 1665032 12824045 := bstep (se 3 (by rfl) ⟨2404508, by rfl⟩ : syracuseStep 12824045 = 4809017) B4809017
theorem B9490283 : Blo 1665032 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B10407851 : Blo 1665032 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B18968579 : Blo 1665032 18968579 := bstep (se 1 (by rfl) ⟨14226434, by rfl⟩ : syracuseStep 18968579 = 28452869) B28452869
theorem B2887753 : Blo 1665032 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B10670291 : Blo 1665032 10670291 := bstep (se 1 (by rfl) ⟨8002718, by rfl⟩ : syracuseStep 10670291 = 16005437) B16005437
theorem B5624477 : Blo 1665032 5624477 := bstep (se 3 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 5624477 = 2109179) B2109179
theorem B5337875 : Blo 1665032 5337875 := bstep (se 1 (by rfl) ⟨4003406, by rfl⟩ : syracuseStep 5337875 = 8006813) B8006813
theorem B5338183 : Blo 1665032 5338183 := bstep (se 1 (by rfl) ⟨4003637, by rfl⟩ : syracuseStep 5338183 = 8007275) B8007275
theorem B27023051 : Blo 1665032 27023051 := bstep (se 1 (by rfl) ⟨20267288, by rfl⟩ : syracuseStep 27023051 = 40534577) B40534577
theorem B7116635 : Blo 1665032 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B7600087 : Blo 1665032 7600087 := bstep (se 1 (by rfl) ⟨5700065, by rfl⟩ : syracuseStep 7600087 = 11400131) B11400131
theorem B8001755 : Blo 1665032 8001755 := bstep (se 1 (by rfl) ⟨6001316, by rfl⟩ : syracuseStep 8001755 = 12002633) B12002633
theorem B10131803 : Blo 1665032 10131803 := bstep (se 1 (by rfl) ⟨7598852, by rfl⟩ : syracuseStep 10131803 = 15197705) B15197705
theorem B48036361 : Blo 1665032 48036361 := bstep (se 2 (by rfl) ⟨18013635, by rfl⟩ : syracuseStep 48036361 = 36027271) B36027271
theorem B10672697 : Blo 1665032 10672697 := bstep (se 2 (by rfl) ⟨4002261, by rfl⟩ : syracuseStep 10672697 = 8004523) B8004523
theorem B6322769 : Blo 1665032 6322769 := bstep (se 2 (by rfl) ⟨2371038, by rfl⟩ : syracuseStep 6322769 = 4742077) B4742077
theorem B10672955 : Blo 1665032 10672955 := bstep (se 1 (by rfl) ⟨8004716, by rfl⟩ : syracuseStep 10672955 = 16009433) B16009433
theorem B18005161 : Blo 1665032 18005161 := bstep (se 2 (by rfl) ⟨6751935, by rfl⟩ : syracuseStep 18005161 = 13503871) B13503871
theorem B21347549 : Blo 1665032 21347549 := bstep (se 3 (by rfl) ⟨4002665, by rfl⟩ : syracuseStep 21347549 = 8005331) B8005331
theorem B2850103 : Blo 1665032 2850103 := bstep (se 1 (by rfl) ⟨2137577, by rfl⟩ : syracuseStep 2850103 = 4275155) B4275155
theorem B2498159 : Blo 1665032 2498159 := bstep (se 1 (by rfl) ⟨1873619, by rfl⟩ : syracuseStep 2498159 = 3747239) B3747239
theorem B2498279 : Blo 1665032 2498279 := bstep (se 1 (by rfl) ⟨1873709, by rfl⟩ : syracuseStep 2498279 = 3747419) B3747419
theorem B1900351 : Blo 1665032 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B2498555 : Blo 1665032 2498555 := bstep (se 1 (by rfl) ⟨1873916, by rfl⟩ : syracuseStep 2498555 = 3747833) B3747833
theorem B3850337 : Blo 1665032 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B2810153 : Blo 1665032 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B9486659 : Blo 1665032 9486659 := bstep (se 1 (by rfl) ⟨7114994, by rfl⟩ : syracuseStep 9486659 = 14229989) B14229989
theorem B4743593 : Blo 1665032 4743593 := bstep (se 2 (by rfl) ⟨1778847, by rfl⟩ : syracuseStep 4743593 = 3557695) B3557695
theorem B6324743 : Blo 1665032 6324743 := bstep (se 1 (by rfl) ⟨4743557, by rfl⟩ : syracuseStep 6324743 = 9487115) B9487115
theorem B5620535 : Blo 1665032 5620535 := bstep (se 1 (by rfl) ⟨4215401, by rfl⟩ : syracuseStep 5620535 = 8430803) B8430803
theorem B18015367 : Blo 1665032 18015367 := bstep (se 1 (by rfl) ⟨13511525, by rfl⟩ : syracuseStep 18015367 = 27023051) B27023051
theorem B5620967 : Blo 1665032 5620967 := bstep (se 1 (by rfl) ⟨4215725, by rfl⟩ : syracuseStep 5620967 = 8431451) B8431451
theorem B4744423 : Blo 1665032 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B2811145 : Blo 1665032 2811145 := bstep (se 2 (by rfl) ⟨1054179, by rfl⟩ : syracuseStep 2811145 = 2108359) B2108359
theorem B12174695 : Blo 1665032 12174695 := bstep (se 1 (by rfl) ⟨9131021, by rfl⟩ : syracuseStep 12174695 = 18262043) B18262043
theorem B5334503 : Blo 1665032 5334503 := bstep (se 1 (by rfl) ⟨4000877, by rfl⟩ : syracuseStep 5334503 = 8001755) B8001755
theorem B4113895 : Blo 1665032 4113895 := bstep (se 1 (by rfl) ⟨3085421, by rfl⟩ : syracuseStep 4113895 = 6170843) B6170843
theorem B3556943 : Blo 1665032 3556943 := bstep (se 1 (by rfl) ⟨2667707, by rfl⟩ : syracuseStep 3556943 = 5335415) B5335415
theorem B10135205 : Blo 1665032 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B7595785 : Blo 1665032 7595785 := bstep (se 2 (by rfl) ⟨2848419, by rfl⟩ : syracuseStep 7595785 = 5696839) B5696839
theorem B5621615 : Blo 1665032 5621615 := bstep (se 1 (by rfl) ⟨4216211, by rfl⟩ : syracuseStep 5621615 = 8432423) B8432423
theorem B7112569 : Blo 1665032 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B5933035 : Blo 1665032 5933035 := bstep (se 1 (by rfl) ⟨4449776, by rfl⟩ : syracuseStep 5933035 = 8899553) B8899553
theorem B13502447 : Blo 1665032 13502447 := bstep (se 1 (by rfl) ⟨10126835, by rfl⟩ : syracuseStep 13502447 = 20253671) B20253671
theorem B14231699 : Blo 1665032 14231699 := bstep (se 1 (by rfl) ⟨10673774, by rfl⟩ : syracuseStep 14231699 = 21347549) B21347549
theorem B1665439 : Blo 1665032 1665439 := bstep (se 1 (by rfl) ⟨1249079, by rfl⟩ : syracuseStep 1665439 = 2498159) B2498159
theorem B1665519 : Blo 1665032 1665519 := bstep (se 1 (by rfl) ⟨1249139, by rfl⟩ : syracuseStep 1665519 = 2498279) B2498279
theorem B6326855 : Blo 1665032 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B1665703 : Blo 1665032 1665703 := bstep (se 1 (by rfl) ⟨1249277, by rfl⟩ : syracuseStep 1665703 = 2498555) B2498555
theorem B1665743 : Blo 1665032 1665743 := bstep (se 1 (by rfl) ⟨1249307, by rfl⟩ : syracuseStep 1665743 = 2498615) B2498615
theorem B1665823 : Blo 1665032 1665823 := bstep (se 1 (by rfl) ⟨1249367, by rfl⟩ : syracuseStep 1665823 = 2498735) B2498735
theorem B7113527 : Blo 1665032 7113527 := bstep (se 1 (by rfl) ⟨5335145, by rfl⟩ : syracuseStep 7113527 = 10670291) B10670291
theorem B14232449 : Blo 1665032 14232449 := bstep (se 2 (by rfl) ⟨5337168, by rfl⟩ : syracuseStep 14232449 = 10674337) B10674337
theorem B1665959 : Blo 1665032 1665959 := bstep (se 1 (by rfl) ⟨1249469, by rfl⟩ : syracuseStep 1665959 = 2498939) B2498939
theorem B1666075 : Blo 1665032 1666075 := bstep (se 1 (by rfl) ⟨1249556, by rfl⟩ : syracuseStep 1666075 = 2499113) B2499113
theorem B1666139 : Blo 1665032 1666139 := bstep (se 1 (by rfl) ⟨1249604, by rfl⟩ : syracuseStep 1666139 = 2499209) B2499209
theorem B3558583 : Blo 1665032 3558583 := bstep (se 1 (by rfl) ⟨2668937, by rfl⟩ : syracuseStep 3558583 = 5337875) B5337875
theorem B1666279 : Blo 1665032 1666279 := bstep (se 1 (by rfl) ⟨1249709, by rfl⟩ : syracuseStep 1666279 = 2499419) B2499419
theorem B1666303 : Blo 1665032 1666303 := bstep (se 1 (by rfl) ⟨1249727, by rfl⟩ : syracuseStep 1666303 = 2499455) B2499455
theorem B1666351 : Blo 1665032 1666351 := bstep (se 1 (by rfl) ⟨1249763, by rfl⟩ : syracuseStep 1666351 = 2499527) B2499527
theorem B64048481 : Blo 1665032 64048481 := bstep (se 2 (by rfl) ⟨24018180, by rfl⟩ : syracuseStep 64048481 = 48036361) B48036361
theorem B1666495 : Blo 1665032 1666495 := bstep (se 1 (by rfl) ⟨1249871, by rfl⟩ : syracuseStep 1666495 = 2499743) B2499743
theorem B3747347 : Blo 1665032 3747347 := bstep (se 1 (by rfl) ⟨2810510, by rfl⟩ : syracuseStep 3747347 = 5621021) B5621021
theorem B4501097 : Blo 1665032 4501097 := bstep (se 2 (by rfl) ⟨1687911, by rfl⟩ : syracuseStep 4501097 = 3375823) B3375823
theorem B3747707 : Blo 1665032 3747707 := bstep (se 1 (by rfl) ⟨2810780, by rfl⟩ : syracuseStep 3747707 = 5621561) B5621561
theorem B2404255 : Blo 1665032 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B8433719 : Blo 1665032 8433719 := bstep (se 1 (by rfl) ⟨6325289, by rfl⟩ : syracuseStep 8433719 = 12650579) B12650579
theorem B16003169 : Blo 1665032 16003169 := bstep (se 2 (by rfl) ⟨6001188, by rfl⟩ : syracuseStep 16003169 = 12002377) B12002377
theorem B24006881 : Blo 1665032 24006881 := bstep (se 2 (by rfl) ⟨9002580, by rfl⟩ : syracuseStep 24006881 = 18005161) B18005161
theorem B6754535 : Blo 1665032 6754535 := bstep (se 1 (by rfl) ⟨5065901, by rfl⟩ : syracuseStep 6754535 = 10131803) B10131803
theorem B7115131 : Blo 1665032 7115131 := bstep (se 1 (by rfl) ⟨5336348, by rfl⟩ : syracuseStep 7115131 = 10672697) B10672697
theorem B4215179 : Blo 1665032 4215179 := bstep (se 1 (by rfl) ⟨3161384, by rfl⟩ : syracuseStep 4215179 = 6322769) B6322769
theorem B7115303 : Blo 1665032 7115303 := bstep (se 1 (by rfl) ⟨5336477, by rfl⟩ : syracuseStep 7115303 = 10672955) B10672955
theorem B8549363 : Blo 1665032 8549363 := bstep (se 1 (by rfl) ⟨6412022, by rfl⟩ : syracuseStep 8549363 = 12824045) B12824045
theorem B12645719 : Blo 1665032 12645719 := bstep (se 1 (by rfl) ⟨9484289, by rfl⟩ : syracuseStep 12645719 = 18968579) B18968579
theorem B12653981 : Blo 1665032 12653981 := bstep (se 3 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 12653981 = 4745243) B4745243
theorem B11392751 : Blo 1665032 11392751 := bstep (se 1 (by rfl) ⟨8544563, by rfl⟩ : syracuseStep 11392751 = 17089127) B17089127
theorem B3749651 : Blo 1665032 3749651 := bstep (se 1 (by rfl) ⟨2812238, by rfl⟩ : syracuseStep 3749651 = 5624477) B5624477
theorem B16013123 : Blo 1665032 16013123 := bstep (se 1 (by rfl) ⟨12009842, by rfl⟩ : syracuseStep 16013123 = 24019685) B24019685
theorem B2136191 : Blo 1665032 2136191 := bstep (se 1 (by rfl) ⟨1602143, by rfl⟩ : syracuseStep 2136191 = 3204287) B3204287
theorem B1874047 : Blo 1665032 1874047 := bstep (se 1 (by rfl) ⟨1405535, by rfl⟩ : syracuseStep 1874047 = 2811071) B2811071
theorem B6003035 : Blo 1665032 6003035 := bstep (se 1 (by rfl) ⟨4502276, by rfl⟩ : syracuseStep 6003035 = 9004553) B9004553
theorem B7117577 : Blo 1665032 7117577 := bstep (se 2 (by rfl) ⟨2669091, by rfl⟩ : syracuseStep 7117577 = 5338183) B5338183
theorem B28842875 : Blo 1665032 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B6003623 : Blo 1665032 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B3800137 : Blo 1665032 3800137 := bstep (se 2 (by rfl) ⟨1425051, by rfl⟩ : syracuseStep 3800137 = 2850103) B2850103
theorem B40533797 : Blo 1665032 40533797 := bstep (se 4 (by rfl) ⟨3800043, by rfl⟩ : syracuseStep 40533797 = 7600087) B7600087
theorem B6938567 : Blo 1665032 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B2498729 : Blo 1665032 2498729 := bstep (se 2 (by rfl) ⟨937023, by rfl⟩ : syracuseStep 2498729 = 1874047) B1874047
theorem B6324439 : Blo 1665032 6324439 := bstep (se 1 (by rfl) ⟨4743329, by rfl⟩ : syracuseStep 6324439 = 9486659) B9486659
theorem B2810119 : Blo 1665032 2810119 := bstep (se 1 (by rfl) ⟨2107589, by rfl⟩ : syracuseStep 2810119 = 4215179) B4215179
theorem B3162395 : Blo 1665032 3162395 := bstep (se 1 (by rfl) ⟨2371796, by rfl⟩ : syracuseStep 3162395 = 4743593) B4743593
theorem B4743535 : Blo 1665032 4743535 := bstep (se 1 (by rfl) ⟨3557651, by rfl⟩ : syracuseStep 4743535 = 7115303) B7115303
theorem B9486841 : Blo 1665032 9486841 := bstep (se 2 (by rfl) ⟨3557565, by rfl⟩ : syracuseStep 9486841 = 7115131) B7115131
theorem B8430479 : Blo 1665032 8430479 := bstep (se 1 (by rfl) ⟨6322859, by rfl⟩ : syracuseStep 8430479 = 12645719) B12645719
theorem B7595167 : Blo 1665032 7595167 := bstep (se 1 (by rfl) ⟨5696375, by rfl⟩ : syracuseStep 7595167 = 11392751) B11392751
theorem B2499767 : Blo 1665032 2499767 := bstep (se 1 (by rfl) ⟨1874825, by rfl⟩ : syracuseStep 2499767 = 3749651) B3749651
theorem B10675415 : Blo 1665032 10675415 := bstep (se 1 (by rfl) ⟨8006561, by rfl⟩ : syracuseStep 10675415 = 16013123) B16013123
theorem B9487799 : Blo 1665032 9487799 := bstep (se 1 (by rfl) ⟨7115849, by rfl⟩ : syracuseStep 9487799 = 14231699) B14231699
theorem B24020489 : Blo 1665032 24020489 := bstep (se 2 (by rfl) ⟨9007683, by rfl⟩ : syracuseStep 24020489 = 18015367) B18015367
theorem B4744777 : Blo 1665032 4744777 := bstep (se 2 (by rfl) ⟨1779291, by rfl⟩ : syracuseStep 4744777 = 3558583) B3558583
theorem B6325897 : Blo 1665032 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B4745051 : Blo 1665032 4745051 := bstep (se 1 (by rfl) ⟨3558788, by rfl⟩ : syracuseStep 4745051 = 7117577) B7117577
theorem B19228583 : Blo 1665032 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B9488299 : Blo 1665032 9488299 := bstep (se 1 (by rfl) ⟨7116224, by rfl⟩ : syracuseStep 9488299 = 14232449) B14232449
theorem B42698987 : Blo 1665032 42698987 := bstep (se 1 (by rfl) ⟨32024240, by rfl⟩ : syracuseStep 42698987 = 64048481) B64048481
theorem B10127713 : Blo 1665032 10127713 := bstep (se 2 (by rfl) ⟨3797892, by rfl⟩ : syracuseStep 10127713 = 7595785) B7595785
theorem B3000731 : Blo 1665032 3000731 := bstep (se 1 (by rfl) ⟨2250548, by rfl⟩ : syracuseStep 3000731 = 4501097) B4501097
theorem B3205673 : Blo 1665032 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B5622479 : Blo 1665032 5622479 := bstep (se 1 (by rfl) ⟨4216859, by rfl⟩ : syracuseStep 5622479 = 8433719) B8433719
theorem B10668779 : Blo 1665032 10668779 := bstep (se 1 (by rfl) ⟨8001584, by rfl⟩ : syracuseStep 10668779 = 16003169) B16003169
theorem B2566891 : Blo 1665032 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B5696509 : Blo 1665032 5696509 := bstep (se 3 (by rfl) ⟨1068095, by rfl⟩ : syracuseStep 5696509 = 2136191) B2136191
theorem B3747023 : Blo 1665032 3747023 := bstep (se 1 (by rfl) ⟨2810267, by rfl⟩ : syracuseStep 3747023 = 5620535) B5620535
theorem B3747311 : Blo 1665032 3747311 := bstep (se 1 (by rfl) ⟨2810483, by rfl⟩ : syracuseStep 3747311 = 5620967) B5620967
theorem B2371295 : Blo 1665032 2371295 := bstep (se 1 (by rfl) ⟨1778471, by rfl⟩ : syracuseStep 2371295 = 3556943) B3556943
theorem B3747743 : Blo 1665032 3747743 := bstep (se 1 (by rfl) ⟨2810807, by rfl⟩ : syracuseStep 3747743 = 5621615) B5621615
theorem B14225341 : Blo 1665032 14225341 := bstep (se 3 (by rfl) ⟨2667251, by rfl⟩ : syracuseStep 14225341 = 5334503) B5334503
theorem B5066849 : Blo 1665032 5066849 := bstep (se 2 (by rfl) ⟨1900068, by rfl⟩ : syracuseStep 5066849 = 3800137) B3800137
theorem B4002023 : Blo 1665032 4002023 := bstep (se 1 (by rfl) ⟨3001517, by rfl⟩ : syracuseStep 4002023 = 6003035) B6003035
theorem B3748193 : Blo 1665032 3748193 := bstep (se 2 (by rfl) ⟨1405572, by rfl⟩ : syracuseStep 3748193 = 2811145) B2811145
theorem B4002415 : Blo 1665032 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B5485193 : Blo 1665032 5485193 := bstep (se 2 (by rfl) ⟨2056947, by rfl⟩ : syracuseStep 5485193 = 4113895) B4113895
theorem B9483425 : Blo 1665032 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B27022531 : Blo 1665032 27022531 := bstep (se 1 (by rfl) ⟨20266898, by rfl⟩ : syracuseStep 27022531 = 40533797) B40533797
theorem B4625711 : Blo 1665032 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B7910713 : Blo 1665032 7910713 := bstep (se 2 (by rfl) ⟨2966517, by rfl⟩ : syracuseStep 7910713 = 5933035) B5933035
theorem B16004587 : Blo 1665032 16004587 := bstep (se 1 (by rfl) ⟨12003440, by rfl⟩ : syracuseStep 16004587 = 24006881) B24006881
theorem B4503023 : Blo 1665032 4503023 := bstep (se 1 (by rfl) ⟨3377267, by rfl⟩ : syracuseStep 4503023 = 6754535) B6754535
theorem B1873435 : Blo 1665032 1873435 := bstep (se 1 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 1873435 = 2810153) B2810153
theorem B4216495 : Blo 1665032 4216495 := bstep (se 1 (by rfl) ⟨3162371, by rfl⟩ : syracuseStep 4216495 = 6324743) B6324743
theorem B5699575 : Blo 1665032 5699575 := bstep (se 1 (by rfl) ⟨4274681, by rfl⟩ : syracuseStep 5699575 = 8549363) B8549363
theorem B8116463 : Blo 1665032 8116463 := bstep (se 1 (by rfl) ⟨6087347, by rfl⟩ : syracuseStep 8116463 = 12174695) B12174695
theorem B8435987 : Blo 1665032 8435987 := bstep (se 1 (by rfl) ⟨6326990, by rfl⟩ : syracuseStep 8435987 = 12653981) B12653981
theorem B6756803 : Blo 1665032 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B9001631 : Blo 1665032 9001631 := bstep (se 1 (by rfl) ⟨6751223, by rfl⟩ : syracuseStep 9001631 = 13502447) B13502447
theorem B4217903 : Blo 1665032 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B4742351 : Blo 1665032 4742351 := bstep (se 1 (by rfl) ⟨3556763, by rfl⟩ : syracuseStep 4742351 = 7113527) B7113527
theorem B2498231 : Blo 1665032 2498231 := bstep (se 1 (by rfl) ⟨1873673, by rfl⟩ : syracuseStep 2498231 = 3747347) B3747347
theorem B2498471 : Blo 1665032 2498471 := bstep (se 1 (by rfl) ⟨1873853, by rfl⟩ : syracuseStep 2498471 = 3747707) B3747707
theorem B2498795 : Blo 1665032 2498795 := bstep (se 1 (by rfl) ⟨1874096, by rfl⟩ : syracuseStep 2498795 = 3748193) B3748193
theorem B6324713 : Blo 1665032 6324713 := bstep (se 2 (by rfl) ⟨2371767, by rfl⟩ : syracuseStep 6324713 = 4743535) B4743535
theorem B5620319 : Blo 1665032 5620319 := bstep (se 1 (by rfl) ⟨4215239, by rfl⟩ : syracuseStep 5620319 = 8430479) B8430479
theorem B12649121 : Blo 1665032 12649121 := bstep (se 2 (by rfl) ⟨4743420, by rfl⟩ : syracuseStep 12649121 = 9486841) B9486841
theorem B6325199 : Blo 1665032 6325199 := bstep (se 1 (by rfl) ⟨4743899, by rfl⟩ : syracuseStep 6325199 = 9487799) B9487799
theorem B3163367 : Blo 1665032 3163367 := bstep (se 1 (by rfl) ⟨2372525, by rfl⟩ : syracuseStep 3163367 = 4745051) B4745051
theorem B7595345 : Blo 1665032 7595345 := bstep (se 2 (by rfl) ⟨2848254, by rfl⟩ : syracuseStep 7595345 = 5696509) B5696509
theorem B10126889 : Blo 1665032 10126889 := bstep (se 2 (by rfl) ⟨3797583, by rfl⟩ : syracuseStep 10126889 = 7595167) B7595167
theorem B36030041 : Blo 1665032 36030041 := bstep (se 2 (by rfl) ⟨13511265, by rfl⟩ : syracuseStep 36030041 = 27022531) B27022531
theorem B7112519 : Blo 1665032 7112519 := bstep (se 1 (by rfl) ⟨5334389, by rfl⟩ : syracuseStep 7112519 = 10668779) B10668779
theorem B2811935 : Blo 1665032 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B6326369 : Blo 1665032 6326369 := bstep (se 2 (by rfl) ⟨2372388, by rfl⟩ : syracuseStep 6326369 = 4744777) B4744777
theorem B5621993 : Blo 1665032 5621993 := bstep (se 2 (by rfl) ⟨2108247, by rfl⟩ : syracuseStep 5621993 = 4216495) B4216495
theorem B1665487 : Blo 1665032 1665487 := bstep (se 1 (by rfl) ⟨1249115, by rfl⟩ : syracuseStep 1665487 = 2498231) B2498231
theorem B12651065 : Blo 1665032 12651065 := bstep (se 2 (by rfl) ⟨4744149, by rfl⟩ : syracuseStep 12651065 = 9488299) B9488299
theorem B18967121 : Blo 1665032 18967121 := bstep (se 2 (by rfl) ⟨7112670, by rfl⟩ : syracuseStep 18967121 = 14225341) B14225341
theorem B1665647 : Blo 1665032 1665647 := bstep (se 1 (by rfl) ⟨1249235, by rfl⟩ : syracuseStep 1665647 = 2498471) B2498471
theorem B3377899 : Blo 1665032 3377899 := bstep (se 1 (by rfl) ⟨2533424, by rfl⟩ : syracuseStep 3377899 = 5066849) B5066849
theorem B1665819 : Blo 1665032 1665819 := bstep (se 1 (by rfl) ⟨1249364, by rfl⟩ : syracuseStep 1665819 = 2498729) B2498729
theorem B2108263 : Blo 1665032 2108263 := bstep (se 1 (by rfl) ⟨1581197, by rfl⟩ : syracuseStep 2108263 = 3162395) B3162395
theorem B8432585 : Blo 1665032 8432585 := bstep (se 2 (by rfl) ⟨3162219, by rfl⟩ : syracuseStep 8432585 = 6324439) B6324439
theorem B3746825 : Blo 1665032 3746825 := bstep (se 2 (by rfl) ⟨1405059, by rfl⟩ : syracuseStep 3746825 = 2810119) B2810119
theorem B3656795 : Blo 1665032 3656795 := bstep (se 1 (by rfl) ⟨2742596, by rfl⟩ : syracuseStep 3656795 = 5485193) B5485193
theorem B13503617 : Blo 1665032 13503617 := bstep (se 2 (by rfl) ⟨5063856, by rfl⟩ : syracuseStep 13503617 = 10127713) B10127713
theorem B1666511 : Blo 1665032 1666511 := bstep (se 1 (by rfl) ⟨1249883, by rfl⟩ : syracuseStep 1666511 = 2499767) B2499767
theorem B3083807 : Blo 1665032 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B3002015 : Blo 1665032 3002015 := bstep (se 1 (by rfl) ⟨2251511, by rfl⟩ : syracuseStep 3002015 = 4503023) B4503023
theorem B5410975 : Blo 1665032 5410975 := bstep (se 1 (by rfl) ⟨4058231, by rfl⟩ : syracuseStep 5410975 = 8116463) B8116463
theorem B5623991 : Blo 1665032 5623991 := bstep (se 1 (by rfl) ⟨4217993, by rfl⟩ : syracuseStep 5623991 = 8435987) B8435987
theorem B10547617 : Blo 1665032 10547617 := bstep (se 2 (by rfl) ⟨3955356, by rfl⟩ : syracuseStep 10547617 = 7910713) B7910713
theorem B6001087 : Blo 1665032 6001087 := bstep (se 1 (by rfl) ⟨4500815, by rfl⟩ : syracuseStep 6001087 = 9001631) B9001631
theorem B3748319 : Blo 1665032 3748319 := bstep (se 1 (by rfl) ⟨2811239, by rfl⟩ : syracuseStep 3748319 = 5622479) B5622479
theorem B8434529 : Blo 1665032 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B7599433 : Blo 1665032 7599433 := bstep (se 2 (by rfl) ⟨2849787, by rfl⟩ : syracuseStep 7599433 = 5699575) B5699575
theorem B2668015 : Blo 1665032 2668015 := bstep (se 1 (by rfl) ⟨2001011, by rfl⟩ : syracuseStep 2668015 = 4002023) B4002023
theorem B21346213 : Blo 1665032 21346213 := bstep (se 4 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 21346213 = 4002415) B4002415
theorem B6322283 : Blo 1665032 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B7116943 : Blo 1665032 7116943 := bstep (se 1 (by rfl) ⟨5337707, by rfl⟩ : syracuseStep 7116943 = 10675415) B10675415
theorem B3422521 : Blo 1665032 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B16013659 : Blo 1665032 16013659 := bstep (se 1 (by rfl) ⟨12010244, by rfl⟩ : syracuseStep 16013659 = 24020489) B24020489
theorem B8001949 : Blo 1665032 8001949 := bstep (se 3 (by rfl) ⟨1500365, by rfl⟩ : syracuseStep 8001949 = 3000731) B3000731
theorem B12819055 : Blo 1665032 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B28465991 : Blo 1665032 28465991 := bstep (se 1 (by rfl) ⟨21349493, by rfl⟩ : syracuseStep 28465991 = 42698987) B42698987
theorem B4504535 : Blo 1665032 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B2137115 : Blo 1665032 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B6323453 : Blo 1665032 6323453 := bstep (se 3 (by rfl) ⟨1185647, by rfl⟩ : syracuseStep 6323453 = 2371295) B2371295
theorem B21339449 : Blo 1665032 21339449 := bstep (se 2 (by rfl) ⟨8002293, by rfl⟩ : syracuseStep 21339449 = 16004587) B16004587
theorem B2497913 : Blo 1665032 2497913 := bstep (se 2 (by rfl) ⟨936717, by rfl⟩ : syracuseStep 2497913 = 1873435) B1873435
theorem B2498015 : Blo 1665032 2498015 := bstep (se 1 (by rfl) ⟨1873511, by rfl⟩ : syracuseStep 2498015 = 3747023) B3747023
theorem B3161567 : Blo 1665032 3161567 := bstep (se 1 (by rfl) ⟨2371175, by rfl⟩ : syracuseStep 3161567 = 4742351) B4742351
theorem B2498207 : Blo 1665032 2498207 := bstep (se 1 (by rfl) ⟨1873655, by rfl⟩ : syracuseStep 2498207 = 3747311) B3747311
theorem B2498495 : Blo 1665032 2498495 := bstep (se 1 (by rfl) ⟨1873871, by rfl⟩ : syracuseStep 2498495 = 3747743) B3747743
theorem B2498879 : Blo 1665032 2498879 := bstep (se 1 (by rfl) ⟨1874159, by rfl⟩ : syracuseStep 2498879 = 3748319) B3748319
theorem B4563361 : Blo 1665032 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B5063563 : Blo 1665032 5063563 := bstep (se 1 (by rfl) ⟨3797672, by rfl⟩ : syracuseStep 5063563 = 7595345) B7595345
theorem B6751259 : Blo 1665032 6751259 := bstep (se 1 (by rfl) ⟨5063444, by rfl⟩ : syracuseStep 6751259 = 10126889) B10126889
theorem B24020027 : Blo 1665032 24020027 := bstep (se 1 (by rfl) ⟨18015020, by rfl⟩ : syracuseStep 24020027 = 36030041) B36030041
theorem B2811017 : Blo 1665032 2811017 := bstep (se 2 (by rfl) ⟨1054131, by rfl⟩ : syracuseStep 2811017 = 2108263) B2108263
theorem B5621723 : Blo 1665032 5621723 := bstep (se 1 (by rfl) ⟨4216292, by rfl⟩ : syracuseStep 5621723 = 8432585) B8432585
theorem B3557353 : Blo 1665032 3557353 := bstep (se 2 (by rfl) ⟨1334007, by rfl⟩ : syracuseStep 3557353 = 2668015) B2668015
theorem B1665275 : Blo 1665032 1665275 := bstep (se 1 (by rfl) ⟨1248956, by rfl⟩ : syracuseStep 1665275 = 2497913) B2497913
theorem B1665343 : Blo 1665032 1665343 := bstep (se 1 (by rfl) ⟨1249007, by rfl⟩ : syracuseStep 1665343 = 2498015) B2498015
theorem B2107711 : Blo 1665032 2107711 := bstep (se 1 (by rfl) ⟨1580783, by rfl⟩ : syracuseStep 2107711 = 3161567) B3161567
theorem B1665471 : Blo 1665032 1665471 := bstep (se 1 (by rfl) ⟨1249103, by rfl⟩ : syracuseStep 1665471 = 2498207) B2498207
theorem B2001343 : Blo 1665032 2001343 := bstep (se 1 (by rfl) ⟨1501007, by rfl⟩ : syracuseStep 2001343 = 3002015) B3002015
theorem B28461617 : Blo 1665032 28461617 := bstep (se 2 (by rfl) ⟨10673106, by rfl⟩ : syracuseStep 28461617 = 21346213) B21346213
theorem B1665663 : Blo 1665032 1665663 := bstep (se 1 (by rfl) ⟨1249247, by rfl⟩ : syracuseStep 1665663 = 2498495) B2498495
theorem B1665863 : Blo 1665032 1665863 := bstep (se 1 (by rfl) ⟨1249397, by rfl⟩ : syracuseStep 1665863 = 2498795) B2498795
theorem B9489257 : Blo 1665032 9489257 := bstep (se 2 (by rfl) ⟨3558471, by rfl⟩ : syracuseStep 9489257 = 7116943) B7116943
theorem B3746879 : Blo 1665032 3746879 := bstep (se 1 (by rfl) ⟨2810159, by rfl⟩ : syracuseStep 3746879 = 5620319) B5620319
theorem B8432747 : Blo 1665032 8432747 := bstep (se 1 (by rfl) ⟨6324560, by rfl⟩ : syracuseStep 8432747 = 12649121) B12649121
theorem B21351545 : Blo 1665032 21351545 := bstep (se 2 (by rfl) ⟨8006829, by rfl⟩ : syracuseStep 21351545 = 16013659) B16013659
theorem B10669265 : Blo 1665032 10669265 := bstep (se 2 (by rfl) ⟨4000974, by rfl⟩ : syracuseStep 10669265 = 8001949) B8001949
theorem B5623019 : Blo 1665032 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B17092073 : Blo 1665032 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B2108911 : Blo 1665032 2108911 := bstep (se 1 (by rfl) ⟨1581683, by rfl⟩ : syracuseStep 2108911 = 3163367) B3163367
theorem B39005813 : Blo 1665032 39005813 := bstep (se 5 (by rfl) ⟨1828397, by rfl⟩ : syracuseStep 39005813 = 3656795) B3656795
theorem B4214855 : Blo 1665032 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B3747995 : Blo 1665032 3747995 := bstep (se 1 (by rfl) ⟨2810996, by rfl⟩ : syracuseStep 3747995 = 5621993) B5621993
theorem B8434043 : Blo 1665032 8434043 := bstep (se 1 (by rfl) ⟨6325532, by rfl⟩ : syracuseStep 8434043 = 12651065) B12651065
theorem B12644747 : Blo 1665032 12644747 := bstep (se 1 (by rfl) ⟨9483560, by rfl⟩ : syracuseStep 12644747 = 18967121) B18967121
theorem B18977327 : Blo 1665032 18977327 := bstep (se 1 (by rfl) ⟨14232995, by rfl⟩ : syracuseStep 18977327 = 28465991) B28465991
theorem B3003023 : Blo 1665032 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B4215635 : Blo 1665032 4215635 := bstep (se 1 (by rfl) ⟨3161726, by rfl⟩ : syracuseStep 4215635 = 6323453) B6323453
theorem B14226299 : Blo 1665032 14226299 := bstep (se 1 (by rfl) ⟨10669724, by rfl⟩ : syracuseStep 14226299 = 21339449) B21339449
theorem B5698973 : Blo 1665032 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B3749327 : Blo 1665032 3749327 := bstep (se 1 (by rfl) ⟨2811995, by rfl⟩ : syracuseStep 3749327 = 5623991) B5623991
theorem B7214633 : Blo 1665032 7214633 := bstep (se 2 (by rfl) ⟨2705487, by rfl⟩ : syracuseStep 7214633 = 5410975) B5410975
theorem B4216475 : Blo 1665032 4216475 := bstep (se 1 (by rfl) ⟨3162356, by rfl⟩ : syracuseStep 4216475 = 6324713) B6324713
theorem B14063489 : Blo 1665032 14063489 := bstep (se 2 (by rfl) ⟨5273808, by rfl⟩ : syracuseStep 14063489 = 10547617) B10547617
theorem B8001449 : Blo 1665032 8001449 := bstep (se 2 (by rfl) ⟨3000543, by rfl⟩ : syracuseStep 8001449 = 6001087) B6001087
theorem B4216799 : Blo 1665032 4216799 := bstep (se 1 (by rfl) ⟨3162599, by rfl⟩ : syracuseStep 4216799 = 6325199) B6325199
theorem B4503865 : Blo 1665032 4503865 := bstep (se 2 (by rfl) ⟨1688949, by rfl⟩ : syracuseStep 4503865 = 3377899) B3377899
theorem B4741679 : Blo 1665032 4741679 := bstep (se 1 (by rfl) ⟨3556259, by rfl⟩ : syracuseStep 4741679 = 7112519) B7112519
theorem B1874623 : Blo 1665032 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B4217579 : Blo 1665032 4217579 := bstep (se 1 (by rfl) ⟨3163184, by rfl⟩ : syracuseStep 4217579 = 6326369) B6326369
theorem B10132577 : Blo 1665032 10132577 := bstep (se 2 (by rfl) ⟨3799716, by rfl⟩ : syracuseStep 10132577 = 7599433) B7599433
theorem B2497883 : Blo 1665032 2497883 := bstep (se 1 (by rfl) ⟨1873412, by rfl⟩ : syracuseStep 2497883 = 3746825) B3746825
theorem B9002411 : Blo 1665032 9002411 := bstep (se 1 (by rfl) ⟨6751808, by rfl⟩ : syracuseStep 9002411 = 13503617) B13503617
theorem B2055871 : Blo 1665032 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B2809903 : Blo 1665032 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B2498663 : Blo 1665032 2498663 := bstep (se 1 (by rfl) ⟨1873997, by rfl⟩ : syracuseStep 2498663 = 3747995) B3747995
theorem B8429831 : Blo 1665032 8429831 := bstep (se 1 (by rfl) ⟨6322373, by rfl⟩ : syracuseStep 8429831 = 12644747) B12644747
theorem B6005153 : Blo 1665032 6005153 := bstep (se 2 (by rfl) ⟨2251932, by rfl⟩ : syracuseStep 6005153 = 4503865) B4503865
theorem B2810281 : Blo 1665032 2810281 := bstep (se 2 (by rfl) ⟨1053855, by rfl⟩ : syracuseStep 2810281 = 2107711) B2107711
theorem B2810423 : Blo 1665032 2810423 := bstep (se 1 (by rfl) ⟨2107817, by rfl⟩ : syracuseStep 2810423 = 4215635) B4215635
theorem B2499497 : Blo 1665032 2499497 := bstep (se 2 (by rfl) ⟨937311, by rfl⟩ : syracuseStep 2499497 = 1874623) B1874623
theorem B2499551 : Blo 1665032 2499551 := bstep (se 1 (by rfl) ⟨1874663, by rfl⟩ : syracuseStep 2499551 = 3749327) B3749327
theorem B4809755 : Blo 1665032 4809755 := bstep (se 1 (by rfl) ⟨3607316, by rfl⟩ : syracuseStep 4809755 = 7214633) B7214633
theorem B2810983 : Blo 1665032 2810983 := bstep (se 1 (by rfl) ⟨2108237, by rfl⟩ : syracuseStep 2810983 = 4216475) B4216475
theorem B5334299 : Blo 1665032 5334299 := bstep (se 1 (by rfl) ⟨4000724, by rfl⟩ : syracuseStep 5334299 = 8001449) B8001449
theorem B2811199 : Blo 1665032 2811199 := bstep (se 1 (by rfl) ⟨2108399, by rfl⟩ : syracuseStep 2811199 = 4216799) B4216799
theorem B18974411 : Blo 1665032 18974411 := bstep (se 1 (by rfl) ⟨14230808, by rfl⟩ : syracuseStep 18974411 = 28461617) B28461617
theorem B2811719 : Blo 1665032 2811719 := bstep (se 1 (by rfl) ⟨2108789, by rfl⟩ : syracuseStep 2811719 = 4217579) B4217579
theorem B6326171 : Blo 1665032 6326171 := bstep (se 1 (by rfl) ⟨4744628, by rfl⟩ : syracuseStep 6326171 = 9489257) B9489257
theorem B2811881 : Blo 1665032 2811881 := bstep (se 2 (by rfl) ⟨1054455, by rfl⟩ : syracuseStep 2811881 = 2108911) B2108911
theorem B5621831 : Blo 1665032 5621831 := bstep (se 1 (by rfl) ⟨4216373, by rfl⟩ : syracuseStep 5621831 = 8432747) B8432747
theorem B7112843 : Blo 1665032 7112843 := bstep (se 1 (by rfl) ⟨5334632, by rfl⟩ : syracuseStep 7112843 = 10669265) B10669265
theorem B1665255 : Blo 1665032 1665255 := bstep (se 1 (by rfl) ⟨1248941, by rfl⟩ : syracuseStep 1665255 = 2497883) B2497883
theorem B26003875 : Blo 1665032 26003875 := bstep (se 1 (by rfl) ⟨19502906, by rfl⟩ : syracuseStep 26003875 = 39005813) B39005813
theorem B1665919 : Blo 1665032 1665919 := bstep (se 1 (by rfl) ⟨1249439, by rfl⟩ : syracuseStep 1665919 = 2498879) B2498879
theorem B5622695 : Blo 1665032 5622695 := bstep (se 1 (by rfl) ⟨4217021, by rfl⟩ : syracuseStep 5622695 = 8434043) B8434043
theorem B12651551 : Blo 1665032 12651551 := bstep (se 1 (by rfl) ⟨9488663, by rfl⟩ : syracuseStep 12651551 = 18977327) B18977327
theorem B2002015 : Blo 1665032 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B4500839 : Blo 1665032 4500839 := bstep (se 1 (by rfl) ⟨3375629, by rfl⟩ : syracuseStep 4500839 = 6751259) B6751259
theorem B10964645 : Blo 1665032 10964645 := bstep (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) B2055871
theorem B9375659 : Blo 1665032 9375659 := bstep (se 1 (by rfl) ⟨7031744, by rfl⟩ : syracuseStep 9375659 = 14063489) B14063489
theorem B3747815 : Blo 1665032 3747815 := bstep (se 1 (by rfl) ⟨2810861, by rfl⟩ : syracuseStep 3747815 = 5621723) B5621723
theorem B27005669 : Blo 1665032 27005669 := bstep (se 4 (by rfl) ⟨2531781, by rfl⟩ : syracuseStep 27005669 = 5063563) B5063563
theorem B6755051 : Blo 1665032 6755051 := bstep (se 1 (by rfl) ⟨5066288, by rfl⟩ : syracuseStep 6755051 = 10132577) B10132577
theorem B14234363 : Blo 1665032 14234363 := bstep (se 1 (by rfl) ⟨10675772, by rfl⟩ : syracuseStep 14234363 = 21351545) B21351545
theorem B3748679 : Blo 1665032 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B6001607 : Blo 1665032 6001607 := bstep (se 1 (by rfl) ⟨4501205, by rfl⟩ : syracuseStep 6001607 = 9002411) B9002411
theorem B9484199 : Blo 1665032 9484199 := bstep (se 1 (by rfl) ⟨7113149, by rfl⟩ : syracuseStep 9484199 = 14226299) B14226299
theorem B2668457 : Blo 1665032 2668457 := bstep (se 2 (by rfl) ⟨1000671, by rfl⟩ : syracuseStep 2668457 = 2001343) B2001343
theorem B16013351 : Blo 1665032 16013351 := bstep (se 1 (by rfl) ⟨12010013, by rfl⟩ : syracuseStep 16013351 = 24020027) B24020027
theorem B1874011 : Blo 1665032 1874011 := bstep (se 1 (by rfl) ⟨1405508, by rfl⟩ : syracuseStep 1874011 = 2811017) B2811017
theorem B3799315 : Blo 1665032 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B3161119 : Blo 1665032 3161119 := bstep (se 1 (by rfl) ⟨2370839, by rfl⟩ : syracuseStep 3161119 = 4741679) B4741679
theorem B2497919 : Blo 1665032 2497919 := bstep (se 1 (by rfl) ⟨1873439, by rfl⟩ : syracuseStep 2497919 = 3746879) B3746879
theorem B24337925 : Blo 1665032 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B11394715 : Blo 1665032 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B4743137 : Blo 1665032 4743137 := bstep (se 2 (by rfl) ⟨1778676, by rfl⟩ : syracuseStep 4743137 = 3557353) B3557353
theorem B2498681 : Blo 1665032 2498681 := bstep (se 2 (by rfl) ⟨937005, by rfl⟩ : syracuseStep 2498681 = 1874011) B1874011
theorem B5619887 : Blo 1665032 5619887 := bstep (se 1 (by rfl) ⟨4214915, by rfl⟩ : syracuseStep 5619887 = 8429831) B8429831
theorem B2499119 : Blo 1665032 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B3556199 : Blo 1665032 3556199 := bstep (se 1 (by rfl) ⟨2667149, by rfl⟩ : syracuseStep 3556199 = 5334299) B5334299
theorem B12649607 : Blo 1665032 12649607 := bstep (se 1 (by rfl) ⟨9487205, by rfl⟩ : syracuseStep 12649607 = 18974411) B18974411
theorem B1778971 : Blo 1665032 1778971 := bstep (se 1 (by rfl) ⟨1334228, by rfl⟩ : syracuseStep 1778971 = 2668457) B2668457
theorem B10675567 : Blo 1665032 10675567 := bstep (se 1 (by rfl) ⟨8006675, by rfl⟩ : syracuseStep 10675567 = 16013351) B16013351
theorem B3000559 : Blo 1665032 3000559 := bstep (se 1 (by rfl) ⟨2250419, by rfl⟩ : syracuseStep 3000559 = 4500839) B4500839
theorem B1665279 : Blo 1665032 1665279 := bstep (se 1 (by rfl) ⟨1248959, by rfl⟩ : syracuseStep 1665279 = 2497919) B2497919
theorem B7309763 : Blo 1665032 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B3746537 : Blo 1665032 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B1665775 : Blo 1665032 1665775 := bstep (se 1 (by rfl) ⟨1249331, by rfl⟩ : syracuseStep 1665775 = 2498663) B2498663
theorem B5065753 : Blo 1665032 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B10677413 : Blo 1665032 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B9489575 : Blo 1665032 9489575 := bstep (se 1 (by rfl) ⟨7117181, by rfl⟩ : syracuseStep 9489575 = 14234363) B14234363
theorem B34671833 : Blo 1665032 34671833 := bstep (se 2 (by rfl) ⟨13001937, by rfl⟩ : syracuseStep 34671833 = 26003875) B26003875
theorem B3747041 : Blo 1665032 3747041 := bstep (se 2 (by rfl) ⟨1405140, by rfl⟩ : syracuseStep 3747041 = 2810281) B2810281
theorem B1666331 : Blo 1665032 1666331 := bstep (se 1 (by rfl) ⟨1249748, by rfl⟩ : syracuseStep 1666331 = 2499497) B2499497
theorem B4001071 : Blo 1665032 4001071 := bstep (se 1 (by rfl) ⟨3000803, by rfl⟩ : syracuseStep 4001071 = 6001607) B6001607
theorem B1666367 : Blo 1665032 1666367 := bstep (se 1 (by rfl) ⟨1249775, by rfl⟩ : syracuseStep 1666367 = 2499551) B2499551
theorem B3206503 : Blo 1665032 3206503 := bstep (se 1 (by rfl) ⟨2404877, by rfl⟩ : syracuseStep 3206503 = 4809755) B4809755
theorem B4214825 : Blo 1665032 4214825 := bstep (se 2 (by rfl) ⟨1580559, by rfl⟩ : syracuseStep 4214825 = 3161119) B3161119
theorem B3747887 : Blo 1665032 3747887 := bstep (se 1 (by rfl) ⟨2810915, by rfl⟩ : syracuseStep 3747887 = 5621831) B5621831
theorem B3747977 : Blo 1665032 3747977 := bstep (se 2 (by rfl) ⟨1405491, by rfl⟩ : syracuseStep 3747977 = 2810983) B2810983
theorem B3748265 : Blo 1665032 3748265 := bstep (se 2 (by rfl) ⟨1405599, by rfl⟩ : syracuseStep 3748265 = 2811199) B2811199
theorem B3748463 : Blo 1665032 3748463 := bstep (se 1 (by rfl) ⟨2811347, by rfl⟩ : syracuseStep 3748463 = 5622695) B5622695
theorem B8434367 : Blo 1665032 8434367 := bstep (se 1 (by rfl) ⟨6325775, by rfl⟩ : syracuseStep 8434367 = 12651551) B12651551
theorem B15192953 : Blo 1665032 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B16225283 : Blo 1665032 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B4003435 : Blo 1665032 4003435 := bstep (se 1 (by rfl) ⟨3002576, by rfl⟩ : syracuseStep 4003435 = 6005153) B6005153
theorem B1873615 : Blo 1665032 1873615 := bstep (se 1 (by rfl) ⟨1405211, by rfl⟩ : syracuseStep 1873615 = 2810423) B2810423
theorem B18003779 : Blo 1665032 18003779 := bstep (se 1 (by rfl) ⟨13502834, by rfl⟩ : syracuseStep 18003779 = 27005669) B27005669
theorem B4503367 : Blo 1665032 4503367 := bstep (se 1 (by rfl) ⟨3377525, by rfl⟩ : syracuseStep 4503367 = 6755051) B6755051
theorem B1874479 : Blo 1665032 1874479 := bstep (se 1 (by rfl) ⟨1405859, by rfl⟩ : syracuseStep 1874479 = 2811719) B2811719
theorem B4217447 : Blo 1665032 4217447 := bstep (se 1 (by rfl) ⟨3163085, by rfl⟩ : syracuseStep 4217447 = 6326171) B6326171
theorem B6322799 : Blo 1665032 6322799 := bstep (se 1 (by rfl) ⟨4742099, by rfl⟩ : syracuseStep 6322799 = 9484199) B9484199
theorem B1874587 : Blo 1665032 1874587 := bstep (se 1 (by rfl) ⟨1405940, by rfl⟩ : syracuseStep 1874587 = 2811881) B2811881
theorem B4741895 : Blo 1665032 4741895 := bstep (se 1 (by rfl) ⟨3556421, by rfl⟩ : syracuseStep 4741895 = 7112843) B7112843
theorem B6250439 : Blo 1665032 6250439 := bstep (se 1 (by rfl) ⟨4687829, by rfl⟩ : syracuseStep 6250439 = 9375659) B9375659
theorem B3162091 : Blo 1665032 3162091 := bstep (se 1 (by rfl) ⟨2371568, by rfl⟩ : syracuseStep 3162091 = 4743137) B4743137
theorem B2498543 : Blo 1665032 2498543 := bstep (se 1 (by rfl) ⟨1873907, by rfl⟩ : syracuseStep 2498543 = 3747815) B3747815
theorem B2809883 : Blo 1665032 2809883 := bstep (se 1 (by rfl) ⟨2107412, by rfl⟩ : syracuseStep 2809883 = 4214825) B4214825
theorem B2498591 : Blo 1665032 2498591 := bstep (se 1 (by rfl) ⟨1873943, by rfl⟩ : syracuseStep 2498591 = 3747887) B3747887
theorem B2498651 : Blo 1665032 2498651 := bstep (se 1 (by rfl) ⟨1873988, by rfl⟩ : syracuseStep 2498651 = 3747977) B3747977
theorem B2498843 : Blo 1665032 2498843 := bstep (se 1 (by rfl) ⟨1874132, by rfl⟩ : syracuseStep 2498843 = 3748265) B3748265
theorem B2498975 : Blo 1665032 2498975 := bstep (se 1 (by rfl) ⟨1874231, by rfl⟩ : syracuseStep 2498975 = 3748463) B3748463
theorem B2499305 : Blo 1665032 2499305 := bstep (se 2 (by rfl) ⟨937239, by rfl⟩ : syracuseStep 2499305 = 1874479) B1874479
theorem B2499449 : Blo 1665032 2499449 := bstep (se 2 (by rfl) ⟨937293, by rfl⟩ : syracuseStep 2499449 = 1874587) B1874587
theorem B12002519 : Blo 1665032 12002519 := bstep (se 1 (by rfl) ⟨9001889, by rfl⟩ : syracuseStep 12002519 = 18003779) B18003779
theorem B5334761 : Blo 1665032 5334761 := bstep (se 2 (by rfl) ⟨2000535, by rfl⟩ : syracuseStep 5334761 = 4001071) B4001071
theorem B2811631 : Blo 1665032 2811631 := bstep (se 1 (by rfl) ⟨2108723, by rfl⟩ : syracuseStep 2811631 = 4217447) B4217447
theorem B6326383 : Blo 1665032 6326383 := bstep (se 1 (by rfl) ⟨4744787, by rfl⟩ : syracuseStep 6326383 = 9489575) B9489575
theorem B1665695 : Blo 1665032 1665695 := bstep (se 1 (by rfl) ⟨1249271, by rfl⟩ : syracuseStep 1665695 = 2498543) B2498543
theorem B1665787 : Blo 1665032 1665787 := bstep (se 1 (by rfl) ⟨1249340, by rfl⟩ : syracuseStep 1665787 = 2498681) B2498681
theorem B3746591 : Blo 1665032 3746591 := bstep (se 1 (by rfl) ⟨2809943, by rfl⟩ : syracuseStep 3746591 = 5619887) B5619887
theorem B4000745 : Blo 1665032 4000745 := bstep (se 2 (by rfl) ⟨1500279, by rfl⟩ : syracuseStep 4000745 = 3000559) B3000559
theorem B1666079 : Blo 1665032 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B5622911 : Blo 1665032 5622911 := bstep (se 1 (by rfl) ⟨4217183, by rfl⟩ : syracuseStep 5622911 = 8434367) B8434367
theorem B2370799 : Blo 1665032 2370799 := bstep (se 1 (by rfl) ⟨1778099, by rfl⟩ : syracuseStep 2370799 = 3556199) B3556199
theorem B10128635 : Blo 1665032 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B8433071 : Blo 1665032 8433071 := bstep (se 1 (by rfl) ⟨6324803, by rfl⟩ : syracuseStep 8433071 = 12649607) B12649607
theorem B6754337 : Blo 1665032 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B2371961 : Blo 1665032 2371961 := bstep (se 2 (by rfl) ⟨889485, by rfl⟩ : syracuseStep 2371961 = 1778971) B1778971
theorem B4215199 : Blo 1665032 4215199 := bstep (se 1 (by rfl) ⟨3161399, by rfl⟩ : syracuseStep 4215199 = 6322799) B6322799
theorem B14234089 : Blo 1665032 14234089 := bstep (se 2 (by rfl) ⟨5337783, by rfl⟩ : syracuseStep 14234089 = 10675567) B10675567
theorem B5337913 : Blo 1665032 5337913 := bstep (se 2 (by rfl) ⟨2001717, by rfl⟩ : syracuseStep 5337913 = 4003435) B4003435
theorem B23114555 : Blo 1665032 23114555 := bstep (se 1 (by rfl) ⟨17335916, by rfl⟩ : syracuseStep 23114555 = 34671833) B34671833
theorem B4166959 : Blo 1665032 4166959 := bstep (se 1 (by rfl) ⟨3125219, by rfl⟩ : syracuseStep 4166959 = 6250439) B6250439
theorem B4216121 : Blo 1665032 4216121 := bstep (se 2 (by rfl) ⟨1581045, by rfl⟩ : syracuseStep 4216121 = 3162091) B3162091
theorem B43267421 : Blo 1665032 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B4873175 : Blo 1665032 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B4275337 : Blo 1665032 4275337 := bstep (se 2 (by rfl) ⟨1603251, by rfl⟩ : syracuseStep 4275337 = 3206503) B3206503
theorem B2497691 : Blo 1665032 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B3161263 : Blo 1665032 3161263 := bstep (se 1 (by rfl) ⟨2370947, by rfl⟩ : syracuseStep 3161263 = 4741895) B4741895
theorem B7118275 : Blo 1665032 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B2498027 : Blo 1665032 2498027 := bstep (se 1 (by rfl) ⟨1873520, by rfl⟩ : syracuseStep 2498027 = 3747041) B3747041
theorem B2498153 : Blo 1665032 2498153 := bstep (se 2 (by rfl) ⟨936807, by rfl⟩ : syracuseStep 2498153 = 1873615) B1873615
theorem B6004489 : Blo 1665032 6004489 := bstep (se 2 (by rfl) ⟨2251683, by rfl⟩ : syracuseStep 6004489 = 4503367) B4503367
theorem B15409703 : Blo 1665032 15409703 := bstep (se 1 (by rfl) ⟨11557277, by rfl⟩ : syracuseStep 15409703 = 23114555) B23114555
theorem B5620265 : Blo 1665032 5620265 := bstep (se 2 (by rfl) ⟨2107599, by rfl⟩ : syracuseStep 5620265 = 4215199) B4215199
theorem B2810747 : Blo 1665032 2810747 := bstep (se 1 (by rfl) ⟨2108060, by rfl⟩ : syracuseStep 2810747 = 4216121) B4216121
theorem B28844947 : Blo 1665032 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B6325229 : Blo 1665032 6325229 := bstep (se 3 (by rfl) ⟨1185980, by rfl⟩ : syracuseStep 6325229 = 2371961) B2371961
theorem B3556507 : Blo 1665032 3556507 := bstep (se 1 (by rfl) ⟨2667380, by rfl⟩ : syracuseStep 3556507 = 5334761) B5334761
theorem B5555945 : Blo 1665032 5555945 := bstep (se 2 (by rfl) ⟨2083479, by rfl⟩ : syracuseStep 5555945 = 4166959) B4166959
theorem B1665127 : Blo 1665032 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B6752423 : Blo 1665032 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B5622047 : Blo 1665032 5622047 := bstep (se 1 (by rfl) ⟨4216535, by rfl⟩ : syracuseStep 5622047 = 8433071) B8433071
theorem B1665351 : Blo 1665032 1665351 := bstep (se 1 (by rfl) ⟨1249013, by rfl⟩ : syracuseStep 1665351 = 2498027) B2498027
theorem B8005985 : Blo 1665032 8005985 := bstep (se 2 (by rfl) ⟨3002244, by rfl⟩ : syracuseStep 8005985 = 6004489) B6004489
theorem B1665435 : Blo 1665032 1665435 := bstep (se 1 (by rfl) ⟨1249076, by rfl⟩ : syracuseStep 1665435 = 2498153) B2498153
theorem B1665727 : Blo 1665032 1665727 := bstep (se 1 (by rfl) ⟨1249295, by rfl⟩ : syracuseStep 1665727 = 2498591) B2498591
theorem B1665767 : Blo 1665032 1665767 := bstep (se 1 (by rfl) ⟨1249325, by rfl⟩ : syracuseStep 1665767 = 2498651) B2498651
theorem B1665895 : Blo 1665032 1665895 := bstep (se 1 (by rfl) ⟨1249421, by rfl⟩ : syracuseStep 1665895 = 2498843) B2498843
theorem B1665983 : Blo 1665032 1665983 := bstep (se 1 (by rfl) ⟨1249487, by rfl⟩ : syracuseStep 1665983 = 2498975) B2498975
theorem B1666203 : Blo 1665032 1666203 := bstep (se 1 (by rfl) ⟨1249652, by rfl⟩ : syracuseStep 1666203 = 2499305) B2499305
theorem B1666299 : Blo 1665032 1666299 := bstep (se 1 (by rfl) ⟨1249724, by rfl⟩ : syracuseStep 1666299 = 2499449) B2499449
theorem B12644261 : Blo 1665032 12644261 := bstep (se 4 (by rfl) ⟨1185399, by rfl⟩ : syracuseStep 12644261 = 2370799) B2370799
theorem B4215017 : Blo 1665032 4215017 := bstep (se 2 (by rfl) ⟨1580631, by rfl⟩ : syracuseStep 4215017 = 3161263) B3161263
theorem B9491033 : Blo 1665032 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B3248783 : Blo 1665032 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B2667163 : Blo 1665032 2667163 := bstep (se 1 (by rfl) ⟨2000372, by rfl⟩ : syracuseStep 2667163 = 4000745) B4000745
theorem B3748607 : Blo 1665032 3748607 := bstep (se 1 (by rfl) ⟨2811455, by rfl⟩ : syracuseStep 3748607 = 5622911) B5622911
theorem B3748841 : Blo 1665032 3748841 := bstep (se 2 (by rfl) ⟨1405815, by rfl⟩ : syracuseStep 3748841 = 2811631) B2811631
theorem B1873255 : Blo 1665032 1873255 := bstep (se 1 (by rfl) ⟨1404941, by rfl⟩ : syracuseStep 1873255 = 2809883) B2809883
theorem B4502891 : Blo 1665032 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B8435177 : Blo 1665032 8435177 := bstep (se 2 (by rfl) ⟨3163191, by rfl⟩ : syracuseStep 8435177 = 6326383) B6326383
theorem B18978785 : Blo 1665032 18978785 := bstep (se 2 (by rfl) ⟨7117044, by rfl⟩ : syracuseStep 18978785 = 14234089) B14234089
theorem B8001679 : Blo 1665032 8001679 := bstep (se 1 (by rfl) ⟨6001259, by rfl⟩ : syracuseStep 8001679 = 12002519) B12002519
theorem B7117217 : Blo 1665032 7117217 := bstep (se 2 (by rfl) ⟨2668956, by rfl⟩ : syracuseStep 7117217 = 5337913) B5337913
theorem B5700449 : Blo 1665032 5700449 := bstep (se 2 (by rfl) ⟨2137668, by rfl⟩ : syracuseStep 5700449 = 4275337) B4275337
theorem B2497727 : Blo 1665032 2497727 := bstep (se 1 (by rfl) ⟨1873295, by rfl⟩ : syracuseStep 2497727 = 3746591) B3746591
theorem B2810011 : Blo 1665032 2810011 := bstep (se 1 (by rfl) ⟨2107508, by rfl⟩ : syracuseStep 2810011 = 4215017) B4215017
theorem B18006461 : Blo 1665032 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B2499071 : Blo 1665032 2499071 := bstep (se 1 (by rfl) ⟨1874303, by rfl⟩ : syracuseStep 2499071 = 3748607) B3748607
theorem B2499227 : Blo 1665032 2499227 := bstep (se 1 (by rfl) ⟨1874420, by rfl⟩ : syracuseStep 2499227 = 3748841) B3748841
theorem B3556217 : Blo 1665032 3556217 := bstep (se 2 (by rfl) ⟨1333581, by rfl⟩ : syracuseStep 3556217 = 2667163) B2667163
theorem B3703963 : Blo 1665032 3703963 := bstep (se 1 (by rfl) ⟨2777972, by rfl⟩ : syracuseStep 3703963 = 5555945) B5555945
theorem B41092541 : Blo 1665032 41092541 := bstep (se 3 (by rfl) ⟨7704851, by rfl⟩ : syracuseStep 41092541 = 15409703) B15409703
theorem B4744811 : Blo 1665032 4744811 := bstep (se 1 (by rfl) ⟨3558608, by rfl⟩ : syracuseStep 4744811 = 7117217) B7117217
theorem B1665151 : Blo 1665032 1665151 := bstep (se 1 (by rfl) ⟨1248863, by rfl⟩ : syracuseStep 1665151 = 2497727) B2497727
theorem B10668905 : Blo 1665032 10668905 := bstep (se 2 (by rfl) ⟨4000839, by rfl⟩ : syracuseStep 10668905 = 8001679) B8001679
theorem B3746843 : Blo 1665032 3746843 := bstep (se 1 (by rfl) ⟨2810132, by rfl⟩ : syracuseStep 3746843 = 5620265) B5620265
theorem B6327355 : Blo 1665032 6327355 := bstep (se 1 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 6327355 = 9491033) B9491033
theorem B2165855 : Blo 1665032 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B5623451 : Blo 1665032 5623451 := bstep (se 1 (by rfl) ⟨4217588, by rfl⟩ : syracuseStep 5623451 = 8435177) B8435177
theorem B12652523 : Blo 1665032 12652523 := bstep (se 1 (by rfl) ⟨9489392, by rfl⟩ : syracuseStep 12652523 = 18978785) B18978785
theorem B3748031 : Blo 1665032 3748031 := bstep (se 1 (by rfl) ⟨2811023, by rfl⟩ : syracuseStep 3748031 = 5622047) B5622047
theorem B5337323 : Blo 1665032 5337323 := bstep (se 1 (by rfl) ⟨4002992, by rfl⟩ : syracuseStep 5337323 = 8005985) B8005985
theorem B15201197 : Blo 1665032 15201197 := bstep (se 3 (by rfl) ⟨2850224, by rfl⟩ : syracuseStep 15201197 = 5700449) B5700449
theorem B1873831 : Blo 1665032 1873831 := bstep (se 1 (by rfl) ⟨1405373, by rfl⟩ : syracuseStep 1873831 = 2810747) B2810747
theorem B4216819 : Blo 1665032 4216819 := bstep (se 1 (by rfl) ⟨3162614, by rfl⟩ : syracuseStep 4216819 = 6325229) B6325229
theorem B12007709 : Blo 1665032 12007709 := bstep (se 3 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 12007709 = 4502891) B4502891
theorem B38459929 : Blo 1665032 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B4742009 : Blo 1665032 4742009 := bstep (se 2 (by rfl) ⟨1778253, by rfl⟩ : syracuseStep 4742009 = 3556507) B3556507
theorem B2497673 : Blo 1665032 2497673 := bstep (se 2 (by rfl) ⟨936627, by rfl⟩ : syracuseStep 2497673 = 1873255) B1873255
theorem B8429507 : Blo 1665032 8429507 := bstep (se 1 (by rfl) ⟨6322130, by rfl⟩ : syracuseStep 8429507 = 12644261) B12644261
theorem B2498687 : Blo 1665032 2498687 := bstep (se 1 (by rfl) ⟨1874015, by rfl⟩ : syracuseStep 2498687 = 3748031) B3748031
theorem B10134131 : Blo 1665032 10134131 := bstep (se 1 (by rfl) ⟨7600598, by rfl⟩ : syracuseStep 10134131 = 15201197) B15201197
theorem B27395027 : Blo 1665032 27395027 := bstep (se 1 (by rfl) ⟨20546270, by rfl⟩ : syracuseStep 27395027 = 41092541) B41092541
theorem B23102453 : Blo 1665032 23102453 := bstep (se 5 (by rfl) ⟨1082927, by rfl⟩ : syracuseStep 23102453 = 2165855) B2165855
theorem B3163207 : Blo 1665032 3163207 := bstep (se 1 (by rfl) ⟨2372405, by rfl⟩ : syracuseStep 3163207 = 4744811) B4744811
theorem B8005139 : Blo 1665032 8005139 := bstep (se 1 (by rfl) ⟨6003854, by rfl⟩ : syracuseStep 8005139 = 12007709) B12007709
theorem B7112603 : Blo 1665032 7112603 := bstep (se 1 (by rfl) ⟨5334452, by rfl⟩ : syracuseStep 7112603 = 10668905) B10668905
theorem B1665115 : Blo 1665032 1665115 := bstep (se 1 (by rfl) ⟨1248836, by rfl⟩ : syracuseStep 1665115 = 2497673) B2497673
theorem B5622425 : Blo 1665032 5622425 := bstep (se 2 (by rfl) ⟨2108409, by rfl⟩ : syracuseStep 5622425 = 4216819) B4216819
theorem B3558215 : Blo 1665032 3558215 := bstep (se 1 (by rfl) ⟨2668661, by rfl⟩ : syracuseStep 3558215 = 5337323) B5337323
theorem B3746681 : Blo 1665032 3746681 := bstep (se 2 (by rfl) ⟨1405005, by rfl⟩ : syracuseStep 3746681 = 2810011) B2810011
theorem B12004307 : Blo 1665032 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B1666047 : Blo 1665032 1666047 := bstep (se 1 (by rfl) ⟨1249535, by rfl⟩ : syracuseStep 1666047 = 2499071) B2499071
theorem B1666151 : Blo 1665032 1666151 := bstep (se 1 (by rfl) ⟨1249613, by rfl⟩ : syracuseStep 1666151 = 2499227) B2499227
theorem B2370811 : Blo 1665032 2370811 := bstep (se 1 (by rfl) ⟨1778108, by rfl⟩ : syracuseStep 2370811 = 3556217) B3556217
theorem B3748967 : Blo 1665032 3748967 := bstep (se 1 (by rfl) ⟨2811725, by rfl⟩ : syracuseStep 3748967 = 5623451) B5623451
theorem B8435015 : Blo 1665032 8435015 := bstep (se 1 (by rfl) ⟨6326261, by rfl⟩ : syracuseStep 8435015 = 12652523) B12652523
theorem B51279905 : Blo 1665032 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B8436473 : Blo 1665032 8436473 := bstep (se 2 (by rfl) ⟨3163677, by rfl⟩ : syracuseStep 8436473 = 6327355) B6327355
theorem B4938617 : Blo 1665032 4938617 := bstep (se 2 (by rfl) ⟨1851981, by rfl⟩ : syracuseStep 4938617 = 3703963) B3703963
theorem B3161339 : Blo 1665032 3161339 := bstep (se 1 (by rfl) ⟨2371004, by rfl⟩ : syracuseStep 3161339 = 4742009) B4742009
theorem B2497895 : Blo 1665032 2497895 := bstep (se 1 (by rfl) ⟨1873421, by rfl⟩ : syracuseStep 2497895 = 3746843) B3746843
theorem B2498441 : Blo 1665032 2498441 := bstep (se 2 (by rfl) ⟨936915, by rfl⟩ : syracuseStep 2498441 = 1873831) B1873831
theorem B5619671 : Blo 1665032 5619671 := bstep (se 1 (by rfl) ⟨4214753, by rfl⟩ : syracuseStep 5619671 = 8429507) B8429507
theorem B2499311 : Blo 1665032 2499311 := bstep (se 1 (by rfl) ⟨1874483, by rfl⟩ : syracuseStep 2499311 = 3748967) B3748967
theorem B2107559 : Blo 1665032 2107559 := bstep (se 1 (by rfl) ⟨1580669, by rfl⟩ : syracuseStep 2107559 = 3161339) B3161339
theorem B9488573 : Blo 1665032 9488573 := bstep (se 3 (by rfl) ⟨1779107, by rfl⟩ : syracuseStep 9488573 = 3558215) B3558215
theorem B1665263 : Blo 1665032 1665263 := bstep (se 1 (by rfl) ⟨1248947, by rfl⟩ : syracuseStep 1665263 = 2497895) B2497895
theorem B1665627 : Blo 1665032 1665627 := bstep (se 1 (by rfl) ⟨1249220, by rfl⟩ : syracuseStep 1665627 = 2498441) B2498441
theorem B61606541 : Blo 1665032 61606541 := bstep (se 3 (by rfl) ⟨11551226, by rfl⟩ : syracuseStep 61606541 = 23102453) B23102453
theorem B3746447 : Blo 1665032 3746447 := bstep (se 1 (by rfl) ⟨2809835, by rfl⟩ : syracuseStep 3746447 = 5619671) B5619671
theorem B1665791 : Blo 1665032 1665791 := bstep (se 1 (by rfl) ⟨1249343, by rfl⟩ : syracuseStep 1665791 = 2498687) B2498687
theorem B18263351 : Blo 1665032 18263351 := bstep (se 1 (by rfl) ⟨13697513, by rfl⟩ : syracuseStep 18263351 = 27395027) B27395027
theorem B5623343 : Blo 1665032 5623343 := bstep (se 1 (by rfl) ⟨4217507, by rfl⟩ : syracuseStep 5623343 = 8435015) B8435015
theorem B5336759 : Blo 1665032 5336759 := bstep (se 1 (by rfl) ⟨4002569, by rfl⟩ : syracuseStep 5336759 = 8005139) B8005139
theorem B3748283 : Blo 1665032 3748283 := bstep (se 1 (by rfl) ⟨2811212, by rfl⟩ : syracuseStep 3748283 = 5622425) B5622425
theorem B5624315 : Blo 1665032 5624315 := bstep (se 1 (by rfl) ⟨4218236, by rfl⟩ : syracuseStep 5624315 = 8436473) B8436473
theorem B13169645 : Blo 1665032 13169645 := bstep (se 3 (by rfl) ⟨2469308, by rfl⟩ : syracuseStep 13169645 = 4938617) B4938617
theorem B136746413 : Blo 1665032 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B4741735 : Blo 1665032 4741735 := bstep (se 1 (by rfl) ⟨3556301, by rfl⟩ : syracuseStep 4741735 = 7112603) B7112603
theorem B4217609 : Blo 1665032 4217609 := bstep (se 2 (by rfl) ⟨1581603, by rfl⟩ : syracuseStep 4217609 = 3163207) B3163207
theorem B27024349 : Blo 1665032 27024349 := bstep (se 3 (by rfl) ⟨5067065, by rfl⟩ : syracuseStep 27024349 = 10134131) B10134131
theorem B3161081 : Blo 1665032 3161081 := bstep (se 2 (by rfl) ⟨1185405, by rfl⟩ : syracuseStep 3161081 = 2370811) B2370811
theorem B2497787 : Blo 1665032 2497787 := bstep (se 1 (by rfl) ⟨1873340, by rfl⟩ : syracuseStep 2497787 = 3746681) B3746681
theorem B8002871 : Blo 1665032 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B2498855 : Blo 1665032 2498855 := bstep (se 1 (by rfl) ⟨1874141, by rfl⟩ : syracuseStep 2498855 = 3748283) B3748283
theorem B5620157 : Blo 1665032 5620157 := bstep (se 3 (by rfl) ⟨1053779, by rfl⟩ : syracuseStep 5620157 = 2107559) B2107559
theorem B48702269 : Blo 1665032 48702269 := bstep (se 3 (by rfl) ⟨9131675, by rfl⟩ : syracuseStep 48702269 = 18263351) B18263351
theorem B6325715 : Blo 1665032 6325715 := bstep (se 1 (by rfl) ⟨4744286, by rfl⟩ : syracuseStep 6325715 = 9488573) B9488573
theorem B164284109 : Blo 1665032 164284109 := bstep (se 3 (by rfl) ⟨30803270, by rfl⟩ : syracuseStep 164284109 = 61606541) B61606541
theorem B2811739 : Blo 1665032 2811739 := bstep (se 1 (by rfl) ⟨2108804, by rfl⟩ : syracuseStep 2811739 = 4217609) B4217609
theorem B2107387 : Blo 1665032 2107387 := bstep (se 1 (by rfl) ⟨1580540, by rfl⟩ : syracuseStep 2107387 = 3161081) B3161081
theorem B1665191 : Blo 1665032 1665191 := bstep (se 1 (by rfl) ⟨1248893, by rfl⟩ : syracuseStep 1665191 = 2497787) B2497787
theorem B5335247 : Blo 1665032 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B3557839 : Blo 1665032 3557839 := bstep (se 1 (by rfl) ⟨2668379, by rfl⟩ : syracuseStep 3557839 = 5336759) B5336759
theorem B1666207 : Blo 1665032 1666207 := bstep (se 1 (by rfl) ⟨1249655, by rfl⟩ : syracuseStep 1666207 = 2499311) B2499311
theorem B91164275 : Blo 1665032 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B36032465 : Blo 1665032 36032465 := bstep (se 2 (by rfl) ⟨13512174, by rfl⟩ : syracuseStep 36032465 = 27024349) B27024349
theorem B3748895 : Blo 1665032 3748895 := bstep (se 1 (by rfl) ⟨2811671, by rfl⟩ : syracuseStep 3748895 = 5623343) B5623343
theorem B3749543 : Blo 1665032 3749543 := bstep (se 1 (by rfl) ⟨2812157, by rfl⟩ : syracuseStep 3749543 = 5624315) B5624315
theorem B8779763 : Blo 1665032 8779763 := bstep (se 1 (by rfl) ⟨6584822, by rfl⟩ : syracuseStep 8779763 = 13169645) B13169645
theorem B6322313 : Blo 1665032 6322313 := bstep (se 2 (by rfl) ⟨2370867, by rfl⟩ : syracuseStep 6322313 = 4741735) B4741735
theorem B2497631 : Blo 1665032 2497631 := bstep (se 1 (by rfl) ⟨1873223, by rfl⟩ : syracuseStep 2497631 = 3746447) B3746447
theorem B4743785 : Blo 1665032 4743785 := bstep (se 2 (by rfl) ⟨1778919, by rfl⟩ : syracuseStep 4743785 = 3557839) B3557839
theorem B2499263 : Blo 1665032 2499263 := bstep (se 1 (by rfl) ⟨1874447, by rfl⟩ : syracuseStep 2499263 = 3748895) B3748895
theorem B2499695 : Blo 1665032 2499695 := bstep (se 1 (by rfl) ⟨1874771, by rfl⟩ : syracuseStep 2499695 = 3749543) B3749543
theorem B1665087 : Blo 1665032 1665087 := bstep (se 1 (by rfl) ⟨1248815, by rfl⟩ : syracuseStep 1665087 = 2497631) B2497631
theorem B24021643 : Blo 1665032 24021643 := bstep (se 1 (by rfl) ⟨18016232, by rfl⟩ : syracuseStep 24021643 = 36032465) B36032465
theorem B1665903 : Blo 1665032 1665903 := bstep (se 1 (by rfl) ⟨1249427, by rfl⟩ : syracuseStep 1665903 = 2498855) B2498855
theorem B3746771 : Blo 1665032 3746771 := bstep (se 1 (by rfl) ⟨2810078, by rfl⟩ : syracuseStep 3746771 = 5620157) B5620157
theorem B109522739 : Blo 1665032 109522739 := bstep (se 1 (by rfl) ⟨82142054, by rfl⟩ : syracuseStep 109522739 = 164284109) B164284109
theorem B4214875 : Blo 1665032 4214875 := bstep (se 1 (by rfl) ⟨3161156, by rfl⟩ : syracuseStep 4214875 = 6322313) B6322313
theorem B129872717 : Blo 1665032 129872717 := bstep (se 3 (by rfl) ⟨24351134, by rfl⟩ : syracuseStep 129872717 = 48702269) B48702269
theorem B3748985 : Blo 1665032 3748985 := bstep (se 2 (by rfl) ⟨1405869, by rfl⟩ : syracuseStep 3748985 = 2811739) B2811739
theorem B14227325 : Blo 1665032 14227325 := bstep (se 3 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 14227325 = 5335247) B5335247
theorem B4217143 : Blo 1665032 4217143 := bstep (se 1 (by rfl) ⟨3162857, by rfl⟩ : syracuseStep 4217143 = 6325715) B6325715
theorem B60776183 : Blo 1665032 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B23412701 : Blo 1665032 23412701 := bstep (se 3 (by rfl) ⟨4389881, by rfl⟩ : syracuseStep 23412701 = 8779763) B8779763
theorem B2809849 : Blo 1665032 2809849 := bstep (se 2 (by rfl) ⟨1053693, by rfl⟩ : syracuseStep 2809849 = 2107387) B2107387
theorem B5619833 : Blo 1665032 5619833 := bstep (se 2 (by rfl) ⟨2107437, by rfl⟩ : syracuseStep 5619833 = 4214875) B4214875
theorem B86581811 : Blo 1665032 86581811 := bstep (se 1 (by rfl) ⟨64936358, by rfl⟩ : syracuseStep 86581811 = 129872717) B129872717
theorem B2499323 : Blo 1665032 2499323 := bstep (se 1 (by rfl) ⟨1874492, by rfl⟩ : syracuseStep 2499323 = 3748985) B3748985
theorem B12650093 : Blo 1665032 12650093 := bstep (se 3 (by rfl) ⟨2371892, by rfl⟩ : syracuseStep 12650093 = 4743785) B4743785
theorem B15608467 : Blo 1665032 15608467 := bstep (se 1 (by rfl) ⟨11706350, by rfl⟩ : syracuseStep 15608467 = 23412701) B23412701
theorem B3746465 : Blo 1665032 3746465 := bstep (se 2 (by rfl) ⟨1404924, by rfl⟩ : syracuseStep 3746465 = 2809849) B2809849
theorem B5622857 : Blo 1665032 5622857 := bstep (se 2 (by rfl) ⟨2108571, by rfl⟩ : syracuseStep 5622857 = 4217143) B4217143
theorem B1666175 : Blo 1665032 1666175 := bstep (se 1 (by rfl) ⟨1249631, by rfl⟩ : syracuseStep 1666175 = 2499263) B2499263
theorem B1666463 : Blo 1665032 1666463 := bstep (se 1 (by rfl) ⟨1249847, by rfl⟩ : syracuseStep 1666463 = 2499695) B2499695
theorem B32028857 : Blo 1665032 32028857 := bstep (se 2 (by rfl) ⟨12010821, by rfl⟩ : syracuseStep 32028857 = 24021643) B24021643
theorem B9484883 : Blo 1665032 9484883 := bstep (se 1 (by rfl) ⟨7113662, by rfl⟩ : syracuseStep 9484883 = 14227325) B14227325
theorem B2497847 : Blo 1665032 2497847 := bstep (se 1 (by rfl) ⟨1873385, by rfl⟩ : syracuseStep 2497847 = 3746771) B3746771
theorem B292060637 : Blo 1665032 292060637 := bstep (se 3 (by rfl) ⟨54761369, by rfl⟩ : syracuseStep 292060637 = 109522739) B109522739
theorem B40517455 : Blo 1665032 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B57721207 : Blo 1665032 57721207 := bstep (se 1 (by rfl) ⟨43290905, by rfl⟩ : syracuseStep 57721207 = 86581811) B86581811
theorem B1665231 : Blo 1665032 1665231 := bstep (se 1 (by rfl) ⟨1248923, by rfl⟩ : syracuseStep 1665231 = 2497847) B2497847
theorem B3746555 : Blo 1665032 3746555 := bstep (se 1 (by rfl) ⟨2809916, by rfl⟩ : syracuseStep 3746555 = 5619833) B5619833
theorem B1666215 : Blo 1665032 1666215 := bstep (se 1 (by rfl) ⟨1249661, by rfl⟩ : syracuseStep 1666215 = 2499323) B2499323
theorem B20811289 : Blo 1665032 20811289 := bstep (se 2 (by rfl) ⟨7804233, by rfl⟩ : syracuseStep 20811289 = 15608467) B15608467
theorem B8433395 : Blo 1665032 8433395 := bstep (se 1 (by rfl) ⟨6325046, by rfl⟩ : syracuseStep 8433395 = 12650093) B12650093
theorem B21352571 : Blo 1665032 21352571 := bstep (se 1 (by rfl) ⟨16014428, by rfl⟩ : syracuseStep 21352571 = 32028857) B32028857
theorem B3748571 : Blo 1665032 3748571 := bstep (se 1 (by rfl) ⟨2811428, by rfl⟩ : syracuseStep 3748571 = 5622857) B5622857
theorem B54023273 : Blo 1665032 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B6323255 : Blo 1665032 6323255 := bstep (se 1 (by rfl) ⟨4742441, by rfl⟩ : syracuseStep 6323255 = 9484883) B9484883
theorem B2497643 : Blo 1665032 2497643 := bstep (se 1 (by rfl) ⟨1873232, by rfl⟩ : syracuseStep 2497643 = 3746465) B3746465
theorem B194707091 : Blo 1665032 194707091 := bstep (se 1 (by rfl) ⟨146030318, by rfl⟩ : syracuseStep 194707091 = 292060637) B292060637
theorem B2499047 : Blo 1665032 2499047 := bstep (se 1 (by rfl) ⟨1874285, by rfl⟩ : syracuseStep 2499047 = 3748571) B3748571
theorem B27748385 : Blo 1665032 27748385 := bstep (se 2 (by rfl) ⟨10405644, by rfl⟩ : syracuseStep 27748385 = 20811289) B20811289
theorem B1665095 : Blo 1665032 1665095 := bstep (se 1 (by rfl) ⟨1248821, by rfl⟩ : syracuseStep 1665095 = 2497643) B2497643
theorem B129804727 : Blo 1665032 129804727 := bstep (se 1 (by rfl) ⟨97353545, by rfl⟩ : syracuseStep 129804727 = 194707091) B194707091
theorem B5622263 : Blo 1665032 5622263 := bstep (se 1 (by rfl) ⟨4216697, by rfl⟩ : syracuseStep 5622263 = 8433395) B8433395
theorem B36015515 : Blo 1665032 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B4215503 : Blo 1665032 4215503 := bstep (se 1 (by rfl) ⟨3161627, by rfl⟩ : syracuseStep 4215503 = 6323255) B6323255
theorem B14235047 : Blo 1665032 14235047 := bstep (se 1 (by rfl) ⟨10676285, by rfl⟩ : syracuseStep 14235047 = 21352571) B21352571
theorem B76961609 : Blo 1665032 76961609 := bstep (se 2 (by rfl) ⟨28860603, by rfl⟩ : syracuseStep 76961609 = 57721207) B57721207
theorem B2497703 : Blo 1665032 2497703 := bstep (se 1 (by rfl) ⟨1873277, by rfl⟩ : syracuseStep 2497703 = 3746555) B3746555
theorem B2810335 : Blo 1665032 2810335 := bstep (se 1 (by rfl) ⟨2107751, by rfl⟩ : syracuseStep 2810335 = 4215503) B4215503
theorem B173072969 : Blo 1665032 173072969 := bstep (se 2 (by rfl) ⟨64902363, by rfl⟩ : syracuseStep 173072969 = 129804727) B129804727
theorem B51307739 : Blo 1665032 51307739 := bstep (se 1 (by rfl) ⟨38480804, by rfl⟩ : syracuseStep 51307739 = 76961609) B76961609
theorem B18498923 : Blo 1665032 18498923 := bstep (se 1 (by rfl) ⟨13874192, by rfl⟩ : syracuseStep 18498923 = 27748385) B27748385
theorem B1665135 : Blo 1665032 1665135 := bstep (se 1 (by rfl) ⟨1248851, by rfl⟩ : syracuseStep 1665135 = 2497703) B2497703
theorem B1666031 : Blo 1665032 1666031 := bstep (se 1 (by rfl) ⟨1249523, by rfl⟩ : syracuseStep 1666031 = 2499047) B2499047
theorem B9490031 : Blo 1665032 9490031 := bstep (se 1 (by rfl) ⟨7117523, by rfl⟩ : syracuseStep 9490031 = 14235047) B14235047
theorem B3748175 : Blo 1665032 3748175 := bstep (se 1 (by rfl) ⟨2811131, by rfl⟩ : syracuseStep 3748175 = 5622263) B5622263
theorem B24010343 : Blo 1665032 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B2498783 : Blo 1665032 2498783 := bstep (se 1 (by rfl) ⟨1874087, by rfl⟩ : syracuseStep 2498783 = 3748175) B3748175
theorem B197321845 : Blo 1665032 197321845 := bstep (se 5 (by rfl) ⟨9249461, by rfl⟩ : syracuseStep 197321845 = 18498923) B18498923
theorem B6326687 : Blo 1665032 6326687 := bstep (se 1 (by rfl) ⟨4745015, by rfl⟩ : syracuseStep 6326687 = 9490031) B9490031
theorem B3747113 : Blo 1665032 3747113 := bstep (se 2 (by rfl) ⟨1405167, by rfl⟩ : syracuseStep 3747113 = 2810335) B2810335
theorem B34205159 : Blo 1665032 34205159 := bstep (se 1 (by rfl) ⟨25653869, by rfl⟩ : syracuseStep 34205159 = 51307739) B51307739
theorem B115381979 : Blo 1665032 115381979 := bstep (se 1 (by rfl) ⟨86536484, by rfl⟩ : syracuseStep 115381979 = 173072969) B173072969
theorem B16006895 : Blo 1665032 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B263095793 : Blo 1665032 263095793 := bstep (se 2 (by rfl) ⟨98660922, by rfl⟩ : syracuseStep 263095793 = 197321845) B197321845
theorem B1665855 : Blo 1665032 1665855 := bstep (se 1 (by rfl) ⟨1249391, by rfl⟩ : syracuseStep 1665855 = 2498783) B2498783
theorem B22803439 : Blo 1665032 22803439 := bstep (se 1 (by rfl) ⟨17102579, by rfl⟩ : syracuseStep 22803439 = 34205159) B34205159
theorem B10671263 : Blo 1665032 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B76921319 : Blo 1665032 76921319 := bstep (se 1 (by rfl) ⟨57690989, by rfl⟩ : syracuseStep 76921319 = 115381979) B115381979
theorem B4217791 : Blo 1665032 4217791 := bstep (se 1 (by rfl) ⟨3163343, by rfl⟩ : syracuseStep 4217791 = 6326687) B6326687
theorem B2498075 : Blo 1665032 2498075 := bstep (se 1 (by rfl) ⟨1873556, by rfl⟩ : syracuseStep 2498075 = 3747113) B3747113
theorem B1665383 : Blo 1665032 1665383 := bstep (se 1 (by rfl) ⟨1249037, by rfl⟩ : syracuseStep 1665383 = 2498075) B2498075
theorem B7114175 : Blo 1665032 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B5623721 : Blo 1665032 5623721 := bstep (se 2 (by rfl) ⟨2108895, by rfl⟩ : syracuseStep 5623721 = 4217791) B4217791
theorem B30404585 : Blo 1665032 30404585 := bstep (se 2 (by rfl) ⟨11401719, by rfl⟩ : syracuseStep 30404585 = 22803439) B22803439
theorem B175397195 : Blo 1665032 175397195 := bstep (se 1 (by rfl) ⟨131547896, by rfl⟩ : syracuseStep 175397195 = 263095793) B263095793
theorem B51280879 : Blo 1665032 51280879 := bstep (se 1 (by rfl) ⟨38460659, by rfl⟩ : syracuseStep 51280879 = 76921319) B76921319
theorem B81078893 : Blo 1665032 81078893 := bstep (se 3 (by rfl) ⟨15202292, by rfl⟩ : syracuseStep 81078893 = 30404585) B30404585
theorem B467725853 : Blo 1665032 467725853 := bstep (se 3 (by rfl) ⟨87698597, by rfl⟩ : syracuseStep 467725853 = 175397195) B175397195
theorem B68374505 : Blo 1665032 68374505 := bstep (se 2 (by rfl) ⟨25640439, by rfl⟩ : syracuseStep 68374505 = 51280879) B51280879
theorem B3749147 : Blo 1665032 3749147 := bstep (se 1 (by rfl) ⟨2811860, by rfl⟩ : syracuseStep 3749147 = 5623721) B5623721
theorem B4742783 : Blo 1665032 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B2499431 : Blo 1665032 2499431 := bstep (se 1 (by rfl) ⟨1874573, by rfl⟩ : syracuseStep 2499431 = 3749147) B3749147
theorem B54052595 : Blo 1665032 54052595 := bstep (se 1 (by rfl) ⟨40539446, by rfl⟩ : syracuseStep 54052595 = 81078893) B81078893
theorem B45583003 : Blo 1665032 45583003 := bstep (se 1 (by rfl) ⟨34187252, by rfl⟩ : syracuseStep 45583003 = 68374505) B68374505
theorem B1247268941 : Blo 1665032 1247268941 := bstep (se 3 (by rfl) ⟨233862926, by rfl⟩ : syracuseStep 1247268941 = 467725853) B467725853
theorem B3161855 : Blo 1665032 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B831512627 : Blo 1665032 831512627 := bstep (se 1 (by rfl) ⟨623634470, by rfl⟩ : syracuseStep 831512627 = 1247268941) B1247268941
theorem B8431613 : Blo 1665032 8431613 := bstep (se 3 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 8431613 = 3161855) B3161855
theorem B1666287 : Blo 1665032 1666287 := bstep (se 1 (by rfl) ⟨1249715, by rfl⟩ : syracuseStep 1666287 = 2499431) B2499431
theorem B243109349 : Blo 1665032 243109349 := bstep (se 4 (by rfl) ⟨22791501, by rfl⟩ : syracuseStep 243109349 = 45583003) B45583003
theorem B36035063 : Blo 1665032 36035063 := bstep (se 1 (by rfl) ⟨27026297, by rfl⟩ : syracuseStep 36035063 = 54052595) B54052595
theorem B5621075 : Blo 1665032 5621075 := bstep (se 1 (by rfl) ⟨4215806, by rfl⟩ : syracuseStep 5621075 = 8431613) B8431613
theorem B162072899 : Blo 1665032 162072899 := bstep (se 1 (by rfl) ⟨121554674, by rfl⟩ : syracuseStep 162072899 = 243109349) B243109349
theorem B24023375 : Blo 1665032 24023375 := bstep (se 1 (by rfl) ⟨18017531, by rfl⟩ : syracuseStep 24023375 = 36035063) B36035063
theorem B554341751 : Blo 1665032 554341751 := bstep (se 1 (by rfl) ⟨415756313, by rfl⟩ : syracuseStep 554341751 = 831512627) B831512627
theorem B16015583 : Blo 1665032 16015583 := bstep (se 1 (by rfl) ⟨12011687, by rfl⟩ : syracuseStep 16015583 = 24023375) B24023375
theorem B3747383 : Blo 1665032 3747383 := bstep (se 1 (by rfl) ⟨2810537, by rfl⟩ : syracuseStep 3747383 = 5621075) B5621075
theorem B369561167 : Blo 1665032 369561167 := bstep (se 1 (by rfl) ⟨277170875, by rfl⟩ : syracuseStep 369561167 = 554341751) B554341751
theorem B108048599 : Blo 1665032 108048599 := bstep (se 1 (by rfl) ⟨81036449, by rfl⟩ : syracuseStep 108048599 = 162072899) B162072899
theorem B72032399 : Blo 1665032 72032399 := bstep (se 1 (by rfl) ⟨54024299, by rfl⟩ : syracuseStep 72032399 = 108048599) B108048599
theorem B10677055 : Blo 1665032 10677055 := bstep (se 1 (by rfl) ⟨8007791, by rfl⟩ : syracuseStep 10677055 = 16015583) B16015583
theorem B2498255 : Blo 1665032 2498255 := bstep (se 1 (by rfl) ⟨1873691, by rfl⟩ : syracuseStep 2498255 = 3747383) B3747383
theorem B246374111 : Blo 1665032 246374111 := bstep (se 1 (by rfl) ⟨184780583, by rfl⟩ : syracuseStep 246374111 = 369561167) B369561167
theorem B48021599 : Blo 1665032 48021599 := bstep (se 1 (by rfl) ⟨36016199, by rfl⟩ : syracuseStep 48021599 = 72032399) B72032399
theorem B1665503 : Blo 1665032 1665503 := bstep (se 1 (by rfl) ⟨1249127, by rfl⟩ : syracuseStep 1665503 = 2498255) B2498255
theorem B14236073 : Blo 1665032 14236073 := bstep (se 2 (by rfl) ⟨5338527, by rfl⟩ : syracuseStep 14236073 = 10677055) B10677055
theorem B164249407 : Blo 1665032 164249407 := bstep (se 1 (by rfl) ⟨123187055, by rfl⟩ : syracuseStep 164249407 = 246374111) B246374111
theorem B32014399 : Blo 1665032 32014399 := bstep (se 1 (by rfl) ⟨24010799, by rfl⟩ : syracuseStep 32014399 = 48021599) B48021599
theorem B218999209 : Blo 1665032 218999209 := bstep (se 2 (by rfl) ⟨82124703, by rfl⟩ : syracuseStep 218999209 = 164249407) B164249407
theorem B9490715 : Blo 1665032 9490715 := bstep (se 1 (by rfl) ⟨7118036, by rfl⟩ : syracuseStep 9490715 = 14236073) B14236073
theorem B6327143 : Blo 1665032 6327143 := bstep (se 1 (by rfl) ⟨4745357, by rfl⟩ : syracuseStep 6327143 = 9490715) B9490715
theorem B291998945 : Blo 1665032 291998945 := bstep (se 2 (by rfl) ⟨109499604, by rfl⟩ : syracuseStep 291998945 = 218999209) B218999209
theorem B42685865 : Blo 1665032 42685865 := bstep (se 2 (by rfl) ⟨16007199, by rfl⟩ : syracuseStep 42685865 = 32014399) B32014399
theorem B28457243 : Blo 1665032 28457243 := bstep (se 1 (by rfl) ⟨21342932, by rfl⟩ : syracuseStep 28457243 = 42685865) B42685865
theorem B4218095 : Blo 1665032 4218095 := bstep (se 1 (by rfl) ⟨3163571, by rfl⟩ : syracuseStep 4218095 = 6327143) B6327143
theorem B194665963 : Blo 1665032 194665963 := bstep (se 1 (by rfl) ⟨145999472, by rfl⟩ : syracuseStep 194665963 = 291998945) B291998945
theorem B2812063 : Blo 1665032 2812063 := bstep (se 1 (by rfl) ⟨2109047, by rfl⟩ : syracuseStep 2812063 = 4218095) B4218095
theorem B18971495 : Blo 1665032 18971495 := bstep (se 1 (by rfl) ⟨14228621, by rfl⟩ : syracuseStep 18971495 = 28457243) B28457243
theorem B259554617 : Blo 1665032 259554617 := bstep (se 2 (by rfl) ⟨97332981, by rfl⟩ : syracuseStep 259554617 = 194665963) B194665963
theorem B173036411 : Blo 1665032 173036411 := bstep (se 1 (by rfl) ⟨129777308, by rfl⟩ : syracuseStep 173036411 = 259554617) B259554617
theorem B3749417 : Blo 1665032 3749417 := bstep (se 2 (by rfl) ⟨1406031, by rfl⟩ : syracuseStep 3749417 = 2812063) B2812063
theorem B12647663 : Blo 1665032 12647663 := bstep (se 1 (by rfl) ⟨9485747, by rfl⟩ : syracuseStep 12647663 = 18971495) B18971495
theorem B2499611 : Blo 1665032 2499611 := bstep (se 1 (by rfl) ⟨1874708, by rfl⟩ : syracuseStep 2499611 = 3749417) B3749417
theorem B8431775 : Blo 1665032 8431775 := bstep (se 1 (by rfl) ⟨6323831, by rfl⟩ : syracuseStep 8431775 = 12647663) B12647663
theorem B115357607 : Blo 1665032 115357607 := bstep (se 1 (by rfl) ⟨86518205, by rfl⟩ : syracuseStep 115357607 = 173036411) B173036411
theorem B5621183 : Blo 1665032 5621183 := bstep (se 1 (by rfl) ⟨4215887, by rfl⟩ : syracuseStep 5621183 = 8431775) B8431775
theorem B1666407 : Blo 1665032 1666407 := bstep (se 1 (by rfl) ⟨1249805, by rfl⟩ : syracuseStep 1666407 = 2499611) B2499611
theorem B76905071 : Blo 1665032 76905071 := bstep (se 1 (by rfl) ⟨57678803, by rfl⟩ : syracuseStep 76905071 = 115357607) B115357607
theorem B3747455 : Blo 1665032 3747455 := bstep (se 1 (by rfl) ⟨2810591, by rfl⟩ : syracuseStep 3747455 = 5621183) B5621183
theorem B51270047 : Blo 1665032 51270047 := bstep (se 1 (by rfl) ⟨38452535, by rfl⟩ : syracuseStep 51270047 = 76905071) B76905071
theorem B34180031 : Blo 1665032 34180031 := bstep (se 1 (by rfl) ⟨25635023, by rfl⟩ : syracuseStep 34180031 = 51270047) B51270047
theorem B2498303 : Blo 1665032 2498303 := bstep (se 1 (by rfl) ⟨1873727, by rfl⟩ : syracuseStep 2498303 = 3747455) B3747455
theorem B1665535 : Blo 1665032 1665535 := bstep (se 1 (by rfl) ⟨1249151, by rfl⟩ : syracuseStep 1665535 = 2498303) B2498303
theorem B22786687 : Blo 1665032 22786687 := bstep (se 1 (by rfl) ⟨17090015, by rfl⟩ : syracuseStep 22786687 = 34180031) B34180031
theorem B30382249 : Blo 1665032 30382249 := bstep (se 2 (by rfl) ⟨11393343, by rfl⟩ : syracuseStep 30382249 = 22786687) B22786687
theorem B40509665 : Blo 1665032 40509665 := bstep (se 2 (by rfl) ⟨15191124, by rfl⟩ : syracuseStep 40509665 = 30382249) B30382249
theorem B27006443 : Blo 1665032 27006443 := bstep (se 1 (by rfl) ⟨20254832, by rfl⟩ : syracuseStep 27006443 = 40509665) B40509665
theorem B18004295 : Blo 1665032 18004295 := bstep (se 1 (by rfl) ⟨13503221, by rfl⟩ : syracuseStep 18004295 = 27006443) B27006443
theorem B48011453 : Blo 1665032 48011453 := bstep (se 3 (by rfl) ⟨9002147, by rfl⟩ : syracuseStep 48011453 = 18004295) B18004295
theorem B32007635 : Blo 1665032 32007635 := bstep (se 1 (by rfl) ⟨24005726, by rfl⟩ : syracuseStep 32007635 = 48011453) B48011453
theorem B21338423 : Blo 1665032 21338423 := bstep (se 1 (by rfl) ⟨16003817, by rfl⟩ : syracuseStep 21338423 = 32007635) B32007635
theorem B14225615 : Blo 1665032 14225615 := bstep (se 1 (by rfl) ⟨10669211, by rfl⟩ : syracuseStep 14225615 = 21338423) B21338423
theorem B9483743 : Blo 1665032 9483743 := bstep (se 1 (by rfl) ⟨7112807, by rfl⟩ : syracuseStep 9483743 = 14225615) B14225615
theorem B6322495 : Blo 1665032 6322495 := bstep (se 1 (by rfl) ⟨4741871, by rfl⟩ : syracuseStep 6322495 = 9483743) B9483743
theorem B8429993 : Blo 1665032 8429993 := bstep (se 2 (by rfl) ⟨3161247, by rfl⟩ : syracuseStep 8429993 = 6322495) B6322495
theorem B5619995 : Blo 1665032 5619995 := bstep (se 1 (by rfl) ⟨4214996, by rfl⟩ : syracuseStep 5619995 = 8429993) B8429993
theorem B3746663 : Blo 1665032 3746663 := bstep (se 1 (by rfl) ⟨2809997, by rfl⟩ : syracuseStep 3746663 = 5619995) B5619995
theorem B2497775 : Blo 1665032 2497775 := bstep (se 1 (by rfl) ⟨1873331, by rfl⟩ : syracuseStep 2497775 = 3746663) B3746663
theorem B1665183 : Blo 1665032 1665183 := bstep (se 1 (by rfl) ⟨1248887, by rfl⟩ : syracuseStep 1665183 = 2497775) B2497775

theorem C0 (j : ℕ) (h1 : 416258 ≤ j) (h2 : j ≤ 416632) : Blo 1665032 (4 * j + 3) := by
  interval_cases j
  · exact B1665035
  · exact B1665039
  · exact B1665043
  · exact B1665047
  · exact B1665051
  · exact B1665055
  · exact B1665059
  · exact B1665063
  · exact B1665067
  · exact B1665071
  · exact B1665075
  · exact B1665079
  · exact B1665083
  · exact B1665087
  · exact B1665091
  · exact B1665095
  · exact B1665099
  · exact B1665103
  · exact B1665107
  · exact B1665111
  · exact B1665115
  · exact B1665119
  · exact B1665123
  · exact B1665127
  · exact B1665131
  · exact B1665135
  · exact B1665139
  · exact B1665143
  · exact B1665147
  · exact B1665151
  · exact B1665155
  · exact B1665159
  · exact B1665163
  · exact B1665167
  · exact B1665171
  · exact B1665175
  · exact B1665179
  · exact B1665183
  · exact B1665187
  · exact B1665191
  · exact B1665195
  · exact B1665199
  · exact B1665203
  · exact B1665207
  · exact B1665211
  · exact B1665215
  · exact B1665219
  · exact B1665223
  · exact B1665227
  · exact B1665231
  · exact B1665235
  · exact B1665239
  · exact B1665243
  · exact B1665247
  · exact B1665251
  · exact B1665255
  · exact B1665259
  · exact B1665263
  · exact B1665267
  · exact B1665271
  · exact B1665275
  · exact B1665279
  · exact B1665283
  · exact B1665287
  · exact B1665291
  · exact B1665295
  · exact B1665299
  · exact B1665303
  · exact B1665307
  · exact B1665311
  · exact B1665315
  · exact B1665319
  · exact B1665323
  · exact B1665327
  · exact B1665331
  · exact B1665335
  · exact B1665339
  · exact B1665343
  · exact B1665347
  · exact B1665351
  · exact B1665355
  · exact B1665359
  · exact B1665363
  · exact B1665367
  · exact B1665371
  · exact B1665375
  · exact B1665379
  · exact B1665383
  · exact B1665387
  · exact B1665391
  · exact B1665395
  · exact B1665399
  · exact B1665403
  · exact B1665407
  · exact B1665411
  · exact B1665415
  · exact B1665419
  · exact B1665423
  · exact B1665427
  · exact B1665431
  · exact B1665435
  · exact B1665439
  · exact B1665443
  · exact B1665447
  · exact B1665451
  · exact B1665455
  · exact B1665459
  · exact B1665463
  · exact B1665467
  · exact B1665471
  · exact B1665475
  · exact B1665479
  · exact B1665483
  · exact B1665487
  · exact B1665491
  · exact B1665495
  · exact B1665499
  · exact B1665503
  · exact B1665507
  · exact B1665511
  · exact B1665515
  · exact B1665519
  · exact B1665523
  · exact B1665527
  · exact B1665531
  · exact B1665535
  · exact B1665539
  · exact B1665543
  · exact B1665547
  · exact B1665551
  · exact B1665555
  · exact B1665559
  · exact B1665563
  · exact B1665567
  · exact B1665571
  · exact B1665575
  · exact B1665579
  · exact B1665583
  · exact B1665587
  · exact B1665591
  · exact B1665595
  · exact B1665599
  · exact B1665603
  · exact B1665607
  · exact B1665611
  · exact B1665615
  · exact B1665619
  · exact B1665623
  · exact B1665627
  · exact B1665631
  · exact B1665635
  · exact B1665639
  · exact B1665643
  · exact B1665647
  · exact B1665651
  · exact B1665655
  · exact B1665659
  · exact B1665663
  · exact B1665667
  · exact B1665671
  · exact B1665675
  · exact B1665679
  · exact B1665683
  · exact B1665687
  · exact B1665691
  · exact B1665695
  · exact B1665699
  · exact B1665703
  · exact B1665707
  · exact B1665711
  · exact B1665715
  · exact B1665719
  · exact B1665723
  · exact B1665727
  · exact B1665731
  · exact B1665735
  · exact B1665739
  · exact B1665743
  · exact B1665747
  · exact B1665751
  · exact B1665755
  · exact B1665759
  · exact B1665763
  · exact B1665767
  · exact B1665771
  · exact B1665775
  · exact B1665779
  · exact B1665783
  · exact B1665787
  · exact B1665791
  · exact B1665795
  · exact B1665799
  · exact B1665803
  · exact B1665807
  · exact B1665811
  · exact B1665815
  · exact B1665819
  · exact B1665823
  · exact B1665827
  · exact B1665831
  · exact B1665835
  · exact B1665839
  · exact B1665843
  · exact B1665847
  · exact B1665851
  · exact B1665855
  · exact B1665859
  · exact B1665863
  · exact B1665867
  · exact B1665871
  · exact B1665875
  · exact B1665879
  · exact B1665883
  · exact B1665887
  · exact B1665891
  · exact B1665895
  · exact B1665899
  · exact B1665903
  · exact B1665907
  · exact B1665911
  · exact B1665915
  · exact B1665919
  · exact B1665923
  · exact B1665927
  · exact B1665931
  · exact B1665935
  · exact B1665939
  · exact B1665943
  · exact B1665947
  · exact B1665951
  · exact B1665955
  · exact B1665959
  · exact B1665963
  · exact B1665967
  · exact B1665971
  · exact B1665975
  · exact B1665979
  · exact B1665983
  · exact B1665987
  · exact B1665991
  · exact B1665995
  · exact B1665999
  · exact B1666003
  · exact B1666007
  · exact B1666011
  · exact B1666015
  · exact B1666019
  · exact B1666023
  · exact B1666027
  · exact B1666031
  · exact B1666035
  · exact B1666039
  · exact B1666043
  · exact B1666047
  · exact B1666051
  · exact B1666055
  · exact B1666059
  · exact B1666063
  · exact B1666067
  · exact B1666071
  · exact B1666075
  · exact B1666079
  · exact B1666083
  · exact B1666087
  · exact B1666091
  · exact B1666095
  · exact B1666099
  · exact B1666103
  · exact B1666107
  · exact B1666111
  · exact B1666115
  · exact B1666119
  · exact B1666123
  · exact B1666127
  · exact B1666131
  · exact B1666135
  · exact B1666139
  · exact B1666143
  · exact B1666147
  · exact B1666151
  · exact B1666155
  · exact B1666159
  · exact B1666163
  · exact B1666167
  · exact B1666171
  · exact B1666175
  · exact B1666179
  · exact B1666183
  · exact B1666187
  · exact B1666191
  · exact B1666195
  · exact B1666199
  · exact B1666203
  · exact B1666207
  · exact B1666211
  · exact B1666215
  · exact B1666219
  · exact B1666223
  · exact B1666227
  · exact B1666231
  · exact B1666235
  · exact B1666239
  · exact B1666243
  · exact B1666247
  · exact B1666251
  · exact B1666255
  · exact B1666259
  · exact B1666263
  · exact B1666267
  · exact B1666271
  · exact B1666275
  · exact B1666279
  · exact B1666283
  · exact B1666287
  · exact B1666291
  · exact B1666295
  · exact B1666299
  · exact B1666303
  · exact B1666307
  · exact B1666311
  · exact B1666315
  · exact B1666319
  · exact B1666323
  · exact B1666327
  · exact B1666331
  · exact B1666335
  · exact B1666339
  · exact B1666343
  · exact B1666347
  · exact B1666351
  · exact B1666355
  · exact B1666359
  · exact B1666363
  · exact B1666367
  · exact B1666371
  · exact B1666375
  · exact B1666379
  · exact B1666383
  · exact B1666387
  · exact B1666391
  · exact B1666395
  · exact B1666399
  · exact B1666403
  · exact B1666407
  · exact B1666411
  · exact B1666415
  · exact B1666419
  · exact B1666423
  · exact B1666427
  · exact B1666431
  · exact B1666435
  · exact B1666439
  · exact B1666443
  · exact B1666447
  · exact B1666451
  · exact B1666455
  · exact B1666459
  · exact B1666463
  · exact B1666467
  · exact B1666471
  · exact B1666475
  · exact B1666479
  · exact B1666483
  · exact B1666487
  · exact B1666491
  · exact B1666495
  · exact B1666499
  · exact B1666503
  · exact B1666507
  · exact B1666511
  · exact B1666515
  · exact B1666519
  · exact B1666523
  · exact B1666527
  · exact B1666531

theorem solution (m : ℕ) (hlo : 1665032 ≤ m) (hhi : m ≤ 1666532) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 416258 ≤ j := by omega
    have hj2 : j ≤ 416632 := by omega
    have hb : Blo 1665032 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
