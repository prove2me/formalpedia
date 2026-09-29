-- Prove2me | solution 1 for syracuse_descends_range_1867635_1869635
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:12:53.556244+00:00
-- url     : https://prove2.me/submissions/251dd559-2d8a-48ca-8858-0603d533a89b

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


theorem B2801669 : Blo 1867635 2801669 := bbase (se 4 (by rfl) ⟨262656, by rfl⟩ : syracuseStep 2801669 = 525313) (by norm_num)
theorem B2801693 : Blo 1867635 2801693 := bbase (se 3 (by rfl) ⟨525317, by rfl⟩ : syracuseStep 2801693 = 1050635) (by norm_num)
theorem B3989533 : Blo 1867635 3989533 := bbase (se 3 (by rfl) ⟨748037, by rfl⟩ : syracuseStep 3989533 = 1496075) (by norm_num)
theorem B4202549 : Blo 1867635 4202549 := bbase (se 5 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 4202549 = 393989) (by norm_num)
theorem B2801717 : Blo 1867635 2801717 := bbase (se 5 (by rfl) ⟨131330, by rfl⟩ : syracuseStep 2801717 = 262661) (by norm_num)
theorem B2801741 : Blo 1867635 2801741 := bbase (se 3 (by rfl) ⟨525326, by rfl⟩ : syracuseStep 2801741 = 1050653) (by norm_num)
theorem B2801765 : Blo 1867635 2801765 := bbase (se 4 (by rfl) ⟨262665, by rfl⟩ : syracuseStep 2801765 = 525331) (by norm_num)
theorem B3547253 : Blo 1867635 3547253 := bbase (se 5 (by rfl) ⟨166277, by rfl⟩ : syracuseStep 3547253 = 332555) (by norm_num)
theorem B4202621 : Blo 1867635 4202621 := bbase (se 3 (by rfl) ⟨787991, by rfl⟩ : syracuseStep 4202621 = 1575983) (by norm_num)
theorem B2801789 : Blo 1867635 2801789 := bbase (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) (by norm_num)
theorem B3154045 : Blo 1867635 3154045 := bbase (se 3 (by rfl) ⟨591383, by rfl⟩ : syracuseStep 3154045 = 1182767) (by norm_num)
theorem B8519813 : Blo 1867635 8519813 := bbase (se 4 (by rfl) ⟨798732, by rfl⟩ : syracuseStep 8519813 = 1597465) (by norm_num)
theorem B2801813 : Blo 1867635 2801813 := bbase (se 6 (by rfl) ⟨65667, by rfl⟩ : syracuseStep 2801813 = 131335) (by norm_num)
theorem B2801837 : Blo 1867635 2801837 := bbase (se 3 (by rfl) ⟨525344, by rfl⟩ : syracuseStep 2801837 = 1050689) (by norm_num)
theorem B2244781 : Blo 1867635 2244781 := bbase (se 3 (by rfl) ⟨420896, by rfl⟩ : syracuseStep 2244781 = 841793) (by norm_num)
theorem B4202693 : Blo 1867635 4202693 := bbase (se 4 (by rfl) ⟨394002, by rfl⟩ : syracuseStep 4202693 = 788005) (by norm_num)
theorem B2801861 : Blo 1867635 2801861 := bbase (se 4 (by rfl) ⟨262674, by rfl⟩ : syracuseStep 2801861 = 525349) (by norm_num)
theorem B3154133 : Blo 1867635 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B2801885 : Blo 1867635 2801885 := bbase (se 3 (by rfl) ⟨525353, by rfl⟩ : syracuseStep 2801885 = 1050707) (by norm_num)
theorem B2801909 : Blo 1867635 2801909 := bbase (se 5 (by rfl) ⟨131339, by rfl⟩ : syracuseStep 2801909 = 262679) (by norm_num)
theorem B4202765 : Blo 1867635 4202765 := bbase (se 3 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 4202765 = 1576037) (by norm_num)
theorem B2801933 : Blo 1867635 2801933 := bbase (se 3 (by rfl) ⟨525362, by rfl⟩ : syracuseStep 2801933 = 1050725) (by norm_num)
theorem B3547405 : Blo 1867635 3547405 := bbase (se 3 (by rfl) ⟨665138, by rfl⟩ : syracuseStep 3547405 = 1330277) (by norm_num)
theorem B6308117 : Blo 1867635 6308117 := bbase (se 6 (by rfl) ⟨147846, by rfl⟩ : syracuseStep 6308117 = 295693) (by norm_num)
theorem B2130205 : Blo 1867635 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B2801957 : Blo 1867635 2801957 := bbase (se 4 (by rfl) ⟨262683, by rfl⟩ : syracuseStep 2801957 = 525367) (by norm_num)
theorem B2801981 : Blo 1867635 2801981 := bbase (se 3 (by rfl) ⟨525371, by rfl⟩ : syracuseStep 2801981 = 1050743) (by norm_num)
theorem B4202837 : Blo 1867635 4202837 := bbase (se 10 (by rfl) ⟨6156, by rfl⟩ : syracuseStep 4202837 = 12313) (by norm_num)
theorem B2802005 : Blo 1867635 2802005 := bbase (se 10 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 2802005 = 8209) (by norm_num)
theorem B3154261 : Blo 1867635 3154261 := bbase (se 10 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 3154261 = 9241) (by norm_num)
theorem B2802029 : Blo 1867635 2802029 := bbase (se 3 (by rfl) ⟨525380, by rfl⟩ : syracuseStep 2802029 = 1050761) (by norm_num)
theorem B3596653 : Blo 1867635 3596653 := bbase (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) (by norm_num)
theorem B2802053 : Blo 1867635 2802053 := bbase (se 4 (by rfl) ⟨262692, by rfl⟩ : syracuseStep 2802053 = 525385) (by norm_num)
theorem B4202909 : Blo 1867635 4202909 := bbase (se 3 (by rfl) ⟨788045, by rfl⟩ : syracuseStep 4202909 = 1576091) (by norm_num)
theorem B2802077 : Blo 1867635 2802077 := bbase (se 3 (by rfl) ⟨525389, by rfl⟩ : syracuseStep 2802077 = 1050779) (by norm_num)
theorem B3154349 : Blo 1867635 3154349 := bbase (se 3 (by rfl) ⟨591440, by rfl⟩ : syracuseStep 3154349 = 1182881) (by norm_num)
theorem B2802101 : Blo 1867635 2802101 := bbase (se 5 (by rfl) ⟨131348, by rfl⟩ : syracuseStep 2802101 = 262697) (by norm_num)
theorem B2802125 : Blo 1867635 2802125 := bbase (se 3 (by rfl) ⟨525398, by rfl⟩ : syracuseStep 2802125 = 1050797) (by norm_num)
theorem B4202981 : Blo 1867635 4202981 := bbase (se 4 (by rfl) ⟨394029, by rfl⟩ : syracuseStep 4202981 = 788059) (by norm_num)
theorem B2802149 : Blo 1867635 2802149 := bbase (se 4 (by rfl) ⟨262701, by rfl⟩ : syracuseStep 2802149 = 525403) (by norm_num)
theorem B2802173 : Blo 1867635 2802173 := bbase (se 3 (by rfl) ⟨525407, by rfl⟩ : syracuseStep 2802173 = 1050815) (by norm_num)
theorem B2802197 : Blo 1867635 2802197 := bbase (se 6 (by rfl) ⟨65676, by rfl⟩ : syracuseStep 2802197 = 131353) (by norm_num)
theorem B4203053 : Blo 1867635 4203053 := bbase (se 3 (by rfl) ⟨788072, by rfl⟩ : syracuseStep 4203053 = 1576145) (by norm_num)
theorem B2802221 : Blo 1867635 2802221 := bbase (se 3 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 2802221 = 1050833) (by norm_num)
theorem B3154477 : Blo 1867635 3154477 := bbase (se 3 (by rfl) ⟨591464, by rfl⟩ : syracuseStep 3154477 = 1182929) (by norm_num)
theorem B3547709 : Blo 1867635 3547709 := bbase (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) (by norm_num)
theorem B2802245 : Blo 1867635 2802245 := bbase (se 4 (by rfl) ⟨262710, by rfl⟩ : syracuseStep 2802245 = 525421) (by norm_num)
theorem B2802269 : Blo 1867635 2802269 := bbase (se 3 (by rfl) ⟨525425, by rfl⟩ : syracuseStep 2802269 = 1050851) (by norm_num)
theorem B4203125 : Blo 1867635 4203125 := bbase (se 5 (by rfl) ⟨197021, by rfl⟩ : syracuseStep 4203125 = 394043) (by norm_num)
theorem B2802293 : Blo 1867635 2802293 := bbase (se 5 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 2802293 = 262715) (by norm_num)
theorem B3154565 : Blo 1867635 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B2802317 : Blo 1867635 2802317 := bbase (se 3 (by rfl) ⟨525434, by rfl⟩ : syracuseStep 2802317 = 1050869) (by norm_num)
theorem B4489877 : Blo 1867635 4489877 := bbase (se 6 (by rfl) ⟨105231, by rfl⟩ : syracuseStep 4489877 = 210463) (by norm_num)
theorem B2802341 : Blo 1867635 2802341 := bbase (se 4 (by rfl) ⟨262719, by rfl⟩ : syracuseStep 2802341 = 525439) (by norm_num)
theorem B4203197 : Blo 1867635 4203197 := bbase (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) (by norm_num)
theorem B2802365 : Blo 1867635 2802365 := bbase (se 3 (by rfl) ⟨525443, by rfl⟩ : syracuseStep 2802365 = 1050887) (by norm_num)
theorem B6308549 : Blo 1867635 6308549 := bbase (se 4 (by rfl) ⟨591426, by rfl⟩ : syracuseStep 6308549 = 1182853) (by norm_num)
theorem B2802389 : Blo 1867635 2802389 := bbase (se 7 (by rfl) ⟨32840, by rfl⟩ : syracuseStep 2802389 = 65681) (by norm_num)
theorem B2802413 : Blo 1867635 2802413 := bbase (se 3 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 2802413 = 1050905) (by norm_num)
theorem B6390517 : Blo 1867635 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B4203269 : Blo 1867635 4203269 := bbase (se 4 (by rfl) ⟨394056, by rfl⟩ : syracuseStep 4203269 = 788113) (by norm_num)
theorem B2802437 : Blo 1867635 2802437 := bbase (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) (by norm_num)
theorem B3154693 : Blo 1867635 3154693 := bbase (se 4 (by rfl) ⟨295752, by rfl⟩ : syracuseStep 3154693 = 591505) (by norm_num)
theorem B2802461 : Blo 1867635 2802461 := bbase (se 3 (by rfl) ⟨525461, by rfl⟩ : syracuseStep 2802461 = 1050923) (by norm_num)
theorem B4727605 : Blo 1867635 4727605 := bbase (se 5 (by rfl) ⟨221606, by rfl⟩ : syracuseStep 4727605 = 443213) (by norm_num)
theorem B2802485 : Blo 1867635 2802485 := bbase (se 5 (by rfl) ⟨131366, by rfl⟩ : syracuseStep 2802485 = 262733) (by norm_num)
theorem B9462581 : Blo 1867635 9462581 := bbase (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) (by norm_num)
theorem B2769733 : Blo 1867635 2769733 := bbase (se 4 (by rfl) ⟨259662, by rfl⟩ : syracuseStep 2769733 = 519325) (by norm_num)
theorem B4203341 : Blo 1867635 4203341 := bbase (se 3 (by rfl) ⟨788126, by rfl⟩ : syracuseStep 4203341 = 1576253) (by norm_num)
theorem B2802509 : Blo 1867635 2802509 := bbase (se 3 (by rfl) ⟨525470, by rfl⟩ : syracuseStep 2802509 = 1050941) (by norm_num)
theorem B3154781 : Blo 1867635 3154781 := bbase (se 3 (by rfl) ⟨591521, by rfl⟩ : syracuseStep 3154781 = 1183043) (by norm_num)
theorem B2802533 : Blo 1867635 2802533 := bbase (se 4 (by rfl) ⟨262737, by rfl⟩ : syracuseStep 2802533 = 525475) (by norm_num)
theorem B2245477 : Blo 1867635 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B2802557 : Blo 1867635 2802557 := bbase (se 3 (by rfl) ⟨525479, by rfl⟩ : syracuseStep 2802557 = 1050959) (by norm_num)
theorem B4203413 : Blo 1867635 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B2802581 : Blo 1867635 2802581 := bbase (se 6 (by rfl) ⟨65685, by rfl⟩ : syracuseStep 2802581 = 131371) (by norm_num)
theorem B3990421 : Blo 1867635 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B2245525 : Blo 1867635 2245525 := bbase (se 6 (by rfl) ⟨52629, by rfl⟩ : syracuseStep 2245525 = 105259) (by norm_num)
theorem B4727717 : Blo 1867635 4727717 := bbase (se 4 (by rfl) ⟨443223, by rfl⟩ : syracuseStep 4727717 = 886447) (by norm_num)
theorem B2802605 : Blo 1867635 2802605 := bbase (se 3 (by rfl) ⟨525488, by rfl⟩ : syracuseStep 2802605 = 1050977) (by norm_num)
theorem B10101685 : Blo 1867635 10101685 := bbase (se 5 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 10101685 = 947033) (by norm_num)
theorem B7095221 : Blo 1867635 7095221 := bbase (se 5 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 7095221 = 665177) (by norm_num)
theorem B2802629 : Blo 1867635 2802629 := bbase (se 4 (by rfl) ⟨262746, by rfl⟩ : syracuseStep 2802629 = 525493) (by norm_num)
theorem B4203485 : Blo 1867635 4203485 := bbase (se 3 (by rfl) ⟨788153, by rfl⟩ : syracuseStep 4203485 = 1576307) (by norm_num)
theorem B2802653 : Blo 1867635 2802653 := bbase (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) (by norm_num)
theorem B3154909 : Blo 1867635 3154909 := bbase (se 3 (by rfl) ⟨591545, by rfl⟩ : syracuseStep 3154909 = 1183091) (by norm_num)
theorem B2802677 : Blo 1867635 2802677 := bbase (se 5 (by rfl) ⟨131375, by rfl⟩ : syracuseStep 2802677 = 262751) (by norm_num)
theorem B3990541 : Blo 1867635 3990541 := bbase (se 3 (by rfl) ⟨748226, by rfl⟩ : syracuseStep 3990541 = 1496453) (by norm_num)
theorem B2802701 : Blo 1867635 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B31917077 : Blo 1867635 31917077 := bbase (se 6 (by rfl) ⟨748056, by rfl⟩ : syracuseStep 31917077 = 1496113) (by norm_num)
theorem B4203557 : Blo 1867635 4203557 := bbase (se 4 (by rfl) ⟨394083, by rfl⟩ : syracuseStep 4203557 = 788167) (by norm_num)
theorem B2802725 : Blo 1867635 2802725 := bbase (se 4 (by rfl) ⟨262755, by rfl⟩ : syracuseStep 2802725 = 525511) (by norm_num)
theorem B1893421 : Blo 1867635 1893421 := bbase (se 3 (by rfl) ⟨355016, by rfl⟩ : syracuseStep 1893421 = 710033) (by norm_num)
theorem B3154997 : Blo 1867635 3154997 := bbase (se 5 (by rfl) ⟨147890, by rfl⟩ : syracuseStep 3154997 = 295781) (by norm_num)
theorem B2802749 : Blo 1867635 2802749 := bbase (se 3 (by rfl) ⟨525515, by rfl⟩ : syracuseStep 2802749 = 1051031) (by norm_num)
theorem B2802773 : Blo 1867635 2802773 := bbase (se 8 (by rfl) ⟨16422, by rfl⟩ : syracuseStep 2802773 = 32845) (by norm_num)
theorem B6734933 : Blo 1867635 6734933 := bbase (se 8 (by rfl) ⟨39462, by rfl⟩ : syracuseStep 6734933 = 78925) (by norm_num)
theorem B4727909 : Blo 1867635 4727909 := bbase (se 4 (by rfl) ⟨443241, by rfl⟩ : syracuseStep 4727909 = 886483) (by norm_num)
theorem B4203629 : Blo 1867635 4203629 := bbase (se 3 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 4203629 = 1576361) (by norm_num)
theorem B2802797 : Blo 1867635 2802797 := bbase (se 3 (by rfl) ⟨525524, by rfl⟩ : syracuseStep 2802797 = 1051049) (by norm_num)
theorem B6308981 : Blo 1867635 6308981 := bbase (se 5 (by rfl) ⟨295733, by rfl⟩ : syracuseStep 6308981 = 591467) (by norm_num)
theorem B2802821 : Blo 1867635 2802821 := bbase (se 4 (by rfl) ⟨262764, by rfl⟩ : syracuseStep 2802821 = 525529) (by norm_num)
theorem B5121157 : Blo 1867635 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B2802845 : Blo 1867635 2802845 := bbase (se 3 (by rfl) ⟨525533, by rfl⟩ : syracuseStep 2802845 = 1051067) (by norm_num)
theorem B4203701 : Blo 1867635 4203701 := bbase (se 5 (by rfl) ⟨197048, by rfl⟩ : syracuseStep 4203701 = 394097) (by norm_num)
theorem B2802869 : Blo 1867635 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B2802893 : Blo 1867635 2802893 := bbase (se 3 (by rfl) ⟨525542, by rfl⟩ : syracuseStep 2802893 = 1051085) (by norm_num)
theorem B7095509 : Blo 1867635 7095509 := bbase (se 7 (by rfl) ⟨83150, by rfl⟩ : syracuseStep 7095509 = 166301) (by norm_num)
theorem B2802917 : Blo 1867635 2802917 := bbase (se 4 (by rfl) ⟨262773, by rfl⟩ : syracuseStep 2802917 = 525547) (by norm_num)
theorem B4203773 : Blo 1867635 4203773 := bbase (se 3 (by rfl) ⟨788207, by rfl⟩ : syracuseStep 4203773 = 1576415) (by norm_num)
theorem B2802941 : Blo 1867635 2802941 := bbase (se 3 (by rfl) ⟨525551, by rfl⟩ : syracuseStep 2802941 = 1051103) (by norm_num)
theorem B3990797 : Blo 1867635 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2802965 : Blo 1867635 2802965 := bbase (se 6 (by rfl) ⟨65694, by rfl⟩ : syracuseStep 2802965 = 131389) (by norm_num)
theorem B3196189 : Blo 1867635 3196189 := bbase (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) (by norm_num)
theorem B2802989 : Blo 1867635 2802989 := bbase (se 3 (by rfl) ⟨525560, by rfl⟩ : syracuseStep 2802989 = 1051121) (by norm_num)
theorem B3548461 : Blo 1867635 3548461 := bbase (se 3 (by rfl) ⟨665336, by rfl⟩ : syracuseStep 3548461 = 1330673) (by norm_num)
theorem B4203845 : Blo 1867635 4203845 := bbase (se 4 (by rfl) ⟨394110, by rfl⟩ : syracuseStep 4203845 = 788221) (by norm_num)
theorem B2803013 : Blo 1867635 2803013 := bbase (se 4 (by rfl) ⟨262782, by rfl⟩ : syracuseStep 2803013 = 525565) (by norm_num)
theorem B1893713 : Blo 1867635 1893713 := bbase (se 2 (by rfl) ⟨710142, by rfl⟩ : syracuseStep 1893713 = 1420285) (by norm_num)
theorem B2803037 : Blo 1867635 2803037 := bbase (se 3 (by rfl) ⟨525569, by rfl⟩ : syracuseStep 2803037 = 1051139) (by norm_num)
theorem B2803061 : Blo 1867635 2803061 := bbase (se 5 (by rfl) ⟨131393, by rfl⟩ : syracuseStep 2803061 = 262787) (by norm_num)
theorem B6735221 : Blo 1867635 6735221 := bbase (se 5 (by rfl) ⟨315713, by rfl⟩ : syracuseStep 6735221 = 631427) (by norm_num)
theorem B4203917 : Blo 1867635 4203917 := bbase (se 3 (by rfl) ⟨788234, by rfl⟩ : syracuseStep 4203917 = 1576469) (by norm_num)
theorem B2803085 : Blo 1867635 2803085 := bbase (se 3 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 2803085 = 1051157) (by norm_num)
theorem B2803109 : Blo 1867635 2803109 := bbase (se 4 (by rfl) ⟨262791, by rfl⟩ : syracuseStep 2803109 = 525583) (by norm_num)
theorem B4728253 : Blo 1867635 4728253 := bbase (se 3 (by rfl) ⟨886547, by rfl⟩ : syracuseStep 4728253 = 1773095) (by norm_num)
theorem B2803133 : Blo 1867635 2803133 := bbase (se 3 (by rfl) ⟨525587, by rfl⟩ : syracuseStep 2803133 = 1051175) (by norm_num)
theorem B3548605 : Blo 1867635 3548605 := bbase (se 3 (by rfl) ⟨665363, by rfl⟩ : syracuseStep 3548605 = 1330727) (by norm_num)
theorem B4203989 : Blo 1867635 4203989 := bbase (se 7 (by rfl) ⟨49265, by rfl⟩ : syracuseStep 4203989 = 98531) (by norm_num)
theorem B2803157 : Blo 1867635 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B4261357 : Blo 1867635 4261357 := bbase (se 3 (by rfl) ⟨799004, by rfl⟩ : syracuseStep 4261357 = 1598009) (by norm_num)
theorem B2803181 : Blo 1867635 2803181 := bbase (se 3 (by rfl) ⟨525596, by rfl⟩ : syracuseStep 2803181 = 1051193) (by norm_num)
theorem B2803205 : Blo 1867635 2803205 := bbase (se 4 (by rfl) ⟨262800, by rfl⟩ : syracuseStep 2803205 = 525601) (by norm_num)
theorem B4204061 : Blo 1867635 4204061 := bbase (se 3 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 4204061 = 1576523) (by norm_num)
theorem B2803229 : Blo 1867635 2803229 := bbase (se 3 (by rfl) ⟨525605, by rfl⟩ : syracuseStep 2803229 = 1051211) (by norm_num)
theorem B6309413 : Blo 1867635 6309413 := bbase (se 4 (by rfl) ⟨591507, by rfl⟩ : syracuseStep 6309413 = 1183015) (by norm_num)
theorem B4728365 : Blo 1867635 4728365 := bbase (se 3 (by rfl) ⟨886568, by rfl⟩ : syracuseStep 4728365 = 1773137) (by norm_num)
theorem B2803253 : Blo 1867635 2803253 := bbase (se 5 (by rfl) ⟨131402, by rfl⟩ : syracuseStep 2803253 = 262805) (by norm_num)
theorem B2803277 : Blo 1867635 2803277 := bbase (se 3 (by rfl) ⟨525614, by rfl⟩ : syracuseStep 2803277 = 1051229) (by norm_num)
theorem B3368533 : Blo 1867635 3368533 := bbase (se 8 (by rfl) ⟨19737, by rfl⟩ : syracuseStep 3368533 = 39475) (by norm_num)
theorem B3548765 : Blo 1867635 3548765 := bbase (se 3 (by rfl) ⟨665393, by rfl⟩ : syracuseStep 3548765 = 1330787) (by norm_num)
theorem B4204133 : Blo 1867635 4204133 := bbase (se 4 (by rfl) ⟨394137, by rfl⟩ : syracuseStep 4204133 = 788275) (by norm_num)
theorem B2803301 : Blo 1867635 2803301 := bbase (se 4 (by rfl) ⟨262809, by rfl⟩ : syracuseStep 2803301 = 525619) (by norm_num)
theorem B2524789 : Blo 1867635 2524789 := bbase (se 5 (by rfl) ⟨118349, by rfl⟩ : syracuseStep 2524789 = 236699) (by norm_num)
theorem B2803325 : Blo 1867635 2803325 := bbase (se 3 (by rfl) ⟨525623, by rfl⟩ : syracuseStep 2803325 = 1051247) (by norm_num)
theorem B2803349 : Blo 1867635 2803349 := bbase (se 6 (by rfl) ⟨65703, by rfl⟩ : syracuseStep 2803349 = 131407) (by norm_num)
theorem B4204205 : Blo 1867635 4204205 := bbase (se 3 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 4204205 = 1576577) (by norm_num)
theorem B2803373 : Blo 1867635 2803373 := bbase (se 3 (by rfl) ⟨525632, by rfl⟩ : syracuseStep 2803373 = 1051265) (by norm_num)
theorem B2803397 : Blo 1867635 2803397 := bbase (se 4 (by rfl) ⟨262818, by rfl⟩ : syracuseStep 2803397 = 525637) (by norm_num)
theorem B2803421 : Blo 1867635 2803421 := bbase (se 3 (by rfl) ⟨525641, by rfl⟩ : syracuseStep 2803421 = 1051283) (by norm_num)
theorem B4728557 : Blo 1867635 4728557 := bbase (se 3 (by rfl) ⟨886604, by rfl⟩ : syracuseStep 4728557 = 1773209) (by norm_num)
theorem B3548909 : Blo 1867635 3548909 := bbase (se 3 (by rfl) ⟨665420, by rfl⟩ : syracuseStep 3548909 = 1330841) (by norm_num)
theorem B4204277 : Blo 1867635 4204277 := bbase (se 5 (by rfl) ⟨197075, by rfl⟩ : syracuseStep 4204277 = 394151) (by norm_num)
theorem B2803445 : Blo 1867635 2803445 := bbase (se 5 (by rfl) ⟨131411, by rfl⟩ : syracuseStep 2803445 = 262823) (by norm_num)
theorem B2803469 : Blo 1867635 2803469 := bbase (se 3 (by rfl) ⟨525650, by rfl⟩ : syracuseStep 2803469 = 1051301) (by norm_num)
theorem B6735653 : Blo 1867635 6735653 := bbase (se 4 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 6735653 = 1262935) (by norm_num)
theorem B2803493 : Blo 1867635 2803493 := bbase (se 4 (by rfl) ⟨262827, by rfl⟩ : syracuseStep 2803493 = 525655) (by norm_num)
theorem B4204349 : Blo 1867635 4204349 := bbase (se 3 (by rfl) ⟨788315, by rfl⟩ : syracuseStep 4204349 = 1576631) (by norm_num)
theorem B2803517 : Blo 1867635 2803517 := bbase (se 3 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 2803517 = 1051319) (by norm_num)
theorem B2803541 : Blo 1867635 2803541 := bbase (se 9 (by rfl) ⟨8213, by rfl⟩ : syracuseStep 2803541 = 16427) (by norm_num)
theorem B2697061 : Blo 1867635 2697061 := bbase (se 4 (by rfl) ⟨252849, by rfl⟩ : syracuseStep 2697061 = 505699) (by norm_num)
theorem B2803565 : Blo 1867635 2803565 := bbase (se 3 (by rfl) ⟨525668, by rfl⟩ : syracuseStep 2803565 = 1051337) (by norm_num)
theorem B4204421 : Blo 1867635 4204421 := bbase (se 4 (by rfl) ⟨394164, by rfl⟩ : syracuseStep 4204421 = 788329) (by norm_num)
theorem B2803589 : Blo 1867635 2803589 := bbase (se 4 (by rfl) ⟨262836, by rfl⟩ : syracuseStep 2803589 = 525673) (by norm_num)
theorem B2992021 : Blo 1867635 2992021 := bbase (se 6 (by rfl) ⟨70125, by rfl⟩ : syracuseStep 2992021 = 140251) (by norm_num)
theorem B2803613 : Blo 1867635 2803613 := bbase (se 3 (by rfl) ⟨525677, by rfl⟩ : syracuseStep 2803613 = 1051355) (by norm_num)
theorem B2803637 : Blo 1867635 2803637 := bbase (se 5 (by rfl) ⟨131420, by rfl⟩ : syracuseStep 2803637 = 262841) (by norm_num)
theorem B4204493 : Blo 1867635 4204493 := bbase (se 3 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 4204493 = 1576685) (by norm_num)
theorem B2803661 : Blo 1867635 2803661 := bbase (se 3 (by rfl) ⟨525686, by rfl⟩ : syracuseStep 2803661 = 1051373) (by norm_num)
theorem B6309845 : Blo 1867635 6309845 := bbase (se 7 (by rfl) ⟨73943, by rfl⟩ : syracuseStep 6309845 = 147887) (by norm_num)
theorem B3196901 : Blo 1867635 3196901 := bbase (se 4 (by rfl) ⟨299709, by rfl⟩ : syracuseStep 3196901 = 599419) (by norm_num)
theorem B2803685 : Blo 1867635 2803685 := bbase (se 4 (by rfl) ⟨262845, by rfl⟩ : syracuseStep 2803685 = 525691) (by norm_num)
theorem B2803709 : Blo 1867635 2803709 := bbase (se 3 (by rfl) ⟨525695, by rfl⟩ : syracuseStep 2803709 = 1051391) (by norm_num)
theorem B3549197 : Blo 1867635 3549197 := bbase (se 3 (by rfl) ⟨665474, by rfl⟩ : syracuseStep 3549197 = 1330949) (by norm_num)
theorem B4204565 : Blo 1867635 4204565 := bbase (se 6 (by rfl) ⟨98544, by rfl⟩ : syracuseStep 4204565 = 197089) (by norm_num)
theorem B2803733 : Blo 1867635 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B5318693 : Blo 1867635 5318693 := bbase (se 4 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 5318693 = 997255) (by norm_num)
theorem B4491301 : Blo 1867635 4491301 := bbase (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) (by norm_num)
theorem B2803757 : Blo 1867635 2803757 := bbase (se 3 (by rfl) ⟨525704, by rfl⟩ : syracuseStep 2803757 = 1051409) (by norm_num)
theorem B4728901 : Blo 1867635 4728901 := bbase (se 4 (by rfl) ⟨443334, by rfl⟩ : syracuseStep 4728901 = 886669) (by norm_num)
theorem B2803781 : Blo 1867635 2803781 := bbase (se 4 (by rfl) ⟨262854, by rfl⟩ : syracuseStep 2803781 = 525709) (by norm_num)
theorem B9463877 : Blo 1867635 9463877 := bbase (se 4 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 9463877 = 1774477) (by norm_num)
theorem B4204637 : Blo 1867635 4204637 := bbase (se 3 (by rfl) ⟨788369, by rfl⟩ : syracuseStep 4204637 = 1576739) (by norm_num)
theorem B2803805 : Blo 1867635 2803805 := bbase (se 3 (by rfl) ⟨525713, by rfl⟩ : syracuseStep 2803805 = 1051427) (by norm_num)
theorem B2803829 : Blo 1867635 2803829 := bbase (se 5 (by rfl) ⟨131429, by rfl⟩ : syracuseStep 2803829 = 262859) (by norm_num)
theorem B3991685 : Blo 1867635 3991685 := bbase (se 4 (by rfl) ⟨374220, by rfl⟩ : syracuseStep 3991685 = 748441) (by norm_num)
theorem B2803853 : Blo 1867635 2803853 := bbase (se 3 (by rfl) ⟨525722, by rfl⟩ : syracuseStep 2803853 = 1051445) (by norm_num)
theorem B4204709 : Blo 1867635 4204709 := bbase (se 4 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 4204709 = 788383) (by norm_num)
theorem B2803877 : Blo 1867635 2803877 := bbase (se 4 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 2803877 = 525727) (by norm_num)
theorem B3549349 : Blo 1867635 3549349 := bbase (se 4 (by rfl) ⟨332751, by rfl⟩ : syracuseStep 3549349 = 665503) (by norm_num)
theorem B4729013 : Blo 1867635 4729013 := bbase (se 5 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 4729013 = 443345) (by norm_num)
theorem B2803901 : Blo 1867635 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B7981253 : Blo 1867635 7981253 := bbase (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) (by norm_num)
theorem B2803925 : Blo 1867635 2803925 := bbase (se 7 (by rfl) ⟨32858, by rfl⟩ : syracuseStep 2803925 = 65717) (by norm_num)
theorem B4204781 : Blo 1867635 4204781 := bbase (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) (by norm_num)
theorem B2803949 : Blo 1867635 2803949 := bbase (se 3 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 2803949 = 1051481) (by norm_num)
theorem B3197189 : Blo 1867635 3197189 := bbase (se 4 (by rfl) ⟨299736, by rfl⟩ : syracuseStep 3197189 = 599473) (by norm_num)
theorem B2803973 : Blo 1867635 2803973 := bbase (se 4 (by rfl) ⟨262872, by rfl⟩ : syracuseStep 2803973 = 525745) (by norm_num)
theorem B2803997 : Blo 1867635 2803997 := bbase (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) (by norm_num)
theorem B4204853 : Blo 1867635 4204853 := bbase (se 5 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 4204853 = 394205) (by norm_num)
theorem B2804021 : Blo 1867635 2804021 := bbase (se 5 (by rfl) ⟨131438, by rfl⟩ : syracuseStep 2804021 = 262877) (by norm_num)
theorem B2525509 : Blo 1867635 2525509 := bbase (se 4 (by rfl) ⟨236766, by rfl⟩ : syracuseStep 2525509 = 473533) (by norm_num)
theorem B2804045 : Blo 1867635 2804045 := bbase (se 3 (by rfl) ⟨525758, by rfl⟩ : syracuseStep 2804045 = 1051517) (by norm_num)
theorem B2992477 : Blo 1867635 2992477 := bbase (se 3 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 2992477 = 1122179) (by norm_num)
theorem B2804069 : Blo 1867635 2804069 := bbase (se 4 (by rfl) ⟨262881, by rfl⟩ : syracuseStep 2804069 = 525763) (by norm_num)
theorem B4729205 : Blo 1867635 4729205 := bbase (se 5 (by rfl) ⟨221681, by rfl⟩ : syracuseStep 4729205 = 443363) (by norm_num)
theorem B7096693 : Blo 1867635 7096693 := bbase (se 5 (by rfl) ⟨332657, by rfl⟩ : syracuseStep 7096693 = 665315) (by norm_num)
theorem B3991925 : Blo 1867635 3991925 := bbase (se 5 (by rfl) ⟨187121, by rfl⟩ : syracuseStep 3991925 = 374243) (by norm_num)
theorem B4204925 : Blo 1867635 4204925 := bbase (se 3 (by rfl) ⟨788423, by rfl⟩ : syracuseStep 4204925 = 1576847) (by norm_num)
theorem B2804093 : Blo 1867635 2804093 := bbase (se 3 (by rfl) ⟨525767, by rfl⟩ : syracuseStep 2804093 = 1051535) (by norm_num)
theorem B2804117 : Blo 1867635 2804117 := bbase (se 6 (by rfl) ⟨65721, by rfl⟩ : syracuseStep 2804117 = 131443) (by norm_num)
theorem B2804141 : Blo 1867635 2804141 := bbase (se 3 (by rfl) ⟨525776, by rfl⟩ : syracuseStep 2804141 = 1051553) (by norm_num)
theorem B4204997 : Blo 1867635 4204997 := bbase (se 4 (by rfl) ⟨394218, by rfl⟩ : syracuseStep 4204997 = 788437) (by norm_num)
theorem B2804165 : Blo 1867635 2804165 := bbase (se 4 (by rfl) ⟨262890, by rfl⟩ : syracuseStep 2804165 = 525781) (by norm_num)
theorem B2804189 : Blo 1867635 2804189 := bbase (se 3 (by rfl) ⟨525785, by rfl⟩ : syracuseStep 2804189 = 1051571) (by norm_num)
theorem B9456101 : Blo 1867635 9456101 := bbase (se 4 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 9456101 = 1773019) (by norm_num)
theorem B5048821 : Blo 1867635 5048821 := bbase (se 5 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 5048821 = 473327) (by norm_num)
theorem B2804213 : Blo 1867635 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B4205069 : Blo 1867635 4205069 := bbase (se 3 (by rfl) ⟨788450, by rfl⟩ : syracuseStep 4205069 = 1576901) (by norm_num)
theorem B2804237 : Blo 1867635 2804237 := bbase (se 3 (by rfl) ⟨525794, by rfl⟩ : syracuseStep 2804237 = 1051589) (by norm_num)
theorem B2804261 : Blo 1867635 2804261 := bbase (se 4 (by rfl) ⟨262899, by rfl⟩ : syracuseStep 2804261 = 525799) (by norm_num)
theorem B2804285 : Blo 1867635 2804285 := bbase (se 3 (by rfl) ⟨525803, by rfl⟩ : syracuseStep 2804285 = 1051607) (by norm_num)
theorem B4205141 : Blo 1867635 4205141 := bbase (se 8 (by rfl) ⟨24639, by rfl⟩ : syracuseStep 4205141 = 49279) (by norm_num)
theorem B2804309 : Blo 1867635 2804309 := bbase (se 8 (by rfl) ⟨16431, by rfl⟩ : syracuseStep 2804309 = 32863) (by norm_num)
theorem B2804333 : Blo 1867635 2804333 := bbase (se 3 (by rfl) ⟨525812, by rfl⟩ : syracuseStep 2804333 = 1051625) (by norm_num)
theorem B4795013 : Blo 1867635 4795013 := bbase (se 4 (by rfl) ⟨449532, by rfl⟩ : syracuseStep 4795013 = 899065) (by norm_num)
theorem B2804357 : Blo 1867635 2804357 := bbase (se 4 (by rfl) ⟨262908, by rfl⟩ : syracuseStep 2804357 = 525817) (by norm_num)
theorem B4205213 : Blo 1867635 4205213 := bbase (se 3 (by rfl) ⟨788477, by rfl⟩ : syracuseStep 4205213 = 1576955) (by norm_num)
theorem B2804381 : Blo 1867635 2804381 := bbase (se 3 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 2804381 = 1051643) (by norm_num)
theorem B7096997 : Blo 1867635 7096997 := bbase (se 4 (by rfl) ⟨665343, by rfl⟩ : syracuseStep 7096997 = 1330687) (by norm_num)
theorem B2804405 : Blo 1867635 2804405 := bbase (se 5 (by rfl) ⟨131456, by rfl⟩ : syracuseStep 2804405 = 262913) (by norm_num)
theorem B4491973 : Blo 1867635 4491973 := bbase (se 4 (by rfl) ⟨421122, by rfl⟩ : syracuseStep 4491973 = 842245) (by norm_num)
theorem B4729549 : Blo 1867635 4729549 := bbase (se 3 (by rfl) ⟨886790, by rfl⟩ : syracuseStep 4729549 = 1773581) (by norm_num)
theorem B2804429 : Blo 1867635 2804429 := bbase (se 3 (by rfl) ⟨525830, by rfl⟩ : syracuseStep 2804429 = 1051661) (by norm_num)
theorem B4205285 : Blo 1867635 4205285 := bbase (se 4 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 4205285 = 788491) (by norm_num)
theorem B2804453 : Blo 1867635 2804453 := bbase (se 4 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 2804453 = 525835) (by norm_num)
theorem B2525941 : Blo 1867635 2525941 := bbase (se 5 (by rfl) ⟨118403, by rfl⟩ : syracuseStep 2525941 = 236807) (by norm_num)
theorem B5319445 : Blo 1867635 5319445 := bbase (se 6 (by rfl) ⟨124674, by rfl⟩ : syracuseStep 5319445 = 249349) (by norm_num)
theorem B4205357 : Blo 1867635 4205357 := bbase (se 3 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 4205357 = 1577009) (by norm_num)
theorem B4729661 : Blo 1867635 4729661 := bbase (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) (by norm_num)
theorem B5679973 : Blo 1867635 5679973 := bbase (se 4 (by rfl) ⟨532497, by rfl⟩ : syracuseStep 5679973 = 1064995) (by norm_num)
theorem B3992429 : Blo 1867635 3992429 := bbase (se 3 (by rfl) ⟨748580, by rfl⟩ : syracuseStep 3992429 = 1497161) (by norm_num)
theorem B4205429 : Blo 1867635 4205429 := bbase (se 5 (by rfl) ⟨197129, by rfl⟩ : syracuseStep 4205429 = 394259) (by norm_num)
theorem B3992437 : Blo 1867635 3992437 := bbase (se 5 (by rfl) ⟨187145, by rfl⟩ : syracuseStep 3992437 = 374291) (by norm_num)
theorem B4205501 : Blo 1867635 4205501 := bbase (se 3 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 4205501 = 1577063) (by norm_num)
theorem B4729853 : Blo 1867635 4729853 := bbase (se 3 (by rfl) ⟨886847, by rfl⟩ : syracuseStep 4729853 = 1773695) (by norm_num)
theorem B2993149 : Blo 1867635 2993149 := bbase (se 3 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 2993149 = 1122431) (by norm_num)
theorem B4205573 : Blo 1867635 4205573 := bbase (se 4 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 4205573 = 788545) (by norm_num)
theorem B4205645 : Blo 1867635 4205645 := bbase (se 3 (by rfl) ⟨788558, by rfl⟩ : syracuseStep 4205645 = 1577117) (by norm_num)
theorem B4205717 : Blo 1867635 4205717 := bbase (se 6 (by rfl) ⟨98571, by rfl⟩ : syracuseStep 4205717 = 197143) (by norm_num)
theorem B11365589 : Blo 1867635 11365589 := bbase (se 7 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 11365589 = 266381) (by norm_num)
theorem B2526421 : Blo 1867635 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B4205789 : Blo 1867635 4205789 := bbase (se 3 (by rfl) ⟨788585, by rfl⟩ : syracuseStep 4205789 = 1577171) (by norm_num)
theorem B4205861 : Blo 1867635 4205861 := bbase (se 4 (by rfl) ⟨394299, by rfl⟩ : syracuseStep 4205861 = 788599) (by norm_num)
theorem B4730197 : Blo 1867635 4730197 := bbase (se 11 (by rfl) ⟨3464, by rfl⟩ : syracuseStep 4730197 = 6929) (by norm_num)
theorem B4205933 : Blo 1867635 4205933 := bbase (se 3 (by rfl) ⟨788612, by rfl⟩ : syracuseStep 4205933 = 1577225) (by norm_num)
theorem B2993573 : Blo 1867635 2993573 := bbase (se 4 (by rfl) ⟨280647, by rfl⟩ : syracuseStep 2993573 = 561295) (by norm_num)
theorem B4206005 : Blo 1867635 4206005 := bbase (se 5 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 4206005 = 394313) (by norm_num)
theorem B4730309 : Blo 1867635 4730309 := bbase (se 4 (by rfl) ⟨443466, by rfl⟩ : syracuseStep 4730309 = 886933) (by norm_num)
theorem B4206077 : Blo 1867635 4206077 := bbase (se 3 (by rfl) ⟨788639, by rfl⟩ : syracuseStep 4206077 = 1577279) (by norm_num)
theorem B4206149 : Blo 1867635 4206149 := bbase (se 4 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 4206149 = 788653) (by norm_num)
theorem B6303365 : Blo 1867635 6303365 := bbase (se 4 (by rfl) ⟨590940, by rfl⟩ : syracuseStep 6303365 = 1181881) (by norm_num)
theorem B5049989 : Blo 1867635 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B4730501 : Blo 1867635 4730501 := bbase (se 4 (by rfl) ⟨443484, by rfl⟩ : syracuseStep 4730501 = 886969) (by norm_num)
theorem B4206221 : Blo 1867635 4206221 := bbase (se 3 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 4206221 = 1577333) (by norm_num)
theorem B3239573 : Blo 1867635 3239573 := bbase (se 6 (by rfl) ⟨75927, by rfl⟩ : syracuseStep 3239573 = 151855) (by norm_num)
theorem B2993861 : Blo 1867635 2993861 := bbase (se 4 (by rfl) ⟨280674, by rfl⟩ : syracuseStep 2993861 = 561349) (by norm_num)
theorem B4206293 : Blo 1867635 4206293 := bbase (se 7 (by rfl) ⟨49292, by rfl⟩ : syracuseStep 4206293 = 98585) (by norm_num)
theorem B2559709 : Blo 1867635 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B9457397 : Blo 1867635 9457397 := bbase (se 5 (by rfl) ⟨443315, by rfl⟩ : syracuseStep 9457397 = 886631) (by norm_num)
theorem B4206365 : Blo 1867635 4206365 := bbase (se 3 (by rfl) ⟨788693, by rfl⟩ : syracuseStep 4206365 = 1577387) (by norm_num)
theorem B2395993 : Blo 1867635 2395993 := bbase (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) (by norm_num)
theorem B4206437 : Blo 1867635 4206437 := bbase (se 4 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 4206437 = 788707) (by norm_num)
theorem B2101117 : Blo 1867635 2101117 := bbase (se 3 (by rfl) ⟨393959, by rfl⟩ : syracuseStep 2101117 = 787919) (by norm_num)
theorem B2101153 : Blo 1867635 2101153 := bbase (se 2 (by rfl) ⟨787932, by rfl⟩ : syracuseStep 2101153 = 1575865) (by norm_num)
theorem B4206509 : Blo 1867635 4206509 := bbase (se 3 (by rfl) ⟨788720, by rfl⟩ : syracuseStep 4206509 = 1577441) (by norm_num)
theorem B7983029 : Blo 1867635 7983029 := bbase (se 5 (by rfl) ⟨374204, by rfl⟩ : syracuseStep 7983029 = 748409) (by norm_num)
theorem B2101189 : Blo 1867635 2101189 := bbase (se 4 (by rfl) ⟨196986, by rfl⟩ : syracuseStep 2101189 = 393973) (by norm_num)
theorem B5050325 : Blo 1867635 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B4730845 : Blo 1867635 4730845 := bbase (se 3 (by rfl) ⟨887033, by rfl⟩ : syracuseStep 4730845 = 1774067) (by norm_num)
theorem B2101225 : Blo 1867635 2101225 := bbase (se 2 (by rfl) ⟨787959, by rfl⟩ : syracuseStep 2101225 = 1575919) (by norm_num)
theorem B2396137 : Blo 1867635 2396137 := bbase (se 2 (by rfl) ⟨898551, by rfl⟩ : syracuseStep 2396137 = 1797103) (by norm_num)
theorem B4206581 : Blo 1867635 4206581 := bbase (se 5 (by rfl) ⟨197183, by rfl⟩ : syracuseStep 4206581 = 394367) (by norm_num)
theorem B1994749 : Blo 1867635 1994749 := bbase (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) (by norm_num)
theorem B2101261 : Blo 1867635 2101261 := bbase (se 3 (by rfl) ⟨393986, by rfl⟩ : syracuseStep 2101261 = 787973) (by norm_num)
theorem B2101297 : Blo 1867635 2101297 := bbase (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) (by norm_num)
theorem B6303797 : Blo 1867635 6303797 := bbase (se 5 (by rfl) ⟨295490, by rfl⟩ : syracuseStep 6303797 = 590981) (by norm_num)
theorem B4206653 : Blo 1867635 4206653 := bbase (se 3 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 4206653 = 1577495) (by norm_num)
theorem B4730957 : Blo 1867635 4730957 := bbase (se 3 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 4730957 = 1774109) (by norm_num)
theorem B2101333 : Blo 1867635 2101333 := bbase (se 8 (by rfl) ⟨12312, by rfl⟩ : syracuseStep 2101333 = 24625) (by norm_num)
theorem B1994869 : Blo 1867635 1994869 := bbase (se 5 (by rfl) ⟨93509, by rfl⟩ : syracuseStep 1994869 = 187019) (by norm_num)
theorem B2101369 : Blo 1867635 2101369 := bbase (se 2 (by rfl) ⟨788013, by rfl⟩ : syracuseStep 2101369 = 1576027) (by norm_num)
theorem B8982677 : Blo 1867635 8982677 := bbase (se 6 (by rfl) ⟨210531, by rfl⟩ : syracuseStep 8982677 = 421063) (by norm_num)
theorem B2101405 : Blo 1867635 2101405 := bbase (se 3 (by rfl) ⟨394013, by rfl⟩ : syracuseStep 2101405 = 788027) (by norm_num)
theorem B7983269 : Blo 1867635 7983269 := bbase (se 4 (by rfl) ⟨748431, by rfl⟩ : syracuseStep 7983269 = 1496863) (by norm_num)
theorem B4796581 : Blo 1867635 4796581 := bbase (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) (by norm_num)
theorem B5681333 : Blo 1867635 5681333 := bbase (se 5 (by rfl) ⟨266312, by rfl⟩ : syracuseStep 5681333 = 532625) (by norm_num)
theorem B2101441 : Blo 1867635 2101441 := bbase (se 2 (by rfl) ⟨788040, by rfl⟩ : syracuseStep 2101441 = 1576081) (by norm_num)
theorem B2101477 : Blo 1867635 2101477 := bbase (se 4 (by rfl) ⟨197013, by rfl⟩ : syracuseStep 2101477 = 394027) (by norm_num)
theorem B2101513 : Blo 1867635 2101513 := bbase (se 2 (by rfl) ⟨788067, by rfl⟩ : syracuseStep 2101513 = 1576135) (by norm_num)
theorem B4731149 : Blo 1867635 4731149 := bbase (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) (by norm_num)
theorem B2101549 : Blo 1867635 2101549 := bbase (se 3 (by rfl) ⟨394040, by rfl⟩ : syracuseStep 2101549 = 788081) (by norm_num)
theorem B2101585 : Blo 1867635 2101585 := bbase (se 2 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 2101585 = 1576189) (by norm_num)
theorem B2363737 : Blo 1867635 2363737 := bbase (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) (by norm_num)
theorem B2396521 : Blo 1867635 2396521 := bbase (se 2 (by rfl) ⟨898695, by rfl⟩ : syracuseStep 2396521 = 1797391) (by norm_num)
theorem B1995121 : Blo 1867635 1995121 := bbase (se 2 (by rfl) ⟨748170, by rfl⟩ : syracuseStep 1995121 = 1496341) (by norm_num)
theorem B2101621 : Blo 1867635 2101621 := bbase (se 5 (by rfl) ⟨98513, by rfl⟩ : syracuseStep 2101621 = 197027) (by norm_num)
theorem B1995125 : Blo 1867635 1995125 := bbase (se 5 (by rfl) ⟨93521, by rfl⟩ : syracuseStep 1995125 = 187043) (by norm_num)
theorem B2101657 : Blo 1867635 2101657 := bbase (se 2 (by rfl) ⟨788121, by rfl⟩ : syracuseStep 2101657 = 1576243) (by norm_num)
theorem B2363833 : Blo 1867635 2363833 := bbase (se 2 (by rfl) ⟨886437, by rfl⟩ : syracuseStep 2363833 = 1772875) (by norm_num)
theorem B2101693 : Blo 1867635 2101693 := bbase (se 3 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 2101693 = 788135) (by norm_num)
theorem B2101729 : Blo 1867635 2101729 := bbase (se 2 (by rfl) ⟨788148, by rfl⟩ : syracuseStep 2101729 = 1576297) (by norm_num)
theorem B6304229 : Blo 1867635 6304229 := bbase (se 4 (by rfl) ⟨591021, by rfl⟩ : syracuseStep 6304229 = 1182043) (by norm_num)
theorem B2994661 : Blo 1867635 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B15159797 : Blo 1867635 15159797 := bbase (se 5 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 15159797 = 1421231) (by norm_num)
theorem B2101765 : Blo 1867635 2101765 := bbase (se 4 (by rfl) ⟨197040, by rfl⟩ : syracuseStep 2101765 = 394081) (by norm_num)
theorem B2101801 : Blo 1867635 2101801 := bbase (se 2 (by rfl) ⟨788175, by rfl⟩ : syracuseStep 2101801 = 1576351) (by norm_num)
theorem B2101837 : Blo 1867635 2101837 := bbase (se 3 (by rfl) ⟨394094, by rfl⟩ : syracuseStep 2101837 = 788189) (by norm_num)
theorem B2364005 : Blo 1867635 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B4731493 : Blo 1867635 4731493 := bbase (se 4 (by rfl) ⟨443577, by rfl⟩ : syracuseStep 4731493 = 887155) (by norm_num)
theorem B2101873 : Blo 1867635 2101873 := bbase (se 2 (by rfl) ⟨788202, by rfl⟩ : syracuseStep 2101873 = 1576405) (by norm_num)
theorem B3789437 : Blo 1867635 3789437 := bbase (se 3 (by rfl) ⟨710519, by rfl⟩ : syracuseStep 3789437 = 1421039) (by norm_num)
theorem B2101909 : Blo 1867635 2101909 := bbase (se 6 (by rfl) ⟨49263, by rfl⟩ : syracuseStep 2101909 = 98527) (by norm_num)
theorem B2364061 : Blo 1867635 2364061 := bbase (se 3 (by rfl) ⟨443261, by rfl⟩ : syracuseStep 2364061 = 886523) (by norm_num)
theorem B2101945 : Blo 1867635 2101945 := bbase (se 2 (by rfl) ⟨788229, by rfl⟩ : syracuseStep 2101945 = 1576459) (by norm_num)
theorem B5984965 : Blo 1867635 5984965 := bbase (se 4 (by rfl) ⟨561090, by rfl⟩ : syracuseStep 5984965 = 1122181) (by norm_num)
theorem B4731605 : Blo 1867635 4731605 := bbase (se 7 (by rfl) ⟨55448, by rfl⟩ : syracuseStep 4731605 = 110897) (by norm_num)
theorem B2101981 : Blo 1867635 2101981 := bbase (se 3 (by rfl) ⟨394121, by rfl⟩ : syracuseStep 2101981 = 788243) (by norm_num)
theorem B2364157 : Blo 1867635 2364157 := bbase (se 3 (by rfl) ⟨443279, by rfl⟩ : syracuseStep 2364157 = 886559) (by norm_num)
theorem B2102017 : Blo 1867635 2102017 := bbase (se 2 (by rfl) ⟨788256, by rfl⟩ : syracuseStep 2102017 = 1576513) (by norm_num)
theorem B21279509 : Blo 1867635 21279509 := bbase (se 6 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 21279509 = 997477) (by norm_num)
theorem B8975141 : Blo 1867635 8975141 := bbase (se 4 (by rfl) ⟨841419, by rfl⟩ : syracuseStep 8975141 = 1682839) (by norm_num)
theorem B2102053 : Blo 1867635 2102053 := bbase (se 4 (by rfl) ⟨197067, by rfl⟩ : syracuseStep 2102053 = 394135) (by norm_num)
theorem B2077489 : Blo 1867635 2077489 := bbase (se 2 (by rfl) ⟨779058, by rfl⟩ : syracuseStep 2077489 = 1558117) (by norm_num)
theorem B2102089 : Blo 1867635 2102089 := bbase (se 2 (by rfl) ⟨788283, by rfl⟩ : syracuseStep 2102089 = 1576567) (by norm_num)
theorem B2102125 : Blo 1867635 2102125 := bbase (se 3 (by rfl) ⟨394148, by rfl⟩ : syracuseStep 2102125 = 788297) (by norm_num)
theorem B2102161 : Blo 1867635 2102161 := bbase (se 2 (by rfl) ⟨788310, by rfl⟩ : syracuseStep 2102161 = 1576621) (by norm_num)
theorem B6304661 : Blo 1867635 6304661 := bbase (se 6 (by rfl) ⟨147765, by rfl⟩ : syracuseStep 6304661 = 295531) (by norm_num)
theorem B4731797 : Blo 1867635 4731797 := bbase (se 6 (by rfl) ⟨110901, by rfl⟩ : syracuseStep 4731797 = 221803) (by norm_num)
theorem B2364329 : Blo 1867635 2364329 := bbase (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) (by norm_num)
theorem B1995689 : Blo 1867635 1995689 := bbase (se 2 (by rfl) ⟨748383, by rfl⟩ : syracuseStep 1995689 = 1496767) (by norm_num)
theorem B2102197 : Blo 1867635 2102197 := bbase (se 5 (by rfl) ⟨98540, by rfl⟩ : syracuseStep 2102197 = 197081) (by norm_num)
theorem B2102233 : Blo 1867635 2102233 := bbase (se 2 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 2102233 = 1576675) (by norm_num)
theorem B2364385 : Blo 1867635 2364385 := bbase (se 2 (by rfl) ⟨886644, by rfl⟩ : syracuseStep 2364385 = 1773289) (by norm_num)
theorem B2102269 : Blo 1867635 2102269 := bbase (se 3 (by rfl) ⟨394175, by rfl⟩ : syracuseStep 2102269 = 788351) (by norm_num)
theorem B3789821 : Blo 1867635 3789821 := bbase (se 3 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 3789821 = 1421183) (by norm_num)
theorem B9458693 : Blo 1867635 9458693 := bbase (se 4 (by rfl) ⟨886752, by rfl⟩ : syracuseStep 9458693 = 1773505) (by norm_num)
theorem B2307089 : Blo 1867635 2307089 := bbase (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) (by norm_num)
theorem B2102305 : Blo 1867635 2102305 := bbase (se 2 (by rfl) ⟨788364, by rfl⟩ : syracuseStep 2102305 = 1576729) (by norm_num)
theorem B2364481 : Blo 1867635 2364481 := bbase (se 2 (by rfl) ⟨886680, by rfl⟩ : syracuseStep 2364481 = 1773361) (by norm_num)
theorem B2102341 : Blo 1867635 2102341 := bbase (se 4 (by rfl) ⟨197094, by rfl⟩ : syracuseStep 2102341 = 394189) (by norm_num)
theorem B1995877 : Blo 1867635 1995877 := bbase (se 4 (by rfl) ⟨187113, by rfl⟩ : syracuseStep 1995877 = 374227) (by norm_num)
theorem B2102377 : Blo 1867635 2102377 := bbase (se 2 (by rfl) ⟨788391, by rfl⟩ : syracuseStep 2102377 = 1576783) (by norm_num)
theorem B7091333 : Blo 1867635 7091333 := bbase (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) (by norm_num)
theorem B2102413 : Blo 1867635 2102413 := bbase (se 3 (by rfl) ⟨394202, by rfl⟩ : syracuseStep 2102413 = 788405) (by norm_num)
theorem B2102449 : Blo 1867635 2102449 := bbase (se 2 (by rfl) ⟨788418, by rfl⟩ : syracuseStep 2102449 = 1576837) (by norm_num)
theorem B17953973 : Blo 1867635 17953973 := bbase (se 5 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 17953973 = 1683185) (by norm_num)
theorem B2102485 : Blo 1867635 2102485 := bbase (se 7 (by rfl) ⟨24638, by rfl⟩ : syracuseStep 2102485 = 49277) (by norm_num)
theorem B6477029 : Blo 1867635 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B2364653 : Blo 1867635 2364653 := bbase (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) (by norm_num)
theorem B4732141 : Blo 1867635 4732141 := bbase (se 3 (by rfl) ⟨887276, by rfl⟩ : syracuseStep 4732141 = 1774553) (by norm_num)
theorem B2102521 : Blo 1867635 2102521 := bbase (se 2 (by rfl) ⟨788445, by rfl⟩ : syracuseStep 2102521 = 1576891) (by norm_num)
theorem B2102557 : Blo 1867635 2102557 := bbase (se 3 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 2102557 = 788459) (by norm_num)
theorem B2364709 : Blo 1867635 2364709 := bbase (se 4 (by rfl) ⟨221691, by rfl⟩ : syracuseStep 2364709 = 443383) (by norm_num)
theorem B2102593 : Blo 1867635 2102593 := bbase (se 2 (by rfl) ⟨788472, by rfl⟩ : syracuseStep 2102593 = 1576945) (by norm_num)
theorem B6305093 : Blo 1867635 6305093 := bbase (se 4 (by rfl) ⟨591102, by rfl⟩ : syracuseStep 6305093 = 1182205) (by norm_num)
theorem B4732253 : Blo 1867635 4732253 := bbase (se 3 (by rfl) ⟨887297, by rfl⟩ : syracuseStep 4732253 = 1774595) (by norm_num)
theorem B2102629 : Blo 1867635 2102629 := bbase (se 4 (by rfl) ⟨197121, by rfl⟩ : syracuseStep 2102629 = 394243) (by norm_num)
theorem B9721205 : Blo 1867635 9721205 := bbase (se 5 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 9721205 = 911363) (by norm_num)
theorem B2364805 : Blo 1867635 2364805 := bbase (se 4 (by rfl) ⟨221700, by rfl⟩ : syracuseStep 2364805 = 443401) (by norm_num)
theorem B2102665 : Blo 1867635 2102665 := bbase (se 2 (by rfl) ⟨788499, by rfl⟩ : syracuseStep 2102665 = 1576999) (by norm_num)
theorem B7091621 : Blo 1867635 7091621 := bbase (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) (by norm_num)
theorem B2102701 : Blo 1867635 2102701 := bbase (se 3 (by rfl) ⟨394256, by rfl⟩ : syracuseStep 2102701 = 788513) (by norm_num)
theorem B2102737 : Blo 1867635 2102737 := bbase (se 2 (by rfl) ⟨788526, by rfl⟩ : syracuseStep 2102737 = 1577053) (by norm_num)
theorem B2102773 : Blo 1867635 2102773 := bbase (se 5 (by rfl) ⟨98567, by rfl⟩ : syracuseStep 2102773 = 197135) (by norm_num)
theorem B6477317 : Blo 1867635 6477317 := bbase (se 4 (by rfl) ⟨607248, by rfl⟩ : syracuseStep 6477317 = 1214497) (by norm_num)
theorem B8975893 : Blo 1867635 8975893 := bbase (se 6 (by rfl) ⟨210372, by rfl⟩ : syracuseStep 8975893 = 420745) (by norm_num)
theorem B2102809 : Blo 1867635 2102809 := bbase (se 2 (by rfl) ⟨788553, by rfl⟩ : syracuseStep 2102809 = 1577107) (by norm_num)
theorem B4732445 : Blo 1867635 4732445 := bbase (se 3 (by rfl) ⟨887333, by rfl⟩ : syracuseStep 4732445 = 1774667) (by norm_num)
theorem B2364977 : Blo 1867635 2364977 := bbase (se 2 (by rfl) ⟨886866, by rfl⟩ : syracuseStep 2364977 = 1773733) (by norm_num)
theorem B5322293 : Blo 1867635 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B2102845 : Blo 1867635 2102845 := bbase (se 3 (by rfl) ⟨394283, by rfl⟩ : syracuseStep 2102845 = 788567) (by norm_num)
theorem B40416853 : Blo 1867635 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B2102881 : Blo 1867635 2102881 := bbase (se 2 (by rfl) ⟨788580, by rfl⟩ : syracuseStep 2102881 = 1577161) (by norm_num)
theorem B2365033 : Blo 1867635 2365033 := bbase (se 2 (by rfl) ⟨886887, by rfl⟩ : syracuseStep 2365033 = 1773775) (by norm_num)
theorem B2102917 : Blo 1867635 2102917 := bbase (se 4 (by rfl) ⟨197148, by rfl⟩ : syracuseStep 2102917 = 394297) (by norm_num)
theorem B2102953 : Blo 1867635 2102953 := bbase (se 2 (by rfl) ⟨788607, by rfl⟩ : syracuseStep 2102953 = 1577215) (by norm_num)
theorem B11368117 : Blo 1867635 11368117 := bbase (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) (by norm_num)
theorem B10106549 : Blo 1867635 10106549 := bbase (se 5 (by rfl) ⟨473744, by rfl⟩ : syracuseStep 10106549 = 947489) (by norm_num)
theorem B2365129 : Blo 1867635 2365129 := bbase (se 2 (by rfl) ⟨886923, by rfl⟩ : syracuseStep 2365129 = 1773847) (by norm_num)
theorem B2102989 : Blo 1867635 2102989 := bbase (se 3 (by rfl) ⟨394310, by rfl⟩ : syracuseStep 2102989 = 788621) (by norm_num)
theorem B2660053 : Blo 1867635 2660053 := bbase (se 7 (by rfl) ⟨31172, by rfl⟩ : syracuseStep 2660053 = 62345) (by norm_num)
theorem B2103025 : Blo 1867635 2103025 := bbase (se 2 (by rfl) ⟨788634, by rfl⟩ : syracuseStep 2103025 = 1577269) (by norm_num)
theorem B6305525 : Blo 1867635 6305525 := bbase (se 5 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 6305525 = 591143) (by norm_num)
theorem B2103061 : Blo 1867635 2103061 := bbase (se 6 (by rfl) ⟨49290, by rfl⟩ : syracuseStep 2103061 = 98581) (by norm_num)
theorem B3151669 : Blo 1867635 3151669 := bbase (se 5 (by rfl) ⟨147734, by rfl⟩ : syracuseStep 3151669 = 295469) (by norm_num)
theorem B2103097 : Blo 1867635 2103097 := bbase (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) (by norm_num)
theorem B2103133 : Blo 1867635 2103133 := bbase (se 3 (by rfl) ⟨394337, by rfl⟩ : syracuseStep 2103133 = 788675) (by norm_num)
theorem B2840437 : Blo 1867635 2840437 := bbase (se 5 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 2840437 = 266291) (by norm_num)
theorem B2365301 : Blo 1867635 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B2103169 : Blo 1867635 2103169 := bbase (se 2 (by rfl) ⟨788688, by rfl⟩ : syracuseStep 2103169 = 1577377) (by norm_num)
theorem B3151757 : Blo 1867635 3151757 := bbase (se 3 (by rfl) ⟨590954, by rfl⟩ : syracuseStep 3151757 = 1181909) (by norm_num)
theorem B2398097 : Blo 1867635 2398097 := bbase (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) (by norm_num)
theorem B2103205 : Blo 1867635 2103205 := bbase (se 4 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 2103205 = 394351) (by norm_num)
theorem B2365357 : Blo 1867635 2365357 := bbase (se 3 (by rfl) ⟨443504, by rfl⟩ : syracuseStep 2365357 = 887009) (by norm_num)
theorem B2103241 : Blo 1867635 2103241 := bbase (se 2 (by rfl) ⟨788715, by rfl⟩ : syracuseStep 2103241 = 1577431) (by norm_num)
theorem B2398189 : Blo 1867635 2398189 := bbase (se 3 (by rfl) ⟨449660, by rfl⟩ : syracuseStep 2398189 = 899321) (by norm_num)
theorem B2103277 : Blo 1867635 2103277 := bbase (se 3 (by rfl) ⟨394364, by rfl⟩ : syracuseStep 2103277 = 788729) (by norm_num)
theorem B11974645 : Blo 1867635 11974645 := bbase (se 5 (by rfl) ⟨561311, by rfl⟩ : syracuseStep 11974645 = 1122623) (by norm_num)
theorem B3151885 : Blo 1867635 3151885 := bbase (se 3 (by rfl) ⟨590978, by rfl⟩ : syracuseStep 3151885 = 1181957) (by norm_num)
theorem B2365453 : Blo 1867635 2365453 := bbase (se 3 (by rfl) ⟨443522, by rfl⟩ : syracuseStep 2365453 = 887045) (by norm_num)
theorem B2103313 : Blo 1867635 2103313 := bbase (se 2 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 2103313 = 1577485) (by norm_num)
theorem B5986325 : Blo 1867635 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B3151973 : Blo 1867635 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B2840741 : Blo 1867635 2840741 := bbase (se 4 (by rfl) ⟨266319, by rfl⟩ : syracuseStep 2840741 = 532639) (by norm_num)
theorem B6305957 : Blo 1867635 6305957 := bbase (se 4 (by rfl) ⟨591183, by rfl⟩ : syracuseStep 6305957 = 1182367) (by norm_num)
theorem B2463925 : Blo 1867635 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B2365625 : Blo 1867635 2365625 := bbase (se 2 (by rfl) ⟨887109, by rfl⟩ : syracuseStep 2365625 = 1774219) (by norm_num)
theorem B3152101 : Blo 1867635 3152101 := bbase (se 4 (by rfl) ⟨295509, by rfl⟩ : syracuseStep 3152101 = 591019) (by norm_num)
theorem B4045037 : Blo 1867635 4045037 := bbase (se 3 (by rfl) ⟨758444, by rfl⟩ : syracuseStep 4045037 = 1516889) (by norm_num)
theorem B2365681 : Blo 1867635 2365681 := bbase (se 2 (by rfl) ⟨887130, by rfl⟩ : syracuseStep 2365681 = 1774261) (by norm_num)
theorem B9459989 : Blo 1867635 9459989 := bbase (se 6 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 9459989 = 443437) (by norm_num)
theorem B2660645 : Blo 1867635 2660645 := bbase (se 4 (by rfl) ⟨249435, by rfl⟩ : syracuseStep 2660645 = 498871) (by norm_num)
theorem B3152189 : Blo 1867635 3152189 := bbase (se 3 (by rfl) ⟨591035, by rfl⟩ : syracuseStep 3152189 = 1182071) (by norm_num)
theorem B4438349 : Blo 1867635 4438349 := bbase (se 3 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 4438349 = 1664381) (by norm_num)
theorem B2365777 : Blo 1867635 2365777 := bbase (se 2 (by rfl) ⟨887166, by rfl⟩ : syracuseStep 2365777 = 1774333) (by norm_num)
theorem B2660725 : Blo 1867635 2660725 := bbase (se 5 (by rfl) ⟨124721, by rfl⟩ : syracuseStep 2660725 = 249443) (by norm_num)
theorem B7985557 : Blo 1867635 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B3152317 : Blo 1867635 3152317 := bbase (se 3 (by rfl) ⟨591059, by rfl⟩ : syracuseStep 3152317 = 1182119) (by norm_num)
theorem B2660845 : Blo 1867635 2660845 := bbase (se 3 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 2660845 = 997817) (by norm_num)
theorem B2365949 : Blo 1867635 2365949 := bbase (se 3 (by rfl) ⟨443615, by rfl⟩ : syracuseStep 2365949 = 887231) (by norm_num)
theorem B3152405 : Blo 1867635 3152405 := bbase (se 6 (by rfl) ⟨73884, by rfl⟩ : syracuseStep 3152405 = 147769) (by norm_num)
theorem B7576085 : Blo 1867635 7576085 := bbase (se 6 (by rfl) ⟨177564, by rfl⟩ : syracuseStep 7576085 = 355129) (by norm_num)
theorem B4487717 : Blo 1867635 4487717 := bbase (se 4 (by rfl) ⟨420723, by rfl⟩ : syracuseStep 4487717 = 841447) (by norm_num)
theorem B2366005 : Blo 1867635 2366005 := bbase (se 5 (by rfl) ⟨110906, by rfl⟩ : syracuseStep 2366005 = 221813) (by norm_num)
theorem B3693125 : Blo 1867635 3693125 := bbase (se 4 (by rfl) ⟨346230, by rfl⟩ : syracuseStep 3693125 = 692461) (by norm_num)
theorem B7092805 : Blo 1867635 7092805 := bbase (se 4 (by rfl) ⟨664950, by rfl⟩ : syracuseStep 7092805 = 1329901) (by norm_num)
theorem B2660941 : Blo 1867635 2660941 := bbase (se 3 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 2660941 = 997853) (by norm_num)
theorem B6306389 : Blo 1867635 6306389 := bbase (se 8 (by rfl) ⟨36951, by rfl⟩ : syracuseStep 6306389 = 73903) (by norm_num)
theorem B2079325 : Blo 1867635 2079325 := bbase (se 3 (by rfl) ⟨389873, by rfl⟩ : syracuseStep 2079325 = 779747) (by norm_num)
theorem B4553317 : Blo 1867635 4553317 := bbase (se 4 (by rfl) ⟨426873, by rfl⟩ : syracuseStep 4553317 = 853747) (by norm_num)
theorem B3152533 : Blo 1867635 3152533 := bbase (se 6 (by rfl) ⟨73887, by rfl⟩ : syracuseStep 3152533 = 147775) (by norm_num)
theorem B2366101 : Blo 1867635 2366101 := bbase (se 6 (by rfl) ⟨55455, by rfl⟩ : syracuseStep 2366101 = 110911) (by norm_num)
theorem B3545765 : Blo 1867635 3545765 := bbase (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) (by norm_num)
theorem B5323477 : Blo 1867635 5323477 := bbase (se 7 (by rfl) ⟨62384, by rfl⟩ : syracuseStep 5323477 = 124769) (by norm_num)
theorem B3152621 : Blo 1867635 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B3365621 : Blo 1867635 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B2841445 : Blo 1867635 2841445 := bbase (se 4 (by rfl) ⟨266385, by rfl⟩ : syracuseStep 2841445 = 532771) (by norm_num)
theorem B3152749 : Blo 1867635 3152749 := bbase (se 3 (by rfl) ⟨591140, by rfl⟩ : syracuseStep 3152749 = 1182281) (by norm_num)
theorem B7093109 : Blo 1867635 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B14195573 : Blo 1867635 14195573 := bbase (se 5 (by rfl) ⟨665417, by rfl⟩ : syracuseStep 14195573 = 1330835) (by norm_num)
theorem B5323637 : Blo 1867635 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B12131221 : Blo 1867635 12131221 := bbase (se 6 (by rfl) ⟨284325, by rfl⟩ : syracuseStep 12131221 = 568651) (by norm_num)
theorem B4488101 : Blo 1867635 4488101 := bbase (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) (by norm_num)
theorem B3595189 : Blo 1867635 3595189 := bbase (se 5 (by rfl) ⟨168524, by rfl⟩ : syracuseStep 3595189 = 337049) (by norm_num)
theorem B3152837 : Blo 1867635 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B68189141 : Blo 1867635 68189141 := bbase (se 7 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 68189141 = 1598183) (by norm_num)
theorem B6306821 : Blo 1867635 6306821 := bbase (se 4 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 6306821 = 1182529) (by norm_num)
theorem B2661437 : Blo 1867635 2661437 := bbase (se 3 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 2661437 = 998039) (by norm_num)
theorem B3152965 : Blo 1867635 3152965 := bbase (se 4 (by rfl) ⟨295590, by rfl⟩ : syracuseStep 3152965 = 591181) (by norm_num)
theorem B5323877 : Blo 1867635 5323877 := bbase (se 4 (by rfl) ⟨499113, by rfl⟩ : syracuseStep 5323877 = 998227) (by norm_num)
theorem B4488301 : Blo 1867635 4488301 := bbase (se 3 (by rfl) ⟨841556, by rfl⟩ : syracuseStep 4488301 = 1683113) (by norm_num)
theorem B3153053 : Blo 1867635 3153053 := bbase (se 3 (by rfl) ⟨591197, by rfl⟩ : syracuseStep 3153053 = 1182395) (by norm_num)
theorem B13474997 : Blo 1867635 13474997 := bbase (se 5 (by rfl) ⟨631640, by rfl⟩ : syracuseStep 13474997 = 1263281) (by norm_num)
theorem B14187797 : Blo 1867635 14187797 := bbase (se 6 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 14187797 = 665053) (by norm_num)
theorem B3153181 : Blo 1867635 3153181 := bbase (se 3 (by rfl) ⟨591221, by rfl⟩ : syracuseStep 3153181 = 1182443) (by norm_num)
theorem B5324069 : Blo 1867635 5324069 := bbase (se 4 (by rfl) ⟨499131, by rfl⟩ : syracuseStep 5324069 = 998263) (by norm_num)
theorem B3153269 : Blo 1867635 3153269 := bbase (se 5 (by rfl) ⟨147809, by rfl⟩ : syracuseStep 3153269 = 295619) (by norm_num)
theorem B3546517 : Blo 1867635 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B3988901 : Blo 1867635 3988901 := bbase (se 4 (by rfl) ⟨373959, by rfl⟩ : syracuseStep 3988901 = 747919) (by norm_num)
theorem B6307253 : Blo 1867635 6307253 := bbase (se 5 (by rfl) ⟨295652, by rfl⟩ : syracuseStep 6307253 = 591305) (by norm_num)
theorem B3153397 : Blo 1867635 3153397 := bbase (se 5 (by rfl) ⟨147815, by rfl⟩ : syracuseStep 3153397 = 295631) (by norm_num)
theorem B3546661 : Blo 1867635 3546661 := bbase (se 4 (by rfl) ⟨332499, by rfl⟩ : syracuseStep 3546661 = 664999) (by norm_num)
theorem B9461285 : Blo 1867635 9461285 := bbase (se 4 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 9461285 = 1773991) (by norm_num)
theorem B3153485 : Blo 1867635 3153485 := bbase (se 3 (by rfl) ⟨591278, by rfl⟩ : syracuseStep 3153485 = 1182557) (by norm_num)
theorem B2661989 : Blo 1867635 2661989 := bbase (se 4 (by rfl) ⟨249561, by rfl⟩ : syracuseStep 2661989 = 499123) (by norm_num)
theorem B10641077 : Blo 1867635 10641077 := bbase (se 5 (by rfl) ⟨498800, by rfl⟩ : syracuseStep 10641077 = 997601) (by norm_num)
theorem B3546821 : Blo 1867635 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B4202189 : Blo 1867635 4202189 := bbase (se 3 (by rfl) ⟨787910, by rfl⟩ : syracuseStep 4202189 = 1575821) (by norm_num)
theorem B3153613 : Blo 1867635 3153613 := bbase (se 3 (by rfl) ⟨591302, by rfl⟩ : syracuseStep 3153613 = 1182605) (by norm_num)
theorem B7577317 : Blo 1867635 7577317 := bbase (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) (by norm_num)
theorem B4202261 : Blo 1867635 4202261 := bbase (se 6 (by rfl) ⟨98490, by rfl⟩ : syracuseStep 4202261 = 196981) (by norm_num)
theorem B3153701 : Blo 1867635 3153701 := bbase (se 4 (by rfl) ⟨295659, by rfl⟩ : syracuseStep 3153701 = 591319) (by norm_num)
theorem B2801453 : Blo 1867635 2801453 := bbase (se 3 (by rfl) ⟨525272, by rfl⟩ : syracuseStep 2801453 = 1050545) (by norm_num)
theorem B2801477 : Blo 1867635 2801477 := bbase (se 4 (by rfl) ⟨262638, by rfl⟩ : syracuseStep 2801477 = 525277) (by norm_num)
theorem B3546965 : Blo 1867635 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B2801501 : Blo 1867635 2801501 := bbase (se 3 (by rfl) ⟨525281, by rfl⟩ : syracuseStep 2801501 = 1050563) (by norm_num)
theorem B4202333 : Blo 1867635 4202333 := bbase (se 3 (by rfl) ⟨787937, by rfl⟩ : syracuseStep 4202333 = 1575875) (by norm_num)
theorem B2244449 : Blo 1867635 2244449 := bbase (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) (by norm_num)
theorem B6307685 : Blo 1867635 6307685 := bbase (se 4 (by rfl) ⟨591345, by rfl⟩ : syracuseStep 6307685 = 1182691) (by norm_num)
theorem B2801525 : Blo 1867635 2801525 := bbase (se 5 (by rfl) ⟨131321, by rfl⟩ : syracuseStep 2801525 = 262643) (by norm_num)
theorem B2801549 : Blo 1867635 2801549 := bbase (se 3 (by rfl) ⟨525290, by rfl⟩ : syracuseStep 2801549 = 1050581) (by norm_num)
theorem B2801573 : Blo 1867635 2801573 := bbase (se 4 (by rfl) ⟨262647, by rfl⟩ : syracuseStep 2801573 = 525295) (by norm_num)
theorem B4202405 : Blo 1867635 4202405 := bbase (se 4 (by rfl) ⟨393975, by rfl⟩ : syracuseStep 4202405 = 787951) (by norm_num)
theorem B3153829 : Blo 1867635 3153829 := bbase (se 4 (by rfl) ⟨295671, by rfl⟩ : syracuseStep 3153829 = 591343) (by norm_num)
theorem B2842541 : Blo 1867635 2842541 := bbase (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) (by norm_num)
theorem B2801597 : Blo 1867635 2801597 := bbase (se 3 (by rfl) ⟨525299, by rfl⟩ : syracuseStep 2801597 = 1050599) (by norm_num)
theorem B2801621 : Blo 1867635 2801621 := bbase (se 7 (by rfl) ⟨32831, by rfl⟩ : syracuseStep 2801621 = 65663) (by norm_num)
theorem B2801645 : Blo 1867635 2801645 := bbase (se 3 (by rfl) ⟨525308, by rfl⟩ : syracuseStep 2801645 = 1050617) (by norm_num)
theorem B4202477 : Blo 1867635 4202477 := bbase (se 3 (by rfl) ⟨787964, by rfl⟩ : syracuseStep 4202477 = 1575929) (by norm_num)
theorem B3153917 : Blo 1867635 3153917 := bbase (se 3 (by rfl) ⟨591359, by rfl⟩ : syracuseStep 3153917 = 1182719) (by norm_num)
theorem B1867779 : Blo 1867635 1867779 := bstep (se 1 (by rfl) ⟨1400834, by rfl⟩ : syracuseStep 1867779 = 2801669) B2801669
theorem B4202513 : Blo 1867635 4202513 := bstep (se 2 (by rfl) ⟨1575942, by rfl⟩ : syracuseStep 4202513 = 3151885) B3151885
theorem B2801681 : Blo 1867635 2801681 := bstep (se 2 (by rfl) ⟨1050630, by rfl⟩ : syracuseStep 2801681 = 2101261) B2101261
theorem B1867795 : Blo 1867635 1867795 := bstep (se 1 (by rfl) ⟨1400846, by rfl⟩ : syracuseStep 1867795 = 2801693) B2801693
theorem B3153937 : Blo 1867635 3153937 := bstep (se 2 (by rfl) ⟨1182726, by rfl⟩ : syracuseStep 3153937 = 2365453) B2365453
theorem B4202531 : Blo 1867635 4202531 := bstep (se 1 (by rfl) ⟨3151898, by rfl⟩ : syracuseStep 4202531 = 6303797) B6303797
theorem B2801699 : Blo 1867635 2801699 := bstep (se 1 (by rfl) ⟨2101274, by rfl⟩ : syracuseStep 2801699 = 4202549) B4202549
theorem B1867811 : Blo 1867635 1867811 := bstep (se 1 (by rfl) ⟨1400858, by rfl⟩ : syracuseStep 1867811 = 2801717) B2801717
theorem B6152237 : Blo 1867635 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B5988401 : Blo 1867635 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B1867827 : Blo 1867635 1867827 := bstep (se 1 (by rfl) ⟨1400870, by rfl⟩ : syracuseStep 1867827 = 2801741) B2801741
theorem B3153971 : Blo 1867635 3153971 := bstep (se 1 (by rfl) ⟨2365478, by rfl⟩ : syracuseStep 3153971 = 4730957) B4730957
theorem B2801729 : Blo 1867635 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B1867843 : Blo 1867635 1867843 := bstep (se 1 (by rfl) ⟨1400882, by rfl⟩ : syracuseStep 1867843 = 2801765) B2801765
theorem B2801747 : Blo 1867635 2801747 := bstep (se 1 (by rfl) ⟨2101310, by rfl⟩ : syracuseStep 2801747 = 4202621) B4202621
theorem B1867859 : Blo 1867635 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B1867875 : Blo 1867635 1867875 := bstep (se 1 (by rfl) ⟨1400906, by rfl⟩ : syracuseStep 1867875 = 2801813) B2801813
theorem B5988451 : Blo 1867635 5988451 := bstep (se 1 (by rfl) ⟨4491338, by rfl⟩ : syracuseStep 5988451 = 8982677) B8982677
theorem B2801777 : Blo 1867635 2801777 := bstep (se 2 (by rfl) ⟨1050666, by rfl⟩ : syracuseStep 2801777 = 2101333) B2101333
theorem B1867891 : Blo 1867635 1867891 := bstep (se 1 (by rfl) ⟨1400918, by rfl⟩ : syracuseStep 1867891 = 2801837) B2801837
theorem B2801795 : Blo 1867635 2801795 := bstep (se 1 (by rfl) ⟨2101346, by rfl⟩ : syracuseStep 2801795 = 4202693) B4202693
theorem B1867907 : Blo 1867635 1867907 := bstep (se 1 (by rfl) ⟨1400930, by rfl⟩ : syracuseStep 1867907 = 2801861) B2801861
theorem B1867923 : Blo 1867635 1867923 := bstep (se 1 (by rfl) ⟨1400942, by rfl⟩ : syracuseStep 1867923 = 2801885) B2801885
theorem B2801825 : Blo 1867635 2801825 := bstep (se 2 (by rfl) ⟨1050684, by rfl⟩ : syracuseStep 2801825 = 2101369) B2101369
theorem B1867939 : Blo 1867635 1867939 := bstep (se 1 (by rfl) ⟨1400954, by rfl⟩ : syracuseStep 1867939 = 2801909) B2801909
theorem B2801843 : Blo 1867635 2801843 := bstep (se 1 (by rfl) ⟨2101382, by rfl⟩ : syracuseStep 2801843 = 4202765) B4202765
theorem B1867955 : Blo 1867635 1867955 := bstep (se 1 (by rfl) ⟨1400966, by rfl⟩ : syracuseStep 1867955 = 2801933) B2801933
theorem B3154099 : Blo 1867635 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B1867971 : Blo 1867635 1867971 := bstep (se 1 (by rfl) ⟨1400978, by rfl⟩ : syracuseStep 1867971 = 2801957) B2801957
theorem B2801873 : Blo 1867635 2801873 := bstep (se 2 (by rfl) ⟨1050702, by rfl⟩ : syracuseStep 2801873 = 2101405) B2101405
theorem B1867987 : Blo 1867635 1867987 := bstep (se 1 (by rfl) ⟨1400990, by rfl⟩ : syracuseStep 1867987 = 2801981) B2801981
theorem B2801891 : Blo 1867635 2801891 := bstep (se 1 (by rfl) ⟨2101418, by rfl⟩ : syracuseStep 2801891 = 4202837) B4202837
theorem B1868003 : Blo 1867635 1868003 := bstep (se 1 (by rfl) ⟨1401002, by rfl⟩ : syracuseStep 1868003 = 2802005) B2802005
theorem B3285233 : Blo 1867635 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B1868019 : Blo 1867635 1868019 := bstep (se 1 (by rfl) ⟨1401014, by rfl⟩ : syracuseStep 1868019 = 2802029) B2802029
theorem B2801921 : Blo 1867635 2801921 := bstep (se 2 (by rfl) ⟨1050720, by rfl⟩ : syracuseStep 2801921 = 2101441) B2101441
theorem B1868035 : Blo 1867635 1868035 := bstep (se 1 (by rfl) ⟨1401026, by rfl⟩ : syracuseStep 1868035 = 2802053) B2802053
theorem B2801939 : Blo 1867635 2801939 := bstep (se 1 (by rfl) ⟨2101454, by rfl⟩ : syracuseStep 2801939 = 4202909) B4202909
theorem B1868051 : Blo 1867635 1868051 := bstep (se 1 (by rfl) ⟨1401038, by rfl⟩ : syracuseStep 1868051 = 2802077) B2802077
theorem B1868067 : Blo 1867635 1868067 := bstep (se 1 (by rfl) ⟨1401050, by rfl⟩ : syracuseStep 1868067 = 2802101) B2802101
theorem B4202801 : Blo 1867635 4202801 := bstep (se 2 (by rfl) ⟨1576050, by rfl⟩ : syracuseStep 4202801 = 3152101) B3152101
theorem B2801969 : Blo 1867635 2801969 := bstep (se 2 (by rfl) ⟨1050738, by rfl⟩ : syracuseStep 2801969 = 2101477) B2101477
theorem B1868083 : Blo 1867635 1868083 := bstep (se 1 (by rfl) ⟨1401062, by rfl⟩ : syracuseStep 1868083 = 2802125) B2802125
theorem B3154241 : Blo 1867635 3154241 := bstep (se 2 (by rfl) ⟨1182840, by rfl⟩ : syracuseStep 3154241 = 2365681) B2365681
theorem B4202819 : Blo 1867635 4202819 := bstep (se 1 (by rfl) ⟨3152114, by rfl⟩ : syracuseStep 4202819 = 6304229) B6304229
theorem B2801987 : Blo 1867635 2801987 := bstep (se 1 (by rfl) ⟨2101490, by rfl⟩ : syracuseStep 2801987 = 4202981) B4202981
theorem B1868099 : Blo 1867635 1868099 := bstep (se 1 (by rfl) ⟨1401074, by rfl⟩ : syracuseStep 1868099 = 2802149) B2802149
theorem B1868115 : Blo 1867635 1868115 := bstep (se 1 (by rfl) ⟨1401086, by rfl⟩ : syracuseStep 1868115 = 2802173) B2802173
theorem B2802017 : Blo 1867635 2802017 := bstep (se 2 (by rfl) ⟨1050756, by rfl⟩ : syracuseStep 2802017 = 2101513) B2101513
theorem B1868131 : Blo 1867635 1868131 := bstep (se 1 (by rfl) ⟨1401098, by rfl⟩ : syracuseStep 1868131 = 2802197) B2802197
theorem B2802035 : Blo 1867635 2802035 := bstep (se 1 (by rfl) ⟨2101526, by rfl⟩ : syracuseStep 2802035 = 4203053) B4203053
theorem B1868147 : Blo 1867635 1868147 := bstep (se 1 (by rfl) ⟨1401110, by rfl⟩ : syracuseStep 1868147 = 2802221) B2802221
theorem B1868163 : Blo 1867635 1868163 := bstep (se 1 (by rfl) ⟨1401122, by rfl⟩ : syracuseStep 1868163 = 2802245) B2802245
theorem B2802065 : Blo 1867635 2802065 := bstep (se 2 (by rfl) ⟨1050774, by rfl⟩ : syracuseStep 2802065 = 2101549) B2101549
theorem B1868179 : Blo 1867635 1868179 := bstep (se 1 (by rfl) ⟨1401134, by rfl⟩ : syracuseStep 1868179 = 2802269) B2802269
theorem B2802083 : Blo 1867635 2802083 := bstep (se 1 (by rfl) ⟨2101562, by rfl⟩ : syracuseStep 2802083 = 4203125) B4203125
theorem B1868195 : Blo 1867635 1868195 := bstep (se 1 (by rfl) ⟨1401146, by rfl⟩ : syracuseStep 1868195 = 2802293) B2802293
theorem B3367345 : Blo 1867635 3367345 := bstep (se 2 (by rfl) ⟨1262754, by rfl⟩ : syracuseStep 3367345 = 2525509) B2525509
theorem B1868211 : Blo 1867635 1868211 := bstep (se 1 (by rfl) ⟨1401158, by rfl⟩ : syracuseStep 1868211 = 2802317) B2802317
theorem B2802113 : Blo 1867635 2802113 := bstep (se 2 (by rfl) ⟨1050792, by rfl⟩ : syracuseStep 2802113 = 2101585) B2101585
theorem B1868227 : Blo 1867635 1868227 := bstep (se 1 (by rfl) ⟨1401170, by rfl⟩ : syracuseStep 1868227 = 2802341) B2802341
theorem B3154369 : Blo 1867635 3154369 := bstep (se 2 (by rfl) ⟨1182888, by rfl⟩ : syracuseStep 3154369 = 2365777) B2365777
theorem B3989969 : Blo 1867635 3989969 := bstep (se 2 (by rfl) ⟨1496238, by rfl⟩ : syracuseStep 3989969 = 2992477) B2992477
theorem B2802131 : Blo 1867635 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B1868243 : Blo 1867635 1868243 := bstep (se 1 (by rfl) ⟨1401182, by rfl⟩ : syracuseStep 1868243 = 2802365) B2802365
theorem B3195361 : Blo 1867635 3195361 := bstep (se 2 (by rfl) ⟨1198260, by rfl⟩ : syracuseStep 3195361 = 2396521) B2396521
theorem B1868259 : Blo 1867635 1868259 := bstep (se 1 (by rfl) ⟨1401194, by rfl⟩ : syracuseStep 1868259 = 2802389) B2802389
theorem B3154403 : Blo 1867635 3154403 := bstep (se 1 (by rfl) ⟨2365802, by rfl⟩ : syracuseStep 3154403 = 4731605) B4731605
theorem B6308333 : Blo 1867635 6308333 := bstep (se 3 (by rfl) ⟨1182812, by rfl⟩ : syracuseStep 6308333 = 2365625) B2365625
theorem B2802161 : Blo 1867635 2802161 := bstep (se 2 (by rfl) ⟨1050810, by rfl⟩ : syracuseStep 2802161 = 2101621) B2101621
theorem B3547633 : Blo 1867635 3547633 := bstep (se 2 (by rfl) ⟨1330362, by rfl⟩ : syracuseStep 3547633 = 2660725) B2660725
theorem B1868275 : Blo 1867635 1868275 := bstep (se 1 (by rfl) ⟨1401206, by rfl⟩ : syracuseStep 1868275 = 2802413) B2802413
theorem B9462257 : Blo 1867635 9462257 := bstep (se 2 (by rfl) ⟨3548346, by rfl⟩ : syracuseStep 9462257 = 7096693) B7096693
theorem B2802179 : Blo 1867635 2802179 := bstep (se 1 (by rfl) ⟨2101634, by rfl⟩ : syracuseStep 2802179 = 4203269) B4203269
theorem B1868291 : Blo 1867635 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B1868307 : Blo 1867635 1868307 := bstep (se 1 (by rfl) ⟨1401230, by rfl⟩ : syracuseStep 1868307 = 2802461) B2802461
theorem B2802209 : Blo 1867635 2802209 := bstep (se 2 (by rfl) ⟨1050828, by rfl⟩ : syracuseStep 2802209 = 2101657) B2101657
theorem B1868323 : Blo 1867635 1868323 := bstep (se 1 (by rfl) ⟨1401242, by rfl⟩ : syracuseStep 1868323 = 2802485) B2802485
theorem B6308387 : Blo 1867635 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B2802227 : Blo 1867635 2802227 := bstep (se 1 (by rfl) ⟨2101670, by rfl⟩ : syracuseStep 2802227 = 4203341) B4203341
theorem B1868339 : Blo 1867635 1868339 := bstep (se 1 (by rfl) ⟨1401254, by rfl⟩ : syracuseStep 1868339 = 2802509) B2802509
theorem B1868355 : Blo 1867635 1868355 := bstep (se 1 (by rfl) ⟨1401266, by rfl⟩ : syracuseStep 1868355 = 2802533) B2802533
theorem B23937605 : Blo 1867635 23937605 := bstep (se 4 (by rfl) ⟨2244150, by rfl⟩ : syracuseStep 23937605 = 4488301) B4488301
theorem B4203089 : Blo 1867635 4203089 := bstep (se 2 (by rfl) ⟨1576158, by rfl⟩ : syracuseStep 4203089 = 3152317) B3152317
theorem B2802257 : Blo 1867635 2802257 := bstep (se 2 (by rfl) ⟨1050846, by rfl⟩ : syracuseStep 2802257 = 2101693) B2101693
theorem B1868371 : Blo 1867635 1868371 := bstep (se 1 (by rfl) ⟨1401278, by rfl⟩ : syracuseStep 1868371 = 2802557) B2802557
theorem B4203107 : Blo 1867635 4203107 := bstep (se 1 (by rfl) ⟨3152330, by rfl⟩ : syracuseStep 4203107 = 6304661) B6304661
theorem B2802275 : Blo 1867635 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B1868387 : Blo 1867635 1868387 := bstep (se 1 (by rfl) ⟨1401290, by rfl⟩ : syracuseStep 1868387 = 2802581) B2802581
theorem B3154531 : Blo 1867635 3154531 := bstep (se 1 (by rfl) ⟨2365898, by rfl⟩ : syracuseStep 3154531 = 4731797) B4731797
theorem B1868403 : Blo 1867635 1868403 := bstep (se 1 (by rfl) ⟨1401302, by rfl⟩ : syracuseStep 1868403 = 2802605) B2802605
theorem B2802305 : Blo 1867635 2802305 := bstep (se 2 (by rfl) ⟨1050864, by rfl⟩ : syracuseStep 2802305 = 2101729) B2101729
theorem B1868419 : Blo 1867635 1868419 := bstep (se 1 (by rfl) ⟨1401314, by rfl⟩ : syracuseStep 1868419 = 2802629) B2802629
theorem B3547793 : Blo 1867635 3547793 := bstep (se 2 (by rfl) ⟨1330422, by rfl⟩ : syracuseStep 3547793 = 2660845) B2660845
theorem B2802323 : Blo 1867635 2802323 := bstep (se 1 (by rfl) ⟨2101742, by rfl⟩ : syracuseStep 2802323 = 4203485) B4203485
theorem B1868435 : Blo 1867635 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B1868451 : Blo 1867635 1868451 := bstep (se 1 (by rfl) ⟨1401338, by rfl⟩ : syracuseStep 1868451 = 2802677) B2802677
theorem B2802353 : Blo 1867635 2802353 := bstep (se 2 (by rfl) ⟨1050882, by rfl⟩ : syracuseStep 2802353 = 2101765) B2101765
theorem B1868467 : Blo 1867635 1868467 := bstep (se 1 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 1868467 = 2802701) B2802701
theorem B2802371 : Blo 1867635 2802371 := bstep (se 1 (by rfl) ⟨2101778, by rfl⟩ : syracuseStep 2802371 = 4203557) B4203557
theorem B1868483 : Blo 1867635 1868483 := bstep (se 1 (by rfl) ⟨1401362, by rfl⟩ : syracuseStep 1868483 = 2802725) B2802725
theorem B1868499 : Blo 1867635 1868499 := bstep (se 1 (by rfl) ⟨1401374, by rfl⟩ : syracuseStep 1868499 = 2802749) B2802749
theorem B2802401 : Blo 1867635 2802401 := bstep (se 2 (by rfl) ⟨1050900, by rfl⟩ : syracuseStep 2802401 = 2101801) B2101801
theorem B1868515 : Blo 1867635 1868515 := bstep (se 1 (by rfl) ⟨1401386, by rfl⟩ : syracuseStep 1868515 = 2802773) B2802773
theorem B4489955 : Blo 1867635 4489955 := bstep (se 1 (by rfl) ⟨3367466, by rfl⟩ : syracuseStep 4489955 = 6734933) B6734933
theorem B3154673 : Blo 1867635 3154673 := bstep (se 2 (by rfl) ⟨1183002, by rfl⟩ : syracuseStep 3154673 = 2366005) B2366005
theorem B2802419 : Blo 1867635 2802419 := bstep (se 1 (by rfl) ⟨2101814, by rfl⟩ : syracuseStep 2802419 = 4203629) B4203629
theorem B1868531 : Blo 1867635 1868531 := bstep (se 1 (by rfl) ⟨1401398, by rfl⟩ : syracuseStep 1868531 = 2802797) B2802797
theorem B4727555 : Blo 1867635 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B1868547 : Blo 1867635 1868547 := bstep (se 1 (by rfl) ⟨1401410, by rfl⟩ : syracuseStep 1868547 = 2802821) B2802821
theorem B7095053 : Blo 1867635 7095053 := bstep (se 3 (by rfl) ⟨1330322, by rfl⟩ : syracuseStep 7095053 = 2660645) B2660645
theorem B14197517 : Blo 1867635 14197517 := bstep (se 3 (by rfl) ⟨2662034, by rfl⟩ : syracuseStep 14197517 = 5324069) B5324069
theorem B2802449 : Blo 1867635 2802449 := bstep (se 2 (by rfl) ⟨1050918, by rfl⟩ : syracuseStep 2802449 = 2101837) B2101837
theorem B1868563 : Blo 1867635 1868563 := bstep (se 1 (by rfl) ⟨1401422, by rfl⟩ : syracuseStep 1868563 = 2802845) B2802845
theorem B11969315 : Blo 1867635 11969315 := bstep (se 1 (by rfl) ⟨8976986, by rfl⟩ : syracuseStep 11969315 = 17953973) B17953973
theorem B2802467 : Blo 1867635 2802467 := bstep (se 1 (by rfl) ⟨2101850, by rfl⟩ : syracuseStep 2802467 = 4203701) B4203701
theorem B1868579 : Blo 1867635 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B6308657 : Blo 1867635 6308657 := bstep (se 2 (by rfl) ⟨2365746, by rfl⟩ : syracuseStep 6308657 = 4731493) B4731493
theorem B1868595 : Blo 1867635 1868595 := bstep (se 1 (by rfl) ⟨1401446, by rfl⟩ : syracuseStep 1868595 = 2802893) B2802893
theorem B2802497 : Blo 1867635 2802497 := bstep (se 2 (by rfl) ⟨1050936, by rfl⟩ : syracuseStep 2802497 = 2101873) B2101873
theorem B4318019 : Blo 1867635 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B1868611 : Blo 1867635 1868611 := bstep (se 1 (by rfl) ⟨1401458, by rfl⟩ : syracuseStep 1868611 = 2802917) B2802917
theorem B2802515 : Blo 1867635 2802515 := bstep (se 1 (by rfl) ⟨2101886, by rfl⟩ : syracuseStep 2802515 = 4203773) B4203773
theorem B1868627 : Blo 1867635 1868627 := bstep (se 1 (by rfl) ⟨1401470, by rfl⟩ : syracuseStep 1868627 = 2802941) B2802941
theorem B1868643 : Blo 1867635 1868643 := bstep (se 1 (by rfl) ⟨1401482, by rfl⟩ : syracuseStep 1868643 = 2802965) B2802965
theorem B4203377 : Blo 1867635 4203377 := bstep (se 2 (by rfl) ⟨1576266, by rfl⟩ : syracuseStep 4203377 = 3152533) B3152533
theorem B2802545 : Blo 1867635 2802545 := bstep (se 2 (by rfl) ⟨1050954, by rfl⟩ : syracuseStep 2802545 = 2101909) B2101909
theorem B1868659 : Blo 1867635 1868659 := bstep (se 1 (by rfl) ⟨1401494, by rfl⟩ : syracuseStep 1868659 = 2802989) B2802989
theorem B3154801 : Blo 1867635 3154801 := bstep (se 2 (by rfl) ⟨1183050, by rfl⟩ : syracuseStep 3154801 = 2366101) B2366101
theorem B4203395 : Blo 1867635 4203395 := bstep (se 1 (by rfl) ⟨3152546, by rfl⟩ : syracuseStep 4203395 = 6305093) B6305093
theorem B2802563 : Blo 1867635 2802563 := bstep (se 1 (by rfl) ⟨2101922, by rfl⟩ : syracuseStep 2802563 = 4203845) B4203845
theorem B1868675 : Blo 1867635 1868675 := bstep (se 1 (by rfl) ⟨1401506, by rfl⟩ : syracuseStep 1868675 = 2803013) B2803013
theorem B1868691 : Blo 1867635 1868691 := bstep (se 1 (by rfl) ⟨1401518, by rfl⟩ : syracuseStep 1868691 = 2803037) B2803037
theorem B2802593 : Blo 1867635 2802593 := bstep (se 2 (by rfl) ⟨1050972, by rfl⟩ : syracuseStep 2802593 = 2101945) B2101945
theorem B1868707 : Blo 1867635 1868707 := bstep (se 1 (by rfl) ⟨1401530, by rfl⟩ : syracuseStep 1868707 = 2803061) B2803061
theorem B4490147 : Blo 1867635 4490147 := bstep (se 1 (by rfl) ⟨3367610, by rfl⟩ : syracuseStep 4490147 = 6735221) B6735221
theorem B6480803 : Blo 1867635 6480803 := bstep (se 1 (by rfl) ⟨4860602, by rfl⟩ : syracuseStep 6480803 = 9721205) B9721205
theorem B7979953 : Blo 1867635 7979953 := bstep (se 2 (by rfl) ⟨2992482, by rfl⟩ : syracuseStep 7979953 = 5984965) B5984965
theorem B5989297 : Blo 1867635 5989297 := bstep (se 2 (by rfl) ⟨2245986, by rfl⟩ : syracuseStep 5989297 = 4491973) B4491973
theorem B2802611 : Blo 1867635 2802611 := bstep (se 1 (by rfl) ⟨2101958, by rfl⟩ : syracuseStep 2802611 = 4203917) B4203917
theorem B1868723 : Blo 1867635 1868723 := bstep (se 1 (by rfl) ⟨1401542, by rfl⟩ : syracuseStep 1868723 = 2803085) B2803085
theorem B4727747 : Blo 1867635 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B1868739 : Blo 1867635 1868739 := bstep (se 1 (by rfl) ⟨1401554, by rfl⟩ : syracuseStep 1868739 = 2803109) B2803109
theorem B2802641 : Blo 1867635 2802641 := bstep (se 2 (by rfl) ⟨1050990, by rfl⟩ : syracuseStep 2802641 = 2101981) B2101981
theorem B1868755 : Blo 1867635 1868755 := bstep (se 1 (by rfl) ⟨1401566, by rfl⟩ : syracuseStep 1868755 = 2803133) B2803133
theorem B2802659 : Blo 1867635 2802659 := bstep (se 1 (by rfl) ⟨2101994, by rfl⟩ : syracuseStep 2802659 = 4203989) B4203989
theorem B1868771 : Blo 1867635 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B8520689 : Blo 1867635 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B1868787 : Blo 1867635 1868787 := bstep (se 1 (by rfl) ⟨1401590, by rfl⟩ : syracuseStep 1868787 = 2803181) B2803181
theorem B3367921 : Blo 1867635 3367921 := bstep (se 2 (by rfl) ⟨1262970, by rfl⟩ : syracuseStep 3367921 = 2525941) B2525941
theorem B2802689 : Blo 1867635 2802689 := bstep (se 2 (by rfl) ⟨1051008, by rfl⟩ : syracuseStep 2802689 = 2102017) B2102017
theorem B4318211 : Blo 1867635 4318211 := bstep (se 1 (by rfl) ⟨3238658, by rfl⟩ : syracuseStep 4318211 = 6477317) B6477317
theorem B1868803 : Blo 1867635 1868803 := bstep (se 1 (by rfl) ⟨1401602, by rfl⟩ : syracuseStep 1868803 = 2803205) B2803205
theorem B2802707 : Blo 1867635 2802707 := bstep (se 1 (by rfl) ⟨2102030, by rfl⟩ : syracuseStep 2802707 = 4204061) B4204061
theorem B1868819 : Blo 1867635 1868819 := bstep (se 1 (by rfl) ⟨1401614, by rfl⟩ : syracuseStep 1868819 = 2803229) B2803229
theorem B3154963 : Blo 1867635 3154963 := bstep (se 1 (by rfl) ⟨2366222, by rfl⟩ : syracuseStep 3154963 = 4732445) B4732445
theorem B1868835 : Blo 1867635 1868835 := bstep (se 1 (by rfl) ⟨1401626, by rfl⟩ : syracuseStep 1868835 = 2803253) B2803253
theorem B3548195 : Blo 1867635 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B2802737 : Blo 1867635 2802737 := bstep (se 2 (by rfl) ⟨1051026, by rfl⟩ : syracuseStep 2802737 = 2102053) B2102053
theorem B1868851 : Blo 1867635 1868851 := bstep (se 1 (by rfl) ⟨1401638, by rfl⟩ : syracuseStep 1868851 = 2803277) B2803277
theorem B2769985 : Blo 1867635 2769985 := bstep (se 2 (by rfl) ⟨1038744, by rfl⟩ : syracuseStep 2769985 = 2077489) B2077489
theorem B2802755 : Blo 1867635 2802755 := bstep (se 1 (by rfl) ⟨2102066, by rfl⟩ : syracuseStep 2802755 = 4204133) B4204133
theorem B1868867 : Blo 1867635 1868867 := bstep (se 1 (by rfl) ⟨1401650, by rfl⟩ : syracuseStep 1868867 = 2803301) B2803301
theorem B1868883 : Blo 1867635 1868883 := bstep (se 1 (by rfl) ⟨1401662, by rfl⟩ : syracuseStep 1868883 = 2803325) B2803325
theorem B2802785 : Blo 1867635 2802785 := bstep (se 2 (by rfl) ⟨1051044, by rfl⟩ : syracuseStep 2802785 = 2102089) B2102089
theorem B1868899 : Blo 1867635 1868899 := bstep (se 1 (by rfl) ⟨1401674, by rfl⟩ : syracuseStep 1868899 = 2803349) B2803349
theorem B2802803 : Blo 1867635 2802803 := bstep (se 1 (by rfl) ⟨2102102, by rfl⟩ : syracuseStep 2802803 = 4204205) B4204205
theorem B1868915 : Blo 1867635 1868915 := bstep (se 1 (by rfl) ⟨1401686, by rfl⟩ : syracuseStep 1868915 = 2803373) B2803373
theorem B1868931 : Blo 1867635 1868931 := bstep (se 1 (by rfl) ⟨1401698, by rfl⟩ : syracuseStep 1868931 = 2803397) B2803397
theorem B4203665 : Blo 1867635 4203665 := bstep (se 2 (by rfl) ⟨1576374, by rfl⟩ : syracuseStep 4203665 = 3152749) B3152749
theorem B2802833 : Blo 1867635 2802833 := bstep (se 2 (by rfl) ⟨1051062, by rfl⟩ : syracuseStep 2802833 = 2102125) B2102125
theorem B1868947 : Blo 1867635 1868947 := bstep (se 1 (by rfl) ⟨1401710, by rfl⟩ : syracuseStep 1868947 = 2803421) B2803421
theorem B4203683 : Blo 1867635 4203683 := bstep (se 1 (by rfl) ⟨3152762, by rfl⟩ : syracuseStep 4203683 = 6305525) B6305525
theorem B2802851 : Blo 1867635 2802851 := bstep (se 1 (by rfl) ⟨2102138, by rfl⟩ : syracuseStep 2802851 = 4204277) B4204277
theorem B1868963 : Blo 1867635 1868963 := bstep (se 1 (by rfl) ⟨1401722, by rfl⟩ : syracuseStep 1868963 = 2803445) B2803445
theorem B1868979 : Blo 1867635 1868979 := bstep (se 1 (by rfl) ⟨1401734, by rfl⟩ : syracuseStep 1868979 = 2803469) B2803469
theorem B2802881 : Blo 1867635 2802881 := bstep (se 2 (by rfl) ⟨1051080, by rfl⟩ : syracuseStep 2802881 = 2102161) B2102161
theorem B4490435 : Blo 1867635 4490435 := bstep (se 1 (by rfl) ⟨3367826, by rfl⟩ : syracuseStep 4490435 = 6735653) B6735653
theorem B40412357 : Blo 1867635 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B1868995 : Blo 1867635 1868995 := bstep (se 1 (by rfl) ⟨1401746, by rfl⟩ : syracuseStep 1868995 = 2803493) B2803493
theorem B2802899 : Blo 1867635 2802899 := bstep (se 1 (by rfl) ⟨2102174, by rfl⟩ : syracuseStep 2802899 = 4204349) B4204349
theorem B1869011 : Blo 1867635 1869011 := bstep (se 1 (by rfl) ⟨1401758, by rfl⟩ : syracuseStep 1869011 = 2803517) B2803517
theorem B1869027 : Blo 1867635 1869027 := bstep (se 1 (by rfl) ⟨1401770, by rfl⟩ : syracuseStep 1869027 = 2803541) B2803541
theorem B4793585 : Blo 1867635 4793585 := bstep (se 2 (by rfl) ⟨1797594, by rfl⟩ : syracuseStep 4793585 = 3595189) B3595189
theorem B13468913 : Blo 1867635 13468913 := bstep (se 2 (by rfl) ⟨5050842, by rfl⟩ : syracuseStep 13468913 = 10101685) B10101685
theorem B2802929 : Blo 1867635 2802929 := bstep (se 2 (by rfl) ⟨1051098, by rfl⟩ : syracuseStep 2802929 = 2102197) B2102197
theorem B1869043 : Blo 1867635 1869043 := bstep (se 1 (by rfl) ⟨1401782, by rfl⟩ : syracuseStep 1869043 = 2803565) B2803565
theorem B2802947 : Blo 1867635 2802947 := bstep (se 1 (by rfl) ⟨2102210, by rfl⟩ : syracuseStep 2802947 = 4204421) B4204421
theorem B1869059 : Blo 1867635 1869059 := bstep (se 1 (by rfl) ⟨1401794, by rfl⟩ : syracuseStep 1869059 = 2803589) B2803589
theorem B1869075 : Blo 1867635 1869075 := bstep (se 1 (by rfl) ⟨1401806, by rfl⟩ : syracuseStep 1869075 = 2803613) B2803613
theorem B2802977 : Blo 1867635 2802977 := bstep (se 2 (by rfl) ⟨1051116, by rfl⟩ : syracuseStep 2802977 = 2102233) B2102233
theorem B1869091 : Blo 1867635 1869091 := bstep (se 1 (by rfl) ⟨1401818, by rfl⟩ : syracuseStep 1869091 = 2803637) B2803637
theorem B2802995 : Blo 1867635 2802995 := bstep (se 1 (by rfl) ⟨2102246, by rfl⟩ : syracuseStep 2802995 = 4204493) B4204493
theorem B1869107 : Blo 1867635 1869107 := bstep (se 1 (by rfl) ⟨1401830, by rfl⟩ : syracuseStep 1869107 = 2803661) B2803661
theorem B2131267 : Blo 1867635 2131267 := bstep (se 1 (by rfl) ⟨1598450, by rfl⟩ : syracuseStep 2131267 = 3196901) B3196901
theorem B1869123 : Blo 1867635 1869123 := bstep (se 1 (by rfl) ⟨1401842, by rfl⟩ : syracuseStep 1869123 = 2803685) B2803685
theorem B6309197 : Blo 1867635 6309197 := bstep (se 3 (by rfl) ⟨1182974, by rfl⟩ : syracuseStep 6309197 = 2365949) B2365949
theorem B3990865 : Blo 1867635 3990865 := bstep (se 2 (by rfl) ⟨1496574, by rfl⟩ : syracuseStep 3990865 = 2993149) B2993149
theorem B2803025 : Blo 1867635 2803025 := bstep (se 2 (by rfl) ⟨1051134, by rfl⟩ : syracuseStep 2803025 = 2102269) B2102269
theorem B1869139 : Blo 1867635 1869139 := bstep (se 1 (by rfl) ⟨1401854, by rfl⟩ : syracuseStep 1869139 = 2803709) B2803709
theorem B3990883 : Blo 1867635 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B2803043 : Blo 1867635 2803043 := bstep (se 1 (by rfl) ⟨2102282, by rfl⟩ : syracuseStep 2803043 = 4204565) B4204565
theorem B1869155 : Blo 1867635 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B1869171 : Blo 1867635 1869171 := bstep (se 1 (by rfl) ⟨1401878, by rfl⟩ : syracuseStep 1869171 = 2803757) B2803757
theorem B2803073 : Blo 1867635 2803073 := bstep (se 2 (by rfl) ⟨1051152, by rfl⟩ : syracuseStep 2803073 = 2102305) B2102305
theorem B1869187 : Blo 1867635 1869187 := bstep (se 1 (by rfl) ⟨1401890, by rfl⟩ : syracuseStep 1869187 = 2803781) B2803781
theorem B6309251 : Blo 1867635 6309251 := bstep (se 1 (by rfl) ⟨4731938, by rfl⟩ : syracuseStep 6309251 = 9463877) B9463877
theorem B2803091 : Blo 1867635 2803091 := bstep (se 1 (by rfl) ⟨2102318, by rfl⟩ : syracuseStep 2803091 = 4204637) B4204637
theorem B1869203 : Blo 1867635 1869203 := bstep (se 1 (by rfl) ⟨1401902, by rfl⟩ : syracuseStep 1869203 = 2803805) B2803805
theorem B1869219 : Blo 1867635 1869219 := bstep (se 1 (by rfl) ⟨1401914, by rfl⟩ : syracuseStep 1869219 = 2803829) B2803829
theorem B4203953 : Blo 1867635 4203953 := bstep (se 2 (by rfl) ⟨1576482, by rfl⟩ : syracuseStep 4203953 = 3152965) B3152965
theorem B2803121 : Blo 1867635 2803121 := bstep (se 2 (by rfl) ⟨1051170, by rfl⟩ : syracuseStep 2803121 = 2102341) B2102341
theorem B1869235 : Blo 1867635 1869235 := bstep (se 1 (by rfl) ⟨1401926, by rfl⟩ : syracuseStep 1869235 = 2803853) B2803853
theorem B1893827 : Blo 1867635 1893827 := bstep (se 1 (by rfl) ⟨1420370, by rfl⟩ : syracuseStep 1893827 = 2840741) B2840741
theorem B4203971 : Blo 1867635 4203971 := bstep (se 1 (by rfl) ⟨3152978, by rfl⟩ : syracuseStep 4203971 = 6305957) B6305957
theorem B2803139 : Blo 1867635 2803139 := bstep (se 1 (by rfl) ⟨2102354, by rfl⟩ : syracuseStep 2803139 = 4204709) B4204709
theorem B1869251 : Blo 1867635 1869251 := bstep (se 1 (by rfl) ⟨1401938, by rfl⟩ : syracuseStep 1869251 = 2803877) B2803877
theorem B1869267 : Blo 1867635 1869267 := bstep (se 1 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 1869267 = 2803901) B2803901
theorem B2803169 : Blo 1867635 2803169 := bstep (se 2 (by rfl) ⟨1051188, by rfl⟩ : syracuseStep 2803169 = 2102377) B2102377
theorem B1869283 : Blo 1867635 1869283 := bstep (se 1 (by rfl) ⟨1401962, by rfl⟩ : syracuseStep 1869283 = 2803925) B2803925
theorem B2803187 : Blo 1867635 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B1869299 : Blo 1867635 1869299 := bstep (se 1 (by rfl) ⟨1401974, by rfl⟩ : syracuseStep 1869299 = 2803949) B2803949
theorem B1869315 : Blo 1867635 1869315 := bstep (se 1 (by rfl) ⟨1401986, by rfl⟩ : syracuseStep 1869315 = 2803973) B2803973
theorem B2803217 : Blo 1867635 2803217 := bstep (se 2 (by rfl) ⟨1051206, by rfl⟩ : syracuseStep 2803217 = 2102413) B2102413
theorem B1869331 : Blo 1867635 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B2803235 : Blo 1867635 2803235 := bstep (se 1 (by rfl) ⟨2102426, by rfl⟩ : syracuseStep 2803235 = 4204853) B4204853
theorem B1869347 : Blo 1867635 1869347 := bstep (se 1 (by rfl) ⟨1402010, by rfl⟩ : syracuseStep 1869347 = 2804021) B2804021
theorem B2958899 : Blo 1867635 2958899 := bstep (se 1 (by rfl) ⟨2219174, by rfl⟩ : syracuseStep 2958899 = 4438349) B4438349
theorem B1869363 : Blo 1867635 1869363 := bstep (se 1 (by rfl) ⟨1402022, by rfl⟩ : syracuseStep 1869363 = 2804045) B2804045
theorem B2803265 : Blo 1867635 2803265 := bstep (se 2 (by rfl) ⟨1051224, by rfl⟩ : syracuseStep 2803265 = 2102449) B2102449
theorem B1869379 : Blo 1867635 1869379 := bstep (se 1 (by rfl) ⟨1402034, by rfl⟩ : syracuseStep 1869379 = 2804069) B2804069
theorem B2803283 : Blo 1867635 2803283 := bstep (se 1 (by rfl) ⟨2102462, by rfl⟩ : syracuseStep 2803283 = 4204925) B4204925
theorem B1869395 : Blo 1867635 1869395 := bstep (se 1 (by rfl) ⟨1402046, by rfl⟩ : syracuseStep 1869395 = 2804093) B2804093
theorem B1869411 : Blo 1867635 1869411 := bstep (se 1 (by rfl) ⟨1402058, by rfl⟩ : syracuseStep 1869411 = 2804117) B2804117
theorem B2803313 : Blo 1867635 2803313 := bstep (se 2 (by rfl) ⟨1051242, by rfl⟩ : syracuseStep 2803313 = 2102485) B2102485
theorem B3368561 : Blo 1867635 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B1869427 : Blo 1867635 1869427 := bstep (se 1 (by rfl) ⟨1402070, by rfl⟩ : syracuseStep 1869427 = 2804141) B2804141
theorem B2803331 : Blo 1867635 2803331 := bstep (se 1 (by rfl) ⟨2102498, by rfl⟩ : syracuseStep 2803331 = 4204997) B4204997
theorem B1869443 : Blo 1867635 1869443 := bstep (se 1 (by rfl) ⟨1402082, by rfl⟩ : syracuseStep 1869443 = 2804165) B2804165
theorem B6309521 : Blo 1867635 6309521 := bstep (se 2 (by rfl) ⟨2366070, by rfl⟩ : syracuseStep 6309521 = 4732141) B4732141
theorem B1869459 : Blo 1867635 1869459 := bstep (se 1 (by rfl) ⟨1402094, by rfl⟩ : syracuseStep 1869459 = 2804189) B2804189
theorem B2803361 : Blo 1867635 2803361 := bstep (se 2 (by rfl) ⟨1051260, by rfl⟩ : syracuseStep 2803361 = 2102521) B2102521
theorem B1869475 : Blo 1867635 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B2803379 : Blo 1867635 2803379 := bstep (se 1 (by rfl) ⟨2102534, by rfl⟩ : syracuseStep 2803379 = 4205069) B4205069
theorem B1869491 : Blo 1867635 1869491 := bstep (se 1 (by rfl) ⟨1402118, by rfl⟩ : syracuseStep 1869491 = 2804237) B2804237
theorem B2991811 : Blo 1867635 2991811 := bstep (se 1 (by rfl) ⟨2243858, by rfl⟩ : syracuseStep 2991811 = 4487717) B4487717
theorem B1869507 : Blo 1867635 1869507 := bstep (se 1 (by rfl) ⟨1402130, by rfl⟩ : syracuseStep 1869507 = 2804261) B2804261
theorem B14771909 : Blo 1867635 14771909 := bstep (se 4 (by rfl) ⟨1384866, by rfl⟩ : syracuseStep 14771909 = 2769733) B2769733
theorem B4261585 : Blo 1867635 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B4204241 : Blo 1867635 4204241 := bstep (se 2 (by rfl) ⟨1576590, by rfl⟩ : syracuseStep 4204241 = 3153181) B3153181
theorem B2803409 : Blo 1867635 2803409 := bstep (se 2 (by rfl) ⟨1051278, by rfl⟩ : syracuseStep 2803409 = 2102557) B2102557
theorem B1869523 : Blo 1867635 1869523 := bstep (se 1 (by rfl) ⟨1402142, by rfl⟩ : syracuseStep 1869523 = 2804285) B2804285
theorem B4204259 : Blo 1867635 4204259 := bstep (se 1 (by rfl) ⟨3153194, by rfl⟩ : syracuseStep 4204259 = 6306389) B6306389
theorem B2803427 : Blo 1867635 2803427 := bstep (se 1 (by rfl) ⟨2102570, by rfl⟩ : syracuseStep 2803427 = 4205141) B4205141
theorem B1869539 : Blo 1867635 1869539 := bstep (se 1 (by rfl) ⟨1402154, by rfl⟩ : syracuseStep 1869539 = 2804309) B2804309
theorem B1869555 : Blo 1867635 1869555 := bstep (se 1 (by rfl) ⟨1402166, by rfl⟩ : syracuseStep 1869555 = 2804333) B2804333
theorem B2803457 : Blo 1867635 2803457 := bstep (se 2 (by rfl) ⟨1051296, by rfl⟩ : syracuseStep 2803457 = 2102593) B2102593
theorem B3196675 : Blo 1867635 3196675 := bstep (se 1 (by rfl) ⟨2397506, by rfl⟩ : syracuseStep 3196675 = 4795013) B4795013
theorem B1869571 : Blo 1867635 1869571 := bstep (se 1 (by rfl) ⟨1402178, by rfl⟩ : syracuseStep 1869571 = 2804357) B2804357
theorem B2803475 : Blo 1867635 2803475 := bstep (se 1 (by rfl) ⟨2102606, by rfl⟩ : syracuseStep 2803475 = 4205213) B4205213
theorem B1869587 : Blo 1867635 1869587 := bstep (se 1 (by rfl) ⟨1402190, by rfl⟩ : syracuseStep 1869587 = 2804381) B2804381
theorem B1869603 : Blo 1867635 1869603 := bstep (se 1 (by rfl) ⟨1402202, by rfl⟩ : syracuseStep 1869603 = 2804405) B2804405
theorem B2803505 : Blo 1867635 2803505 := bstep (se 2 (by rfl) ⟨1051314, by rfl⟩ : syracuseStep 2803505 = 2102629) B2102629
theorem B1869619 : Blo 1867635 1869619 := bstep (se 1 (by rfl) ⟨1402214, by rfl⟩ : syracuseStep 1869619 = 2804429) B2804429
theorem B2803523 : Blo 1867635 2803523 := bstep (se 1 (by rfl) ⟨2102642, by rfl⟩ : syracuseStep 2803523 = 4205285) B4205285
theorem B1869635 : Blo 1867635 1869635 := bstep (se 1 (by rfl) ⟨1402226, by rfl⟩ : syracuseStep 1869635 = 2804453) B2804453
theorem B2803553 : Blo 1867635 2803553 := bstep (se 2 (by rfl) ⟨1051332, by rfl⟩ : syracuseStep 2803553 = 2102665) B2102665
theorem B4728689 : Blo 1867635 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B2803571 : Blo 1867635 2803571 := bstep (se 1 (by rfl) ⟨2102678, by rfl⟩ : syracuseStep 2803571 = 4205357) B4205357
theorem B2803601 : Blo 1867635 2803601 := bstep (se 2 (by rfl) ⟨1051350, by rfl⟩ : syracuseStep 2803601 = 2102701) B2102701
theorem B4728739 : Blo 1867635 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B2803619 : Blo 1867635 2803619 := bstep (se 1 (by rfl) ⟨2102714, by rfl⟩ : syracuseStep 2803619 = 4205429) B4205429
theorem B9463715 : Blo 1867635 9463715 := bstep (se 1 (by rfl) ⟨7097786, by rfl⟩ : syracuseStep 9463715 = 14195573) B14195573
theorem B3549091 : Blo 1867635 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B2803649 : Blo 1867635 2803649 := bstep (se 2 (by rfl) ⟨1051368, by rfl⟩ : syracuseStep 2803649 = 2102737) B2102737
theorem B2992067 : Blo 1867635 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B2803667 : Blo 1867635 2803667 := bstep (se 1 (by rfl) ⟨2102750, by rfl⟩ : syracuseStep 2803667 = 4205501) B4205501
theorem B45459427 : Blo 1867635 45459427 := bstep (se 1 (by rfl) ⟨34094570, by rfl⟩ : syracuseStep 45459427 = 68189141) B68189141
theorem B4204529 : Blo 1867635 4204529 := bstep (se 2 (by rfl) ⟨1576698, by rfl⟩ : syracuseStep 4204529 = 3153397) B3153397
theorem B2803697 : Blo 1867635 2803697 := bstep (se 2 (by rfl) ⟨1051386, by rfl⟩ : syracuseStep 2803697 = 2102773) B2102773
theorem B4204547 : Blo 1867635 4204547 := bstep (se 1 (by rfl) ⟨3153410, by rfl⟩ : syracuseStep 4204547 = 6306821) B6306821
theorem B2803715 : Blo 1867635 2803715 := bstep (se 1 (by rfl) ⟨2102786, by rfl⟩ : syracuseStep 2803715 = 4205573) B4205573
theorem B2803745 : Blo 1867635 2803745 := bstep (se 2 (by rfl) ⟨1051404, by rfl⟩ : syracuseStep 2803745 = 2102809) B2102809
theorem B4728881 : Blo 1867635 4728881 := bstep (se 2 (by rfl) ⟨1773330, by rfl⟩ : syracuseStep 4728881 = 3546661) B3546661
theorem B2803763 : Blo 1867635 2803763 := bstep (se 1 (by rfl) ⟨2102822, by rfl⟩ : syracuseStep 2803763 = 4205645) B4205645
theorem B3549251 : Blo 1867635 3549251 := bstep (se 1 (by rfl) ⟨2661938, by rfl⟩ : syracuseStep 3549251 = 5323877) B5323877
theorem B2803793 : Blo 1867635 2803793 := bstep (se 2 (by rfl) ⟨1051422, by rfl⟩ : syracuseStep 2803793 = 2102845) B2102845
theorem B2803811 : Blo 1867635 2803811 := bstep (se 1 (by rfl) ⟨2102858, by rfl⟩ : syracuseStep 2803811 = 4205717) B4205717
theorem B53889137 : Blo 1867635 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B4491377 : Blo 1867635 4491377 := bstep (se 2 (by rfl) ⟨1684266, by rfl⟩ : syracuseStep 4491377 = 3368533) B3368533
theorem B2803841 : Blo 1867635 2803841 := bstep (se 2 (by rfl) ⟨1051440, by rfl⟩ : syracuseStep 2803841 = 2102881) B2102881
theorem B2803859 : Blo 1867635 2803859 := bstep (se 1 (by rfl) ⟨2102894, by rfl⟩ : syracuseStep 2803859 = 4205789) B4205789
theorem B2803889 : Blo 1867635 2803889 := bstep (se 2 (by rfl) ⟨1051458, by rfl⟩ : syracuseStep 2803889 = 2102917) B2102917
theorem B2803907 : Blo 1867635 2803907 := bstep (se 1 (by rfl) ⟨2102930, by rfl⟩ : syracuseStep 2803907 = 4205861) B4205861
theorem B2803937 : Blo 1867635 2803937 := bstep (se 2 (by rfl) ⟨1051476, by rfl⟩ : syracuseStep 2803937 = 2102953) B2102953
theorem B15157489 : Blo 1867635 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B2803955 : Blo 1867635 2803955 := bstep (se 1 (by rfl) ⟨2102966, by rfl⟩ : syracuseStep 2803955 = 4205933) B4205933
theorem B4204817 : Blo 1867635 4204817 := bstep (se 2 (by rfl) ⟨1576806, by rfl⟩ : syracuseStep 4204817 = 3153613) B3153613
theorem B2803985 : Blo 1867635 2803985 := bstep (se 2 (by rfl) ⟨1051494, by rfl⟩ : syracuseStep 2803985 = 2102989) B2102989
theorem B4204835 : Blo 1867635 4204835 := bstep (se 1 (by rfl) ⟨3153626, by rfl⟩ : syracuseStep 4204835 = 6307253) B6307253
theorem B2804003 : Blo 1867635 2804003 := bstep (se 1 (by rfl) ⟨2103002, by rfl⟩ : syracuseStep 2804003 = 4206005) B4206005
theorem B2804033 : Blo 1867635 2804033 := bstep (se 2 (by rfl) ⟨1051512, by rfl⟩ : syracuseStep 2804033 = 2103025) B2103025
theorem B2804051 : Blo 1867635 2804051 := bstep (se 1 (by rfl) ⟨2103038, by rfl⟩ : syracuseStep 2804051 = 4206077) B4206077
theorem B2804081 : Blo 1867635 2804081 := bstep (se 2 (by rfl) ⟨1051530, by rfl⟩ : syracuseStep 2804081 = 2103061) B2103061
theorem B2804099 : Blo 1867635 2804099 := bstep (se 1 (by rfl) ⟨2103074, by rfl⟩ : syracuseStep 2804099 = 4206149) B4206149
theorem B2804129 : Blo 1867635 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B2804147 : Blo 1867635 2804147 := bstep (se 1 (by rfl) ⟨2103110, by rfl⟩ : syracuseStep 2804147 = 4206221) B4206221
theorem B2804177 : Blo 1867635 2804177 := bstep (se 2 (by rfl) ⟨1051566, by rfl⟩ : syracuseStep 2804177 = 2103133) B2103133
theorem B2804195 : Blo 1867635 2804195 := bstep (se 1 (by rfl) ⟨2103146, by rfl⟩ : syracuseStep 2804195 = 4206293) B4206293
theorem B3787249 : Blo 1867635 3787249 := bstep (se 2 (by rfl) ⟨1420218, by rfl⟩ : syracuseStep 3787249 = 2840437) B2840437
theorem B2804225 : Blo 1867635 2804225 := bstep (se 2 (by rfl) ⟨1051584, by rfl⟩ : syracuseStep 2804225 = 2103169) B2103169
theorem B2804243 : Blo 1867635 2804243 := bstep (se 1 (by rfl) ⟨2103182, by rfl⟩ : syracuseStep 2804243 = 4206365) B4206365
theorem B4205105 : Blo 1867635 4205105 := bstep (se 2 (by rfl) ⟨1576914, by rfl⟩ : syracuseStep 4205105 = 3153829) B3153829
theorem B2804273 : Blo 1867635 2804273 := bstep (se 2 (by rfl) ⟨1051602, by rfl⟩ : syracuseStep 2804273 = 2103205) B2103205
theorem B4205123 : Blo 1867635 4205123 := bstep (se 1 (by rfl) ⟨3153842, by rfl⟩ : syracuseStep 4205123 = 6307685) B6307685
theorem B2804291 : Blo 1867635 2804291 := bstep (se 1 (by rfl) ⟨2103218, by rfl⟩ : syracuseStep 2804291 = 4206437) B4206437
theorem B2804321 : Blo 1867635 2804321 := bstep (se 2 (by rfl) ⟨1051620, by rfl⟩ : syracuseStep 2804321 = 2103241) B2103241
theorem B1895027 : Blo 1867635 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B2804339 : Blo 1867635 2804339 := bstep (se 1 (by rfl) ⟨2103254, by rfl⟩ : syracuseStep 2804339 = 4206509) B4206509
theorem B3197585 : Blo 1867635 3197585 := bstep (se 2 (by rfl) ⟨1199094, by rfl⟩ : syracuseStep 3197585 = 2398189) B2398189
theorem B2804369 : Blo 1867635 2804369 := bstep (se 2 (by rfl) ⟨1051638, by rfl⟩ : syracuseStep 2804369 = 2103277) B2103277
theorem B2804387 : Blo 1867635 2804387 := bstep (se 1 (by rfl) ⟨2103290, by rfl⟩ : syracuseStep 2804387 = 4206581) B4206581
theorem B2804417 : Blo 1867635 2804417 := bstep (se 2 (by rfl) ⟨1051656, by rfl⟩ : syracuseStep 2804417 = 2103313) B2103313
theorem B9464525 : Blo 1867635 9464525 := bstep (se 3 (by rfl) ⟨1774598, by rfl⟩ : syracuseStep 9464525 = 3549197) B3549197
theorem B5319377 : Blo 1867635 5319377 := bstep (se 2 (by rfl) ⟨1994766, by rfl⟩ : syracuseStep 5319377 = 3989533) B3989533
theorem B2804435 : Blo 1867635 2804435 := bstep (se 1 (by rfl) ⟨2103326, by rfl⟩ : syracuseStep 2804435 = 4206653) B4206653
theorem B5679875 : Blo 1867635 5679875 := bstep (se 1 (by rfl) ⟨4259906, by rfl⟩ : syracuseStep 5679875 = 8519813) B8519813
theorem B7097165 : Blo 1867635 7097165 := bstep (se 3 (by rfl) ⟨1330718, by rfl⟩ : syracuseStep 7097165 = 2661437) B2661437
theorem B4205393 : Blo 1867635 4205393 := bstep (se 2 (by rfl) ⟨1577022, by rfl⟩ : syracuseStep 4205393 = 3154045) B3154045
theorem B4205411 : Blo 1867635 4205411 := bstep (se 1 (by rfl) ⟨3154058, by rfl⟩ : syracuseStep 4205411 = 6308117) B6308117
theorem B2993041 : Blo 1867635 2993041 := bstep (se 2 (by rfl) ⟨1122390, by rfl⟩ : syracuseStep 2993041 = 2244781) B2244781
theorem B10644493 : Blo 1867635 10644493 := bstep (se 3 (by rfl) ⟨1995842, by rfl⟩ : syracuseStep 10644493 = 3991685) B3991685
theorem B4729873 : Blo 1867635 4729873 := bstep (se 2 (by rfl) ⟨1773702, by rfl⟩ : syracuseStep 4729873 = 3547405) B3547405
theorem B14191685 : Blo 1867635 14191685 := bstep (se 4 (by rfl) ⟨1330470, by rfl⟩ : syracuseStep 14191685 = 2660941) B2660941
theorem B4205681 : Blo 1867635 4205681 := bstep (se 2 (by rfl) ⟨1577130, by rfl⟩ : syracuseStep 4205681 = 3154261) B3154261
theorem B4205699 : Blo 1867635 4205699 := bstep (se 1 (by rfl) ⟨3154274, by rfl⟩ : syracuseStep 4205699 = 6308549) B6308549
theorem B15150221 : Blo 1867635 15150221 := bstep (se 3 (by rfl) ⟨2840666, by rfl⟩ : syracuseStep 15150221 = 5681333) B5681333
theorem B4795537 : Blo 1867635 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B5983427 : Blo 1867635 5983427 := bstep (se 1 (by rfl) ⟨4487570, by rfl⟩ : syracuseStep 5983427 = 8975141) B8975141
theorem B24284357 : Blo 1867635 24284357 := bstep (se 4 (by rfl) ⟨2276658, by rfl⟩ : syracuseStep 24284357 = 4553317) B4553317
theorem B4730147 : Blo 1867635 4730147 := bstep (se 1 (by rfl) ⟨3547610, by rfl⟩ : syracuseStep 4730147 = 7095221) B7095221
theorem B2526547 : Blo 1867635 2526547 := bstep (se 1 (by rfl) ⟨1894910, by rfl⟩ : syracuseStep 2526547 = 3789821) B3789821
theorem B21278051 : Blo 1867635 21278051 := bstep (se 1 (by rfl) ⟨15958538, by rfl⟩ : syracuseStep 21278051 = 31917077) B31917077
theorem B4205969 : Blo 1867635 4205969 := bstep (se 2 (by rfl) ⟨1577238, by rfl⟩ : syracuseStep 4205969 = 3154477) B3154477
theorem B4205987 : Blo 1867635 4205987 := bstep (se 1 (by rfl) ⟨3154490, by rfl⟩ : syracuseStep 4205987 = 6308981) B6308981
theorem B9457073 : Blo 1867635 9457073 := bstep (se 2 (by rfl) ⟨3546402, by rfl⟩ : syracuseStep 9457073 = 7092805) B7092805
theorem B2772433 : Blo 1867635 2772433 := bstep (se 2 (by rfl) ⟨1039662, by rfl⟩ : syracuseStep 2772433 = 2079325) B2079325
theorem B4730339 : Blo 1867635 4730339 := bstep (se 1 (by rfl) ⟨3547754, by rfl⟩ : syracuseStep 4730339 = 7095509) B7095509
theorem B5049901 : Blo 1867635 5049901 := bstep (se 3 (by rfl) ⟨946856, by rfl⟩ : syracuseStep 5049901 = 1893713) B1893713
theorem B7097969 : Blo 1867635 7097969 := bstep (se 2 (by rfl) ⟨2661738, by rfl⟩ : syracuseStep 7097969 = 5323477) B5323477
theorem B5320333 : Blo 1867635 5320333 := bstep (se 3 (by rfl) ⟨997562, by rfl⟩ : syracuseStep 5320333 = 1995125) B1995125
theorem B4206257 : Blo 1867635 4206257 := bstep (se 2 (by rfl) ⟨1577346, by rfl⟩ : syracuseStep 4206257 = 3154693) B3154693
theorem B4206275 : Blo 1867635 4206275 := bstep (se 1 (by rfl) ⟨3154706, by rfl⟩ : syracuseStep 4206275 = 6309413) B6309413
theorem B6303473 : Blo 1867635 6303473 := bstep (se 2 (by rfl) ⟨2363802, by rfl⟩ : syracuseStep 6303473 = 4727605) B4727605
theorem B6737699 : Blo 1867635 6737699 := bstep (se 1 (by rfl) ⟨5053274, by rfl⟩ : syracuseStep 6737699 = 10106549) B10106549
theorem B7573297 : Blo 1867635 7573297 := bstep (se 2 (by rfl) ⟨2839986, by rfl⟩ : syracuseStep 7573297 = 5679973) B5679973
theorem B2993969 : Blo 1867635 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B16174961 : Blo 1867635 16174961 := bstep (se 2 (by rfl) ⟨6065610, by rfl⟩ : syracuseStep 16174961 = 12131221) B12131221
theorem B5320561 : Blo 1867635 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B2101171 : Blo 1867635 2101171 := bstep (se 1 (by rfl) ⟨1575878, by rfl⟩ : syracuseStep 2101171 = 3151757) B3151757
theorem B4206545 : Blo 1867635 4206545 := bstep (se 2 (by rfl) ⟨1577454, by rfl⟩ : syracuseStep 4206545 = 3154909) B3154909
theorem B4206563 : Blo 1867635 4206563 := bstep (se 1 (by rfl) ⟨3154922, by rfl⟩ : syracuseStep 4206563 = 6309845) B6309845
theorem B5320721 : Blo 1867635 5320721 := bstep (se 2 (by rfl) ⟨1995270, by rfl⟩ : syracuseStep 5320721 = 3990541) B3990541
theorem B2101315 : Blo 1867635 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B5320835 : Blo 1867635 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B6828209 : Blo 1867635 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B2101459 : Blo 1867635 2101459 := bstep (se 1 (by rfl) ⟨1576094, by rfl⟩ : syracuseStep 2101459 = 3152189) B3152189
theorem B6304013 : Blo 1867635 6304013 := bstep (se 3 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 6304013 = 2364005) B2364005
theorem B7098637 : Blo 1867635 7098637 := bstep (se 3 (by rfl) ⟨1330994, by rfl⟩ : syracuseStep 7098637 = 2661989) B2661989
theorem B6304067 : Blo 1867635 6304067 := bstep (se 1 (by rfl) ⟨4728050, by rfl⟩ : syracuseStep 6304067 = 9456101) B9456101
theorem B10105165 : Blo 1867635 10105165 := bstep (se 3 (by rfl) ⟨1894718, by rfl⟩ : syracuseStep 10105165 = 3789437) B3789437
theorem B2101603 : Blo 1867635 2101603 := bstep (se 1 (by rfl) ⟨1576202, by rfl⟩ : syracuseStep 2101603 = 3152405) B3152405
theorem B5050723 : Blo 1867635 5050723 := bstep (se 1 (by rfl) ⟨3788042, by rfl⟩ : syracuseStep 5050723 = 7576085) B7576085
theorem B2462083 : Blo 1867635 2462083 := bstep (se 1 (by rfl) ⟨1846562, by rfl⟩ : syracuseStep 2462083 = 3693125) B3693125
theorem B8638861 : Blo 1867635 8638861 := bstep (se 3 (by rfl) ⟨1619786, by rfl⟩ : syracuseStep 8638861 = 3239573) B3239573
theorem B11973005 : Blo 1867635 11973005 := bstep (se 3 (by rfl) ⟨2244938, by rfl⟩ : syracuseStep 11973005 = 4489877) B4489877
theorem B4731281 : Blo 1867635 4731281 := bstep (se 2 (by rfl) ⟨1774230, by rfl⟩ : syracuseStep 4731281 = 3548461) B3548461
theorem B2363843 : Blo 1867635 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B4731331 : Blo 1867635 4731331 := bstep (se 1 (by rfl) ⟨3548498, by rfl⟩ : syracuseStep 4731331 = 7096997) B7096997
theorem B2101747 : Blo 1867635 2101747 := bstep (se 1 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 2101747 = 3152621) B3152621
theorem B7983629 : Blo 1867635 7983629 := bstep (se 3 (by rfl) ⟨1496930, by rfl⟩ : syracuseStep 7983629 = 2993861) B2993861
theorem B6304337 : Blo 1867635 6304337 := bstep (se 2 (by rfl) ⟨2364126, by rfl⟩ : syracuseStep 6304337 = 4728253) B4728253
theorem B4731473 : Blo 1867635 4731473 := bstep (se 2 (by rfl) ⟨1774302, by rfl⟩ : syracuseStep 4731473 = 3548605) B3548605
theorem B2101891 : Blo 1867635 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B5681809 : Blo 1867635 5681809 := bstep (se 2 (by rfl) ⟨2130678, by rfl⟩ : syracuseStep 5681809 = 4261357) B4261357
theorem B3154835 : Blo 1867635 3154835 := bstep (se 1 (by rfl) ⟨2366126, by rfl⟩ : syracuseStep 3154835 = 4732253) B4732253
theorem B2102035 : Blo 1867635 2102035 := bstep (se 1 (by rfl) ⟨1576526, by rfl⟩ : syracuseStep 2102035 = 3153053) B3153053
theorem B8983331 : Blo 1867635 8983331 := bstep (se 1 (by rfl) ⟨6737498, by rfl⟩ : syracuseStep 8983331 = 13474997) B13474997
theorem B9458531 : Blo 1867635 9458531 := bstep (se 1 (by rfl) ⟨7093898, by rfl⟩ : syracuseStep 9458531 = 14187797) B14187797
theorem B2102179 : Blo 1867635 2102179 := bstep (se 1 (by rfl) ⟨1576634, by rfl⟩ : syracuseStep 2102179 = 3153269) B3153269
theorem B5985197 : Blo 1867635 5985197 := bstep (se 3 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 5985197 = 2244449) B2244449
theorem B2659267 : Blo 1867635 2659267 := bstep (se 1 (by rfl) ⟨1994450, by rfl⟩ : syracuseStep 2659267 = 3988901) B3988901
theorem B1995715 : Blo 1867635 1995715 := bstep (se 1 (by rfl) ⟨1496786, by rfl⟩ : syracuseStep 1995715 = 2993573) B2993573
theorem B10646477 : Blo 1867635 10646477 := bstep (se 3 (by rfl) ⟨1996214, by rfl⟩ : syracuseStep 10646477 = 3992429) B3992429
theorem B3412945 : Blo 1867635 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B6394925 : Blo 1867635 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B2102323 : Blo 1867635 2102323 := bstep (se 1 (by rfl) ⟨1576742, by rfl⟩ : syracuseStep 2102323 = 3153485) B3153485
theorem B6304877 : Blo 1867635 6304877 := bstep (se 3 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 6304877 = 2364329) B2364329
theorem B5321837 : Blo 1867635 5321837 := bstep (se 3 (by rfl) ⟨997844, by rfl⟩ : syracuseStep 5321837 = 1995689) B1995689
theorem B2364547 : Blo 1867635 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B6304931 : Blo 1867635 6304931 := bstep (se 1 (by rfl) ⟨4728698, by rfl⟩ : syracuseStep 6304931 = 9457397) B9457397
theorem B2102467 : Blo 1867635 2102467 := bstep (se 1 (by rfl) ⟨1576850, by rfl⟩ : syracuseStep 2102467 = 3153701) B3153701
theorem B15971525 : Blo 1867635 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B2364643 : Blo 1867635 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B5322019 : Blo 1867635 5322019 := bstep (se 1 (by rfl) ⟨3991514, by rfl⟩ : syracuseStep 5322019 = 7983029) B7983029
theorem B10638661 : Blo 1867635 10638661 := bstep (se 4 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 10638661 = 1994749) B1994749
theorem B2102611 : Blo 1867635 2102611 := bstep (se 1 (by rfl) ⟨1576958, by rfl⟩ : syracuseStep 2102611 = 3153917) B3153917
theorem B6305201 : Blo 1867635 6305201 := bstep (se 2 (by rfl) ⟨2364450, by rfl⟩ : syracuseStep 6305201 = 4728901) B4728901
theorem B5322179 : Blo 1867635 5322179 := bstep (se 1 (by rfl) ⟨3991634, by rfl⟩ : syracuseStep 5322179 = 7983269) B7983269
theorem B2102755 : Blo 1867635 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B2659825 : Blo 1867635 2659825 := bstep (se 2 (by rfl) ⟨997434, by rfl⟩ : syracuseStep 2659825 = 1994869) B1994869
theorem B6395441 : Blo 1867635 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B4732465 : Blo 1867635 4732465 := bstep (se 2 (by rfl) ⟨1774674, by rfl⟩ : syracuseStep 4732465 = 3549349) B3549349
theorem B10098245 : Blo 1867635 10098245 := bstep (se 4 (by rfl) ⟨946710, by rfl⟩ : syracuseStep 10098245 = 1893421) B1893421
theorem B2102899 : Blo 1867635 2102899 := bstep (se 1 (by rfl) ⟨1577174, by rfl⟩ : syracuseStep 2102899 = 3154349) B3154349
theorem B9459341 : Blo 1867635 9459341 := bstep (se 3 (by rfl) ⟨1773626, by rfl⟩ : syracuseStep 9459341 = 3547253) B3547253
theorem B10106531 : Blo 1867635 10106531 := bstep (se 1 (by rfl) ⟨7579898, by rfl⟩ : syracuseStep 10106531 = 15159797) B15159797
theorem B2840273 : Blo 1867635 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B2365139 : Blo 1867635 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B2103043 : Blo 1867635 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B3151649 : Blo 1867635 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B14186339 : Blo 1867635 14186339 := bstep (se 1 (by rfl) ⟨10639754, by rfl⟩ : syracuseStep 14186339 = 21279509) B21279509
theorem B10647409 : Blo 1867635 10647409 := bstep (se 2 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 10647409 = 7985557) B7985557
theorem B2103187 : Blo 1867635 2103187 := bstep (se 1 (by rfl) ⟨1577390, by rfl⟩ : syracuseStep 2103187 = 3154781) B3154781
theorem B3151777 : Blo 1867635 3151777 := bstep (se 2 (by rfl) ⟨1181916, by rfl⟩ : syracuseStep 3151777 = 2363833) B2363833
theorem B3151811 : Blo 1867635 3151811 := bstep (se 1 (by rfl) ⟨2363858, by rfl⟩ : syracuseStep 3151811 = 4727717) B4727717
theorem B13465541 : Blo 1867635 13465541 := bstep (se 4 (by rfl) ⟨1262394, by rfl⟩ : syracuseStep 13465541 = 2524789) B2524789
theorem B6305741 : Blo 1867635 6305741 := bstep (se 3 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 6305741 = 2364653) B2364653
theorem B10786765 : Blo 1867635 10786765 := bstep (se 3 (by rfl) ⟨2022518, by rfl⟩ : syracuseStep 10786765 = 4045037) B4045037
theorem B6731761 : Blo 1867635 6731761 := bstep (se 2 (by rfl) ⟨2524410, by rfl⟩ : syracuseStep 6731761 = 5048821) B5048821
theorem B6305795 : Blo 1867635 6305795 := bstep (se 1 (by rfl) ⟨4729346, by rfl⟩ : syracuseStep 6305795 = 9458693) B9458693
theorem B8525837 : Blo 1867635 8525837 := bstep (se 3 (by rfl) ⟨1598594, by rfl⟩ : syracuseStep 8525837 = 3197189) B3197189
theorem B2103331 : Blo 1867635 2103331 := bstep (se 1 (by rfl) ⟨1577498, by rfl⟩ : syracuseStep 2103331 = 3154997) B3154997
theorem B3151939 : Blo 1867635 3151939 := bstep (se 1 (by rfl) ⟨2363954, by rfl⟩ : syracuseStep 3151939 = 4727909) B4727909
theorem B2660531 : Blo 1867635 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B3152081 : Blo 1867635 3152081 := bstep (se 2 (by rfl) ⟨1182030, by rfl⟩ : syracuseStep 3152081 = 2364061) B2364061
theorem B6306065 : Blo 1867635 6306065 := bstep (se 2 (by rfl) ⟨2364774, by rfl⟩ : syracuseStep 6306065 = 4729549) B4729549
theorem B3152209 : Blo 1867635 3152209 := bstep (se 2 (by rfl) ⟨1182078, by rfl⟩ : syracuseStep 3152209 = 2364157) B2364157
theorem B7092593 : Blo 1867635 7092593 := bstep (se 2 (by rfl) ⟨2659722, by rfl⟩ : syracuseStep 7092593 = 5319445) B5319445
theorem B3152243 : Blo 1867635 3152243 := bstep (se 1 (by rfl) ⟨2364182, by rfl⟩ : syracuseStep 3152243 = 4728365) B4728365
theorem B2365843 : Blo 1867635 2365843 := bstep (se 1 (by rfl) ⟨1774382, by rfl⟩ : syracuseStep 2365843 = 3548765) B3548765
theorem B5323249 : Blo 1867635 5323249 := bstep (se 2 (by rfl) ⟨1996218, by rfl⟩ : syracuseStep 5323249 = 3992437) B3992437
theorem B3152371 : Blo 1867635 3152371 := bstep (se 1 (by rfl) ⟨2364278, by rfl⟩ : syracuseStep 3152371 = 4728557) B4728557
theorem B2365939 : Blo 1867635 2365939 := bstep (se 1 (by rfl) ⟨1774454, by rfl⟩ : syracuseStep 2365939 = 3548909) B3548909
theorem B3152513 : Blo 1867635 3152513 := bstep (se 2 (by rfl) ⟨1182192, by rfl⟩ : syracuseStep 3152513 = 2364385) B2364385
theorem B3545795 : Blo 1867635 3545795 := bstep (se 1 (by rfl) ⟨2659346, by rfl⟩ : syracuseStep 3545795 = 5318693) B5318693
theorem B3152641 : Blo 1867635 3152641 := bstep (se 2 (by rfl) ⟨1182240, by rfl⟩ : syracuseStep 3152641 = 2364481) B2364481
theorem B3152675 : Blo 1867635 3152675 := bstep (se 1 (by rfl) ⟨2364506, by rfl⟩ : syracuseStep 3152675 = 4729013) B4729013
theorem B6306605 : Blo 1867635 6306605 := bstep (se 3 (by rfl) ⟨1182488, by rfl⟩ : syracuseStep 6306605 = 2364977) B2364977
theorem B2661169 : Blo 1867635 2661169 := bstep (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) B1995877
theorem B6306659 : Blo 1867635 6306659 := bstep (se 1 (by rfl) ⟨4729994, by rfl⟩ : syracuseStep 6306659 = 9459989) B9459989
theorem B3152803 : Blo 1867635 3152803 := bstep (se 1 (by rfl) ⟨2364602, by rfl⟩ : syracuseStep 3152803 = 4729205) B4729205
theorem B2661283 : Blo 1867635 2661283 := bstep (se 1 (by rfl) ⟨1995962, by rfl⟩ : syracuseStep 2661283 = 3991925) B3991925
theorem B3152945 : Blo 1867635 3152945 := bstep (se 2 (by rfl) ⟨1182354, by rfl⟩ : syracuseStep 3152945 = 2364709) B2364709
theorem B6306929 : Blo 1867635 6306929 := bstep (se 2 (by rfl) ⟨2365098, by rfl⟩ : syracuseStep 6306929 = 4730197) B4730197
theorem B2243747 : Blo 1867635 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B3153073 : Blo 1867635 3153073 := bstep (se 2 (by rfl) ⟨1182402, by rfl⟩ : syracuseStep 3153073 = 2364805) B2364805
theorem B15154373 : Blo 1867635 15154373 := bstep (se 4 (by rfl) ⟨1420722, by rfl⟩ : syracuseStep 15154373 = 2841445) B2841445
theorem B3153107 : Blo 1867635 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B10640645 : Blo 1867635 10640645 := bstep (se 4 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 10640645 = 1995121) B1995121
theorem B3153235 : Blo 1867635 3153235 := bstep (se 1 (by rfl) ⟨2364926, by rfl⟩ : syracuseStep 3153235 = 4729853) B4729853
theorem B11967857 : Blo 1867635 11967857 := bstep (se 2 (by rfl) ⟨4487946, by rfl⟩ : syracuseStep 11967857 = 8975893) B8975893
theorem B15957445 : Blo 1867635 15957445 := bstep (se 4 (by rfl) ⟨1496010, by rfl⟩ : syracuseStep 15957445 = 2992021) B2992021
theorem B11976133 : Blo 1867635 11976133 := bstep (se 4 (by rfl) ⟨1122762, by rfl⟩ : syracuseStep 11976133 = 2245525) B2245525
theorem B3153377 : Blo 1867635 3153377 := bstep (se 2 (by rfl) ⟨1182516, by rfl⟩ : syracuseStep 3153377 = 2365033) B2365033
theorem B7577059 : Blo 1867635 7577059 := bstep (se 1 (by rfl) ⟨5682794, by rfl⟩ : syracuseStep 7577059 = 11365589) B11365589
theorem B3153505 : Blo 1867635 3153505 := bstep (se 2 (by rfl) ⟨1182564, by rfl⟩ : syracuseStep 3153505 = 2365129) B2365129
theorem B3546737 : Blo 1867635 3546737 := bstep (se 2 (by rfl) ⟨1330026, by rfl⟩ : syracuseStep 3546737 = 2660053) B2660053
theorem B3153539 : Blo 1867635 3153539 := bstep (se 1 (by rfl) ⟨2365154, by rfl⟩ : syracuseStep 3153539 = 4730309) B4730309
theorem B6307469 : Blo 1867635 6307469 := bstep (se 3 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 6307469 = 2365301) B2365301
theorem B6307523 : Blo 1867635 6307523 := bstep (se 1 (by rfl) ⟨4730642, by rfl⟩ : syracuseStep 6307523 = 9461285) B9461285
theorem B4202225 : Blo 1867635 4202225 := bstep (se 2 (by rfl) ⟨1575834, by rfl⟩ : syracuseStep 4202225 = 3151669) B3151669
theorem B4202243 : Blo 1867635 4202243 := bstep (se 1 (by rfl) ⟨3151682, by rfl⟩ : syracuseStep 4202243 = 6303365) B6303365
theorem B3366659 : Blo 1867635 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B3153667 : Blo 1867635 3153667 := bstep (se 1 (by rfl) ⟨2365250, by rfl⟩ : syracuseStep 3153667 = 4730501) B4730501
theorem B3194657 : Blo 1867635 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B7094051 : Blo 1867635 7094051 := bstep (se 1 (by rfl) ⟨5320538, by rfl⟩ : syracuseStep 7094051 = 10641077) B10641077
theorem B3596081 : Blo 1867635 3596081 := bstep (se 2 (by rfl) ⟨1348530, by rfl⟩ : syracuseStep 3596081 = 2697061) B2697061
theorem B2801459 : Blo 1867635 2801459 := bstep (se 1 (by rfl) ⟨2101094, by rfl⟩ : syracuseStep 2801459 = 4202189) B4202189
theorem B2801489 : Blo 1867635 2801489 := bstep (se 2 (by rfl) ⟨1050558, by rfl⟩ : syracuseStep 2801489 = 2101117) B2101117
theorem B2801507 : Blo 1867635 2801507 := bstep (se 1 (by rfl) ⟨2101130, by rfl⟩ : syracuseStep 2801507 = 4202261) B4202261
theorem B1867635 : Blo 1867635 1867635 := bstep (se 1 (by rfl) ⟨1400726, by rfl⟩ : syracuseStep 1867635 = 2801453) B2801453
theorem B2801537 : Blo 1867635 2801537 := bstep (se 2 (by rfl) ⟨1050576, by rfl⟩ : syracuseStep 2801537 = 2101153) B2101153
theorem B1867651 : Blo 1867635 1867651 := bstep (se 1 (by rfl) ⟨1400738, by rfl⟩ : syracuseStep 1867651 = 2801477) B2801477
theorem B3153809 : Blo 1867635 3153809 := bstep (se 2 (by rfl) ⟨1182678, by rfl⟩ : syracuseStep 3153809 = 2365357) B2365357
theorem B1867667 : Blo 1867635 1867667 := bstep (se 1 (by rfl) ⟨1400750, by rfl⟩ : syracuseStep 1867667 = 2801501) B2801501
theorem B2801555 : Blo 1867635 2801555 := bstep (se 1 (by rfl) ⟨2101166, by rfl⟩ : syracuseStep 2801555 = 4202333) B4202333
theorem B1867683 : Blo 1867635 1867683 := bstep (se 1 (by rfl) ⟨1400762, by rfl⟩ : syracuseStep 1867683 = 2801525) B2801525
theorem B2801585 : Blo 1867635 2801585 := bstep (se 2 (by rfl) ⟨1050594, by rfl⟩ : syracuseStep 2801585 = 2101189) B2101189
theorem B1867699 : Blo 1867635 1867699 := bstep (se 1 (by rfl) ⟨1400774, by rfl⟩ : syracuseStep 1867699 = 2801549) B2801549
theorem B1867715 : Blo 1867635 1867715 := bstep (se 1 (by rfl) ⟨1400786, by rfl⟩ : syracuseStep 1867715 = 2801573) B2801573
theorem B2801603 : Blo 1867635 2801603 := bstep (se 1 (by rfl) ⟨2101202, by rfl⟩ : syracuseStep 2801603 = 4202405) B4202405
theorem B6307793 : Blo 1867635 6307793 := bstep (se 2 (by rfl) ⟨2365422, by rfl⟩ : syracuseStep 6307793 = 4730845) B4730845
theorem B1867731 : Blo 1867635 1867731 := bstep (se 1 (by rfl) ⟨1400798, by rfl⟩ : syracuseStep 1867731 = 2801597) B2801597
theorem B2801633 : Blo 1867635 2801633 := bstep (se 2 (by rfl) ⟨1050612, by rfl⟩ : syracuseStep 2801633 = 2101225) B2101225
theorem B3194849 : Blo 1867635 3194849 := bstep (se 2 (by rfl) ⟨1198068, by rfl⟩ : syracuseStep 3194849 = 2396137) B2396137
theorem B1867747 : Blo 1867635 1867747 := bstep (se 1 (by rfl) ⟨1400810, by rfl⟩ : syracuseStep 1867747 = 2801621) B2801621
theorem B3366883 : Blo 1867635 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B15966193 : Blo 1867635 15966193 := bstep (se 2 (by rfl) ⟨5987322, by rfl⟩ : syracuseStep 15966193 = 11974645) B11974645
theorem B1867763 : Blo 1867635 1867763 := bstep (se 1 (by rfl) ⟨1400822, by rfl⟩ : syracuseStep 1867763 = 2801645) B2801645
theorem B2801651 : Blo 1867635 2801651 := bstep (se 1 (by rfl) ⟨2101238, by rfl⟩ : syracuseStep 2801651 = 4202477) B4202477
theorem B2801675 : Blo 1867635 2801675 := bstep (se 1 (by rfl) ⟨2101256, by rfl⟩ : syracuseStep 2801675 = 4202513) B4202513
theorem B1867787 : Blo 1867635 1867787 := bstep (se 1 (by rfl) ⟨1400840, by rfl⟩ : syracuseStep 1867787 = 2801681) B2801681
theorem B3547147 : Blo 1867635 3547147 := bstep (se 1 (by rfl) ⟨2660360, by rfl⟩ : syracuseStep 3547147 = 5320721) B5320721
theorem B2801687 : Blo 1867635 2801687 := bstep (se 1 (by rfl) ⟨2101265, by rfl⟩ : syracuseStep 2801687 = 4202531) B4202531
theorem B1867799 : Blo 1867635 1867799 := bstep (se 1 (by rfl) ⟨1400849, by rfl⟩ : syracuseStep 1867799 = 2801699) B2801699
theorem B1867819 : Blo 1867635 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B1867831 : Blo 1867635 1867831 := bstep (se 1 (by rfl) ⟨1400873, by rfl⟩ : syracuseStep 1867831 = 2801747) B2801747
theorem B1867851 : Blo 1867635 1867851 := bstep (se 1 (by rfl) ⟨1400888, by rfl⟩ : syracuseStep 1867851 = 2801777) B2801777
theorem B1867863 : Blo 1867635 1867863 := bstep (se 1 (by rfl) ⟨1400897, by rfl⟩ : syracuseStep 1867863 = 2801795) B2801795
theorem B3547223 : Blo 1867635 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B4202585 : Blo 1867635 4202585 := bstep (se 2 (by rfl) ⟨1575969, by rfl⟩ : syracuseStep 4202585 = 3151939) B3151939
theorem B2801753 : Blo 1867635 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B1867883 : Blo 1867635 1867883 := bstep (se 1 (by rfl) ⟨1400912, by rfl⟩ : syracuseStep 1867883 = 2801825) B2801825
theorem B1867895 : Blo 1867635 1867895 := bstep (se 1 (by rfl) ⟨1400921, by rfl⟩ : syracuseStep 1867895 = 2801843) B2801843
theorem B1867915 : Blo 1867635 1867915 := bstep (se 1 (by rfl) ⟨1400936, by rfl⟩ : syracuseStep 1867915 = 2801873) B2801873
theorem B1867927 : Blo 1867635 1867927 := bstep (se 1 (by rfl) ⟨1400945, by rfl⟩ : syracuseStep 1867927 = 2801891) B2801891
theorem B1867947 : Blo 1867635 1867947 := bstep (se 1 (by rfl) ⟨1400960, by rfl⟩ : syracuseStep 1867947 = 2801921) B2801921
theorem B4202675 : Blo 1867635 4202675 := bstep (se 1 (by rfl) ⟨3152006, by rfl⟩ : syracuseStep 4202675 = 6304013) B6304013
theorem B1867959 : Blo 1867635 1867959 := bstep (se 1 (by rfl) ⟨1400969, by rfl⟩ : syracuseStep 1867959 = 2801939) B2801939
theorem B2801867 : Blo 1867635 2801867 := bstep (se 1 (by rfl) ⟨2101400, by rfl⟩ : syracuseStep 2801867 = 4202801) B4202801
theorem B1867979 : Blo 1867635 1867979 := bstep (se 1 (by rfl) ⟨1400984, by rfl⟩ : syracuseStep 1867979 = 2801969) B2801969
theorem B4202711 : Blo 1867635 4202711 := bstep (se 1 (by rfl) ⟨3152033, by rfl⟩ : syracuseStep 4202711 = 6304067) B6304067
theorem B2801879 : Blo 1867635 2801879 := bstep (se 1 (by rfl) ⟨2101409, by rfl⟩ : syracuseStep 2801879 = 4202819) B4202819
theorem B1867991 : Blo 1867635 1867991 := bstep (se 1 (by rfl) ⟨1400993, by rfl⟩ : syracuseStep 1867991 = 2801987) B2801987
theorem B1868011 : Blo 1867635 1868011 := bstep (se 1 (by rfl) ⟨1401008, by rfl⟩ : syracuseStep 1868011 = 2802017) B2802017
theorem B1868023 : Blo 1867635 1868023 := bstep (se 1 (by rfl) ⟨1401017, by rfl⟩ : syracuseStep 1868023 = 2802035) B2802035
theorem B1868043 : Blo 1867635 1868043 := bstep (se 1 (by rfl) ⟨1401032, by rfl⟩ : syracuseStep 1868043 = 2802065) B2802065
theorem B3154187 : Blo 1867635 3154187 := bstep (se 1 (by rfl) ⟨2365640, by rfl⟩ : syracuseStep 3154187 = 4731281) B4731281
theorem B1868055 : Blo 1867635 1868055 := bstep (se 1 (by rfl) ⟨1401041, by rfl⟩ : syracuseStep 1868055 = 2802083) B2802083
theorem B2801945 : Blo 1867635 2801945 := bstep (se 2 (by rfl) ⟨1050729, by rfl⟩ : syracuseStep 2801945 = 2101459) B2101459
theorem B1868075 : Blo 1867635 1868075 := bstep (se 1 (by rfl) ⟨1401056, by rfl⟩ : syracuseStep 1868075 = 2802113) B2802113
theorem B1868087 : Blo 1867635 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B20209985 : Blo 1867635 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B1868107 : Blo 1867635 1868107 := bstep (se 1 (by rfl) ⟨1401080, by rfl⟩ : syracuseStep 1868107 = 2802161) B2802161
theorem B6308171 : Blo 1867635 6308171 := bstep (se 1 (by rfl) ⟨4731128, by rfl⟩ : syracuseStep 6308171 = 9462257) B9462257
theorem B1868119 : Blo 1867635 1868119 := bstep (se 1 (by rfl) ⟨1401089, by rfl⟩ : syracuseStep 1868119 = 2802179) B2802179
theorem B1868139 : Blo 1867635 1868139 := bstep (se 1 (by rfl) ⟨1401104, by rfl⟩ : syracuseStep 1868139 = 2802209) B2802209
theorem B1868151 : Blo 1867635 1868151 := bstep (se 1 (by rfl) ⟨1401113, by rfl⟩ : syracuseStep 1868151 = 2802227) B2802227
theorem B15958403 : Blo 1867635 15958403 := bstep (se 1 (by rfl) ⟨11968802, by rfl⟩ : syracuseStep 15958403 = 23937605) B23937605
theorem B4202891 : Blo 1867635 4202891 := bstep (se 1 (by rfl) ⟨3152168, by rfl⟩ : syracuseStep 4202891 = 6304337) B6304337
theorem B2802059 : Blo 1867635 2802059 := bstep (se 1 (by rfl) ⟨2101544, by rfl⟩ : syracuseStep 2802059 = 4203089) B4203089
theorem B1868171 : Blo 1867635 1868171 := bstep (se 1 (by rfl) ⟨1401128, by rfl⟩ : syracuseStep 1868171 = 2802257) B2802257
theorem B3154315 : Blo 1867635 3154315 := bstep (se 1 (by rfl) ⟨2365736, by rfl⟩ : syracuseStep 3154315 = 4731473) B4731473
theorem B2802071 : Blo 1867635 2802071 := bstep (se 1 (by rfl) ⟨2101553, by rfl⟩ : syracuseStep 2802071 = 4203107) B4203107
theorem B1868183 : Blo 1867635 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B1868203 : Blo 1867635 1868203 := bstep (se 1 (by rfl) ⟨1401152, by rfl⟩ : syracuseStep 1868203 = 2802305) B2802305
theorem B1868215 : Blo 1867635 1868215 := bstep (se 1 (by rfl) ⟨1401161, by rfl⟩ : syracuseStep 1868215 = 2802323) B2802323
theorem B4202945 : Blo 1867635 4202945 := bstep (se 2 (by rfl) ⟨1576104, by rfl⟩ : syracuseStep 4202945 = 3152209) B3152209
theorem B1868235 : Blo 1867635 1868235 := bstep (se 1 (by rfl) ⟨1401176, by rfl⟩ : syracuseStep 1868235 = 2802353) B2802353
theorem B1868247 : Blo 1867635 1868247 := bstep (se 1 (by rfl) ⟨1401185, by rfl⟩ : syracuseStep 1868247 = 2802371) B2802371
theorem B2802137 : Blo 1867635 2802137 := bstep (se 2 (by rfl) ⟨1050801, by rfl⟩ : syracuseStep 2802137 = 2101603) B2101603
theorem B6734297 : Blo 1867635 6734297 := bstep (se 2 (by rfl) ⟨2525361, by rfl⟩ : syracuseStep 6734297 = 5050723) B5050723
theorem B7094749 : Blo 1867635 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B1868267 : Blo 1867635 1868267 := bstep (se 1 (by rfl) ⟨1401200, by rfl⟩ : syracuseStep 1868267 = 2802401) B2802401
theorem B1868279 : Blo 1867635 1868279 := bstep (se 1 (by rfl) ⟨1401209, by rfl⟩ : syracuseStep 1868279 = 2802419) B2802419
theorem B1868299 : Blo 1867635 1868299 := bstep (se 1 (by rfl) ⟨1401224, by rfl⟩ : syracuseStep 1868299 = 2802449) B2802449
theorem B11518481 : Blo 1867635 11518481 := bstep (se 2 (by rfl) ⟨4319430, by rfl⟩ : syracuseStep 11518481 = 8638861) B8638861
theorem B7979543 : Blo 1867635 7979543 := bstep (se 1 (by rfl) ⟨5984657, by rfl⟩ : syracuseStep 7979543 = 11969315) B11969315
theorem B1868311 : Blo 1867635 1868311 := bstep (se 1 (by rfl) ⟨1401233, by rfl⟩ : syracuseStep 1868311 = 2802467) B2802467
theorem B3154457 : Blo 1867635 3154457 := bstep (se 2 (by rfl) ⟨1182921, by rfl⟩ : syracuseStep 3154457 = 2365843) B2365843
theorem B1868331 : Blo 1867635 1868331 := bstep (se 1 (by rfl) ⟨1401248, by rfl⟩ : syracuseStep 1868331 = 2802497) B2802497
theorem B1868343 : Blo 1867635 1868343 := bstep (se 1 (by rfl) ⟨1401257, by rfl⟩ : syracuseStep 1868343 = 2802515) B2802515
theorem B4489793 : Blo 1867635 4489793 := bstep (se 2 (by rfl) ⟨1683672, by rfl⟩ : syracuseStep 4489793 = 3367345) B3367345
theorem B2802251 : Blo 1867635 2802251 := bstep (se 1 (by rfl) ⟨2101688, by rfl⟩ : syracuseStep 2802251 = 4203377) B4203377
theorem B1868363 : Blo 1867635 1868363 := bstep (se 1 (by rfl) ⟨1401272, by rfl⟩ : syracuseStep 1868363 = 2802545) B2802545
theorem B2802263 : Blo 1867635 2802263 := bstep (se 1 (by rfl) ⟨2101697, by rfl⟩ : syracuseStep 2802263 = 4203395) B4203395
theorem B1868375 : Blo 1867635 1868375 := bstep (se 1 (by rfl) ⟨1401281, by rfl⟩ : syracuseStep 1868375 = 2802563) B2802563
theorem B6308441 : Blo 1867635 6308441 := bstep (se 2 (by rfl) ⟨2365665, by rfl⟩ : syracuseStep 6308441 = 4731331) B4731331
theorem B1868395 : Blo 1867635 1868395 := bstep (se 1 (by rfl) ⟨1401296, by rfl⟩ : syracuseStep 1868395 = 2802593) B2802593
theorem B3990131 : Blo 1867635 3990131 := bstep (se 1 (by rfl) ⟨2992598, by rfl⟩ : syracuseStep 3990131 = 5985197) B5985197
theorem B1868407 : Blo 1867635 1868407 := bstep (se 1 (by rfl) ⟨1401305, by rfl⟩ : syracuseStep 1868407 = 2802611) B2802611
theorem B4260481 : Blo 1867635 4260481 := bstep (se 2 (by rfl) ⟨1597680, by rfl⟩ : syracuseStep 4260481 = 3195361) B3195361
theorem B1868427 : Blo 1867635 1868427 := bstep (se 1 (by rfl) ⟨1401320, by rfl⟩ : syracuseStep 1868427 = 2802641) B2802641
theorem B1868439 : Blo 1867635 1868439 := bstep (se 1 (by rfl) ⟨1401329, by rfl⟩ : syracuseStep 1868439 = 2802659) B2802659
theorem B4203161 : Blo 1867635 4203161 := bstep (se 2 (by rfl) ⟨1576185, by rfl⟩ : syracuseStep 4203161 = 3152371) B3152371
theorem B2802329 : Blo 1867635 2802329 := bstep (se 2 (by rfl) ⟨1050873, by rfl⟩ : syracuseStep 2802329 = 2101747) B2101747
theorem B3154585 : Blo 1867635 3154585 := bstep (se 2 (by rfl) ⟨1182969, by rfl⟩ : syracuseStep 3154585 = 2365939) B2365939
theorem B1868459 : Blo 1867635 1868459 := bstep (se 1 (by rfl) ⟨1401344, by rfl⟩ : syracuseStep 1868459 = 2802689) B2802689
theorem B1868471 : Blo 1867635 1868471 := bstep (se 1 (by rfl) ⟨1401353, by rfl⟩ : syracuseStep 1868471 = 2802707) B2802707
theorem B1868491 : Blo 1867635 1868491 := bstep (se 1 (by rfl) ⟨1401368, by rfl⟩ : syracuseStep 1868491 = 2802737) B2802737
theorem B1868503 : Blo 1867635 1868503 := bstep (se 1 (by rfl) ⟨1401377, by rfl⟩ : syracuseStep 1868503 = 2802755) B2802755
theorem B1868523 : Blo 1867635 1868523 := bstep (se 1 (by rfl) ⟨1401392, by rfl⟩ : syracuseStep 1868523 = 2802785) B2802785
theorem B4203251 : Blo 1867635 4203251 := bstep (se 1 (by rfl) ⟨3152438, by rfl⟩ : syracuseStep 4203251 = 6304877) B6304877
theorem B1868535 : Blo 1867635 1868535 := bstep (se 1 (by rfl) ⟨1401401, by rfl⟩ : syracuseStep 1868535 = 2802803) B2802803
theorem B3547891 : Blo 1867635 3547891 := bstep (se 1 (by rfl) ⟨2660918, by rfl⟩ : syracuseStep 3547891 = 5321837) B5321837
theorem B30302981 : Blo 1867635 30302981 := bstep (se 4 (by rfl) ⟨2840904, by rfl⟩ : syracuseStep 30302981 = 5681809) B5681809
theorem B2802443 : Blo 1867635 2802443 := bstep (se 1 (by rfl) ⟨2101832, by rfl⟩ : syracuseStep 2802443 = 4203665) B4203665
theorem B1868555 : Blo 1867635 1868555 := bstep (se 1 (by rfl) ⟨1401416, by rfl⟩ : syracuseStep 1868555 = 2802833) B2802833
theorem B4203287 : Blo 1867635 4203287 := bstep (se 1 (by rfl) ⟨3152465, by rfl⟩ : syracuseStep 4203287 = 6304931) B6304931
theorem B2802455 : Blo 1867635 2802455 := bstep (se 1 (by rfl) ⟨2101841, by rfl⟩ : syracuseStep 2802455 = 4203683) B4203683
theorem B1868567 : Blo 1867635 1868567 := bstep (se 1 (by rfl) ⟨1401425, by rfl⟩ : syracuseStep 1868567 = 2802851) B2802851
theorem B1868587 : Blo 1867635 1868587 := bstep (se 1 (by rfl) ⟨1401440, by rfl⟩ : syracuseStep 1868587 = 2802881) B2802881
theorem B1868599 : Blo 1867635 1868599 := bstep (se 1 (by rfl) ⟨1401449, by rfl⟩ : syracuseStep 1868599 = 2802899) B2802899
theorem B8979275 : Blo 1867635 8979275 := bstep (se 1 (by rfl) ⟨6734456, by rfl⟩ : syracuseStep 8979275 = 13468913) B13468913
theorem B1868619 : Blo 1867635 1868619 := bstep (se 1 (by rfl) ⟨1401464, by rfl⟩ : syracuseStep 1868619 = 2802929) B2802929
theorem B1868631 : Blo 1867635 1868631 := bstep (se 1 (by rfl) ⟨1401473, by rfl⟩ : syracuseStep 1868631 = 2802947) B2802947
theorem B2802521 : Blo 1867635 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1868651 : Blo 1867635 1868651 := bstep (se 1 (by rfl) ⟨1401488, by rfl⟩ : syracuseStep 1868651 = 2802977) B2802977
theorem B1868663 : Blo 1867635 1868663 := bstep (se 1 (by rfl) ⟨1401497, by rfl⟩ : syracuseStep 1868663 = 2802995) B2802995
theorem B1868683 : Blo 1867635 1868683 := bstep (se 1 (by rfl) ⟨1401512, by rfl⟩ : syracuseStep 1868683 = 2803025) B2803025
theorem B1868695 : Blo 1867635 1868695 := bstep (se 1 (by rfl) ⟨1401521, by rfl⟩ : syracuseStep 1868695 = 2803043) B2803043
theorem B1868715 : Blo 1867635 1868715 := bstep (se 1 (by rfl) ⟨1401536, by rfl⟩ : syracuseStep 1868715 = 2803073) B2803073
theorem B1868727 : Blo 1867635 1868727 := bstep (se 1 (by rfl) ⟨1401545, by rfl⟩ : syracuseStep 1868727 = 2803091) B2803091
theorem B4203467 : Blo 1867635 4203467 := bstep (se 1 (by rfl) ⟨3152600, by rfl⟩ : syracuseStep 4203467 = 6305201) B6305201
theorem B2802635 : Blo 1867635 2802635 := bstep (se 1 (by rfl) ⟨2101976, by rfl⟩ : syracuseStep 2802635 = 4203953) B4203953
theorem B1868747 : Blo 1867635 1868747 := bstep (se 1 (by rfl) ⟨1401560, by rfl⟩ : syracuseStep 1868747 = 2803121) B2803121
theorem B1867767 : Blo 1867635 1867767 := bstep (se 1 (by rfl) ⟨1400825, by rfl⟩ : syracuseStep 1867767 = 2801651) B2801651
theorem B2802647 : Blo 1867635 2802647 := bstep (se 1 (by rfl) ⟨2101985, by rfl⟩ : syracuseStep 2802647 = 4203971) B4203971
theorem B1868759 : Blo 1867635 1868759 := bstep (se 1 (by rfl) ⟨1401569, by rfl⟩ : syracuseStep 1868759 = 2803139) B2803139
theorem B3548119 : Blo 1867635 3548119 := bstep (se 1 (by rfl) ⟨2661089, by rfl⟩ : syracuseStep 3548119 = 5322179) B5322179
theorem B1868779 : Blo 1867635 1868779 := bstep (se 1 (by rfl) ⟨1401584, by rfl⟩ : syracuseStep 1868779 = 2803169) B2803169
theorem B1868791 : Blo 1867635 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B4203521 : Blo 1867635 4203521 := bstep (se 2 (by rfl) ⟨1576320, by rfl⟩ : syracuseStep 4203521 = 3152641) B3152641
theorem B1868811 : Blo 1867635 1868811 := bstep (se 1 (by rfl) ⟨1401608, by rfl⟩ : syracuseStep 1868811 = 2803217) B2803217
theorem B1868823 : Blo 1867635 1868823 := bstep (se 1 (by rfl) ⟨1401617, by rfl⟩ : syracuseStep 1868823 = 2803235) B2803235
theorem B2802713 : Blo 1867635 2802713 := bstep (se 2 (by rfl) ⟨1051017, by rfl⟩ : syracuseStep 2802713 = 2102035) B2102035
theorem B1868843 : Blo 1867635 1868843 := bstep (se 1 (by rfl) ⟨1401632, by rfl⟩ : syracuseStep 1868843 = 2803265) B2803265
theorem B1868855 : Blo 1867635 1868855 := bstep (se 1 (by rfl) ⟨1401641, by rfl⟩ : syracuseStep 1868855 = 2803283) B2803283
theorem B3548225 : Blo 1867635 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B1868875 : Blo 1867635 1868875 := bstep (se 1 (by rfl) ⟨1401656, by rfl⟩ : syracuseStep 1868875 = 2803313) B2803313
theorem B1868887 : Blo 1867635 1868887 := bstep (se 1 (by rfl) ⟨1401665, by rfl⟩ : syracuseStep 1868887 = 2803331) B2803331
theorem B1868907 : Blo 1867635 1868907 := bstep (se 1 (by rfl) ⟨1401680, by rfl⟩ : syracuseStep 1868907 = 2803361) B2803361
theorem B1868919 : Blo 1867635 1868919 := bstep (se 1 (by rfl) ⟨1401689, by rfl⟩ : syracuseStep 1868919 = 2803379) B2803379
theorem B9847939 : Blo 1867635 9847939 := bstep (se 1 (by rfl) ⟨7385954, by rfl⟩ : syracuseStep 9847939 = 14771909) B14771909
theorem B1893515 : Blo 1867635 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B2802827 : Blo 1867635 2802827 := bstep (se 1 (by rfl) ⟨2102120, by rfl⟩ : syracuseStep 2802827 = 4204241) B4204241
theorem B1868939 : Blo 1867635 1868939 := bstep (se 1 (by rfl) ⟨1401704, by rfl⟩ : syracuseStep 1868939 = 2803409) B2803409
theorem B2802839 : Blo 1867635 2802839 := bstep (se 1 (by rfl) ⟨2102129, by rfl⟩ : syracuseStep 2802839 = 4204259) B4204259
theorem B1868951 : Blo 1867635 1868951 := bstep (se 1 (by rfl) ⟨1401713, by rfl⟩ : syracuseStep 1868951 = 2803427) B2803427
theorem B1868971 : Blo 1867635 1868971 := bstep (se 1 (by rfl) ⟨1401728, by rfl⟩ : syracuseStep 1868971 = 2803457) B2803457
theorem B1868983 : Blo 1867635 1868983 := bstep (se 1 (by rfl) ⟨1401737, by rfl⟩ : syracuseStep 1868983 = 2803475) B2803475
theorem B3990721 : Blo 1867635 3990721 := bstep (se 2 (by rfl) ⟨1496520, by rfl⟩ : syracuseStep 3990721 = 2993041) B2993041
theorem B1869003 : Blo 1867635 1869003 := bstep (se 1 (by rfl) ⟨1401752, by rfl⟩ : syracuseStep 1869003 = 2803505) B2803505
theorem B1869015 : Blo 1867635 1869015 := bstep (se 1 (by rfl) ⟨1401761, by rfl⟩ : syracuseStep 1869015 = 2803523) B2803523
theorem B4203737 : Blo 1867635 4203737 := bstep (se 2 (by rfl) ⟨1576401, by rfl⟩ : syracuseStep 4203737 = 3152803) B3152803
theorem B2802905 : Blo 1867635 2802905 := bstep (se 2 (by rfl) ⟨1051089, by rfl⟩ : syracuseStep 2802905 = 2102179) B2102179
theorem B3548377 : Blo 1867635 3548377 := bstep (se 2 (by rfl) ⟨1330641, by rfl⟩ : syracuseStep 3548377 = 2661283) B2661283
theorem B1869035 : Blo 1867635 1869035 := bstep (se 1 (by rfl) ⟨1401776, by rfl⟩ : syracuseStep 1869035 = 2803553) B2803553
theorem B1869047 : Blo 1867635 1869047 := bstep (se 1 (by rfl) ⟨1401785, by rfl⟩ : syracuseStep 1869047 = 2803571) B2803571
theorem B1869067 : Blo 1867635 1869067 := bstep (se 1 (by rfl) ⟨1401800, by rfl⟩ : syracuseStep 1869067 = 2803601) B2803601
theorem B1869079 : Blo 1867635 1869079 := bstep (se 1 (by rfl) ⟨1401809, by rfl⟩ : syracuseStep 1869079 = 2803619) B2803619
theorem B6309143 : Blo 1867635 6309143 := bstep (se 1 (by rfl) ⟨4731857, by rfl⟩ : syracuseStep 6309143 = 9463715) B9463715
theorem B1869099 : Blo 1867635 1869099 := bstep (se 1 (by rfl) ⟨1401824, by rfl⟩ : syracuseStep 1869099 = 2803649) B2803649
theorem B4203827 : Blo 1867635 4203827 := bstep (se 1 (by rfl) ⟨3152870, by rfl⟩ : syracuseStep 4203827 = 6305741) B6305741
theorem B1869111 : Blo 1867635 1869111 := bstep (se 1 (by rfl) ⟨1401833, by rfl⟩ : syracuseStep 1869111 = 2803667) B2803667
theorem B4490561 : Blo 1867635 4490561 := bstep (se 2 (by rfl) ⟨1683960, by rfl⟩ : syracuseStep 4490561 = 3367921) B3367921
theorem B2803019 : Blo 1867635 2803019 := bstep (se 1 (by rfl) ⟨2102264, by rfl⟩ : syracuseStep 2803019 = 4204529) B4204529
theorem B1869131 : Blo 1867635 1869131 := bstep (se 1 (by rfl) ⟨1401848, by rfl⟩ : syracuseStep 1869131 = 2803697) B2803697
theorem B4203863 : Blo 1867635 4203863 := bstep (se 1 (by rfl) ⟨3152897, by rfl⟩ : syracuseStep 4203863 = 6305795) B6305795
theorem B2803031 : Blo 1867635 2803031 := bstep (se 1 (by rfl) ⟨2102273, by rfl⟩ : syracuseStep 2803031 = 4204547) B4204547
theorem B1869143 : Blo 1867635 1869143 := bstep (se 1 (by rfl) ⟨1401857, by rfl⟩ : syracuseStep 1869143 = 2803715) B2803715
theorem B1869163 : Blo 1867635 1869163 := bstep (se 1 (by rfl) ⟨1401872, by rfl⟩ : syracuseStep 1869163 = 2803745) B2803745
theorem B1869175 : Blo 1867635 1869175 := bstep (se 1 (by rfl) ⟨1401881, by rfl⟩ : syracuseStep 1869175 = 2803763) B2803763
theorem B5988887 : Blo 1867635 5988887 := bstep (se 1 (by rfl) ⟨4491665, by rfl⟩ : syracuseStep 5988887 = 8983331) B8983331
theorem B1869195 : Blo 1867635 1869195 := bstep (se 1 (by rfl) ⟨1401896, by rfl⟩ : syracuseStep 1869195 = 2803793) B2803793
theorem B1869207 : Blo 1867635 1869207 := bstep (se 1 (by rfl) ⟨1401905, by rfl⟩ : syracuseStep 1869207 = 2803811) B2803811
theorem B2803097 : Blo 1867635 2803097 := bstep (se 2 (by rfl) ⟨1051161, by rfl⟩ : syracuseStep 2803097 = 2102323) B2102323
theorem B1869227 : Blo 1867635 1869227 := bstep (se 1 (by rfl) ⟨1401920, by rfl⟩ : syracuseStep 1869227 = 2803841) B2803841
theorem B1869239 : Blo 1867635 1869239 := bstep (se 1 (by rfl) ⟨1401929, by rfl⟩ : syracuseStep 1869239 = 2803859) B2803859
theorem B1869259 : Blo 1867635 1869259 := bstep (se 1 (by rfl) ⟨1401944, by rfl⟩ : syracuseStep 1869259 = 2803889) B2803889
theorem B1869271 : Blo 1867635 1869271 := bstep (se 1 (by rfl) ⟨1401953, by rfl⟩ : syracuseStep 1869271 = 2803907) B2803907
theorem B1869291 : Blo 1867635 1869291 := bstep (se 1 (by rfl) ⟨1401968, by rfl⟩ : syracuseStep 1869291 = 2803937) B2803937
theorem B1869303 : Blo 1867635 1869303 := bstep (se 1 (by rfl) ⟨1401977, by rfl⟩ : syracuseStep 1869303 = 2803955) B2803955
theorem B4204043 : Blo 1867635 4204043 := bstep (se 1 (by rfl) ⟨3153032, by rfl⟩ : syracuseStep 4204043 = 6306065) B6306065
theorem B2803211 : Blo 1867635 2803211 := bstep (se 1 (by rfl) ⟨2102408, by rfl⟩ : syracuseStep 2803211 = 4204817) B4204817
theorem B1869323 : Blo 1867635 1869323 := bstep (se 1 (by rfl) ⟨1401992, by rfl⟩ : syracuseStep 1869323 = 2803985) B2803985
theorem B2803223 : Blo 1867635 2803223 := bstep (se 1 (by rfl) ⟨2102417, by rfl⟩ : syracuseStep 2803223 = 4204835) B4204835
theorem B1869335 : Blo 1867635 1869335 := bstep (se 1 (by rfl) ⟨1402001, by rfl⟩ : syracuseStep 1869335 = 2804003) B2804003
theorem B1869355 : Blo 1867635 1869355 := bstep (se 1 (by rfl) ⟨1402016, by rfl⟩ : syracuseStep 1869355 = 2804033) B2804033
theorem B1869367 : Blo 1867635 1869367 := bstep (se 1 (by rfl) ⟨1402025, by rfl⟩ : syracuseStep 1869367 = 2804051) B2804051
theorem B4204097 : Blo 1867635 4204097 := bstep (se 2 (by rfl) ⟨1576536, by rfl⟩ : syracuseStep 4204097 = 3153073) B3153073
theorem B4728395 : Blo 1867635 4728395 := bstep (se 1 (by rfl) ⟨3546296, by rfl⟩ : syracuseStep 4728395 = 7092593) B7092593
theorem B1869387 : Blo 1867635 1869387 := bstep (se 1 (by rfl) ⟨1402040, by rfl⟩ : syracuseStep 1869387 = 2804081) B2804081
theorem B1869399 : Blo 1867635 1869399 := bstep (se 1 (by rfl) ⟨1402049, by rfl⟩ : syracuseStep 1869399 = 2804099) B2804099
theorem B2803289 : Blo 1867635 2803289 := bstep (se 2 (by rfl) ⟨1051233, by rfl⟩ : syracuseStep 2803289 = 2102467) B2102467
theorem B1869419 : Blo 1867635 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B1869431 : Blo 1867635 1869431 := bstep (se 1 (by rfl) ⟨1402073, by rfl⟩ : syracuseStep 1869431 = 2804147) B2804147
theorem B1869451 : Blo 1867635 1869451 := bstep (se 1 (by rfl) ⟨1402088, by rfl⟩ : syracuseStep 1869451 = 2804177) B2804177
theorem B1869463 : Blo 1867635 1869463 := bstep (se 1 (by rfl) ⟨1402097, by rfl⟩ : syracuseStep 1869463 = 2804195) B2804195
theorem B1869483 : Blo 1867635 1869483 := bstep (se 1 (by rfl) ⟨1402112, by rfl⟩ : syracuseStep 1869483 = 2804225) B2804225
theorem B1869495 : Blo 1867635 1869495 := bstep (se 1 (by rfl) ⟨1402121, by rfl⟩ : syracuseStep 1869495 = 2804243) B2804243
theorem B2803403 : Blo 1867635 2803403 := bstep (se 1 (by rfl) ⟨2102552, by rfl⟩ : syracuseStep 2803403 = 4205105) B4205105
theorem B1869515 : Blo 1867635 1869515 := bstep (se 1 (by rfl) ⟨1402136, by rfl⟩ : syracuseStep 1869515 = 2804273) B2804273
theorem B2803415 : Blo 1867635 2803415 := bstep (se 1 (by rfl) ⟨2102561, by rfl⟩ : syracuseStep 2803415 = 4205123) B4205123
theorem B1869527 : Blo 1867635 1869527 := bstep (se 1 (by rfl) ⟨1402145, by rfl⟩ : syracuseStep 1869527 = 2804291) B2804291
theorem B7096025 : Blo 1867635 7096025 := bstep (se 2 (by rfl) ⟨2661009, by rfl⟩ : syracuseStep 7096025 = 5322019) B5322019
theorem B1869547 : Blo 1867635 1869547 := bstep (se 1 (by rfl) ⟨1402160, by rfl⟩ : syracuseStep 1869547 = 2804321) B2804321
theorem B1869559 : Blo 1867635 1869559 := bstep (se 1 (by rfl) ⟨1402169, by rfl⟩ : syracuseStep 1869559 = 2804339) B2804339
theorem B2131723 : Blo 1867635 2131723 := bstep (se 1 (by rfl) ⟨1598792, by rfl⟩ : syracuseStep 2131723 = 3197585) B3197585
theorem B1869579 : Blo 1867635 1869579 := bstep (se 1 (by rfl) ⟨1402184, by rfl⟩ : syracuseStep 1869579 = 2804369) B2804369
theorem B1869591 : Blo 1867635 1869591 := bstep (se 1 (by rfl) ⟨1402193, by rfl⟩ : syracuseStep 1869591 = 2804387) B2804387
theorem B4204313 : Blo 1867635 4204313 := bstep (se 2 (by rfl) ⟨1576617, by rfl⟩ : syracuseStep 4204313 = 3153235) B3153235
theorem B2803481 : Blo 1867635 2803481 := bstep (se 2 (by rfl) ⟨1051305, by rfl⟩ : syracuseStep 2803481 = 2102611) B2102611
theorem B3368729 : Blo 1867635 3368729 := bstep (se 2 (by rfl) ⟨1263273, by rfl⟩ : syracuseStep 3368729 = 2526547) B2526547
theorem B1869611 : Blo 1867635 1869611 := bstep (se 1 (by rfl) ⟨1402208, by rfl⟩ : syracuseStep 1869611 = 2804417) B2804417
theorem B6309683 : Blo 1867635 6309683 := bstep (se 1 (by rfl) ⟨4732262, by rfl⟩ : syracuseStep 6309683 = 9464525) B9464525
theorem B1869623 : Blo 1867635 1869623 := bstep (se 1 (by rfl) ⟨1402217, by rfl⟩ : syracuseStep 1869623 = 2804435) B2804435
theorem B3786583 : Blo 1867635 3786583 := bstep (se 1 (by rfl) ⟨2839937, by rfl⟩ : syracuseStep 3786583 = 5679875) B5679875
theorem B9455453 : Blo 1867635 9455453 := bstep (se 3 (by rfl) ⟨1772897, by rfl⟩ : syracuseStep 9455453 = 3545795) B3545795
theorem B4204403 : Blo 1867635 4204403 := bstep (se 1 (by rfl) ⟨3153302, by rfl⟩ : syracuseStep 4204403 = 6306605) B6306605
theorem B2803595 : Blo 1867635 2803595 := bstep (se 1 (by rfl) ⟨2102696, by rfl⟩ : syracuseStep 2803595 = 4205393) B4205393
theorem B4204439 : Blo 1867635 4204439 := bstep (se 1 (by rfl) ⟨3153329, by rfl⟩ : syracuseStep 4204439 = 6306659) B6306659
theorem B2803607 : Blo 1867635 2803607 := bstep (se 1 (by rfl) ⟨2102705, by rfl⟩ : syracuseStep 2803607 = 4205411) B4205411
theorem B21276593 : Blo 1867635 21276593 := bstep (se 2 (by rfl) ⟨7978722, by rfl⟩ : syracuseStep 21276593 = 15957445) B15957445
theorem B15968177 : Blo 1867635 15968177 := bstep (se 2 (by rfl) ⟨5988066, by rfl⟩ : syracuseStep 15968177 = 11976133) B11976133
theorem B10102745 : Blo 1867635 10102745 := bstep (se 2 (by rfl) ⟨3788529, by rfl⟩ : syracuseStep 10102745 = 7577059) B7577059
theorem B2803673 : Blo 1867635 2803673 := bstep (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) B2102755
theorem B6309953 : Blo 1867635 6309953 := bstep (se 2 (by rfl) ⟨2366232, by rfl⟩ : syracuseStep 6309953 = 4732465) B4732465
theorem B4204619 : Blo 1867635 4204619 := bstep (se 1 (by rfl) ⟨3153464, by rfl⟩ : syracuseStep 4204619 = 6306929) B6306929
theorem B2803787 : Blo 1867635 2803787 := bstep (se 1 (by rfl) ⟨2102840, by rfl⟩ : syracuseStep 2803787 = 4205681) B4205681
theorem B2803799 : Blo 1867635 2803799 := bstep (se 1 (by rfl) ⟨2102849, by rfl⟩ : syracuseStep 2803799 = 4205699) B4205699
theorem B17967197 : Blo 1867635 17967197 := bstep (se 3 (by rfl) ⟨3368849, by rfl⟩ : syracuseStep 17967197 = 6737699) B6737699
theorem B4204673 : Blo 1867635 4204673 := bstep (se 2 (by rfl) ⟨1576752, by rfl⟩ : syracuseStep 4204673 = 3153505) B3153505
theorem B10102915 : Blo 1867635 10102915 := bstep (se 1 (by rfl) ⟨7577186, by rfl⟩ : syracuseStep 10102915 = 15154373) B15154373
theorem B16189571 : Blo 1867635 16189571 := bstep (se 1 (by rfl) ⟨12142178, by rfl⟩ : syracuseStep 16189571 = 24284357) B24284357
theorem B2803865 : Blo 1867635 2803865 := bstep (se 2 (by rfl) ⟨1051449, by rfl⟩ : syracuseStep 2803865 = 2102899) B2102899
theorem B2803979 : Blo 1867635 2803979 := bstep (se 1 (by rfl) ⟨2102984, by rfl⟩ : syracuseStep 2803979 = 4205969) B4205969
theorem B2803991 : Blo 1867635 2803991 := bstep (se 1 (by rfl) ⟨2102993, by rfl⟩ : syracuseStep 2803991 = 4205987) B4205987
theorem B4262233 : Blo 1867635 4262233 := bstep (se 2 (by rfl) ⟨1598337, by rfl⟩ : syracuseStep 4262233 = 3196675) B3196675
theorem B4204889 : Blo 1867635 4204889 := bstep (se 2 (by rfl) ⟨1576833, by rfl⟩ : syracuseStep 4204889 = 3153667) B3153667
theorem B2804057 : Blo 1867635 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B4204979 : Blo 1867635 4204979 := bstep (se 1 (by rfl) ⟨3153734, by rfl⟩ : syracuseStep 4204979 = 6307469) B6307469
theorem B2804171 : Blo 1867635 2804171 := bstep (se 1 (by rfl) ⟨2103128, by rfl⟩ : syracuseStep 2804171 = 4206257) B4206257
theorem B4205015 : Blo 1867635 4205015 := bstep (se 1 (by rfl) ⟨3153761, by rfl⟩ : syracuseStep 4205015 = 6307523) B6307523
theorem B2804183 : Blo 1867635 2804183 := bstep (se 1 (by rfl) ⟨2103137, by rfl⟩ : syracuseStep 2804183 = 4206275) B4206275
theorem B4729367 : Blo 1867635 4729367 := bstep (se 1 (by rfl) ⟨3547025, by rfl⟩ : syracuseStep 4729367 = 7094051) B7094051
theorem B2804249 : Blo 1867635 2804249 := bstep (se 2 (by rfl) ⟨1051593, by rfl⟩ : syracuseStep 2804249 = 2103187) B2103187
theorem B10783307 : Blo 1867635 10783307 := bstep (se 1 (by rfl) ⟨8087480, by rfl⟩ : syracuseStep 10783307 = 16174961) B16174961
theorem B4205195 : Blo 1867635 4205195 := bstep (se 1 (by rfl) ⟨3153896, by rfl⟩ : syracuseStep 4205195 = 6307793) B6307793
theorem B2804363 : Blo 1867635 2804363 := bstep (se 1 (by rfl) ⟨2103272, by rfl⟩ : syracuseStep 2804363 = 4206545) B4206545
theorem B2804375 : Blo 1867635 2804375 := bstep (se 1 (by rfl) ⟨2103281, by rfl⟩ : syracuseStep 2804375 = 4206563) B4206563
theorem B4205249 : Blo 1867635 4205249 := bstep (se 2 (by rfl) ⟨1576968, by rfl⟩ : syracuseStep 4205249 = 3153937) B3153937
theorem B3992267 : Blo 1867635 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B2804441 : Blo 1867635 2804441 := bstep (se 2 (by rfl) ⟨1051665, by rfl⟩ : syracuseStep 2804441 = 2103331) B2103331
theorem B4205465 : Blo 1867635 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B7982003 : Blo 1867635 7982003 := bstep (se 1 (by rfl) ⟨5986502, by rfl⟩ : syracuseStep 7982003 = 11973005) B11973005
theorem B4205555 : Blo 1867635 4205555 := bstep (se 1 (by rfl) ⟨3154166, by rfl⟩ : syracuseStep 4205555 = 6308333) B6308333
theorem B9464849 : Blo 1867635 9464849 := bstep (se 2 (by rfl) ⟨3549318, by rfl⟩ : syracuseStep 9464849 = 7098637) B7098637
theorem B4205591 : Blo 1867635 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B5983325 : Blo 1867635 5983325 := bstep (se 3 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 5983325 = 2243747) B2243747
theorem B2993303 : Blo 1867635 2993303 := bstep (se 1 (by rfl) ⟨2244977, by rfl⟩ : syracuseStep 2993303 = 4489955) B4489955
theorem B4730035 : Blo 1867635 4730035 := bstep (se 1 (by rfl) ⟨3547526, by rfl⟩ : syracuseStep 4730035 = 7095053) B7095053
theorem B9465011 : Blo 1867635 9465011 := bstep (se 1 (by rfl) ⟨7098758, by rfl⟩ : syracuseStep 9465011 = 14197517) B14197517
theorem B38358197 : Blo 1867635 38358197 := bstep (se 5 (by rfl) ⟨1798040, by rfl⟩ : syracuseStep 38358197 = 3596081) B3596081
theorem B4205771 : Blo 1867635 4205771 := bstep (se 1 (by rfl) ⟨3154328, by rfl⟩ : syracuseStep 4205771 = 6308657) B6308657
theorem B2878679 : Blo 1867635 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B4205825 : Blo 1867635 4205825 := bstep (se 2 (by rfl) ⟨1577184, by rfl⟩ : syracuseStep 4205825 = 3154369) B3154369
theorem B2993431 : Blo 1867635 2993431 := bstep (se 1 (by rfl) ⟨2245073, by rfl⟩ : syracuseStep 2993431 = 4490147) B4490147
theorem B4320535 : Blo 1867635 4320535 := bstep (se 1 (by rfl) ⟨3240401, by rfl⟩ : syracuseStep 4320535 = 6480803) B6480803
theorem B12782893 : Blo 1867635 12782893 := bstep (se 3 (by rfl) ⟨2396792, by rfl⟩ : syracuseStep 12782893 = 4793585) B4793585
theorem B7097651 : Blo 1867635 7097651 := bstep (se 1 (by rfl) ⟨5323238, by rfl⟩ : syracuseStep 7097651 = 10646477) B10646477
theorem B5049665 : Blo 1867635 5049665 := bstep (se 2 (by rfl) ⟨1893624, by rfl⟩ : syracuseStep 5049665 = 3787249) B3787249
theorem B4730177 : Blo 1867635 4730177 := bstep (se 2 (by rfl) ⟨1773816, by rfl⟩ : syracuseStep 4730177 = 3547633) B3547633
theorem B7097665 : Blo 1867635 7097665 := bstep (se 2 (by rfl) ⟨2661624, by rfl⟩ : syracuseStep 7097665 = 5323249) B5323249
theorem B5680459 : Blo 1867635 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B4263283 : Blo 1867635 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B4206041 : Blo 1867635 4206041 := bstep (se 2 (by rfl) ⟨1577265, by rfl⟩ : syracuseStep 4206041 = 3154531) B3154531
theorem B4206131 : Blo 1867635 4206131 := bstep (se 1 (by rfl) ⟨3154598, by rfl⟩ : syracuseStep 4206131 = 6309197) B6309197
theorem B4206167 : Blo 1867635 4206167 := bstep (se 1 (by rfl) ⟨3154625, by rfl⟩ : syracuseStep 4206167 = 6309251) B6309251
theorem B4206347 : Blo 1867635 4206347 := bstep (se 1 (by rfl) ⟨3154760, by rfl⟩ : syracuseStep 4206347 = 6309521) B6309521
theorem B6737687 : Blo 1867635 6737687 := bstep (se 1 (by rfl) ⟨5053265, by rfl⟩ : syracuseStep 6737687 = 10106531) B10106531
theorem B4206401 : Blo 1867635 4206401 := bstep (se 2 (by rfl) ⟨1577400, by rfl⟩ : syracuseStep 4206401 = 3154801) B3154801
theorem B5050205 : Blo 1867635 5050205 := bstep (se 3 (by rfl) ⟨946913, by rfl⟩ : syracuseStep 5050205 = 1893827) B1893827
theorem B6303581 : Blo 1867635 6303581 := bstep (se 3 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 6303581 = 2363843) B2363843
theorem B2101099 : Blo 1867635 2101099 := bstep (se 1 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 2101099 = 3151649) B3151649
theorem B20213621 : Blo 1867635 20213621 := bstep (se 5 (by rfl) ⟨947513, by rfl⟩ : syracuseStep 20213621 = 1895027) B1895027
theorem B9457559 : Blo 1867635 9457559 := bstep (se 1 (by rfl) ⟨7093169, by rfl⟩ : syracuseStep 9457559 = 14186339) B14186339
theorem B4550593 : Blo 1867635 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B2101207 : Blo 1867635 2101207 := bstep (se 1 (by rfl) ⟨1575905, by rfl⟩ : syracuseStep 2101207 = 3151811) B3151811
theorem B1994711 : Blo 1867635 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B14192657 : Blo 1867635 14192657 := bstep (se 2 (by rfl) ⟨5322246, by rfl⟩ : syracuseStep 14192657 = 10644493) B10644493
theorem B4206617 : Blo 1867635 4206617 := bstep (se 2 (by rfl) ⟨1577481, by rfl⟩ : syracuseStep 4206617 = 3154963) B3154963
theorem B35926091 : Blo 1867635 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B2994251 : Blo 1867635 2994251 := bstep (se 1 (by rfl) ⟨2245688, by rfl⟩ : syracuseStep 2994251 = 4491377) B4491377
theorem B2101387 : Blo 1867635 2101387 := bstep (se 1 (by rfl) ⟨1576040, by rfl⟩ : syracuseStep 2101387 = 3152081) B3152081
theorem B6394049 : Blo 1867635 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B2101495 : Blo 1867635 2101495 := bstep (se 1 (by rfl) ⟨1576121, by rfl⟩ : syracuseStep 2101495 = 3152243) B3152243
theorem B8982829 : Blo 1867635 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B2101675 : Blo 1867635 2101675 := bstep (se 1 (by rfl) ⟨1576256, by rfl⟩ : syracuseStep 2101675 = 3152513) B3152513
theorem B14184881 : Blo 1867635 14184881 := bstep (se 2 (by rfl) ⟨5319330, by rfl⟩ : syracuseStep 14184881 = 10638661) B10638661
theorem B5321153 : Blo 1867635 5321153 := bstep (se 2 (by rfl) ⟨1995432, by rfl⟩ : syracuseStep 5321153 = 3990865) B3990865
theorem B5321177 : Blo 1867635 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B2101783 : Blo 1867635 2101783 := bstep (se 1 (by rfl) ⟨1576337, by rfl⟩ : syracuseStep 2101783 = 3152675) B3152675
theorem B4731443 : Blo 1867635 4731443 := bstep (se 1 (by rfl) ⟨3548582, by rfl⟩ : syracuseStep 4731443 = 7097165) B7097165
theorem B2101963 : Blo 1867635 2101963 := bstep (se 1 (by rfl) ⟨1576472, by rfl⟩ : syracuseStep 2101963 = 3152945) B3152945
theorem B7983917 : Blo 1867635 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B2102071 : Blo 1867635 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B14185367 : Blo 1867635 14185367 := bstep (se 1 (by rfl) ⟨10639025, by rfl⟩ : syracuseStep 14185367 = 21278051) B21278051
theorem B5682113 : Blo 1867635 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B6304715 : Blo 1867635 6304715 := bstep (se 1 (by rfl) ⟨4728536, by rfl⟩ : syracuseStep 6304715 = 9457073) B9457073
theorem B2102251 : Blo 1867635 2102251 := bstep (se 1 (by rfl) ⟨1576688, by rfl⟩ : syracuseStep 2102251 = 3153377) B3153377
theorem B10097729 : Blo 1867635 10097729 := bstep (se 2 (by rfl) ⟨3786648, by rfl⟩ : syracuseStep 10097729 = 7573297) B7573297
theorem B2364491 : Blo 1867635 2364491 := bstep (se 1 (by rfl) ⟨1773368, by rfl⟩ : syracuseStep 2364491 = 3546737) B3546737
theorem B4731979 : Blo 1867635 4731979 := bstep (se 1 (by rfl) ⟨3548984, by rfl⟩ : syracuseStep 4731979 = 7097969) B7097969
theorem B2102359 : Blo 1867635 2102359 := bstep (se 1 (by rfl) ⟨1576769, by rfl⟩ : syracuseStep 2102359 = 3153539) B3153539
theorem B35042485 : Blo 1867635 35042485 := bstep (se 5 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 35042485 = 3285233) B3285233
theorem B6304985 : Blo 1867635 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B4732121 : Blo 1867635 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B2102539 : Blo 1867635 2102539 := bstep (se 1 (by rfl) ⟨1576904, by rfl⟩ : syracuseStep 2102539 = 3153809) B3153809
theorem B14382353 : Blo 1867635 14382353 := bstep (se 2 (by rfl) ⟨5393382, by rfl⟩ : syracuseStep 14382353 = 10786765) B10786765
theorem B8975681 : Blo 1867635 8975681 := bstep (se 2 (by rfl) ⟨3365880, by rfl⟩ : syracuseStep 8975681 = 6731761) B6731761
theorem B21288257 : Blo 1867635 21288257 := bstep (se 2 (by rfl) ⟨7983096, by rfl⟩ : syracuseStep 21288257 = 15966193) B15966193
theorem B11515229 : Blo 1867635 11515229 := bstep (se 3 (by rfl) ⟨2159105, by rfl⟩ : syracuseStep 11515229 = 4318211) B4318211
theorem B4101491 : Blo 1867635 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B2102647 : Blo 1867635 2102647 := bstep (se 1 (by rfl) ⟨1576985, by rfl⟩ : syracuseStep 2102647 = 3153971) B3153971
theorem B4552139 : Blo 1867635 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B7984601 : Blo 1867635 7984601 := bstep (se 2 (by rfl) ⟨2994225, by rfl⟩ : syracuseStep 7984601 = 5988451) B5988451
theorem B2102827 : Blo 1867635 2102827 := bstep (se 1 (by rfl) ⟨1577120, by rfl⟩ : syracuseStep 2102827 = 3154241) B3154241
theorem B2659979 : Blo 1867635 2659979 := bstep (se 1 (by rfl) ⟨1994984, by rfl⟩ : syracuseStep 2659979 = 3989969) B3989969
theorem B2102935 : Blo 1867635 2102935 := bstep (se 1 (by rfl) ⟨1577201, by rfl⟩ : syracuseStep 2102935 = 3154403) B3154403
theorem B5322419 : Blo 1867635 5322419 := bstep (se 1 (by rfl) ⟨3991814, by rfl⟩ : syracuseStep 5322419 = 7983629) B7983629
theorem B2365195 : Blo 1867635 2365195 := bstep (se 1 (by rfl) ⟨1773896, by rfl⟩ : syracuseStep 2365195 = 3547793) B3547793
theorem B13473553 : Blo 1867635 13473553 := bstep (se 2 (by rfl) ⟨5052582, by rfl⟩ : syracuseStep 13473553 = 10105165) B10105165
theorem B2103115 : Blo 1867635 2103115 := bstep (se 1 (by rfl) ⟨1577336, by rfl⟩ : syracuseStep 2103115 = 3154673) B3154673
theorem B3151703 : Blo 1867635 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B15955805 : Blo 1867635 15955805 := bstep (se 3 (by rfl) ⟨2991713, by rfl⟩ : syracuseStep 15955805 = 5983427) B5983427
theorem B11974493 : Blo 1867635 11974493 := bstep (se 3 (by rfl) ⟨2245217, by rfl⟩ : syracuseStep 11974493 = 4490435) B4490435
theorem B31561589 : Blo 1867635 31561589 := bstep (se 5 (by rfl) ⟨1479449, by rfl⟩ : syracuseStep 31561589 = 2958899) B2958899
theorem B6305687 : Blo 1867635 6305687 := bstep (se 1 (by rfl) ⟨4729265, by rfl⟩ : syracuseStep 6305687 = 9458531) B9458531
theorem B2103223 : Blo 1867635 2103223 := bstep (se 1 (by rfl) ⟨1577417, by rfl⟩ : syracuseStep 2103223 = 3154835) B3154835
theorem B3151831 : Blo 1867635 3151831 := bstep (se 1 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 3151831 = 4727747) B4727747
theorem B2365463 : Blo 1867635 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B26941571 : Blo 1867635 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B10647683 : Blo 1867635 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B6732163 : Blo 1867635 6732163 := bstep (se 1 (by rfl) ⟨5049122, by rfl⟩ : syracuseStep 6732163 = 10098245) B10098245
theorem B6306227 : Blo 1867635 6306227 := bstep (se 1 (by rfl) ⟨4729670, by rfl⟩ : syracuseStep 6306227 = 9459341) B9459341
theorem B10639937 : Blo 1867635 10639937 := bstep (se 2 (by rfl) ⟨3989976, by rfl⟩ : syracuseStep 10639937 = 7979953) B7979953
theorem B7985729 : Blo 1867635 7985729 := bstep (se 2 (by rfl) ⟨2994648, by rfl⟩ : syracuseStep 7985729 = 5989297) B5989297
theorem B3152459 : Blo 1867635 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B3545689 : Blo 1867635 3545689 := bstep (se 2 (by rfl) ⟨1329633, by rfl⟩ : syracuseStep 3545689 = 2659267) B2659267
theorem B2660953 : Blo 1867635 2660953 := bstep (se 2 (by rfl) ⟨997857, by rfl⟩ : syracuseStep 2660953 = 1995715) B1995715
theorem B8977027 : Blo 1867635 8977027 := bstep (se 1 (by rfl) ⟨6732770, by rfl⟩ : syracuseStep 8977027 = 13465541) B13465541
theorem B5683891 : Blo 1867635 5683891 := bstep (se 1 (by rfl) ⟨4262918, by rfl⟩ : syracuseStep 5683891 = 8525837) B8525837
theorem B6306497 : Blo 1867635 6306497 := bstep (se 2 (by rfl) ⟨2364936, by rfl⟩ : syracuseStep 6306497 = 4729873) B4729873
theorem B3152587 : Blo 1867635 3152587 := bstep (se 1 (by rfl) ⟨2364440, by rfl⟩ : syracuseStep 3152587 = 4728881) B4728881
theorem B2366167 : Blo 1867635 2366167 := bstep (se 1 (by rfl) ⟨1774625, by rfl⟩ : syracuseStep 2366167 = 3549251) B3549251
theorem B3693313 : Blo 1867635 3693313 := bstep (se 2 (by rfl) ⟨1384992, by rfl⟩ : syracuseStep 3693313 = 2769985) B2769985
theorem B17054509 : Blo 1867635 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B3152729 : Blo 1867635 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B3152857 : Blo 1867635 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B2841689 : Blo 1867635 2841689 := bstep (se 2 (by rfl) ⟨1065633, by rfl⟩ : syracuseStep 2841689 = 2131267) B2131267
theorem B3546251 : Blo 1867635 3546251 := bstep (se 1 (by rfl) ⟨2659688, by rfl⟩ : syracuseStep 3546251 = 5319377) B5319377
theorem B6307037 : Blo 1867635 6307037 := bstep (se 3 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 6307037 = 2365139) B2365139
theorem B3546433 : Blo 1867635 3546433 := bstep (se 2 (by rfl) ⟨1329912, by rfl⟩ : syracuseStep 3546433 = 2659825) B2659825
theorem B13131109 : Blo 1867635 13131109 := bstep (se 4 (by rfl) ⟨1231041, by rfl⟩ : syracuseStep 13131109 = 2462083) B2462083
theorem B9461123 : Blo 1867635 9461123 := bstep (se 1 (by rfl) ⟨7095842, by rfl⟩ : syracuseStep 9461123 = 14191685) B14191685
theorem B6733201 : Blo 1867635 6733201 := bstep (se 2 (by rfl) ⟨2524950, by rfl⟩ : syracuseStep 6733201 = 5049901) B5049901
theorem B10100147 : Blo 1867635 10100147 := bstep (se 1 (by rfl) ⟨7575110, by rfl⟩ : syracuseStep 10100147 = 15150221) B15150221
theorem B7093763 : Blo 1867635 7093763 := bstep (se 1 (by rfl) ⟨5320322, by rfl⟩ : syracuseStep 7093763 = 10640645) B10640645
theorem B7093777 : Blo 1867635 7093777 := bstep (se 2 (by rfl) ⟨2660166, by rfl⟩ : syracuseStep 7093777 = 5320333) B5320333
theorem B3153431 : Blo 1867635 3153431 := bstep (se 1 (by rfl) ⟨2365073, by rfl⟩ : syracuseStep 3153431 = 4730147) B4730147
theorem B7978571 : Blo 1867635 7978571 := bstep (se 1 (by rfl) ⟨5983928, by rfl⟩ : syracuseStep 7978571 = 11967857) B11967857
theorem B3989081 : Blo 1867635 3989081 := bstep (se 2 (by rfl) ⟨1495905, by rfl⟩ : syracuseStep 3989081 = 2991811) B2991811
theorem B3153559 : Blo 1867635 3153559 := bstep (se 1 (by rfl) ⟨2365169, by rfl⟩ : syracuseStep 3153559 = 4730339) B4730339
theorem B14786309 : Blo 1867635 14786309 := bstep (se 4 (by rfl) ⟨1386216, by rfl⟩ : syracuseStep 14786309 = 2772433) B2772433
theorem B7094081 : Blo 1867635 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B14196545 : Blo 1867635 14196545 := bstep (se 2 (by rfl) ⟨5323704, by rfl⟩ : syracuseStep 14196545 = 10647409) B10647409
theorem B2801483 : Blo 1867635 2801483 := bstep (se 1 (by rfl) ⟨2101112, by rfl⟩ : syracuseStep 2801483 = 4202225) B4202225
theorem B4202315 : Blo 1867635 4202315 := bstep (se 1 (by rfl) ⟨3151736, by rfl⟩ : syracuseStep 4202315 = 6303473) B6303473
theorem B2801495 : Blo 1867635 2801495 := bstep (se 1 (by rfl) ⟨2101121, by rfl⟩ : syracuseStep 2801495 = 4202243) B4202243
theorem B2244439 : Blo 1867635 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B2129771 : Blo 1867635 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B1867639 : Blo 1867635 1867639 := bstep (se 1 (by rfl) ⟨1400729, by rfl⟩ : syracuseStep 1867639 = 2801459) B2801459
theorem B4202369 : Blo 1867635 4202369 := bstep (se 2 (by rfl) ⟨1575888, by rfl⟩ : syracuseStep 4202369 = 3151777) B3151777
theorem B1867659 : Blo 1867635 1867659 := bstep (se 1 (by rfl) ⟨1400744, by rfl⟩ : syracuseStep 1867659 = 2801489) B2801489
theorem B1867671 : Blo 1867635 1867671 := bstep (se 1 (by rfl) ⟨1400753, by rfl⟩ : syracuseStep 1867671 = 2801507) B2801507
theorem B2801561 : Blo 1867635 2801561 := bstep (se 2 (by rfl) ⟨1050585, by rfl⟩ : syracuseStep 2801561 = 2101171) B2101171
theorem B1867691 : Blo 1867635 1867691 := bstep (se 1 (by rfl) ⟨1400768, by rfl⟩ : syracuseStep 1867691 = 2801537) B2801537
theorem B1867703 : Blo 1867635 1867703 := bstep (se 1 (by rfl) ⟨1400777, by rfl⟩ : syracuseStep 1867703 = 2801555) B2801555
theorem B1867723 : Blo 1867635 1867723 := bstep (se 1 (by rfl) ⟨1400792, by rfl⟩ : syracuseStep 1867723 = 2801585) B2801585
theorem B1867735 : Blo 1867635 1867735 := bstep (se 1 (by rfl) ⟨1400801, by rfl⟩ : syracuseStep 1867735 = 2801603) B2801603
theorem B4489177 : Blo 1867635 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B60612569 : Blo 1867635 60612569 := bstep (se 2 (by rfl) ⟨22729713, by rfl⟩ : syracuseStep 60612569 = 45459427) B45459427
theorem B1867755 : Blo 1867635 1867755 := bstep (se 1 (by rfl) ⟨1400816, by rfl⟩ : syracuseStep 1867755 = 2801633) B2801633
theorem B2129899 : Blo 1867635 2129899 := bstep (se 1 (by rfl) ⟨1597424, by rfl⟩ : syracuseStep 2129899 = 3194849) B3194849
theorem B1867783 : Blo 1867635 1867783 := bstep (se 1 (by rfl) ⟨1400837, by rfl⟩ : syracuseStep 1867783 = 2801675) B2801675
theorem B9461771 : Blo 1867635 9461771 := bstep (se 1 (by rfl) ⟨7096328, by rfl⟩ : syracuseStep 9461771 = 14192657) B14192657
theorem B1867791 : Blo 1867635 1867791 := bstep (se 1 (by rfl) ⟨1400843, by rfl⟩ : syracuseStep 1867791 = 2801687) B2801687
theorem B2801723 : Blo 1867635 2801723 := bstep (se 1 (by rfl) ⟨2101292, by rfl⟩ : syracuseStep 2801723 = 4202585) B4202585
theorem B1867835 : Blo 1867635 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B6307901 : Blo 1867635 6307901 := bstep (se 3 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 6307901 = 2365463) B2365463
theorem B2801783 : Blo 1867635 2801783 := bstep (se 1 (by rfl) ⟨2101337, by rfl⟩ : syracuseStep 2801783 = 4202675) B4202675
theorem B1867911 : Blo 1867635 1867911 := bstep (se 1 (by rfl) ⟨1400933, by rfl⟩ : syracuseStep 1867911 = 2801867) B2801867
theorem B2801807 : Blo 1867635 2801807 := bstep (se 1 (by rfl) ⟨2101355, by rfl⟩ : syracuseStep 2801807 = 4202711) B4202711
theorem B1867919 : Blo 1867635 1867919 := bstep (se 1 (by rfl) ⟨1400939, by rfl⟩ : syracuseStep 1867919 = 2801879) B2801879
theorem B9461933 : Blo 1867635 9461933 := bstep (se 3 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 9461933 = 3548225) B3548225
theorem B2801849 : Blo 1867635 2801849 := bstep (se 2 (by rfl) ⟨1050693, by rfl⟩ : syracuseStep 2801849 = 2101387) B2101387
theorem B1867963 : Blo 1867635 1867963 := bstep (se 1 (by rfl) ⟨1400972, by rfl⟩ : syracuseStep 1867963 = 2801945) B2801945
theorem B7577837 : Blo 1867635 7577837 := bstep (se 3 (by rfl) ⟨1420844, by rfl⟩ : syracuseStep 7577837 = 2841689) B2841689
theorem B2801927 : Blo 1867635 2801927 := bstep (se 1 (by rfl) ⟨2101445, by rfl⟩ : syracuseStep 2801927 = 4202891) B4202891
theorem B1868039 : Blo 1867635 1868039 := bstep (se 1 (by rfl) ⟨1401029, by rfl⟩ : syracuseStep 1868039 = 2802059) B2802059
theorem B1868047 : Blo 1867635 1868047 := bstep (se 1 (by rfl) ⟨1401035, by rfl⟩ : syracuseStep 1868047 = 2802071) B2802071
theorem B2801963 : Blo 1867635 2801963 := bstep (se 1 (by rfl) ⟨2101472, by rfl⟩ : syracuseStep 2801963 = 4202945) B4202945
theorem B1868091 : Blo 1867635 1868091 := bstep (se 1 (by rfl) ⟨1401068, by rfl⟩ : syracuseStep 1868091 = 2802137) B2802137
theorem B3547451 : Blo 1867635 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B2801993 : Blo 1867635 2801993 := bstep (se 2 (by rfl) ⟨1050747, by rfl⟩ : syracuseStep 2801993 = 2101495) B2101495
theorem B3154295 : Blo 1867635 3154295 := bstep (se 1 (by rfl) ⟨2365721, by rfl⟩ : syracuseStep 3154295 = 4731443) B4731443
theorem B1868167 : Blo 1867635 1868167 := bstep (se 1 (by rfl) ⟨1401125, by rfl⟩ : syracuseStep 1868167 = 2802251) B2802251
theorem B1868175 : Blo 1867635 1868175 := bstep (se 1 (by rfl) ⟨1401131, by rfl⟩ : syracuseStep 1868175 = 2802263) B2802263
theorem B2802107 : Blo 1867635 2802107 := bstep (se 1 (by rfl) ⟨2101580, by rfl⟩ : syracuseStep 2802107 = 4203161) B4203161
theorem B1868219 : Blo 1867635 1868219 := bstep (se 1 (by rfl) ⟨1401164, by rfl⟩ : syracuseStep 1868219 = 2802329) B2802329
theorem B2802167 : Blo 1867635 2802167 := bstep (se 1 (by rfl) ⟨2101625, by rfl⟩ : syracuseStep 2802167 = 4203251) B4203251
theorem B20201987 : Blo 1867635 20201987 := bstep (se 1 (by rfl) ⟨15151490, by rfl⟩ : syracuseStep 20201987 = 30302981) B30302981
theorem B1868295 : Blo 1867635 1868295 := bstep (se 1 (by rfl) ⟨1401221, by rfl⟩ : syracuseStep 1868295 = 2802443) B2802443
theorem B2802191 : Blo 1867635 2802191 := bstep (se 1 (by rfl) ⟨2101643, by rfl⟩ : syracuseStep 2802191 = 4203287) B4203287
theorem B1868303 : Blo 1867635 1868303 := bstep (se 1 (by rfl) ⟨1401227, by rfl⟩ : syracuseStep 1868303 = 2802455) B2802455
theorem B2802233 : Blo 1867635 2802233 := bstep (se 2 (by rfl) ⟨1050837, by rfl⟩ : syracuseStep 2802233 = 2101675) B2101675
theorem B1868347 : Blo 1867635 1868347 := bstep (se 1 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 1868347 = 2802521) B2802521
theorem B7676477 : Blo 1867635 7676477 := bstep (se 3 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 7676477 = 2878679) B2878679
theorem B4203143 : Blo 1867635 4203143 := bstep (se 1 (by rfl) ⟨3152357, by rfl⟩ : syracuseStep 4203143 = 6304715) B6304715
theorem B2802311 : Blo 1867635 2802311 := bstep (se 1 (by rfl) ⟨2101733, by rfl⟩ : syracuseStep 2802311 = 4203467) B4203467
theorem B1868423 : Blo 1867635 1868423 := bstep (se 1 (by rfl) ⟨1401317, by rfl⟩ : syracuseStep 1868423 = 2802635) B2802635
theorem B1868431 : Blo 1867635 1868431 := bstep (se 1 (by rfl) ⟨1401323, by rfl⟩ : syracuseStep 1868431 = 2802647) B2802647
theorem B2802347 : Blo 1867635 2802347 := bstep (se 1 (by rfl) ⟨2101760, by rfl⟩ : syracuseStep 2802347 = 4203521) B4203521
theorem B1868475 : Blo 1867635 1868475 := bstep (se 1 (by rfl) ⟨1401356, by rfl⟩ : syracuseStep 1868475 = 2802713) B2802713
theorem B2802377 : Blo 1867635 2802377 := bstep (se 2 (by rfl) ⟨1050891, by rfl⟩ : syracuseStep 2802377 = 2101783) B2101783
theorem B1868551 : Blo 1867635 1868551 := bstep (se 1 (by rfl) ⟨1401413, by rfl⟩ : syracuseStep 1868551 = 2802827) B2802827
theorem B1868559 : Blo 1867635 1868559 := bstep (se 1 (by rfl) ⟨1401419, by rfl⟩ : syracuseStep 1868559 = 2802839) B2802839
theorem B4727585 : Blo 1867635 4727585 := bstep (se 2 (by rfl) ⟨1772844, by rfl⟩ : syracuseStep 4727585 = 3545689) B3545689
theorem B3547937 : Blo 1867635 3547937 := bstep (se 2 (by rfl) ⟨1330476, by rfl⟩ : syracuseStep 3547937 = 2660953) B2660953
theorem B4203323 : Blo 1867635 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2802491 : Blo 1867635 2802491 := bstep (se 1 (by rfl) ⟨2101868, by rfl⟩ : syracuseStep 2802491 = 4203737) B4203737
theorem B1868603 : Blo 1867635 1868603 := bstep (se 1 (by rfl) ⟨1401452, by rfl⟩ : syracuseStep 1868603 = 2802905) B2802905
theorem B3154747 : Blo 1867635 3154747 := bstep (se 1 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 3154747 = 4732121) B4732121
theorem B11969369 : Blo 1867635 11969369 := bstep (se 2 (by rfl) ⟨4488513, by rfl⟩ : syracuseStep 11969369 = 8977027) B8977027
theorem B2802551 : Blo 1867635 2802551 := bstep (se 1 (by rfl) ⟨2101913, by rfl⟩ : syracuseStep 2802551 = 4203827) B4203827
theorem B1868679 : Blo 1867635 1868679 := bstep (se 1 (by rfl) ⟨1401509, by rfl⟩ : syracuseStep 1868679 = 2803019) B2803019
theorem B2802575 : Blo 1867635 2802575 := bstep (se 1 (by rfl) ⟨2101931, by rfl⟩ : syracuseStep 2802575 = 4203863) B4203863
theorem B1868687 : Blo 1867635 1868687 := bstep (se 1 (by rfl) ⟨1401515, by rfl⟩ : syracuseStep 1868687 = 2803031) B2803031
theorem B7676819 : Blo 1867635 7676819 := bstep (se 1 (by rfl) ⟨5757614, by rfl⟩ : syracuseStep 7676819 = 11515229) B11515229
theorem B7578521 : Blo 1867635 7578521 := bstep (se 2 (by rfl) ⟨2841945, by rfl⟩ : syracuseStep 7578521 = 5683891) B5683891
theorem B4203449 : Blo 1867635 4203449 := bstep (se 2 (by rfl) ⟨1576293, by rfl⟩ : syracuseStep 4203449 = 3152587) B3152587
theorem B2802617 : Blo 1867635 2802617 := bstep (se 2 (by rfl) ⟨1050981, by rfl⟩ : syracuseStep 2802617 = 2101963) B2101963
theorem B1868731 : Blo 1867635 1868731 := bstep (se 1 (by rfl) ⟨1401548, by rfl⟩ : syracuseStep 1868731 = 2803097) B2803097
theorem B3154889 : Blo 1867635 3154889 := bstep (se 2 (by rfl) ⟨1183083, by rfl⟩ : syracuseStep 3154889 = 2366167) B2366167
theorem B2802695 : Blo 1867635 2802695 := bstep (se 1 (by rfl) ⟨2102021, by rfl⟩ : syracuseStep 2802695 = 4204043) B4204043
theorem B1868807 : Blo 1867635 1868807 := bstep (se 1 (by rfl) ⟨1401605, by rfl⟩ : syracuseStep 1868807 = 2803211) B2803211
theorem B1868815 : Blo 1867635 1868815 := bstep (se 1 (by rfl) ⟨1401611, by rfl⟩ : syracuseStep 1868815 = 2803223) B2803223
theorem B2802731 : Blo 1867635 2802731 := bstep (se 1 (by rfl) ⟨2102048, by rfl⟩ : syracuseStep 2802731 = 4204097) B4204097
theorem B1868859 : Blo 1867635 1868859 := bstep (se 1 (by rfl) ⟨1401644, by rfl⟩ : syracuseStep 1868859 = 2803289) B2803289
theorem B2802761 : Blo 1867635 2802761 := bstep (se 2 (by rfl) ⟨1051035, by rfl⟩ : syracuseStep 2802761 = 2102071) B2102071
theorem B3548279 : Blo 1867635 3548279 := bstep (se 1 (by rfl) ⟨2661209, by rfl⟩ : syracuseStep 3548279 = 5322419) B5322419
theorem B1868935 : Blo 1867635 1868935 := bstep (se 1 (by rfl) ⟨1401701, by rfl⟩ : syracuseStep 1868935 = 2803403) B2803403
theorem B1868943 : Blo 1867635 1868943 := bstep (se 1 (by rfl) ⟨1401707, by rfl⟩ : syracuseStep 1868943 = 2803415) B2803415
theorem B14189741 : Blo 1867635 14189741 := bstep (se 3 (by rfl) ⟨2660576, by rfl⟩ : syracuseStep 14189741 = 5321153) B5321153
theorem B2802875 : Blo 1867635 2802875 := bstep (se 1 (by rfl) ⟨2102156, by rfl⟩ : syracuseStep 2802875 = 4204313) B4204313
theorem B1868987 : Blo 1867635 1868987 := bstep (se 1 (by rfl) ⟨1401740, by rfl⟩ : syracuseStep 1868987 = 2803481) B2803481
theorem B2245819 : Blo 1867635 2245819 := bstep (se 1 (by rfl) ⟨1684364, by rfl⟩ : syracuseStep 2245819 = 3368729) B3368729
theorem B17958125 : Blo 1867635 17958125 := bstep (se 3 (by rfl) ⟨3367148, by rfl⟩ : syracuseStep 17958125 = 6734297) B6734297
theorem B2802935 : Blo 1867635 2802935 := bstep (se 1 (by rfl) ⟨2102201, by rfl⟩ : syracuseStep 2802935 = 4204403) B4204403
theorem B1869063 : Blo 1867635 1869063 := bstep (se 1 (by rfl) ⟨1401797, by rfl⟩ : syracuseStep 1869063 = 2803595) B2803595
theorem B4203791 : Blo 1867635 4203791 := bstep (se 1 (by rfl) ⟨3152843, by rfl⟩ : syracuseStep 4203791 = 6305687) B6305687
theorem B2802959 : Blo 1867635 2802959 := bstep (se 1 (by rfl) ⟨2102219, by rfl⟩ : syracuseStep 2802959 = 4204439) B4204439
theorem B1869071 : Blo 1867635 1869071 := bstep (se 1 (by rfl) ⟨1401803, by rfl⟩ : syracuseStep 1869071 = 2803607) B2803607
theorem B4203809 : Blo 1867635 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B2803001 : Blo 1867635 2803001 := bstep (se 2 (by rfl) ⟨1051125, by rfl⟩ : syracuseStep 2803001 = 2102251) B2102251
theorem B6735163 : Blo 1867635 6735163 := bstep (se 1 (by rfl) ⟨5051372, by rfl⟩ : syracuseStep 6735163 = 10102745) B10102745
theorem B1869115 : Blo 1867635 1869115 := bstep (se 1 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 1869115 = 2803673) B2803673
theorem B2803079 : Blo 1867635 2803079 := bstep (se 1 (by rfl) ⟨2102309, by rfl⟩ : syracuseStep 2803079 = 4204619) B4204619
theorem B1869191 : Blo 1867635 1869191 := bstep (se 1 (by rfl) ⟨1401893, by rfl⟩ : syracuseStep 1869191 = 2803787) B2803787
theorem B1869199 : Blo 1867635 1869199 := bstep (se 1 (by rfl) ⟨1401899, by rfl⟩ : syracuseStep 1869199 = 2803799) B2803799
theorem B11978131 : Blo 1867635 11978131 := bstep (se 1 (by rfl) ⟨8983598, by rfl⟩ : syracuseStep 11978131 = 17967197) B17967197
theorem B2803115 : Blo 1867635 2803115 := bstep (se 1 (by rfl) ⟨2102336, by rfl⟩ : syracuseStep 2803115 = 4204673) B4204673
theorem B6309305 : Blo 1867635 6309305 := bstep (se 2 (by rfl) ⟨2365989, by rfl⟩ : syracuseStep 6309305 = 4731979) B4731979
theorem B1869243 : Blo 1867635 1869243 := bstep (se 1 (by rfl) ⟨1401932, by rfl⟩ : syracuseStep 1869243 = 2803865) B2803865
theorem B2803145 : Blo 1867635 2803145 := bstep (se 2 (by rfl) ⟨1051179, by rfl⟩ : syracuseStep 2803145 = 2102359) B2102359
theorem B1869319 : Blo 1867635 1869319 := bstep (se 1 (by rfl) ⟨1401989, by rfl⟩ : syracuseStep 1869319 = 2803979) B2803979
theorem B1869327 : Blo 1867635 1869327 := bstep (se 1 (by rfl) ⟨1401995, by rfl⟩ : syracuseStep 1869327 = 2803991) B2803991
theorem B2803259 : Blo 1867635 2803259 := bstep (se 1 (by rfl) ⟨2102444, by rfl⟩ : syracuseStep 2803259 = 4204889) B4204889
theorem B1869371 : Blo 1867635 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B47908421 : Blo 1867635 47908421 := bstep (se 4 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 47908421 = 8982829) B8982829
theorem B4204151 : Blo 1867635 4204151 := bstep (se 1 (by rfl) ⟨3153113, by rfl⟩ : syracuseStep 4204151 = 6306227) B6306227
theorem B2803319 : Blo 1867635 2803319 := bstep (se 1 (by rfl) ⟨2102489, by rfl⟩ : syracuseStep 2803319 = 4204979) B4204979
theorem B1869447 : Blo 1867635 1869447 := bstep (se 1 (by rfl) ⟨1402085, by rfl⟩ : syracuseStep 1869447 = 2804171) B2804171
theorem B2803343 : Blo 1867635 2803343 := bstep (se 1 (by rfl) ⟨2102507, by rfl⟩ : syracuseStep 2803343 = 4205015) B4205015
theorem B1869455 : Blo 1867635 1869455 := bstep (se 1 (by rfl) ⟨1402091, by rfl⟩ : syracuseStep 1869455 = 2804183) B2804183
theorem B2803385 : Blo 1867635 2803385 := bstep (se 2 (by rfl) ⟨1051269, by rfl⟩ : syracuseStep 2803385 = 2102539) B2102539
theorem B1869499 : Blo 1867635 1869499 := bstep (se 1 (by rfl) ⟨1402124, by rfl⟩ : syracuseStep 1869499 = 2804249) B2804249
theorem B3991241 : Blo 1867635 3991241 := bstep (se 2 (by rfl) ⟨1496715, by rfl⟩ : syracuseStep 3991241 = 2993431) B2993431
theorem B5760713 : Blo 1867635 5760713 := bstep (se 2 (by rfl) ⟨2160267, by rfl⟩ : syracuseStep 5760713 = 4320535) B4320535
theorem B30295781 : Blo 1867635 30295781 := bstep (se 4 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 30295781 = 5680459) B5680459
theorem B4728577 : Blo 1867635 4728577 := bstep (se 2 (by rfl) ⟨1773216, by rfl⟩ : syracuseStep 4728577 = 3546433) B3546433
theorem B9463553 : Blo 1867635 9463553 := bstep (se 2 (by rfl) ⟨3548832, by rfl⟩ : syracuseStep 9463553 = 7097665) B7097665
theorem B2803463 : Blo 1867635 2803463 := bstep (se 1 (by rfl) ⟨2102597, by rfl⟩ : syracuseStep 2803463 = 4205195) B4205195
theorem B1869575 : Blo 1867635 1869575 := bstep (se 1 (by rfl) ⟨1402181, by rfl⟩ : syracuseStep 1869575 = 2804363) B2804363
theorem B1869583 : Blo 1867635 1869583 := bstep (se 1 (by rfl) ⟨1402187, by rfl⟩ : syracuseStep 1869583 = 2804375) B2804375
theorem B11970341 : Blo 1867635 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B4204331 : Blo 1867635 4204331 := bstep (se 1 (by rfl) ⟨3153248, by rfl⟩ : syracuseStep 4204331 = 6306497) B6306497
theorem B2803499 : Blo 1867635 2803499 := bstep (se 1 (by rfl) ⟨2102624, by rfl⟩ : syracuseStep 2803499 = 4205249) B4205249
theorem B17508145 : Blo 1867635 17508145 := bstep (se 2 (by rfl) ⟨6565554, by rfl⟩ : syracuseStep 17508145 = 13131109) B13131109
theorem B1869627 : Blo 1867635 1869627 := bstep (se 1 (by rfl) ⟨1402220, by rfl⟩ : syracuseStep 1869627 = 2804441) B2804441
theorem B2803529 : Blo 1867635 2803529 := bstep (se 2 (by rfl) ⟨1051323, by rfl⟩ : syracuseStep 2803529 = 2102647) B2102647
theorem B2803643 : Blo 1867635 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B2803703 : Blo 1867635 2803703 := bstep (se 1 (by rfl) ⟨2102777, by rfl⟩ : syracuseStep 2803703 = 4205555) B4205555
theorem B6309899 : Blo 1867635 6309899 := bstep (se 1 (by rfl) ⟨4732424, by rfl⟩ : syracuseStep 6309899 = 9464849) B9464849
theorem B2803727 : Blo 1867635 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B2803769 : Blo 1867635 2803769 := bstep (se 2 (by rfl) ⟨1051413, by rfl⟩ : syracuseStep 2803769 = 2102827) B2102827
theorem B6310007 : Blo 1867635 6310007 := bstep (se 1 (by rfl) ⟨4732505, by rfl⟩ : syracuseStep 6310007 = 9465011) B9465011
theorem B2803847 : Blo 1867635 2803847 := bstep (se 1 (by rfl) ⟨2102885, by rfl⟩ : syracuseStep 2803847 = 4205771) B4205771
theorem B4204691 : Blo 1867635 4204691 := bstep (se 1 (by rfl) ⟨3153518, by rfl⟩ : syracuseStep 4204691 = 6307037) B6307037
theorem B2803883 : Blo 1867635 2803883 := bstep (se 1 (by rfl) ⟨2102912, by rfl⟩ : syracuseStep 2803883 = 4205825) B4205825
theorem B4204745 : Blo 1867635 4204745 := bstep (se 2 (by rfl) ⟨1576779, by rfl⟩ : syracuseStep 4204745 = 3153559) B3153559
theorem B2803913 : Blo 1867635 2803913 := bstep (se 2 (by rfl) ⟨1051467, by rfl⟩ : syracuseStep 2803913 = 2102935) B2102935
theorem B5679389 : Blo 1867635 5679389 := bstep (se 3 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 5679389 = 2129771) B2129771
theorem B2804027 : Blo 1867635 2804027 := bstep (se 1 (by rfl) ⟨2103020, by rfl⟩ : syracuseStep 2804027 = 4206041) B4206041
theorem B4729175 : Blo 1867635 4729175 := bstep (se 1 (by rfl) ⟨3546881, by rfl⟩ : syracuseStep 4729175 = 7093763) B7093763
theorem B2804087 : Blo 1867635 2804087 := bstep (se 1 (by rfl) ⟨2103065, by rfl⟩ : syracuseStep 2804087 = 4206131) B4206131
theorem B5319047 : Blo 1867635 5319047 := bstep (se 1 (by rfl) ⟨3989285, by rfl⟩ : syracuseStep 5319047 = 7978571) B7978571
theorem B2804111 : Blo 1867635 2804111 := bstep (se 1 (by rfl) ⟨2103083, by rfl⟩ : syracuseStep 2804111 = 4206167) B4206167
theorem B2804153 : Blo 1867635 2804153 := bstep (se 2 (by rfl) ⟨1051557, by rfl⟩ : syracuseStep 2804153 = 2103115) B2103115
theorem B5048777 : Blo 1867635 5048777 := bstep (se 2 (by rfl) ⟨1893291, by rfl⟩ : syracuseStep 5048777 = 3786583) B3786583
theorem B21285341 : Blo 1867635 21285341 := bstep (se 3 (by rfl) ⟨3991001, by rfl⟩ : syracuseStep 21285341 = 7982003) B7982003
theorem B9857539 : Blo 1867635 9857539 := bstep (se 1 (by rfl) ⟨7393154, by rfl⟩ : syracuseStep 9857539 = 14786309) B14786309
theorem B2804231 : Blo 1867635 2804231 := bstep (se 1 (by rfl) ⟨2103173, by rfl⟩ : syracuseStep 2804231 = 4206347) B4206347
theorem B4491791 : Blo 1867635 4491791 := bstep (se 1 (by rfl) ⟨3368843, by rfl⟩ : syracuseStep 4491791 = 6737687) B6737687
theorem B4729387 : Blo 1867635 4729387 := bstep (se 1 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 4729387 = 7094081) B7094081
theorem B9464363 : Blo 1867635 9464363 := bstep (se 1 (by rfl) ⟨7098272, by rfl⟩ : syracuseStep 9464363 = 14196545) B14196545
theorem B2804267 : Blo 1867635 2804267 := bstep (se 1 (by rfl) ⟨2103200, by rfl⟩ : syracuseStep 2804267 = 4206401) B4206401
theorem B5319229 : Blo 1867635 5319229 := bstep (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) B1994711
theorem B2804297 : Blo 1867635 2804297 := bstep (se 2 (by rfl) ⟨1051611, by rfl⟩ : syracuseStep 2804297 = 2103223) B2103223
theorem B4729529 : Blo 1867635 4729529 := bstep (se 2 (by rfl) ⟨1773573, by rfl⟩ : syracuseStep 4729529 = 3547147) B3547147
theorem B2804411 : Blo 1867635 2804411 := bstep (se 1 (by rfl) ⟨2103308, by rfl⟩ : syracuseStep 2804411 = 4206617) B4206617
theorem B4262699 : Blo 1867635 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B13470553 : Blo 1867635 13470553 := bstep (se 2 (by rfl) ⟨5051457, by rfl⟩ : syracuseStep 13470553 = 10102915) B10102915
theorem B4205447 : Blo 1867635 4205447 := bstep (se 1 (by rfl) ⟨3154085, by rfl⟩ : syracuseStep 4205447 = 6308171) B6308171
theorem B9456587 : Blo 1867635 9456587 := bstep (se 1 (by rfl) ⟨7092440, by rfl⟩ : syracuseStep 9456587 = 14184881) B14184881
theorem B5319695 : Blo 1867635 5319695 := bstep (se 1 (by rfl) ⟨3989771, by rfl⟩ : syracuseStep 5319695 = 7979543) B7979543
theorem B3992591 : Blo 1867635 3992591 := bstep (se 1 (by rfl) ⟨2994443, by rfl⟩ : syracuseStep 3992591 = 5988887) B5988887
theorem B5049373 : Blo 1867635 5049373 := bstep (se 3 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 5049373 = 1893515) B1893515
theorem B2993195 : Blo 1867635 2993195 := bstep (se 1 (by rfl) ⟨2244896, by rfl⟩ : syracuseStep 2993195 = 4489793) B4489793
theorem B4205627 : Blo 1867635 4205627 := bstep (se 1 (by rfl) ⟨3154220, by rfl⟩ : syracuseStep 4205627 = 6308441) B6308441
theorem B4205753 : Blo 1867635 4205753 := bstep (se 2 (by rfl) ⟨1577157, by rfl⟩ : syracuseStep 4205753 = 3154315) B3154315
theorem B9456911 : Blo 1867635 9456911 := bstep (se 1 (by rfl) ⟨7092683, by rfl⟩ : syracuseStep 9456911 = 14185367) B14185367
theorem B3788075 : Blo 1867635 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B4206095 : Blo 1867635 4206095 := bstep (se 1 (by rfl) ⟨3154571, by rfl⟩ : syracuseStep 4206095 = 6309143) B6309143
theorem B4206113 : Blo 1867635 4206113 := bstep (se 2 (by rfl) ⟨1577292, by rfl⟩ : syracuseStep 4206113 = 3154585) B3154585
theorem B5983787 : Blo 1867635 5983787 := bstep (se 1 (by rfl) ⟨4487840, by rfl⟩ : syracuseStep 5983787 = 8975681) B8975681
theorem B14192171 : Blo 1867635 14192171 := bstep (se 1 (by rfl) ⟨10644128, by rfl⟩ : syracuseStep 14192171 = 21288257) B21288257
theorem B2993707 : Blo 1867635 2993707 := bstep (se 1 (by rfl) ⟨2245280, by rfl⟩ : syracuseStep 2993707 = 4490561) B4490561
theorem B4730521 : Blo 1867635 4730521 := bstep (se 2 (by rfl) ⟨1773945, by rfl⟩ : syracuseStep 4730521 = 3547891) B3547891
theorem B4730683 : Blo 1867635 4730683 := bstep (se 1 (by rfl) ⟨3548012, by rfl⟩ : syracuseStep 4730683 = 7096025) B7096025
theorem B4206455 : Blo 1867635 4206455 := bstep (se 1 (by rfl) ⟨3154841, by rfl⟩ : syracuseStep 4206455 = 6309683) B6309683
theorem B2101135 : Blo 1867635 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B10637203 : Blo 1867635 10637203 := bstep (se 1 (by rfl) ⟨7977902, by rfl⟩ : syracuseStep 10637203 = 15955805) B15955805
theorem B6303635 : Blo 1867635 6303635 := bstep (se 1 (by rfl) ⟨4727726, by rfl⟩ : syracuseStep 6303635 = 9455453) B9455453
theorem B7982995 : Blo 1867635 7982995 := bstep (se 1 (by rfl) ⟨5987246, by rfl⟩ : syracuseStep 7982995 = 11974493) B11974493
theorem B21041059 : Blo 1867635 21041059 := bstep (se 1 (by rfl) ⟨15780794, by rfl⟩ : syracuseStep 21041059 = 31561589) B31561589
theorem B14184395 : Blo 1867635 14184395 := bstep (se 1 (by rfl) ⟨10638296, by rfl⟩ : syracuseStep 14184395 = 21276593) B21276593
theorem B4730825 : Blo 1867635 4730825 := bstep (se 2 (by rfl) ⟨1774059, by rfl⟩ : syracuseStep 4730825 = 3548119) B3548119
theorem B10645451 : Blo 1867635 10645451 := bstep (se 1 (by rfl) ⟨7984088, by rfl⟩ : syracuseStep 10645451 = 15968177) B15968177
theorem B19697669 : Blo 1867635 19697669 := bstep (se 4 (by rfl) ⟨1846656, by rfl⟩ : syracuseStep 19697669 = 3693313) B3693313
theorem B4206635 : Blo 1867635 4206635 := bstep (se 1 (by rfl) ⟨3154976, by rfl⟩ : syracuseStep 4206635 = 6309953) B6309953
theorem B30715949 : Blo 1867635 30715949 := bstep (se 3 (by rfl) ⟨5759240, by rfl⟩ : syracuseStep 30715949 = 11518481) B11518481
theorem B17961047 : Blo 1867635 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B7098455 : Blo 1867635 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B10793047 : Blo 1867635 10793047 := bstep (se 1 (by rfl) ⟨8094785, by rfl⟩ : syracuseStep 10793047 = 16189571) B16189571
theorem B46723313 : Blo 1867635 46723313 := bstep (se 2 (by rfl) ⟨17521242, by rfl⟩ : syracuseStep 46723313 = 35042485) B35042485
theorem B5320961 : Blo 1867635 5320961 := bstep (se 2 (by rfl) ⟨1995360, by rfl⟩ : syracuseStep 5320961 = 3990721) B3990721
theorem B4731169 : Blo 1867635 4731169 := bstep (se 2 (by rfl) ⟨1774188, by rfl⟩ : syracuseStep 4731169 = 3548377) B3548377
theorem B7188871 : Blo 1867635 7188871 := bstep (se 1 (by rfl) ⟨5391653, by rfl⟩ : syracuseStep 7188871 = 10783307) B10783307
theorem B2101639 : Blo 1867635 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B17043857 : Blo 1867635 17043857 := bstep (se 2 (by rfl) ⟨6391446, by rfl⟩ : syracuseStep 17043857 = 12782893) B12782893
theorem B2101819 : Blo 1867635 2101819 := bstep (se 1 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 2101819 = 3152729) B3152729
theorem B22737509 : Blo 1867635 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B9458369 : Blo 1867635 9458369 := bstep (se 2 (by rfl) ⟨3546888, by rfl⟩ : syracuseStep 9458369 = 7093777) B7093777
theorem B2364167 : Blo 1867635 2364167 := bstep (se 1 (by rfl) ⟨1773125, by rfl⟩ : syracuseStep 2364167 = 3546251) B3546251
theorem B1995535 : Blo 1867635 1995535 := bstep (se 1 (by rfl) ⟨1496651, by rfl⟩ : syracuseStep 1995535 = 2993303) B2993303
theorem B25572131 : Blo 1867635 25572131 := bstep (se 1 (by rfl) ⟨19179098, by rfl⟩ : syracuseStep 25572131 = 38358197) B38358197
theorem B4731767 : Blo 1867635 4731767 := bstep (se 1 (by rfl) ⟨3548825, by rfl⟩ : syracuseStep 4731767 = 7097651) B7097651
theorem B2102287 : Blo 1867635 2102287 := bstep (se 1 (by rfl) ⟨1576715, by rfl⟩ : syracuseStep 2102287 = 3153431) B3153431
theorem B2659387 : Blo 1867635 2659387 := bstep (se 1 (by rfl) ⟨1994540, by rfl⟩ : syracuseStep 2659387 = 3989081) B3989081
theorem B6067457 : Blo 1867635 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B6305039 : Blo 1867635 6305039 := bstep (se 1 (by rfl) ⟨4728779, by rfl⟩ : syracuseStep 6305039 = 9457559) B9457559
theorem B5985569 : Blo 1867635 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B2839865 : Blo 1867635 2839865 := bstep (se 2 (by rfl) ⟨1064949, by rfl⟩ : syracuseStep 2839865 = 2129899) B2129899
theorem B40408379 : Blo 1867635 40408379 := bstep (se 1 (by rfl) ⟨30306284, by rfl⟩ : syracuseStep 40408379 = 60612569) B60612569
theorem B23950727 : Blo 1867635 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B2364815 : Blo 1867635 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B2102791 : Blo 1867635 2102791 := bstep (se 1 (by rfl) ⟨1577093, by rfl⟩ : syracuseStep 2102791 = 3154187) B3154187
theorem B6305309 : Blo 1867635 6305309 := bstep (se 3 (by rfl) ⟨1182245, by rfl⟩ : syracuseStep 6305309 = 2364491) B2364491
theorem B7984669 : Blo 1867635 7984669 := bstep (se 3 (by rfl) ⟨1497125, by rfl⟩ : syracuseStep 7984669 = 2994251) B2994251
theorem B13473323 : Blo 1867635 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B10638935 : Blo 1867635 10638935 := bstep (se 1 (by rfl) ⟨7979201, by rfl⟩ : syracuseStep 10638935 = 15958403) B15958403
theorem B2102971 : Blo 1867635 2102971 := bstep (se 1 (by rfl) ⟨1577228, by rfl⟩ : syracuseStep 2102971 = 3154457) B3154457
theorem B2660087 : Blo 1867635 2660087 := bstep (se 1 (by rfl) ⟨1995065, by rfl⟩ : syracuseStep 2660087 = 3990131) B3990131
theorem B5682977 : Blo 1867635 5682977 := bstep (se 2 (by rfl) ⟨2131116, by rfl⟩ : syracuseStep 5682977 = 4262233) B4262233
theorem B5322611 : Blo 1867635 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B9459665 : Blo 1867635 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B22722565 : Blo 1867635 22722565 := bstep (se 4 (by rfl) ⟨2130240, by rfl⟩ : syracuseStep 22722565 = 4260481) B4260481
theorem B6731819 : Blo 1867635 6731819 := bstep (se 1 (by rfl) ⟨5048864, by rfl⟩ : syracuseStep 6731819 = 10097729) B10097729
theorem B38352941 : Blo 1867635 38352941 := bstep (se 3 (by rfl) ⟨7191176, by rfl⟩ : syracuseStep 38352941 = 14382353) B14382353
theorem B2734327 : Blo 1867635 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B5323067 : Blo 1867635 5323067 := bstep (se 1 (by rfl) ⟨3992300, by rfl⟩ : syracuseStep 5323067 = 7984601) B7984601
theorem B3152263 : Blo 1867635 3152263 := bstep (se 1 (by rfl) ⟨2364197, by rfl⟩ : syracuseStep 3152263 = 4728395) B4728395
theorem B22739345 : Blo 1867635 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B26933725 : Blo 1867635 26933725 := bstep (se 3 (by rfl) ⟨5050073, by rfl⟩ : syracuseStep 26933725 = 10100147) B10100147
theorem B12139037 : Blo 1867635 12139037 := bstep (se 3 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 12139037 = 4552139) B4552139
theorem B13130585 : Blo 1867635 13130585 := bstep (se 2 (by rfl) ⟨4923969, by rfl⟩ : syracuseStep 13130585 = 9847939) B9847939
theorem B6306713 : Blo 1867635 6306713 := bstep (se 2 (by rfl) ⟨2365017, by rfl⟩ : syracuseStep 6306713 = 4730035) B4730035
theorem B3152911 : Blo 1867635 3152911 := bstep (se 1 (by rfl) ⟨2364683, by rfl⟩ : syracuseStep 3152911 = 4729367) B4729367
theorem B7093277 : Blo 1867635 7093277 := bstep (se 3 (by rfl) ⟨1329989, by rfl⟩ : syracuseStep 7093277 = 2659979) B2659979
theorem B7093291 : Blo 1867635 7093291 := bstep (se 1 (by rfl) ⟨5319968, by rfl⟩ : syracuseStep 7093291 = 10639937) B10639937
theorem B5323819 : Blo 1867635 5323819 := bstep (se 1 (by rfl) ⟨3992864, by rfl⟩ : syracuseStep 5323819 = 7985729) B7985729
theorem B2661511 : Blo 1867635 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B8977601 : Blo 1867635 8977601 := bstep (se 2 (by rfl) ⟨3366600, by rfl⟩ : syracuseStep 8977601 = 6733201) B6733201
theorem B35904869 : Blo 1867635 35904869 := bstep (se 4 (by rfl) ⟨3366081, by rfl⟩ : syracuseStep 35904869 = 6732163) B6732163
theorem B3988883 : Blo 1867635 3988883 := bstep (se 1 (by rfl) ⟨2991662, by rfl⟩ : syracuseStep 3988883 = 5983325) B5983325
theorem B23944733 : Blo 1867635 23944733 := bstep (se 3 (by rfl) ⟨4489637, by rfl⟩ : syracuseStep 23944733 = 8979275) B8979275
theorem B3366443 : Blo 1867635 3366443 := bstep (se 1 (by rfl) ⟨2524832, by rfl⟩ : syracuseStep 3366443 = 5049665) B5049665
theorem B3153451 : Blo 1867635 3153451 := bstep (se 1 (by rfl) ⟨2365088, by rfl⟩ : syracuseStep 3153451 = 4730177) B4730177
theorem B6307415 : Blo 1867635 6307415 := bstep (se 1 (by rfl) ⟨4730561, by rfl⟩ : syracuseStep 6307415 = 9461123) B9461123
theorem B3153593 : Blo 1867635 3153593 := bstep (se 2 (by rfl) ⟨1182597, by rfl⟩ : syracuseStep 3153593 = 2365195) B2365195
theorem B2842297 : Blo 1867635 2842297 := bstep (se 2 (by rfl) ⟨1065861, by rfl⟩ : syracuseStep 2842297 = 2131723) B2131723
theorem B17964737 : Blo 1867635 17964737 := bstep (se 2 (by rfl) ⟨6736776, by rfl⟩ : syracuseStep 17964737 = 13473553) B13473553
theorem B2801465 : Blo 1867635 2801465 := bstep (se 2 (by rfl) ⟨1050549, by rfl⟩ : syracuseStep 2801465 = 2101099) B2101099
theorem B1867655 : Blo 1867635 1867655 := bstep (se 1 (by rfl) ⟨1400741, by rfl⟩ : syracuseStep 1867655 = 2801483) B2801483
theorem B2801543 : Blo 1867635 2801543 := bstep (se 1 (by rfl) ⟨2101157, by rfl⟩ : syracuseStep 2801543 = 4202315) B4202315
theorem B1867663 : Blo 1867635 1867663 := bstep (se 1 (by rfl) ⟨1400747, by rfl⟩ : syracuseStep 1867663 = 2801495) B2801495
theorem B3366803 : Blo 1867635 3366803 := bstep (se 1 (by rfl) ⟨2525102, by rfl⟩ : syracuseStep 3366803 = 5050205) B5050205
theorem B4202387 : Blo 1867635 4202387 := bstep (se 1 (by rfl) ⟨3151790, by rfl⟩ : syracuseStep 4202387 = 6303581) B6303581
theorem B13475747 : Blo 1867635 13475747 := bstep (se 1 (by rfl) ⟨10106810, by rfl⟩ : syracuseStep 13475747 = 20213621) B20213621
theorem B2801579 : Blo 1867635 2801579 := bstep (se 1 (by rfl) ⟨2101184, by rfl⟩ : syracuseStep 2801579 = 4202369) B4202369
theorem B1867707 : Blo 1867635 1867707 := bstep (se 1 (by rfl) ⟨1400780, by rfl⟩ : syracuseStep 1867707 = 2801561) B2801561
theorem B2801609 : Blo 1867635 2801609 := bstep (se 2 (by rfl) ⟨1050603, by rfl⟩ : syracuseStep 2801609 = 2101207) B2101207
theorem B4202441 : Blo 1867635 4202441 := bstep (se 2 (by rfl) ⟨1575915, by rfl⟩ : syracuseStep 4202441 = 3151831) B3151831
theorem B13131779 : Blo 1867635 13131779 := bstep (se 1 (by rfl) ⟨9848834, by rfl⟩ : syracuseStep 13131779 = 19697669) B19697669
theorem B6307847 : Blo 1867635 6307847 := bstep (se 1 (by rfl) ⟨4730885, by rfl⟩ : syracuseStep 6307847 = 9461771) B9461771
theorem B1867815 : Blo 1867635 1867815 := bstep (se 1 (by rfl) ⟨1400861, by rfl⟩ : syracuseStep 1867815 = 2801723) B2801723
theorem B1867855 : Blo 1867635 1867855 := bstep (se 1 (by rfl) ⟨1400891, by rfl⟩ : syracuseStep 1867855 = 2801783) B2801783
theorem B1867871 : Blo 1867635 1867871 := bstep (se 1 (by rfl) ⟨1400903, by rfl⟩ : syracuseStep 1867871 = 2801807) B2801807
theorem B6307955 : Blo 1867635 6307955 := bstep (se 1 (by rfl) ⟨4730966, by rfl⟩ : syracuseStep 6307955 = 9461933) B9461933
theorem B1867899 : Blo 1867635 1867899 := bstep (se 1 (by rfl) ⟨1400924, by rfl⟩ : syracuseStep 1867899 = 2801849) B2801849
theorem B3547307 : Blo 1867635 3547307 := bstep (se 1 (by rfl) ⟨2660480, by rfl⟩ : syracuseStep 3547307 = 5320961) B5320961
theorem B1867951 : Blo 1867635 1867951 := bstep (se 1 (by rfl) ⟨1400963, by rfl⟩ : syracuseStep 1867951 = 2801927) B2801927
theorem B1867975 : Blo 1867635 1867975 := bstep (se 1 (by rfl) ⟨1400981, by rfl⟩ : syracuseStep 1867975 = 2801963) B2801963
theorem B1867995 : Blo 1867635 1867995 := bstep (se 1 (by rfl) ⟨1400996, by rfl⟩ : syracuseStep 1867995 = 2801993) B2801993
theorem B11362571 : Blo 1867635 11362571 := bstep (se 1 (by rfl) ⟨8521928, by rfl⟩ : syracuseStep 11362571 = 17043857) B17043857
theorem B1868071 : Blo 1867635 1868071 := bstep (se 1 (by rfl) ⟨1401053, by rfl⟩ : syracuseStep 1868071 = 2802107) B2802107
theorem B1868111 : Blo 1867635 1868111 := bstep (se 1 (by rfl) ⟨1401083, by rfl⟩ : syracuseStep 1868111 = 2802167) B2802167
theorem B13467991 : Blo 1867635 13467991 := bstep (se 1 (by rfl) ⟨10100993, by rfl⟩ : syracuseStep 13467991 = 20201987) B20201987
theorem B1868127 : Blo 1867635 1868127 := bstep (se 1 (by rfl) ⟨1401095, by rfl⟩ : syracuseStep 1868127 = 2802191) B2802191
theorem B1868155 : Blo 1867635 1868155 := bstep (se 1 (by rfl) ⟨1401116, by rfl⟩ : syracuseStep 1868155 = 2802233) B2802233
theorem B6308225 : Blo 1867635 6308225 := bstep (se 2 (by rfl) ⟨2365584, by rfl⟩ : syracuseStep 6308225 = 4731169) B4731169
theorem B2802095 : Blo 1867635 2802095 := bstep (se 1 (by rfl) ⟨2101571, by rfl⟩ : syracuseStep 2802095 = 4203143) B4203143
theorem B1868207 : Blo 1867635 1868207 := bstep (se 1 (by rfl) ⟨1401155, by rfl⟩ : syracuseStep 1868207 = 2802311) B2802311
theorem B1868231 : Blo 1867635 1868231 := bstep (se 1 (by rfl) ⟨1401173, by rfl⟩ : syracuseStep 1868231 = 2802347) B2802347
theorem B1868251 : Blo 1867635 1868251 := bstep (se 1 (by rfl) ⟨1401188, by rfl⟩ : syracuseStep 1868251 = 2802377) B2802377
theorem B9585161 : Blo 1867635 9585161 := bstep (se 2 (by rfl) ⟨3594435, by rfl⟩ : syracuseStep 9585161 = 7188871) B7188871
theorem B4203017 : Blo 1867635 4203017 := bstep (se 2 (by rfl) ⟨1576131, by rfl⟩ : syracuseStep 4203017 = 3152263) B3152263
theorem B2802185 : Blo 1867635 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B17048087 : Blo 1867635 17048087 := bstep (se 1 (by rfl) ⟨12786065, by rfl⟩ : syracuseStep 17048087 = 25572131) B25572131
theorem B2802215 : Blo 1867635 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B1868327 : Blo 1867635 1868327 := bstep (se 1 (by rfl) ⟨1401245, by rfl⟩ : syracuseStep 1868327 = 2802491) B2802491
theorem B7979579 : Blo 1867635 7979579 := bstep (se 1 (by rfl) ⟨5984684, by rfl⟩ : syracuseStep 7979579 = 11969369) B11969369
theorem B1868367 : Blo 1867635 1868367 := bstep (se 1 (by rfl) ⟨1401275, by rfl⟩ : syracuseStep 1868367 = 2802551) B2802551
theorem B3154511 : Blo 1867635 3154511 := bstep (se 1 (by rfl) ⟨2365883, by rfl⟩ : syracuseStep 3154511 = 4731767) B4731767
theorem B1868383 : Blo 1867635 1868383 := bstep (se 1 (by rfl) ⟨1401287, by rfl⟩ : syracuseStep 1868383 = 2802575) B2802575
theorem B2802299 : Blo 1867635 2802299 := bstep (se 1 (by rfl) ⟨2101724, by rfl⟩ : syracuseStep 2802299 = 4203449) B4203449
theorem B1868411 : Blo 1867635 1868411 := bstep (se 1 (by rfl) ⟨1401308, by rfl⟩ : syracuseStep 1868411 = 2802617) B2802617
theorem B1868463 : Blo 1867635 1868463 := bstep (se 1 (by rfl) ⟨1401347, by rfl⟩ : syracuseStep 1868463 = 2802695) B2802695
theorem B1868487 : Blo 1867635 1868487 := bstep (se 1 (by rfl) ⟨1401365, by rfl⟩ : syracuseStep 1868487 = 2802731) B2802731
theorem B1868507 : Blo 1867635 1868507 := bstep (se 1 (by rfl) ⟨1401380, by rfl⟩ : syracuseStep 1868507 = 2802761) B2802761
theorem B2802425 : Blo 1867635 2802425 := bstep (se 2 (by rfl) ⟨1050909, by rfl⟩ : syracuseStep 2802425 = 2101819) B2101819
theorem B1868583 : Blo 1867635 1868583 := bstep (se 1 (by rfl) ⟨1401437, by rfl⟩ : syracuseStep 1868583 = 2802875) B2802875
theorem B1868623 : Blo 1867635 1868623 := bstep (se 1 (by rfl) ⟨1401467, by rfl⟩ : syracuseStep 1868623 = 2802935) B2802935
theorem B4203359 : Blo 1867635 4203359 := bstep (se 1 (by rfl) ⟨3152519, by rfl⟩ : syracuseStep 4203359 = 6305039) B6305039
theorem B2802527 : Blo 1867635 2802527 := bstep (se 1 (by rfl) ⟨2101895, by rfl⟩ : syracuseStep 2802527 = 4203791) B4203791
theorem B1868639 : Blo 1867635 1868639 := bstep (se 1 (by rfl) ⟨1401479, by rfl⟩ : syracuseStep 1868639 = 2802959) B2802959
theorem B2802539 : Blo 1867635 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B3990379 : Blo 1867635 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B1868667 : Blo 1867635 1868667 := bstep (se 1 (by rfl) ⟨1401500, by rfl⟩ : syracuseStep 1868667 = 2803001) B2803001
theorem B1868719 : Blo 1867635 1868719 := bstep (se 1 (by rfl) ⟨1401539, by rfl⟩ : syracuseStep 1868719 = 2803079) B2803079
theorem B15967151 : Blo 1867635 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B1868743 : Blo 1867635 1868743 := bstep (se 1 (by rfl) ⟨1401557, by rfl⟩ : syracuseStep 1868743 = 2803115) B2803115
theorem B1868763 : Blo 1867635 1868763 := bstep (se 1 (by rfl) ⟨1401572, by rfl⟩ : syracuseStep 1868763 = 2803145) B2803145
theorem B4203539 : Blo 1867635 4203539 := bstep (se 1 (by rfl) ⟨3152654, by rfl⟩ : syracuseStep 4203539 = 6305309) B6305309
theorem B1868839 : Blo 1867635 1868839 := bstep (se 1 (by rfl) ⟨1401629, by rfl⟩ : syracuseStep 1868839 = 2803259) B2803259
theorem B2802767 : Blo 1867635 2802767 := bstep (se 1 (by rfl) ⟨2102075, by rfl⟩ : syracuseStep 2802767 = 4204151) B4204151
theorem B1868879 : Blo 1867635 1868879 := bstep (se 1 (by rfl) ⟨1401659, by rfl⟩ : syracuseStep 1868879 = 2803319) B2803319
theorem B1868895 : Blo 1867635 1868895 := bstep (se 1 (by rfl) ⟨1401671, by rfl⟩ : syracuseStep 1868895 = 2803343) B2803343
theorem B1868923 : Blo 1867635 1868923 := bstep (se 1 (by rfl) ⟨1401692, by rfl⟩ : syracuseStep 1868923 = 2803385) B2803385
theorem B6309035 : Blo 1867635 6309035 := bstep (se 1 (by rfl) ⟨4731776, by rfl⟩ : syracuseStep 6309035 = 9463553) B9463553
theorem B1868975 : Blo 1867635 1868975 := bstep (se 1 (by rfl) ⟨1401731, by rfl⟩ : syracuseStep 1868975 = 2803463) B2803463
theorem B7980227 : Blo 1867635 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B2802887 : Blo 1867635 2802887 := bstep (se 1 (by rfl) ⟨2102165, by rfl⟩ : syracuseStep 2802887 = 4204331) B4204331
theorem B1868999 : Blo 1867635 1868999 := bstep (se 1 (by rfl) ⟨1401749, by rfl⟩ : syracuseStep 1868999 = 2803499) B2803499
theorem B1869019 : Blo 1867635 1869019 := bstep (se 1 (by rfl) ⟨1401764, by rfl⟩ : syracuseStep 1869019 = 2803529) B2803529
theorem B14583077 : Blo 1867635 14583077 := bstep (se 4 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 14583077 = 2734327) B2734327
theorem B1869095 : Blo 1867635 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B1869135 : Blo 1867635 1869135 := bstep (se 1 (by rfl) ⟨1401851, by rfl⟩ : syracuseStep 1869135 = 2803703) B2803703
theorem B1869151 : Blo 1867635 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B4203881 : Blo 1867635 4203881 := bstep (se 2 (by rfl) ⟨1576455, by rfl⟩ : syracuseStep 4203881 = 3152911) B3152911
theorem B2803049 : Blo 1867635 2803049 := bstep (se 2 (by rfl) ⟨1051143, by rfl⟩ : syracuseStep 2803049 = 2102287) B2102287
theorem B25568627 : Blo 1867635 25568627 := bstep (se 1 (by rfl) ⟨19176470, by rfl⟩ : syracuseStep 25568627 = 38352941) B38352941
theorem B1869179 : Blo 1867635 1869179 := bstep (se 1 (by rfl) ⟨1401884, by rfl⟩ : syracuseStep 1869179 = 2803769) B2803769
theorem B10642853 : Blo 1867635 10642853 := bstep (se 4 (by rfl) ⟨997767, by rfl⟩ : syracuseStep 10642853 = 1995535) B1995535
theorem B1869231 : Blo 1867635 1869231 := bstep (se 1 (by rfl) ⟨1401923, by rfl⟩ : syracuseStep 1869231 = 2803847) B2803847
theorem B2803127 : Blo 1867635 2803127 := bstep (se 1 (by rfl) ⟨2102345, by rfl⟩ : syracuseStep 2803127 = 4204691) B4204691
theorem B1869255 : Blo 1867635 1869255 := bstep (se 1 (by rfl) ⟨1401941, by rfl⟩ : syracuseStep 1869255 = 2803883) B2803883
theorem B2803163 : Blo 1867635 2803163 := bstep (se 1 (by rfl) ⟨2102372, by rfl⟩ : syracuseStep 2803163 = 4204745) B4204745
theorem B1869275 : Blo 1867635 1869275 := bstep (se 1 (by rfl) ⟨1401956, by rfl⟩ : syracuseStep 1869275 = 2803913) B2803913
theorem B3548681 : Blo 1867635 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B3786259 : Blo 1867635 3786259 := bstep (se 1 (by rfl) ⟨2839694, by rfl⟩ : syracuseStep 3786259 = 5679389) B5679389
theorem B3548711 : Blo 1867635 3548711 := bstep (se 1 (by rfl) ⟨2661533, by rfl⟩ : syracuseStep 3548711 = 5323067) B5323067
theorem B1869351 : Blo 1867635 1869351 := bstep (se 1 (by rfl) ⟨1402013, by rfl⟩ : syracuseStep 1869351 = 2804027) B2804027
theorem B1869391 : Blo 1867635 1869391 := bstep (se 1 (by rfl) ⟨1402043, by rfl⟩ : syracuseStep 1869391 = 2804087) B2804087
theorem B1869407 : Blo 1867635 1869407 := bstep (se 1 (by rfl) ⟨1402055, by rfl⟩ : syracuseStep 1869407 = 2804111) B2804111
theorem B1869435 : Blo 1867635 1869435 := bstep (se 1 (by rfl) ⟨1402076, by rfl⟩ : syracuseStep 1869435 = 2804153) B2804153
theorem B14190227 : Blo 1867635 14190227 := bstep (se 1 (by rfl) ⟨10642670, by rfl⟩ : syracuseStep 14190227 = 21285341) B21285341
theorem B1869487 : Blo 1867635 1869487 := bstep (se 1 (by rfl) ⟨1402115, by rfl⟩ : syracuseStep 1869487 = 2804231) B2804231
theorem B6309575 : Blo 1867635 6309575 := bstep (se 1 (by rfl) ⟨4732181, by rfl⟩ : syracuseStep 6309575 = 9464363) B9464363
theorem B1869511 : Blo 1867635 1869511 := bstep (se 1 (by rfl) ⟨1402133, by rfl⟩ : syracuseStep 1869511 = 2804267) B2804267
theorem B1869531 : Blo 1867635 1869531 := bstep (se 1 (by rfl) ⟨1402148, by rfl⟩ : syracuseStep 1869531 = 2804297) B2804297
theorem B8980217 : Blo 1867635 8980217 := bstep (se 2 (by rfl) ⟨3367581, by rfl⟩ : syracuseStep 8980217 = 6735163) B6735163
theorem B1869607 : Blo 1867635 1869607 := bstep (se 1 (by rfl) ⟨1402205, by rfl⟩ : syracuseStep 1869607 = 2804411) B2804411
theorem B10643309 : Blo 1867635 10643309 := bstep (se 3 (by rfl) ⟨1995620, by rfl⟩ : syracuseStep 10643309 = 3991241) B3991241
theorem B2803631 : Blo 1867635 2803631 := bstep (se 1 (by rfl) ⟨2102723, by rfl⟩ : syracuseStep 2803631 = 4205447) B4205447
theorem B4204475 : Blo 1867635 4204475 := bstep (se 1 (by rfl) ⟨3153356, by rfl⟩ : syracuseStep 4204475 = 6306713) B6306713
theorem B2803721 : Blo 1867635 2803721 := bstep (se 2 (by rfl) ⟨1051395, by rfl⟩ : syracuseStep 2803721 = 2102791) B2102791
theorem B4728851 : Blo 1867635 4728851 := bstep (se 1 (by rfl) ⟨3546638, by rfl⟩ : syracuseStep 4728851 = 7093277) B7093277
theorem B2803751 : Blo 1867635 2803751 := bstep (se 1 (by rfl) ⟨2102813, by rfl⟩ : syracuseStep 2803751 = 4205627) B4205627
theorem B4204601 : Blo 1867635 4204601 := bstep (se 2 (by rfl) ⟨1576725, by rfl⟩ : syracuseStep 4204601 = 3153451) B3153451
theorem B3991609 : Blo 1867635 3991609 := bstep (se 2 (by rfl) ⟨1496853, by rfl⟩ : syracuseStep 3991609 = 2993707) B2993707
theorem B2803835 : Blo 1867635 2803835 := bstep (se 1 (by rfl) ⟨2102876, by rfl⟩ : syracuseStep 2803835 = 4205753) B4205753
theorem B2525383 : Blo 1867635 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B2803961 : Blo 1867635 2803961 := bstep (se 2 (by rfl) ⟨1051485, by rfl⟩ : syracuseStep 2803961 = 2102971) B2102971
theorem B2804063 : Blo 1867635 2804063 := bstep (se 1 (by rfl) ⟨2103047, by rfl⟩ : syracuseStep 2804063 = 4206095) B4206095
theorem B2804075 : Blo 1867635 2804075 := bstep (se 1 (by rfl) ⟨2103056, by rfl⟩ : syracuseStep 2804075 = 4206113) B4206113
theorem B4204943 : Blo 1867635 4204943 := bstep (se 1 (by rfl) ⟨3153707, by rfl⟩ : syracuseStep 4204943 = 6307415) B6307415
theorem B14182937 : Blo 1867635 14182937 := bstep (se 2 (by rfl) ⟨5318601, by rfl⟩ : syracuseStep 14182937 = 10637203) B10637203
theorem B10643993 : Blo 1867635 10643993 := bstep (se 2 (by rfl) ⟨3991497, by rfl⟩ : syracuseStep 10643993 = 7982995) B7982995
theorem B2804303 : Blo 1867635 2804303 := bstep (se 1 (by rfl) ⟨2103227, by rfl⟩ : syracuseStep 2804303 = 4206455) B4206455
theorem B9456263 : Blo 1867635 9456263 := bstep (se 1 (by rfl) ⟨7092197, by rfl⟩ : syracuseStep 9456263 = 14184395) B14184395
theorem B7096967 : Blo 1867635 7096967 := bstep (se 1 (by rfl) ⟨5322725, by rfl⟩ : syracuseStep 7096967 = 10645451) B10645451
theorem B30296753 : Blo 1867635 30296753 := bstep (se 2 (by rfl) ⟨11361282, by rfl⟩ : syracuseStep 30296753 = 22722565) B22722565
theorem B2804423 : Blo 1867635 2804423 := bstep (se 1 (by rfl) ⟨2103317, by rfl⟩ : syracuseStep 2804423 = 4206635) B4206635
theorem B4205267 : Blo 1867635 4205267 := bstep (se 1 (by rfl) ⟨3153950, by rfl⟩ : syracuseStep 4205267 = 6307901) B6307901
theorem B31148875 : Blo 1867635 31148875 := bstep (se 1 (by rfl) ⟨23361656, by rfl⟩ : syracuseStep 31148875 = 46723313) B46723313
theorem B15158339 : Blo 1867635 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B23940269 : Blo 1867635 23940269 := bstep (se 3 (by rfl) ⟨4488800, by rfl⟩ : syracuseStep 23940269 = 8977601) B8977601
theorem B7572973 : Blo 1867635 7572973 := bstep (se 3 (by rfl) ⟨1419932, by rfl⟩ : syracuseStep 7572973 = 2839865) B2839865
theorem B11972083 : Blo 1867635 11972083 := bstep (se 1 (by rfl) ⟨8979062, by rfl⟩ : syracuseStep 11972083 = 17958125) B17958125
theorem B26938919 : Blo 1867635 26938919 := bstep (se 1 (by rfl) ⟨20204189, by rfl⟩ : syracuseStep 26938919 = 40408379) B40408379
theorem B4206203 : Blo 1867635 4206203 := bstep (se 1 (by rfl) ⟨3154652, by rfl⟩ : syracuseStep 4206203 = 6309305) B6309305
theorem B15158917 : Blo 1867635 15158917 := bstep (se 4 (by rfl) ⟨1421148, by rfl⟩ : syracuseStep 15158917 = 2842297) B2842297
theorem B8982215 : Blo 1867635 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B10637021 : Blo 1867635 10637021 := bstep (se 3 (by rfl) ⟨1994441, by rfl⟩ : syracuseStep 10637021 = 3988883) B3988883
theorem B4206329 : Blo 1867635 4206329 := bstep (se 2 (by rfl) ⟨1577373, by rfl⟩ : syracuseStep 4206329 = 3154747) B3154747
theorem B20197187 : Blo 1867635 20197187 := bstep (se 1 (by rfl) ⟨15147890, by rfl⟩ : syracuseStep 20197187 = 30295781) B30295781
theorem B3788651 : Blo 1867635 3788651 := bstep (se 1 (by rfl) ⟨2841488, by rfl⟩ : syracuseStep 3788651 = 5682977) B5682977
theorem B13463405 : Blo 1867635 13463405 := bstep (se 3 (by rfl) ⟨2524388, by rfl⟩ : syracuseStep 13463405 = 5048777) B5048777
theorem B4206599 : Blo 1867635 4206599 := bstep (se 1 (by rfl) ⟨3154949, by rfl⟩ : syracuseStep 4206599 = 6309899) B6309899
theorem B9457721 : Blo 1867635 9457721 := bstep (se 2 (by rfl) ⟨3546645, by rfl⟩ : syracuseStep 9457721 = 7093291) B7093291
theorem B7098425 : Blo 1867635 7098425 := bstep (se 2 (by rfl) ⟨2661909, by rfl⟩ : syracuseStep 7098425 = 5323819) B5323819
theorem B4206671 : Blo 1867635 4206671 := bstep (se 1 (by rfl) ⟨3155003, by rfl⟩ : syracuseStep 4206671 = 6310007) B6310007
theorem B2994425 : Blo 1867635 2994425 := bstep (se 2 (by rfl) ⟨1122909, by rfl⟩ : syracuseStep 2994425 = 2245819) B2245819
theorem B15159563 : Blo 1867635 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B2994527 : Blo 1867635 2994527 := bstep (se 1 (by rfl) ⟨2245895, by rfl⟩ : syracuseStep 2994527 = 4491791) B4491791
theorem B15970841 : Blo 1867635 15970841 := bstep (se 2 (by rfl) ⟨5989065, by rfl⟩ : syracuseStep 15970841 = 11978131) B11978131
theorem B8753723 : Blo 1867635 8753723 := bstep (se 1 (by rfl) ⟨6565292, by rfl⟩ : syracuseStep 8753723 = 13130585) B13130585
theorem B6304391 : Blo 1867635 6304391 := bstep (se 1 (by rfl) ⟨4728293, by rfl⟩ : syracuseStep 6304391 = 9456587) B9456587
theorem B6304445 : Blo 1867635 6304445 := bstep (se 3 (by rfl) ⟨1182083, by rfl⟩ : syracuseStep 6304445 = 2364167) B2364167
theorem B1995463 : Blo 1867635 1995463 := bstep (se 1 (by rfl) ⟨1496597, by rfl⟩ : syracuseStep 1995463 = 2993195) B2993195
theorem B10646225 : Blo 1867635 10646225 := bstep (se 2 (by rfl) ⟨3992334, by rfl⟩ : syracuseStep 10646225 = 7984669) B7984669
theorem B6304607 : Blo 1867635 6304607 := bstep (se 1 (by rfl) ⟨4728455, by rfl⟩ : syracuseStep 6304607 = 9456911) B9456911
theorem B14193629 : Blo 1867635 14193629 := bstep (se 3 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 14193629 = 5322611) B5322611
theorem B6304769 : Blo 1867635 6304769 := bstep (se 2 (by rfl) ⟨2364288, by rfl⟩ : syracuseStep 6304769 = 4728577) B4728577
theorem B15963155 : Blo 1867635 15963155 := bstep (se 1 (by rfl) ⟨11972366, by rfl⟩ : syracuseStep 15963155 = 23944733) B23944733
theorem B23344193 : Blo 1867635 23344193 := bstep (se 2 (by rfl) ⟨8754072, by rfl⟩ : syracuseStep 23344193 = 17508145) B17508145
theorem B2102395 : Blo 1867635 2102395 := bstep (se 1 (by rfl) ⟨1576796, by rfl⟩ : syracuseStep 2102395 = 3153593) B3153593
theorem B28054745 : Blo 1867635 28054745 := bstep (se 2 (by rfl) ⟨10520529, by rfl⟩ : syracuseStep 28054745 = 21041059) B21041059
theorem B8983831 : Blo 1867635 8983831 := bstep (se 1 (by rfl) ⟨6737873, by rfl⟩ : syracuseStep 8983831 = 13475747) B13475747
theorem B52573541 : Blo 1867635 52573541 := bstep (se 4 (by rfl) ⟨4928769, by rfl⟩ : syracuseStep 52573541 = 9857539) B9857539
theorem B20477299 : Blo 1867635 20477299 := bstep (se 1 (by rfl) ⟨15357974, by rfl⟩ : syracuseStep 20477299 = 30715949) B30715949
theorem B14185853 : Blo 1867635 14185853 := bstep (se 3 (by rfl) ⟨2659847, by rfl⟩ : syracuseStep 14185853 = 5319695) B5319695
theorem B10646909 : Blo 1867635 10646909 := bstep (se 3 (by rfl) ⟨1996295, by rfl⟩ : syracuseStep 10646909 = 3992591) B3992591
theorem B11974031 : Blo 1867635 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B4732303 : Blo 1867635 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B14390729 : Blo 1867635 14390729 := bstep (se 2 (by rfl) ⟨5396523, by rfl⟩ : syracuseStep 14390729 = 10793047) B10793047
theorem B5051891 : Blo 1867635 5051891 := bstep (se 1 (by rfl) ⟨3788918, by rfl⟩ : syracuseStep 5051891 = 7577837) B7577837
theorem B2364967 : Blo 1867635 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B2102863 : Blo 1867635 2102863 := bstep (se 1 (by rfl) ⟨1577147, by rfl⟩ : syracuseStep 2102863 = 3154295) B3154295
theorem B5117651 : Blo 1867635 5117651 := bstep (se 1 (by rfl) ⟨3838238, by rfl⟩ : syracuseStep 5117651 = 7676477) B7676477
theorem B6305579 : Blo 1867635 6305579 := bstep (se 1 (by rfl) ⟨4729184, by rfl⟩ : syracuseStep 6305579 = 9458369) B9458369
theorem B3151723 : Blo 1867635 3151723 := bstep (se 1 (by rfl) ⟨2363792, by rfl⟩ : syracuseStep 3151723 = 4727585) B4727585
theorem B2365291 : Blo 1867635 2365291 := bstep (se 1 (by rfl) ⟨1773968, by rfl⟩ : syracuseStep 2365291 = 3547937) B3547937
theorem B5117879 : Blo 1867635 5117879 := bstep (se 1 (by rfl) ⟨3838409, by rfl⟩ : syracuseStep 5117879 = 7676819) B7676819
theorem B5052347 : Blo 1867635 5052347 := bstep (se 1 (by rfl) ⟨3789260, by rfl⟩ : syracuseStep 5052347 = 7578521) B7578521
theorem B35911633 : Blo 1867635 35911633 := bstep (se 2 (by rfl) ⟨13466862, by rfl⟩ : syracuseStep 35911633 = 26933725) B26933725
theorem B2103259 : Blo 1867635 2103259 := bstep (se 1 (by rfl) ⟨1577444, by rfl⟩ : syracuseStep 2103259 = 3154889) B3154889
theorem B6305849 : Blo 1867635 6305849 := bstep (se 2 (by rfl) ⟨2364693, by rfl⟩ : syracuseStep 6305849 = 4729387) B4729387
theorem B2365519 : Blo 1867635 2365519 := bstep (se 1 (by rfl) ⟨1774139, by rfl⟩ : syracuseStep 2365519 = 3548279) B3548279
theorem B7092305 : Blo 1867635 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B9459827 : Blo 1867635 9459827 := bstep (se 1 (by rfl) ⟨7094870, by rfl⟩ : syracuseStep 9459827 = 14189741) B14189741
theorem B4044971 : Blo 1867635 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B6306173 : Blo 1867635 6306173 := bstep (se 3 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 6306173 = 2364815) B2364815
theorem B31938947 : Blo 1867635 31938947 := bstep (se 1 (by rfl) ⟨23954210, by rfl⟩ : syracuseStep 31938947 = 47908421) B47908421
theorem B7092623 : Blo 1867635 7092623 := bstep (se 1 (by rfl) ⟨5319467, by rfl⟩ : syracuseStep 7092623 = 10638935) B10638935
theorem B3840475 : Blo 1867635 3840475 := bstep (se 1 (by rfl) ⟨2880356, by rfl⟩ : syracuseStep 3840475 = 5760713) B5760713
theorem B6306443 : Blo 1867635 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B4487879 : Blo 1867635 4487879 := bstep (se 1 (by rfl) ⟨3365909, by rfl⟩ : syracuseStep 4487879 = 6731819) B6731819
theorem B6732497 : Blo 1867635 6732497 := bstep (se 2 (by rfl) ⟨2524686, by rfl⟩ : syracuseStep 6732497 = 5049373) B5049373
theorem B3545849 : Blo 1867635 3545849 := bstep (se 2 (by rfl) ⟨1329693, by rfl⟩ : syracuseStep 3545849 = 2659387) B2659387
theorem B3152783 : Blo 1867635 3152783 := bstep (se 1 (by rfl) ⟨2364587, by rfl⟩ : syracuseStep 3152783 = 4729175) B4729175
theorem B3546031 : Blo 1867635 3546031 := bstep (se 1 (by rfl) ⟨2659523, by rfl⟩ : syracuseStep 3546031 = 5319047) B5319047
theorem B8092691 : Blo 1867635 8092691 := bstep (se 1 (by rfl) ⟨6069518, by rfl⟩ : syracuseStep 8092691 = 12139037) B12139037
theorem B3153019 : Blo 1867635 3153019 := bstep (se 1 (by rfl) ⟨2364764, by rfl⟩ : syracuseStep 3153019 = 4729529) B4729529
theorem B71842949 : Blo 1867635 71842949 := bstep (se 4 (by rfl) ⟨6735276, by rfl⟩ : syracuseStep 71842949 = 13470553) B13470553
theorem B2841799 : Blo 1867635 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B7093565 : Blo 1867635 7093565 := bstep (se 3 (by rfl) ⟨1330043, by rfl⟩ : syracuseStep 7093565 = 2660087) B2660087
theorem B6307361 : Blo 1867635 6307361 := bstep (se 2 (by rfl) ⟨2365260, by rfl⟩ : syracuseStep 6307361 = 4730521) B4730521
theorem B23936579 : Blo 1867635 23936579 := bstep (se 1 (by rfl) ⟨17952434, by rfl⟩ : syracuseStep 23936579 = 35904869) B35904869
theorem B3989191 : Blo 1867635 3989191 := bstep (se 1 (by rfl) ⟨2991893, by rfl⟩ : syracuseStep 3989191 = 5983787) B5983787
theorem B2244295 : Blo 1867635 2244295 := bstep (se 1 (by rfl) ⟨1683221, by rfl⟩ : syracuseStep 2244295 = 3366443) B3366443
theorem B9461447 : Blo 1867635 9461447 := bstep (se 1 (by rfl) ⟨7096085, by rfl⟩ : syracuseStep 9461447 = 14192171) B14192171
theorem B8978141 : Blo 1867635 8978141 := bstep (se 3 (by rfl) ⟨1683401, by rfl⟩ : syracuseStep 8978141 = 3366803) B3366803
theorem B6307577 : Blo 1867635 6307577 := bstep (se 2 (by rfl) ⟨2365341, by rfl⟩ : syracuseStep 6307577 = 4730683) B4730683
theorem B11976491 : Blo 1867635 11976491 := bstep (se 1 (by rfl) ⟨8982368, by rfl⟩ : syracuseStep 11976491 = 17964737) B17964737
theorem B2801513 : Blo 1867635 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B1867643 : Blo 1867635 1867643 := bstep (se 1 (by rfl) ⟨1400732, by rfl⟩ : syracuseStep 1867643 = 2801465) B2801465
theorem B1867695 : Blo 1867635 1867695 := bstep (se 1 (by rfl) ⟨1400771, by rfl⟩ : syracuseStep 1867695 = 2801543) B2801543
theorem B2801591 : Blo 1867635 2801591 := bstep (se 1 (by rfl) ⟨2101193, by rfl⟩ : syracuseStep 2801591 = 4202387) B4202387
theorem B4202423 : Blo 1867635 4202423 := bstep (se 1 (by rfl) ⟨3151817, by rfl⟩ : syracuseStep 4202423 = 6303635) B6303635
theorem B1867719 : Blo 1867635 1867719 := bstep (se 1 (by rfl) ⟨1400789, by rfl⟩ : syracuseStep 1867719 = 2801579) B2801579
theorem B1867739 : Blo 1867635 1867739 := bstep (se 1 (by rfl) ⟨1400804, by rfl⟩ : syracuseStep 1867739 = 2801609) B2801609
theorem B2801627 : Blo 1867635 2801627 := bstep (se 1 (by rfl) ⟨2101220, by rfl⟩ : syracuseStep 2801627 = 4202441) B4202441
theorem B3153883 : Blo 1867635 3153883 := bstep (se 1 (by rfl) ⟨2365412, by rfl⟩ : syracuseStep 3153883 = 4730825) B4730825
theorem B3154025 : Blo 1867635 3154025 := bstep (se 2 (by rfl) ⟨1182759, by rfl⟩ : syracuseStep 3154025 = 2365519) B2365519
theorem B3367177 : Blo 1867635 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B1868063 : Blo 1867635 1868063 := bstep (se 1 (by rfl) ⟨1401047, by rfl⟩ : syracuseStep 1868063 = 2802095) B2802095
theorem B6390107 : Blo 1867635 6390107 := bstep (se 1 (by rfl) ⟨4792580, by rfl⟩ : syracuseStep 6390107 = 9585161) B9585161
theorem B2802011 : Blo 1867635 2802011 := bstep (se 1 (by rfl) ⟨2101508, by rfl⟩ : syracuseStep 2802011 = 4203017) B4203017
theorem B1868123 : Blo 1867635 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B1868143 : Blo 1867635 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B1868199 : Blo 1867635 1868199 := bstep (se 1 (by rfl) ⟨1401149, by rfl⟩ : syracuseStep 1868199 = 2802299) B2802299
theorem B4202927 : Blo 1867635 4202927 := bstep (se 1 (by rfl) ⟨3152195, by rfl⟩ : syracuseStep 4202927 = 6304391) B6304391
theorem B17957321 : Blo 1867635 17957321 := bstep (se 2 (by rfl) ⟨6733995, by rfl⟩ : syracuseStep 17957321 = 13467991) B13467991
theorem B4202963 : Blo 1867635 4202963 := bstep (se 1 (by rfl) ⟨3152222, by rfl⟩ : syracuseStep 4202963 = 6304445) B6304445
theorem B1868283 : Blo 1867635 1868283 := bstep (se 1 (by rfl) ⟨1401212, by rfl⟩ : syracuseStep 1868283 = 2802425) B2802425
theorem B4203071 : Blo 1867635 4203071 := bstep (se 1 (by rfl) ⟨3152303, by rfl⟩ : syracuseStep 4203071 = 6304607) B6304607
theorem B2802239 : Blo 1867635 2802239 := bstep (se 1 (by rfl) ⟨2101679, by rfl⟩ : syracuseStep 2802239 = 4203359) B4203359
theorem B1868351 : Blo 1867635 1868351 := bstep (se 1 (by rfl) ⟨1401263, by rfl⟩ : syracuseStep 1868351 = 2802527) B2802527
theorem B1868359 : Blo 1867635 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B5120633 : Blo 1867635 5120633 := bstep (se 2 (by rfl) ⟨1920237, by rfl⟩ : syracuseStep 5120633 = 3840475) B3840475
theorem B9462419 : Blo 1867635 9462419 := bstep (se 1 (by rfl) ⟨7096814, by rfl⟩ : syracuseStep 9462419 = 14193629) B14193629
theorem B4203179 : Blo 1867635 4203179 := bstep (se 1 (by rfl) ⟨3152384, by rfl⟩ : syracuseStep 4203179 = 6304769) B6304769
theorem B2802359 : Blo 1867635 2802359 := bstep (se 1 (by rfl) ⟨2101769, by rfl⟩ : syracuseStep 2802359 = 4203539) B4203539
theorem B10642103 : Blo 1867635 10642103 := bstep (se 1 (by rfl) ⟨7981577, by rfl⟩ : syracuseStep 10642103 = 15963155) B15963155
theorem B1868511 : Blo 1867635 1868511 := bstep (se 1 (by rfl) ⟨1401383, by rfl⟩ : syracuseStep 1868511 = 2802767) B2802767
theorem B1868591 : Blo 1867635 1868591 := bstep (se 1 (by rfl) ⟨1401443, by rfl⟩ : syracuseStep 1868591 = 2802887) B2802887
theorem B18703163 : Blo 1867635 18703163 := bstep (se 1 (by rfl) ⟨14027372, by rfl⟩ : syracuseStep 18703163 = 28054745) B28054745
theorem B2802587 : Blo 1867635 2802587 := bstep (se 1 (by rfl) ⟨2101940, by rfl⟩ : syracuseStep 2802587 = 4203881) B4203881
theorem B1868699 : Blo 1867635 1868699 := bstep (se 1 (by rfl) ⟨1401524, by rfl⟩ : syracuseStep 1868699 = 2803049) B2803049
theorem B7095235 : Blo 1867635 7095235 := bstep (se 1 (by rfl) ⟨5321426, by rfl⟩ : syracuseStep 7095235 = 10642853) B10642853
theorem B1868751 : Blo 1867635 1868751 := bstep (se 1 (by rfl) ⟨1401563, by rfl⟩ : syracuseStep 1868751 = 2803127) B2803127
theorem B68183005 : Blo 1867635 68183005 := bstep (se 3 (by rfl) ⟨12784313, by rfl⟩ : syracuseStep 68183005 = 25568627) B25568627
theorem B9593819 : Blo 1867635 9593819 := bstep (se 1 (by rfl) ⟨7195364, by rfl⟩ : syracuseStep 9593819 = 14390729) B14390729
theorem B1868775 : Blo 1867635 1868775 := bstep (se 1 (by rfl) ⟨1401581, by rfl⟩ : syracuseStep 1868775 = 2803163) B2803163
theorem B3367927 : Blo 1867635 3367927 := bstep (se 1 (by rfl) ⟨2525945, by rfl⟩ : syracuseStep 3367927 = 5051891) B5051891
theorem B4203719 : Blo 1867635 4203719 := bstep (se 1 (by rfl) ⟨3152789, by rfl⟩ : syracuseStep 4203719 = 6305579) B6305579
theorem B4728041 : Blo 1867635 4728041 := bstep (se 2 (by rfl) ⟨1773015, by rfl⟩ : syracuseStep 4728041 = 3546031) B3546031
theorem B7095539 : Blo 1867635 7095539 := bstep (se 1 (by rfl) ⟨5321654, by rfl⟩ : syracuseStep 7095539 = 10643309) B10643309
theorem B1869087 : Blo 1867635 1869087 := bstep (se 1 (by rfl) ⟨1401815, by rfl⟩ : syracuseStep 1869087 = 2803631) B2803631
theorem B2802983 : Blo 1867635 2802983 := bstep (se 1 (by rfl) ⟨2102237, by rfl⟩ : syracuseStep 2802983 = 4204475) B4204475
theorem B3368231 : Blo 1867635 3368231 := bstep (se 1 (by rfl) ⟨2526173, by rfl⟩ : syracuseStep 3368231 = 5052347) B5052347
theorem B1869147 : Blo 1867635 1869147 := bstep (se 1 (by rfl) ⟨1401860, by rfl⟩ : syracuseStep 1869147 = 2803721) B2803721
theorem B1869167 : Blo 1867635 1869167 := bstep (se 1 (by rfl) ⟨1401875, by rfl⟩ : syracuseStep 1869167 = 2803751) B2803751
theorem B4203899 : Blo 1867635 4203899 := bstep (se 1 (by rfl) ⟨3152924, by rfl⟩ : syracuseStep 4203899 = 6305849) B6305849
theorem B2803067 : Blo 1867635 2803067 := bstep (se 1 (by rfl) ⟨2102300, by rfl⟩ : syracuseStep 2803067 = 4204601) B4204601
theorem B4728203 : Blo 1867635 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B1869223 : Blo 1867635 1869223 := bstep (se 1 (by rfl) ⟨1401917, by rfl⟩ : syracuseStep 1869223 = 2803835) B2803835
theorem B9463229 : Blo 1867635 9463229 := bstep (se 3 (by rfl) ⟨1774355, by rfl⟩ : syracuseStep 9463229 = 3548711) B3548711
theorem B2696647 : Blo 1867635 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B4204025 : Blo 1867635 4204025 := bstep (se 2 (by rfl) ⟨1576509, by rfl⟩ : syracuseStep 4204025 = 3153019) B3153019
theorem B2803193 : Blo 1867635 2803193 := bstep (se 2 (by rfl) ⟨1051197, by rfl⟩ : syracuseStep 2803193 = 2102395) B2102395
theorem B1869307 : Blo 1867635 1869307 := bstep (se 1 (by rfl) ⟨1401980, by rfl⟩ : syracuseStep 1869307 = 2803961) B2803961
theorem B1869375 : Blo 1867635 1869375 := bstep (se 1 (by rfl) ⟨1402031, by rfl⟩ : syracuseStep 1869375 = 2804063) B2804063
theorem B1869383 : Blo 1867635 1869383 := bstep (se 1 (by rfl) ⟨1402037, by rfl⟩ : syracuseStep 1869383 = 2804075) B2804075
theorem B4204115 : Blo 1867635 4204115 := bstep (se 1 (by rfl) ⟨3153086, by rfl⟩ : syracuseStep 4204115 = 6306173) B6306173
theorem B21292631 : Blo 1867635 21292631 := bstep (se 1 (by rfl) ⟨15969473, by rfl⟩ : syracuseStep 21292631 = 31938947) B31938947
theorem B4728415 : Blo 1867635 4728415 := bstep (se 1 (by rfl) ⟨3546311, by rfl⟩ : syracuseStep 4728415 = 7092623) B7092623
theorem B2803295 : Blo 1867635 2803295 := bstep (se 1 (by rfl) ⟨2102471, by rfl⟩ : syracuseStep 2803295 = 4204943) B4204943
theorem B9455291 : Blo 1867635 9455291 := bstep (se 1 (by rfl) ⟨7091468, by rfl⟩ : syracuseStep 9455291 = 14182937) B14182937
theorem B7095995 : Blo 1867635 7095995 := bstep (se 1 (by rfl) ⟨5321996, by rfl⟩ : syracuseStep 7095995 = 10643993) B10643993
theorem B11978441 : Blo 1867635 11978441 := bstep (se 2 (by rfl) ⟨4491915, by rfl⟩ : syracuseStep 11978441 = 8983831) B8983831
theorem B1869535 : Blo 1867635 1869535 := bstep (se 1 (by rfl) ⟨1402151, by rfl⟩ : syracuseStep 1869535 = 2804303) B2804303
theorem B166127333 : Blo 1867635 166127333 := bstep (se 4 (by rfl) ⟨15574437, by rfl⟩ : syracuseStep 166127333 = 31148875) B31148875
theorem B4204295 : Blo 1867635 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2991919 : Blo 1867635 2991919 := bstep (se 1 (by rfl) ⟨2243939, by rfl⟩ : syracuseStep 2991919 = 4487879) B4487879
theorem B1869615 : Blo 1867635 1869615 := bstep (se 1 (by rfl) ⟨1402211, by rfl⟩ : syracuseStep 1869615 = 2804423) B2804423
theorem B2803511 : Blo 1867635 2803511 := bstep (se 1 (by rfl) ⟨2102633, by rfl⟩ : syracuseStep 2803511 = 4205267) B4205267
theorem B6309737 : Blo 1867635 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B5048345 : Blo 1867635 5048345 := bstep (se 2 (by rfl) ⟨1893129, by rfl⟩ : syracuseStep 5048345 = 3786259) B3786259
theorem B2803817 : Blo 1867635 2803817 := bstep (se 2 (by rfl) ⟨1051431, by rfl⟩ : syracuseStep 2803817 = 2102863) B2102863
theorem B15960179 : Blo 1867635 15960179 := bstep (se 1 (by rfl) ⟨11970134, by rfl⟩ : syracuseStep 15960179 = 23940269) B23940269
theorem B20211889 : Blo 1867635 20211889 := bstep (se 2 (by rfl) ⟨7579458, by rfl⟩ : syracuseStep 20211889 = 15158917) B15158917
theorem B4729043 : Blo 1867635 4729043 := bstep (se 1 (by rfl) ⟨3546782, by rfl⟩ : syracuseStep 4729043 = 7093565) B7093565
theorem B5318921 : Blo 1867635 5318921 := bstep (se 2 (by rfl) ⟨1994595, by rfl⟩ : syracuseStep 5318921 = 3989191) B3989191
theorem B2992393 : Blo 1867635 2992393 := bstep (se 2 (by rfl) ⟨1122147, by rfl⟩ : syracuseStep 2992393 = 2244295) B2244295
theorem B10103069 : Blo 1867635 10103069 := bstep (se 3 (by rfl) ⟨1894325, by rfl⟩ : syracuseStep 10103069 = 3788651) B3788651
theorem B4204907 : Blo 1867635 4204907 := bstep (se 1 (by rfl) ⟨3153680, by rfl⟩ : syracuseStep 4204907 = 6307361) B6307361
theorem B17959279 : Blo 1867635 17959279 := bstep (se 1 (by rfl) ⟨13469459, by rfl⟩ : syracuseStep 17959279 = 26938919) B26938919
theorem B2804135 : Blo 1867635 2804135 := bstep (se 1 (by rfl) ⟨2103101, by rfl⟩ : syracuseStep 2804135 = 4206203) B4206203
theorem B4205051 : Blo 1867635 4205051 := bstep (se 1 (by rfl) ⟨3153788, by rfl⟩ : syracuseStep 4205051 = 6307577) B6307577
theorem B2804219 : Blo 1867635 2804219 := bstep (se 1 (by rfl) ⟨2103164, by rfl⟩ : syracuseStep 2804219 = 4206329) B4206329
theorem B4205177 : Blo 1867635 4205177 := bstep (se 2 (by rfl) ⟨1576941, by rfl⟩ : syracuseStep 4205177 = 3153883) B3153883
theorem B2804345 : Blo 1867635 2804345 := bstep (se 2 (by rfl) ⟨1051629, by rfl⟩ : syracuseStep 2804345 = 2103259) B2103259
theorem B4205231 : Blo 1867635 4205231 := bstep (se 1 (by rfl) ⟨3153923, by rfl⟩ : syracuseStep 4205231 = 6307847) B6307847
theorem B2804399 : Blo 1867635 2804399 := bstep (se 1 (by rfl) ⟨2103299, by rfl⟩ : syracuseStep 2804399 = 4206599) B4206599
theorem B2804447 : Blo 1867635 2804447 := bstep (se 1 (by rfl) ⟨2103335, by rfl⟩ : syracuseStep 2804447 = 4206671) B4206671
theorem B4205303 : Blo 1867635 4205303 := bstep (se 1 (by rfl) ⟨3153977, by rfl⟩ : syracuseStep 4205303 = 6307955) B6307955
theorem B4205483 : Blo 1867635 4205483 := bstep (se 1 (by rfl) ⟨3154112, by rfl⟩ : syracuseStep 4205483 = 6308225) B6308225
theorem B11365391 : Blo 1867635 11365391 := bstep (se 1 (by rfl) ⟨8524043, by rfl⟩ : syracuseStep 11365391 = 17048087) B17048087
theorem B5835815 : Blo 1867635 5835815 := bstep (se 1 (by rfl) ⟨4376861, by rfl⟩ : syracuseStep 5835815 = 8753723) B8753723
theorem B5319719 : Blo 1867635 5319719 := bstep (se 1 (by rfl) ⟨3989789, by rfl⟩ : syracuseStep 5319719 = 7979579) B7979579
theorem B7097483 : Blo 1867635 7097483 := bstep (se 1 (by rfl) ⟨5323112, by rfl⟩ : syracuseStep 7097483 = 10646225) B10646225
theorem B10644767 : Blo 1867635 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B4206023 : Blo 1867635 4206023 := bstep (se 1 (by rfl) ⟨3154517, by rfl⟩ : syracuseStep 4206023 = 6309035) B6309035
theorem B5320151 : Blo 1867635 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B9457235 : Blo 1867635 9457235 := bstep (se 1 (by rfl) ⟨7092926, by rfl⟩ : syracuseStep 9457235 = 14185853) B14185853
theorem B7097939 : Blo 1867635 7097939 := bstep (se 1 (by rfl) ⟨5323454, by rfl⟩ : syracuseStep 7097939 = 10646909) B10646909
theorem B7982687 : Blo 1867635 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B4206383 : Blo 1867635 4206383 := bstep (se 1 (by rfl) ⟨3154787, by rfl⟩ : syracuseStep 4206383 = 6309575) B6309575
theorem B3411767 : Blo 1867635 3411767 := bstep (se 1 (by rfl) ⟨2558825, by rfl⟩ : syracuseStep 3411767 = 5117651) B5117651
theorem B5320505 : Blo 1867635 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3411919 : Blo 1867635 3411919 := bstep (se 1 (by rfl) ⟨2558939, by rfl⟩ : syracuseStep 3411919 = 5117879) B5117879
theorem B3789065 : Blo 1867635 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B6304175 : Blo 1867635 6304175 := bstep (se 1 (by rfl) ⟨4728131, by rfl⟩ : syracuseStep 6304175 = 9456263) B9456263
theorem B4731311 : Blo 1867635 4731311 := bstep (se 1 (by rfl) ⟨3548483, by rfl⟩ : syracuseStep 4731311 = 7096967) B7096967
theorem B20197835 : Blo 1867635 20197835 := bstep (se 1 (by rfl) ⟨15148376, by rfl⟩ : syracuseStep 20197835 = 30296753) B30296753
theorem B2363899 : Blo 1867635 2363899 := bstep (se 1 (by rfl) ⟨1772924, by rfl⟩ : syracuseStep 2363899 = 3545849) B3545849
theorem B17953325 : Blo 1867635 17953325 := bstep (se 3 (by rfl) ⟨3366248, by rfl⟩ : syracuseStep 17953325 = 6732497) B6732497
theorem B2101855 : Blo 1867635 2101855 := bstep (se 1 (by rfl) ⟨1576391, by rfl⟩ : syracuseStep 2101855 = 3152783) B3152783
theorem B10097297 : Blo 1867635 10097297 := bstep (se 2 (by rfl) ⟨3786486, by rfl⟩ : syracuseStep 10097297 = 7572973) B7572973
theorem B15962777 : Blo 1867635 15962777 := bstep (se 2 (by rfl) ⟨5986041, by rfl⟩ : syracuseStep 15962777 = 11972083) B11972083
theorem B5395127 : Blo 1867635 5395127 := bstep (se 1 (by rfl) ⟨4046345, by rfl⟩ : syracuseStep 5395127 = 8092691) B8092691
theorem B10105559 : Blo 1867635 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B47895299 : Blo 1867635 47895299 := bstep (se 1 (by rfl) ⟨35921474, by rfl⟩ : syracuseStep 47895299 = 71842949) B71842949
theorem B7091347 : Blo 1867635 7091347 := bstep (se 1 (by rfl) ⟨5318510, by rfl⟩ : syracuseStep 7091347 = 10637021) B10637021
theorem B5985427 : Blo 1867635 5985427 := bstep (se 1 (by rfl) ⟨4489070, by rfl⟩ : syracuseStep 5985427 = 8978141) B8978141
theorem B7984327 : Blo 1867635 7984327 := bstep (se 1 (by rfl) ⟨5988245, by rfl⟩ : syracuseStep 7984327 = 11976491) B11976491
theorem B13464791 : Blo 1867635 13464791 := bstep (se 1 (by rfl) ⟨10098593, by rfl⟩ : syracuseStep 13464791 = 20197187) B20197187
theorem B8975603 : Blo 1867635 8975603 := bstep (se 1 (by rfl) ⟨6731702, by rfl⟩ : syracuseStep 8975603 = 13463405) B13463405
theorem B35018077 : Blo 1867635 35018077 := bstep (se 3 (by rfl) ⟨6565889, by rfl⟩ : syracuseStep 35018077 = 13131779) B13131779
theorem B6305147 : Blo 1867635 6305147 := bstep (se 1 (by rfl) ⟨4728860, by rfl⟩ : syracuseStep 6305147 = 9457721) B9457721
theorem B4732283 : Blo 1867635 4732283 := bstep (se 1 (by rfl) ⟨3549212, by rfl⟩ : syracuseStep 4732283 = 7098425) B7098425
theorem B5322145 : Blo 1867635 5322145 := bstep (se 2 (by rfl) ⟨1995804, by rfl⟩ : syracuseStep 5322145 = 3991609) B3991609
theorem B2364871 : Blo 1867635 2364871 := bstep (se 1 (by rfl) ⟨1773653, by rfl⟩ : syracuseStep 2364871 = 3547307) B3547307
theorem B1996283 : Blo 1867635 1996283 := bstep (se 1 (by rfl) ⟨1497212, by rfl⟩ : syracuseStep 1996283 = 2994425) B2994425
theorem B7575047 : Blo 1867635 7575047 := bstep (se 1 (by rfl) ⟨5681285, by rfl⟩ : syracuseStep 7575047 = 11362571) B11362571
theorem B10106375 : Blo 1867635 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B10647227 : Blo 1867635 10647227 := bstep (se 1 (by rfl) ⟨7985420, by rfl⟩ : syracuseStep 10647227 = 15970841) B15970841
theorem B2103007 : Blo 1867635 2103007 := bstep (se 1 (by rfl) ⟨1577255, by rfl⟩ : syracuseStep 2103007 = 3154511) B3154511
theorem B15562795 : Blo 1867635 15562795 := bstep (se 1 (by rfl) ⟨11672096, by rfl⟩ : syracuseStep 15562795 = 23344193) B23344193
theorem B9722051 : Blo 1867635 9722051 := bstep (se 1 (by rfl) ⟨7291538, by rfl⟩ : syracuseStep 9722051 = 14583077) B14583077
theorem B7985405 : Blo 1867635 7985405 := bstep (se 3 (by rfl) ⟨1497263, by rfl⟩ : syracuseStep 7985405 = 2994527) B2994527
theorem B2660617 : Blo 1867635 2660617 := bstep (se 2 (by rfl) ⟨997731, by rfl⟩ : syracuseStep 2660617 = 1995463) B1995463
theorem B140196109 : Blo 1867635 140196109 := bstep (se 3 (by rfl) ⟨26286770, by rfl⟩ : syracuseStep 140196109 = 52573541) B52573541
theorem B2365787 : Blo 1867635 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B9460151 : Blo 1867635 9460151 := bstep (se 1 (by rfl) ⟨7095113, by rfl⟩ : syracuseStep 9460151 = 14190227) B14190227
theorem B5986811 : Blo 1867635 5986811 := bstep (se 1 (by rfl) ⟨4490108, by rfl⟩ : syracuseStep 5986811 = 8980217) B8980217
theorem B3152567 : Blo 1867635 3152567 := bstep (se 1 (by rfl) ⟨2364425, by rfl⟩ : syracuseStep 3152567 = 4728851) B4728851
theorem B6306551 : Blo 1867635 6306551 := bstep (se 1 (by rfl) ⟨4729913, by rfl⟩ : syracuseStep 6306551 = 9459827) B9459827
theorem B27303065 : Blo 1867635 27303065 := bstep (se 2 (by rfl) ⟨10238649, by rfl⟩ : syracuseStep 27303065 = 20477299) B20477299
theorem B3153289 : Blo 1867635 3153289 := bstep (se 2 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 3153289 = 2364967) B2364967
theorem B15957719 : Blo 1867635 15957719 := bstep (se 1 (by rfl) ⟨11968289, by rfl⟩ : syracuseStep 15957719 = 23936579) B23936579
theorem B6307631 : Blo 1867635 6307631 := bstep (se 1 (by rfl) ⟨4730723, by rfl⟩ : syracuseStep 6307631 = 9461447) B9461447
theorem B5988143 : Blo 1867635 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B4202297 : Blo 1867635 4202297 := bstep (se 2 (by rfl) ⟨1575861, by rfl⟩ : syracuseStep 4202297 = 3151723) B3151723
theorem B3153721 : Blo 1867635 3153721 := bstep (se 2 (by rfl) ⟨1182645, by rfl⟩ : syracuseStep 3153721 = 2365291) B2365291
theorem B1867675 : Blo 1867635 1867675 := bstep (se 1 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 1867675 = 2801513) B2801513
theorem B47882177 : Blo 1867635 47882177 := bstep (se 2 (by rfl) ⟨17955816, by rfl⟩ : syracuseStep 47882177 = 35911633) B35911633
theorem B1867727 : Blo 1867635 1867727 := bstep (se 1 (by rfl) ⟨1400795, by rfl⟩ : syracuseStep 1867727 = 2801591) B2801591
theorem B2801615 : Blo 1867635 2801615 := bstep (se 1 (by rfl) ⟨2101211, by rfl⟩ : syracuseStep 2801615 = 4202423) B4202423
theorem B1867751 : Blo 1867635 1867751 := bstep (se 1 (by rfl) ⟨1400813, by rfl⟩ : syracuseStep 1867751 = 2801627) B2801627
theorem B20750393 : Blo 1867635 20750393 := bstep (se 2 (by rfl) ⟨7781397, by rfl⟩ : syracuseStep 20750393 = 15562795) B15562795
theorem B4260071 : Blo 1867635 4260071 := bstep (se 1 (by rfl) ⟨3195053, by rfl⟩ : syracuseStep 4260071 = 6390107) B6390107
theorem B1868007 : Blo 1867635 1868007 := bstep (se 1 (by rfl) ⟨1401005, by rfl⟩ : syracuseStep 1868007 = 2802011) B2802011
theorem B4202783 : Blo 1867635 4202783 := bstep (se 1 (by rfl) ⟨3152087, by rfl⟩ : syracuseStep 4202783 = 6304175) B6304175
theorem B2801951 : Blo 1867635 2801951 := bstep (se 1 (by rfl) ⟨2101463, by rfl⟩ : syracuseStep 2801951 = 4202927) B4202927
theorem B3154207 : Blo 1867635 3154207 := bstep (se 1 (by rfl) ⟨2365655, by rfl⟩ : syracuseStep 3154207 = 4731311) B4731311
theorem B2801975 : Blo 1867635 2801975 := bstep (se 1 (by rfl) ⟨2101481, by rfl⟩ : syracuseStep 2801975 = 4202963) B4202963
theorem B3547489 : Blo 1867635 3547489 := bstep (se 2 (by rfl) ⟨1330308, by rfl⟩ : syracuseStep 3547489 = 2660617) B2660617
theorem B11968883 : Blo 1867635 11968883 := bstep (se 1 (by rfl) ⟨8976662, by rfl⟩ : syracuseStep 11968883 = 17953325) B17953325
theorem B2802047 : Blo 1867635 2802047 := bstep (se 1 (by rfl) ⟨2101535, by rfl⟩ : syracuseStep 2802047 = 4203071) B4203071
theorem B1868159 : Blo 1867635 1868159 := bstep (se 1 (by rfl) ⟨1401119, by rfl⟩ : syracuseStep 1868159 = 2802239) B2802239
theorem B6308279 : Blo 1867635 6308279 := bstep (se 1 (by rfl) ⟨4731209, by rfl⟩ : syracuseStep 6308279 = 9462419) B9462419
theorem B10641851 : Blo 1867635 10641851 := bstep (se 1 (by rfl) ⟨7981388, by rfl⟩ : syracuseStep 10641851 = 15962777) B15962777
theorem B2802119 : Blo 1867635 2802119 := bstep (se 1 (by rfl) ⟨2101589, by rfl⟩ : syracuseStep 2802119 = 4203179) B4203179
theorem B1868239 : Blo 1867635 1868239 := bstep (se 1 (by rfl) ⟨1401179, by rfl⟩ : syracuseStep 1868239 = 2802359) B2802359
theorem B7094735 : Blo 1867635 7094735 := bstep (se 1 (by rfl) ⟨5321051, by rfl⟩ : syracuseStep 7094735 = 10642103) B10642103
theorem B23945705 : Blo 1867635 23945705 := bstep (se 2 (by rfl) ⟨8979639, by rfl⟩ : syracuseStep 23945705 = 17959279) B17959279
theorem B1868391 : Blo 1867635 1868391 := bstep (se 1 (by rfl) ⟨1401293, by rfl⟩ : syracuseStep 1868391 = 2802587) B2802587
theorem B2802473 : Blo 1867635 2802473 := bstep (se 2 (by rfl) ⟨1050927, by rfl⟩ : syracuseStep 2802473 = 2101855) B2101855
theorem B2802479 : Blo 1867635 2802479 := bstep (se 1 (by rfl) ⟨2101859, by rfl⟩ : syracuseStep 2802479 = 4203719) B4203719
theorem B1868655 : Blo 1867635 1868655 := bstep (se 1 (by rfl) ⟨1401491, by rfl⟩ : syracuseStep 1868655 = 2802983) B2802983
theorem B2245487 : Blo 1867635 2245487 := bstep (se 1 (by rfl) ⟨1684115, by rfl⟩ : syracuseStep 2245487 = 3368231) B3368231
theorem B6308765 : Blo 1867635 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B4203431 : Blo 1867635 4203431 := bstep (se 1 (by rfl) ⟨3152573, by rfl⟩ : syracuseStep 4203431 = 6305147) B6305147
theorem B2802599 : Blo 1867635 2802599 := bstep (se 1 (by rfl) ⟨2101949, by rfl⟩ : syracuseStep 2802599 = 4203899) B4203899
theorem B1868711 : Blo 1867635 1868711 := bstep (se 1 (by rfl) ⟨1401533, by rfl⟩ : syracuseStep 1868711 = 2803067) B2803067
theorem B3154855 : Blo 1867635 3154855 := bstep (se 1 (by rfl) ⟨2366141, by rfl⟩ : syracuseStep 3154855 = 4732283) B4732283
theorem B6308819 : Blo 1867635 6308819 := bstep (se 1 (by rfl) ⟨4731614, by rfl⟩ : syracuseStep 6308819 = 9463229) B9463229
theorem B2802683 : Blo 1867635 2802683 := bstep (se 1 (by rfl) ⟨2102012, by rfl⟩ : syracuseStep 2802683 = 4204025) B4204025
theorem B1868795 : Blo 1867635 1868795 := bstep (se 1 (by rfl) ⟨1401596, by rfl⟩ : syracuseStep 1868795 = 2803193) B2803193
theorem B2802743 : Blo 1867635 2802743 := bstep (se 1 (by rfl) ⟨2102057, by rfl⟩ : syracuseStep 2802743 = 4204115) B4204115
theorem B1868863 : Blo 1867635 1868863 := bstep (se 1 (by rfl) ⟨1401647, by rfl⟩ : syracuseStep 1868863 = 2803295) B2803295
theorem B2802863 : Blo 1867635 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B1869007 : Blo 1867635 1869007 := bstep (se 1 (by rfl) ⟨1401755, by rfl⟩ : syracuseStep 1869007 = 2803511) B2803511
theorem B4490569 : Blo 1867635 4490569 := bstep (se 2 (by rfl) ⟨1683963, by rfl⟩ : syracuseStep 4490569 = 3367927) B3367927
theorem B15959429 : Blo 1867635 15959429 := bstep (se 4 (by rfl) ⟨1496196, by rfl⟩ : syracuseStep 15959429 = 2992393) B2992393
theorem B17958277 : Blo 1867635 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1869211 : Blo 1867635 1869211 := bstep (se 1 (by rfl) ⟨1401908, by rfl⟩ : syracuseStep 1869211 = 2803817) B2803817
theorem B6481367 : Blo 1867635 6481367 := bstep (se 1 (by rfl) ⟨4861025, by rfl⟩ : syracuseStep 6481367 = 9722051) B9722051
theorem B9455129 : Blo 1867635 9455129 := bstep (se 2 (by rfl) ⟨3545673, by rfl⟩ : syracuseStep 9455129 = 7091347) B7091347
theorem B7980569 : Blo 1867635 7980569 := bstep (se 2 (by rfl) ⟨2992713, by rfl⟩ : syracuseStep 7980569 = 5985427) B5985427
theorem B2803271 : Blo 1867635 2803271 := bstep (se 1 (by rfl) ⟨2102453, by rfl⟩ : syracuseStep 2803271 = 4204907) B4204907
theorem B1869423 : Blo 1867635 1869423 := bstep (se 1 (by rfl) ⟨1402067, by rfl⟩ : syracuseStep 1869423 = 2804135) B2804135
theorem B3991207 : Blo 1867635 3991207 := bstep (se 1 (by rfl) ⟨2993405, by rfl⟩ : syracuseStep 3991207 = 5986811) B5986811
theorem B2803367 : Blo 1867635 2803367 := bstep (se 1 (by rfl) ⟨2102525, by rfl⟩ : syracuseStep 2803367 = 4205051) B4205051
theorem B1869479 : Blo 1867635 1869479 := bstep (se 1 (by rfl) ⟨1402109, by rfl⟩ : syracuseStep 1869479 = 2804219) B2804219
theorem B2803451 : Blo 1867635 2803451 := bstep (se 1 (by rfl) ⟨2102588, by rfl⟩ : syracuseStep 2803451 = 4205177) B4205177
theorem B1869563 : Blo 1867635 1869563 := bstep (se 1 (by rfl) ⟨1402172, by rfl⟩ : syracuseStep 1869563 = 2804345) B2804345
theorem B2803487 : Blo 1867635 2803487 := bstep (se 1 (by rfl) ⟨2102615, by rfl⟩ : syracuseStep 2803487 = 4205231) B4205231
theorem B1869599 : Blo 1867635 1869599 := bstep (se 1 (by rfl) ⟨1402199, by rfl⟩ : syracuseStep 1869599 = 2804399) B2804399
theorem B14387005 : Blo 1867635 14387005 := bstep (se 3 (by rfl) ⟨2697563, by rfl⟩ : syracuseStep 14387005 = 5395127) B5395127
theorem B1869631 : Blo 1867635 1869631 := bstep (se 1 (by rfl) ⟨1402223, by rfl⟩ : syracuseStep 1869631 = 2804447) B2804447
theorem B4204367 : Blo 1867635 4204367 := bstep (se 1 (by rfl) ⟨3153275, by rfl⟩ : syracuseStep 4204367 = 6306551) B6306551
theorem B2803535 : Blo 1867635 2803535 := bstep (se 1 (by rfl) ⟨2102651, by rfl⟩ : syracuseStep 2803535 = 4205303) B4205303
theorem B4204385 : Blo 1867635 4204385 := bstep (se 2 (by rfl) ⟨1576644, by rfl⟩ : syracuseStep 4204385 = 3153289) B3153289
theorem B7096193 : Blo 1867635 7096193 := bstep (se 2 (by rfl) ⟨2661072, by rfl⟩ : syracuseStep 7096193 = 5322145) B5322145
theorem B2803655 : Blo 1867635 2803655 := bstep (se 1 (by rfl) ⟨2102741, by rfl⟩ : syracuseStep 2803655 = 4205483) B4205483
theorem B49875101 : Blo 1867635 49875101 := bstep (se 3 (by rfl) ⟨9351581, by rfl⟩ : syracuseStep 49875101 = 18703163) B18703163
theorem B7096511 : Blo 1867635 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B2804009 : Blo 1867635 2804009 := bstep (se 2 (by rfl) ⟨1051503, by rfl⟩ : syracuseStep 2804009 = 2103007) B2103007
theorem B2804015 : Blo 1867635 2804015 := bstep (se 1 (by rfl) ⟨2103011, by rfl⟩ : syracuseStep 2804015 = 4206023) B4206023
theorem B4204961 : Blo 1867635 4204961 := bstep (se 2 (by rfl) ⟨1576860, by rfl⟩ : syracuseStep 4204961 = 3153721) B3153721
theorem B18196901 : Blo 1867635 18196901 := bstep (se 4 (by rfl) ⟨1705959, by rfl⟩ : syracuseStep 18196901 = 3411919) B3411919
theorem B4205087 : Blo 1867635 4205087 := bstep (se 1 (by rfl) ⟨3153815, by rfl⟩ : syracuseStep 4205087 = 6307631) B6307631
theorem B3992095 : Blo 1867635 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B2804255 : Blo 1867635 2804255 := bstep (se 1 (by rfl) ⟨2103191, by rfl⟩ : syracuseStep 2804255 = 4206383) B4206383
theorem B11971547 : Blo 1867635 11971547 := bstep (se 1 (by rfl) ⟨8978660, by rfl⟩ : syracuseStep 11971547 = 17957321) B17957321
theorem B186928145 : Blo 1867635 186928145 := bstep (se 2 (by rfl) ⟨70098054, by rfl⟩ : syracuseStep 186928145 = 140196109) B140196109
theorem B6737039 : Blo 1867635 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B10104173 : Blo 1867635 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B5983735 : Blo 1867635 5983735 := bstep (se 1 (by rfl) ⟨4487801, by rfl⟩ : syracuseStep 5983735 = 8975603) B8975603
theorem B4730359 : Blo 1867635 4730359 := bstep (se 1 (by rfl) ⟨3547769, by rfl⟩ : syracuseStep 4730359 = 7095539) B7095539
theorem B5050031 : Blo 1867635 5050031 := bstep (se 1 (by rfl) ⟨3787523, by rfl⟩ : syracuseStep 5050031 = 7575047) B7575047
theorem B6303527 : Blo 1867635 6303527 := bstep (se 1 (by rfl) ⟨4727645, by rfl⟩ : syracuseStep 6303527 = 9455291) B9455291
theorem B4730663 : Blo 1867635 4730663 := bstep (se 1 (by rfl) ⟨3547997, by rfl⟩ : syracuseStep 4730663 = 7095995) B7095995
theorem B7098151 : Blo 1867635 7098151 := bstep (se 1 (by rfl) ⟨5323613, by rfl⟩ : syracuseStep 7098151 = 10647227) B10647227
theorem B4206491 : Blo 1867635 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B90910673 : Blo 1867635 90910673 := bstep (se 2 (by rfl) ⟨34091502, by rfl⟩ : syracuseStep 90910673 = 68183005) B68183005
theorem B10645769 : Blo 1867635 10645769 := bstep (se 2 (by rfl) ⟨3992163, by rfl⟩ : syracuseStep 10645769 = 7984327) B7984327
theorem B2101711 : Blo 1867635 2101711 := bstep (se 1 (by rfl) ⟨1576283, by rfl⟩ : syracuseStep 2101711 = 3152567) B3152567
theorem B46690769 : Blo 1867635 46690769 := bstep (se 2 (by rfl) ⟨17509038, by rfl⟩ : syracuseStep 46690769 = 35018077) B35018077
theorem B4731655 : Blo 1867635 4731655 := bstep (se 1 (by rfl) ⟨3548741, by rfl⟩ : syracuseStep 4731655 = 7097483) B7097483
theorem B6304553 : Blo 1867635 6304553 := bstep (se 2 (by rfl) ⟨2364207, by rfl⟩ : syracuseStep 6304553 = 4728415) B4728415
theorem B6304823 : Blo 1867635 6304823 := bstep (se 1 (by rfl) ⟨4728617, by rfl⟩ : syracuseStep 6304823 = 9457235) B9457235
theorem B4731959 : Blo 1867635 4731959 := bstep (se 1 (by rfl) ⟨3548969, by rfl⟩ : syracuseStep 4731959 = 7097939) B7097939
theorem B5321791 : Blo 1867635 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B10638479 : Blo 1867635 10638479 := bstep (se 1 (by rfl) ⟨7978859, by rfl⟩ : syracuseStep 10638479 = 15957719) B15957719
theorem B2274511 : Blo 1867635 2274511 := bstep (se 1 (by rfl) ⟨1705883, by rfl⟩ : syracuseStep 2274511 = 3411767) B3411767
theorem B31921451 : Blo 1867635 31921451 := bstep (se 1 (by rfl) ⟨23941088, by rfl⟩ : syracuseStep 31921451 = 47882177) B47882177
theorem B30307709 : Blo 1867635 30307709 := bstep (se 3 (by rfl) ⟨5682695, by rfl⟩ : syracuseStep 30307709 = 11365391) B11365391
theorem B2102683 : Blo 1867635 2102683 := bstep (se 1 (by rfl) ⟨1577012, by rfl⟩ : syracuseStep 2102683 = 3154025) B3154025
theorem B26949185 : Blo 1867635 26949185 := bstep (se 2 (by rfl) ⟨10105944, by rfl⟩ : syracuseStep 26949185 = 20211889) B20211889
theorem B13465223 : Blo 1867635 13465223 := bstep (se 1 (by rfl) ⟨10098917, by rfl⟩ : syracuseStep 13465223 = 20197835) B20197835
theorem B3413755 : Blo 1867635 3413755 := bstep (se 1 (by rfl) ⟨2560316, by rfl⟩ : syracuseStep 3413755 = 5120633) B5120633
theorem B6731531 : Blo 1867635 6731531 := bstep (se 1 (by rfl) ⟨5048648, by rfl⟩ : syracuseStep 6731531 = 10097297) B10097297
theorem B31930199 : Blo 1867635 31930199 := bstep (se 1 (by rfl) ⟨23947649, by rfl⟩ : syracuseStep 31930199 = 47895299) B47895299
theorem B6395879 : Blo 1867635 6395879 := bstep (se 1 (by rfl) ⟨4796909, by rfl⟩ : syracuseStep 6395879 = 9593819) B9593819
theorem B3151865 : Blo 1867635 3151865 := bstep (se 2 (by rfl) ⟨1181949, by rfl⟩ : syracuseStep 3151865 = 2363899) B2363899
theorem B26941517 : Blo 1867635 26941517 := bstep (se 3 (by rfl) ⟨5051534, by rfl⟩ : syracuseStep 26941517 = 10103069) B10103069
theorem B8976527 : Blo 1867635 8976527 := bstep (se 1 (by rfl) ⟨6732395, by rfl⟩ : syracuseStep 8976527 = 13464791) B13464791
theorem B3152027 : Blo 1867635 3152027 := bstep (se 1 (by rfl) ⟨2364020, by rfl⟩ : syracuseStep 3152027 = 4728041) B4728041
theorem B3152135 : Blo 1867635 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B14195087 : Blo 1867635 14195087 := bstep (se 1 (by rfl) ⟨10646315, by rfl⟩ : syracuseStep 14195087 = 21292631) B21292631
theorem B7985627 : Blo 1867635 7985627 := bstep (se 1 (by rfl) ⟨5989220, by rfl⟩ : syracuseStep 7985627 = 11978441) B11978441
theorem B9460313 : Blo 1867635 9460313 := bstep (se 2 (by rfl) ⟨3547617, by rfl⟩ : syracuseStep 9460313 = 7095235) B7095235
theorem B5323421 : Blo 1867635 5323421 := bstep (se 3 (by rfl) ⟨998141, by rfl⟩ : syracuseStep 5323421 = 1996283) B1996283
theorem B3365563 : Blo 1867635 3365563 := bstep (se 1 (by rfl) ⟨2524172, by rfl⟩ : syracuseStep 3365563 = 5048345) B5048345
theorem B26950333 : Blo 1867635 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B10640119 : Blo 1867635 10640119 := bstep (se 1 (by rfl) ⟨7980089, by rfl⟩ : syracuseStep 10640119 = 15960179) B15960179
theorem B3152695 : Blo 1867635 3152695 := bstep (se 1 (by rfl) ⟨2364521, by rfl⟩ : syracuseStep 3152695 = 4729043) B4729043
theorem B5323603 : Blo 1867635 5323603 := bstep (se 1 (by rfl) ⟨3992702, by rfl⟩ : syracuseStep 5323603 = 7985405) B7985405
theorem B3545947 : Blo 1867635 3545947 := bstep (se 1 (by rfl) ⟨2659460, by rfl⟩ : syracuseStep 3545947 = 5318921) B5318921
theorem B6306767 : Blo 1867635 6306767 := bstep (se 1 (by rfl) ⟨4730075, by rfl⟩ : syracuseStep 6306767 = 9460151) B9460151
theorem B3595529 : Blo 1867635 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B3153161 : Blo 1867635 3153161 := bstep (se 2 (by rfl) ⟨1182435, by rfl⟩ : syracuseStep 3153161 = 2364871) B2364871
theorem B443006221 : Blo 1867635 443006221 := bstep (se 3 (by rfl) ⟨83063666, by rfl⟩ : syracuseStep 443006221 = 166127333) B166127333
theorem B3890543 : Blo 1867635 3890543 := bstep (se 1 (by rfl) ⟨2917907, by rfl⟩ : syracuseStep 3890543 = 5835815) B5835815
theorem B3546479 : Blo 1867635 3546479 := bstep (se 1 (by rfl) ⟨2659859, by rfl⟩ : syracuseStep 3546479 = 5319719) B5319719
theorem B18202043 : Blo 1867635 18202043 := bstep (se 1 (by rfl) ⟨13651532, by rfl⟩ : syracuseStep 18202043 = 27303065) B27303065
theorem B3546767 : Blo 1867635 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B3989225 : Blo 1867635 3989225 := bstep (se 2 (by rfl) ⟨1495959, by rfl⟩ : syracuseStep 3989225 = 2991919) B2991919
theorem B2801531 : Blo 1867635 2801531 := bstep (se 1 (by rfl) ⟨2101148, by rfl⟩ : syracuseStep 2801531 = 4202297) B4202297
theorem B3547003 : Blo 1867635 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B1867743 : Blo 1867635 1867743 := bstep (se 1 (by rfl) ⟨1400807, by rfl⟩ : syracuseStep 1867743 = 2801615) B2801615
theorem B21291173 : Blo 1867635 21291173 := bstep (se 4 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 21291173 = 3992095) B3992095
theorem B2801855 : Blo 1867635 2801855 := bstep (se 1 (by rfl) ⟨2101391, by rfl⟩ : syracuseStep 2801855 = 4202783) B4202783
theorem B1867967 : Blo 1867635 1867967 := bstep (se 1 (by rfl) ⟨1400975, by rfl⟩ : syracuseStep 1867967 = 2801951) B2801951
theorem B1867983 : Blo 1867635 1867983 := bstep (se 1 (by rfl) ⟨1400987, by rfl⟩ : syracuseStep 1867983 = 2801975) B2801975
theorem B7979255 : Blo 1867635 7979255 := bstep (se 1 (by rfl) ⟨5984441, by rfl⟩ : syracuseStep 7979255 = 11968883) B11968883
theorem B1868031 : Blo 1867635 1868031 := bstep (se 1 (by rfl) ⟨1401023, by rfl⟩ : syracuseStep 1868031 = 2802047) B2802047
theorem B7094567 : Blo 1867635 7094567 := bstep (se 1 (by rfl) ⟨5320925, by rfl⟩ : syracuseStep 7094567 = 10641851) B10641851
theorem B1868079 : Blo 1867635 1868079 := bstep (se 1 (by rfl) ⟨1401059, by rfl⟩ : syracuseStep 1868079 = 2802119) B2802119
theorem B4203035 : Blo 1867635 4203035 := bstep (se 1 (by rfl) ⟨3152276, by rfl⟩ : syracuseStep 4203035 = 6304553) B6304553
theorem B1868315 : Blo 1867635 1868315 := bstep (se 1 (by rfl) ⟨1401236, by rfl⟩ : syracuseStep 1868315 = 2802473) B2802473
theorem B1868319 : Blo 1867635 1868319 := bstep (se 1 (by rfl) ⟨1401239, by rfl⟩ : syracuseStep 1868319 = 2802479) B2802479
theorem B2802281 : Blo 1867635 2802281 := bstep (se 2 (by rfl) ⟨1050855, by rfl⟩ : syracuseStep 2802281 = 2101711) B2101711
theorem B2802287 : Blo 1867635 2802287 := bstep (se 1 (by rfl) ⟨2101715, by rfl⟩ : syracuseStep 2802287 = 4203431) B4203431
theorem B1868399 : Blo 1867635 1868399 := bstep (se 1 (by rfl) ⟨1401299, by rfl⟩ : syracuseStep 1868399 = 2802599) B2802599
theorem B1868455 : Blo 1867635 1868455 := bstep (se 1 (by rfl) ⟨1401341, by rfl⟩ : syracuseStep 1868455 = 2802683) B2802683
theorem B4203215 : Blo 1867635 4203215 := bstep (se 1 (by rfl) ⟨3152411, by rfl⟩ : syracuseStep 4203215 = 6304823) B6304823
theorem B1868495 : Blo 1867635 1868495 := bstep (se 1 (by rfl) ⟨1401371, by rfl⟩ : syracuseStep 1868495 = 2802743) B2802743
theorem B3154639 : Blo 1867635 3154639 := bstep (se 1 (by rfl) ⟨2365979, by rfl⟩ : syracuseStep 3154639 = 4731959) B4731959
theorem B1868575 : Blo 1867635 1868575 := bstep (se 1 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 1868575 = 2802863) B2802863
theorem B6308873 : Blo 1867635 6308873 := bstep (se 2 (by rfl) ⟨2365827, by rfl⟩ : syracuseStep 6308873 = 4731655) B4731655
theorem B1868847 : Blo 1867635 1868847 := bstep (se 1 (by rfl) ⟨1401635, by rfl⟩ : syracuseStep 1868847 = 2803271) B2803271
theorem B17966123 : Blo 1867635 17966123 := bstep (se 1 (by rfl) ⟨13474592, by rfl⟩ : syracuseStep 17966123 = 26949185) B26949185
theorem B4203593 : Blo 1867635 4203593 := bstep (se 2 (by rfl) ⟨1576347, by rfl⟩ : syracuseStep 4203593 = 3152695) B3152695
theorem B1868911 : Blo 1867635 1868911 := bstep (se 1 (by rfl) ⟨1401683, by rfl⟩ : syracuseStep 1868911 = 2803367) B2803367
theorem B4727929 : Blo 1867635 4727929 := bstep (se 2 (by rfl) ⟨1772973, by rfl⟩ : syracuseStep 4727929 = 3545947) B3545947
theorem B1868967 : Blo 1867635 1868967 := bstep (se 1 (by rfl) ⟨1401725, by rfl⟩ : syracuseStep 1868967 = 2803451) B2803451
theorem B1868991 : Blo 1867635 1868991 := bstep (se 1 (by rfl) ⟨1401743, by rfl⟩ : syracuseStep 1868991 = 2803487) B2803487
theorem B2802911 : Blo 1867635 2802911 := bstep (se 1 (by rfl) ⟨2102183, by rfl⟩ : syracuseStep 2802911 = 4204367) B4204367
theorem B1869023 : Blo 1867635 1869023 := bstep (se 1 (by rfl) ⟨1401767, by rfl⟩ : syracuseStep 1869023 = 2803535) B2803535
theorem B2802923 : Blo 1867635 2802923 := bstep (se 1 (by rfl) ⟨2102192, by rfl⟩ : syracuseStep 2802923 = 4204385) B4204385
theorem B1869103 : Blo 1867635 1869103 := bstep (se 1 (by rfl) ⟨1401827, by rfl⟩ : syracuseStep 1869103 = 2803655) B2803655
theorem B7095721 : Blo 1867635 7095721 := bstep (se 2 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 7095721 = 5321791) B5321791
theorem B1869339 : Blo 1867635 1869339 := bstep (se 1 (by rfl) ⟨1402004, by rfl⟩ : syracuseStep 1869339 = 2804009) B2804009
theorem B1869343 : Blo 1867635 1869343 := bstep (se 1 (by rfl) ⟨1402007, by rfl⟩ : syracuseStep 1869343 = 2804015) B2804015
theorem B9463391 : Blo 1867635 9463391 := bstep (se 1 (by rfl) ⟨7097543, by rfl⟩ : syracuseStep 9463391 = 14195087) B14195087
theorem B2803307 : Blo 1867635 2803307 := bstep (se 1 (by rfl) ⟨2102480, by rfl⟩ : syracuseStep 2803307 = 4204961) B4204961
theorem B48522901 : Blo 1867635 48522901 := bstep (se 6 (by rfl) ⟨1137255, by rfl⟩ : syracuseStep 48522901 = 2274511) B2274511
theorem B2803391 : Blo 1867635 2803391 := bstep (se 1 (by rfl) ⟨2102543, by rfl⟩ : syracuseStep 2803391 = 4205087) B4205087
theorem B1869503 : Blo 1867635 1869503 := bstep (se 1 (by rfl) ⟨1402127, by rfl⟩ : syracuseStep 1869503 = 2804255) B2804255
theorem B3548947 : Blo 1867635 3548947 := bstep (se 1 (by rfl) ⟨2661710, by rfl⟩ : syracuseStep 3548947 = 5323421) B5323421
theorem B2803577 : Blo 1867635 2803577 := bstep (se 2 (by rfl) ⟨1051341, by rfl⟩ : syracuseStep 2803577 = 2102683) B2102683
theorem B4204511 : Blo 1867635 4204511 := bstep (se 1 (by rfl) ⟨3153383, by rfl⟩ : syracuseStep 4204511 = 6306767) B6306767
theorem B7981031 : Blo 1867635 7981031 := bstep (se 1 (by rfl) ⟨5985773, by rfl⟩ : syracuseStep 7981031 = 11971547) B11971547
theorem B124618763 : Blo 1867635 124618763 := bstep (se 1 (by rfl) ⟨93464072, by rfl⟩ : syracuseStep 124618763 = 186928145) B186928145
theorem B4491359 : Blo 1867635 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B6736115 : Blo 1867635 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B12134695 : Blo 1867635 12134695 := bstep (se 1 (by rfl) ⟨9101021, by rfl⟩ : syracuseStep 12134695 = 18202043) B18202043
theorem B9464201 : Blo 1867635 9464201 := bstep (se 2 (by rfl) ⟨3549075, by rfl⟩ : syracuseStep 9464201 = 7098151) B7098151
theorem B4729337 : Blo 1867635 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B2804327 : Blo 1867635 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B60607115 : Blo 1867635 60607115 := bstep (se 1 (by rfl) ⟨45455336, by rfl⟩ : syracuseStep 60607115 = 90910673) B90910673
theorem B7097179 : Blo 1867635 7097179 := bstep (se 1 (by rfl) ⟨5322884, by rfl⟩ : syracuseStep 7097179 = 10645769) B10645769
theorem B4205519 : Blo 1867635 4205519 := bstep (se 1 (by rfl) ⟨3154139, by rfl⟩ : syracuseStep 4205519 = 6308279) B6308279
theorem B4729823 : Blo 1867635 4729823 := bstep (se 1 (by rfl) ⟨3547367, by rfl⟩ : syracuseStep 4729823 = 7094735) B7094735
theorem B4205609 : Blo 1867635 4205609 := bstep (se 2 (by rfl) ⟨1577103, by rfl⟩ : syracuseStep 4205609 = 3154207) B3154207
theorem B4729985 : Blo 1867635 4729985 := bstep (se 2 (by rfl) ⟨1773744, by rfl⟩ : syracuseStep 4729985 = 3547489) B3547489
theorem B4205843 : Blo 1867635 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B4205879 : Blo 1867635 4205879 := bstep (se 1 (by rfl) ⟨3154409, by rfl⟩ : syracuseStep 4205879 = 6308819) B6308819
theorem B35933777 : Blo 1867635 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B20205139 : Blo 1867635 20205139 := bstep (se 1 (by rfl) ⟨15153854, by rfl⟩ : syracuseStep 20205139 = 30307709) B30307709
theorem B4320911 : Blo 1867635 4320911 := bstep (se 1 (by rfl) ⟨3240683, by rfl⟩ : syracuseStep 4320911 = 6481367) B6481367
theorem B6303419 : Blo 1867635 6303419 := bstep (se 1 (by rfl) ⟨4727564, by rfl⟩ : syracuseStep 6303419 = 9455129) B9455129
theorem B5320379 : Blo 1867635 5320379 := bstep (se 1 (by rfl) ⟨3990284, by rfl⟩ : syracuseStep 5320379 = 7980569) B7980569
theorem B7098137 : Blo 1867635 7098137 := bstep (se 2 (by rfl) ⟨2661801, by rfl⟩ : syracuseStep 7098137 = 5323603) B5323603
theorem B4206473 : Blo 1867635 4206473 := bstep (se 2 (by rfl) ⟨1577427, by rfl⟩ : syracuseStep 4206473 = 3154855) B3154855
theorem B21286799 : Blo 1867635 21286799 := bstep (se 1 (by rfl) ⟨15965099, by rfl⟩ : syracuseStep 21286799 = 31930199) B31930199
theorem B4730795 : Blo 1867635 4730795 := bstep (se 1 (by rfl) ⟨3548096, by rfl⟩ : syracuseStep 4730795 = 7096193) B7096193
theorem B18206693 : Blo 1867635 18206693 := bstep (se 4 (by rfl) ⟨1706877, by rfl⟩ : syracuseStep 18206693 = 3413755) B3413755
theorem B2101243 : Blo 1867635 2101243 := bstep (se 1 (by rfl) ⟨1575932, by rfl⟩ : syracuseStep 2101243 = 3151865) B3151865
theorem B17961011 : Blo 1867635 17961011 := bstep (se 1 (by rfl) ⟨13470758, by rfl⟩ : syracuseStep 17961011 = 26941517) B26941517
theorem B5984351 : Blo 1867635 5984351 := bstep (se 1 (by rfl) ⟨4488263, by rfl⟩ : syracuseStep 5984351 = 8976527) B8976527
theorem B2101351 : Blo 1867635 2101351 := bstep (se 1 (by rfl) ⟨1576013, by rfl⟩ : syracuseStep 2101351 = 3152027) B3152027
theorem B4731007 : Blo 1867635 4731007 := bstep (se 1 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 4731007 = 7096511) B7096511
theorem B2101423 : Blo 1867635 2101423 := bstep (se 1 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 2101423 = 3152135) B3152135
theorem B9458045 : Blo 1867635 9458045 := bstep (se 3 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 9458045 = 3546767) B3546767
theorem B23949701 : Blo 1867635 23949701 := bstep (se 4 (by rfl) ⟨2245284, by rfl⟩ : syracuseStep 23949701 = 4490569) B4490569
theorem B2397019 : Blo 1867635 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B2102107 : Blo 1867635 2102107 := bstep (se 1 (by rfl) ⟨1576580, by rfl⟩ : syracuseStep 2102107 = 3153161) B3153161
theorem B5321609 : Blo 1867635 5321609 := bstep (se 2 (by rfl) ⟨1995603, by rfl⟩ : syracuseStep 5321609 = 3991207) B3991207
theorem B2364319 : Blo 1867635 2364319 := bstep (se 1 (by rfl) ⟨1773239, by rfl⟩ : syracuseStep 2364319 = 3546479) B3546479
theorem B19182673 : Blo 1867635 19182673 := bstep (se 2 (by rfl) ⟨7193502, by rfl⟩ : syracuseStep 19182673 = 14387005) B14387005
theorem B2659483 : Blo 1867635 2659483 := bstep (se 1 (by rfl) ⟨1994612, by rfl⟩ : syracuseStep 2659483 = 3989225) B3989225
theorem B13833595 : Blo 1867635 13833595 := bstep (se 1 (by rfl) ⟨10375196, by rfl⟩ : syracuseStep 13833595 = 20750393) B20750393
theorem B31127179 : Blo 1867635 31127179 := bstep (se 1 (by rfl) ⟨23345384, by rfl⟩ : syracuseStep 31127179 = 46690769) B46690769
theorem B15963803 : Blo 1867635 15963803 := bstep (se 1 (by rfl) ⟨11972852, by rfl⟩ : syracuseStep 15963803 = 23945705) B23945705
theorem B11360189 : Blo 1867635 11360189 := bstep (se 3 (by rfl) ⟨2130035, by rfl⟩ : syracuseStep 11360189 = 4260071) B4260071
theorem B7092319 : Blo 1867635 7092319 := bstep (se 1 (by rfl) ⟨5319239, by rfl⟩ : syracuseStep 7092319 = 10638479) B10638479
theorem B21280967 : Blo 1867635 21280967 := bstep (se 1 (by rfl) ⟨15960725, by rfl⟩ : syracuseStep 21280967 = 31921451) B31921451
theorem B4487417 : Blo 1867635 4487417 := bstep (se 2 (by rfl) ⟨1682781, by rfl⟩ : syracuseStep 4487417 = 3365563) B3365563
theorem B10639619 : Blo 1867635 10639619 := bstep (se 1 (by rfl) ⟨7979714, by rfl⟩ : syracuseStep 10639619 = 15959429) B15959429
theorem B14186825 : Blo 1867635 14186825 := bstep (se 2 (by rfl) ⟨5320059, by rfl⟩ : syracuseStep 14186825 = 10640119) B10640119
theorem B8976815 : Blo 1867635 8976815 := bstep (se 1 (by rfl) ⟨6732611, by rfl⟩ : syracuseStep 8976815 = 13465223) B13465223
theorem B41499125 : Blo 1867635 41499125 := bstep (se 5 (by rfl) ⟨1945271, by rfl⟩ : syracuseStep 41499125 = 3890543) B3890543
theorem B4487687 : Blo 1867635 4487687 := bstep (se 1 (by rfl) ⟨3365765, by rfl⟩ : syracuseStep 4487687 = 6731531) B6731531
theorem B33250067 : Blo 1867635 33250067 := bstep (se 1 (by rfl) ⟨24937550, by rfl⟩ : syracuseStep 33250067 = 49875101) B49875101
theorem B12131267 : Blo 1867635 12131267 := bstep (se 1 (by rfl) ⟨9098450, by rfl⟩ : syracuseStep 12131267 = 18196901) B18196901
theorem B5323751 : Blo 1867635 5323751 := bstep (se 1 (by rfl) ⟨3992813, by rfl⟩ : syracuseStep 5323751 = 7985627) B7985627
theorem B590674961 : Blo 1867635 590674961 := bstep (se 2 (by rfl) ⟨221503110, by rfl⟩ : syracuseStep 590674961 = 443006221) B443006221
theorem B6306875 : Blo 1867635 6306875 := bstep (se 1 (by rfl) ⟨4730156, by rfl⟩ : syracuseStep 6306875 = 9460313) B9460313
theorem B13466749 : Blo 1867635 13466749 := bstep (se 3 (by rfl) ⟨2525015, by rfl⟩ : syracuseStep 13466749 = 5050031) B5050031
theorem B23944369 : Blo 1867635 23944369 := bstep (se 2 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 23944369 = 17958277) B17958277
theorem B7978313 : Blo 1867635 7978313 := bstep (se 2 (by rfl) ⟨2991867, by rfl⟩ : syracuseStep 7978313 = 5983735) B5983735
theorem B6307145 : Blo 1867635 6307145 := bstep (se 2 (by rfl) ⟨2365179, by rfl⟩ : syracuseStep 6307145 = 4730359) B4730359
theorem B5987965 : Blo 1867635 5987965 := bstep (se 3 (by rfl) ⟨1122743, by rfl⟩ : syracuseStep 5987965 = 2245487) B2245487
theorem B4202351 : Blo 1867635 4202351 := bstep (se 1 (by rfl) ⟨3151763, by rfl⟩ : syracuseStep 4202351 = 6303527) B6303527
theorem B3153775 : Blo 1867635 3153775 := bstep (se 1 (by rfl) ⟨2365331, by rfl⟩ : syracuseStep 3153775 = 4730663) B4730663
theorem B1867687 : Blo 1867635 1867687 := bstep (se 1 (by rfl) ⟨1400765, by rfl⟩ : syracuseStep 1867687 = 2801531) B2801531
theorem B17055677 : Blo 1867635 17055677 := bstep (se 3 (by rfl) ⟨3197939, by rfl⟩ : syracuseStep 17055677 = 6395879) B6395879
theorem B332316701 : Blo 1867635 332316701 := bstep (se 3 (by rfl) ⟨62309381, by rfl⟩ : syracuseStep 332316701 = 124618763) B124618763
theorem B1575133229 : Blo 1867635 1575133229 := bstep (se 3 (by rfl) ⟨295337480, by rfl⟩ : syracuseStep 1575133229 = 590674961) B590674961
theorem B3989567 : Blo 1867635 3989567 := bstep (se 1 (by rfl) ⟨2992175, by rfl⟩ : syracuseStep 3989567 = 5984351) B5984351
theorem B1867903 : Blo 1867635 1867903 := bstep (se 1 (by rfl) ⟨1400927, by rfl⟩ : syracuseStep 1867903 = 2801855) B2801855
theorem B2801801 : Blo 1867635 2801801 := bstep (se 2 (by rfl) ⟨1050675, by rfl⟩ : syracuseStep 2801801 = 2101351) B2101351
theorem B6308009 : Blo 1867635 6308009 := bstep (se 2 (by rfl) ⟨2365503, by rfl⟩ : syracuseStep 6308009 = 4731007) B4731007
theorem B2801897 : Blo 1867635 2801897 := bstep (se 2 (by rfl) ⟨1050711, by rfl⟩ : syracuseStep 2801897 = 2101423) B2101423
theorem B15966467 : Blo 1867635 15966467 := bstep (se 1 (by rfl) ⟨11974850, by rfl⟩ : syracuseStep 15966467 = 23949701) B23949701
theorem B2802023 : Blo 1867635 2802023 := bstep (se 1 (by rfl) ⟨2101517, by rfl⟩ : syracuseStep 2802023 = 4203035) B4203035
theorem B16179593 : Blo 1867635 16179593 := bstep (se 2 (by rfl) ⟨6067347, by rfl⟩ : syracuseStep 16179593 = 12134695) B12134695
theorem B1868187 : Blo 1867635 1868187 := bstep (se 1 (by rfl) ⟨1401140, by rfl⟩ : syracuseStep 1868187 = 2802281) B2802281
theorem B1868191 : Blo 1867635 1868191 := bstep (se 1 (by rfl) ⟨1401143, by rfl⟩ : syracuseStep 1868191 = 2802287) B2802287
theorem B2802143 : Blo 1867635 2802143 := bstep (se 1 (by rfl) ⟨2101607, by rfl⟩ : syracuseStep 2802143 = 4203215) B4203215
theorem B3547739 : Blo 1867635 3547739 := bstep (se 1 (by rfl) ⟨2660804, by rfl⟩ : syracuseStep 3547739 = 5321609) B5321609
theorem B11977415 : Blo 1867635 11977415 := bstep (se 1 (by rfl) ⟨8983061, by rfl⟩ : syracuseStep 11977415 = 17966123) B17966123
theorem B2802395 : Blo 1867635 2802395 := bstep (se 1 (by rfl) ⟨2101796, by rfl⟩ : syracuseStep 2802395 = 4203593) B4203593
theorem B1868607 : Blo 1867635 1868607 := bstep (se 1 (by rfl) ⟨1401455, by rfl⟩ : syracuseStep 1868607 = 2802911) B2802911
theorem B1868615 : Blo 1867635 1868615 := bstep (se 1 (by rfl) ⟨1401461, by rfl⟩ : syracuseStep 1868615 = 2802923) B2802923
theorem B6308927 : Blo 1867635 6308927 := bstep (se 1 (by rfl) ⟨4731695, by rfl⟩ : syracuseStep 6308927 = 9463391) B9463391
theorem B1868871 : Blo 1867635 1868871 := bstep (se 1 (by rfl) ⟨1401653, by rfl⟩ : syracuseStep 1868871 = 2803307) B2803307
theorem B10642535 : Blo 1867635 10642535 := bstep (se 1 (by rfl) ⟨7981901, by rfl⟩ : syracuseStep 10642535 = 15963803) B15963803
theorem B3196025 : Blo 1867635 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B2802809 : Blo 1867635 2802809 := bstep (se 2 (by rfl) ⟨1051053, by rfl⟩ : syracuseStep 2802809 = 2102107) B2102107
theorem B9462905 : Blo 1867635 9462905 := bstep (se 2 (by rfl) ⟨3548589, by rfl⟩ : syracuseStep 9462905 = 7097179) B7097179
theorem B1868927 : Blo 1867635 1868927 := bstep (se 1 (by rfl) ⟨1401695, by rfl⟩ : syracuseStep 1868927 = 2803391) B2803391
theorem B1869051 : Blo 1867635 1869051 := bstep (se 1 (by rfl) ⟨1401788, by rfl⟩ : syracuseStep 1869051 = 2803577) B2803577
theorem B2803007 : Blo 1867635 2803007 := bstep (se 1 (by rfl) ⟨2102255, by rfl⟩ : syracuseStep 2803007 = 4204511) B4204511
theorem B25576897 : Blo 1867635 25576897 := bstep (se 2 (by rfl) ⟨9591336, by rfl⟩ : syracuseStep 25576897 = 19182673) B19182673
theorem B4490743 : Blo 1867635 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B2991611 : Blo 1867635 2991611 := bstep (se 1 (by rfl) ⟨2243708, by rfl⟩ : syracuseStep 2991611 = 4487417) B4487417
theorem B31925825 : Blo 1867635 31925825 := bstep (se 2 (by rfl) ⟨11972184, by rfl⟩ : syracuseStep 31925825 = 23944369) B23944369
theorem B6309467 : Blo 1867635 6309467 := bstep (se 1 (by rfl) ⟨4732100, by rfl⟩ : syracuseStep 6309467 = 9464201) B9464201
theorem B27666083 : Blo 1867635 27666083 := bstep (se 1 (by rfl) ⟨20749562, by rfl⟩ : syracuseStep 27666083 = 41499125) B41499125
theorem B2991791 : Blo 1867635 2991791 := bstep (se 1 (by rfl) ⟨2243843, by rfl⟩ : syracuseStep 2991791 = 4487687) B4487687
theorem B1869551 : Blo 1867635 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B40404743 : Blo 1867635 40404743 := bstep (se 1 (by rfl) ⟨30303557, by rfl⟩ : syracuseStep 40404743 = 60607115) B60607115
theorem B2803679 : Blo 1867635 2803679 := bstep (se 1 (by rfl) ⟨2102759, by rfl⟩ : syracuseStep 2803679 = 4205519) B4205519
theorem B3549167 : Blo 1867635 3549167 := bstep (se 1 (by rfl) ⟨2661875, by rfl⟩ : syracuseStep 3549167 = 5323751) B5323751
theorem B2803739 : Blo 1867635 2803739 := bstep (se 1 (by rfl) ⟨2102804, by rfl⟩ : syracuseStep 2803739 = 4205609) B4205609
theorem B4204583 : Blo 1867635 4204583 := bstep (se 1 (by rfl) ⟨3153437, by rfl⟩ : syracuseStep 4204583 = 6306875) B6306875
theorem B2803895 : Blo 1867635 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B41502905 : Blo 1867635 41502905 := bstep (se 2 (by rfl) ⟨15563589, by rfl⟩ : syracuseStep 41502905 = 31127179) B31127179
theorem B2803919 : Blo 1867635 2803919 := bstep (se 1 (by rfl) ⟨2102939, by rfl⟩ : syracuseStep 2803919 = 4205879) B4205879
theorem B5318875 : Blo 1867635 5318875 := bstep (se 1 (by rfl) ⟨3989156, by rfl⟩ : syracuseStep 5318875 = 7978313) B7978313
theorem B4204763 : Blo 1867635 4204763 := bstep (se 1 (by rfl) ⟨3153572, by rfl⟩ : syracuseStep 4204763 = 6307145) B6307145
theorem B23955851 : Blo 1867635 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B4205033 : Blo 1867635 4205033 := bstep (se 2 (by rfl) ⟨1576887, by rfl⟩ : syracuseStep 4205033 = 3153775) B3153775
theorem B2804315 : Blo 1867635 2804315 := bstep (se 1 (by rfl) ⟨2103236, by rfl⟩ : syracuseStep 2804315 = 4206473) B4206473
theorem B14191199 : Blo 1867635 14191199 := bstep (se 1 (by rfl) ⟨10643399, by rfl⟩ : syracuseStep 14191199 = 21286799) B21286799
theorem B9456425 : Blo 1867635 9456425 := bstep (se 2 (by rfl) ⟨3546159, by rfl⟩ : syracuseStep 9456425 = 7092319) B7092319
theorem B5319503 : Blo 1867635 5319503 := bstep (se 1 (by rfl) ⟨3989627, by rfl⟩ : syracuseStep 5319503 = 7979255) B7979255
theorem B4729711 : Blo 1867635 4729711 := bstep (se 1 (by rfl) ⟨3547283, by rfl⟩ : syracuseStep 4729711 = 7094567) B7094567
theorem B4205915 : Blo 1867635 4205915 := bstep (se 1 (by rfl) ⟨3154436, by rfl⟩ : syracuseStep 4205915 = 6308873) B6308873
theorem B14183909 : Blo 1867635 14183909 := bstep (se 4 (by rfl) ⟨1329741, by rfl⟩ : syracuseStep 14183909 = 2659483) B2659483
theorem B4206185 : Blo 1867635 4206185 := bstep (se 2 (by rfl) ⟨1577319, by rfl⟩ : syracuseStep 4206185 = 3154639) B3154639
theorem B7573459 : Blo 1867635 7573459 := bstep (se 1 (by rfl) ⟨5680094, by rfl⟩ : syracuseStep 7573459 = 11360189) B11360189
theorem B5320687 : Blo 1867635 5320687 := bstep (se 1 (by rfl) ⟨3990515, by rfl⟩ : syracuseStep 5320687 = 7981031) B7981031
theorem B2994239 : Blo 1867635 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B6303905 : Blo 1867635 6303905 := bstep (se 2 (by rfl) ⟨2363964, by rfl⟩ : syracuseStep 6303905 = 4727929) B4727929
theorem B9457883 : Blo 1867635 9457883 := bstep (se 1 (by rfl) ⟨7093412, by rfl⟩ : syracuseStep 9457883 = 14186825) B14186825
theorem B5984543 : Blo 1867635 5984543 := bstep (se 1 (by rfl) ⟨4488407, by rfl⟩ : syracuseStep 5984543 = 8976815) B8976815
theorem B18444793 : Blo 1867635 18444793 := bstep (se 2 (by rfl) ⟨6916797, by rfl⟩ : syracuseStep 18444793 = 13833595) B13833595
theorem B26940185 : Blo 1867635 26940185 := bstep (se 2 (by rfl) ⟨10102569, by rfl⟩ : syracuseStep 26940185 = 20205139) B20205139
theorem B7983953 : Blo 1867635 7983953 := bstep (se 2 (by rfl) ⟨2993982, by rfl⟩ : syracuseStep 7983953 = 5987965) B5987965
theorem B64697201 : Blo 1867635 64697201 := bstep (se 2 (by rfl) ⟨24261450, by rfl⟩ : syracuseStep 64697201 = 48522901) B48522901
theorem B4731929 : Blo 1867635 4731929 := bstep (se 2 (by rfl) ⟨1774473, by rfl⟩ : syracuseStep 4731929 = 3548947) B3548947
theorem B2880607 : Blo 1867635 2880607 := bstep (se 1 (by rfl) ⟨2160455, by rfl⟩ : syracuseStep 2880607 = 4320911) B4320911
theorem B4732091 : Blo 1867635 4732091 := bstep (se 1 (by rfl) ⟨3549068, by rfl⟩ : syracuseStep 4732091 = 7098137) B7098137
theorem B12137795 : Blo 1867635 12137795 := bstep (se 1 (by rfl) ⟨9103346, by rfl⟩ : syracuseStep 12137795 = 18206693) B18206693
theorem B11974007 : Blo 1867635 11974007 := bstep (se 1 (by rfl) ⟨8980505, by rfl⟩ : syracuseStep 11974007 = 17961011) B17961011
theorem B14194115 : Blo 1867635 14194115 := bstep (se 1 (by rfl) ⟨10645586, by rfl⟩ : syracuseStep 14194115 = 21291173) B21291173
theorem B6305363 : Blo 1867635 6305363 := bstep (se 1 (by rfl) ⟨4729022, by rfl⟩ : syracuseStep 6305363 = 9458045) B9458045
theorem B3152425 : Blo 1867635 3152425 := bstep (se 2 (by rfl) ⟨1182159, by rfl⟩ : syracuseStep 3152425 = 2364319) B2364319
theorem B14187311 : Blo 1867635 14187311 := bstep (se 1 (by rfl) ⟨10640483, by rfl⟩ : syracuseStep 14187311 = 21280967) B21280967
theorem B17955665 : Blo 1867635 17955665 := bstep (se 2 (by rfl) ⟨6733374, by rfl⟩ : syracuseStep 17955665 = 13466749) B13466749
theorem B7093079 : Blo 1867635 7093079 := bstep (se 1 (by rfl) ⟨5319809, by rfl⟩ : syracuseStep 7093079 = 10639619) B10639619
theorem B3152891 : Blo 1867635 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B22166711 : Blo 1867635 22166711 := bstep (se 1 (by rfl) ⟨16625033, by rfl⟩ : syracuseStep 22166711 = 33250067) B33250067
theorem B9460961 : Blo 1867635 9460961 := bstep (se 2 (by rfl) ⟨3547860, by rfl⟩ : syracuseStep 9460961 = 7095721) B7095721
theorem B3153215 : Blo 1867635 3153215 := bstep (se 1 (by rfl) ⟨2364911, by rfl⟩ : syracuseStep 3153215 = 4729823) B4729823
theorem B3153323 : Blo 1867635 3153323 := bstep (se 1 (by rfl) ⟨2364992, by rfl⟩ : syracuseStep 3153323 = 4729985) B4729985
theorem B4202279 : Blo 1867635 4202279 := bstep (se 1 (by rfl) ⟨3151709, by rfl⟩ : syracuseStep 4202279 = 6303419) B6303419
theorem B3546919 : Blo 1867635 3546919 := bstep (se 1 (by rfl) ⟨2660189, by rfl⟩ : syracuseStep 3546919 = 5320379) B5320379
theorem B32350045 : Blo 1867635 32350045 := bstep (se 3 (by rfl) ⟨6065633, by rfl⟩ : syracuseStep 32350045 = 12131267) B12131267
theorem B2801567 : Blo 1867635 2801567 := bstep (se 1 (by rfl) ⟨2101175, by rfl⟩ : syracuseStep 2801567 = 4202351) B4202351
theorem B3153863 : Blo 1867635 3153863 := bstep (se 1 (by rfl) ⟨2365397, by rfl⟩ : syracuseStep 3153863 = 4730795) B4730795
theorem B11370451 : Blo 1867635 11370451 := bstep (se 1 (by rfl) ⟨8527838, by rfl⟩ : syracuseStep 11370451 = 17055677) B17055677
theorem B2801657 : Blo 1867635 2801657 := bstep (se 2 (by rfl) ⟨1050621, by rfl⟩ : syracuseStep 2801657 = 2101243) B2101243
theorem B221544467 : Blo 1867635 221544467 := bstep (se 1 (by rfl) ⟨166158350, by rfl⟩ : syracuseStep 221544467 = 332316701) B332316701
theorem B1867867 : Blo 1867635 1867867 := bstep (se 1 (by rfl) ⟨1400900, by rfl⟩ : syracuseStep 1867867 = 2801801) B2801801
theorem B4202603 : Blo 1867635 4202603 := bstep (se 1 (by rfl) ⟨3151952, by rfl⟩ : syracuseStep 4202603 = 6303905) B6303905
theorem B1867931 : Blo 1867635 1867931 := bstep (se 1 (by rfl) ⟨1400948, by rfl⟩ : syracuseStep 1867931 = 2801897) B2801897
theorem B1868015 : Blo 1867635 1868015 := bstep (se 1 (by rfl) ⟨1401011, by rfl⟩ : syracuseStep 1868015 = 2802023) B2802023
theorem B1868095 : Blo 1867635 1868095 := bstep (se 1 (by rfl) ⟨1401071, by rfl⟩ : syracuseStep 1868095 = 2802143) B2802143
theorem B1868263 : Blo 1867635 1868263 := bstep (se 1 (by rfl) ⟨1401197, by rfl⟩ : syracuseStep 1868263 = 2802395) B2802395
theorem B43131467 : Blo 1867635 43131467 := bstep (se 1 (by rfl) ⟨32348600, by rfl⟩ : syracuseStep 43131467 = 64697201) B64697201
theorem B24593057 : Blo 1867635 24593057 := bstep (se 2 (by rfl) ⟨9222396, by rfl⟩ : syracuseStep 24593057 = 18444793) B18444793
theorem B3154619 : Blo 1867635 3154619 := bstep (se 1 (by rfl) ⟨2365964, by rfl⟩ : syracuseStep 3154619 = 4731929) B4731929
theorem B4203233 : Blo 1867635 4203233 := bstep (se 2 (by rfl) ⟨1576212, by rfl⟩ : syracuseStep 4203233 = 3152425) B3152425
theorem B7095023 : Blo 1867635 7095023 := bstep (se 1 (by rfl) ⟨5321267, by rfl⟩ : syracuseStep 7095023 = 10642535) B10642535
theorem B2130683 : Blo 1867635 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B1868539 : Blo 1867635 1868539 := bstep (se 1 (by rfl) ⟨1401404, by rfl⟩ : syracuseStep 1868539 = 2802809) B2802809
theorem B15958781 : Blo 1867635 15958781 := bstep (se 3 (by rfl) ⟨2992271, by rfl⟩ : syracuseStep 15958781 = 5984543) B5984543
theorem B6308603 : Blo 1867635 6308603 := bstep (se 1 (by rfl) ⟨4731452, by rfl⟩ : syracuseStep 6308603 = 9462905) B9462905
theorem B3154727 : Blo 1867635 3154727 := bstep (se 1 (by rfl) ⟨2366045, by rfl⟩ : syracuseStep 3154727 = 4732091) B4732091
theorem B1868671 : Blo 1867635 1868671 := bstep (se 1 (by rfl) ⟨1401503, by rfl⟩ : syracuseStep 1868671 = 2803007) B2803007
theorem B9462743 : Blo 1867635 9462743 := bstep (se 1 (by rfl) ⟨7097057, by rfl⟩ : syracuseStep 9462743 = 14194115) B14194115
theorem B21283883 : Blo 1867635 21283883 := bstep (se 1 (by rfl) ⟨15962912, by rfl⟩ : syracuseStep 21283883 = 31925825) B31925825
theorem B4203575 : Blo 1867635 4203575 := bstep (se 1 (by rfl) ⟨3152681, by rfl⟩ : syracuseStep 4203575 = 6305363) B6305363
theorem B26936495 : Blo 1867635 26936495 := bstep (se 1 (by rfl) ⟨20202371, by rfl⟩ : syracuseStep 26936495 = 40404743) B40404743
theorem B1869119 : Blo 1867635 1869119 := bstep (se 1 (by rfl) ⟨1401839, by rfl⟩ : syracuseStep 1869119 = 2803679) B2803679
theorem B1869159 : Blo 1867635 1869159 := bstep (se 1 (by rfl) ⟨1401869, by rfl⟩ : syracuseStep 1869159 = 2803739) B2803739
theorem B2803055 : Blo 1867635 2803055 := bstep (se 1 (by rfl) ⟨2102291, by rfl⟩ : syracuseStep 2803055 = 4204583) B4204583
theorem B1869263 : Blo 1867635 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B1869279 : Blo 1867635 1869279 := bstep (se 1 (by rfl) ⟨1401959, by rfl⟩ : syracuseStep 1869279 = 2803919) B2803919
theorem B2803175 : Blo 1867635 2803175 := bstep (se 1 (by rfl) ⟨2102381, by rfl⟩ : syracuseStep 2803175 = 4204763) B4204763
theorem B2803355 : Blo 1867635 2803355 := bstep (se 1 (by rfl) ⟨2102516, by rfl⟩ : syracuseStep 2803355 = 4205033) B4205033
theorem B1869543 : Blo 1867635 1869543 := bstep (se 1 (by rfl) ⟨1402157, by rfl⟩ : syracuseStep 1869543 = 2804315) B2804315
theorem B11970443 : Blo 1867635 11970443 := bstep (se 1 (by rfl) ⟨8977832, by rfl⟩ : syracuseStep 11970443 = 17955665) B17955665
theorem B4728719 : Blo 1867635 4728719 := bstep (se 1 (by rfl) ⟨3546539, by rfl⟩ : syracuseStep 4728719 = 7093079) B7093079
theorem B2803943 : Blo 1867635 2803943 := bstep (se 1 (by rfl) ⟨2102957, by rfl⟩ : syracuseStep 2803943 = 4205915) B4205915
theorem B9455939 : Blo 1867635 9455939 := bstep (se 1 (by rfl) ⟨7091954, by rfl⟩ : syracuseStep 9455939 = 14183909) B14183909
theorem B4729225 : Blo 1867635 4729225 := bstep (se 2 (by rfl) ⟨1773459, by rfl⟩ : syracuseStep 4729225 = 3546919) B3546919
theorem B2804123 : Blo 1867635 2804123 := bstep (se 1 (by rfl) ⟨2103092, by rfl⟩ : syracuseStep 2804123 = 4206185) B4206185
theorem B43133393 : Blo 1867635 43133393 := bstep (se 2 (by rfl) ⟨16175022, by rfl⟩ : syracuseStep 43133393 = 32350045) B32350045
theorem B4205339 : Blo 1867635 4205339 := bstep (se 1 (by rfl) ⟨3154004, by rfl⟩ : syracuseStep 4205339 = 6308009) B6308009
theorem B10644311 : Blo 1867635 10644311 := bstep (se 1 (by rfl) ⟨7983233, by rfl⟩ : syracuseStep 10644311 = 15966467) B15966467
theorem B17960123 : Blo 1867635 17960123 := bstep (se 1 (by rfl) ⟨13470092, by rfl⟩ : syracuseStep 17960123 = 26940185) B26940185
theorem B4205951 : Blo 1867635 4205951 := bstep (se 1 (by rfl) ⟨3154463, by rfl⟩ : syracuseStep 4205951 = 6308927) B6308927
theorem B7982671 : Blo 1867635 7982671 := bstep (se 1 (by rfl) ⟨5987003, by rfl⟩ : syracuseStep 7982671 = 11974007) B11974007
theorem B4206311 : Blo 1867635 4206311 := bstep (se 1 (by rfl) ⟨3154733, by rfl⟩ : syracuseStep 4206311 = 6309467) B6309467
theorem B1994527 : Blo 1867635 1994527 := bstep (se 1 (by rfl) ⟨1495895, by rfl⟩ : syracuseStep 1994527 = 2991791) B2991791
theorem B27668603 : Blo 1867635 27668603 := bstep (se 1 (by rfl) ⟨20751452, by rfl⟩ : syracuseStep 27668603 = 41502905) B41502905
theorem B15970567 : Blo 1867635 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B6304283 : Blo 1867635 6304283 := bstep (se 1 (by rfl) ⟨4728212, by rfl⟩ : syracuseStep 6304283 = 9456425) B9456425
theorem B9458207 : Blo 1867635 9458207 := bstep (se 1 (by rfl) ⟨7093655, by rfl⟩ : syracuseStep 9458207 = 14187311) B14187311
theorem B2101927 : Blo 1867635 2101927 := bstep (se 1 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 2101927 = 3152891) B3152891
theorem B2102143 : Blo 1867635 2102143 := bstep (se 1 (by rfl) ⟨1576607, by rfl⟩ : syracuseStep 2102143 = 3153215) B3153215
theorem B2102215 : Blo 1867635 2102215 := bstep (se 1 (by rfl) ⟨1576661, by rfl⟩ : syracuseStep 2102215 = 3153323) B3153323
theorem B10097945 : Blo 1867635 10097945 := bstep (se 2 (by rfl) ⟨3786729, by rfl⟩ : syracuseStep 10097945 = 7573459) B7573459
theorem B15160601 : Blo 1867635 15160601 := bstep (se 2 (by rfl) ⟨5685225, by rfl⟩ : syracuseStep 15160601 = 11370451) B11370451
theorem B2102575 : Blo 1867635 2102575 := bstep (se 1 (by rfl) ⟨1576931, by rfl⟩ : syracuseStep 2102575 = 3153863) B3153863
theorem B2659711 : Blo 1867635 2659711 := bstep (se 1 (by rfl) ⟨1994783, by rfl⟩ : syracuseStep 2659711 = 3989567) B3989567
theorem B1996159 : Blo 1867635 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B4200355277 : Blo 1867635 4200355277 := bstep (se 3 (by rfl) ⟨787566614, by rfl⟩ : syracuseStep 4200355277 = 1575133229) B1575133229
theorem B6305255 : Blo 1867635 6305255 := bstep (se 1 (by rfl) ⟨4728941, by rfl⟩ : syracuseStep 6305255 = 9457883) B9457883
theorem B7091833 : Blo 1867635 7091833 := bstep (se 2 (by rfl) ⟨2659437, by rfl⟩ : syracuseStep 7091833 = 5318875) B5318875
theorem B7984943 : Blo 1867635 7984943 := bstep (se 1 (by rfl) ⟨5988707, by rfl⟩ : syracuseStep 7984943 = 11977415) B11977415
theorem B5322635 : Blo 1867635 5322635 := bstep (se 1 (by rfl) ⟨3991976, by rfl⟩ : syracuseStep 5322635 = 7983953) B7983953
theorem B8091863 : Blo 1867635 8091863 := bstep (se 1 (by rfl) ⟨6068897, by rfl⟩ : syracuseStep 8091863 = 12137795) B12137795
theorem B43145581 : Blo 1867635 43145581 := bstep (se 3 (by rfl) ⟨8089796, by rfl⟩ : syracuseStep 43145581 = 16179593) B16179593
theorem B6306281 : Blo 1867635 6306281 := bstep (se 2 (by rfl) ⟨2364855, by rfl⟩ : syracuseStep 6306281 = 4729711) B4729711
theorem B7977629 : Blo 1867635 7977629 := bstep (se 3 (by rfl) ⟨1495805, by rfl⟩ : syracuseStep 7977629 = 2991611) B2991611
theorem B2366111 : Blo 1867635 2366111 := bstep (se 1 (by rfl) ⟨1774583, by rfl⟩ : syracuseStep 2366111 = 3549167) B3549167
theorem B3840809 : Blo 1867635 3840809 := bstep (se 2 (by rfl) ⟨1440303, by rfl⟩ : syracuseStep 3840809 = 2880607) B2880607
theorem B9460637 : Blo 1867635 9460637 := bstep (se 3 (by rfl) ⟨1773869, by rfl⟩ : syracuseStep 9460637 = 3547739) B3547739
theorem B9460799 : Blo 1867635 9460799 := bstep (se 1 (by rfl) ⟨7095599, by rfl⟩ : syracuseStep 9460799 = 14191199) B14191199
theorem B73776221 : Blo 1867635 73776221 := bstep (se 3 (by rfl) ⟨13833041, by rfl⟩ : syracuseStep 73776221 = 27666083) B27666083
theorem B3546335 : Blo 1867635 3546335 := bstep (se 1 (by rfl) ⟨2659751, by rfl⟩ : syracuseStep 3546335 = 5319503) B5319503
theorem B34102529 : Blo 1867635 34102529 := bstep (se 2 (by rfl) ⟨12788448, by rfl⟩ : syracuseStep 34102529 = 25576897) B25576897
theorem B5987657 : Blo 1867635 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B14777807 : Blo 1867635 14777807 := bstep (se 1 (by rfl) ⟨11083355, by rfl⟩ : syracuseStep 14777807 = 22166711) B22166711
theorem B6307307 : Blo 1867635 6307307 := bstep (se 1 (by rfl) ⟨4730480, by rfl⟩ : syracuseStep 6307307 = 9460961) B9460961
theorem B2801519 : Blo 1867635 2801519 := bstep (se 1 (by rfl) ⟨2101139, by rfl⟩ : syracuseStep 2801519 = 4202279) B4202279
theorem B1867711 : Blo 1867635 1867711 := bstep (se 1 (by rfl) ⟨1400783, by rfl⟩ : syracuseStep 1867711 = 2801567) B2801567
theorem B7094249 : Blo 1867635 7094249 := bstep (se 2 (by rfl) ⟨2660343, by rfl⟩ : syracuseStep 7094249 = 5320687) B5320687
theorem B1867771 : Blo 1867635 1867771 := bstep (se 1 (by rfl) ⟨1400828, by rfl⟩ : syracuseStep 1867771 = 2801657) B2801657
theorem B2801735 : Blo 1867635 2801735 := bstep (se 1 (by rfl) ⟨2101301, by rfl⟩ : syracuseStep 2801735 = 4202603) B4202603
theorem B4202855 : Blo 1867635 4202855 := bstep (se 1 (by rfl) ⟨3152141, by rfl⟩ : syracuseStep 4202855 = 6304283) B6304283
theorem B28754311 : Blo 1867635 28754311 := bstep (se 1 (by rfl) ⟨21565733, by rfl⟩ : syracuseStep 28754311 = 43131467) B43131467
theorem B2802155 : Blo 1867635 2802155 := bstep (se 1 (by rfl) ⟨2101616, by rfl⟩ : syracuseStep 2802155 = 4203233) B4203233
theorem B6308495 : Blo 1867635 6308495 := bstep (se 1 (by rfl) ⟨4731371, by rfl⟩ : syracuseStep 6308495 = 9462743) B9462743
theorem B14189255 : Blo 1867635 14189255 := bstep (se 1 (by rfl) ⟨10641941, by rfl⟩ : syracuseStep 14189255 = 21283883) B21283883
theorem B2802383 : Blo 1867635 2802383 := bstep (se 1 (by rfl) ⟨2101787, by rfl⟩ : syracuseStep 2802383 = 4203575) B4203575
theorem B17957663 : Blo 1867635 17957663 := bstep (se 1 (by rfl) ⟨13468247, by rfl⟩ : syracuseStep 17957663 = 26936495) B26936495
theorem B2802569 : Blo 1867635 2802569 := bstep (se 2 (by rfl) ⟨1050963, by rfl⟩ : syracuseStep 2802569 = 2101927) B2101927
theorem B1868703 : Blo 1867635 1868703 := bstep (se 1 (by rfl) ⟨1401527, by rfl⟩ : syracuseStep 1868703 = 2803055) B2803055
theorem B4203503 : Blo 1867635 4203503 := bstep (se 1 (by rfl) ⟨3152627, by rfl⟩ : syracuseStep 4203503 = 6305255) B6305255
theorem B1868783 : Blo 1867635 1868783 := bstep (se 1 (by rfl) ⟨1401587, by rfl⟩ : syracuseStep 1868783 = 2803175) B2803175
theorem B1868903 : Blo 1867635 1868903 := bstep (se 1 (by rfl) ⟨1401677, by rfl⟩ : syracuseStep 1868903 = 2803355) B2803355
theorem B2802857 : Blo 1867635 2802857 := bstep (se 2 (by rfl) ⟨1051071, by rfl⟩ : syracuseStep 2802857 = 2102143) B2102143
theorem B7980295 : Blo 1867635 7980295 := bstep (se 1 (by rfl) ⟨5985221, by rfl⟩ : syracuseStep 7980295 = 11970443) B11970443
theorem B2802953 : Blo 1867635 2802953 := bstep (se 2 (by rfl) ⟨1051107, by rfl⟩ : syracuseStep 2802953 = 2102215) B2102215
theorem B3548423 : Blo 1867635 3548423 := bstep (se 1 (by rfl) ⟨2661317, by rfl⟩ : syracuseStep 3548423 = 5322635) B5322635
theorem B1869295 : Blo 1867635 1869295 := bstep (se 1 (by rfl) ⟨1401971, by rfl⟩ : syracuseStep 1869295 = 2803943) B2803943
theorem B1869415 : Blo 1867635 1869415 := bstep (se 1 (by rfl) ⟨1402061, by rfl⟩ : syracuseStep 1869415 = 2804123) B2804123
theorem B28755595 : Blo 1867635 28755595 := bstep (se 1 (by rfl) ⟨21566696, by rfl⟩ : syracuseStep 28755595 = 43133393) B43133393
theorem B4204187 : Blo 1867635 4204187 := bstep (se 1 (by rfl) ⟨3153140, by rfl⟩ : syracuseStep 4204187 = 6306281) B6306281
theorem B2803433 : Blo 1867635 2803433 := bstep (se 2 (by rfl) ⟨1051287, by rfl⟩ : syracuseStep 2803433 = 2102575) B2102575
theorem B6309629 : Blo 1867635 6309629 := bstep (se 3 (by rfl) ⟨1183055, by rfl⟩ : syracuseStep 6309629 = 2366111) B2366111
theorem B2803559 : Blo 1867635 2803559 := bstep (se 1 (by rfl) ⟨2102669, by rfl⟩ : syracuseStep 2803559 = 4205339) B4205339
theorem B7096207 : Blo 1867635 7096207 := bstep (se 1 (by rfl) ⟨5322155, by rfl⟩ : syracuseStep 7096207 = 10644311) B10644311
theorem B10643561 : Blo 1867635 10643561 := bstep (se 2 (by rfl) ⟨3991335, by rfl⟩ : syracuseStep 10643561 = 7982671) B7982671
theorem B10242157 : Blo 1867635 10242157 := bstep (se 3 (by rfl) ⟨1920404, by rfl⟩ : syracuseStep 10242157 = 3840809) B3840809
theorem B9455777 : Blo 1867635 9455777 := bstep (se 2 (by rfl) ⟨3545916, by rfl⟩ : syracuseStep 9455777 = 7091833) B7091833
theorem B22735019 : Blo 1867635 22735019 := bstep (se 1 (by rfl) ⟨17051264, by rfl⟩ : syracuseStep 22735019 = 34102529) B34102529
theorem B3991771 : Blo 1867635 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B2803967 : Blo 1867635 2803967 := bstep (se 1 (by rfl) ⟨2102975, by rfl⟩ : syracuseStep 2803967 = 4205951) B4205951
theorem B4204871 : Blo 1867635 4204871 := bstep (se 1 (by rfl) ⟨3153653, by rfl⟩ : syracuseStep 4204871 = 6307307) B6307307
theorem B2804207 : Blo 1867635 2804207 := bstep (se 1 (by rfl) ⟨2103155, by rfl⟩ : syracuseStep 2804207 = 4206311) B4206311
theorem B4729499 : Blo 1867635 4729499 := bstep (se 1 (by rfl) ⟨3547124, by rfl⟩ : syracuseStep 4729499 = 7094249) B7094249
theorem B147696311 : Blo 1867635 147696311 := bstep (se 1 (by rfl) ⟨110772233, by rfl⟩ : syracuseStep 147696311 = 221544467) B221544467
theorem B21294089 : Blo 1867635 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B16395371 : Blo 1867635 16395371 := bstep (se 1 (by rfl) ⟨12296528, by rfl⟩ : syracuseStep 16395371 = 24593057) B24593057
theorem B57527441 : Blo 1867635 57527441 := bstep (se 2 (by rfl) ⟨21572790, by rfl⟩ : syracuseStep 57527441 = 43145581) B43145581
theorem B4730015 : Blo 1867635 4730015 := bstep (se 1 (by rfl) ⟨3547511, by rfl⟩ : syracuseStep 4730015 = 7095023) B7095023
theorem B4205735 : Blo 1867635 4205735 := bstep (se 1 (by rfl) ⟨3154301, by rfl⟩ : syracuseStep 4205735 = 6308603) B6308603
theorem B39407485 : Blo 1867635 39407485 := bstep (se 3 (by rfl) ⟨7388903, by rfl⟩ : syracuseStep 39407485 = 14777807) B14777807
theorem B5394575 : Blo 1867635 5394575 := bstep (se 1 (by rfl) ⟨4045931, by rfl⟩ : syracuseStep 5394575 = 8091863) B8091863
theorem B10637477 : Blo 1867635 10637477 := bstep (se 4 (by rfl) ⟨997263, by rfl⟩ : syracuseStep 10637477 = 1994527) B1994527
theorem B6303959 : Blo 1867635 6303959 := bstep (se 1 (by rfl) ⟨4727969, by rfl⟩ : syracuseStep 6303959 = 9455939) B9455939
theorem B5681821 : Blo 1867635 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B11973415 : Blo 1867635 11973415 := bstep (se 1 (by rfl) ⟨8980061, by rfl⟩ : syracuseStep 11973415 = 17960123) B17960123
theorem B2364223 : Blo 1867635 2364223 := bstep (se 1 (by rfl) ⟨1773167, by rfl⟩ : syracuseStep 2364223 = 3546335) B3546335
theorem B18445735 : Blo 1867635 18445735 := bstep (se 1 (by rfl) ⟨13834301, by rfl⟩ : syracuseStep 18445735 = 27668603) B27668603
theorem B6305471 : Blo 1867635 6305471 := bstep (se 1 (by rfl) ⟨4729103, by rfl⟩ : syracuseStep 6305471 = 9458207) B9458207
theorem B2103079 : Blo 1867635 2103079 := bstep (se 1 (by rfl) ⟨1577309, by rfl⟩ : syracuseStep 2103079 = 3154619) B3154619
theorem B10639187 : Blo 1867635 10639187 := bstep (se 1 (by rfl) ⟨7979390, by rfl⟩ : syracuseStep 10639187 = 15958781) B15958781
theorem B6305633 : Blo 1867635 6305633 := bstep (se 2 (by rfl) ⟨2364612, by rfl⟩ : syracuseStep 6305633 = 4729225) B4729225
theorem B2103151 : Blo 1867635 2103151 := bstep (se 1 (by rfl) ⟨1577363, by rfl⟩ : syracuseStep 2103151 = 3154727) B3154727
theorem B6731963 : Blo 1867635 6731963 := bstep (se 1 (by rfl) ⟨5048972, by rfl⟩ : syracuseStep 6731963 = 10097945) B10097945
theorem B10107067 : Blo 1867635 10107067 := bstep (se 1 (by rfl) ⟨7580300, by rfl⟩ : syracuseStep 10107067 = 15160601) B15160601
theorem B2800236851 : Blo 1867635 2800236851 := bstep (se 1 (by rfl) ⟨2100177638, by rfl⟩ : syracuseStep 2800236851 = 4200355277) B4200355277
theorem B786946357 : Blo 1867635 786946357 := bstep (se 5 (by rfl) ⟨36888110, by rfl⟩ : syracuseStep 786946357 = 73776221) B73776221
theorem B5323295 : Blo 1867635 5323295 := bstep (se 1 (by rfl) ⟨3992471, by rfl⟩ : syracuseStep 5323295 = 7984943) B7984943
theorem B3152479 : Blo 1867635 3152479 := bstep (se 1 (by rfl) ⟨2364359, by rfl⟩ : syracuseStep 3152479 = 4728719) B4728719
theorem B21273677 : Blo 1867635 21273677 := bstep (se 3 (by rfl) ⟨3988814, by rfl⟩ : syracuseStep 21273677 = 7977629) B7977629
theorem B3546281 : Blo 1867635 3546281 := bstep (se 2 (by rfl) ⟨1329855, by rfl⟩ : syracuseStep 3546281 = 2659711) B2659711
theorem B2661545 : Blo 1867635 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B6307091 : Blo 1867635 6307091 := bstep (se 1 (by rfl) ⟨4730318, by rfl⟩ : syracuseStep 6307091 = 9460637) B9460637
theorem B6307199 : Blo 1867635 6307199 := bstep (se 1 (by rfl) ⟨4730399, by rfl⟩ : syracuseStep 6307199 = 9460799) B9460799
theorem B1867679 : Blo 1867635 1867679 := bstep (se 1 (by rfl) ⟨1400759, by rfl⟩ : syracuseStep 1867679 = 2801519) B2801519
theorem B1867823 : Blo 1867635 1867823 := bstep (se 1 (by rfl) ⟨1400867, by rfl⟩ : syracuseStep 1867823 = 2801735) B2801735
theorem B3596383 : Blo 1867635 3596383 := bstep (se 1 (by rfl) ⟨2697287, by rfl⟩ : syracuseStep 3596383 = 5394575) B5394575
theorem B4202639 : Blo 1867635 4202639 := bstep (se 1 (by rfl) ⟨3151979, by rfl⟩ : syracuseStep 4202639 = 6303959) B6303959
theorem B13656209 : Blo 1867635 13656209 := bstep (se 2 (by rfl) ⟨5121078, by rfl⟩ : syracuseStep 13656209 = 10242157) B10242157
theorem B2801903 : Blo 1867635 2801903 := bstep (se 1 (by rfl) ⟨2101427, by rfl⟩ : syracuseStep 2801903 = 4202855) B4202855
theorem B13476089 : Blo 1867635 13476089 := bstep (se 2 (by rfl) ⟨5053533, by rfl⟩ : syracuseStep 13476089 = 10107067) B10107067
theorem B1868103 : Blo 1867635 1868103 := bstep (se 1 (by rfl) ⟨1401077, by rfl⟩ : syracuseStep 1868103 = 2802155) B2802155
theorem B1868255 : Blo 1867635 1868255 := bstep (se 1 (by rfl) ⟨1401191, by rfl⟩ : syracuseStep 1868255 = 2802383) B2802383
theorem B38339081 : Blo 1867635 38339081 := bstep (se 2 (by rfl) ⟨14377155, by rfl⟩ : syracuseStep 38339081 = 28754311) B28754311
theorem B1868379 : Blo 1867635 1868379 := bstep (se 1 (by rfl) ⟨1401284, by rfl⟩ : syracuseStep 1868379 = 2802569) B2802569
theorem B2802335 : Blo 1867635 2802335 := bstep (se 1 (by rfl) ⟨2101751, by rfl⟩ : syracuseStep 2802335 = 4203503) B4203503
theorem B1868571 : Blo 1867635 1868571 := bstep (se 1 (by rfl) ⟨1401428, by rfl⟩ : syracuseStep 1868571 = 2802857) B2802857
theorem B4203305 : Blo 1867635 4203305 := bstep (se 2 (by rfl) ⟨1576239, by rfl⟩ : syracuseStep 4203305 = 3152479) B3152479
theorem B1868635 : Blo 1867635 1868635 := bstep (se 1 (by rfl) ⟨1401476, by rfl⟩ : syracuseStep 1868635 = 2802953) B2802953
theorem B2802791 : Blo 1867635 2802791 := bstep (se 1 (by rfl) ⟨2102093, by rfl⟩ : syracuseStep 2802791 = 4204187) B4204187
theorem B4203647 : Blo 1867635 4203647 := bstep (se 1 (by rfl) ⟨3152735, by rfl⟩ : syracuseStep 4203647 = 6305471) B6305471
theorem B1868955 : Blo 1867635 1868955 := bstep (se 1 (by rfl) ⟨1401716, by rfl⟩ : syracuseStep 1868955 = 2803433) B2803433
theorem B4203755 : Blo 1867635 4203755 := bstep (se 1 (by rfl) ⟨3152816, by rfl⟩ : syracuseStep 4203755 = 6305633) B6305633
theorem B1869039 : Blo 1867635 1869039 := bstep (se 1 (by rfl) ⟨1401779, by rfl⟩ : syracuseStep 1869039 = 2803559) B2803559
theorem B7095707 : Blo 1867635 7095707 := bstep (se 1 (by rfl) ⟨5321780, by rfl⟩ : syracuseStep 7095707 = 10643561) B10643561
theorem B1869311 : Blo 1867635 1869311 := bstep (se 1 (by rfl) ⟨1401983, by rfl⟩ : syracuseStep 1869311 = 2803967) B2803967
theorem B2803247 : Blo 1867635 2803247 := bstep (se 1 (by rfl) ⟨2102435, by rfl⟩ : syracuseStep 2803247 = 4204871) B4204871
theorem B1869471 : Blo 1867635 1869471 := bstep (se 1 (by rfl) ⟨1402103, by rfl⟩ : syracuseStep 1869471 = 2804207) B2804207
theorem B3548863 : Blo 1867635 3548863 := bstep (se 1 (by rfl) ⟨2661647, by rfl⟩ : syracuseStep 3548863 = 5323295) B5323295
theorem B14182451 : Blo 1867635 14182451 := bstep (se 1 (by rfl) ⟨10636838, by rfl⟩ : syracuseStep 14182451 = 21273677) B21273677
theorem B10930247 : Blo 1867635 10930247 := bstep (se 1 (by rfl) ⟨8197685, by rfl⟩ : syracuseStep 10930247 = 16395371) B16395371
theorem B2803823 : Blo 1867635 2803823 := bstep (se 1 (by rfl) ⟨2102867, by rfl⟩ : syracuseStep 2803823 = 4205735) B4205735
theorem B4204727 : Blo 1867635 4204727 := bstep (se 1 (by rfl) ⟨3153545, by rfl⟩ : syracuseStep 4204727 = 6307091) B6307091
theorem B38340793 : Blo 1867635 38340793 := bstep (se 2 (by rfl) ⟨14377797, by rfl⟩ : syracuseStep 38340793 = 28755595) B28755595
theorem B4204799 : Blo 1867635 4204799 := bstep (se 1 (by rfl) ⟨3153599, by rfl⟩ : syracuseStep 4204799 = 6307199) B6307199
theorem B2804105 : Blo 1867635 2804105 := bstep (se 2 (by rfl) ⟨1051539, by rfl⟩ : syracuseStep 2804105 = 2103079) B2103079
theorem B2804201 : Blo 1867635 2804201 := bstep (se 2 (by rfl) ⟨1051575, by rfl⟩ : syracuseStep 2804201 = 2103151) B2103151
theorem B4205663 : Blo 1867635 4205663 := bstep (se 1 (by rfl) ⟨3154247, by rfl⟩ : syracuseStep 4205663 = 6308495) B6308495
theorem B9456749 : Blo 1867635 9456749 := bstep (se 3 (by rfl) ⟨1773140, by rfl⟩ : syracuseStep 9456749 = 3546281) B3546281
theorem B7097453 : Blo 1867635 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B11971775 : Blo 1867635 11971775 := bstep (se 1 (by rfl) ⟨8978831, by rfl⟩ : syracuseStep 11971775 = 17957663) B17957663
theorem B4206419 : Blo 1867635 4206419 := bstep (se 1 (by rfl) ⟨3154814, by rfl⟩ : syracuseStep 4206419 = 6309629) B6309629
theorem B6303851 : Blo 1867635 6303851 := bstep (se 1 (by rfl) ⟨4727888, by rfl⟩ : syracuseStep 6303851 = 9455777) B9455777
theorem B98464207 : Blo 1867635 98464207 := bstep (se 1 (by rfl) ⟨73848155, by rfl⟩ : syracuseStep 98464207 = 147696311) B147696311
theorem B38351627 : Blo 1867635 38351627 := bstep (se 1 (by rfl) ⟨28763720, by rfl⟩ : syracuseStep 38351627 = 57527441) B57527441
theorem B7091651 : Blo 1867635 7091651 := bstep (se 1 (by rfl) ⟨5318738, by rfl⟩ : syracuseStep 7091651 = 10637477) B10637477
theorem B5322361 : Blo 1867635 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B1049261809 : Blo 1867635 1049261809 := bstep (se 2 (by rfl) ⟨393473178, by rfl⟩ : syracuseStep 1049261809 = 786946357) B786946357
theorem B60626717 : Blo 1867635 60626717 := bstep (se 3 (by rfl) ⟨11367509, by rfl⟩ : syracuseStep 60626717 = 22735019) B22735019
theorem B9459503 : Blo 1867635 9459503 := bstep (se 1 (by rfl) ⟨7094627, by rfl⟩ : syracuseStep 9459503 = 14189255) B14189255
theorem B2365615 : Blo 1867635 2365615 := bstep (se 1 (by rfl) ⟨1774211, by rfl⟩ : syracuseStep 2365615 = 3548423) B3548423
theorem B7575761 : Blo 1867635 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B15964553 : Blo 1867635 15964553 := bstep (se 2 (by rfl) ⟨5986707, by rfl⟩ : syracuseStep 15964553 = 11973415) B11973415
theorem B3152297 : Blo 1867635 3152297 := bstep (se 2 (by rfl) ⟨1182111, by rfl⟩ : syracuseStep 3152297 = 2364223) B2364223
theorem B7092791 : Blo 1867635 7092791 := bstep (se 1 (by rfl) ⟨5319593, by rfl⟩ : syracuseStep 7092791 = 10639187) B10639187
theorem B4487975 : Blo 1867635 4487975 := bstep (se 1 (by rfl) ⟨3365981, by rfl⟩ : syracuseStep 4487975 = 6731963) B6731963
theorem B1866824567 : Blo 1867635 1866824567 := bstep (se 1 (by rfl) ⟨1400118425, by rfl⟩ : syracuseStep 1866824567 = 2800236851) B2800236851
theorem B10640393 : Blo 1867635 10640393 := bstep (se 2 (by rfl) ⟨3990147, by rfl⟩ : syracuseStep 10640393 = 7980295) B7980295
theorem B3152999 : Blo 1867635 3152999 := bstep (se 1 (by rfl) ⟨2364749, by rfl⟩ : syracuseStep 3152999 = 4729499) B4729499
theorem B14196059 : Blo 1867635 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B3153343 : Blo 1867635 3153343 := bstep (se 1 (by rfl) ⟨2365007, by rfl⟩ : syracuseStep 3153343 = 4730015) B4730015
theorem B98377253 : Blo 1867635 98377253 := bstep (se 4 (by rfl) ⟨9222867, by rfl⟩ : syracuseStep 98377253 = 18445735) B18445735
theorem B52543313 : Blo 1867635 52543313 := bstep (se 2 (by rfl) ⟨19703742, by rfl⟩ : syracuseStep 52543313 = 39407485) B39407485
theorem B9461609 : Blo 1867635 9461609 := bstep (se 2 (by rfl) ⟨3548103, by rfl⟩ : syracuseStep 9461609 = 7096207) B7096207
theorem B4202567 : Blo 1867635 4202567 := bstep (se 1 (by rfl) ⟨3151925, by rfl⟩ : syracuseStep 4202567 = 6303851) B6303851
theorem B2801759 : Blo 1867635 2801759 := bstep (se 1 (by rfl) ⟨2101319, by rfl⟩ : syracuseStep 2801759 = 4202639) B4202639
theorem B1867935 : Blo 1867635 1867935 := bstep (se 1 (by rfl) ⟨1400951, by rfl⟩ : syracuseStep 1867935 = 2801903) B2801903
theorem B3154153 : Blo 1867635 3154153 := bstep (se 2 (by rfl) ⟨1182807, by rfl⟩ : syracuseStep 3154153 = 2365615) B2365615
theorem B25559387 : Blo 1867635 25559387 := bstep (se 1 (by rfl) ⟨19169540, by rfl⟩ : syracuseStep 25559387 = 38339081) B38339081
theorem B1868223 : Blo 1867635 1868223 := bstep (se 1 (by rfl) ⟨1401167, by rfl⟩ : syracuseStep 1868223 = 2802335) B2802335
theorem B25567751 : Blo 1867635 25567751 := bstep (se 1 (by rfl) ⟨19175813, by rfl⟩ : syracuseStep 25567751 = 38351627) B38351627
theorem B2802203 : Blo 1867635 2802203 := bstep (se 1 (by rfl) ⟨2101652, by rfl⟩ : syracuseStep 2802203 = 4203305) B4203305
theorem B131285609 : Blo 1867635 131285609 := bstep (se 2 (by rfl) ⟨49232103, by rfl⟩ : syracuseStep 131285609 = 98464207) B98464207
theorem B1868527 : Blo 1867635 1868527 := bstep (se 1 (by rfl) ⟨1401395, by rfl⟩ : syracuseStep 1868527 = 2802791) B2802791
theorem B2802431 : Blo 1867635 2802431 := bstep (se 1 (by rfl) ⟨2101823, by rfl⟩ : syracuseStep 2802431 = 4203647) B4203647
theorem B2802503 : Blo 1867635 2802503 := bstep (se 1 (by rfl) ⟨2101877, by rfl⟩ : syracuseStep 2802503 = 4203755) B4203755
theorem B4727767 : Blo 1867635 4727767 := bstep (se 1 (by rfl) ⟨3545825, by rfl⟩ : syracuseStep 4727767 = 7091651) B7091651
theorem B1868831 : Blo 1867635 1868831 := bstep (se 1 (by rfl) ⟨1401623, by rfl⟩ : syracuseStep 1868831 = 2803247) B2803247
theorem B9454967 : Blo 1867635 9454967 := bstep (se 1 (by rfl) ⟨7091225, by rfl⟩ : syracuseStep 9454967 = 14182451) B14182451
theorem B1869215 : Blo 1867635 1869215 := bstep (se 1 (by rfl) ⟨1401911, by rfl⟩ : syracuseStep 1869215 = 2803823) B2803823
theorem B2803151 : Blo 1867635 2803151 := bstep (se 1 (by rfl) ⟨2102363, by rfl⟩ : syracuseStep 2803151 = 4204727) B4204727
theorem B2803199 : Blo 1867635 2803199 := bstep (se 1 (by rfl) ⟨2102399, by rfl⟩ : syracuseStep 2803199 = 4204799) B4204799
theorem B10643035 : Blo 1867635 10643035 := bstep (se 1 (by rfl) ⟨7982276, by rfl⟩ : syracuseStep 10643035 = 15964553) B15964553
theorem B1869403 : Blo 1867635 1869403 := bstep (se 1 (by rfl) ⟨1402052, by rfl⟩ : syracuseStep 1869403 = 2804105) B2804105
theorem B1869467 : Blo 1867635 1869467 := bstep (se 1 (by rfl) ⟨1402100, by rfl⟩ : syracuseStep 1869467 = 2804201) B2804201
theorem B4728527 : Blo 1867635 4728527 := bstep (se 1 (by rfl) ⟨3546395, by rfl⟩ : syracuseStep 4728527 = 7092791) B7092791
theorem B2991983 : Blo 1867635 2991983 := bstep (se 1 (by rfl) ⟨2243987, by rfl⟩ : syracuseStep 2991983 = 4487975) B4487975
theorem B4204457 : Blo 1867635 4204457 := bstep (se 2 (by rfl) ⟨1576671, by rfl⟩ : syracuseStep 4204457 = 3153343) B3153343
theorem B2803775 : Blo 1867635 2803775 := bstep (se 1 (by rfl) ⟨2102831, by rfl⟩ : syracuseStep 2803775 = 4205663) B4205663
theorem B7981183 : Blo 1867635 7981183 := bstep (se 1 (by rfl) ⟨5985887, by rfl⟩ : syracuseStep 7981183 = 11971775) B11971775
theorem B7096481 : Blo 1867635 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B9464039 : Blo 1867635 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B1399015745 : Blo 1867635 1399015745 := bstep (se 2 (by rfl) ⟨524630904, by rfl⟩ : syracuseStep 1399015745 = 1049261809) B1049261809
theorem B2804279 : Blo 1867635 2804279 := bstep (se 1 (by rfl) ⟨2103209, by rfl⟩ : syracuseStep 2804279 = 4206419) B4206419
theorem B51121057 : Blo 1867635 51121057 := bstep (se 2 (by rfl) ⟨19170396, by rfl⟩ : syracuseStep 51121057 = 38340793) B38340793
theorem B36416557 : Blo 1867635 36416557 := bstep (se 3 (by rfl) ⟨6828104, by rfl⟩ : syracuseStep 36416557 = 13656209) B13656209
theorem B19180709 : Blo 1867635 19180709 := bstep (se 4 (by rfl) ⟨1798191, by rfl⟩ : syracuseStep 19180709 = 3596383) B3596383
theorem B4730471 : Blo 1867635 4730471 := bstep (se 1 (by rfl) ⟨3547853, by rfl⟩ : syracuseStep 4730471 = 7095707) B7095707
theorem B7286831 : Blo 1867635 7286831 := bstep (se 1 (by rfl) ⟨5465123, by rfl⟩ : syracuseStep 7286831 = 10930247) B10930247
theorem B5050507 : Blo 1867635 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B2101531 : Blo 1867635 2101531 := bstep (se 1 (by rfl) ⟨1576148, by rfl⟩ : syracuseStep 2101531 = 3152297) B3152297
theorem B1244549711 : Blo 1867635 1244549711 := bstep (se 1 (by rfl) ⟨933412283, by rfl⟩ : syracuseStep 1244549711 = 1866824567) B1866824567
theorem B2101999 : Blo 1867635 2101999 := bstep (se 1 (by rfl) ⟨1576499, by rfl⟩ : syracuseStep 2101999 = 3152999) B3152999
theorem B6304499 : Blo 1867635 6304499 := bstep (se 1 (by rfl) ⟨4728374, by rfl⟩ : syracuseStep 6304499 = 9456749) B9456749
theorem B4731635 : Blo 1867635 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B4731817 : Blo 1867635 4731817 := bstep (se 2 (by rfl) ⟨1774431, by rfl⟩ : syracuseStep 4731817 = 3548863) B3548863
theorem B35936237 : Blo 1867635 35936237 := bstep (se 3 (by rfl) ⟨6738044, by rfl⟩ : syracuseStep 35936237 = 13476089) B13476089
theorem B40417811 : Blo 1867635 40417811 := bstep (se 1 (by rfl) ⟨30313358, by rfl⟩ : syracuseStep 40417811 = 60626717) B60626717
theorem B6306335 : Blo 1867635 6306335 := bstep (se 1 (by rfl) ⟨4729751, by rfl⟩ : syracuseStep 6306335 = 9459503) B9459503
theorem B7093595 : Blo 1867635 7093595 := bstep (se 1 (by rfl) ⟨5320196, by rfl⟩ : syracuseStep 7093595 = 10640393) B10640393
theorem B65584835 : Blo 1867635 65584835 := bstep (se 1 (by rfl) ⟨49188626, by rfl⟩ : syracuseStep 65584835 = 98377253) B98377253
theorem B35028875 : Blo 1867635 35028875 := bstep (se 1 (by rfl) ⟨26271656, by rfl⟩ : syracuseStep 35028875 = 52543313) B52543313
theorem B6307739 : Blo 1867635 6307739 := bstep (se 1 (by rfl) ⟨4730804, by rfl⟩ : syracuseStep 6307739 = 9461609) B9461609
theorem B4857887 : Blo 1867635 4857887 := bstep (se 1 (by rfl) ⟨3643415, by rfl⟩ : syracuseStep 4857887 = 7286831) B7286831
theorem B2801711 : Blo 1867635 2801711 := bstep (se 1 (by rfl) ⟨2101283, by rfl⟩ : syracuseStep 2801711 = 4202567) B4202567
theorem B1867839 : Blo 1867635 1867839 := bstep (se 1 (by rfl) ⟨1400879, by rfl⟩ : syracuseStep 1867839 = 2801759) B2801759
theorem B10641577 : Blo 1867635 10641577 := bstep (se 2 (by rfl) ⟨3990591, by rfl⟩ : syracuseStep 10641577 = 7981183) B7981183
theorem B6734009 : Blo 1867635 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B17039591 : Blo 1867635 17039591 := bstep (se 1 (by rfl) ⟨12779693, by rfl⟩ : syracuseStep 17039591 = 25559387) B25559387
theorem B1868135 : Blo 1867635 1868135 := bstep (se 1 (by rfl) ⟨1401101, by rfl⟩ : syracuseStep 1868135 = 2802203) B2802203
theorem B2802041 : Blo 1867635 2802041 := bstep (se 2 (by rfl) ⟨1050765, by rfl⟩ : syracuseStep 2802041 = 2101531) B2101531
theorem B87523739 : Blo 1867635 87523739 := bstep (se 1 (by rfl) ⟨65642804, by rfl⟩ : syracuseStep 87523739 = 131285609) B131285609
theorem B4202999 : Blo 1867635 4202999 := bstep (se 1 (by rfl) ⟨3152249, by rfl⟩ : syracuseStep 4202999 = 6304499) B6304499
theorem B3154423 : Blo 1867635 3154423 := bstep (se 1 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 3154423 = 4731635) B4731635
theorem B1868287 : Blo 1867635 1868287 := bstep (se 1 (by rfl) ⟨1401215, by rfl⟩ : syracuseStep 1868287 = 2802431) B2802431
theorem B1868335 : Blo 1867635 1868335 := bstep (se 1 (by rfl) ⟨1401251, by rfl⟩ : syracuseStep 1868335 = 2802503) B2802503
theorem B1868767 : Blo 1867635 1868767 := bstep (se 1 (by rfl) ⟨1401575, by rfl⟩ : syracuseStep 1868767 = 2803151) B2803151
theorem B2802665 : Blo 1867635 2802665 := bstep (se 2 (by rfl) ⟨1050999, by rfl⟩ : syracuseStep 2802665 = 2101999) B2101999
theorem B1868799 : Blo 1867635 1868799 := bstep (se 1 (by rfl) ⟨1401599, by rfl⟩ : syracuseStep 1868799 = 2803199) B2803199
theorem B6309089 : Blo 1867635 6309089 := bstep (se 2 (by rfl) ⟨2365908, by rfl⟩ : syracuseStep 6309089 = 4731817) B4731817
theorem B2802971 : Blo 1867635 2802971 := bstep (se 1 (by rfl) ⟨2102228, by rfl⟩ : syracuseStep 2802971 = 4204457) B4204457
theorem B1869183 : Blo 1867635 1869183 := bstep (se 1 (by rfl) ⟨1401887, by rfl⟩ : syracuseStep 1869183 = 2803775) B2803775
theorem B48555409 : Blo 1867635 48555409 := bstep (se 2 (by rfl) ⟨18208278, by rfl⟩ : syracuseStep 48555409 = 36416557) B36416557
theorem B6309359 : Blo 1867635 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B932677163 : Blo 1867635 932677163 := bstep (se 1 (by rfl) ⟨699507872, by rfl⟩ : syracuseStep 932677163 = 1399015745) B1399015745
theorem B26945207 : Blo 1867635 26945207 := bstep (se 1 (by rfl) ⟨20208905, by rfl⟩ : syracuseStep 26945207 = 40417811) B40417811
theorem B4204223 : Blo 1867635 4204223 := bstep (se 1 (by rfl) ⟨3153167, by rfl⟩ : syracuseStep 4204223 = 6306335) B6306335
theorem B1869519 : Blo 1867635 1869519 := bstep (se 1 (by rfl) ⟨1402139, by rfl⟩ : syracuseStep 1869519 = 2804279) B2804279
theorem B14190713 : Blo 1867635 14190713 := bstep (se 2 (by rfl) ⟨5321517, by rfl⟩ : syracuseStep 14190713 = 10643035) B10643035
theorem B4729063 : Blo 1867635 4729063 := bstep (se 1 (by rfl) ⟨3546797, by rfl⟩ : syracuseStep 4729063 = 7093595) B7093595
theorem B43723223 : Blo 1867635 43723223 := bstep (se 1 (by rfl) ⟨32792417, by rfl⟩ : syracuseStep 43723223 = 65584835) B65584835
theorem B4205159 : Blo 1867635 4205159 := bstep (se 1 (by rfl) ⟨3153869, by rfl⟩ : syracuseStep 4205159 = 6307739) B6307739
theorem B4205537 : Blo 1867635 4205537 := bstep (se 2 (by rfl) ⟨1577076, by rfl⟩ : syracuseStep 4205537 = 3154153) B3154153
theorem B6303311 : Blo 1867635 6303311 := bstep (se 1 (by rfl) ⟨4727483, by rfl⟩ : syracuseStep 6303311 = 9454967) B9454967
theorem B68161409 : Blo 1867635 68161409 := bstep (se 2 (by rfl) ⟨25560528, by rfl⟩ : syracuseStep 68161409 = 51121057) B51121057
theorem B6303689 : Blo 1867635 6303689 := bstep (se 2 (by rfl) ⟨2363883, by rfl⟩ : syracuseStep 6303689 = 4727767) B4727767
theorem B23957491 : Blo 1867635 23957491 := bstep (se 1 (by rfl) ⟨17968118, by rfl⟩ : syracuseStep 23957491 = 35936237) B35936237
theorem B4730987 : Blo 1867635 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B93410333 : Blo 1867635 93410333 := bstep (se 3 (by rfl) ⟨17514437, by rfl⟩ : syracuseStep 93410333 = 35028875) B35028875
theorem B17045167 : Blo 1867635 17045167 := bstep (se 1 (by rfl) ⟨12783875, by rfl⟩ : syracuseStep 17045167 = 25567751) B25567751
theorem B829699807 : Blo 1867635 829699807 := bstep (se 1 (by rfl) ⟨622274855, by rfl⟩ : syracuseStep 829699807 = 1244549711) B1244549711
theorem B3152351 : Blo 1867635 3152351 := bstep (se 1 (by rfl) ⟨2364263, by rfl⟩ : syracuseStep 3152351 = 4728527) B4728527
theorem B12787139 : Blo 1867635 12787139 := bstep (se 1 (by rfl) ⟨9590354, by rfl⟩ : syracuseStep 12787139 = 19180709) B19180709
theorem B7978621 : Blo 1867635 7978621 := bstep (se 3 (by rfl) ⟨1495991, by rfl⟩ : syracuseStep 7978621 = 2991983) B2991983
theorem B3153647 : Blo 1867635 3153647 := bstep (se 1 (by rfl) ⟨2365235, by rfl⟩ : syracuseStep 3153647 = 4730471) B4730471
theorem B1867807 : Blo 1867635 1867807 := bstep (se 1 (by rfl) ⟨1400855, by rfl⟩ : syracuseStep 1867807 = 2801711) B2801711
theorem B3153991 : Blo 1867635 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B4489339 : Blo 1867635 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B14188769 : Blo 1867635 14188769 := bstep (se 2 (by rfl) ⟨5320788, by rfl⟩ : syracuseStep 14188769 = 10641577) B10641577
theorem B1868027 : Blo 1867635 1868027 := bstep (se 1 (by rfl) ⟨1401020, by rfl⟩ : syracuseStep 1868027 = 2802041) B2802041
theorem B2801999 : Blo 1867635 2801999 := bstep (se 1 (by rfl) ⟨2101499, by rfl⟩ : syracuseStep 2801999 = 4202999) B4202999
theorem B1868443 : Blo 1867635 1868443 := bstep (se 1 (by rfl) ⟨1401332, by rfl⟩ : syracuseStep 1868443 = 2802665) B2802665
theorem B1868647 : Blo 1867635 1868647 := bstep (se 1 (by rfl) ⟨1401485, by rfl⟩ : syracuseStep 1868647 = 2802971) B2802971
theorem B2802815 : Blo 1867635 2802815 := bstep (se 1 (by rfl) ⟨2102111, by rfl⟩ : syracuseStep 2802815 = 4204223) B4204223
theorem B29148815 : Blo 1867635 29148815 := bstep (se 1 (by rfl) ⟨21861611, by rfl⟩ : syracuseStep 29148815 = 43723223) B43723223
theorem B2803439 : Blo 1867635 2803439 := bstep (se 1 (by rfl) ⟨2102579, by rfl⟩ : syracuseStep 2803439 = 4205159) B4205159
theorem B2803691 : Blo 1867635 2803691 := bstep (se 1 (by rfl) ⟨2102768, by rfl⟩ : syracuseStep 2803691 = 4205537) B4205537
theorem B22726889 : Blo 1867635 22726889 := bstep (se 2 (by rfl) ⟨8522583, by rfl⟩ : syracuseStep 22726889 = 17045167) B17045167
theorem B1106266409 : Blo 1867635 1106266409 := bstep (se 2 (by rfl) ⟨414849903, by rfl⟩ : syracuseStep 1106266409 = 829699807) B829699807
theorem B31943321 : Blo 1867635 31943321 := bstep (se 2 (by rfl) ⟨11978745, by rfl⟩ : syracuseStep 31943321 = 23957491) B23957491
theorem B3238591 : Blo 1867635 3238591 := bstep (se 1 (by rfl) ⟨2428943, by rfl⟩ : syracuseStep 3238591 = 4857887) B4857887
theorem B4205897 : Blo 1867635 4205897 := bstep (se 2 (by rfl) ⟨1577211, by rfl⟩ : syracuseStep 4205897 = 3154423) B3154423
theorem B4206059 : Blo 1867635 4206059 := bstep (se 1 (by rfl) ⟨3154544, by rfl⟩ : syracuseStep 4206059 = 6309089) B6309089
theorem B4206239 : Blo 1867635 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B621784775 : Blo 1867635 621784775 := bstep (se 1 (by rfl) ⟨466338581, by rfl⟩ : syracuseStep 621784775 = 932677163) B932677163
theorem B2101567 : Blo 1867635 2101567 := bstep (se 1 (by rfl) ⟨1576175, by rfl⟩ : syracuseStep 2101567 = 3152351) B3152351
theorem B10638161 : Blo 1867635 10638161 := bstep (se 2 (by rfl) ⟨3989310, by rfl⟩ : syracuseStep 10638161 = 7978621) B7978621
theorem B8524759 : Blo 1867635 8524759 := bstep (se 1 (by rfl) ⟨6393569, by rfl⟩ : syracuseStep 8524759 = 12787139) B12787139
theorem B2102431 : Blo 1867635 2102431 := bstep (se 1 (by rfl) ⟨1576823, by rfl⟩ : syracuseStep 2102431 = 3153647) B3153647
theorem B11359727 : Blo 1867635 11359727 := bstep (se 1 (by rfl) ⟨8519795, by rfl⟩ : syracuseStep 11359727 = 17039591) B17039591
theorem B58349159 : Blo 1867635 58349159 := bstep (se 1 (by rfl) ⟨43761869, by rfl⟩ : syracuseStep 58349159 = 87523739) B87523739
theorem B6305417 : Blo 1867635 6305417 := bstep (se 2 (by rfl) ⟨2364531, by rfl⟩ : syracuseStep 6305417 = 4729063) B4729063
theorem B62273555 : Blo 1867635 62273555 := bstep (se 1 (by rfl) ⟨46705166, by rfl⟩ : syracuseStep 62273555 = 93410333) B93410333
theorem B17963471 : Blo 1867635 17963471 := bstep (se 1 (by rfl) ⟨13472603, by rfl⟩ : syracuseStep 17963471 = 26945207) B26945207
theorem B9460475 : Blo 1867635 9460475 := bstep (se 1 (by rfl) ⟨7095356, by rfl⟩ : syracuseStep 9460475 = 14190713) B14190713
theorem B64740545 : Blo 1867635 64740545 := bstep (se 2 (by rfl) ⟨24277704, by rfl⟩ : syracuseStep 64740545 = 48555409) B48555409
theorem B4202207 : Blo 1867635 4202207 := bstep (se 1 (by rfl) ⟨3151655, by rfl⟩ : syracuseStep 4202207 = 6303311) B6303311
theorem B45440939 : Blo 1867635 45440939 := bstep (se 1 (by rfl) ⟨34080704, by rfl⟩ : syracuseStep 45440939 = 68161409) B68161409
theorem B4202459 : Blo 1867635 4202459 := bstep (se 1 (by rfl) ⟨3151844, by rfl⟩ : syracuseStep 4202459 = 6303689) B6303689
theorem B1867999 : Blo 1867635 1867999 := bstep (se 1 (by rfl) ⟨1400999, by rfl⟩ : syracuseStep 1867999 = 2801999) B2801999
theorem B2802089 : Blo 1867635 2802089 := bstep (se 2 (by rfl) ⟨1050783, by rfl⟩ : syracuseStep 2802089 = 2101567) B2101567
theorem B1868543 : Blo 1867635 1868543 := bstep (se 1 (by rfl) ⟨1401407, by rfl⟩ : syracuseStep 1868543 = 2802815) B2802815
theorem B4318121 : Blo 1867635 4318121 := bstep (se 2 (by rfl) ⟨1619295, by rfl⟩ : syracuseStep 4318121 = 3238591) B3238591
theorem B4203611 : Blo 1867635 4203611 := bstep (se 1 (by rfl) ⟨3152708, by rfl⟩ : syracuseStep 4203611 = 6305417) B6305417
theorem B19432543 : Blo 1867635 19432543 := bstep (se 1 (by rfl) ⟨14574407, by rfl⟩ : syracuseStep 19432543 = 29148815) B29148815
theorem B1868959 : Blo 1867635 1868959 := bstep (se 1 (by rfl) ⟨1401719, by rfl⟩ : syracuseStep 1868959 = 2803439) B2803439
theorem B1869127 : Blo 1867635 1869127 := bstep (se 1 (by rfl) ⟨1401845, by rfl⟩ : syracuseStep 1869127 = 2803691) B2803691
theorem B737510939 : Blo 1867635 737510939 := bstep (se 1 (by rfl) ⟨553133204, by rfl⟩ : syracuseStep 737510939 = 1106266409) B1106266409
theorem B2803241 : Blo 1867635 2803241 := bstep (se 2 (by rfl) ⟨1051215, by rfl⟩ : syracuseStep 2803241 = 2102431) B2102431
theorem B2803931 : Blo 1867635 2803931 := bstep (se 1 (by rfl) ⟨2102948, by rfl⟩ : syracuseStep 2803931 = 4205897) B4205897
theorem B2804039 : Blo 1867635 2804039 := bstep (se 1 (by rfl) ⟨2103029, by rfl⟩ : syracuseStep 2804039 = 4206059) B4206059
theorem B2804159 : Blo 1867635 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B4205321 : Blo 1867635 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B7573151 : Blo 1867635 7573151 := bstep (se 1 (by rfl) ⟨5679863, by rfl⟩ : syracuseStep 7573151 = 11359727) B11359727
theorem B38899439 : Blo 1867635 38899439 := bstep (se 1 (by rfl) ⟨29174579, by rfl⟩ : syracuseStep 38899439 = 58349159) B58349159
theorem B11366345 : Blo 1867635 11366345 := bstep (se 2 (by rfl) ⟨4262379, by rfl⟩ : syracuseStep 11366345 = 8524759) B8524759
theorem B15151259 : Blo 1867635 15151259 := bstep (se 1 (by rfl) ⟨11363444, by rfl⟩ : syracuseStep 15151259 = 22726889) B22726889
theorem B21295547 : Blo 1867635 21295547 := bstep (se 1 (by rfl) ⟨15971660, by rfl⟩ : syracuseStep 21295547 = 31943321) B31943321
theorem B43160363 : Blo 1867635 43160363 := bstep (se 1 (by rfl) ⟨32370272, by rfl⟩ : syracuseStep 43160363 = 64740545) B64740545
theorem B9459179 : Blo 1867635 9459179 := bstep (se 1 (by rfl) ⟨7094384, by rfl⟩ : syracuseStep 9459179 = 14188769) B14188769
theorem B5985785 : Blo 1867635 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B7092107 : Blo 1867635 7092107 := bstep (se 1 (by rfl) ⟨5319080, by rfl⟩ : syracuseStep 7092107 = 10638161) B10638161
theorem B41515703 : Blo 1867635 41515703 := bstep (se 1 (by rfl) ⟨31136777, by rfl⟩ : syracuseStep 41515703 = 62273555) B62273555
theorem B11975647 : Blo 1867635 11975647 := bstep (se 1 (by rfl) ⟨8981735, by rfl⟩ : syracuseStep 11975647 = 17963471) B17963471
theorem B6306983 : Blo 1867635 6306983 := bstep (se 1 (by rfl) ⟨4730237, by rfl⟩ : syracuseStep 6306983 = 9460475) B9460475
theorem B414523183 : Blo 1867635 414523183 := bstep (se 1 (by rfl) ⟨310892387, by rfl⟩ : syracuseStep 414523183 = 621784775) B621784775
theorem B2801471 : Blo 1867635 2801471 := bstep (se 1 (by rfl) ⟨2101103, by rfl⟩ : syracuseStep 2801471 = 4202207) B4202207
theorem B30293959 : Blo 1867635 30293959 := bstep (se 1 (by rfl) ⟨22720469, by rfl⟩ : syracuseStep 30293959 = 45440939) B45440939
theorem B2801639 : Blo 1867635 2801639 := bstep (se 1 (by rfl) ⟨2101229, by rfl⟩ : syracuseStep 2801639 = 4202459) B4202459
theorem B1868059 : Blo 1867635 1868059 := bstep (se 1 (by rfl) ⟨1401044, by rfl⟩ : syracuseStep 1868059 = 2802089) B2802089
theorem B14197031 : Blo 1867635 14197031 := bstep (se 1 (by rfl) ⟨10647773, by rfl⟩ : syracuseStep 14197031 = 21295547) B21295547
theorem B40403357 : Blo 1867635 40403357 := bstep (se 3 (by rfl) ⟨7575629, by rfl⟩ : syracuseStep 40403357 = 15151259) B15151259
theorem B2802407 : Blo 1867635 2802407 := bstep (se 1 (by rfl) ⟨2101805, by rfl⟩ : syracuseStep 2802407 = 4203611) B4203611
theorem B1868827 : Blo 1867635 1868827 := bstep (se 1 (by rfl) ⟨1401620, by rfl⟩ : syracuseStep 1868827 = 2803241) B2803241
theorem B4728071 : Blo 1867635 4728071 := bstep (se 1 (by rfl) ⟨3546053, by rfl⟩ : syracuseStep 4728071 = 7092107) B7092107
theorem B15967529 : Blo 1867635 15967529 := bstep (se 2 (by rfl) ⟨5987823, by rfl⟩ : syracuseStep 15967529 = 11975647) B11975647
theorem B1869287 : Blo 1867635 1869287 := bstep (se 1 (by rfl) ⟨1401965, by rfl⟩ : syracuseStep 1869287 = 2803931) B2803931
theorem B1869359 : Blo 1867635 1869359 := bstep (se 1 (by rfl) ⟨1402019, by rfl⟩ : syracuseStep 1869359 = 2804039) B2804039
theorem B1869439 : Blo 1867635 1869439 := bstep (se 1 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 1869439 = 2804159) B2804159
theorem B2803547 : Blo 1867635 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B4204655 : Blo 1867635 4204655 := bstep (se 1 (by rfl) ⟨3153491, by rfl⟩ : syracuseStep 4204655 = 6306983) B6306983
theorem B5048767 : Blo 1867635 5048767 := bstep (se 1 (by rfl) ⟨3786575, by rfl⟩ : syracuseStep 5048767 = 7573151) B7573151
theorem B28773575 : Blo 1867635 28773575 := bstep (se 1 (by rfl) ⟨21580181, by rfl⟩ : syracuseStep 28773575 = 43160363) B43160363
theorem B2878747 : Blo 1867635 2878747 := bstep (se 1 (by rfl) ⟨2159060, by rfl⟩ : syracuseStep 2878747 = 4318121) B4318121
theorem B15962093 : Blo 1867635 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B27677135 : Blo 1867635 27677135 := bstep (se 1 (by rfl) ⟨20757851, by rfl⟩ : syracuseStep 27677135 = 41515703) B41515703
theorem B25932959 : Blo 1867635 25932959 := bstep (se 1 (by rfl) ⟨19449719, by rfl⟩ : syracuseStep 25932959 = 38899439) B38899439
theorem B40391945 : Blo 1867635 40391945 := bstep (se 2 (by rfl) ⟨15146979, by rfl⟩ : syracuseStep 40391945 = 30293959) B30293959
theorem B6306119 : Blo 1867635 6306119 := bstep (se 1 (by rfl) ⟨4729589, by rfl⟩ : syracuseStep 6306119 = 9459179) B9459179
theorem B491673959 : Blo 1867635 491673959 := bstep (se 1 (by rfl) ⟨368755469, by rfl⟩ : syracuseStep 491673959 = 737510939) B737510939
theorem B25910057 : Blo 1867635 25910057 := bstep (se 2 (by rfl) ⟨9716271, by rfl⟩ : syracuseStep 25910057 = 19432543) B19432543
theorem B552697577 : Blo 1867635 552697577 := bstep (se 2 (by rfl) ⟨207261591, by rfl⟩ : syracuseStep 552697577 = 414523183) B414523183
theorem B1867647 : Blo 1867635 1867647 := bstep (se 1 (by rfl) ⟨1400735, by rfl⟩ : syracuseStep 1867647 = 2801471) B2801471
theorem B7577563 : Blo 1867635 7577563 := bstep (se 1 (by rfl) ⟨5683172, by rfl⟩ : syracuseStep 7577563 = 11366345) B11366345
theorem B1867759 : Blo 1867635 1867759 := bstep (se 1 (by rfl) ⟨1400819, by rfl⟩ : syracuseStep 1867759 = 2801639) B2801639
theorem B26935571 : Blo 1867635 26935571 := bstep (se 1 (by rfl) ⟨20201678, by rfl⟩ : syracuseStep 26935571 = 40403357) B40403357
theorem B1868271 : Blo 1867635 1868271 := bstep (se 1 (by rfl) ⟨1401203, by rfl⟩ : syracuseStep 1868271 = 2802407) B2802407
theorem B26927963 : Blo 1867635 26927963 := bstep (se 1 (by rfl) ⟨20195972, by rfl⟩ : syracuseStep 26927963 = 40391945) B40391945
theorem B1869031 : Blo 1867635 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B2803103 : Blo 1867635 2803103 := bstep (se 1 (by rfl) ⟨2102327, by rfl⟩ : syracuseStep 2803103 = 4204655) B4204655
theorem B15353317 : Blo 1867635 15353317 := bstep (se 4 (by rfl) ⟨1439373, by rfl⟩ : syracuseStep 15353317 = 2878747) B2878747
theorem B4204079 : Blo 1867635 4204079 := bstep (se 1 (by rfl) ⟨3153059, by rfl⟩ : syracuseStep 4204079 = 6306119) B6306119
theorem B10103417 : Blo 1867635 10103417 := bstep (se 2 (by rfl) ⟨3788781, by rfl⟩ : syracuseStep 10103417 = 7577563) B7577563
theorem B9464687 : Blo 1867635 9464687 := bstep (se 1 (by rfl) ⟨7098515, by rfl⟩ : syracuseStep 9464687 = 14197031) B14197031
theorem B18451423 : Blo 1867635 18451423 := bstep (se 1 (by rfl) ⟨13838567, by rfl⟩ : syracuseStep 18451423 = 27677135) B27677135
theorem B17288639 : Blo 1867635 17288639 := bstep (se 1 (by rfl) ⟨12966479, by rfl⟩ : syracuseStep 17288639 = 25932959) B25932959
theorem B10645019 : Blo 1867635 10645019 := bstep (se 1 (by rfl) ⟨7983764, by rfl⟩ : syracuseStep 10645019 = 15967529) B15967529
theorem B327782639 : Blo 1867635 327782639 := bstep (se 1 (by rfl) ⟨245836979, by rfl⟩ : syracuseStep 327782639 = 491673959) B491673959
theorem B17273371 : Blo 1867635 17273371 := bstep (se 1 (by rfl) ⟨12955028, by rfl⟩ : syracuseStep 17273371 = 25910057) B25910057
theorem B19182383 : Blo 1867635 19182383 := bstep (se 1 (by rfl) ⟨14386787, by rfl⟩ : syracuseStep 19182383 = 28773575) B28773575
theorem B368465051 : Blo 1867635 368465051 := bstep (se 1 (by rfl) ⟨276348788, by rfl⟩ : syracuseStep 368465051 = 552697577) B552697577
theorem B6731689 : Blo 1867635 6731689 := bstep (se 2 (by rfl) ⟨2524383, by rfl⟩ : syracuseStep 6731689 = 5048767) B5048767
theorem B3152047 : Blo 1867635 3152047 := bstep (se 1 (by rfl) ⟨2364035, by rfl⟩ : syracuseStep 3152047 = 4728071) B4728071
theorem B10641395 : Blo 1867635 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B218521759 : Blo 1867635 218521759 := bstep (se 1 (by rfl) ⟨163891319, by rfl⟩ : syracuseStep 218521759 = 327782639) B327782639
theorem B17957047 : Blo 1867635 17957047 := bstep (se 1 (by rfl) ⟨13467785, by rfl⟩ : syracuseStep 17957047 = 26935571) B26935571
theorem B4202729 : Blo 1867635 4202729 := bstep (se 2 (by rfl) ⟨1576023, by rfl⟩ : syracuseStep 4202729 = 3152047) B3152047
theorem B12788255 : Blo 1867635 12788255 := bstep (se 1 (by rfl) ⟨9591191, by rfl⟩ : syracuseStep 12788255 = 19182383) B19182383
theorem B1868735 : Blo 1867635 1868735 := bstep (se 1 (by rfl) ⟨1401551, by rfl⟩ : syracuseStep 1868735 = 2803103) B2803103
theorem B2802719 : Blo 1867635 2802719 := bstep (se 1 (by rfl) ⟨2102039, by rfl⟩ : syracuseStep 2802719 = 4204079) B4204079
theorem B24601897 : Blo 1867635 24601897 := bstep (se 2 (by rfl) ⟨9225711, by rfl⟩ : syracuseStep 24601897 = 18451423) B18451423
theorem B6735611 : Blo 1867635 6735611 := bstep (se 1 (by rfl) ⟨5051708, by rfl⟩ : syracuseStep 6735611 = 10103417) B10103417
theorem B6309791 : Blo 1867635 6309791 := bstep (se 1 (by rfl) ⟨4732343, by rfl⟩ : syracuseStep 6309791 = 9464687) B9464687
theorem B7096679 : Blo 1867635 7096679 := bstep (se 1 (by rfl) ⟨5322509, by rfl⟩ : syracuseStep 7096679 = 10645019) B10645019
theorem B17951975 : Blo 1867635 17951975 := bstep (se 1 (by rfl) ⟨13463981, by rfl⟩ : syracuseStep 17951975 = 26927963) B26927963
theorem B23031161 : Blo 1867635 23031161 := bstep (se 2 (by rfl) ⟨8636685, by rfl⟩ : syracuseStep 23031161 = 17273371) B17273371
theorem B81884357 : Blo 1867635 81884357 := bstep (se 4 (by rfl) ⟨7676658, by rfl⟩ : syracuseStep 81884357 = 15353317) B15353317
theorem B8975585 : Blo 1867635 8975585 := bstep (se 2 (by rfl) ⟨3365844, by rfl⟩ : syracuseStep 8975585 = 6731689) B6731689
theorem B245643367 : Blo 1867635 245643367 := bstep (se 1 (by rfl) ⟨184232525, by rfl⟩ : syracuseStep 245643367 = 368465051) B368465051
theorem B11525759 : Blo 1867635 11525759 := bstep (se 1 (by rfl) ⟨8644319, by rfl⟩ : syracuseStep 11525759 = 17288639) B17288639
theorem B7094263 : Blo 1867635 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B327524489 : Blo 1867635 327524489 := bstep (se 2 (by rfl) ⟨122821683, by rfl⟩ : syracuseStep 327524489 = 245643367) B245643367
theorem B2801819 : Blo 1867635 2801819 := bstep (se 1 (by rfl) ⟨2101364, by rfl⟩ : syracuseStep 2801819 = 4202729) B4202729
theorem B1868479 : Blo 1867635 1868479 := bstep (se 1 (by rfl) ⟨1401359, by rfl⟩ : syracuseStep 1868479 = 2802719) B2802719
theorem B4490407 : Blo 1867635 4490407 := bstep (se 1 (by rfl) ⟨3367805, by rfl⟩ : syracuseStep 4490407 = 6735611) B6735611
theorem B32802529 : Blo 1867635 32802529 := bstep (se 2 (by rfl) ⟨12300948, by rfl⟩ : syracuseStep 32802529 = 24601897) B24601897
theorem B15354107 : Blo 1867635 15354107 := bstep (se 1 (by rfl) ⟨11515580, by rfl⟩ : syracuseStep 15354107 = 23031161) B23031161
theorem B5983723 : Blo 1867635 5983723 := bstep (se 1 (by rfl) ⟨4487792, by rfl⟩ : syracuseStep 5983723 = 8975585) B8975585
theorem B4206527 : Blo 1867635 4206527 := bstep (se 1 (by rfl) ⟨3154895, by rfl⟩ : syracuseStep 4206527 = 6309791) B6309791
theorem B4731119 : Blo 1867635 4731119 := bstep (se 1 (by rfl) ⟨3548339, by rfl⟩ : syracuseStep 4731119 = 7096679) B7096679
theorem B9459017 : Blo 1867635 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B291362345 : Blo 1867635 291362345 := bstep (se 2 (by rfl) ⟨109260879, by rfl⟩ : syracuseStep 291362345 = 218521759) B218521759
theorem B23942729 : Blo 1867635 23942729 := bstep (se 2 (by rfl) ⟨8978523, by rfl⟩ : syracuseStep 23942729 = 17957047) B17957047
theorem B8525503 : Blo 1867635 8525503 := bstep (se 1 (by rfl) ⟨6394127, by rfl⟩ : syracuseStep 8525503 = 12788255) B12788255
theorem B54589571 : Blo 1867635 54589571 := bstep (se 1 (by rfl) ⟨40942178, by rfl⟩ : syracuseStep 54589571 = 81884357) B81884357
theorem B11967983 : Blo 1867635 11967983 := bstep (se 1 (by rfl) ⟨8975987, by rfl⟩ : syracuseStep 11967983 = 17951975) B17951975
theorem B7683839 : Blo 1867635 7683839 := bstep (se 1 (by rfl) ⟨5762879, by rfl⟩ : syracuseStep 7683839 = 11525759) B11525759
theorem B218349659 : Blo 1867635 218349659 := bstep (se 1 (by rfl) ⟨163762244, by rfl⟩ : syracuseStep 218349659 = 327524489) B327524489
theorem B1867879 : Blo 1867635 1867879 := bstep (se 1 (by rfl) ⟨1400909, by rfl⟩ : syracuseStep 1867879 = 2801819) B2801819
theorem B3154079 : Blo 1867635 3154079 := bstep (se 1 (by rfl) ⟨2365559, by rfl⟩ : syracuseStep 3154079 = 4731119) B4731119
theorem B194241563 : Blo 1867635 194241563 := bstep (se 1 (by rfl) ⟨145681172, by rfl⟩ : syracuseStep 194241563 = 291362345) B291362345
theorem B5122559 : Blo 1867635 5122559 := bstep (se 1 (by rfl) ⟨3841919, by rfl⟩ : syracuseStep 5122559 = 7683839) B7683839
theorem B2804351 : Blo 1867635 2804351 := bstep (se 1 (by rfl) ⟨2103263, by rfl⟩ : syracuseStep 2804351 = 4206527) B4206527
theorem B45469349 : Blo 1867635 45469349 := bstep (se 4 (by rfl) ⟨4262751, by rfl⟩ : syracuseStep 45469349 = 8525503) B8525503
theorem B15961819 : Blo 1867635 15961819 := bstep (se 1 (by rfl) ⟨11971364, by rfl⟩ : syracuseStep 15961819 = 23942729) B23942729
theorem B36393047 : Blo 1867635 36393047 := bstep (se 1 (by rfl) ⟨27294785, by rfl⟩ : syracuseStep 36393047 = 54589571) B54589571
theorem B10236071 : Blo 1867635 10236071 := bstep (se 1 (by rfl) ⟨7677053, by rfl⟩ : syracuseStep 10236071 = 15354107) B15354107
theorem B6306011 : Blo 1867635 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B5987209 : Blo 1867635 5987209 := bstep (se 2 (by rfl) ⟨2245203, by rfl⟩ : syracuseStep 5987209 = 4490407) B4490407
theorem B7978297 : Blo 1867635 7978297 := bstep (se 2 (by rfl) ⟨2991861, by rfl⟩ : syracuseStep 7978297 = 5983723) B5983723
theorem B43736705 : Blo 1867635 43736705 := bstep (se 2 (by rfl) ⟨16401264, by rfl⟩ : syracuseStep 43736705 = 32802529) B32802529
theorem B7978655 : Blo 1867635 7978655 := bstep (se 1 (by rfl) ⟨5983991, by rfl⟩ : syracuseStep 7978655 = 11967983) B11967983
theorem B27296189 : Blo 1867635 27296189 := bstep (se 3 (by rfl) ⟨5118035, by rfl⟩ : syracuseStep 27296189 = 10236071) B10236071
theorem B4204007 : Blo 1867635 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B1869567 : Blo 1867635 1869567 := bstep (se 1 (by rfl) ⟨1402175, by rfl⟩ : syracuseStep 1869567 = 2804351) B2804351
theorem B29157803 : Blo 1867635 29157803 := bstep (se 1 (by rfl) ⟨21868352, by rfl⟩ : syracuseStep 29157803 = 43736705) B43736705
theorem B5319103 : Blo 1867635 5319103 := bstep (se 1 (by rfl) ⟨3989327, by rfl⟩ : syracuseStep 5319103 = 7978655) B7978655
theorem B30312899 : Blo 1867635 30312899 := bstep (se 1 (by rfl) ⟨22734674, by rfl⟩ : syracuseStep 30312899 = 45469349) B45469349
theorem B145566439 : Blo 1867635 145566439 := bstep (se 1 (by rfl) ⟨109174829, by rfl⟩ : syracuseStep 145566439 = 218349659) B218349659
theorem B129494375 : Blo 1867635 129494375 := bstep (se 1 (by rfl) ⟨97120781, by rfl⟩ : syracuseStep 129494375 = 194241563) B194241563
theorem B7982945 : Blo 1867635 7982945 := bstep (se 2 (by rfl) ⟨2993604, by rfl⟩ : syracuseStep 7982945 = 5987209) B5987209
theorem B10637729 : Blo 1867635 10637729 := bstep (se 2 (by rfl) ⟨3989148, by rfl⟩ : syracuseStep 10637729 = 7978297) B7978297
theorem B24262031 : Blo 1867635 24262031 := bstep (se 1 (by rfl) ⟨18196523, by rfl⟩ : syracuseStep 24262031 = 36393047) B36393047
theorem B2102719 : Blo 1867635 2102719 := bstep (se 1 (by rfl) ⟨1577039, by rfl⟩ : syracuseStep 2102719 = 3154079) B3154079
theorem B3415039 : Blo 1867635 3415039 := bstep (se 1 (by rfl) ⟨2561279, by rfl⟩ : syracuseStep 3415039 = 5122559) B5122559
theorem B21282425 : Blo 1867635 21282425 := bstep (se 2 (by rfl) ⟨7980909, by rfl⟩ : syracuseStep 21282425 = 15961819) B15961819
theorem B2802671 : Blo 1867635 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B2803625 : Blo 1867635 2803625 := bstep (se 2 (by rfl) ⟨1051359, by rfl⟩ : syracuseStep 2803625 = 2102719) B2102719
theorem B86329583 : Blo 1867635 86329583 := bstep (se 1 (by rfl) ⟨64747187, by rfl⟩ : syracuseStep 86329583 = 129494375) B129494375
theorem B18213541 : Blo 1867635 18213541 := bstep (se 4 (by rfl) ⟨1707519, by rfl⟩ : syracuseStep 18213541 = 3415039) B3415039
theorem B18197459 : Blo 1867635 18197459 := bstep (se 1 (by rfl) ⟨13648094, by rfl⟩ : syracuseStep 18197459 = 27296189) B27296189
theorem B16174687 : Blo 1867635 16174687 := bstep (se 1 (by rfl) ⟨12131015, by rfl⟩ : syracuseStep 16174687 = 24262031) B24262031
theorem B5321963 : Blo 1867635 5321963 := bstep (se 1 (by rfl) ⟨3991472, by rfl⟩ : syracuseStep 5321963 = 7982945) B7982945
theorem B7091819 : Blo 1867635 7091819 := bstep (se 1 (by rfl) ⟨5318864, by rfl⟩ : syracuseStep 7091819 = 10637729) B10637729
theorem B7092137 : Blo 1867635 7092137 := bstep (se 2 (by rfl) ⟨2659551, by rfl⟩ : syracuseStep 7092137 = 5319103) B5319103
theorem B776354341 : Blo 1867635 776354341 := bstep (se 4 (by rfl) ⟨72783219, by rfl⟩ : syracuseStep 776354341 = 145566439) B145566439
theorem B19438535 : Blo 1867635 19438535 := bstep (se 1 (by rfl) ⟨14578901, by rfl⟩ : syracuseStep 19438535 = 29157803) B29157803
theorem B20208599 : Blo 1867635 20208599 := bstep (se 1 (by rfl) ⟨15156449, by rfl⟩ : syracuseStep 20208599 = 30312899) B30312899
theorem B14188283 : Blo 1867635 14188283 := bstep (se 1 (by rfl) ⟨10641212, by rfl⟩ : syracuseStep 14188283 = 21282425) B21282425
theorem B1868447 : Blo 1867635 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B3547975 : Blo 1867635 3547975 := bstep (se 1 (by rfl) ⟨2660981, by rfl⟩ : syracuseStep 3547975 = 5321963) B5321963
theorem B4727879 : Blo 1867635 4727879 := bstep (se 1 (by rfl) ⟨3545909, by rfl⟩ : syracuseStep 4727879 = 7091819) B7091819
theorem B4728091 : Blo 1867635 4728091 := bstep (se 1 (by rfl) ⟨3546068, by rfl⟩ : syracuseStep 4728091 = 7092137) B7092137
theorem B1869083 : Blo 1867635 1869083 := bstep (se 1 (by rfl) ⟨1401812, by rfl⟩ : syracuseStep 1869083 = 2803625) B2803625
theorem B57553055 : Blo 1867635 57553055 := bstep (se 1 (by rfl) ⟨43164791, by rfl⟩ : syracuseStep 57553055 = 86329583) B86329583
theorem B13472399 : Blo 1867635 13472399 := bstep (se 1 (by rfl) ⟨10104299, by rfl⟩ : syracuseStep 13472399 = 20208599) B20208599
theorem B21566249 : Blo 1867635 21566249 := bstep (se 2 (by rfl) ⟨8087343, by rfl⟩ : syracuseStep 21566249 = 16174687) B16174687
theorem B9458855 : Blo 1867635 9458855 := bstep (se 1 (by rfl) ⟨7094141, by rfl⟩ : syracuseStep 9458855 = 14188283) B14188283
theorem B1035139121 : Blo 1867635 1035139121 := bstep (se 2 (by rfl) ⟨388177170, by rfl⟩ : syracuseStep 1035139121 = 776354341) B776354341
theorem B97138885 : Blo 1867635 97138885 := bstep (se 4 (by rfl) ⟨9106770, by rfl⟩ : syracuseStep 97138885 = 18213541) B18213541
theorem B12959023 : Blo 1867635 12959023 := bstep (se 1 (by rfl) ⟨9719267, by rfl⟩ : syracuseStep 12959023 = 19438535) B19438535
theorem B12131639 : Blo 1867635 12131639 := bstep (se 1 (by rfl) ⟨9098729, by rfl⟩ : syracuseStep 12131639 = 18197459) B18197459
theorem B14377499 : Blo 1867635 14377499 := bstep (se 1 (by rfl) ⟨10783124, by rfl⟩ : syracuseStep 14377499 = 21566249) B21566249
theorem B17278697 : Blo 1867635 17278697 := bstep (se 2 (by rfl) ⟨6479511, by rfl⟩ : syracuseStep 17278697 = 12959023) B12959023
theorem B8087759 : Blo 1867635 8087759 := bstep (se 1 (by rfl) ⟨6065819, by rfl⟩ : syracuseStep 8087759 = 12131639) B12131639
theorem B129518513 : Blo 1867635 129518513 := bstep (se 2 (by rfl) ⟨48569442, by rfl⟩ : syracuseStep 129518513 = 97138885) B97138885
theorem B8981599 : Blo 1867635 8981599 := bstep (se 1 (by rfl) ⟨6736199, by rfl⟩ : syracuseStep 8981599 = 13472399) B13472399
theorem B4730633 : Blo 1867635 4730633 := bstep (se 2 (by rfl) ⟨1773987, by rfl⟩ : syracuseStep 4730633 = 3547975) B3547975
theorem B6304121 : Blo 1867635 6304121 := bstep (se 2 (by rfl) ⟨2364045, by rfl⟩ : syracuseStep 6304121 = 4728091) B4728091
theorem B38368703 : Blo 1867635 38368703 := bstep (se 1 (by rfl) ⟨28776527, by rfl⟩ : syracuseStep 38368703 = 57553055) B57553055
theorem B3151919 : Blo 1867635 3151919 := bstep (se 1 (by rfl) ⟨2363939, by rfl⟩ : syracuseStep 3151919 = 4727879) B4727879
theorem B6305903 : Blo 1867635 6305903 := bstep (se 1 (by rfl) ⟨4729427, by rfl⟩ : syracuseStep 6305903 = 9458855) B9458855
theorem B690092747 : Blo 1867635 690092747 := bstep (se 1 (by rfl) ⟨517569560, by rfl⟩ : syracuseStep 690092747 = 1035139121) B1035139121
theorem B4202747 : Blo 1867635 4202747 := bstep (se 1 (by rfl) ⟨3152060, by rfl⟩ : syracuseStep 4202747 = 6304121) B6304121
theorem B9584999 : Blo 1867635 9584999 := bstep (se 1 (by rfl) ⟨7188749, by rfl⟩ : syracuseStep 9584999 = 14377499) B14377499
theorem B11519131 : Blo 1867635 11519131 := bstep (se 1 (by rfl) ⟨8639348, by rfl⟩ : syracuseStep 11519131 = 17278697) B17278697
theorem B4203935 : Blo 1867635 4203935 := bstep (se 1 (by rfl) ⟨3152951, by rfl⟩ : syracuseStep 4203935 = 6305903) B6305903
theorem B5391839 : Blo 1867635 5391839 := bstep (se 1 (by rfl) ⟨4043879, by rfl⟩ : syracuseStep 5391839 = 8087759) B8087759
theorem B86345675 : Blo 1867635 86345675 := bstep (se 1 (by rfl) ⟨64759256, by rfl⟩ : syracuseStep 86345675 = 129518513) B129518513
theorem B25579135 : Blo 1867635 25579135 := bstep (se 1 (by rfl) ⟨19184351, by rfl⟩ : syracuseStep 25579135 = 38368703) B38368703
theorem B2101279 : Blo 1867635 2101279 := bstep (se 1 (by rfl) ⟨1575959, by rfl⟩ : syracuseStep 2101279 = 3151919) B3151919
theorem B11975465 : Blo 1867635 11975465 := bstep (se 2 (by rfl) ⟨4490799, by rfl⟩ : syracuseStep 11975465 = 8981599) B8981599
theorem B460061831 : Blo 1867635 460061831 := bstep (se 1 (by rfl) ⟨345046373, by rfl⟩ : syracuseStep 460061831 = 690092747) B690092747
theorem B3153755 : Blo 1867635 3153755 := bstep (se 1 (by rfl) ⟨2365316, by rfl⟩ : syracuseStep 3153755 = 4730633) B4730633
theorem B2801705 : Blo 1867635 2801705 := bstep (se 2 (by rfl) ⟨1050639, by rfl⟩ : syracuseStep 2801705 = 2101279) B2101279
theorem B2801831 : Blo 1867635 2801831 := bstep (se 1 (by rfl) ⟨2101373, by rfl⟩ : syracuseStep 2801831 = 4202747) B4202747
theorem B6389999 : Blo 1867635 6389999 := bstep (se 1 (by rfl) ⟨4792499, by rfl⟩ : syracuseStep 6389999 = 9584999) B9584999
theorem B136422053 : Blo 1867635 136422053 := bstep (se 4 (by rfl) ⟨12789567, by rfl⟩ : syracuseStep 136422053 = 25579135) B25579135
theorem B2802623 : Blo 1867635 2802623 := bstep (se 1 (by rfl) ⟨2101967, by rfl⟩ : syracuseStep 2802623 = 4203935) B4203935
theorem B31934573 : Blo 1867635 31934573 := bstep (se 3 (by rfl) ⟨5987732, by rfl⟩ : syracuseStep 31934573 = 11975465) B11975465
theorem B2102503 : Blo 1867635 2102503 := bstep (se 1 (by rfl) ⟨1576877, by rfl⟩ : syracuseStep 2102503 = 3153755) B3153755
theorem B3594559 : Blo 1867635 3594559 := bstep (se 1 (by rfl) ⟨2695919, by rfl⟩ : syracuseStep 3594559 = 5391839) B5391839
theorem B57563783 : Blo 1867635 57563783 := bstep (se 1 (by rfl) ⟨43172837, by rfl⟩ : syracuseStep 57563783 = 86345675) B86345675
theorem B15358841 : Blo 1867635 15358841 := bstep (se 2 (by rfl) ⟨5759565, by rfl⟩ : syracuseStep 15358841 = 11519131) B11519131
theorem B306707887 : Blo 1867635 306707887 := bstep (se 1 (by rfl) ⟨230030915, by rfl⟩ : syracuseStep 306707887 = 460061831) B460061831
theorem B1867803 : Blo 1867635 1867803 := bstep (se 1 (by rfl) ⟨1400852, by rfl⟩ : syracuseStep 1867803 = 2801705) B2801705
theorem B1867887 : Blo 1867635 1867887 := bstep (se 1 (by rfl) ⟨1400915, by rfl⟩ : syracuseStep 1867887 = 2801831) B2801831
theorem B4259999 : Blo 1867635 4259999 := bstep (se 1 (by rfl) ⟨3194999, by rfl⟩ : syracuseStep 4259999 = 6389999) B6389999
theorem B4792745 : Blo 1867635 4792745 := bstep (se 2 (by rfl) ⟨1797279, by rfl⟩ : syracuseStep 4792745 = 3594559) B3594559
theorem B90948035 : Blo 1867635 90948035 := bstep (se 1 (by rfl) ⟨68211026, by rfl⟩ : syracuseStep 90948035 = 136422053) B136422053
theorem B1868415 : Blo 1867635 1868415 := bstep (se 1 (by rfl) ⟨1401311, by rfl⟩ : syracuseStep 1868415 = 2802623) B2802623
theorem B2803337 : Blo 1867635 2803337 := bstep (se 2 (by rfl) ⟨1051251, by rfl⟩ : syracuseStep 2803337 = 2102503) B2102503
theorem B38375855 : Blo 1867635 38375855 := bstep (se 1 (by rfl) ⟨28781891, by rfl⟩ : syracuseStep 38375855 = 57563783) B57563783
theorem B21289715 : Blo 1867635 21289715 := bstep (se 1 (by rfl) ⟨15967286, by rfl⟩ : syracuseStep 21289715 = 31934573) B31934573
theorem B408943849 : Blo 1867635 408943849 := bstep (se 2 (by rfl) ⟨153353943, by rfl⟩ : syracuseStep 408943849 = 306707887) B306707887
theorem B10239227 : Blo 1867635 10239227 := bstep (se 1 (by rfl) ⟨7679420, by rfl⟩ : syracuseStep 10239227 = 15358841) B15358841
theorem B3195163 : Blo 1867635 3195163 := bstep (se 1 (by rfl) ⟨2396372, by rfl⟩ : syracuseStep 3195163 = 4792745) B4792745
theorem B25583903 : Blo 1867635 25583903 := bstep (se 1 (by rfl) ⟨19187927, by rfl⟩ : syracuseStep 25583903 = 38375855) B38375855
theorem B1868891 : Blo 1867635 1868891 := bstep (se 1 (by rfl) ⟨1401668, by rfl⟩ : syracuseStep 1868891 = 2803337) B2803337
theorem B6826151 : Blo 1867635 6826151 := bstep (se 1 (by rfl) ⟨5119613, by rfl⟩ : syracuseStep 6826151 = 10239227) B10239227
theorem B60632023 : Blo 1867635 60632023 := bstep (se 1 (by rfl) ⟨45474017, by rfl⟩ : syracuseStep 60632023 = 90948035) B90948035
theorem B14193143 : Blo 1867635 14193143 := bstep (se 1 (by rfl) ⟨10644857, by rfl⟩ : syracuseStep 14193143 = 21289715) B21289715
theorem B11359997 : Blo 1867635 11359997 := bstep (se 3 (by rfl) ⟨2129999, by rfl⟩ : syracuseStep 11359997 = 4259999) B4259999
theorem B545258465 : Blo 1867635 545258465 := bstep (se 2 (by rfl) ⟨204471924, by rfl⟩ : syracuseStep 545258465 = 408943849) B408943849
theorem B17055935 : Blo 1867635 17055935 := bstep (se 1 (by rfl) ⟨12791951, by rfl⟩ : syracuseStep 17055935 = 25583903) B25583903
theorem B9462095 : Blo 1867635 9462095 := bstep (se 1 (by rfl) ⟨7096571, by rfl⟩ : syracuseStep 9462095 = 14193143) B14193143
theorem B4260217 : Blo 1867635 4260217 := bstep (se 2 (by rfl) ⟨1597581, by rfl⟩ : syracuseStep 4260217 = 3195163) B3195163
theorem B18203069 : Blo 1867635 18203069 := bstep (se 3 (by rfl) ⟨3413075, by rfl⟩ : syracuseStep 18203069 = 6826151) B6826151
theorem B363505643 : Blo 1867635 363505643 := bstep (se 1 (by rfl) ⟨272629232, by rfl⟩ : syracuseStep 363505643 = 545258465) B545258465
theorem B7573331 : Blo 1867635 7573331 := bstep (se 1 (by rfl) ⟨5679998, by rfl⟩ : syracuseStep 7573331 = 11359997) B11359997
theorem B80842697 : Blo 1867635 80842697 := bstep (se 2 (by rfl) ⟨30316011, by rfl⟩ : syracuseStep 80842697 = 60632023) B60632023
theorem B11370623 : Blo 1867635 11370623 := bstep (se 1 (by rfl) ⟨8527967, by rfl⟩ : syracuseStep 11370623 = 17055935) B17055935
theorem B6308063 : Blo 1867635 6308063 := bstep (se 1 (by rfl) ⟨4731047, by rfl⟩ : syracuseStep 6308063 = 9462095) B9462095
theorem B242337095 : Blo 1867635 242337095 := bstep (se 1 (by rfl) ⟨181752821, by rfl⟩ : syracuseStep 242337095 = 363505643) B363505643
theorem B5048887 : Blo 1867635 5048887 := bstep (se 1 (by rfl) ⟨3786665, by rfl⟩ : syracuseStep 5048887 = 7573331) B7573331
theorem B12135379 : Blo 1867635 12135379 := bstep (se 1 (by rfl) ⟨9101534, by rfl⟩ : syracuseStep 12135379 = 18203069) B18203069
theorem B5680289 : Blo 1867635 5680289 := bstep (se 2 (by rfl) ⟨2130108, by rfl⟩ : syracuseStep 5680289 = 4260217) B4260217
theorem B53895131 : Blo 1867635 53895131 := bstep (se 1 (by rfl) ⟨40421348, by rfl⟩ : syracuseStep 53895131 = 80842697) B80842697
theorem B16180505 : Blo 1867635 16180505 := bstep (se 2 (by rfl) ⟨6067689, by rfl⟩ : syracuseStep 16180505 = 12135379) B12135379
theorem B3786859 : Blo 1867635 3786859 := bstep (se 1 (by rfl) ⟨2840144, by rfl⟩ : syracuseStep 3786859 = 5680289) B5680289
theorem B4205375 : Blo 1867635 4205375 := bstep (se 1 (by rfl) ⟨3154031, by rfl⟩ : syracuseStep 4205375 = 6308063) B6308063
theorem B161558063 : Blo 1867635 161558063 := bstep (se 1 (by rfl) ⟨121168547, by rfl⟩ : syracuseStep 161558063 = 242337095) B242337095
theorem B121286645 : Blo 1867635 121286645 := bstep (se 5 (by rfl) ⟨5685311, by rfl⟩ : syracuseStep 121286645 = 11370623) B11370623
theorem B6731849 : Blo 1867635 6731849 := bstep (se 2 (by rfl) ⟨2524443, by rfl⟩ : syracuseStep 6731849 = 5048887) B5048887
theorem B35930087 : Blo 1867635 35930087 := bstep (se 1 (by rfl) ⟨26947565, by rfl⟩ : syracuseStep 35930087 = 53895131) B53895131
theorem B2803583 : Blo 1867635 2803583 := bstep (se 1 (by rfl) ⟨2102687, by rfl⟩ : syracuseStep 2803583 = 4205375) B4205375
theorem B80857763 : Blo 1867635 80857763 := bstep (se 1 (by rfl) ⟨60643322, by rfl⟩ : syracuseStep 80857763 = 121286645) B121286645
theorem B5049145 : Blo 1867635 5049145 := bstep (se 2 (by rfl) ⟨1893429, by rfl⟩ : syracuseStep 5049145 = 3786859) B3786859
theorem B107705375 : Blo 1867635 107705375 := bstep (se 1 (by rfl) ⟨80779031, by rfl⟩ : syracuseStep 107705375 = 161558063) B161558063
theorem B10787003 : Blo 1867635 10787003 := bstep (se 1 (by rfl) ⟨8090252, by rfl⟩ : syracuseStep 10787003 = 16180505) B16180505
theorem B4487899 : Blo 1867635 4487899 := bstep (se 1 (by rfl) ⟨3365924, by rfl⟩ : syracuseStep 4487899 = 6731849) B6731849
theorem B23953391 : Blo 1867635 23953391 := bstep (se 1 (by rfl) ⟨17965043, by rfl⟩ : syracuseStep 23953391 = 35930087) B35930087
theorem B71803583 : Blo 1867635 71803583 := bstep (se 1 (by rfl) ⟨53852687, by rfl⟩ : syracuseStep 71803583 = 107705375) B107705375
theorem B1869055 : Blo 1867635 1869055 := bstep (se 1 (by rfl) ⟨1401791, by rfl⟩ : syracuseStep 1869055 = 2803583) B2803583
theorem B26928773 : Blo 1867635 26928773 := bstep (se 4 (by rfl) ⟨2524572, by rfl⟩ : syracuseStep 26928773 = 5049145) B5049145
theorem B53905175 : Blo 1867635 53905175 := bstep (se 1 (by rfl) ⟨40428881, by rfl⟩ : syracuseStep 53905175 = 80857763) B80857763
theorem B15968927 : Blo 1867635 15968927 := bstep (se 1 (by rfl) ⟨11976695, by rfl⟩ : syracuseStep 15968927 = 23953391) B23953391
theorem B5983865 : Blo 1867635 5983865 := bstep (se 2 (by rfl) ⟨2243949, by rfl⟩ : syracuseStep 5983865 = 4487899) B4487899
theorem B7191335 : Blo 1867635 7191335 := bstep (se 1 (by rfl) ⟨5393501, by rfl⟩ : syracuseStep 7191335 = 10787003) B10787003
theorem B4794223 : Blo 1867635 4794223 := bstep (se 1 (by rfl) ⟨3595667, by rfl⟩ : syracuseStep 4794223 = 7191335) B7191335
theorem B47869055 : Blo 1867635 47869055 := bstep (se 1 (by rfl) ⟨35901791, by rfl⟩ : syracuseStep 47869055 = 71803583) B71803583
theorem B17952515 : Blo 1867635 17952515 := bstep (se 1 (by rfl) ⟨13464386, by rfl⟩ : syracuseStep 17952515 = 26928773) B26928773
theorem B10645951 : Blo 1867635 10645951 := bstep (se 1 (by rfl) ⟨7984463, by rfl⟩ : syracuseStep 10645951 = 15968927) B15968927
theorem B35936783 : Blo 1867635 35936783 := bstep (se 1 (by rfl) ⟨26952587, by rfl⟩ : syracuseStep 35936783 = 53905175) B53905175
theorem B3989243 : Blo 1867635 3989243 := bstep (se 1 (by rfl) ⟨2991932, by rfl⟩ : syracuseStep 3989243 = 5983865) B5983865
theorem B6392297 : Blo 1867635 6392297 := bstep (se 2 (by rfl) ⟨2397111, by rfl⟩ : syracuseStep 6392297 = 4794223) B4794223
theorem B23957855 : Blo 1867635 23957855 := bstep (se 1 (by rfl) ⟨17968391, by rfl⟩ : syracuseStep 23957855 = 35936783) B35936783
theorem B31912703 : Blo 1867635 31912703 := bstep (se 1 (by rfl) ⟨23934527, by rfl⟩ : syracuseStep 31912703 = 47869055) B47869055
theorem B2659495 : Blo 1867635 2659495 := bstep (se 1 (by rfl) ⟨1994621, by rfl⟩ : syracuseStep 2659495 = 3989243) B3989243
theorem B14194601 : Blo 1867635 14194601 := bstep (se 2 (by rfl) ⟨5322975, by rfl⟩ : syracuseStep 14194601 = 10645951) B10645951
theorem B11968343 : Blo 1867635 11968343 := bstep (se 1 (by rfl) ⟨8976257, by rfl⟩ : syracuseStep 11968343 = 17952515) B17952515
theorem B21275135 : Blo 1867635 21275135 := bstep (se 1 (by rfl) ⟨15956351, by rfl⟩ : syracuseStep 21275135 = 31912703) B31912703
theorem B9463067 : Blo 1867635 9463067 := bstep (se 1 (by rfl) ⟨7097300, by rfl⟩ : syracuseStep 9463067 = 14194601) B14194601
theorem B4261531 : Blo 1867635 4261531 := bstep (se 1 (by rfl) ⟨3196148, by rfl⟩ : syracuseStep 4261531 = 6392297) B6392297
theorem B15971903 : Blo 1867635 15971903 := bstep (se 1 (by rfl) ⟨11978927, by rfl⟩ : syracuseStep 15971903 = 23957855) B23957855
theorem B3545993 : Blo 1867635 3545993 := bstep (se 2 (by rfl) ⟨1329747, by rfl⟩ : syracuseStep 3545993 = 2659495) B2659495
theorem B7978895 : Blo 1867635 7978895 := bstep (se 1 (by rfl) ⟨5984171, by rfl⟩ : syracuseStep 7978895 = 11968343) B11968343
theorem B6308711 : Blo 1867635 6308711 := bstep (se 1 (by rfl) ⟨4731533, by rfl⟩ : syracuseStep 6308711 = 9463067) B9463067
theorem B5319263 : Blo 1867635 5319263 := bstep (se 1 (by rfl) ⟨3989447, by rfl⟩ : syracuseStep 5319263 = 7978895) B7978895
theorem B14183423 : Blo 1867635 14183423 := bstep (se 1 (by rfl) ⟨10637567, by rfl⟩ : syracuseStep 14183423 = 21275135) B21275135
theorem B2363995 : Blo 1867635 2363995 := bstep (se 1 (by rfl) ⟨1772996, by rfl⟩ : syracuseStep 2363995 = 3545993) B3545993
theorem B5682041 : Blo 1867635 5682041 := bstep (se 2 (by rfl) ⟨2130765, by rfl⟩ : syracuseStep 5682041 = 4261531) B4261531
theorem B10647935 : Blo 1867635 10647935 := bstep (se 1 (by rfl) ⟨7985951, by rfl⟩ : syracuseStep 10647935 = 15971903) B15971903
theorem B9455615 : Blo 1867635 9455615 := bstep (se 1 (by rfl) ⟨7091711, by rfl⟩ : syracuseStep 9455615 = 14183423) B14183423
theorem B4205807 : Blo 1867635 4205807 := bstep (se 1 (by rfl) ⟨3154355, by rfl⟩ : syracuseStep 4205807 = 6308711) B6308711
theorem B3788027 : Blo 1867635 3788027 := bstep (se 1 (by rfl) ⟨2841020, by rfl⟩ : syracuseStep 3788027 = 5682041) B5682041
theorem B7098623 : Blo 1867635 7098623 := bstep (se 1 (by rfl) ⟨5323967, by rfl⟩ : syracuseStep 7098623 = 10647935) B10647935
theorem B3151993 : Blo 1867635 3151993 := bstep (se 2 (by rfl) ⟨1181997, by rfl⟩ : syracuseStep 3151993 = 2363995) B2363995
theorem B3546175 : Blo 1867635 3546175 := bstep (se 1 (by rfl) ⟨2659631, by rfl⟩ : syracuseStep 3546175 = 5319263) B5319263
theorem B4202657 : Blo 1867635 4202657 := bstep (se 2 (by rfl) ⟨1575996, by rfl⟩ : syracuseStep 4202657 = 3151993) B3151993
theorem B4728233 : Blo 1867635 4728233 := bstep (se 2 (by rfl) ⟨1773087, by rfl⟩ : syracuseStep 4728233 = 3546175) B3546175
theorem B2803871 : Blo 1867635 2803871 := bstep (se 1 (by rfl) ⟨2102903, by rfl⟩ : syracuseStep 2803871 = 4205807) B4205807
theorem B2525351 : Blo 1867635 2525351 := bstep (se 1 (by rfl) ⟨1894013, by rfl⟩ : syracuseStep 2525351 = 3788027) B3788027
theorem B6303743 : Blo 1867635 6303743 := bstep (se 1 (by rfl) ⟨4727807, by rfl⟩ : syracuseStep 6303743 = 9455615) B9455615
theorem B4732415 : Blo 1867635 4732415 := bstep (se 1 (by rfl) ⟨3549311, by rfl⟩ : syracuseStep 4732415 = 7098623) B7098623
theorem B2801771 : Blo 1867635 2801771 := bstep (se 1 (by rfl) ⟨2101328, by rfl⟩ : syracuseStep 2801771 = 4202657) B4202657
theorem B6734269 : Blo 1867635 6734269 := bstep (se 3 (by rfl) ⟨1262675, by rfl⟩ : syracuseStep 6734269 = 2525351) B2525351
theorem B3154943 : Blo 1867635 3154943 := bstep (se 1 (by rfl) ⟨2366207, by rfl⟩ : syracuseStep 3154943 = 4732415) B4732415
theorem B1869247 : Blo 1867635 1869247 := bstep (se 1 (by rfl) ⟨1401935, by rfl⟩ : syracuseStep 1869247 = 2803871) B2803871
theorem B3152155 : Blo 1867635 3152155 := bstep (se 1 (by rfl) ⟨2364116, by rfl⟩ : syracuseStep 3152155 = 4728233) B4728233
theorem B4202495 : Blo 1867635 4202495 := bstep (se 1 (by rfl) ⟨3151871, by rfl⟩ : syracuseStep 4202495 = 6303743) B6303743
theorem B1867847 : Blo 1867635 1867847 := bstep (se 1 (by rfl) ⟨1400885, by rfl⟩ : syracuseStep 1867847 = 2801771) B2801771
theorem B4202873 : Blo 1867635 4202873 := bstep (se 2 (by rfl) ⟨1576077, by rfl⟩ : syracuseStep 4202873 = 3152155) B3152155
theorem B8979025 : Blo 1867635 8979025 := bstep (se 2 (by rfl) ⟨3367134, by rfl⟩ : syracuseStep 8979025 = 6734269) B6734269
theorem B2801663 : Blo 1867635 2801663 := bstep (se 1 (by rfl) ⟨2101247, by rfl⟩ : syracuseStep 2801663 = 4202495) B4202495
theorem B2103295 : Blo 1867635 2103295 := bstep (se 1 (by rfl) ⟨1577471, by rfl⟩ : syracuseStep 2103295 = 3154943) B3154943
theorem B2801915 : Blo 1867635 2801915 := bstep (se 1 (by rfl) ⟨2101436, by rfl⟩ : syracuseStep 2801915 = 4202873) B4202873
theorem B1867775 : Blo 1867635 1867775 := bstep (se 1 (by rfl) ⟨1400831, by rfl⟩ : syracuseStep 1867775 = 2801663) B2801663
theorem B2804393 : Blo 1867635 2804393 := bstep (se 2 (by rfl) ⟨1051647, by rfl⟩ : syracuseStep 2804393 = 2103295) B2103295
theorem B11972033 : Blo 1867635 11972033 := bstep (se 2 (by rfl) ⟨4489512, by rfl⟩ : syracuseStep 11972033 = 8979025) B8979025
theorem B1867943 : Blo 1867635 1867943 := bstep (se 1 (by rfl) ⟨1400957, by rfl⟩ : syracuseStep 1867943 = 2801915) B2801915
theorem B1869595 : Blo 1867635 1869595 := bstep (se 1 (by rfl) ⟨1402196, by rfl⟩ : syracuseStep 1869595 = 2804393) B2804393
theorem B7981355 : Blo 1867635 7981355 := bstep (se 1 (by rfl) ⟨5986016, by rfl⟩ : syracuseStep 7981355 = 11972033) B11972033
theorem B5320903 : Blo 1867635 5320903 := bstep (se 1 (by rfl) ⟨3990677, by rfl⟩ : syracuseStep 5320903 = 7981355) B7981355
theorem B7094537 : Blo 1867635 7094537 := bstep (se 2 (by rfl) ⟨2660451, by rfl⟩ : syracuseStep 7094537 = 5320903) B5320903
theorem B4729691 : Blo 1867635 4729691 := bstep (se 1 (by rfl) ⟨3547268, by rfl⟩ : syracuseStep 4729691 = 7094537) B7094537
theorem B3153127 : Blo 1867635 3153127 := bstep (se 1 (by rfl) ⟨2364845, by rfl⟩ : syracuseStep 3153127 = 4729691) B4729691
theorem B4204169 : Blo 1867635 4204169 := bstep (se 2 (by rfl) ⟨1576563, by rfl⟩ : syracuseStep 4204169 = 3153127) B3153127
theorem B2802779 : Blo 1867635 2802779 := bstep (se 1 (by rfl) ⟨2102084, by rfl⟩ : syracuseStep 2802779 = 4204169) B4204169
theorem B1868519 : Blo 1867635 1868519 := bstep (se 1 (by rfl) ⟨1401389, by rfl⟩ : syracuseStep 1868519 = 2802779) B2802779

theorem C0 (j : ℕ) (h1 : 466908 ≤ j) (h2 : j ≤ 467408) : Blo 1867635 (4 * j + 3) := by
  interval_cases j
  · exact B1867635
  · exact B1867639
  · exact B1867643
  · exact B1867647
  · exact B1867651
  · exact B1867655
  · exact B1867659
  · exact B1867663
  · exact B1867667
  · exact B1867671
  · exact B1867675
  · exact B1867679
  · exact B1867683
  · exact B1867687
  · exact B1867691
  · exact B1867695
  · exact B1867699
  · exact B1867703
  · exact B1867707
  · exact B1867711
  · exact B1867715
  · exact B1867719
  · exact B1867723
  · exact B1867727
  · exact B1867731
  · exact B1867735
  · exact B1867739
  · exact B1867743
  · exact B1867747
  · exact B1867751
  · exact B1867755
  · exact B1867759
  · exact B1867763
  · exact B1867767
  · exact B1867771
  · exact B1867775
  · exact B1867779
  · exact B1867783
  · exact B1867787
  · exact B1867791
  · exact B1867795
  · exact B1867799
  · exact B1867803
  · exact B1867807
  · exact B1867811
  · exact B1867815
  · exact B1867819
  · exact B1867823
  · exact B1867827
  · exact B1867831
  · exact B1867835
  · exact B1867839
  · exact B1867843
  · exact B1867847
  · exact B1867851
  · exact B1867855
  · exact B1867859
  · exact B1867863
  · exact B1867867
  · exact B1867871
  · exact B1867875
  · exact B1867879
  · exact B1867883
  · exact B1867887
  · exact B1867891
  · exact B1867895
  · exact B1867899
  · exact B1867903
  · exact B1867907
  · exact B1867911
  · exact B1867915
  · exact B1867919
  · exact B1867923
  · exact B1867927
  · exact B1867931
  · exact B1867935
  · exact B1867939
  · exact B1867943
  · exact B1867947
  · exact B1867951
  · exact B1867955
  · exact B1867959
  · exact B1867963
  · exact B1867967
  · exact B1867971
  · exact B1867975
  · exact B1867979
  · exact B1867983
  · exact B1867987
  · exact B1867991
  · exact B1867995
  · exact B1867999
  · exact B1868003
  · exact B1868007
  · exact B1868011
  · exact B1868015
  · exact B1868019
  · exact B1868023
  · exact B1868027
  · exact B1868031
  · exact B1868035
  · exact B1868039
  · exact B1868043
  · exact B1868047
  · exact B1868051
  · exact B1868055
  · exact B1868059
  · exact B1868063
  · exact B1868067
  · exact B1868071
  · exact B1868075
  · exact B1868079
  · exact B1868083
  · exact B1868087
  · exact B1868091
  · exact B1868095
  · exact B1868099
  · exact B1868103
  · exact B1868107
  · exact B1868111
  · exact B1868115
  · exact B1868119
  · exact B1868123
  · exact B1868127
  · exact B1868131
  · exact B1868135
  · exact B1868139
  · exact B1868143
  · exact B1868147
  · exact B1868151
  · exact B1868155
  · exact B1868159
  · exact B1868163
  · exact B1868167
  · exact B1868171
  · exact B1868175
  · exact B1868179
  · exact B1868183
  · exact B1868187
  · exact B1868191
  · exact B1868195
  · exact B1868199
  · exact B1868203
  · exact B1868207
  · exact B1868211
  · exact B1868215
  · exact B1868219
  · exact B1868223
  · exact B1868227
  · exact B1868231
  · exact B1868235
  · exact B1868239
  · exact B1868243
  · exact B1868247
  · exact B1868251
  · exact B1868255
  · exact B1868259
  · exact B1868263
  · exact B1868267
  · exact B1868271
  · exact B1868275
  · exact B1868279
  · exact B1868283
  · exact B1868287
  · exact B1868291
  · exact B1868295
  · exact B1868299
  · exact B1868303
  · exact B1868307
  · exact B1868311
  · exact B1868315
  · exact B1868319
  · exact B1868323
  · exact B1868327
  · exact B1868331
  · exact B1868335
  · exact B1868339
  · exact B1868343
  · exact B1868347
  · exact B1868351
  · exact B1868355
  · exact B1868359
  · exact B1868363
  · exact B1868367
  · exact B1868371
  · exact B1868375
  · exact B1868379
  · exact B1868383
  · exact B1868387
  · exact B1868391
  · exact B1868395
  · exact B1868399
  · exact B1868403
  · exact B1868407
  · exact B1868411
  · exact B1868415
  · exact B1868419
  · exact B1868423
  · exact B1868427
  · exact B1868431
  · exact B1868435
  · exact B1868439
  · exact B1868443
  · exact B1868447
  · exact B1868451
  · exact B1868455
  · exact B1868459
  · exact B1868463
  · exact B1868467
  · exact B1868471
  · exact B1868475
  · exact B1868479
  · exact B1868483
  · exact B1868487
  · exact B1868491
  · exact B1868495
  · exact B1868499
  · exact B1868503
  · exact B1868507
  · exact B1868511
  · exact B1868515
  · exact B1868519
  · exact B1868523
  · exact B1868527
  · exact B1868531
  · exact B1868535
  · exact B1868539
  · exact B1868543
  · exact B1868547
  · exact B1868551
  · exact B1868555
  · exact B1868559
  · exact B1868563
  · exact B1868567
  · exact B1868571
  · exact B1868575
  · exact B1868579
  · exact B1868583
  · exact B1868587
  · exact B1868591
  · exact B1868595
  · exact B1868599
  · exact B1868603
  · exact B1868607
  · exact B1868611
  · exact B1868615
  · exact B1868619
  · exact B1868623
  · exact B1868627
  · exact B1868631
  · exact B1868635
  · exact B1868639
  · exact B1868643
  · exact B1868647
  · exact B1868651
  · exact B1868655
  · exact B1868659
  · exact B1868663
  · exact B1868667
  · exact B1868671
  · exact B1868675
  · exact B1868679
  · exact B1868683
  · exact B1868687
  · exact B1868691
  · exact B1868695
  · exact B1868699
  · exact B1868703
  · exact B1868707
  · exact B1868711
  · exact B1868715
  · exact B1868719
  · exact B1868723
  · exact B1868727
  · exact B1868731
  · exact B1868735
  · exact B1868739
  · exact B1868743
  · exact B1868747
  · exact B1868751
  · exact B1868755
  · exact B1868759
  · exact B1868763
  · exact B1868767
  · exact B1868771
  · exact B1868775
  · exact B1868779
  · exact B1868783
  · exact B1868787
  · exact B1868791
  · exact B1868795
  · exact B1868799
  · exact B1868803
  · exact B1868807
  · exact B1868811
  · exact B1868815
  · exact B1868819
  · exact B1868823
  · exact B1868827
  · exact B1868831
  · exact B1868835
  · exact B1868839
  · exact B1868843
  · exact B1868847
  · exact B1868851
  · exact B1868855
  · exact B1868859
  · exact B1868863
  · exact B1868867
  · exact B1868871
  · exact B1868875
  · exact B1868879
  · exact B1868883
  · exact B1868887
  · exact B1868891
  · exact B1868895
  · exact B1868899
  · exact B1868903
  · exact B1868907
  · exact B1868911
  · exact B1868915
  · exact B1868919
  · exact B1868923
  · exact B1868927
  · exact B1868931
  · exact B1868935
  · exact B1868939
  · exact B1868943
  · exact B1868947
  · exact B1868951
  · exact B1868955
  · exact B1868959
  · exact B1868963
  · exact B1868967
  · exact B1868971
  · exact B1868975
  · exact B1868979
  · exact B1868983
  · exact B1868987
  · exact B1868991
  · exact B1868995
  · exact B1868999
  · exact B1869003
  · exact B1869007
  · exact B1869011
  · exact B1869015
  · exact B1869019
  · exact B1869023
  · exact B1869027
  · exact B1869031
  · exact B1869035
  · exact B1869039
  · exact B1869043
  · exact B1869047
  · exact B1869051
  · exact B1869055
  · exact B1869059
  · exact B1869063
  · exact B1869067
  · exact B1869071
  · exact B1869075
  · exact B1869079
  · exact B1869083
  · exact B1869087
  · exact B1869091
  · exact B1869095
  · exact B1869099
  · exact B1869103
  · exact B1869107
  · exact B1869111
  · exact B1869115
  · exact B1869119
  · exact B1869123
  · exact B1869127
  · exact B1869131
  · exact B1869135
  · exact B1869139
  · exact B1869143
  · exact B1869147
  · exact B1869151
  · exact B1869155
  · exact B1869159
  · exact B1869163
  · exact B1869167
  · exact B1869171
  · exact B1869175
  · exact B1869179
  · exact B1869183
  · exact B1869187
  · exact B1869191
  · exact B1869195
  · exact B1869199
  · exact B1869203
  · exact B1869207
  · exact B1869211
  · exact B1869215
  · exact B1869219
  · exact B1869223
  · exact B1869227
  · exact B1869231
  · exact B1869235
  · exact B1869239
  · exact B1869243
  · exact B1869247
  · exact B1869251
  · exact B1869255
  · exact B1869259
  · exact B1869263
  · exact B1869267
  · exact B1869271
  · exact B1869275
  · exact B1869279
  · exact B1869283
  · exact B1869287
  · exact B1869291
  · exact B1869295
  · exact B1869299
  · exact B1869303
  · exact B1869307
  · exact B1869311
  · exact B1869315
  · exact B1869319
  · exact B1869323
  · exact B1869327
  · exact B1869331
  · exact B1869335
  · exact B1869339
  · exact B1869343
  · exact B1869347
  · exact B1869351
  · exact B1869355
  · exact B1869359
  · exact B1869363
  · exact B1869367
  · exact B1869371
  · exact B1869375
  · exact B1869379
  · exact B1869383
  · exact B1869387
  · exact B1869391
  · exact B1869395
  · exact B1869399
  · exact B1869403
  · exact B1869407
  · exact B1869411
  · exact B1869415
  · exact B1869419
  · exact B1869423
  · exact B1869427
  · exact B1869431
  · exact B1869435
  · exact B1869439
  · exact B1869443
  · exact B1869447
  · exact B1869451
  · exact B1869455
  · exact B1869459
  · exact B1869463
  · exact B1869467
  · exact B1869471
  · exact B1869475
  · exact B1869479
  · exact B1869483
  · exact B1869487
  · exact B1869491
  · exact B1869495
  · exact B1869499
  · exact B1869503
  · exact B1869507
  · exact B1869511
  · exact B1869515
  · exact B1869519
  · exact B1869523
  · exact B1869527
  · exact B1869531
  · exact B1869535
  · exact B1869539
  · exact B1869543
  · exact B1869547
  · exact B1869551
  · exact B1869555
  · exact B1869559
  · exact B1869563
  · exact B1869567
  · exact B1869571
  · exact B1869575
  · exact B1869579
  · exact B1869583
  · exact B1869587
  · exact B1869591
  · exact B1869595
  · exact B1869599
  · exact B1869603
  · exact B1869607
  · exact B1869611
  · exact B1869615
  · exact B1869619
  · exact B1869623
  · exact B1869627
  · exact B1869631
  · exact B1869635

theorem solution (m : ℕ) (hlo : 1867635 ≤ m) (hhi : m ≤ 1869635) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 466908 ≤ j := by omega
    have hj2 : j ≤ 467408 := by omega
    have hb : Blo 1867635 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
