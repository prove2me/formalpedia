-- Prove2me | solution 1 for syracuse_descends_range_1522458_1524458
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:29.525698+00:00
-- url     : https://prove2.me/submissions/166a42f8-f258-4229-b7c2-64fd73cd7989

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


theorem B2285573 : Blo 1522458 2285573 := bbase (se 4 (by rfl) ⟨214272, by rfl⟩ : syracuseStep 2285573 = 428545) (by norm_num)
theorem B7716869 : Blo 1522458 7716869 := bbase (se 4 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 7716869 = 1446913) (by norm_num)
theorem B2285597 : Blo 1522458 2285597 := bbase (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) (by norm_num)
theorem B5865509 : Blo 1522458 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B2285621 : Blo 1522458 2285621 := bbase (se 5 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 2285621 = 214277) (by norm_num)
theorem B2441269 : Blo 1522458 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B2891837 : Blo 1522458 2891837 := bbase (se 3 (by rfl) ⟨542219, by rfl⟩ : syracuseStep 2891837 = 1084439) (by norm_num)
theorem B2744389 : Blo 1522458 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B2572357 : Blo 1522458 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B2285645 : Blo 1522458 2285645 := bbase (se 3 (by rfl) ⟨428558, by rfl⟩ : syracuseStep 2285645 = 857117) (by norm_num)
theorem B6504533 : Blo 1522458 6504533 := bbase (se 8 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 6504533 = 76225) (by norm_num)
theorem B2285669 : Blo 1522458 2285669 := bbase (se 4 (by rfl) ⟨214281, by rfl⟩ : syracuseStep 2285669 = 428563) (by norm_num)
theorem B2285693 : Blo 1522458 2285693 := bbase (se 3 (by rfl) ⟨428567, by rfl⟩ : syracuseStep 2285693 = 857135) (by norm_num)
theorem B2285717 : Blo 1522458 2285717 := bbase (se 6 (by rfl) ⟨53571, by rfl⟩ : syracuseStep 2285717 = 107143) (by norm_num)
theorem B2572445 : Blo 1522458 2572445 := bbase (se 3 (by rfl) ⟨482333, by rfl⟩ : syracuseStep 2572445 = 964667) (by norm_num)
theorem B5144741 : Blo 1522458 5144741 := bbase (se 4 (by rfl) ⟨482319, by rfl⟩ : syracuseStep 5144741 = 964639) (by norm_num)
theorem B2285741 : Blo 1522458 2285741 := bbase (se 3 (by rfl) ⟨428576, by rfl⟩ : syracuseStep 2285741 = 857153) (by norm_num)
theorem B11567285 : Blo 1522458 11567285 := bbase (se 5 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 11567285 = 1084433) (by norm_num)
theorem B2285765 : Blo 1522458 2285765 := bbase (se 4 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 2285765 = 428581) (by norm_num)
theorem B3858637 : Blo 1522458 3858637 := bbase (se 3 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 3858637 = 1446989) (by norm_num)
theorem B2285789 : Blo 1522458 2285789 := bbase (se 3 (by rfl) ⟨428585, by rfl⟩ : syracuseStep 2285789 = 857171) (by norm_num)
theorem B6947045 : Blo 1522458 6947045 := bbase (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) (by norm_num)
theorem B2285813 : Blo 1522458 2285813 := bbase (se 5 (by rfl) ⟨107147, by rfl⟩ : syracuseStep 2285813 = 214295) (by norm_num)
theorem B2285837 : Blo 1522458 2285837 := bbase (se 3 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 2285837 = 857189) (by norm_num)
theorem B2285861 : Blo 1522458 2285861 := bbase (se 4 (by rfl) ⟨214299, by rfl⟩ : syracuseStep 2285861 = 428599) (by norm_num)
theorem B2285885 : Blo 1522458 2285885 := bbase (se 3 (by rfl) ⟨428603, by rfl⟩ : syracuseStep 2285885 = 857207) (by norm_num)
theorem B3858749 : Blo 1522458 3858749 := bbase (se 3 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 3858749 = 1447031) (by norm_num)
theorem B3473741 : Blo 1522458 3473741 := bbase (se 3 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 3473741 = 1302653) (by norm_num)
theorem B3252565 : Blo 1522458 3252565 := bbase (se 10 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 3252565 = 9529) (by norm_num)
theorem B2285909 : Blo 1522458 2285909 := bbase (se 10 (by rfl) ⟨3348, by rfl⟩ : syracuseStep 2285909 = 6697) (by norm_num)
theorem B2892125 : Blo 1522458 2892125 := bbase (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) (by norm_num)
theorem B2285933 : Blo 1522458 2285933 := bbase (se 3 (by rfl) ⟨428612, by rfl⟩ : syracuseStep 2285933 = 857225) (by norm_num)
theorem B2285957 : Blo 1522458 2285957 := bbase (se 4 (by rfl) ⟨214308, by rfl⟩ : syracuseStep 2285957 = 428617) (by norm_num)
theorem B3473813 : Blo 1522458 3473813 := bbase (se 6 (by rfl) ⟨81417, by rfl⟩ : syracuseStep 3473813 = 162835) (by norm_num)
theorem B2285981 : Blo 1522458 2285981 := bbase (se 3 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 2285981 = 857243) (by norm_num)
theorem B7709093 : Blo 1522458 7709093 := bbase (se 4 (by rfl) ⟨722727, by rfl⟩ : syracuseStep 7709093 = 1445455) (by norm_num)
theorem B2286005 : Blo 1522458 2286005 := bbase (se 5 (by rfl) ⟨107156, by rfl⟩ : syracuseStep 2286005 = 214313) (by norm_num)
theorem B2286029 : Blo 1522458 2286029 := bbase (se 3 (by rfl) ⟨428630, by rfl⟩ : syracuseStep 2286029 = 857261) (by norm_num)
theorem B2286053 : Blo 1522458 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B2892277 : Blo 1522458 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B3523061 : Blo 1522458 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B2286077 : Blo 1522458 2286077 := bbase (se 3 (by rfl) ⟨428639, by rfl⟩ : syracuseStep 2286077 = 857279) (by norm_num)
theorem B4882949 : Blo 1522458 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B6595093 : Blo 1522458 6595093 := bbase (se 6 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 6595093 = 309145) (by norm_num)
theorem B2286101 : Blo 1522458 2286101 := bbase (se 6 (by rfl) ⟨53580, by rfl⟩ : syracuseStep 2286101 = 107161) (by norm_num)
theorem B2286125 : Blo 1522458 2286125 := bbase (se 3 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 2286125 = 857297) (by norm_num)
theorem B2286149 : Blo 1522458 2286149 := bbase (se 4 (by rfl) ⟨214326, by rfl⟩ : syracuseStep 2286149 = 428653) (by norm_num)
theorem B7324229 : Blo 1522458 7324229 := bbase (se 4 (by rfl) ⟨686646, by rfl⟩ : syracuseStep 7324229 = 1373293) (by norm_num)
theorem B4399685 : Blo 1522458 4399685 := bbase (se 4 (by rfl) ⟨412470, by rfl⟩ : syracuseStep 4399685 = 824941) (by norm_num)
theorem B21955157 : Blo 1522458 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B2286173 : Blo 1522458 2286173 := bbase (se 3 (by rfl) ⟨428657, by rfl⟩ : syracuseStep 2286173 = 857315) (by norm_num)
theorem B2286197 : Blo 1522458 2286197 := bbase (se 5 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 2286197 = 214331) (by norm_num)
theorem B2286221 : Blo 1522458 2286221 := bbase (se 3 (by rfl) ⟨428666, by rfl⟩ : syracuseStep 2286221 = 857333) (by norm_num)
theorem B1712785 : Blo 1522458 1712785 := bbase (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) (by norm_num)
theorem B2286245 : Blo 1522458 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B1712821 : Blo 1522458 1712821 := bbase (se 5 (by rfl) ⟨80288, by rfl⟩ : syracuseStep 1712821 = 160577) (by norm_num)
theorem B2286269 : Blo 1522458 2286269 := bbase (se 3 (by rfl) ⟨428675, by rfl⟩ : syracuseStep 2286269 = 857351) (by norm_num)
theorem B2286293 : Blo 1522458 2286293 := bbase (se 7 (by rfl) ⟨26792, by rfl⟩ : syracuseStep 2286293 = 53585) (by norm_num)
theorem B1712857 : Blo 1522458 1712857 := bbase (se 2 (by rfl) ⟨642321, by rfl⟩ : syracuseStep 1712857 = 1284643) (by norm_num)
theorem B1762009 : Blo 1522458 1762009 := bbase (se 2 (by rfl) ⟨660753, by rfl⟩ : syracuseStep 1762009 = 1321507) (by norm_num)
theorem B7045861 : Blo 1522458 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B2286317 : Blo 1522458 2286317 := bbase (se 3 (by rfl) ⟨428684, by rfl⟩ : syracuseStep 2286317 = 857369) (by norm_num)
theorem B1712893 : Blo 1522458 1712893 := bbase (se 3 (by rfl) ⟨321167, by rfl⟩ : syracuseStep 1712893 = 642335) (by norm_num)
theorem B2286341 : Blo 1522458 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B2286365 : Blo 1522458 2286365 := bbase (se 3 (by rfl) ⟨428693, by rfl⟩ : syracuseStep 2286365 = 857387) (by norm_num)
theorem B1712929 : Blo 1522458 1712929 := bbase (se 2 (by rfl) ⟨642348, by rfl⟩ : syracuseStep 1712929 = 1284697) (by norm_num)
theorem B2892581 : Blo 1522458 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B3089189 : Blo 1522458 3089189 := bbase (se 4 (by rfl) ⟨289611, by rfl⟩ : syracuseStep 3089189 = 579223) (by norm_num)
theorem B2286389 : Blo 1522458 2286389 := bbase (se 5 (by rfl) ⟨107174, by rfl⟩ : syracuseStep 2286389 = 214349) (by norm_num)
theorem B3662653 : Blo 1522458 3662653 := bbase (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) (by norm_num)
theorem B1712965 : Blo 1522458 1712965 := bbase (se 4 (by rfl) ⟨160590, by rfl⟩ : syracuseStep 1712965 = 321181) (by norm_num)
theorem B3253061 : Blo 1522458 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B2286413 : Blo 1522458 2286413 := bbase (se 3 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 2286413 = 857405) (by norm_num)
theorem B2286437 : Blo 1522458 2286437 := bbase (se 4 (by rfl) ⟨214353, by rfl⟩ : syracuseStep 2286437 = 428707) (by norm_num)
theorem B1713001 : Blo 1522458 1713001 := bbase (se 2 (by rfl) ⟨642375, by rfl⟩ : syracuseStep 1713001 = 1284751) (by norm_num)
theorem B2286461 : Blo 1522458 2286461 := bbase (se 3 (by rfl) ⟨428711, by rfl⟩ : syracuseStep 2286461 = 857423) (by norm_num)
theorem B1713037 : Blo 1522458 1713037 := bbase (se 3 (by rfl) ⟨321194, by rfl⟩ : syracuseStep 1713037 = 642389) (by norm_num)
theorem B28173205 : Blo 1522458 28173205 := bbase (se 6 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 28173205 = 1320619) (by norm_num)
theorem B2286485 : Blo 1522458 2286485 := bbase (se 6 (by rfl) ⟨53589, by rfl⟩ : syracuseStep 2286485 = 107179) (by norm_num)
theorem B2286509 : Blo 1522458 2286509 := bbase (se 3 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 2286509 = 857441) (by norm_num)
theorem B1713073 : Blo 1522458 1713073 := bbase (se 2 (by rfl) ⟨642402, by rfl⟩ : syracuseStep 1713073 = 1284805) (by norm_num)
theorem B2286533 : Blo 1522458 2286533 := bbase (se 4 (by rfl) ⟨214362, by rfl⟩ : syracuseStep 2286533 = 428725) (by norm_num)
theorem B1713109 : Blo 1522458 1713109 := bbase (se 7 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 1713109 = 40151) (by norm_num)
theorem B9765845 : Blo 1522458 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B3474397 : Blo 1522458 3474397 := bbase (se 3 (by rfl) ⟨651449, by rfl⟩ : syracuseStep 3474397 = 1302899) (by norm_num)
theorem B2286557 : Blo 1522458 2286557 := bbase (se 3 (by rfl) ⟨428729, by rfl⟩ : syracuseStep 2286557 = 857459) (by norm_num)
theorem B2286581 : Blo 1522458 2286581 := bbase (se 5 (by rfl) ⟨107183, by rfl⟩ : syracuseStep 2286581 = 214367) (by norm_num)
theorem B1713145 : Blo 1522458 1713145 := bbase (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) (by norm_num)
theorem B2286605 : Blo 1522458 2286605 := bbase (se 3 (by rfl) ⟨428738, by rfl⟩ : syracuseStep 2286605 = 857477) (by norm_num)
theorem B1713181 : Blo 1522458 1713181 := bbase (se 3 (by rfl) ⟨321221, by rfl⟩ : syracuseStep 1713181 = 642443) (by norm_num)
theorem B2286629 : Blo 1522458 2286629 := bbase (se 4 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 2286629 = 428743) (by norm_num)
theorem B2286653 : Blo 1522458 2286653 := bbase (se 3 (by rfl) ⟨428747, by rfl⟩ : syracuseStep 2286653 = 857495) (by norm_num)
theorem B1713217 : Blo 1522458 1713217 := bbase (se 2 (by rfl) ⟨642456, by rfl⟩ : syracuseStep 1713217 = 1284913) (by norm_num)
theorem B6505541 : Blo 1522458 6505541 := bbase (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) (by norm_num)
theorem B2286677 : Blo 1522458 2286677 := bbase (se 8 (by rfl) ⟨13398, by rfl⟩ : syracuseStep 2286677 = 26797) (by norm_num)
theorem B1713253 : Blo 1522458 1713253 := bbase (se 4 (by rfl) ⟨160617, by rfl⟩ : syracuseStep 1713253 = 321235) (by norm_num)
theorem B1713289 : Blo 1522458 1713289 := bbase (se 2 (by rfl) ⟨642483, by rfl⟩ : syracuseStep 1713289 = 1284967) (by norm_num)
theorem B2745485 : Blo 1522458 2745485 := bbase (se 3 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 2745485 = 1029557) (by norm_num)
theorem B6177941 : Blo 1522458 6177941 := bbase (se 6 (by rfl) ⟨144795, by rfl⟩ : syracuseStep 6177941 = 289591) (by norm_num)
theorem B1713325 : Blo 1522458 1713325 := bbase (se 3 (by rfl) ⟨321248, by rfl⟩ : syracuseStep 1713325 = 642497) (by norm_num)
theorem B1713361 : Blo 1522458 1713361 := bbase (se 2 (by rfl) ⟨642510, by rfl⟩ : syracuseStep 1713361 = 1285021) (by norm_num)
theorem B12354773 : Blo 1522458 12354773 := bbase (se 7 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 12354773 = 289565) (by norm_num)
theorem B1713397 : Blo 1522458 1713397 := bbase (se 5 (by rfl) ⟨80315, by rfl⟩ : syracuseStep 1713397 = 160631) (by norm_num)
theorem B1713433 : Blo 1522458 1713433 := bbase (se 2 (by rfl) ⟨642537, by rfl⟩ : syracuseStep 1713433 = 1285075) (by norm_num)
theorem B3425597 : Blo 1522458 3425597 := bbase (se 3 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 3425597 = 1284599) (by norm_num)
theorem B1713469 : Blo 1522458 1713469 := bbase (se 3 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 1713469 = 642551) (by norm_num)
theorem B6178133 : Blo 1522458 6178133 := bbase (se 12 (by rfl) ⟨2262, by rfl⟩ : syracuseStep 6178133 = 4525) (by norm_num)
theorem B1713505 : Blo 1522458 1713505 := bbase (se 2 (by rfl) ⟨642564, by rfl⟩ : syracuseStep 1713505 = 1285129) (by norm_num)
theorem B3425669 : Blo 1522458 3425669 := bbase (se 4 (by rfl) ⟨321156, by rfl⟩ : syracuseStep 3425669 = 642313) (by norm_num)
theorem B1713541 : Blo 1522458 1713541 := bbase (se 4 (by rfl) ⟨160644, by rfl⟩ : syracuseStep 1713541 = 321289) (by norm_num)
theorem B5784965 : Blo 1522458 5784965 := bbase (se 4 (by rfl) ⟨542340, by rfl⟩ : syracuseStep 5784965 = 1084681) (by norm_num)
theorem B1713577 : Blo 1522458 1713577 := bbase (se 2 (by rfl) ⟨642591, by rfl⟩ : syracuseStep 1713577 = 1285183) (by norm_num)
theorem B3425741 : Blo 1522458 3425741 := bbase (se 3 (by rfl) ⟨642326, by rfl⟩ : syracuseStep 3425741 = 1284653) (by norm_num)
theorem B1713613 : Blo 1522458 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B1648081 : Blo 1522458 1648081 := bbase (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) (by norm_num)
theorem B1713649 : Blo 1522458 1713649 := bbase (se 2 (by rfl) ⟨642618, by rfl⟩ : syracuseStep 1713649 = 1285237) (by norm_num)
theorem B3425813 : Blo 1522458 3425813 := bbase (se 6 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 3425813 = 160585) (by norm_num)
theorem B1713685 : Blo 1522458 1713685 := bbase (se 6 (by rfl) ⟨40164, by rfl⟩ : syracuseStep 1713685 = 80329) (by norm_num)
theorem B2893333 : Blo 1522458 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B17360405 : Blo 1522458 17360405 := bbase (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) (by norm_num)
theorem B1713721 : Blo 1522458 1713721 := bbase (se 2 (by rfl) ⟨642645, by rfl⟩ : syracuseStep 1713721 = 1285291) (by norm_num)
theorem B3425885 : Blo 1522458 3425885 := bbase (se 3 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 3425885 = 1284707) (by norm_num)
theorem B1713757 : Blo 1522458 1713757 := bbase (se 3 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 1713757 = 642659) (by norm_num)
theorem B1713793 : Blo 1522458 1713793 := bbase (se 2 (by rfl) ⟨642672, by rfl⟩ : syracuseStep 1713793 = 1285345) (by norm_num)
theorem B3425957 : Blo 1522458 3425957 := bbase (se 4 (by rfl) ⟨321183, by rfl⟩ : syracuseStep 3425957 = 642367) (by norm_num)
theorem B1713829 : Blo 1522458 1713829 := bbase (se 4 (by rfl) ⟨160671, by rfl⟩ : syracuseStep 1713829 = 321343) (by norm_num)
theorem B5785253 : Blo 1522458 5785253 := bbase (se 4 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 5785253 = 1084735) (by norm_num)
theorem B2893477 : Blo 1522458 2893477 := bbase (se 4 (by rfl) ⟨271263, by rfl⟩ : syracuseStep 2893477 = 542527) (by norm_num)
theorem B7710389 : Blo 1522458 7710389 := bbase (se 5 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 7710389 = 722849) (by norm_num)
theorem B3253949 : Blo 1522458 3253949 := bbase (se 3 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 3253949 = 1220231) (by norm_num)
theorem B1713865 : Blo 1522458 1713865 := bbase (se 2 (by rfl) ⟨642699, by rfl⟩ : syracuseStep 1713865 = 1285399) (by norm_num)
theorem B3426029 : Blo 1522458 3426029 := bbase (se 3 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 3426029 = 1284761) (by norm_num)
theorem B1713901 : Blo 1522458 1713901 := bbase (se 3 (by rfl) ⟨321356, by rfl⟩ : syracuseStep 1713901 = 642713) (by norm_num)
theorem B2057989 : Blo 1522458 2057989 := bbase (se 4 (by rfl) ⟨192936, by rfl⟩ : syracuseStep 2057989 = 385873) (by norm_num)
theorem B1926929 : Blo 1522458 1926929 := bbase (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) (by norm_num)
theorem B1713937 : Blo 1522458 1713937 := bbase (se 2 (by rfl) ⟨642726, by rfl⟩ : syracuseStep 1713937 = 1285453) (by norm_num)
theorem B3426101 : Blo 1522458 3426101 := bbase (se 5 (by rfl) ⟨160598, by rfl⟩ : syracuseStep 3426101 = 321197) (by norm_num)
theorem B1713973 : Blo 1522458 1713973 := bbase (se 5 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 1713973 = 160685) (by norm_num)
theorem B3254069 : Blo 1522458 3254069 := bbase (se 5 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 3254069 = 305069) (by norm_num)
theorem B2893637 : Blo 1522458 2893637 := bbase (se 4 (by rfl) ⟨271278, by rfl⟩ : syracuseStep 2893637 = 542557) (by norm_num)
theorem B1926985 : Blo 1522458 1926985 := bbase (se 2 (by rfl) ⟨722619, by rfl⟩ : syracuseStep 1926985 = 1445239) (by norm_num)
theorem B1714009 : Blo 1522458 1714009 := bbase (se 2 (by rfl) ⟨642753, by rfl⟩ : syracuseStep 1714009 = 1285507) (by norm_num)
theorem B3426173 : Blo 1522458 3426173 := bbase (se 3 (by rfl) ⟨642407, by rfl⟩ : syracuseStep 3426173 = 1284815) (by norm_num)
theorem B1714045 : Blo 1522458 1714045 := bbase (se 3 (by rfl) ⟨321383, by rfl⟩ : syracuseStep 1714045 = 642767) (by norm_num)
theorem B1714081 : Blo 1522458 1714081 := bbase (se 2 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 1714081 = 1285561) (by norm_num)
theorem B1927081 : Blo 1522458 1927081 := bbase (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) (by norm_num)
theorem B3426245 : Blo 1522458 3426245 := bbase (se 4 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 3426245 = 642421) (by norm_num)
theorem B1714117 : Blo 1522458 1714117 := bbase (se 4 (by rfl) ⟨160698, by rfl⟩ : syracuseStep 1714117 = 321397) (by norm_num)
theorem B2893781 : Blo 1522458 2893781 := bbase (se 7 (by rfl) ⟨33911, by rfl⟩ : syracuseStep 2893781 = 67823) (by norm_num)
theorem B7325653 : Blo 1522458 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B1714153 : Blo 1522458 1714153 := bbase (se 2 (by rfl) ⟨642807, by rfl⟩ : syracuseStep 1714153 = 1285615) (by norm_num)
theorem B3426317 : Blo 1522458 3426317 := bbase (se 3 (by rfl) ⟨642434, by rfl⟩ : syracuseStep 3426317 = 1284869) (by norm_num)
theorem B1714189 : Blo 1522458 1714189 := bbase (se 3 (by rfl) ⟨321410, by rfl⟩ : syracuseStep 1714189 = 642821) (by norm_num)
theorem B3475493 : Blo 1522458 3475493 := bbase (se 4 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 3475493 = 651655) (by norm_num)
theorem B1714225 : Blo 1522458 1714225 := bbase (se 2 (by rfl) ⟨642834, by rfl⟩ : syracuseStep 1714225 = 1285669) (by norm_num)
theorem B1927253 : Blo 1522458 1927253 := bbase (se 8 (by rfl) ⟨11292, by rfl⟩ : syracuseStep 1927253 = 22585) (by norm_num)
theorem B3426389 : Blo 1522458 3426389 := bbase (se 8 (by rfl) ⟨20076, by rfl⟩ : syracuseStep 3426389 = 40153) (by norm_num)
theorem B1714261 : Blo 1522458 1714261 := bbase (se 8 (by rfl) ⟨10044, by rfl⟩ : syracuseStep 1714261 = 20089) (by norm_num)
theorem B1714297 : Blo 1522458 1714297 := bbase (se 2 (by rfl) ⟨642861, by rfl⟩ : syracuseStep 1714297 = 1285723) (by norm_num)
theorem B1927309 : Blo 1522458 1927309 := bbase (se 3 (by rfl) ⟨361370, by rfl⟩ : syracuseStep 1927309 = 722741) (by norm_num)
theorem B3426461 : Blo 1522458 3426461 := bbase (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) (by norm_num)
theorem B1714333 : Blo 1522458 1714333 := bbase (se 3 (by rfl) ⟨321437, by rfl⟩ : syracuseStep 1714333 = 642875) (by norm_num)
theorem B3909805 : Blo 1522458 3909805 := bbase (se 3 (by rfl) ⟨733088, by rfl⟩ : syracuseStep 3909805 = 1466177) (by norm_num)
theorem B1714369 : Blo 1522458 1714369 := bbase (se 2 (by rfl) ⟨642888, by rfl⟩ : syracuseStep 1714369 = 1285777) (by norm_num)
theorem B2058437 : Blo 1522458 2058437 := bbase (se 4 (by rfl) ⟨192978, by rfl⟩ : syracuseStep 2058437 = 385957) (by norm_num)
theorem B3426533 : Blo 1522458 3426533 := bbase (se 4 (by rfl) ⟨321237, by rfl⟩ : syracuseStep 3426533 = 642475) (by norm_num)
theorem B1714405 : Blo 1522458 1714405 := bbase (se 4 (by rfl) ⟨160725, by rfl⟩ : syracuseStep 1714405 = 321451) (by norm_num)
theorem B1927405 : Blo 1522458 1927405 := bbase (se 3 (by rfl) ⟨361388, by rfl⟩ : syracuseStep 1927405 = 722777) (by norm_num)
theorem B2894069 : Blo 1522458 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B5138693 : Blo 1522458 5138693 := bbase (se 4 (by rfl) ⟨481752, by rfl⟩ : syracuseStep 5138693 = 963505) (by norm_num)
theorem B7817477 : Blo 1522458 7817477 := bbase (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) (by norm_num)
theorem B1714441 : Blo 1522458 1714441 := bbase (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) (by norm_num)
theorem B3426605 : Blo 1522458 3426605 := bbase (se 3 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 3426605 = 1284977) (by norm_num)
theorem B1714477 : Blo 1522458 1714477 := bbase (se 3 (by rfl) ⟨321464, by rfl⟩ : syracuseStep 1714477 = 642929) (by norm_num)
theorem B1714513 : Blo 1522458 1714513 := bbase (se 2 (by rfl) ⟨642942, by rfl⟩ : syracuseStep 1714513 = 1285885) (by norm_num)
theorem B3426677 : Blo 1522458 3426677 := bbase (se 5 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 3426677 = 321251) (by norm_num)
theorem B1714549 : Blo 1522458 1714549 := bbase (se 5 (by rfl) ⟨80369, by rfl⟩ : syracuseStep 1714549 = 160739) (by norm_num)
theorem B1927577 : Blo 1522458 1927577 := bbase (se 2 (by rfl) ⟨722841, by rfl⟩ : syracuseStep 1927577 = 1445683) (by norm_num)
theorem B1714585 : Blo 1522458 1714585 := bbase (se 2 (by rfl) ⟨642969, by rfl⟩ : syracuseStep 1714585 = 1285939) (by norm_num)
theorem B3254701 : Blo 1522458 3254701 := bbase (se 3 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 3254701 = 1220513) (by norm_num)
theorem B3426749 : Blo 1522458 3426749 := bbase (se 3 (by rfl) ⟨642515, by rfl⟩ : syracuseStep 3426749 = 1285031) (by norm_num)
theorem B1714621 : Blo 1522458 1714621 := bbase (se 3 (by rfl) ⟨321491, by rfl⟩ : syracuseStep 1714621 = 642983) (by norm_num)
theorem B1927633 : Blo 1522458 1927633 := bbase (se 2 (by rfl) ⟨722862, by rfl⟩ : syracuseStep 1927633 = 1445725) (by norm_num)
theorem B1714657 : Blo 1522458 1714657 := bbase (se 2 (by rfl) ⟨642996, by rfl⟩ : syracuseStep 1714657 = 1285993) (by norm_num)
theorem B13199861 : Blo 1522458 13199861 := bbase (se 5 (by rfl) ⟨618743, by rfl⟩ : syracuseStep 13199861 = 1237487) (by norm_num)
theorem B3426821 : Blo 1522458 3426821 := bbase (se 4 (by rfl) ⟨321264, by rfl⟩ : syracuseStep 3426821 = 642529) (by norm_num)
theorem B1714693 : Blo 1522458 1714693 := bbase (se 4 (by rfl) ⟨160752, by rfl⟩ : syracuseStep 1714693 = 321505) (by norm_num)
theorem B1714729 : Blo 1522458 1714729 := bbase (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) (by norm_num)
theorem B1927729 : Blo 1522458 1927729 := bbase (se 2 (by rfl) ⟨722898, by rfl⟩ : syracuseStep 1927729 = 1445797) (by norm_num)
theorem B3426893 : Blo 1522458 3426893 := bbase (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) (by norm_num)
theorem B1714765 : Blo 1522458 1714765 := bbase (se 3 (by rfl) ⟨321518, by rfl⟩ : syracuseStep 1714765 = 643037) (by norm_num)
theorem B83389013 : Blo 1522458 83389013 := bbase (se 8 (by rfl) ⟨488607, by rfl⟩ : syracuseStep 83389013 = 977215) (by norm_num)
theorem B4336229 : Blo 1522458 4336229 := bbase (se 4 (by rfl) ⟨406521, by rfl⟩ : syracuseStep 4336229 = 813043) (by norm_num)
theorem B1829477 : Blo 1522458 1829477 := bbase (se 4 (by rfl) ⟨171513, by rfl⟩ : syracuseStep 1829477 = 343027) (by norm_num)
theorem B1714801 : Blo 1522458 1714801 := bbase (se 2 (by rfl) ⟨643050, by rfl⟩ : syracuseStep 1714801 = 1286101) (by norm_num)
theorem B3426965 : Blo 1522458 3426965 := bbase (se 6 (by rfl) ⟨80319, by rfl⟩ : syracuseStep 3426965 = 160639) (by norm_num)
theorem B1714837 : Blo 1522458 1714837 := bbase (se 6 (by rfl) ⟨40191, by rfl⟩ : syracuseStep 1714837 = 80383) (by norm_num)
theorem B5139125 : Blo 1522458 5139125 := bbase (se 5 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 5139125 = 481793) (by norm_num)
theorem B1714873 : Blo 1522458 1714873 := bbase (se 2 (by rfl) ⟨643077, by rfl⟩ : syracuseStep 1714873 = 1286155) (by norm_num)
theorem B3427037 : Blo 1522458 3427037 := bbase (se 3 (by rfl) ⟨642569, by rfl⟩ : syracuseStep 3427037 = 1285139) (by norm_num)
theorem B1927901 : Blo 1522458 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B1714909 : Blo 1522458 1714909 := bbase (se 3 (by rfl) ⟨321545, by rfl⟩ : syracuseStep 1714909 = 643091) (by norm_num)
theorem B1714945 : Blo 1522458 1714945 := bbase (se 2 (by rfl) ⟨643104, by rfl⟩ : syracuseStep 1714945 = 1286209) (by norm_num)
theorem B1927957 : Blo 1522458 1927957 := bbase (se 6 (by rfl) ⟨45186, by rfl⟩ : syracuseStep 1927957 = 90373) (by norm_num)
theorem B3427109 : Blo 1522458 3427109 := bbase (se 4 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 3427109 = 642583) (by norm_num)
theorem B1714981 : Blo 1522458 1714981 := bbase (se 4 (by rfl) ⟨160779, by rfl⟩ : syracuseStep 1714981 = 321559) (by norm_num)
theorem B6507317 : Blo 1522458 6507317 := bbase (se 5 (by rfl) ⟨305030, by rfl⟩ : syracuseStep 6507317 = 610061) (by norm_num)
theorem B5786437 : Blo 1522458 5786437 := bbase (se 4 (by rfl) ⟨542478, by rfl⟩ : syracuseStep 5786437 = 1084957) (by norm_num)
theorem B3427181 : Blo 1522458 3427181 := bbase (se 3 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 3427181 = 1285193) (by norm_num)
theorem B1928053 : Blo 1522458 1928053 := bbase (se 5 (by rfl) ⟨90377, by rfl⟩ : syracuseStep 1928053 = 180755) (by norm_num)
theorem B1829785 : Blo 1522458 1829785 := bbase (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) (by norm_num)
theorem B3427253 : Blo 1522458 3427253 := bbase (se 5 (by rfl) ⟨160652, by rfl⟩ : syracuseStep 3427253 = 321305) (by norm_num)
theorem B3476405 : Blo 1522458 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B3910589 : Blo 1522458 3910589 := bbase (se 3 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 3910589 = 1466471) (by norm_num)
theorem B7711685 : Blo 1522458 7711685 := bbase (se 4 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 7711685 = 1445941) (by norm_num)
theorem B1829885 : Blo 1522458 1829885 := bbase (se 3 (by rfl) ⟨343103, by rfl⟩ : syracuseStep 1829885 = 686207) (by norm_num)
theorem B3427325 : Blo 1522458 3427325 := bbase (se 3 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 3427325 = 1285247) (by norm_num)
theorem B1928225 : Blo 1522458 1928225 := bbase (se 2 (by rfl) ⟨723084, by rfl⟩ : syracuseStep 1928225 = 1446169) (by norm_num)
theorem B9759797 : Blo 1522458 9759797 := bbase (se 5 (by rfl) ⟨457490, by rfl⟩ : syracuseStep 9759797 = 914981) (by norm_num)
theorem B3427397 : Blo 1522458 3427397 := bbase (se 4 (by rfl) ⟨321318, by rfl⟩ : syracuseStep 3427397 = 642637) (by norm_num)
theorem B1928281 : Blo 1522458 1928281 := bbase (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) (by norm_num)
theorem B2174045 : Blo 1522458 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B5139557 : Blo 1522458 5139557 := bbase (se 4 (by rfl) ⟨481833, by rfl⟩ : syracuseStep 5139557 = 963667) (by norm_num)
theorem B5786741 : Blo 1522458 5786741 := bbase (se 5 (by rfl) ⟨271253, by rfl⟩ : syracuseStep 5786741 = 542507) (by norm_num)
theorem B3427469 : Blo 1522458 3427469 := bbase (se 3 (by rfl) ⟨642650, by rfl⟩ : syracuseStep 3427469 = 1285301) (by norm_num)
theorem B29273237 : Blo 1522458 29273237 := bbase (se 6 (by rfl) ⟨686091, by rfl⟩ : syracuseStep 29273237 = 1372183) (by norm_num)
theorem B1928377 : Blo 1522458 1928377 := bbase (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) (by norm_num)
theorem B3427541 : Blo 1522458 3427541 := bbase (se 7 (by rfl) ⟨40166, by rfl⟩ : syracuseStep 3427541 = 80333) (by norm_num)
theorem B3427613 : Blo 1522458 3427613 := bbase (se 3 (by rfl) ⟨642677, by rfl⟩ : syracuseStep 3427613 = 1285355) (by norm_num)
theorem B3255589 : Blo 1522458 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B3427685 : Blo 1522458 3427685 := bbase (se 4 (by rfl) ⟨321345, by rfl⟩ : syracuseStep 3427685 = 642691) (by norm_num)
theorem B1928549 : Blo 1522458 1928549 := bbase (se 4 (by rfl) ⟨180801, by rfl⟩ : syracuseStep 1928549 = 361603) (by norm_num)
theorem B3960197 : Blo 1522458 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B1830289 : Blo 1522458 1830289 := bbase (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) (by norm_num)
theorem B1928605 : Blo 1522458 1928605 := bbase (se 3 (by rfl) ⟨361613, by rfl⟩ : syracuseStep 1928605 = 723227) (by norm_num)
theorem B3255709 : Blo 1522458 3255709 := bbase (se 3 (by rfl) ⟨610445, by rfl⟩ : syracuseStep 3255709 = 1220891) (by norm_num)
theorem B3427757 : Blo 1522458 3427757 := bbase (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) (by norm_num)
theorem B4115893 : Blo 1522458 4115893 := bbase (se 5 (by rfl) ⟨192932, by rfl⟩ : syracuseStep 4115893 = 385865) (by norm_num)
theorem B3853757 : Blo 1522458 3853757 := bbase (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) (by norm_num)
theorem B3427829 : Blo 1522458 3427829 := bbase (se 5 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 3427829 = 321359) (by norm_num)
theorem B1928701 : Blo 1522458 1928701 := bbase (se 3 (by rfl) ⟨361631, by rfl⟩ : syracuseStep 1928701 = 723263) (by norm_num)
theorem B5139989 : Blo 1522458 5139989 := bbase (se 6 (by rfl) ⟨120468, by rfl⟩ : syracuseStep 5139989 = 240937) (by norm_num)
theorem B3427901 : Blo 1522458 3427901 := bbase (se 3 (by rfl) ⟨642731, by rfl⟩ : syracuseStep 3427901 = 1285463) (by norm_num)
theorem B3427973 : Blo 1522458 3427973 := bbase (se 4 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 3427973 = 642745) (by norm_num)
theorem B6950549 : Blo 1522458 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B1928873 : Blo 1522458 1928873 := bbase (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) (by norm_num)
theorem B3428045 : Blo 1522458 3428045 := bbase (se 3 (by rfl) ⟨642758, by rfl⟩ : syracuseStep 3428045 = 1285517) (by norm_num)
theorem B1928929 : Blo 1522458 1928929 := bbase (se 2 (by rfl) ⟨723348, by rfl⟩ : syracuseStep 1928929 = 1446697) (by norm_num)
theorem B4878053 : Blo 1522458 4878053 := bbase (se 4 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 4878053 = 914635) (by norm_num)
theorem B1855217 : Blo 1522458 1855217 := bbase (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) (by norm_num)
theorem B1830673 : Blo 1522458 1830673 := bbase (se 2 (by rfl) ⟨686502, by rfl⟩ : syracuseStep 1830673 = 1373005) (by norm_num)
theorem B3854101 : Blo 1522458 3854101 := bbase (se 6 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 3854101 = 180661) (by norm_num)
theorem B3428117 : Blo 1522458 3428117 := bbase (se 6 (by rfl) ⟨80346, by rfl⟩ : syracuseStep 3428117 = 160693) (by norm_num)
theorem B1625881 : Blo 1522458 1625881 := bbase (se 2 (by rfl) ⟨609705, by rfl⟩ : syracuseStep 1625881 = 1219411) (by norm_num)
theorem B1953589 : Blo 1522458 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B1929025 : Blo 1522458 1929025 := bbase (se 2 (by rfl) ⟨723384, by rfl⟩ : syracuseStep 1929025 = 1446769) (by norm_num)
theorem B1625941 : Blo 1522458 1625941 := bbase (se 9 (by rfl) ⟨4763, by rfl⟩ : syracuseStep 1625941 = 9527) (by norm_num)
theorem B3428189 : Blo 1522458 3428189 := bbase (se 3 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 3428189 = 1285571) (by norm_num)
theorem B3854213 : Blo 1522458 3854213 := bbase (se 4 (by rfl) ⟨361332, by rfl⟩ : syracuseStep 3854213 = 722665) (by norm_num)
theorem B3428261 : Blo 1522458 3428261 := bbase (se 4 (by rfl) ⟨321399, by rfl⟩ : syracuseStep 3428261 = 642799) (by norm_num)
theorem B5140421 : Blo 1522458 5140421 := bbase (se 4 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 5140421 = 963829) (by norm_num)
theorem B3428333 : Blo 1522458 3428333 := bbase (se 3 (by rfl) ⟨642812, by rfl⟩ : syracuseStep 3428333 = 1285625) (by norm_num)
theorem B1929197 : Blo 1522458 1929197 := bbase (se 3 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 1929197 = 723449) (by norm_num)
theorem B1929253 : Blo 1522458 1929253 := bbase (se 4 (by rfl) ⟨180867, by rfl⟩ : syracuseStep 1929253 = 361735) (by norm_num)
theorem B3428405 : Blo 1522458 3428405 := bbase (se 5 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 3428405 = 321413) (by norm_num)
theorem B3854405 : Blo 1522458 3854405 := bbase (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) (by norm_num)
theorem B4632677 : Blo 1522458 4632677 := bbase (se 4 (by rfl) ⟨434313, by rfl⟩ : syracuseStep 4632677 = 868627) (by norm_num)
theorem B3428477 : Blo 1522458 3428477 := bbase (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) (by norm_num)
theorem B1929349 : Blo 1522458 1929349 := bbase (se 4 (by rfl) ⟨180876, by rfl⟩ : syracuseStep 1929349 = 361753) (by norm_num)
theorem B1626257 : Blo 1522458 1626257 := bbase (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) (by norm_num)
theorem B4337813 : Blo 1522458 4337813 := bbase (se 6 (by rfl) ⟨101667, by rfl⟩ : syracuseStep 4337813 = 203335) (by norm_num)
theorem B26038421 : Blo 1522458 26038421 := bbase (se 6 (by rfl) ⟨610275, by rfl⟩ : syracuseStep 26038421 = 1220551) (by norm_num)
theorem B3428549 : Blo 1522458 3428549 := bbase (se 4 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 3428549 = 642853) (by norm_num)
theorem B7712981 : Blo 1522458 7712981 := bbase (se 7 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 7712981 = 180773) (by norm_num)
theorem B3428621 : Blo 1522458 3428621 := bbase (se 3 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 3428621 = 1285733) (by norm_num)
theorem B7819573 : Blo 1522458 7819573 := bbase (se 5 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 7819573 = 733085) (by norm_num)
theorem B3428693 : Blo 1522458 3428693 := bbase (se 10 (by rfl) ⟨5022, by rfl⟩ : syracuseStep 3428693 = 10045) (by norm_num)
theorem B5140853 : Blo 1522458 5140853 := bbase (se 5 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 5140853 = 481955) (by norm_num)
theorem B3658117 : Blo 1522458 3658117 := bbase (se 4 (by rfl) ⟨342948, by rfl⟩ : syracuseStep 3658117 = 685897) (by norm_num)
theorem B8671637 : Blo 1522458 8671637 := bbase (se 6 (by rfl) ⟨203241, by rfl⟩ : syracuseStep 8671637 = 406483) (by norm_num)
theorem B3854749 : Blo 1522458 3854749 := bbase (se 3 (by rfl) ⟨722765, by rfl⟩ : syracuseStep 3854749 = 1445531) (by norm_num)
theorem B3428765 : Blo 1522458 3428765 := bbase (se 3 (by rfl) ⟨642893, by rfl⟩ : syracuseStep 3428765 = 1285787) (by norm_num)
theorem B6951349 : Blo 1522458 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B3658213 : Blo 1522458 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B3428837 : Blo 1522458 3428837 := bbase (se 4 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 3428837 = 642907) (by norm_num)
theorem B2200069 : Blo 1522458 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B3854861 : Blo 1522458 3854861 := bbase (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) (by norm_num)
theorem B14635541 : Blo 1522458 14635541 := bbase (se 6 (by rfl) ⟨343020, by rfl⟩ : syracuseStep 14635541 = 686041) (by norm_num)
theorem B3428909 : Blo 1522458 3428909 := bbase (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) (by norm_num)
theorem B1626701 : Blo 1522458 1626701 := bbase (se 3 (by rfl) ⟨305006, by rfl⟩ : syracuseStep 1626701 = 610013) (by norm_num)
theorem B1544789 : Blo 1522458 1544789 := bbase (se 8 (by rfl) ⟨9051, by rfl⟩ : syracuseStep 1544789 = 18103) (by norm_num)
theorem B3428981 : Blo 1522458 3428981 := bbase (se 5 (by rfl) ⟨160733, by rfl⟩ : syracuseStep 3428981 = 321467) (by norm_num)
theorem B1626761 : Blo 1522458 1626761 := bbase (se 2 (by rfl) ⟨610035, by rfl⟩ : syracuseStep 1626761 = 1220071) (by norm_num)
theorem B9261749 : Blo 1522458 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B3429053 : Blo 1522458 3429053 := bbase (se 3 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 3429053 = 1285895) (by norm_num)
theorem B3855053 : Blo 1522458 3855053 := bbase (se 3 (by rfl) ⟨722822, by rfl⟩ : syracuseStep 3855053 = 1445645) (by norm_num)
theorem B3429125 : Blo 1522458 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B1626889 : Blo 1522458 1626889 := bbase (se 2 (by rfl) ⟨610083, by rfl⟩ : syracuseStep 1626889 = 1220167) (by norm_num)
theorem B5141285 : Blo 1522458 5141285 := bbase (se 4 (by rfl) ⟨481995, by rfl⟩ : syracuseStep 5141285 = 963991) (by norm_num)
theorem B4338485 : Blo 1522458 4338485 := bbase (se 5 (by rfl) ⟨203366, by rfl⟩ : syracuseStep 4338485 = 406733) (by norm_num)
theorem B3429197 : Blo 1522458 3429197 := bbase (se 3 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 3429197 = 1285949) (by norm_num)
theorem B3429269 : Blo 1522458 3429269 := bbase (se 6 (by rfl) ⟨80373, by rfl⟩ : syracuseStep 3429269 = 160747) (by norm_num)
theorem B3429341 : Blo 1522458 3429341 := bbase (se 3 (by rfl) ⟨643001, by rfl⟩ : syracuseStep 3429341 = 1286003) (by norm_num)
theorem B3658733 : Blo 1522458 3658733 := bbase (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) (by norm_num)
theorem B2569205 : Blo 1522458 2569205 := bbase (se 5 (by rfl) ⟨120431, by rfl⟩ : syracuseStep 2569205 = 240863) (by norm_num)
theorem B2167813 : Blo 1522458 2167813 := bbase (se 4 (by rfl) ⟨203232, by rfl⟩ : syracuseStep 2167813 = 406465) (by norm_num)
theorem B3855397 : Blo 1522458 3855397 := bbase (se 4 (by rfl) ⟨361443, by rfl⟩ : syracuseStep 3855397 = 722887) (by norm_num)
theorem B3429413 : Blo 1522458 3429413 := bbase (se 4 (by rfl) ⟨321507, by rfl⟩ : syracuseStep 3429413 = 643015) (by norm_num)
theorem B3429485 : Blo 1522458 3429485 := bbase (se 3 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 3429485 = 1286057) (by norm_num)
theorem B2569333 : Blo 1522458 2569333 := bbase (se 5 (by rfl) ⟨120437, by rfl⟩ : syracuseStep 2569333 = 240875) (by norm_num)
theorem B3855509 : Blo 1522458 3855509 := bbase (se 6 (by rfl) ⟨90363, by rfl⟩ : syracuseStep 3855509 = 180727) (by norm_num)
theorem B3429557 : Blo 1522458 3429557 := bbase (se 5 (by rfl) ⟨160760, by rfl⟩ : syracuseStep 3429557 = 321521) (by norm_num)
theorem B1627333 : Blo 1522458 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B2569421 : Blo 1522458 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B55571669 : Blo 1522458 55571669 := bbase (se 7 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 55571669 = 1302461) (by norm_num)
theorem B4117717 : Blo 1522458 4117717 := bbase (se 7 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 4117717 = 96509) (by norm_num)
theorem B5141717 : Blo 1522458 5141717 := bbase (se 7 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 5141717 = 120509) (by norm_num)
theorem B4338917 : Blo 1522458 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B3429629 : Blo 1522458 3429629 := bbase (se 3 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 3429629 = 1286111) (by norm_num)
theorem B5862709 : Blo 1522458 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B1627453 : Blo 1522458 1627453 := bbase (se 3 (by rfl) ⟨305147, by rfl⟩ : syracuseStep 1627453 = 610295) (by norm_num)
theorem B3429701 : Blo 1522458 3429701 := bbase (se 4 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 3429701 = 643069) (by norm_num)
theorem B2569549 : Blo 1522458 2569549 := bbase (se 3 (by rfl) ⟨481790, by rfl⟩ : syracuseStep 2569549 = 963581) (by norm_num)
theorem B2168149 : Blo 1522458 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B3855701 : Blo 1522458 3855701 := bbase (se 15 (by rfl) ⟨176, by rfl⟩ : syracuseStep 3855701 = 353) (by norm_num)
theorem B3429773 : Blo 1522458 3429773 := bbase (se 3 (by rfl) ⟨643082, by rfl⟩ : syracuseStep 3429773 = 1286165) (by norm_num)
theorem B2569637 : Blo 1522458 2569637 := bbase (se 4 (by rfl) ⟨240903, by rfl⟩ : syracuseStep 2569637 = 481807) (by norm_num)
theorem B3429845 : Blo 1522458 3429845 := bbase (se 7 (by rfl) ⟨40193, by rfl⟩ : syracuseStep 3429845 = 80387) (by norm_num)
theorem B7714277 : Blo 1522458 7714277 := bbase (se 4 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 7714277 = 1446427) (by norm_num)
theorem B3659261 : Blo 1522458 3659261 := bbase (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) (by norm_num)
theorem B3429917 : Blo 1522458 3429917 := bbase (se 3 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 3429917 = 1286219) (by norm_num)
theorem B2569765 : Blo 1522458 2569765 := bbase (se 4 (by rfl) ⟨240915, by rfl⟩ : syracuseStep 2569765 = 481831) (by norm_num)
theorem B2168365 : Blo 1522458 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B1627705 : Blo 1522458 1627705 := bbase (se 2 (by rfl) ⟨610389, by rfl⟩ : syracuseStep 1627705 = 1220779) (by norm_num)
theorem B1627709 : Blo 1522458 1627709 := bbase (se 3 (by rfl) ⟨305195, by rfl⟩ : syracuseStep 1627709 = 610391) (by norm_num)
theorem B6952517 : Blo 1522458 6952517 := bbase (se 4 (by rfl) ⟨651798, by rfl⟩ : syracuseStep 6952517 = 1303597) (by norm_num)
theorem B5781077 : Blo 1522458 5781077 := bbase (se 8 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 5781077 = 67747) (by norm_num)
theorem B3429989 : Blo 1522458 3429989 := bbase (se 4 (by rfl) ⟨321561, by rfl⟩ : syracuseStep 3429989 = 643123) (by norm_num)
theorem B2569853 : Blo 1522458 2569853 := bbase (se 3 (by rfl) ⟨481847, by rfl⟩ : syracuseStep 2569853 = 963695) (by norm_num)
theorem B5142149 : Blo 1522458 5142149 := bbase (se 4 (by rfl) ⟨482076, by rfl⟩ : syracuseStep 5142149 = 964153) (by norm_num)
theorem B3856045 : Blo 1522458 3856045 := bbase (se 3 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 3856045 = 1446017) (by norm_num)
theorem B6870757 : Blo 1522458 6870757 := bbase (se 4 (by rfl) ⟨644133, by rfl⟩ : syracuseStep 6870757 = 1288267) (by norm_num)
theorem B3659501 : Blo 1522458 3659501 := bbase (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) (by norm_num)
theorem B2569981 : Blo 1522458 2569981 := bbase (se 3 (by rfl) ⟨481871, by rfl⟩ : syracuseStep 2569981 = 963743) (by norm_num)
theorem B3856157 : Blo 1522458 3856157 := bbase (se 3 (by rfl) ⟨723029, by rfl⟩ : syracuseStep 3856157 = 1446059) (by norm_num)
theorem B2570069 : Blo 1522458 2570069 := bbase (se 9 (by rfl) ⟨7529, by rfl⟩ : syracuseStep 2570069 = 15059) (by norm_num)
theorem B7821157 : Blo 1522458 7821157 := bbase (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) (by norm_num)
theorem B5781365 : Blo 1522458 5781365 := bbase (se 5 (by rfl) ⟨271001, by rfl⟩ : syracuseStep 5781365 = 542003) (by norm_num)
theorem B4880245 : Blo 1522458 4880245 := bbase (se 5 (by rfl) ⟨228761, by rfl⟩ : syracuseStep 4880245 = 457523) (by norm_num)
theorem B4634501 : Blo 1522458 4634501 := bbase (se 4 (by rfl) ⟨434484, by rfl⟩ : syracuseStep 4634501 = 868969) (by norm_num)
theorem B2168741 : Blo 1522458 2168741 := bbase (se 4 (by rfl) ⟨203319, by rfl⟩ : syracuseStep 2168741 = 406639) (by norm_num)
theorem B2570197 : Blo 1522458 2570197 := bbase (se 7 (by rfl) ⟨30119, by rfl⟩ : syracuseStep 2570197 = 60239) (by norm_num)
theorem B4339669 : Blo 1522458 4339669 := bbase (se 7 (by rfl) ⟨50855, by rfl⟩ : syracuseStep 4339669 = 101711) (by norm_num)
theorem B3856349 : Blo 1522458 3856349 := bbase (se 3 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 3856349 = 1446131) (by norm_num)
theorem B2570285 : Blo 1522458 2570285 := bbase (se 3 (by rfl) ⟨481928, by rfl⟩ : syracuseStep 2570285 = 963857) (by norm_num)
theorem B5142581 : Blo 1522458 5142581 := bbase (se 5 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 5142581 = 482117) (by norm_num)
theorem B8681525 : Blo 1522458 8681525 := bbase (se 5 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 8681525 = 813893) (by norm_num)
theorem B1980493 : Blo 1522458 1980493 := bbase (se 3 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 1980493 = 742685) (by norm_num)
theorem B2570413 : Blo 1522458 2570413 := bbase (se 3 (by rfl) ⟨481952, by rfl⟩ : syracuseStep 2570413 = 963905) (by norm_num)
theorem B2283701 : Blo 1522458 2283701 := bbase (se 5 (by rfl) ⟨107048, by rfl⟩ : syracuseStep 2283701 = 214097) (by norm_num)
theorem B2283725 : Blo 1522458 2283725 := bbase (se 3 (by rfl) ⟨428198, by rfl⟩ : syracuseStep 2283725 = 856397) (by norm_num)
theorem B2283749 : Blo 1522458 2283749 := bbase (se 4 (by rfl) ⟨214101, by rfl⟩ : syracuseStep 2283749 = 428203) (by norm_num)
theorem B2283773 : Blo 1522458 2283773 := bbase (se 3 (by rfl) ⟨428207, by rfl⟩ : syracuseStep 2283773 = 856415) (by norm_num)
theorem B2570501 : Blo 1522458 2570501 := bbase (se 4 (by rfl) ⟨240984, by rfl⟩ : syracuseStep 2570501 = 481969) (by norm_num)
theorem B2316557 : Blo 1522458 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B2283797 : Blo 1522458 2283797 := bbase (se 6 (by rfl) ⟨53526, by rfl⟩ : syracuseStep 2283797 = 107053) (by norm_num)
theorem B2283821 : Blo 1522458 2283821 := bbase (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) (by norm_num)
theorem B3856693 : Blo 1522458 3856693 := bbase (se 5 (by rfl) ⟨180782, by rfl⟩ : syracuseStep 3856693 = 361565) (by norm_num)
theorem B2283845 : Blo 1522458 2283845 := bbase (se 4 (by rfl) ⟨214110, by rfl⟩ : syracuseStep 2283845 = 428221) (by norm_num)
theorem B2283869 : Blo 1522458 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B2283893 : Blo 1522458 2283893 := bbase (se 5 (by rfl) ⟨107057, by rfl⟩ : syracuseStep 2283893 = 214115) (by norm_num)
theorem B1980805 : Blo 1522458 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B2570629 : Blo 1522458 2570629 := bbase (se 4 (by rfl) ⟨240996, by rfl⟩ : syracuseStep 2570629 = 481993) (by norm_num)
theorem B2283917 : Blo 1522458 2283917 := bbase (se 3 (by rfl) ⟨428234, by rfl⟩ : syracuseStep 2283917 = 856469) (by norm_num)
theorem B2283941 : Blo 1522458 2283941 := bbase (se 4 (by rfl) ⟨214119, by rfl⟩ : syracuseStep 2283941 = 428239) (by norm_num)
theorem B3856805 : Blo 1522458 3856805 := bbase (se 4 (by rfl) ⟨361575, by rfl⟩ : syracuseStep 3856805 = 723151) (by norm_num)
theorem B2283965 : Blo 1522458 2283965 := bbase (se 3 (by rfl) ⟨428243, by rfl⟩ : syracuseStep 2283965 = 856487) (by norm_num)
theorem B5487061 : Blo 1522458 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B2283989 : Blo 1522458 2283989 := bbase (se 7 (by rfl) ⟨26765, by rfl⟩ : syracuseStep 2283989 = 53531) (by norm_num)
theorem B2570717 : Blo 1522458 2570717 := bbase (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) (by norm_num)
theorem B5143013 : Blo 1522458 5143013 := bbase (se 4 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 5143013 = 964315) (by norm_num)
theorem B2284013 : Blo 1522458 2284013 := bbase (se 3 (by rfl) ⟨428252, by rfl⟩ : syracuseStep 2284013 = 856505) (by norm_num)
theorem B2284037 : Blo 1522458 2284037 := bbase (se 4 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 2284037 = 428257) (by norm_num)
theorem B2284061 : Blo 1522458 2284061 := bbase (se 3 (by rfl) ⟨428261, by rfl⟩ : syracuseStep 2284061 = 856523) (by norm_num)
theorem B2284085 : Blo 1522458 2284085 := bbase (se 5 (by rfl) ⟨107066, by rfl⟩ : syracuseStep 2284085 = 214133) (by norm_num)
theorem B2284109 : Blo 1522458 2284109 := bbase (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) (by norm_num)
theorem B12352085 : Blo 1522458 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B2890333 : Blo 1522458 2890333 := bbase (se 3 (by rfl) ⟨541937, by rfl⟩ : syracuseStep 2890333 = 1083875) (by norm_num)
theorem B2570845 : Blo 1522458 2570845 := bbase (se 3 (by rfl) ⟨482033, by rfl⟩ : syracuseStep 2570845 = 964067) (by norm_num)
theorem B2284133 : Blo 1522458 2284133 := bbase (se 4 (by rfl) ⟨214137, by rfl⟩ : syracuseStep 2284133 = 428275) (by norm_num)
theorem B7322213 : Blo 1522458 7322213 := bbase (se 4 (by rfl) ⟨686457, by rfl⟩ : syracuseStep 7322213 = 1372915) (by norm_num)
theorem B3856997 : Blo 1522458 3856997 := bbase (se 4 (by rfl) ⟨361593, by rfl⟩ : syracuseStep 3856997 = 723187) (by norm_num)
theorem B2284157 : Blo 1522458 2284157 := bbase (se 3 (by rfl) ⟨428279, by rfl⟩ : syracuseStep 2284157 = 856559) (by norm_num)
theorem B2439821 : Blo 1522458 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B2284181 : Blo 1522458 2284181 := bbase (se 6 (by rfl) ⟨53535, by rfl⟩ : syracuseStep 2284181 = 107071) (by norm_num)
theorem B2284205 : Blo 1522458 2284205 := bbase (se 3 (by rfl) ⟨428288, by rfl⟩ : syracuseStep 2284205 = 856577) (by norm_num)
theorem B2570933 : Blo 1522458 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B4881077 : Blo 1522458 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B2284229 : Blo 1522458 2284229 := bbase (se 4 (by rfl) ⟨214146, by rfl⟩ : syracuseStep 2284229 = 428293) (by norm_num)
theorem B7322309 : Blo 1522458 7322309 := bbase (se 4 (by rfl) ⟨686466, by rfl⟩ : syracuseStep 7322309 = 1372933) (by norm_num)
theorem B2284253 : Blo 1522458 2284253 := bbase (se 3 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 2284253 = 856595) (by norm_num)
theorem B2284277 : Blo 1522458 2284277 := bbase (se 5 (by rfl) ⟨107075, by rfl⟩ : syracuseStep 2284277 = 214151) (by norm_num)
theorem B7715573 : Blo 1522458 7715573 := bbase (se 5 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 7715573 = 723335) (by norm_num)
theorem B2284301 : Blo 1522458 2284301 := bbase (se 3 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 2284301 = 856613) (by norm_num)
theorem B2284325 : Blo 1522458 2284325 := bbase (se 4 (by rfl) ⟨214155, by rfl⟩ : syracuseStep 2284325 = 428311) (by norm_num)
theorem B2571061 : Blo 1522458 2571061 := bbase (se 5 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 2571061 = 241037) (by norm_num)
theorem B2284349 : Blo 1522458 2284349 := bbase (se 3 (by rfl) ⟨428315, by rfl⟩ : syracuseStep 2284349 = 856631) (by norm_num)
theorem B2284373 : Blo 1522458 2284373 := bbase (se 9 (by rfl) ⟨6692, by rfl⟩ : syracuseStep 2284373 = 13385) (by norm_num)
theorem B2284397 : Blo 1522458 2284397 := bbase (se 3 (by rfl) ⟨428324, by rfl⟩ : syracuseStep 2284397 = 856649) (by norm_num)
theorem B2284421 : Blo 1522458 2284421 := bbase (se 4 (by rfl) ⟨214164, by rfl⟩ : syracuseStep 2284421 = 428329) (by norm_num)
theorem B2890637 : Blo 1522458 2890637 := bbase (se 3 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 2890637 = 1083989) (by norm_num)
theorem B2571149 : Blo 1522458 2571149 := bbase (se 3 (by rfl) ⟨482090, by rfl⟩ : syracuseStep 2571149 = 964181) (by norm_num)
theorem B5143445 : Blo 1522458 5143445 := bbase (se 6 (by rfl) ⟨120549, by rfl⟩ : syracuseStep 5143445 = 241099) (by norm_num)
theorem B2284445 : Blo 1522458 2284445 := bbase (se 3 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 2284445 = 856667) (by norm_num)
theorem B2284469 : Blo 1522458 2284469 := bbase (se 5 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 2284469 = 214169) (by norm_num)
theorem B3857341 : Blo 1522458 3857341 := bbase (se 3 (by rfl) ⟨723251, by rfl⟩ : syracuseStep 3857341 = 1446503) (by norm_num)
theorem B2284493 : Blo 1522458 2284493 := bbase (se 3 (by rfl) ⟨428342, by rfl⟩ : syracuseStep 2284493 = 856685) (by norm_num)
theorem B2284517 : Blo 1522458 2284517 := bbase (se 4 (by rfl) ⟨214173, by rfl⟩ : syracuseStep 2284517 = 428347) (by norm_num)
theorem B6511589 : Blo 1522458 6511589 := bbase (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) (by norm_num)
theorem B2284541 : Blo 1522458 2284541 := bbase (se 3 (by rfl) ⟨428351, by rfl⟩ : syracuseStep 2284541 = 856703) (by norm_num)
theorem B2571277 : Blo 1522458 2571277 := bbase (se 3 (by rfl) ⟨482114, by rfl⟩ : syracuseStep 2571277 = 964229) (by norm_num)
theorem B5782549 : Blo 1522458 5782549 := bbase (se 6 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 5782549 = 271057) (by norm_num)
theorem B2284565 : Blo 1522458 2284565 := bbase (se 6 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 2284565 = 107089) (by norm_num)
theorem B2284589 : Blo 1522458 2284589 := bbase (se 3 (by rfl) ⟨428360, by rfl⟩ : syracuseStep 2284589 = 856721) (by norm_num)
theorem B3857453 : Blo 1522458 3857453 := bbase (se 3 (by rfl) ⟨723272, by rfl⟩ : syracuseStep 3857453 = 1446545) (by norm_num)
theorem B2284613 : Blo 1522458 2284613 := bbase (se 4 (by rfl) ⟨214182, by rfl⟩ : syracuseStep 2284613 = 428365) (by norm_num)
theorem B2440277 : Blo 1522458 2440277 := bbase (se 8 (by rfl) ⟨14298, by rfl⟩ : syracuseStep 2440277 = 28597) (by norm_num)
theorem B2284637 : Blo 1522458 2284637 := bbase (se 3 (by rfl) ⟨428369, by rfl⟩ : syracuseStep 2284637 = 856739) (by norm_num)
theorem B2571365 : Blo 1522458 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B2284661 : Blo 1522458 2284661 := bbase (se 5 (by rfl) ⟨107093, by rfl⟩ : syracuseStep 2284661 = 214187) (by norm_num)
theorem B2284685 : Blo 1522458 2284685 := bbase (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) (by norm_num)
theorem B7707797 : Blo 1522458 7707797 := bbase (se 6 (by rfl) ⟨180651, by rfl⟩ : syracuseStep 7707797 = 361303) (by norm_num)
theorem B9755797 : Blo 1522458 9755797 := bbase (se 6 (by rfl) ⟨228651, by rfl⟩ : syracuseStep 9755797 = 457303) (by norm_num)
theorem B2284709 : Blo 1522458 2284709 := bbase (se 4 (by rfl) ⟨214191, by rfl⟩ : syracuseStep 2284709 = 428383) (by norm_num)
theorem B2284733 : Blo 1522458 2284733 := bbase (se 3 (by rfl) ⟨428387, by rfl⟩ : syracuseStep 2284733 = 856775) (by norm_num)
theorem B2284757 : Blo 1522458 2284757 := bbase (se 7 (by rfl) ⟨26774, by rfl⟩ : syracuseStep 2284757 = 53549) (by norm_num)
theorem B2571493 : Blo 1522458 2571493 := bbase (se 4 (by rfl) ⟨241077, by rfl⟩ : syracuseStep 2571493 = 482155) (by norm_num)
theorem B2284781 : Blo 1522458 2284781 := bbase (se 3 (by rfl) ⟨428396, by rfl⟩ : syracuseStep 2284781 = 856793) (by norm_num)
theorem B3857645 : Blo 1522458 3857645 := bbase (se 3 (by rfl) ⟨723308, by rfl⟩ : syracuseStep 3857645 = 1446617) (by norm_num)
theorem B2284805 : Blo 1522458 2284805 := bbase (se 4 (by rfl) ⟨214200, by rfl⟩ : syracuseStep 2284805 = 428401) (by norm_num)
theorem B2284829 : Blo 1522458 2284829 := bbase (se 3 (by rfl) ⟨428405, by rfl⟩ : syracuseStep 2284829 = 856811) (by norm_num)
theorem B2284853 : Blo 1522458 2284853 := bbase (se 5 (by rfl) ⟨107102, by rfl⟩ : syracuseStep 2284853 = 214205) (by norm_num)
theorem B14646581 : Blo 1522458 14646581 := bbase (se 5 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 14646581 = 1373117) (by norm_num)
theorem B2170165 : Blo 1522458 2170165 := bbase (se 5 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 2170165 = 203453) (by norm_num)
theorem B2571581 : Blo 1522458 2571581 := bbase (se 3 (by rfl) ⟨482171, by rfl⟩ : syracuseStep 2571581 = 964343) (by norm_num)
theorem B5782853 : Blo 1522458 5782853 := bbase (se 4 (by rfl) ⟨542142, by rfl⟩ : syracuseStep 5782853 = 1084285) (by norm_num)
theorem B5143877 : Blo 1522458 5143877 := bbase (se 4 (by rfl) ⟨482238, by rfl⟩ : syracuseStep 5143877 = 964477) (by norm_num)
theorem B2284877 : Blo 1522458 2284877 := bbase (se 3 (by rfl) ⟨428414, by rfl⟩ : syracuseStep 2284877 = 856829) (by norm_num)
theorem B2284901 : Blo 1522458 2284901 := bbase (se 4 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 2284901 = 428419) (by norm_num)
theorem B2284925 : Blo 1522458 2284925 := bbase (se 3 (by rfl) ⟨428423, by rfl⟩ : syracuseStep 2284925 = 856847) (by norm_num)
theorem B2284949 : Blo 1522458 2284949 := bbase (se 6 (by rfl) ⟨53553, by rfl⟩ : syracuseStep 2284949 = 107107) (by norm_num)
theorem B3906973 : Blo 1522458 3906973 := bbase (se 3 (by rfl) ⟨732557, by rfl⟩ : syracuseStep 3906973 = 1465115) (by norm_num)
theorem B3661213 : Blo 1522458 3661213 := bbase (se 3 (by rfl) ⟨686477, by rfl⟩ : syracuseStep 3661213 = 1372955) (by norm_num)
theorem B2932133 : Blo 1522458 2932133 := bbase (se 4 (by rfl) ⟨274887, by rfl⟩ : syracuseStep 2932133 = 549775) (by norm_num)
theorem B2284973 : Blo 1522458 2284973 := bbase (se 3 (by rfl) ⟨428432, by rfl⟩ : syracuseStep 2284973 = 856865) (by norm_num)
theorem B2571709 : Blo 1522458 2571709 := bbase (se 3 (by rfl) ⟨482195, by rfl⟩ : syracuseStep 2571709 = 964391) (by norm_num)
theorem B2284997 : Blo 1522458 2284997 := bbase (se 4 (by rfl) ⟨214218, by rfl⟩ : syracuseStep 2284997 = 428437) (by norm_num)
theorem B3251677 : Blo 1522458 3251677 := bbase (se 3 (by rfl) ⟨609689, by rfl⟩ : syracuseStep 3251677 = 1219379) (by norm_num)
theorem B2285021 : Blo 1522458 2285021 := bbase (se 3 (by rfl) ⟨428441, by rfl⟩ : syracuseStep 2285021 = 856883) (by norm_num)
theorem B2285045 : Blo 1522458 2285045 := bbase (se 5 (by rfl) ⟨107111, by rfl⟩ : syracuseStep 2285045 = 214223) (by norm_num)
theorem B2285069 : Blo 1522458 2285069 := bbase (se 3 (by rfl) ⟨428450, by rfl⟩ : syracuseStep 2285069 = 856901) (by norm_num)
theorem B2571797 : Blo 1522458 2571797 := bbase (se 6 (by rfl) ⟨60276, by rfl⟩ : syracuseStep 2571797 = 120553) (by norm_num)
theorem B2285093 : Blo 1522458 2285093 := bbase (se 4 (by rfl) ⟨214227, by rfl⟩ : syracuseStep 2285093 = 428455) (by norm_num)
theorem B5561909 : Blo 1522458 5561909 := bbase (se 5 (by rfl) ⟨260714, by rfl⟩ : syracuseStep 5561909 = 521429) (by norm_num)
theorem B2285117 : Blo 1522458 2285117 := bbase (se 3 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 2285117 = 856919) (by norm_num)
theorem B2743877 : Blo 1522458 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B4398661 : Blo 1522458 4398661 := bbase (se 4 (by rfl) ⟨412374, by rfl⟩ : syracuseStep 4398661 = 824749) (by norm_num)
theorem B3857989 : Blo 1522458 3857989 := bbase (se 4 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 3857989 = 723373) (by norm_num)
theorem B2285141 : Blo 1522458 2285141 := bbase (se 8 (by rfl) ⟨13389, by rfl⟩ : syracuseStep 2285141 = 26779) (by norm_num)
theorem B2285165 : Blo 1522458 2285165 := bbase (se 3 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 2285165 = 856937) (by norm_num)
theorem B2891389 : Blo 1522458 2891389 := bbase (se 3 (by rfl) ⟨542135, by rfl⟩ : syracuseStep 2891389 = 1084271) (by norm_num)
theorem B2285189 : Blo 1522458 2285189 := bbase (se 4 (by rfl) ⟨214236, by rfl⟩ : syracuseStep 2285189 = 428473) (by norm_num)
theorem B2571925 : Blo 1522458 2571925 := bbase (se 6 (by rfl) ⟨60279, by rfl⟩ : syracuseStep 2571925 = 120559) (by norm_num)
theorem B2285213 : Blo 1522458 2285213 := bbase (se 3 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 2285213 = 856955) (by norm_num)
theorem B2285237 : Blo 1522458 2285237 := bbase (se 5 (by rfl) ⟨107120, by rfl⟩ : syracuseStep 2285237 = 214241) (by norm_num)
theorem B3858101 : Blo 1522458 3858101 := bbase (se 5 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 3858101 = 361697) (by norm_num)
theorem B2285261 : Blo 1522458 2285261 := bbase (se 3 (by rfl) ⟨428486, by rfl⟩ : syracuseStep 2285261 = 856973) (by norm_num)
theorem B2604773 : Blo 1522458 2604773 := bbase (se 4 (by rfl) ⟨244197, by rfl⟩ : syracuseStep 2604773 = 488395) (by norm_num)
theorem B2285285 : Blo 1522458 2285285 := bbase (se 4 (by rfl) ⟨214245, by rfl⟩ : syracuseStep 2285285 = 428491) (by norm_num)
theorem B2572013 : Blo 1522458 2572013 := bbase (se 3 (by rfl) ⟨482252, by rfl⟩ : syracuseStep 2572013 = 964505) (by norm_num)
theorem B5144309 : Blo 1522458 5144309 := bbase (se 5 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 5144309 = 482279) (by norm_num)
theorem B2285309 : Blo 1522458 2285309 := bbase (se 3 (by rfl) ⟨428495, by rfl⟩ : syracuseStep 2285309 = 856991) (by norm_num)
theorem B2891533 : Blo 1522458 2891533 := bbase (se 3 (by rfl) ⟨542162, by rfl⟩ : syracuseStep 2891533 = 1084325) (by norm_num)
theorem B2285333 : Blo 1522458 2285333 := bbase (se 6 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 2285333 = 107125) (by norm_num)
theorem B11575061 : Blo 1522458 11575061 := bbase (se 6 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 11575061 = 542581) (by norm_num)
theorem B2285357 : Blo 1522458 2285357 := bbase (se 3 (by rfl) ⟨428504, by rfl⟩ : syracuseStep 2285357 = 857009) (by norm_num)
theorem B2285381 : Blo 1522458 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B2285405 : Blo 1522458 2285405 := bbase (se 3 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 2285405 = 857027) (by norm_num)
theorem B2572141 : Blo 1522458 2572141 := bbase (se 3 (by rfl) ⟨482276, by rfl⟩ : syracuseStep 2572141 = 964553) (by norm_num)
theorem B2285429 : Blo 1522458 2285429 := bbase (se 5 (by rfl) ⟨107129, by rfl⟩ : syracuseStep 2285429 = 214259) (by norm_num)
theorem B3858293 : Blo 1522458 3858293 := bbase (se 5 (by rfl) ⟨180857, by rfl⟩ : syracuseStep 3858293 = 361715) (by norm_num)
theorem B2285453 : Blo 1522458 2285453 := bbase (se 3 (by rfl) ⟨428522, by rfl⟩ : syracuseStep 2285453 = 857045) (by norm_num)
theorem B2285477 : Blo 1522458 2285477 := bbase (se 4 (by rfl) ⟨214263, by rfl⟩ : syracuseStep 2285477 = 428527) (by norm_num)
theorem B2744237 : Blo 1522458 2744237 := bbase (se 3 (by rfl) ⟨514544, by rfl⟩ : syracuseStep 2744237 = 1029089) (by norm_num)
theorem B2891693 : Blo 1522458 2891693 := bbase (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) (by norm_num)
theorem B2285501 : Blo 1522458 2285501 := bbase (se 3 (by rfl) ⟨428531, by rfl⟩ : syracuseStep 2285501 = 857063) (by norm_num)
theorem B2572229 : Blo 1522458 2572229 := bbase (se 4 (by rfl) ⟨241146, by rfl⟩ : syracuseStep 2572229 = 482293) (by norm_num)
theorem B2285525 : Blo 1522458 2285525 := bbase (se 7 (by rfl) ⟨26783, by rfl⟩ : syracuseStep 2285525 = 53567) (by norm_num)
theorem B37085141 : Blo 1522458 37085141 := bbase (se 7 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 37085141 = 869183) (by norm_num)
theorem B2285549 : Blo 1522458 2285549 := bbase (se 3 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 2285549 = 857081) (by norm_num)
theorem B1523715 : Blo 1522458 1523715 := bstep (se 1 (by rfl) ⟨1142786, by rfl⟩ : syracuseStep 1523715 = 2285573) B2285573
theorem B5144579 : Blo 1522458 5144579 := bstep (se 1 (by rfl) ⟨3858434, by rfl⟩ : syracuseStep 5144579 = 7716869) B7716869
theorem B2285585 : Blo 1522458 2285585 := bstep (se 2 (by rfl) ⟨857094, by rfl⟩ : syracuseStep 2285585 = 1714189) B1714189
theorem B1523731 : Blo 1522458 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B2285603 : Blo 1522458 2285603 := bstep (se 1 (by rfl) ⟨1714202, by rfl⟩ : syracuseStep 2285603 = 3428405) B3428405
theorem B1523747 : Blo 1522458 1523747 := bstep (se 1 (by rfl) ⟨1142810, by rfl⟩ : syracuseStep 1523747 = 2285621) B2285621
theorem B2572337 : Blo 1522458 2572337 := bstep (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) B1929253
theorem B1523763 : Blo 1522458 1523763 := bstep (se 1 (by rfl) ⟨1142822, by rfl⟩ : syracuseStep 1523763 = 2285645) B2285645
theorem B2285633 : Blo 1522458 2285633 := bstep (se 2 (by rfl) ⟨857112, by rfl⟩ : syracuseStep 2285633 = 1714225) B1714225
theorem B3088451 : Blo 1522458 3088451 := bstep (se 1 (by rfl) ⟨2316338, by rfl⟩ : syracuseStep 3088451 = 4632677) B4632677
theorem B1523779 : Blo 1522458 1523779 := bstep (se 1 (by rfl) ⟨1142834, by rfl⟩ : syracuseStep 1523779 = 2285669) B2285669
theorem B2285651 : Blo 1522458 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B1523795 : Blo 1522458 1523795 := bstep (se 1 (by rfl) ⟨1142846, by rfl⟩ : syracuseStep 1523795 = 2285693) B2285693
theorem B2891875 : Blo 1522458 2891875 := bstep (se 1 (by rfl) ⟨2168906, by rfl⟩ : syracuseStep 2891875 = 4337813) B4337813
theorem B1523811 : Blo 1522458 1523811 := bstep (se 1 (by rfl) ⟨1142858, by rfl⟩ : syracuseStep 1523811 = 2285717) B2285717
theorem B17358947 : Blo 1522458 17358947 := bstep (se 1 (by rfl) ⟨13019210, by rfl⟩ : syracuseStep 17358947 = 26038421) B26038421
theorem B2285681 : Blo 1522458 2285681 := bstep (se 2 (by rfl) ⟨857130, by rfl⟩ : syracuseStep 2285681 = 1714261) B1714261
theorem B1523827 : Blo 1522458 1523827 := bstep (se 1 (by rfl) ⟨1142870, by rfl⟩ : syracuseStep 1523827 = 2285741) B2285741
theorem B2285699 : Blo 1522458 2285699 := bstep (se 1 (by rfl) ⟨1714274, by rfl⟩ : syracuseStep 2285699 = 3428549) B3428549
theorem B1523843 : Blo 1522458 1523843 := bstep (se 1 (by rfl) ⟨1142882, by rfl⟩ : syracuseStep 1523843 = 2285765) B2285765
theorem B1523859 : Blo 1522458 1523859 := bstep (se 1 (by rfl) ⟨1142894, by rfl⟩ : syracuseStep 1523859 = 2285789) B2285789
theorem B2285729 : Blo 1522458 2285729 := bstep (se 2 (by rfl) ⟨857148, by rfl⟩ : syracuseStep 2285729 = 1714297) B1714297
theorem B1523875 : Blo 1522458 1523875 := bstep (se 1 (by rfl) ⟨1142906, by rfl⟩ : syracuseStep 1523875 = 2285813) B2285813
theorem B2572465 : Blo 1522458 2572465 := bstep (se 2 (by rfl) ⟨964674, by rfl⟩ : syracuseStep 2572465 = 1929349) B1929349
theorem B2285747 : Blo 1522458 2285747 := bstep (se 1 (by rfl) ⟨1714310, by rfl⟩ : syracuseStep 2285747 = 3428621) B3428621
theorem B1523891 : Blo 1522458 1523891 := bstep (se 1 (by rfl) ⟨1142918, by rfl⟩ : syracuseStep 1523891 = 2285837) B2285837
theorem B1523907 : Blo 1522458 1523907 := bstep (se 1 (by rfl) ⟨1142930, by rfl⟩ : syracuseStep 1523907 = 2285861) B2285861
theorem B2285777 : Blo 1522458 2285777 := bstep (se 2 (by rfl) ⟨857166, by rfl⟩ : syracuseStep 2285777 = 1714333) B1714333
theorem B1523923 : Blo 1522458 1523923 := bstep (se 1 (by rfl) ⟨1142942, by rfl⟩ : syracuseStep 1523923 = 2285885) B2285885
theorem B2572499 : Blo 1522458 2572499 := bstep (se 1 (by rfl) ⟨1929374, by rfl⟩ : syracuseStep 2572499 = 3858749) B3858749
theorem B2285795 : Blo 1522458 2285795 := bstep (se 1 (by rfl) ⟨1714346, by rfl⟩ : syracuseStep 2285795 = 3428693) B3428693
theorem B1523939 : Blo 1522458 1523939 := bstep (se 1 (by rfl) ⟨1142954, by rfl⟩ : syracuseStep 1523939 = 2285909) B2285909
theorem B1523955 : Blo 1522458 1523955 := bstep (se 1 (by rfl) ⟨1142966, by rfl⟩ : syracuseStep 1523955 = 2285933) B2285933
theorem B2285825 : Blo 1522458 2285825 := bstep (se 2 (by rfl) ⟨857184, by rfl⟩ : syracuseStep 2285825 = 1714369) B1714369
theorem B1523971 : Blo 1522458 1523971 := bstep (se 1 (by rfl) ⟨1142978, by rfl⟩ : syracuseStep 1523971 = 2285957) B2285957
theorem B5144849 : Blo 1522458 5144849 := bstep (se 2 (by rfl) ⟨1929318, by rfl⟩ : syracuseStep 5144849 = 3858637) B3858637
theorem B2285843 : Blo 1522458 2285843 := bstep (se 1 (by rfl) ⟨1714382, by rfl⟩ : syracuseStep 2285843 = 3428765) B3428765
theorem B1523987 : Blo 1522458 1523987 := bstep (se 1 (by rfl) ⟨1142990, by rfl⟩ : syracuseStep 1523987 = 2285981) B2285981
theorem B1524003 : Blo 1522458 1524003 := bstep (se 1 (by rfl) ⟨1143002, by rfl⟩ : syracuseStep 1524003 = 2286005) B2286005
theorem B2285873 : Blo 1522458 2285873 := bstep (se 2 (by rfl) ⟨857202, by rfl⟩ : syracuseStep 2285873 = 1714405) B1714405
theorem B1524019 : Blo 1522458 1524019 := bstep (se 1 (by rfl) ⟨1143014, by rfl⟩ : syracuseStep 1524019 = 2286029) B2286029
theorem B2285891 : Blo 1522458 2285891 := bstep (se 1 (by rfl) ⟨1714418, by rfl⟩ : syracuseStep 2285891 = 3428837) B3428837
theorem B1524035 : Blo 1522458 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B1524051 : Blo 1522458 1524051 := bstep (se 1 (by rfl) ⟨1143038, by rfl⟩ : syracuseStep 1524051 = 2286077) B2286077
theorem B2285921 : Blo 1522458 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B9757027 : Blo 1522458 9757027 := bstep (se 1 (by rfl) ⟨7317770, by rfl⟩ : syracuseStep 9757027 = 14635541) B14635541
theorem B1524067 : Blo 1522458 1524067 := bstep (se 1 (by rfl) ⟨1143050, by rfl⟩ : syracuseStep 1524067 = 2286101) B2286101
theorem B2285939 : Blo 1522458 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B1524083 : Blo 1522458 1524083 := bstep (se 1 (by rfl) ⟨1143062, by rfl⟩ : syracuseStep 1524083 = 2286125) B2286125
theorem B1524099 : Blo 1522458 1524099 := bstep (se 1 (by rfl) ⟨1143074, by rfl⟩ : syracuseStep 1524099 = 2286149) B2286149
theorem B2933123 : Blo 1522458 2933123 := bstep (se 1 (by rfl) ⟨2199842, by rfl⟩ : syracuseStep 2933123 = 4399685) B4399685
theorem B2285969 : Blo 1522458 2285969 := bstep (se 2 (by rfl) ⟨857238, by rfl⟩ : syracuseStep 2285969 = 1714477) B1714477
theorem B1524115 : Blo 1522458 1524115 := bstep (se 1 (by rfl) ⟨1143086, by rfl⟩ : syracuseStep 1524115 = 2286173) B2286173
theorem B2285987 : Blo 1522458 2285987 := bstep (se 1 (by rfl) ⟨1714490, by rfl⟩ : syracuseStep 2285987 = 3428981) B3428981
theorem B1524131 : Blo 1522458 1524131 := bstep (se 1 (by rfl) ⟨1143098, by rfl⟩ : syracuseStep 1524131 = 2286197) B2286197
theorem B1524147 : Blo 1522458 1524147 := bstep (se 1 (by rfl) ⟨1143110, by rfl⟩ : syracuseStep 1524147 = 2286221) B2286221
theorem B2286017 : Blo 1522458 2286017 := bstep (se 2 (by rfl) ⟨857256, by rfl⟩ : syracuseStep 2286017 = 1714513) B1714513
theorem B1524163 : Blo 1522458 1524163 := bstep (se 1 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 1524163 = 2286245) B2286245
theorem B2286035 : Blo 1522458 2286035 := bstep (se 1 (by rfl) ⟨1714526, by rfl⟩ : syracuseStep 2286035 = 3429053) B3429053
theorem B1524179 : Blo 1522458 1524179 := bstep (se 1 (by rfl) ⟨1143134, by rfl⟩ : syracuseStep 1524179 = 2286269) B2286269
theorem B1524195 : Blo 1522458 1524195 := bstep (se 1 (by rfl) ⟨1143146, by rfl⟩ : syracuseStep 1524195 = 2286293) B2286293
theorem B2286065 : Blo 1522458 2286065 := bstep (se 2 (by rfl) ⟨857274, by rfl⟩ : syracuseStep 2286065 = 1714549) B1714549
theorem B1524211 : Blo 1522458 1524211 := bstep (se 1 (by rfl) ⟨1143158, by rfl⟩ : syracuseStep 1524211 = 2286317) B2286317
theorem B2286083 : Blo 1522458 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B1524227 : Blo 1522458 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B5489165 : Blo 1522458 5489165 := bstep (se 3 (by rfl) ⟨1029218, by rfl⟩ : syracuseStep 5489165 = 2058437) B2058437
theorem B1524243 : Blo 1522458 1524243 := bstep (se 1 (by rfl) ⟨1143182, by rfl⟩ : syracuseStep 1524243 = 2286365) B2286365
theorem B2286113 : Blo 1522458 2286113 := bstep (se 2 (by rfl) ⟨857292, by rfl⟩ : syracuseStep 2286113 = 1714585) B1714585
theorem B2892323 : Blo 1522458 2892323 := bstep (se 1 (by rfl) ⟨2169242, by rfl⟩ : syracuseStep 2892323 = 4338485) B4338485
theorem B1524259 : Blo 1522458 1524259 := bstep (se 1 (by rfl) ⟨1143194, by rfl⟩ : syracuseStep 1524259 = 2286389) B2286389
theorem B2286131 : Blo 1522458 2286131 := bstep (se 1 (by rfl) ⟨1714598, by rfl⟩ : syracuseStep 2286131 = 3429197) B3429197
theorem B1524275 : Blo 1522458 1524275 := bstep (se 1 (by rfl) ⟨1143206, by rfl⟩ : syracuseStep 1524275 = 2286413) B2286413
theorem B1524291 : Blo 1522458 1524291 := bstep (se 1 (by rfl) ⟨1143218, by rfl⟩ : syracuseStep 1524291 = 2286437) B2286437
theorem B2286161 : Blo 1522458 2286161 := bstep (se 2 (by rfl) ⟨857310, by rfl⟩ : syracuseStep 2286161 = 1714621) B1714621
theorem B1524307 : Blo 1522458 1524307 := bstep (se 1 (by rfl) ⟨1143230, by rfl⟩ : syracuseStep 1524307 = 2286461) B2286461
theorem B2286179 : Blo 1522458 2286179 := bstep (se 1 (by rfl) ⟨1714634, by rfl⟩ : syracuseStep 2286179 = 3429269) B3429269
theorem B1524323 : Blo 1522458 1524323 := bstep (se 1 (by rfl) ⟨1143242, by rfl⟩ : syracuseStep 1524323 = 2286485) B2286485
theorem B7316081 : Blo 1522458 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B1524339 : Blo 1522458 1524339 := bstep (se 1 (by rfl) ⟨1143254, by rfl⟩ : syracuseStep 1524339 = 2286509) B2286509
theorem B2286209 : Blo 1522458 2286209 := bstep (se 2 (by rfl) ⟨857328, by rfl⟩ : syracuseStep 2286209 = 1714657) B1714657
theorem B1524355 : Blo 1522458 1524355 := bstep (se 1 (by rfl) ⟨1143266, by rfl⟩ : syracuseStep 1524355 = 2286533) B2286533
theorem B7717517 : Blo 1522458 7717517 := bstep (se 3 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 7717517 = 2894069) B2894069
theorem B2286227 : Blo 1522458 2286227 := bstep (se 1 (by rfl) ⟨1714670, by rfl⟩ : syracuseStep 2286227 = 3429341) B3429341
theorem B1524371 : Blo 1522458 1524371 := bstep (se 1 (by rfl) ⟨1143278, by rfl⟩ : syracuseStep 1524371 = 2286557) B2286557
theorem B1712803 : Blo 1522458 1712803 := bstep (se 1 (by rfl) ⟨1284602, by rfl⟩ : syracuseStep 1712803 = 2569205) B2569205
theorem B1524387 : Blo 1522458 1524387 := bstep (se 1 (by rfl) ⟨1143290, by rfl⟩ : syracuseStep 1524387 = 2286581) B2286581
theorem B2286257 : Blo 1522458 2286257 := bstep (se 2 (by rfl) ⟨857346, by rfl⟩ : syracuseStep 2286257 = 1714693) B1714693
theorem B2933425 : Blo 1522458 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B1524403 : Blo 1522458 1524403 := bstep (se 1 (by rfl) ⟨1143302, by rfl⟩ : syracuseStep 1524403 = 2286605) B2286605
theorem B2286275 : Blo 1522458 2286275 := bstep (se 1 (by rfl) ⟨1714706, by rfl⟩ : syracuseStep 2286275 = 3429413) B3429413
theorem B1524419 : Blo 1522458 1524419 := bstep (se 1 (by rfl) ⟨1143314, by rfl⟩ : syracuseStep 1524419 = 2286629) B2286629
theorem B6177485 : Blo 1522458 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B1524435 : Blo 1522458 1524435 := bstep (se 1 (by rfl) ⟨1143326, by rfl⟩ : syracuseStep 1524435 = 2286653) B2286653
theorem B2286305 : Blo 1522458 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B1524451 : Blo 1522458 1524451 := bstep (se 1 (by rfl) ⟨1143338, by rfl⟩ : syracuseStep 1524451 = 2286677) B2286677
theorem B2286323 : Blo 1522458 2286323 := bstep (se 1 (by rfl) ⟨1714742, by rfl⟩ : syracuseStep 2286323 = 3429485) B3429485
theorem B2286353 : Blo 1522458 2286353 := bstep (se 2 (by rfl) ⟨857382, by rfl⟩ : syracuseStep 2286353 = 1714765) B1714765
theorem B2286371 : Blo 1522458 2286371 := bstep (se 1 (by rfl) ⟨1714778, by rfl⟩ : syracuseStep 2286371 = 3429557) B3429557
theorem B1712947 : Blo 1522458 1712947 := bstep (se 1 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 1712947 = 2569421) B2569421
theorem B2286401 : Blo 1522458 2286401 := bstep (se 2 (by rfl) ⟨857400, by rfl⟩ : syracuseStep 2286401 = 1714801) B1714801
theorem B2892611 : Blo 1522458 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B2286419 : Blo 1522458 2286419 := bstep (se 1 (by rfl) ⟨1714814, by rfl⟩ : syracuseStep 2286419 = 3429629) B3429629
theorem B2286449 : Blo 1522458 2286449 := bstep (se 2 (by rfl) ⟨857418, by rfl⟩ : syracuseStep 2286449 = 1714837) B1714837
theorem B2286467 : Blo 1522458 2286467 := bstep (se 1 (by rfl) ⟨1714850, by rfl⟩ : syracuseStep 2286467 = 3429701) B3429701
theorem B16475021 : Blo 1522458 16475021 := bstep (se 3 (by rfl) ⟨3089066, by rfl⟩ : syracuseStep 16475021 = 6178133) B6178133
theorem B2286497 : Blo 1522458 2286497 := bstep (se 2 (by rfl) ⟨857436, by rfl⟩ : syracuseStep 2286497 = 1714873) B1714873
theorem B2286515 : Blo 1522458 2286515 := bstep (se 1 (by rfl) ⟨1714886, by rfl⟩ : syracuseStep 2286515 = 3429773) B3429773
theorem B1713091 : Blo 1522458 1713091 := bstep (se 1 (by rfl) ⟨1284818, by rfl⟩ : syracuseStep 1713091 = 2569637) B2569637
theorem B2286545 : Blo 1522458 2286545 := bstep (se 2 (by rfl) ⟨857454, by rfl⟩ : syracuseStep 2286545 = 1714909) B1714909
theorem B2286563 : Blo 1522458 2286563 := bstep (se 1 (by rfl) ⟨1714922, by rfl⟩ : syracuseStep 2286563 = 3429845) B3429845
theorem B2286593 : Blo 1522458 2286593 := bstep (se 2 (by rfl) ⟨857472, by rfl⟩ : syracuseStep 2286593 = 1714945) B1714945
theorem B2286611 : Blo 1522458 2286611 := bstep (se 1 (by rfl) ⟨1714958, by rfl⟩ : syracuseStep 2286611 = 3429917) B3429917
theorem B2286641 : Blo 1522458 2286641 := bstep (se 2 (by rfl) ⟨857490, by rfl⟩ : syracuseStep 2286641 = 1714981) B1714981
theorem B2286659 : Blo 1522458 2286659 := bstep (se 1 (by rfl) ⟨1714994, by rfl⟩ : syracuseStep 2286659 = 3429989) B3429989
theorem B4883537 : Blo 1522458 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B1713235 : Blo 1522458 1713235 := bstep (se 1 (by rfl) ⟨1284926, by rfl⟩ : syracuseStep 1713235 = 2569853) B2569853
theorem B1713379 : Blo 1522458 1713379 := bstep (se 1 (by rfl) ⟨1285034, by rfl⟩ : syracuseStep 1713379 = 2570069) B2570069
theorem B9758029 : Blo 1522458 9758029 := bstep (se 3 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 9758029 = 3659261) B3659261
theorem B7710065 : Blo 1522458 7710065 := bstep (se 2 (by rfl) ⟨2891274, by rfl⟩ : syracuseStep 7710065 = 5782549) B5782549
theorem B1713523 : Blo 1522458 1713523 := bstep (se 1 (by rfl) ⟨1285142, by rfl⟩ : syracuseStep 1713523 = 2570285) B2570285
theorem B3425777 : Blo 1522458 3425777 := bstep (se 2 (by rfl) ⟨1284666, by rfl⟩ : syracuseStep 3425777 = 2569333) B2569333
theorem B3425795 : Blo 1522458 3425795 := bstep (se 1 (by rfl) ⟨2569346, by rfl⟩ : syracuseStep 3425795 = 5138693) B5138693
theorem B1713667 : Blo 1522458 1713667 := bstep (se 1 (by rfl) ⟨1285250, by rfl⟩ : syracuseStep 1713667 = 2570501) B2570501
theorem B19531277 : Blo 1522458 19531277 := bstep (se 3 (by rfl) ⟨3662114, by rfl⟩ : syracuseStep 19531277 = 7324229) B7324229
theorem B5490289 : Blo 1522458 5490289 := bstep (se 2 (by rfl) ⟨2058858, by rfl⟩ : syracuseStep 5490289 = 4117717) B4117717
theorem B1713811 : Blo 1522458 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B6506189 : Blo 1522458 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B8234723 : Blo 1522458 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B55592675 : Blo 1522458 55592675 := bstep (se 1 (by rfl) ⟨41694506, by rfl⟩ : syracuseStep 55592675 = 83389013) B83389013
theorem B2893553 : Blo 1522458 2893553 := bstep (se 2 (by rfl) ⟨1085082, by rfl⟩ : syracuseStep 2893553 = 2170165) B2170165
theorem B3426065 : Blo 1522458 3426065 := bstep (se 2 (by rfl) ⟨1284774, by rfl⟩ : syracuseStep 3426065 = 2569549) B2569549
theorem B3426083 : Blo 1522458 3426083 := bstep (se 1 (by rfl) ⟨2569562, by rfl⟩ : syracuseStep 3426083 = 5139125) B5139125
theorem B1713955 : Blo 1522458 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B3254051 : Blo 1522458 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B1927091 : Blo 1522458 1927091 := bstep (se 1 (by rfl) ⟨1445318, by rfl⟩ : syracuseStep 1927091 = 2890637) B2890637
theorem B1714099 : Blo 1522458 1714099 := bstep (se 1 (by rfl) ⟨1285574, by rfl⟩ : syracuseStep 1714099 = 2571149) B2571149
theorem B2197441 : Blo 1522458 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B4335569 : Blo 1522458 4335569 := bstep (se 2 (by rfl) ⟨1625838, by rfl⟩ : syracuseStep 4335569 = 3251677) B3251677
theorem B2607059 : Blo 1522458 2607059 := bstep (se 1 (by rfl) ⟨1955294, by rfl⟩ : syracuseStep 2607059 = 3910589) B3910589
theorem B6506531 : Blo 1522458 6506531 := bstep (se 1 (by rfl) ⟨4879898, by rfl⟩ : syracuseStep 6506531 = 9759797) B9759797
theorem B5138477 : Blo 1522458 5138477 := bstep (se 3 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 5138477 = 1926929) B1926929
theorem B3426353 : Blo 1522458 3426353 := bstep (se 2 (by rfl) ⟨1284882, by rfl⟩ : syracuseStep 3426353 = 2569765) B2569765
theorem B3426371 : Blo 1522458 3426371 := bstep (se 1 (by rfl) ⟨2569778, by rfl⟩ : syracuseStep 3426371 = 5139557) B5139557
theorem B1714243 : Blo 1522458 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B5138531 : Blo 1522458 5138531 := bstep (se 1 (by rfl) ⟨3853898, by rfl⟩ : syracuseStep 5138531 = 7707797) B7707797
theorem B19515491 : Blo 1522458 19515491 := bstep (se 1 (by rfl) ⟨14636618, by rfl⟩ : syracuseStep 19515491 = 29273237) B29273237
theorem B1714387 : Blo 1522458 1714387 := bstep (se 1 (by rfl) ⟨1285790, by rfl⟩ : syracuseStep 1714387 = 2571581) B2571581
theorem B2640131 : Blo 1522458 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B9161009 : Blo 1522458 9161009 := bstep (se 2 (by rfl) ⟨3435378, by rfl⟩ : syracuseStep 9161009 = 6870757) B6870757
theorem B3426641 : Blo 1522458 3426641 := bstep (se 2 (by rfl) ⟨1284990, by rfl⟩ : syracuseStep 3426641 = 2569981) B2569981
theorem B3426659 : Blo 1522458 3426659 := bstep (se 1 (by rfl) ⟨2569994, by rfl⟩ : syracuseStep 3426659 = 5139989) B5139989
theorem B1714531 : Blo 1522458 1714531 := bstep (se 1 (by rfl) ⟨1285898, by rfl⟩ : syracuseStep 1714531 = 2571797) B2571797
theorem B5138801 : Blo 1522458 5138801 := bstep (se 2 (by rfl) ⟨1927050, by rfl⟩ : syracuseStep 5138801 = 3854101) B3854101
theorem B1829251 : Blo 1522458 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B7317965 : Blo 1522458 7317965 := bstep (se 3 (by rfl) ⟨1372118, by rfl⟩ : syracuseStep 7317965 = 2744237) B2744237
theorem B6506993 : Blo 1522458 6506993 := bstep (se 2 (by rfl) ⟨2440122, by rfl⟩ : syracuseStep 6506993 = 4880245) B4880245
theorem B1714675 : Blo 1522458 1714675 := bstep (se 1 (by rfl) ⟨1286006, by rfl⟩ : syracuseStep 1714675 = 2572013) B2572013
theorem B3426929 : Blo 1522458 3426929 := bstep (se 2 (by rfl) ⟨1285098, by rfl⟩ : syracuseStep 3426929 = 2570197) B2570197
theorem B5786225 : Blo 1522458 5786225 := bstep (se 2 (by rfl) ⟨2169834, by rfl⟩ : syracuseStep 5786225 = 4339669) B4339669
theorem B1927795 : Blo 1522458 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B9767537 : Blo 1522458 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B3426947 : Blo 1522458 3426947 := bstep (se 1 (by rfl) ⟨2570210, by rfl⟩ : syracuseStep 3426947 = 5140421) B5140421
theorem B1714819 : Blo 1522458 1714819 := bstep (se 1 (by rfl) ⟨1286114, by rfl⟩ : syracuseStep 1714819 = 2572229) B2572229
theorem B3910339 : Blo 1522458 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B1927891 : Blo 1522458 1927891 := bstep (se 1 (by rfl) ⟨1445918, by rfl⟩ : syracuseStep 1927891 = 2891837) B2891837
theorem B4336355 : Blo 1522458 4336355 := bstep (se 1 (by rfl) ⟨3252266, by rfl⟩ : syracuseStep 4336355 = 6504533) B6504533
theorem B1714963 : Blo 1522458 1714963 := bstep (se 1 (by rfl) ⟨1286222, by rfl⟩ : syracuseStep 1714963 = 2572445) B2572445
theorem B42257173 : Blo 1522458 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B7711523 : Blo 1522458 7711523 := bstep (se 1 (by rfl) ⟨5783642, by rfl⟩ : syracuseStep 7711523 = 11567285) B11567285
theorem B4631363 : Blo 1522458 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B5139341 : Blo 1522458 5139341 := bstep (se 3 (by rfl) ⟨963626, by rfl⟩ : syracuseStep 5139341 = 1927253) B1927253
theorem B3427217 : Blo 1522458 3427217 := bstep (se 2 (by rfl) ⟨1285206, by rfl⟩ : syracuseStep 3427217 = 2570413) B2570413
theorem B3427235 : Blo 1522458 3427235 := bstep (se 1 (by rfl) ⟨2570426, by rfl⟩ : syracuseStep 3427235 = 5140853) B5140853
theorem B5139395 : Blo 1522458 5139395 := bstep (se 1 (by rfl) ⟨3854546, by rfl⟩ : syracuseStep 5139395 = 7709093) B7709093
theorem B13020101 : Blo 1522458 13020101 := bstep (se 4 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 13020101 = 2441269) B2441269
theorem B3255299 : Blo 1522458 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B4336685 : Blo 1522458 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B4336753 : Blo 1522458 4336753 := bstep (se 2 (by rfl) ⟨1626282, by rfl⟩ : syracuseStep 4336753 = 3252565) B3252565
theorem B4877489 : Blo 1522458 4877489 := bstep (se 2 (by rfl) ⟨1829058, by rfl⟩ : syracuseStep 4877489 = 3658117) B3658117
theorem B3427505 : Blo 1522458 3427505 := bstep (se 2 (by rfl) ⟨1285314, by rfl⟩ : syracuseStep 3427505 = 2570629) B2570629
theorem B3427523 : Blo 1522458 3427523 := bstep (se 1 (by rfl) ⟨2570642, by rfl⟩ : syracuseStep 3427523 = 5141285) B5141285
theorem B1928387 : Blo 1522458 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B5139665 : Blo 1522458 5139665 := bstep (se 2 (by rfl) ⟨1927374, by rfl⟩ : syracuseStep 5139665 = 3854749) B3854749
theorem B9268465 : Blo 1522458 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B4337027 : Blo 1522458 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B1830323 : Blo 1522458 1830323 := bstep (se 1 (by rfl) ⟨1372742, by rfl⟩ : syracuseStep 1830323 = 2745485) B2745485
theorem B3853777 : Blo 1522458 3853777 := bstep (se 2 (by rfl) ⟨1445166, by rfl⟩ : syracuseStep 3853777 = 2890333) B2890333
theorem B3427793 : Blo 1522458 3427793 := bstep (se 2 (by rfl) ⟨1285422, by rfl⟩ : syracuseStep 3427793 = 2570845) B2570845
theorem B37047779 : Blo 1522458 37047779 := bstep (se 1 (by rfl) ⟨27785834, by rfl⟩ : syracuseStep 37047779 = 55571669) B55571669
theorem B3427811 : Blo 1522458 3427811 := bstep (se 1 (by rfl) ⟨2570858, by rfl⟩ : syracuseStep 3427811 = 5141717) B5141717
theorem B7712333 : Blo 1522458 7712333 := bstep (se 3 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 7712333 = 2892125) B2892125
theorem B8679109 : Blo 1522458 8679109 := bstep (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) B1627333
theorem B3854051 : Blo 1522458 3854051 := bstep (se 1 (by rfl) ⟨2890538, by rfl⟩ : syracuseStep 3854051 = 5781077) B5781077
theorem B5140205 : Blo 1522458 5140205 := bstep (se 3 (by rfl) ⟨963788, by rfl⟩ : syracuseStep 5140205 = 1927577) B1927577
theorem B3428081 : Blo 1522458 3428081 := bstep (se 2 (by rfl) ⟨1285530, by rfl⟩ : syracuseStep 3428081 = 2571061) B2571061
theorem B3428099 : Blo 1522458 3428099 := bstep (se 1 (by rfl) ⟨2571074, by rfl⟩ : syracuseStep 3428099 = 5142149) B5142149
theorem B7819021 : Blo 1522458 7819021 := bstep (se 3 (by rfl) ⟨1466066, by rfl⟩ : syracuseStep 7819021 = 2932133) B2932133
theorem B41676565 : Blo 1522458 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B5140259 : Blo 1522458 5140259 := bstep (se 1 (by rfl) ⟨3855194, by rfl⟩ : syracuseStep 5140259 = 7710389) B7710389
theorem B37564273 : Blo 1522458 37564273 := bstep (se 2 (by rfl) ⟨14086602, by rfl⟩ : syracuseStep 37564273 = 28173205) B28173205
theorem B1929091 : Blo 1522458 1929091 := bstep (se 1 (by rfl) ⟨1446818, by rfl⟩ : syracuseStep 1929091 = 2893637) B2893637
theorem B3854243 : Blo 1522458 3854243 := bstep (se 1 (by rfl) ⟨2890682, by rfl⟩ : syracuseStep 3854243 = 5781365) B5781365
theorem B1929187 : Blo 1522458 1929187 := bstep (se 1 (by rfl) ⟨1446890, by rfl⟩ : syracuseStep 1929187 = 2893781) B2893781
theorem B3428369 : Blo 1522458 3428369 := bstep (se 2 (by rfl) ⟨1285638, by rfl⟩ : syracuseStep 3428369 = 2571277) B2571277
theorem B3428387 : Blo 1522458 3428387 := bstep (se 1 (by rfl) ⟨2571290, by rfl⟩ : syracuseStep 3428387 = 5142581) B5142581
theorem B5787683 : Blo 1522458 5787683 := bstep (se 1 (by rfl) ⟨4340762, by rfl⟩ : syracuseStep 5787683 = 8681525) B8681525
theorem B5140529 : Blo 1522458 5140529 := bstep (se 2 (by rfl) ⟨1927698, by rfl⟩ : syracuseStep 5140529 = 3855397) B3855397
theorem B4337869 : Blo 1522458 4337869 := bstep (se 3 (by rfl) ⟨813350, by rfl⟩ : syracuseStep 4337869 = 1626701) B1626701
theorem B4878605 : Blo 1522458 4878605 := bstep (se 3 (by rfl) ⟨914738, by rfl⟩ : syracuseStep 4878605 = 1829477) B1829477
theorem B42250517 : Blo 1522458 42250517 := bstep (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) B1980493
theorem B3428657 : Blo 1522458 3428657 := bstep (se 2 (by rfl) ⟨1285746, by rfl⟩ : syracuseStep 3428657 = 2571493) B2571493
theorem B3428675 : Blo 1522458 3428675 := bstep (se 1 (by rfl) ⟨2571506, by rfl⟩ : syracuseStep 3428675 = 5143013) B5143013
theorem B4338029 : Blo 1522458 4338029 := bstep (se 3 (by rfl) ⟨813380, by rfl⟩ : syracuseStep 4338029 = 1626761) B1626761
theorem B37589525 : Blo 1522458 37589525 := bstep (se 6 (by rfl) ⟨881004, by rfl⟩ : syracuseStep 37589525 = 1762009) B1762009
theorem B4338211 : Blo 1522458 4338211 := bstep (se 1 (by rfl) ⟨3253658, by rfl⟩ : syracuseStep 4338211 = 6507317) B6507317
theorem B5141069 : Blo 1522458 5141069 := bstep (se 3 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 5141069 = 1927901) B1927901
theorem B3428945 : Blo 1522458 3428945 := bstep (se 2 (by rfl) ⟨1285854, by rfl⟩ : syracuseStep 3428945 = 2571709) B2571709
theorem B3428963 : Blo 1522458 3428963 := bstep (se 1 (by rfl) ⟨2571722, by rfl⟩ : syracuseStep 3428963 = 5143445) B5143445
theorem B5141123 : Blo 1522458 5141123 := bstep (se 1 (by rfl) ⟨3855842, by rfl⟩ : syracuseStep 5141123 = 7711685) B7711685
theorem B1626851 : Blo 1522458 1626851 := bstep (se 1 (by rfl) ⟨1220138, by rfl⟩ : syracuseStep 1626851 = 2440277) B2440277
theorem B8237837 : Blo 1522458 8237837 := bstep (se 3 (by rfl) ⟨1544594, by rfl⟩ : syracuseStep 8237837 = 3089189) B3089189
theorem B20837189 : Blo 1522458 20837189 := bstep (se 4 (by rfl) ⟨1953486, by rfl⟩ : syracuseStep 20837189 = 3906973) B3906973
theorem B3855185 : Blo 1522458 3855185 := bstep (se 2 (by rfl) ⟨1445694, by rfl⟩ : syracuseStep 3855185 = 2891389) B2891389
theorem B3429233 : Blo 1522458 3429233 := bstep (se 2 (by rfl) ⟨1285962, by rfl⟩ : syracuseStep 3429233 = 2571925) B2571925
theorem B3855235 : Blo 1522458 3855235 := bstep (se 1 (by rfl) ⟨2891426, by rfl⟩ : syracuseStep 3855235 = 5782853) B5782853
theorem B3429251 : Blo 1522458 3429251 := bstep (se 1 (by rfl) ⟨2571938, by rfl⟩ : syracuseStep 3429251 = 5143877) B5143877
theorem B5141393 : Blo 1522458 5141393 := bstep (se 2 (by rfl) ⟨1928022, by rfl⟩ : syracuseStep 5141393 = 3856045) B3856045
theorem B2569171 : Blo 1522458 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B12358669 : Blo 1522458 12358669 := bstep (se 3 (by rfl) ⟨2317250, by rfl⟩ : syracuseStep 12358669 = 4634501) B4634501
theorem B3855377 : Blo 1522458 3855377 := bstep (se 2 (by rfl) ⟨1445766, by rfl⟩ : syracuseStep 3855377 = 2891533) B2891533
theorem B2167841 : Blo 1522458 2167841 := bstep (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) B1625881
theorem B3707939 : Blo 1522458 3707939 := bstep (se 1 (by rfl) ⟨2780954, by rfl⟩ : syracuseStep 3707939 = 5561909) B5561909
theorem B2569313 : Blo 1522458 2569313 := bstep (se 2 (by rfl) ⟨963492, by rfl⟩ : syracuseStep 2569313 = 1926985) B1926985
theorem B4633699 : Blo 1522458 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B2167921 : Blo 1522458 2167921 := bstep (se 2 (by rfl) ⟨812970, by rfl⟩ : syracuseStep 2167921 = 1625941) B1625941
theorem B9270413 : Blo 1522458 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B3429521 : Blo 1522458 3429521 := bstep (se 2 (by rfl) ⟨1286070, by rfl⟩ : syracuseStep 3429521 = 2572141) B2572141
theorem B3429539 : Blo 1522458 3429539 := bstep (se 1 (by rfl) ⟨2572154, by rfl⟩ : syracuseStep 3429539 = 5144309) B5144309
theorem B19510469 : Blo 1522458 19510469 := bstep (se 4 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 19510469 = 3658213) B3658213
theorem B2569441 : Blo 1522458 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B2569475 : Blo 1522458 2569475 := bstep (se 1 (by rfl) ⟨1927106, by rfl⟩ : syracuseStep 2569475 = 3854213) B3854213
theorem B4879693 : Blo 1522458 4879693 := bstep (se 3 (by rfl) ⟨914942, by rfl⟩ : syracuseStep 4879693 = 1829885) B1829885
theorem B2569603 : Blo 1522458 2569603 := bstep (se 1 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 2569603 = 3854405) B3854405
theorem B5141933 : Blo 1522458 5141933 := bstep (se 3 (by rfl) ⟨964112, by rfl⟩ : syracuseStep 5141933 = 1928225) B1928225
theorem B3659185 : Blo 1522458 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B3429809 : Blo 1522458 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B3429827 : Blo 1522458 3429827 := bstep (se 1 (by rfl) ⟨2572370, by rfl⟩ : syracuseStep 3429827 = 5144741) B5144741
theorem B35173829 : Blo 1522458 35173829 := bstep (se 4 (by rfl) ⟨3297546, by rfl⟩ : syracuseStep 35173829 = 6595093) B6595093
theorem B5141987 : Blo 1522458 5141987 := bstep (se 1 (by rfl) ⟨3856490, by rfl⟩ : syracuseStep 5141987 = 7712981) B7712981
theorem B2569745 : Blo 1522458 2569745 := bstep (se 2 (by rfl) ⟨963654, by rfl⟩ : syracuseStep 2569745 = 1927309) B1927309
theorem B2315827 : Blo 1522458 2315827 := bstep (se 1 (by rfl) ⟨1736870, by rfl⟩ : syracuseStep 2315827 = 3473741) B3473741
theorem B5797453 : Blo 1522458 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B5781091 : Blo 1522458 5781091 := bstep (se 1 (by rfl) ⟨4335818, by rfl⟩ : syracuseStep 5781091 = 8671637) B8671637
theorem B8681093 : Blo 1522458 8681093 := bstep (se 4 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 8681093 = 1627705) B1627705
theorem B2569873 : Blo 1522458 2569873 := bstep (se 2 (by rfl) ⟨963702, by rfl⟩ : syracuseStep 2569873 = 1927405) B1927405
theorem B2569907 : Blo 1522458 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B14636771 : Blo 1522458 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B5142257 : Blo 1522458 5142257 := bstep (se 2 (by rfl) ⟨1928346, by rfl⟩ : syracuseStep 5142257 = 3856693) B3856693
theorem B10426097 : Blo 1522458 10426097 := bstep (se 2 (by rfl) ⟨3909786, by rfl⟩ : syracuseStep 10426097 = 7819573) B7819573
theorem B2570035 : Blo 1522458 2570035 := bstep (se 1 (by rfl) ⟨1927526, by rfl⟩ : syracuseStep 2570035 = 3855053) B3855053
theorem B2168707 : Blo 1522458 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B32946061 : Blo 1522458 32946061 := bstep (se 3 (by rfl) ⟨6177386, by rfl⟩ : syracuseStep 32946061 = 12354773) B12354773
theorem B4339601 : Blo 1522458 4339601 := bstep (se 2 (by rfl) ⟨1627350, by rfl⟩ : syracuseStep 4339601 = 3254701) B3254701
theorem B2570177 : Blo 1522458 2570177 := bstep (se 2 (by rfl) ⟨963816, by rfl⟩ : syracuseStep 2570177 = 1927633) B1927633
theorem B6510563 : Blo 1522458 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B3856369 : Blo 1522458 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B2439155 : Blo 1522458 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B20846605 : Blo 1522458 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B2570305 : Blo 1522458 2570305 := bstep (se 2 (by rfl) ⟨963864, by rfl⟩ : syracuseStep 2570305 = 1927729) B1927729
theorem B2570339 : Blo 1522458 2570339 := bstep (se 1 (by rfl) ⟨1927754, by rfl⟩ : syracuseStep 2570339 = 3855509) B3855509
theorem B4118627 : Blo 1522458 4118627 := bstep (se 1 (by rfl) ⟨3088970, by rfl⟩ : syracuseStep 4118627 = 6177941) B6177941
theorem B2283713 : Blo 1522458 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B2283731 : Blo 1522458 2283731 := bstep (se 1 (by rfl) ⟨1712798, by rfl⟩ : syracuseStep 2283731 = 3425597) B3425597
theorem B2570467 : Blo 1522458 2570467 := bstep (se 1 (by rfl) ⟨1927850, by rfl⟩ : syracuseStep 2570467 = 3855701) B3855701
theorem B2283761 : Blo 1522458 2283761 := bstep (se 2 (by rfl) ⟨856410, by rfl⟩ : syracuseStep 2283761 = 1712821) B1712821
theorem B2283779 : Blo 1522458 2283779 := bstep (se 1 (by rfl) ⟨1712834, by rfl⟩ : syracuseStep 2283779 = 3425669) B3425669
theorem B3856643 : Blo 1522458 3856643 := bstep (se 1 (by rfl) ⟨2892482, by rfl⟩ : syracuseStep 3856643 = 5784965) B5784965
theorem B5142797 : Blo 1522458 5142797 := bstep (se 3 (by rfl) ⟨964274, by rfl⟩ : syracuseStep 5142797 = 1928549) B1928549
theorem B83409173 : Blo 1522458 83409173 := bstep (se 6 (by rfl) ⟨1954902, by rfl⟩ : syracuseStep 83409173 = 3909805) B3909805
theorem B2283809 : Blo 1522458 2283809 := bstep (se 2 (by rfl) ⟨856428, by rfl⟩ : syracuseStep 2283809 = 1712857) B1712857
theorem B9394481 : Blo 1522458 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B2283827 : Blo 1522458 2283827 := bstep (se 1 (by rfl) ⟨1712870, by rfl⟩ : syracuseStep 2283827 = 3425741) B3425741
theorem B5142851 : Blo 1522458 5142851 := bstep (se 1 (by rfl) ⟨3857138, by rfl⟩ : syracuseStep 5142851 = 7714277) B7714277
theorem B2283857 : Blo 1522458 2283857 := bstep (se 2 (by rfl) ⟨856446, by rfl⟩ : syracuseStep 2283857 = 1712893) B1712893
theorem B2169185 : Blo 1522458 2169185 := bstep (se 2 (by rfl) ⟨813444, by rfl⟩ : syracuseStep 2169185 = 1626889) B1626889
theorem B2283875 : Blo 1522458 2283875 := bstep (se 1 (by rfl) ⟨1712906, by rfl⟩ : syracuseStep 2283875 = 3425813) B3425813
theorem B11573603 : Blo 1522458 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B2570609 : Blo 1522458 2570609 := bstep (se 2 (by rfl) ⟨963978, by rfl⟩ : syracuseStep 2570609 = 1927957) B1927957
theorem B2283905 : Blo 1522458 2283905 := bstep (se 2 (by rfl) ⟨856464, by rfl⟩ : syracuseStep 2283905 = 1712929) B1712929
theorem B4635011 : Blo 1522458 4635011 := bstep (se 1 (by rfl) ⟨3476258, by rfl⟩ : syracuseStep 4635011 = 6952517) B6952517
theorem B9263501 : Blo 1522458 9263501 := bstep (se 3 (by rfl) ⟨1736906, by rfl⟩ : syracuseStep 9263501 = 3473813) B3473813
theorem B2283923 : Blo 1522458 2283923 := bstep (se 1 (by rfl) ⟨1712942, by rfl⟩ : syracuseStep 2283923 = 3425885) B3425885
theorem B2283953 : Blo 1522458 2283953 := bstep (se 2 (by rfl) ⟨856482, by rfl⟩ : syracuseStep 2283953 = 1712965) B1712965
theorem B7715249 : Blo 1522458 7715249 := bstep (se 2 (by rfl) ⟨2893218, by rfl⟩ : syracuseStep 7715249 = 5786437) B5786437
theorem B2283971 : Blo 1522458 2283971 := bstep (se 1 (by rfl) ⟨1712978, by rfl⟩ : syracuseStep 2283971 = 3425957) B3425957
theorem B3856835 : Blo 1522458 3856835 := bstep (se 1 (by rfl) ⟨2892626, by rfl⟩ : syracuseStep 3856835 = 5785253) B5785253
theorem B2169299 : Blo 1522458 2169299 := bstep (se 1 (by rfl) ⟨1626974, by rfl⟩ : syracuseStep 2169299 = 3253949) B3253949
theorem B2284001 : Blo 1522458 2284001 := bstep (se 2 (by rfl) ⟨856500, by rfl⟩ : syracuseStep 2284001 = 1713001) B1713001
theorem B2570737 : Blo 1522458 2570737 := bstep (se 2 (by rfl) ⟨964026, by rfl⟩ : syracuseStep 2570737 = 1928053) B1928053
theorem B2284019 : Blo 1522458 2284019 := bstep (se 1 (by rfl) ⟨1713014, by rfl⟩ : syracuseStep 2284019 = 3426029) B3426029
theorem B2439667 : Blo 1522458 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B2284049 : Blo 1522458 2284049 := bstep (se 2 (by rfl) ⟨856518, by rfl⟩ : syracuseStep 2284049 = 1713037) B1713037
theorem B2570771 : Blo 1522458 2570771 := bstep (se 1 (by rfl) ⟨1928078, by rfl⟩ : syracuseStep 2570771 = 3856157) B3856157
theorem B2439713 : Blo 1522458 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B2284067 : Blo 1522458 2284067 := bstep (se 1 (by rfl) ⟨1713050, by rfl⟩ : syracuseStep 2284067 = 3426101) B3426101
theorem B2169379 : Blo 1522458 2169379 := bstep (se 1 (by rfl) ⟨1627034, by rfl⟩ : syracuseStep 2169379 = 3254069) B3254069
theorem B2284097 : Blo 1522458 2284097 := bstep (se 2 (by rfl) ⟨856536, by rfl⟩ : syracuseStep 2284097 = 1713073) B1713073
theorem B5143121 : Blo 1522458 5143121 := bstep (se 2 (by rfl) ⟨1928670, by rfl⟩ : syracuseStep 5143121 = 3857341) B3857341
theorem B2284115 : Blo 1522458 2284115 := bstep (se 1 (by rfl) ⟨1713086, by rfl⟩ : syracuseStep 2284115 = 3426173) B3426173
theorem B2284145 : Blo 1522458 2284145 := bstep (se 2 (by rfl) ⟨856554, by rfl⟩ : syracuseStep 2284145 = 1713109) B1713109
theorem B2284163 : Blo 1522458 2284163 := bstep (se 1 (by rfl) ⟨1713122, by rfl⟩ : syracuseStep 2284163 = 3426245) B3426245
theorem B9394829 : Blo 1522458 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B35199629 : Blo 1522458 35199629 := bstep (se 3 (by rfl) ⟨6599930, by rfl⟩ : syracuseStep 35199629 = 13199861) B13199861
theorem B2570899 : Blo 1522458 2570899 := bstep (se 1 (by rfl) ⟨1928174, by rfl⟩ : syracuseStep 2570899 = 3856349) B3856349
theorem B2284193 : Blo 1522458 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B2890417 : Blo 1522458 2890417 := bstep (se 2 (by rfl) ⟨1083906, by rfl⟩ : syracuseStep 2890417 = 2167813) B2167813
theorem B2284211 : Blo 1522458 2284211 := bstep (se 1 (by rfl) ⟨1713158, by rfl⟩ : syracuseStep 2284211 = 3426317) B3426317
theorem B2316995 : Blo 1522458 2316995 := bstep (se 1 (by rfl) ⟨1737746, by rfl⟩ : syracuseStep 2316995 = 3475493) B3475493
theorem B2284241 : Blo 1522458 2284241 := bstep (se 2 (by rfl) ⟨856590, by rfl⟩ : syracuseStep 2284241 = 1713181) B1713181
theorem B2284259 : Blo 1522458 2284259 := bstep (se 1 (by rfl) ⟨1713194, by rfl⟩ : syracuseStep 2284259 = 3426389) B3426389
theorem B2284289 : Blo 1522458 2284289 := bstep (se 2 (by rfl) ⟨856608, by rfl⟩ : syracuseStep 2284289 = 1713217) B1713217
theorem B2284307 : Blo 1522458 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B2571041 : Blo 1522458 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B1522467 : Blo 1522458 1522467 := bstep (se 1 (by rfl) ⟨1141850, by rfl⟩ : syracuseStep 1522467 = 2283701) B2283701
theorem B2284337 : Blo 1522458 2284337 := bstep (se 2 (by rfl) ⟨856626, by rfl⟩ : syracuseStep 2284337 = 1713253) B1713253
theorem B1522483 : Blo 1522458 1522483 := bstep (se 1 (by rfl) ⟨1141862, by rfl⟩ : syracuseStep 1522483 = 2283725) B2283725
theorem B1522499 : Blo 1522458 1522499 := bstep (se 1 (by rfl) ⟨1141874, by rfl⟩ : syracuseStep 1522499 = 2283749) B2283749
theorem B2284355 : Blo 1522458 2284355 := bstep (se 1 (by rfl) ⟨1713266, by rfl⟩ : syracuseStep 2284355 = 3426533) B3426533
theorem B4340557 : Blo 1522458 4340557 := bstep (se 3 (by rfl) ⟨813854, by rfl⟩ : syracuseStep 4340557 = 1627709) B1627709
theorem B1522515 : Blo 1522458 1522515 := bstep (se 1 (by rfl) ⟨1141886, by rfl⟩ : syracuseStep 1522515 = 2283773) B2283773
theorem B2284385 : Blo 1522458 2284385 := bstep (se 2 (by rfl) ⟨856644, by rfl⟩ : syracuseStep 2284385 = 1713289) B1713289
theorem B1522531 : Blo 1522458 1522531 := bstep (se 1 (by rfl) ⟨1141898, by rfl⟩ : syracuseStep 1522531 = 2283797) B2283797
theorem B13007729 : Blo 1522458 13007729 := bstep (se 2 (by rfl) ⟨4877898, by rfl⟩ : syracuseStep 13007729 = 9755797) B9755797
theorem B1522547 : Blo 1522458 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B2284403 : Blo 1522458 2284403 := bstep (se 1 (by rfl) ⟨1713302, by rfl⟩ : syracuseStep 2284403 = 3426605) B3426605
theorem B1522563 : Blo 1522458 1522563 := bstep (se 1 (by rfl) ⟨1141922, by rfl⟩ : syracuseStep 1522563 = 2283845) B2283845
theorem B2284433 : Blo 1522458 2284433 := bstep (se 2 (by rfl) ⟨856662, by rfl⟩ : syracuseStep 2284433 = 1713325) B1713325
theorem B4119437 : Blo 1522458 4119437 := bstep (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) B1544789
theorem B1522579 : Blo 1522458 1522579 := bstep (se 1 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 1522579 = 2283869) B2283869
theorem B2571169 : Blo 1522458 2571169 := bstep (se 2 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 2571169 = 1928377) B1928377
theorem B1522595 : Blo 1522458 1522595 := bstep (se 1 (by rfl) ⟨1141946, by rfl⟩ : syracuseStep 1522595 = 2283893) B2283893
theorem B2284451 : Blo 1522458 2284451 := bstep (se 1 (by rfl) ⟨1713338, by rfl⟩ : syracuseStep 2284451 = 3426677) B3426677
theorem B1522611 : Blo 1522458 1522611 := bstep (se 1 (by rfl) ⟨1141958, by rfl⟩ : syracuseStep 1522611 = 2283917) B2283917
theorem B2284481 : Blo 1522458 2284481 := bstep (se 2 (by rfl) ⟨856680, by rfl⟩ : syracuseStep 2284481 = 1713361) B1713361
theorem B1522627 : Blo 1522458 1522627 := bstep (se 1 (by rfl) ⟨1141970, by rfl⟩ : syracuseStep 1522627 = 2283941) B2283941
theorem B2571203 : Blo 1522458 2571203 := bstep (se 1 (by rfl) ⟨1928402, by rfl⟩ : syracuseStep 2571203 = 3856805) B3856805
theorem B31267781 : Blo 1522458 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B1522643 : Blo 1522458 1522643 := bstep (se 1 (by rfl) ⟨1141982, by rfl⟩ : syracuseStep 1522643 = 2283965) B2283965
theorem B2284499 : Blo 1522458 2284499 := bstep (se 1 (by rfl) ⟨1713374, by rfl⟩ : syracuseStep 2284499 = 3426749) B3426749
theorem B1522659 : Blo 1522458 1522659 := bstep (se 1 (by rfl) ⟨1141994, by rfl⟩ : syracuseStep 1522659 = 2283989) B2283989
theorem B2284529 : Blo 1522458 2284529 := bstep (se 2 (by rfl) ⟨856698, by rfl⟩ : syracuseStep 2284529 = 1713397) B1713397
theorem B1522675 : Blo 1522458 1522675 := bstep (se 1 (by rfl) ⟨1142006, by rfl⟩ : syracuseStep 1522675 = 2284013) B2284013
theorem B1522691 : Blo 1522458 1522691 := bstep (se 1 (by rfl) ⟨1142018, by rfl⟩ : syracuseStep 1522691 = 2284037) B2284037
theorem B2284547 : Blo 1522458 2284547 := bstep (se 1 (by rfl) ⟨1713410, by rfl⟩ : syracuseStep 2284547 = 3426821) B3426821
theorem B1522707 : Blo 1522458 1522707 := bstep (se 1 (by rfl) ⟨1142030, by rfl⟩ : syracuseStep 1522707 = 2284061) B2284061
theorem B2284577 : Blo 1522458 2284577 := bstep (se 2 (by rfl) ⟨856716, by rfl⟩ : syracuseStep 2284577 = 1713433) B1713433
theorem B1522723 : Blo 1522458 1522723 := bstep (se 1 (by rfl) ⟨1142042, by rfl⟩ : syracuseStep 1522723 = 2284085) B2284085
theorem B4340785 : Blo 1522458 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B1522739 : Blo 1522458 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B2284595 : Blo 1522458 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B2890819 : Blo 1522458 2890819 := bstep (se 1 (by rfl) ⟨2168114, by rfl⟩ : syracuseStep 2890819 = 4336229) B4336229
theorem B1522755 : Blo 1522458 1522755 := bstep (se 1 (by rfl) ⟨1142066, by rfl⟩ : syracuseStep 1522755 = 2284133) B2284133
theorem B4881475 : Blo 1522458 4881475 := bstep (se 1 (by rfl) ⟨3661106, by rfl⟩ : syracuseStep 4881475 = 7322213) B7322213
theorem B2571331 : Blo 1522458 2571331 := bstep (se 1 (by rfl) ⟨1928498, by rfl⟩ : syracuseStep 2571331 = 3856997) B3856997
theorem B2284625 : Blo 1522458 2284625 := bstep (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) B1713469
theorem B2169937 : Blo 1522458 2169937 := bstep (se 2 (by rfl) ⟨813726, by rfl⟩ : syracuseStep 2169937 = 1627453) B1627453
theorem B1522771 : Blo 1522458 1522771 := bstep (se 1 (by rfl) ⟨1142078, by rfl⟩ : syracuseStep 1522771 = 2284157) B2284157
theorem B1522787 : Blo 1522458 1522787 := bstep (se 1 (by rfl) ⟨1142090, by rfl⟩ : syracuseStep 1522787 = 2284181) B2284181
theorem B2284643 : Blo 1522458 2284643 := bstep (se 1 (by rfl) ⟨1713482, by rfl⟩ : syracuseStep 2284643 = 3426965) B3426965
theorem B5143661 : Blo 1522458 5143661 := bstep (se 3 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 5143661 = 1928873) B1928873
theorem B2890865 : Blo 1522458 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1522803 : Blo 1522458 1522803 := bstep (se 1 (by rfl) ⟨1142102, by rfl⟩ : syracuseStep 1522803 = 2284205) B2284205
theorem B2284673 : Blo 1522458 2284673 := bstep (se 2 (by rfl) ⟨856752, by rfl⟩ : syracuseStep 2284673 = 1713505) B1713505
theorem B1522819 : Blo 1522458 1522819 := bstep (se 1 (by rfl) ⟨1142114, by rfl⟩ : syracuseStep 1522819 = 2284229) B2284229
theorem B4881539 : Blo 1522458 4881539 := bstep (se 1 (by rfl) ⟨3661154, by rfl⟩ : syracuseStep 4881539 = 7322309) B7322309
theorem B24697997 : Blo 1522458 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B1522835 : Blo 1522458 1522835 := bstep (se 1 (by rfl) ⟨1142126, by rfl⟩ : syracuseStep 1522835 = 2284253) B2284253
theorem B2284691 : Blo 1522458 2284691 := bstep (se 1 (by rfl) ⟨1713518, by rfl⟩ : syracuseStep 2284691 = 3427037) B3427037
theorem B1522851 : Blo 1522458 1522851 := bstep (se 1 (by rfl) ⟨1142138, by rfl⟩ : syracuseStep 1522851 = 2284277) B2284277
theorem B5143715 : Blo 1522458 5143715 := bstep (se 1 (by rfl) ⟨3857786, by rfl⟩ : syracuseStep 5143715 = 7715573) B7715573
theorem B2284721 : Blo 1522458 2284721 := bstep (se 2 (by rfl) ⟨856770, by rfl⟩ : syracuseStep 2284721 = 1713541) B1713541
theorem B1522867 : Blo 1522458 1522867 := bstep (se 1 (by rfl) ⟨1142150, by rfl⟩ : syracuseStep 1522867 = 2284301) B2284301
theorem B2440385 : Blo 1522458 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B1522883 : Blo 1522458 1522883 := bstep (se 1 (by rfl) ⟨1142162, by rfl⟩ : syracuseStep 1522883 = 2284325) B2284325
theorem B2284739 : Blo 1522458 2284739 := bstep (se 1 (by rfl) ⟨1713554, by rfl⟩ : syracuseStep 2284739 = 3427109) B3427109
theorem B4881617 : Blo 1522458 4881617 := bstep (se 2 (by rfl) ⟨1830606, by rfl⟩ : syracuseStep 4881617 = 3661213) B3661213
theorem B2571473 : Blo 1522458 2571473 := bstep (se 2 (by rfl) ⟨964302, by rfl⟩ : syracuseStep 2571473 = 1928605) B1928605
theorem B1522899 : Blo 1522458 1522899 := bstep (se 1 (by rfl) ⟨1142174, by rfl⟩ : syracuseStep 1522899 = 2284349) B2284349
theorem B4340945 : Blo 1522458 4340945 := bstep (se 2 (by rfl) ⟨1627854, by rfl⟩ : syracuseStep 4340945 = 3255709) B3255709
theorem B2284769 : Blo 1522458 2284769 := bstep (se 2 (by rfl) ⟨856788, by rfl⟩ : syracuseStep 2284769 = 1713577) B1713577
theorem B1522915 : Blo 1522458 1522915 := bstep (se 1 (by rfl) ⟨1142186, by rfl⟩ : syracuseStep 1522915 = 2284373) B2284373
theorem B5487857 : Blo 1522458 5487857 := bstep (se 2 (by rfl) ⟨2057946, by rfl⟩ : syracuseStep 5487857 = 4115893) B4115893
theorem B1522931 : Blo 1522458 1522931 := bstep (se 1 (by rfl) ⟨1142198, by rfl⟩ : syracuseStep 1522931 = 2284397) B2284397
theorem B2284787 : Blo 1522458 2284787 := bstep (se 1 (by rfl) ⟨1713590, by rfl⟩ : syracuseStep 2284787 = 3427181) B3427181
theorem B1522947 : Blo 1522458 1522947 := bstep (se 1 (by rfl) ⟨1142210, by rfl⟩ : syracuseStep 1522947 = 2284421) B2284421
theorem B2284817 : Blo 1522458 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B1522963 : Blo 1522458 1522963 := bstep (se 1 (by rfl) ⟨1142222, by rfl⟩ : syracuseStep 1522963 = 2284445) B2284445
theorem B1522979 : Blo 1522458 1522979 := bstep (se 1 (by rfl) ⟨1142234, by rfl⟩ : syracuseStep 1522979 = 2284469) B2284469
theorem B2284835 : Blo 1522458 2284835 := bstep (se 1 (by rfl) ⟨1713626, by rfl⟩ : syracuseStep 2284835 = 3427253) B3427253
theorem B4947245 : Blo 1522458 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B1522995 : Blo 1522458 1522995 := bstep (se 1 (by rfl) ⟨1142246, by rfl⟩ : syracuseStep 1522995 = 2284493) B2284493
theorem B2284865 : Blo 1522458 2284865 := bstep (se 2 (by rfl) ⟨856824, by rfl⟩ : syracuseStep 2284865 = 1713649) B1713649
theorem B1523011 : Blo 1522458 1523011 := bstep (se 1 (by rfl) ⟨1142258, by rfl⟩ : syracuseStep 1523011 = 2284517) B2284517
theorem B4341059 : Blo 1522458 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B2571601 : Blo 1522458 2571601 := bstep (se 2 (by rfl) ⟨964350, by rfl⟩ : syracuseStep 2571601 = 1928701) B1928701
theorem B1523027 : Blo 1522458 1523027 := bstep (se 1 (by rfl) ⟨1142270, by rfl⟩ : syracuseStep 1523027 = 2284541) B2284541
theorem B2284883 : Blo 1522458 2284883 := bstep (se 1 (by rfl) ⟨1713662, by rfl⟩ : syracuseStep 2284883 = 3427325) B3427325
theorem B1523043 : Blo 1522458 1523043 := bstep (se 1 (by rfl) ⟨1142282, by rfl⟩ : syracuseStep 1523043 = 2284565) B2284565
theorem B2284913 : Blo 1522458 2284913 := bstep (se 2 (by rfl) ⟨856842, by rfl⟩ : syracuseStep 2284913 = 1713685) B1713685
theorem B3857777 : Blo 1522458 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B1523059 : Blo 1522458 1523059 := bstep (se 1 (by rfl) ⟨1142294, by rfl⟩ : syracuseStep 1523059 = 2284589) B2284589
theorem B2571635 : Blo 1522458 2571635 := bstep (se 1 (by rfl) ⟨1928726, by rfl⟩ : syracuseStep 2571635 = 3857453) B3857453
theorem B2284931 : Blo 1522458 2284931 := bstep (se 1 (by rfl) ⟨1713698, by rfl⟩ : syracuseStep 2284931 = 3427397) B3427397
theorem B1523075 : Blo 1522458 1523075 := bstep (se 1 (by rfl) ⟨1142306, by rfl⟩ : syracuseStep 1523075 = 2284613) B2284613
theorem B2891153 : Blo 1522458 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B1523091 : Blo 1522458 1523091 := bstep (se 1 (by rfl) ⟨1142318, by rfl⟩ : syracuseStep 1523091 = 2284637) B2284637
theorem B2284961 : Blo 1522458 2284961 := bstep (se 2 (by rfl) ⟨856860, by rfl⟩ : syracuseStep 2284961 = 1713721) B1713721
theorem B1523107 : Blo 1522458 1523107 := bstep (se 1 (by rfl) ⟨1142330, by rfl⟩ : syracuseStep 1523107 = 2284661) B2284661
theorem B3857827 : Blo 1522458 3857827 := bstep (se 1 (by rfl) ⟨2893370, by rfl⟩ : syracuseStep 3857827 = 5786741) B5786741
theorem B5864881 : Blo 1522458 5864881 := bstep (se 2 (by rfl) ⟨2199330, by rfl⟩ : syracuseStep 5864881 = 4398661) B4398661
theorem B5143985 : Blo 1522458 5143985 := bstep (se 2 (by rfl) ⟨1928994, by rfl⟩ : syracuseStep 5143985 = 3857989) B3857989
theorem B1523123 : Blo 1522458 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B2284979 : Blo 1522458 2284979 := bstep (se 1 (by rfl) ⟨1713734, by rfl⟩ : syracuseStep 2284979 = 3427469) B3427469
theorem B1523139 : Blo 1522458 1523139 := bstep (se 1 (by rfl) ⟨1142354, by rfl⟩ : syracuseStep 1523139 = 2284709) B2284709
theorem B2285009 : Blo 1522458 2285009 := bstep (se 2 (by rfl) ⟨856878, by rfl⟩ : syracuseStep 2285009 = 1713757) B1713757
theorem B1523155 : Blo 1522458 1523155 := bstep (se 1 (by rfl) ⟨1142366, by rfl⟩ : syracuseStep 1523155 = 2284733) B2284733
theorem B1523171 : Blo 1522458 1523171 := bstep (se 1 (by rfl) ⟨1142378, by rfl⟩ : syracuseStep 1523171 = 2284757) B2284757
theorem B2285027 : Blo 1522458 2285027 := bstep (se 1 (by rfl) ⟨1713770, by rfl⟩ : syracuseStep 2285027 = 3427541) B3427541
theorem B1523187 : Blo 1522458 1523187 := bstep (se 1 (by rfl) ⟨1142390, by rfl⟩ : syracuseStep 1523187 = 2284781) B2284781
theorem B2571763 : Blo 1522458 2571763 := bstep (se 1 (by rfl) ⟨1928822, by rfl⟩ : syracuseStep 2571763 = 3857645) B3857645
theorem B2285057 : Blo 1522458 2285057 := bstep (se 2 (by rfl) ⟨856896, by rfl⟩ : syracuseStep 2285057 = 1713793) B1713793
theorem B1523203 : Blo 1522458 1523203 := bstep (se 1 (by rfl) ⟨1142402, by rfl⟩ : syracuseStep 1523203 = 2284805) B2284805
theorem B1523219 : Blo 1522458 1523219 := bstep (se 1 (by rfl) ⟨1142414, by rfl⟩ : syracuseStep 1523219 = 2284829) B2284829
theorem B2285075 : Blo 1522458 2285075 := bstep (se 1 (by rfl) ⟨1713806, by rfl⟩ : syracuseStep 2285075 = 3427613) B3427613
theorem B1523235 : Blo 1522458 1523235 := bstep (se 1 (by rfl) ⟨1142426, by rfl⟩ : syracuseStep 1523235 = 2284853) B2284853
theorem B9764387 : Blo 1522458 9764387 := bstep (se 1 (by rfl) ⟨7323290, by rfl⟩ : syracuseStep 9764387 = 14646581) B14646581
theorem B2285105 : Blo 1522458 2285105 := bstep (se 2 (by rfl) ⟨856914, by rfl⟩ : syracuseStep 2285105 = 1713829) B1713829
theorem B3857969 : Blo 1522458 3857969 := bstep (se 2 (by rfl) ⟨1446738, by rfl⟩ : syracuseStep 3857969 = 2893477) B2893477
theorem B1523251 : Blo 1522458 1523251 := bstep (se 1 (by rfl) ⟨1142438, by rfl⟩ : syracuseStep 1523251 = 2284877) B2284877
theorem B1523267 : Blo 1522458 1523267 := bstep (se 1 (by rfl) ⟨1142450, by rfl⟩ : syracuseStep 1523267 = 2284901) B2284901
theorem B2285123 : Blo 1522458 2285123 := bstep (se 1 (by rfl) ⟨1713842, by rfl⟩ : syracuseStep 2285123 = 3427685) B3427685
theorem B1523283 : Blo 1522458 1523283 := bstep (se 1 (by rfl) ⟨1142462, by rfl⟩ : syracuseStep 1523283 = 2284925) B2284925
theorem B2285153 : Blo 1522458 2285153 := bstep (se 2 (by rfl) ⟨856932, by rfl⟩ : syracuseStep 2285153 = 1713865) B1713865
theorem B1523299 : Blo 1522458 1523299 := bstep (se 1 (by rfl) ⟨1142474, by rfl⟩ : syracuseStep 1523299 = 2284949) B2284949
theorem B1523315 : Blo 1522458 1523315 := bstep (se 1 (by rfl) ⟨1142486, by rfl⟩ : syracuseStep 1523315 = 2284973) B2284973
theorem B2285171 : Blo 1522458 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B2571905 : Blo 1522458 2571905 := bstep (se 2 (by rfl) ⟨964464, by rfl⟩ : syracuseStep 2571905 = 1928929) B1928929
theorem B1523331 : Blo 1522458 1523331 := bstep (se 1 (by rfl) ⟨1142498, by rfl⟩ : syracuseStep 1523331 = 2284997) B2284997
theorem B2285201 : Blo 1522458 2285201 := bstep (se 2 (by rfl) ⟨856950, by rfl⟩ : syracuseStep 2285201 = 1713901) B1713901
theorem B1523347 : Blo 1522458 1523347 := bstep (se 1 (by rfl) ⟨1142510, by rfl⟩ : syracuseStep 1523347 = 2285021) B2285021
theorem B1523363 : Blo 1522458 1523363 := bstep (se 1 (by rfl) ⟨1142522, by rfl⟩ : syracuseStep 1523363 = 2285045) B2285045
theorem B2285219 : Blo 1522458 2285219 := bstep (se 1 (by rfl) ⟨1713914, by rfl⟩ : syracuseStep 2285219 = 3427829) B3427829
theorem B2743985 : Blo 1522458 2743985 := bstep (se 2 (by rfl) ⟨1028994, by rfl⟩ : syracuseStep 2743985 = 2057989) B2057989
theorem B1523379 : Blo 1522458 1523379 := bstep (se 1 (by rfl) ⟨1142534, by rfl⟩ : syracuseStep 1523379 = 2285069) B2285069
theorem B2285249 : Blo 1522458 2285249 := bstep (se 2 (by rfl) ⟨856968, by rfl⟩ : syracuseStep 2285249 = 1713937) B1713937
theorem B1523395 : Blo 1522458 1523395 := bstep (se 1 (by rfl) ⟨1142546, by rfl⟩ : syracuseStep 1523395 = 2285093) B2285093
theorem B2440897 : Blo 1522458 2440897 := bstep (se 2 (by rfl) ⟨915336, by rfl⟩ : syracuseStep 2440897 = 1830673) B1830673
theorem B1523411 : Blo 1522458 1523411 := bstep (se 1 (by rfl) ⟨1142558, by rfl⟩ : syracuseStep 1523411 = 2285117) B2285117
theorem B2285267 : Blo 1522458 2285267 := bstep (se 1 (by rfl) ⟨1713950, by rfl⟩ : syracuseStep 2285267 = 3427901) B3427901
theorem B1523427 : Blo 1522458 1523427 := bstep (se 1 (by rfl) ⟨1142570, by rfl⟩ : syracuseStep 1523427 = 2285141) B2285141
theorem B2285297 : Blo 1522458 2285297 := bstep (se 2 (by rfl) ⟨856986, by rfl⟩ : syracuseStep 2285297 = 1713973) B1713973
theorem B1523443 : Blo 1522458 1523443 := bstep (se 1 (by rfl) ⟨1142582, by rfl⟩ : syracuseStep 1523443 = 2285165) B2285165
theorem B2572033 : Blo 1522458 2572033 := bstep (se 2 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 2572033 = 1929025) B1929025
theorem B1523459 : Blo 1522458 1523459 := bstep (se 1 (by rfl) ⟨1142594, by rfl⟩ : syracuseStep 1523459 = 2285189) B2285189
theorem B2285315 : Blo 1522458 2285315 := bstep (se 1 (by rfl) ⟨1713986, by rfl⟩ : syracuseStep 2285315 = 3427973) B3427973
theorem B5783309 : Blo 1522458 5783309 := bstep (se 3 (by rfl) ⟨1084370, by rfl⟩ : syracuseStep 5783309 = 2168741) B2168741
theorem B1523475 : Blo 1522458 1523475 := bstep (se 1 (by rfl) ⟨1142606, by rfl⟩ : syracuseStep 1523475 = 2285213) B2285213
theorem B2285345 : Blo 1522458 2285345 := bstep (se 2 (by rfl) ⟨857004, by rfl⟩ : syracuseStep 2285345 = 1714009) B1714009
theorem B1523491 : Blo 1522458 1523491 := bstep (se 1 (by rfl) ⟨1142618, by rfl⟩ : syracuseStep 1523491 = 2285237) B2285237
theorem B2572067 : Blo 1522458 2572067 := bstep (se 1 (by rfl) ⟨1929050, by rfl⟩ : syracuseStep 2572067 = 3858101) B3858101
theorem B10428209 : Blo 1522458 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B1523507 : Blo 1522458 1523507 := bstep (se 1 (by rfl) ⟨1142630, by rfl⟩ : syracuseStep 1523507 = 2285261) B2285261
theorem B2285363 : Blo 1522458 2285363 := bstep (se 1 (by rfl) ⟨1714022, by rfl⟩ : syracuseStep 2285363 = 3428045) B3428045
theorem B3252035 : Blo 1522458 3252035 := bstep (se 1 (by rfl) ⟨2439026, by rfl⟩ : syracuseStep 3252035 = 4878053) B4878053
theorem B1736515 : Blo 1522458 1736515 := bstep (se 1 (by rfl) ⟨1302386, by rfl⟩ : syracuseStep 1736515 = 2604773) B2604773
theorem B18530117 : Blo 1522458 18530117 := bstep (se 4 (by rfl) ⟨1737198, by rfl⟩ : syracuseStep 18530117 = 3474397) B3474397
theorem B1523523 : Blo 1522458 1523523 := bstep (se 1 (by rfl) ⟨1142642, by rfl⟩ : syracuseStep 1523523 = 2285285) B2285285
theorem B2285393 : Blo 1522458 2285393 := bstep (se 2 (by rfl) ⟨857022, by rfl⟩ : syracuseStep 2285393 = 1714045) B1714045
theorem B1523539 : Blo 1522458 1523539 := bstep (se 1 (by rfl) ⟨1142654, by rfl⟩ : syracuseStep 1523539 = 2285309) B2285309
theorem B1523555 : Blo 1522458 1523555 := bstep (se 1 (by rfl) ⟨1142666, by rfl⟩ : syracuseStep 1523555 = 2285333) B2285333
theorem B2285411 : Blo 1522458 2285411 := bstep (se 1 (by rfl) ⟨1714058, by rfl⟩ : syracuseStep 2285411 = 3428117) B3428117
theorem B7716707 : Blo 1522458 7716707 := bstep (se 1 (by rfl) ⟨5787530, by rfl⟩ : syracuseStep 7716707 = 11575061) B11575061
theorem B1523571 : Blo 1522458 1523571 := bstep (se 1 (by rfl) ⟨1142678, by rfl⟩ : syracuseStep 1523571 = 2285357) B2285357
theorem B2285441 : Blo 1522458 2285441 := bstep (se 2 (by rfl) ⟨857040, by rfl⟩ : syracuseStep 2285441 = 1714081) B1714081
theorem B1523587 : Blo 1522458 1523587 := bstep (se 1 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 1523587 = 2285381) B2285381
theorem B1523603 : Blo 1522458 1523603 := bstep (se 1 (by rfl) ⟨1142702, by rfl⟩ : syracuseStep 1523603 = 2285405) B2285405
theorem B2285459 : Blo 1522458 2285459 := bstep (se 1 (by rfl) ⟨1714094, by rfl⟩ : syracuseStep 2285459 = 3428189) B3428189
theorem B1523619 : Blo 1522458 1523619 := bstep (se 1 (by rfl) ⟨1142714, by rfl⟩ : syracuseStep 1523619 = 2285429) B2285429
theorem B2572195 : Blo 1522458 2572195 := bstep (se 1 (by rfl) ⟨1929146, by rfl⟩ : syracuseStep 2572195 = 3858293) B3858293
theorem B2285489 : Blo 1522458 2285489 := bstep (se 2 (by rfl) ⟨857058, by rfl⟩ : syracuseStep 2285489 = 1714117) B1714117
theorem B1523635 : Blo 1522458 1523635 := bstep (se 1 (by rfl) ⟨1142726, by rfl⟩ : syracuseStep 1523635 = 2285453) B2285453
theorem B1523651 : Blo 1522458 1523651 := bstep (se 1 (by rfl) ⟨1142738, by rfl⟩ : syracuseStep 1523651 = 2285477) B2285477
theorem B2285507 : Blo 1522458 2285507 := bstep (se 1 (by rfl) ⟨1714130, by rfl⟩ : syracuseStep 2285507 = 3428261) B3428261
theorem B5144525 : Blo 1522458 5144525 := bstep (se 3 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 5144525 = 1929197) B1929197
theorem B1523667 : Blo 1522458 1523667 := bstep (se 1 (by rfl) ⟨1142750, by rfl⟩ : syracuseStep 1523667 = 2285501) B2285501
theorem B2285537 : Blo 1522458 2285537 := bstep (se 2 (by rfl) ⟨857076, by rfl⟩ : syracuseStep 2285537 = 1714153) B1714153
theorem B1523683 : Blo 1522458 1523683 := bstep (se 1 (by rfl) ⟨1142762, by rfl⟩ : syracuseStep 1523683 = 2285525) B2285525
theorem B24723427 : Blo 1522458 24723427 := bstep (se 1 (by rfl) ⟨18542570, by rfl⟩ : syracuseStep 24723427 = 37085141) B37085141
theorem B1523699 : Blo 1522458 1523699 := bstep (se 1 (by rfl) ⟨1142774, by rfl⟩ : syracuseStep 1523699 = 2285549) B2285549
theorem B2285555 : Blo 1522458 2285555 := bstep (se 1 (by rfl) ⟨1714166, by rfl⟩ : syracuseStep 2285555 = 3428333) B3428333
theorem B2285579 : Blo 1522458 2285579 := bstep (se 1 (by rfl) ⟨1714184, by rfl⟩ : syracuseStep 2285579 = 3428369) B3428369
theorem B1523723 : Blo 1522458 1523723 := bstep (se 1 (by rfl) ⟨1142792, by rfl⟩ : syracuseStep 1523723 = 2285585) B2285585
theorem B27795473 : Blo 1522458 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B2285591 : Blo 1522458 2285591 := bstep (se 1 (by rfl) ⟨1714193, by rfl⟩ : syracuseStep 2285591 = 3428387) B3428387
theorem B1523735 : Blo 1522458 1523735 := bstep (se 1 (by rfl) ⟨1142801, by rfl⟩ : syracuseStep 1523735 = 2285603) B2285603
theorem B3858455 : Blo 1522458 3858455 := bstep (se 1 (by rfl) ⟨2893841, by rfl⟩ : syracuseStep 3858455 = 5787683) B5787683
theorem B1523755 : Blo 1522458 1523755 := bstep (se 1 (by rfl) ⟨1142816, by rfl⟩ : syracuseStep 1523755 = 2285633) B2285633
theorem B1523767 : Blo 1522458 1523767 := bstep (se 1 (by rfl) ⟨1142825, by rfl⟩ : syracuseStep 1523767 = 2285651) B2285651
theorem B1523787 : Blo 1522458 1523787 := bstep (se 1 (by rfl) ⟨1142840, by rfl⟩ : syracuseStep 1523787 = 2285681) B2285681
theorem B1523799 : Blo 1522458 1523799 := bstep (se 1 (by rfl) ⟨1142849, by rfl⟩ : syracuseStep 1523799 = 2285699) B2285699
theorem B2285657 : Blo 1522458 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B9887837 : Blo 1522458 9887837 := bstep (se 3 (by rfl) ⟨1853969, by rfl⟩ : syracuseStep 9887837 = 3707939) B3707939
theorem B1523819 : Blo 1522458 1523819 := bstep (se 1 (by rfl) ⟨1142864, by rfl⟩ : syracuseStep 1523819 = 2285729) B2285729
theorem B1523831 : Blo 1522458 1523831 := bstep (se 1 (by rfl) ⟨1142873, by rfl⟩ : syracuseStep 1523831 = 2285747) B2285747
theorem B1523851 : Blo 1522458 1523851 := bstep (se 1 (by rfl) ⟨1142888, by rfl⟩ : syracuseStep 1523851 = 2285777) B2285777
theorem B1523863 : Blo 1522458 1523863 := bstep (se 1 (by rfl) ⟨1142897, by rfl⟩ : syracuseStep 1523863 = 2285795) B2285795
theorem B1523883 : Blo 1522458 1523883 := bstep (se 1 (by rfl) ⟨1142912, by rfl⟩ : syracuseStep 1523883 = 2285825) B2285825
theorem B3252403 : Blo 1522458 3252403 := bstep (se 1 (by rfl) ⟨2439302, by rfl⟩ : syracuseStep 3252403 = 4878605) B4878605
theorem B1523895 : Blo 1522458 1523895 := bstep (se 1 (by rfl) ⟨1142921, by rfl⟩ : syracuseStep 1523895 = 2285843) B2285843
theorem B2285771 : Blo 1522458 2285771 := bstep (se 1 (by rfl) ⟨1714328, by rfl⟩ : syracuseStep 2285771 = 3428657) B3428657
theorem B1523915 : Blo 1522458 1523915 := bstep (se 1 (by rfl) ⟨1142936, by rfl⟩ : syracuseStep 1523915 = 2285873) B2285873
theorem B2285783 : Blo 1522458 2285783 := bstep (se 1 (by rfl) ⟨1714337, by rfl⟩ : syracuseStep 2285783 = 3428675) B3428675
theorem B1523927 : Blo 1522458 1523927 := bstep (se 1 (by rfl) ⟨1142945, by rfl⟩ : syracuseStep 1523927 = 2285891) B2285891
theorem B1523947 : Blo 1522458 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B2892019 : Blo 1522458 2892019 := bstep (se 1 (by rfl) ⟨2169014, by rfl⟩ : syracuseStep 2892019 = 4338029) B4338029
theorem B1523959 : Blo 1522458 1523959 := bstep (se 1 (by rfl) ⟨1142969, by rfl⟩ : syracuseStep 1523959 = 2285939) B2285939
theorem B1523979 : Blo 1522458 1523979 := bstep (se 1 (by rfl) ⟨1142984, by rfl⟩ : syracuseStep 1523979 = 2285969) B2285969
theorem B5783825 : Blo 1522458 5783825 := bstep (se 2 (by rfl) ⟨2168934, by rfl⟩ : syracuseStep 5783825 = 4337869) B4337869
theorem B1523991 : Blo 1522458 1523991 := bstep (se 1 (by rfl) ⟨1142993, by rfl⟩ : syracuseStep 1523991 = 2285987) B2285987
theorem B2285849 : Blo 1522458 2285849 := bstep (se 2 (by rfl) ⟨857193, by rfl⟩ : syracuseStep 2285849 = 1714387) B1714387
theorem B1524011 : Blo 1522458 1524011 := bstep (se 1 (by rfl) ⟨1143008, by rfl⟩ : syracuseStep 1524011 = 2286017) B2286017
theorem B1524023 : Blo 1522458 1524023 := bstep (se 1 (by rfl) ⟨1143017, by rfl⟩ : syracuseStep 1524023 = 2286035) B2286035
theorem B1524043 : Blo 1522458 1524043 := bstep (se 1 (by rfl) ⟨1143032, by rfl⟩ : syracuseStep 1524043 = 2286065) B2286065
theorem B1524055 : Blo 1522458 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B25059683 : Blo 1522458 25059683 := bstep (se 1 (by rfl) ⟨18794762, by rfl⟩ : syracuseStep 25059683 = 37589525) B37589525
theorem B1524075 : Blo 1522458 1524075 := bstep (se 1 (by rfl) ⟨1143056, by rfl⟩ : syracuseStep 1524075 = 2286113) B2286113
theorem B1524087 : Blo 1522458 1524087 := bstep (se 1 (by rfl) ⟨1143065, by rfl⟩ : syracuseStep 1524087 = 2286131) B2286131
theorem B2285963 : Blo 1522458 2285963 := bstep (se 1 (by rfl) ⟨1714472, by rfl⟩ : syracuseStep 2285963 = 3428945) B3428945
theorem B1524107 : Blo 1522458 1524107 := bstep (se 1 (by rfl) ⟨1143080, by rfl⟩ : syracuseStep 1524107 = 2286161) B2286161
theorem B2285975 : Blo 1522458 2285975 := bstep (se 1 (by rfl) ⟨1714481, by rfl⟩ : syracuseStep 2285975 = 3428963) B3428963
theorem B1524119 : Blo 1522458 1524119 := bstep (se 1 (by rfl) ⟨1143089, by rfl⟩ : syracuseStep 1524119 = 2286179) B2286179
theorem B1524139 : Blo 1522458 1524139 := bstep (se 1 (by rfl) ⟨1143104, by rfl⟩ : syracuseStep 1524139 = 2286209) B2286209
theorem B5145011 : Blo 1522458 5145011 := bstep (se 1 (by rfl) ⟨3858758, by rfl⟩ : syracuseStep 5145011 = 7717517) B7717517
theorem B1524151 : Blo 1522458 1524151 := bstep (se 1 (by rfl) ⟨1143113, by rfl⟩ : syracuseStep 1524151 = 2286227) B2286227
theorem B1524171 : Blo 1522458 1524171 := bstep (se 1 (by rfl) ⟨1143128, by rfl⟩ : syracuseStep 1524171 = 2286257) B2286257
theorem B1524183 : Blo 1522458 1524183 := bstep (se 1 (by rfl) ⟨1143137, by rfl⟩ : syracuseStep 1524183 = 2286275) B2286275
theorem B13009369 : Blo 1522458 13009369 := bstep (se 2 (by rfl) ⟨4878513, by rfl⟩ : syracuseStep 13009369 = 9757027) B9757027
theorem B2286041 : Blo 1522458 2286041 := bstep (se 2 (by rfl) ⟨857265, by rfl⟩ : syracuseStep 2286041 = 1714531) B1714531
theorem B1524203 : Blo 1522458 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B1524215 : Blo 1522458 1524215 := bstep (se 1 (by rfl) ⟨1143161, by rfl⟩ : syracuseStep 1524215 = 2286323) B2286323
theorem B1524235 : Blo 1522458 1524235 := bstep (se 1 (by rfl) ⟨1143176, by rfl⟩ : syracuseStep 1524235 = 2286353) B2286353
theorem B1524247 : Blo 1522458 1524247 := bstep (se 1 (by rfl) ⟨1143185, by rfl⟩ : syracuseStep 1524247 = 2286371) B2286371
theorem B1524267 : Blo 1522458 1524267 := bstep (se 1 (by rfl) ⟨1143200, by rfl⟩ : syracuseStep 1524267 = 2286401) B2286401
theorem B1524279 : Blo 1522458 1524279 := bstep (se 1 (by rfl) ⟨1143209, by rfl⟩ : syracuseStep 1524279 = 2286419) B2286419
theorem B2286155 : Blo 1522458 2286155 := bstep (se 1 (by rfl) ⟨1714616, by rfl⟩ : syracuseStep 2286155 = 3429233) B3429233
theorem B1524299 : Blo 1522458 1524299 := bstep (se 1 (by rfl) ⟨1143224, by rfl⟩ : syracuseStep 1524299 = 2286449) B2286449
theorem B2286167 : Blo 1522458 2286167 := bstep (se 1 (by rfl) ⟨1714625, by rfl⟩ : syracuseStep 2286167 = 3429251) B3429251
theorem B1524311 : Blo 1522458 1524311 := bstep (se 1 (by rfl) ⟨1143233, by rfl⟩ : syracuseStep 1524311 = 2286467) B2286467
theorem B1524331 : Blo 1522458 1524331 := bstep (se 1 (by rfl) ⟨1143248, by rfl⟩ : syracuseStep 1524331 = 2286497) B2286497
theorem B1524343 : Blo 1522458 1524343 := bstep (se 1 (by rfl) ⟨1143257, by rfl⟩ : syracuseStep 1524343 = 2286515) B2286515
theorem B1524363 : Blo 1522458 1524363 := bstep (se 1 (by rfl) ⟨1143272, by rfl⟩ : syracuseStep 1524363 = 2286545) B2286545
theorem B1524375 : Blo 1522458 1524375 := bstep (se 1 (by rfl) ⟨1143281, by rfl⟩ : syracuseStep 1524375 = 2286563) B2286563
theorem B3252889 : Blo 1522458 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B2286233 : Blo 1522458 2286233 := bstep (se 2 (by rfl) ⟨857337, by rfl⟩ : syracuseStep 2286233 = 1714675) B1714675
theorem B1524395 : Blo 1522458 1524395 := bstep (se 1 (by rfl) ⟨1143296, by rfl⟩ : syracuseStep 1524395 = 2286593) B2286593
theorem B1524407 : Blo 1522458 1524407 := bstep (se 1 (by rfl) ⟨1143305, by rfl⟩ : syracuseStep 1524407 = 2286611) B2286611
theorem B1524427 : Blo 1522458 1524427 := bstep (se 1 (by rfl) ⟨1143320, by rfl⟩ : syracuseStep 1524427 = 2286641) B2286641
theorem B1524439 : Blo 1522458 1524439 := bstep (se 1 (by rfl) ⟨1143329, by rfl⟩ : syracuseStep 1524439 = 2286659) B2286659
theorem B5784281 : Blo 1522458 5784281 := bstep (se 2 (by rfl) ⟨2169105, by rfl⟩ : syracuseStep 5784281 = 4338211) B4338211
theorem B2892505 : Blo 1522458 2892505 := bstep (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) B2169379
theorem B1712875 : Blo 1522458 1712875 := bstep (se 1 (by rfl) ⟨1284656, by rfl⟩ : syracuseStep 1712875 = 2569313) B2569313
theorem B2286347 : Blo 1522458 2286347 := bstep (se 1 (by rfl) ⟨1714760, by rfl⟩ : syracuseStep 2286347 = 3429521) B3429521
theorem B2286359 : Blo 1522458 2286359 := bstep (se 1 (by rfl) ⟨1714769, by rfl⟩ : syracuseStep 2286359 = 3429539) B3429539
theorem B25051949 : Blo 1522458 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B1712983 : Blo 1522458 1712983 := bstep (se 1 (by rfl) ⟨1284737, by rfl⟩ : syracuseStep 1712983 = 2569475) B2569475
theorem B2286425 : Blo 1522458 2286425 := bstep (se 2 (by rfl) ⟨857409, by rfl⟩ : syracuseStep 2286425 = 1714819) B1714819
theorem B5784493 : Blo 1522458 5784493 := bstep (se 3 (by rfl) ⟨1084592, by rfl⟩ : syracuseStep 5784493 = 2169185) B2169185
theorem B2286539 : Blo 1522458 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B2286551 : Blo 1522458 2286551 := bstep (se 1 (by rfl) ⟨1714913, by rfl⟩ : syracuseStep 2286551 = 3429827) B3429827
theorem B13018117 : Blo 1522458 13018117 := bstep (se 4 (by rfl) ⟨1220448, by rfl⟩ : syracuseStep 13018117 = 2440897) B2440897
theorem B1713163 : Blo 1522458 1713163 := bstep (se 1 (by rfl) ⟨1284872, by rfl⟩ : syracuseStep 1713163 = 2569745) B2569745
theorem B2286617 : Blo 1522458 2286617 := bstep (se 2 (by rfl) ⟨857481, by rfl⟩ : syracuseStep 2286617 = 1714963) B1714963
theorem B7709741 : Blo 1522458 7709741 := bstep (se 3 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 7709741 = 2891153) B2891153
theorem B1713271 : Blo 1522458 1713271 := bstep (se 1 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 1713271 = 2569907) B2569907
theorem B9757847 : Blo 1522458 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B5489815 : Blo 1522458 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B37061783 : Blo 1522458 37061783 := bstep (se 1 (by rfl) ⟨27796337, by rfl⟩ : syracuseStep 37061783 = 55592675) B55592675
theorem B5784797 : Blo 1522458 5784797 := bstep (se 3 (by rfl) ⟨1084649, by rfl⟩ : syracuseStep 5784797 = 2169299) B2169299
theorem B2893067 : Blo 1522458 2893067 := bstep (se 1 (by rfl) ⟨2169800, by rfl⟩ : syracuseStep 2893067 = 4339601) B4339601
theorem B3425561 : Blo 1522458 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B1713451 : Blo 1522458 1713451 := bstep (se 1 (by rfl) ⟨1285088, by rfl⟩ : syracuseStep 1713451 = 2570177) B2570177
theorem B1738039 : Blo 1522458 1738039 := bstep (se 1 (by rfl) ⟨1303529, by rfl⟩ : syracuseStep 1738039 = 2607059) B2607059
theorem B3425651 : Blo 1522458 3425651 := bstep (se 1 (by rfl) ⟨2569238, by rfl⟩ : syracuseStep 3425651 = 5138477) B5138477
theorem B31286645 : Blo 1522458 31286645 := bstep (se 5 (by rfl) ⟨1466561, by rfl⟩ : syracuseStep 31286645 = 2933123) B2933123
theorem B3425687 : Blo 1522458 3425687 := bstep (se 1 (by rfl) ⟨2569265, by rfl⟩ : syracuseStep 3425687 = 5138531) B5138531
theorem B13010327 : Blo 1522458 13010327 := bstep (se 1 (by rfl) ⟨9757745, by rfl⟩ : syracuseStep 13010327 = 19515491) B19515491
theorem B1713559 : Blo 1522458 1713559 := bstep (se 1 (by rfl) ⟨1285169, by rfl⟩ : syracuseStep 1713559 = 2570339) B2570339
theorem B2745751 : Blo 1522458 2745751 := bstep (se 1 (by rfl) ⟨2059313, by rfl⟩ : syracuseStep 2745751 = 4118627) B4118627
theorem B2893249 : Blo 1522458 2893249 := bstep (se 2 (by rfl) ⟨1084968, by rfl⟩ : syracuseStep 2893249 = 2169937) B2169937
theorem B6178265 : Blo 1522458 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B3425867 : Blo 1522458 3425867 := bstep (se 1 (by rfl) ⟨2569400, by rfl⟩ : syracuseStep 3425867 = 5138801) B5138801
theorem B1713739 : Blo 1522458 1713739 := bstep (se 1 (by rfl) ⟨1285304, by rfl⟩ : syracuseStep 1713739 = 2570609) B2570609
theorem B3090007 : Blo 1522458 3090007 := bstep (se 1 (by rfl) ⟨2317505, by rfl⟩ : syracuseStep 3090007 = 4635011) B4635011
theorem B3425921 : Blo 1522458 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1713847 : Blo 1522458 1713847 := bstep (se 1 (by rfl) ⟨1285385, by rfl⟩ : syracuseStep 1713847 = 2570771) B2570771
theorem B13010705 : Blo 1522458 13010705 := bstep (se 2 (by rfl) ⟨4879014, by rfl⟩ : syracuseStep 13010705 = 9758029) B9758029
theorem B6506257 : Blo 1522458 6506257 := bstep (se 2 (by rfl) ⟨2439846, by rfl⟩ : syracuseStep 6506257 = 4879693) B4879693
theorem B3426137 : Blo 1522458 3426137 := bstep (se 2 (by rfl) ⟨1284801, by rfl⟩ : syracuseStep 3426137 = 2569603) B2569603
theorem B1714027 : Blo 1522458 1714027 := bstep (se 1 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 1714027 = 2571041) B2571041
theorem B3426227 : Blo 1522458 3426227 := bstep (se 1 (by rfl) ⟨2569670, by rfl⟩ : syracuseStep 3426227 = 5139341) B5139341
theorem B5138369 : Blo 1522458 5138369 := bstep (se 2 (by rfl) ⟨1926888, by rfl⟩ : syracuseStep 5138369 = 3853777) B3853777
theorem B3426263 : Blo 1522458 3426263 := bstep (se 1 (by rfl) ⟨2569697, by rfl⟩ : syracuseStep 3426263 = 5139395) B5139395
theorem B1714135 : Blo 1522458 1714135 := bstep (se 1 (by rfl) ⟨1285601, by rfl⟩ : syracuseStep 1714135 = 2571203) B2571203
theorem B1927243 : Blo 1522458 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B3254359 : Blo 1522458 3254359 := bstep (se 1 (by rfl) ⟨2440769, by rfl⟩ : syracuseStep 3254359 = 4881539) B4881539
theorem B8677469 : Blo 1522458 8677469 := bstep (se 3 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 8677469 = 3254051) B3254051
theorem B3426443 : Blo 1522458 3426443 := bstep (se 1 (by rfl) ⟨2569832, by rfl⟩ : syracuseStep 3426443 = 5139665) B5139665
theorem B3254411 : Blo 1522458 3254411 := bstep (se 1 (by rfl) ⟨2440808, by rfl⟩ : syracuseStep 3254411 = 4881617) B4881617
theorem B1714315 : Blo 1522458 1714315 := bstep (se 1 (by rfl) ⟨1285736, by rfl⟩ : syracuseStep 1714315 = 2571473) B2571473
theorem B2893963 : Blo 1522458 2893963 := bstep (se 1 (by rfl) ⟨2170472, by rfl⟩ : syracuseStep 2893963 = 4340945) B4340945
theorem B3426497 : Blo 1522458 3426497 := bstep (se 2 (by rfl) ⟨1284936, by rfl⟩ : syracuseStep 3426497 = 2569873) B2569873
theorem B2894039 : Blo 1522458 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B1714423 : Blo 1522458 1714423 := bstep (se 1 (by rfl) ⟨1285817, by rfl⟩ : syracuseStep 1714423 = 2571635) B2571635
theorem B55568753 : Blo 1522458 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B3426713 : Blo 1522458 3426713 := bstep (se 2 (by rfl) ⟨1285017, by rfl⟩ : syracuseStep 3426713 = 2570035) B2570035
theorem B1714603 : Blo 1522458 1714603 := bstep (se 1 (by rfl) ⟨1285952, by rfl⟩ : syracuseStep 1714603 = 2571905) B2571905
theorem B1829323 : Blo 1522458 1829323 := bstep (se 1 (by rfl) ⟨1371992, by rfl⟩ : syracuseStep 1829323 = 2743985) B2743985
theorem B5138909 : Blo 1522458 5138909 := bstep (se 3 (by rfl) ⟨963545, by rfl⟩ : syracuseStep 5138909 = 1927091) B1927091
theorem B3426803 : Blo 1522458 3426803 := bstep (se 1 (by rfl) ⟨2570102, by rfl⟩ : syracuseStep 3426803 = 5140205) B5140205
theorem B43928081 : Blo 1522458 43928081 := bstep (se 2 (by rfl) ⟨16473030, by rfl⟩ : syracuseStep 43928081 = 32946061) B32946061
theorem B3426839 : Blo 1522458 3426839 := bstep (se 1 (by rfl) ⟨2570129, by rfl⟩ : syracuseStep 3426839 = 5140259) B5140259
theorem B1714711 : Blo 1522458 1714711 := bstep (se 1 (by rfl) ⟨1286033, by rfl⟩ : syracuseStep 1714711 = 2572067) B2572067
theorem B3427019 : Blo 1522458 3427019 := bstep (se 1 (by rfl) ⟨2570264, by rfl⟩ : syracuseStep 3427019 = 5140529) B5140529
theorem B1714891 : Blo 1522458 1714891 := bstep (se 1 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 1714891 = 2572337) B2572337
theorem B2058967 : Blo 1522458 2058967 := bstep (se 1 (by rfl) ⟨1544225, by rfl⟩ : syracuseStep 2058967 = 3088451) B3088451
theorem B3427073 : Blo 1522458 3427073 := bstep (se 2 (by rfl) ⟨1285152, by rfl⟩ : syracuseStep 3427073 = 2570305) B2570305
theorem B1714999 : Blo 1522458 1714999 := bstep (se 1 (by rfl) ⟨1286249, by rfl⟩ : syracuseStep 1714999 = 2572499) B2572499
theorem B28167011 : Blo 1522458 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B3427289 : Blo 1522458 3427289 := bstep (se 2 (by rfl) ⟨1285233, by rfl⟩ : syracuseStep 3427289 = 2570467) B2570467
theorem B1928215 : Blo 1522458 1928215 := bstep (se 1 (by rfl) ⟨1446161, by rfl⟩ : syracuseStep 1928215 = 2892323) B2892323
theorem B3427379 : Blo 1522458 3427379 := bstep (se 1 (by rfl) ⟨2570534, by rfl⟩ : syracuseStep 3427379 = 5141069) B5141069
theorem B4877387 : Blo 1522458 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B3427415 : Blo 1522458 3427415 := bstep (se 1 (by rfl) ⟨2570561, by rfl⟩ : syracuseStep 3427415 = 5141123) B5141123
theorem B5491891 : Blo 1522458 5491891 := bstep (se 1 (by rfl) ⟨4118918, by rfl⟩ : syracuseStep 5491891 = 8237837) B8237837
theorem B3427595 : Blo 1522458 3427595 := bstep (se 1 (by rfl) ⟨2570696, by rfl⟩ : syracuseStep 3427595 = 5141393) B5141393
theorem B3427649 : Blo 1522458 3427649 := bstep (se 2 (by rfl) ⟨1285368, by rfl⟩ : syracuseStep 3427649 = 2570737) B2570737
theorem B6180275 : Blo 1522458 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B3427865 : Blo 1522458 3427865 := bstep (se 2 (by rfl) ⟨1285449, by rfl⟩ : syracuseStep 3427865 = 2570899) B2570899
theorem B3853889 : Blo 1522458 3853889 := bstep (se 2 (by rfl) ⟨1445208, by rfl⟩ : syracuseStep 3853889 = 2890417) B2890417
theorem B5140043 : Blo 1522458 5140043 := bstep (se 1 (by rfl) ⟨3855032, by rfl⟩ : syracuseStep 5140043 = 7710065) B7710065
theorem B3427955 : Blo 1522458 3427955 := bstep (se 1 (by rfl) ⟨2570966, by rfl⟩ : syracuseStep 3427955 = 5141933) B5141933
theorem B23449219 : Blo 1522458 23449219 := bstep (se 1 (by rfl) ⟨17586914, by rfl⟩ : syracuseStep 23449219 = 35173829) B35173829
theorem B3427991 : Blo 1522458 3427991 := bstep (se 1 (by rfl) ⟨2570993, by rfl⟩ : syracuseStep 3427991 = 5141987) B5141987
theorem B13020851 : Blo 1522458 13020851 := bstep (se 1 (by rfl) ⟨9765638, by rfl⟩ : syracuseStep 13020851 = 19531277) B19531277
theorem B5787395 : Blo 1522458 5787395 := bstep (se 1 (by rfl) ⟨4340546, by rfl⟩ : syracuseStep 5787395 = 8681093) B8681093
theorem B5787409 : Blo 1522458 5787409 := bstep (se 2 (by rfl) ⟨2170278, by rfl⟩ : syracuseStep 5787409 = 4340557) B4340557
theorem B4337459 : Blo 1522458 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B3428171 : Blo 1522458 3428171 := bstep (se 1 (by rfl) ⟨2571128, by rfl⟩ : syracuseStep 3428171 = 5142257) B5142257
theorem B6950731 : Blo 1522458 6950731 := bstep (se 1 (by rfl) ⟨5213048, by rfl⟩ : syracuseStep 6950731 = 10426097) B10426097
theorem B1929035 : Blo 1522458 1929035 := bstep (se 1 (by rfl) ⟨1446776, by rfl⟩ : syracuseStep 1929035 = 2893553) B2893553
theorem B5140313 : Blo 1522458 5140313 := bstep (se 2 (by rfl) ⟨1927617, by rfl⟩ : syracuseStep 5140313 = 3855235) B3855235
theorem B3428225 : Blo 1522458 3428225 := bstep (se 2 (by rfl) ⟨1285584, by rfl⟩ : syracuseStep 3428225 = 2571169) B2571169
theorem B1626103 : Blo 1522458 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B16478225 : Blo 1522458 16478225 := bstep (se 2 (by rfl) ⟨6179334, by rfl⟩ : syracuseStep 16478225 = 12358669) B12358669
theorem B4337687 : Blo 1522458 4337687 := bstep (se 1 (by rfl) ⟨3253265, by rfl⟩ : syracuseStep 4337687 = 6506531) B6506531
theorem B5787713 : Blo 1522458 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B3854425 : Blo 1522458 3854425 := bstep (se 2 (by rfl) ⟨1445409, by rfl⟩ : syracuseStep 3854425 = 2890819) B2890819
theorem B6508633 : Blo 1522458 6508633 := bstep (se 2 (by rfl) ⟨2440737, by rfl⟩ : syracuseStep 6508633 = 4881475) B4881475
theorem B3428441 : Blo 1522458 3428441 := bstep (se 2 (by rfl) ⟨1285665, by rfl⟩ : syracuseStep 3428441 = 2571331) B2571331
theorem B3428531 : Blo 1522458 3428531 := bstep (se 1 (by rfl) ⟨2571398, by rfl⟩ : syracuseStep 3428531 = 5142797) B5142797
theorem B6107339 : Blo 1522458 6107339 := bstep (se 1 (by rfl) ⟨4580504, by rfl⟩ : syracuseStep 6107339 = 9161009) B9161009
theorem B3428567 : Blo 1522458 3428567 := bstep (se 1 (by rfl) ⟨2571425, by rfl⟩ : syracuseStep 3428567 = 5142851) B5142851
theorem B4878643 : Blo 1522458 4878643 := bstep (se 1 (by rfl) ⟨3658982, by rfl⟩ : syracuseStep 4878643 = 7317965) B7317965
theorem B12357953 : Blo 1522458 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B4337995 : Blo 1522458 4337995 := bstep (se 1 (by rfl) ⟨3253496, by rfl⟩ : syracuseStep 4337995 = 6506993) B6506993
theorem B1626475 : Blo 1522458 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B3428747 : Blo 1522458 3428747 := bstep (se 1 (by rfl) ⟨2571560, by rfl⟩ : syracuseStep 3428747 = 5143121) B5143121
theorem B6263219 : Blo 1522458 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B23466419 : Blo 1522458 23466419 := bstep (se 1 (by rfl) ⟨17599814, by rfl⟩ : syracuseStep 23466419 = 35199629) B35199629
theorem B3428801 : Blo 1522458 3428801 := bstep (se 2 (by rfl) ⟨1285800, by rfl⟩ : syracuseStep 3428801 = 2571601) B2571601
theorem B1544663 : Blo 1522458 1544663 := bstep (se 1 (by rfl) ⟨1158497, by rfl⟩ : syracuseStep 1544663 = 2316995) B2316995
theorem B5141015 : Blo 1522458 5141015 := bstep (se 1 (by rfl) ⟨3855761, by rfl⟩ : syracuseStep 5141015 = 7711523) B7711523
theorem B4878913 : Blo 1522458 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B7819841 : Blo 1522458 7819841 := bstep (se 2 (by rfl) ⟨2932440, by rfl⟩ : syracuseStep 7819841 = 5864881) B5864881
theorem B8671819 : Blo 1522458 8671819 := bstep (se 1 (by rfl) ⟨6503864, by rfl⟩ : syracuseStep 8671819 = 13007729) B13007729
theorem B4338269 : Blo 1522458 4338269 := bstep (se 3 (by rfl) ⟨813425, by rfl⟩ : syracuseStep 4338269 = 1626851) B1626851
theorem B20845187 : Blo 1522458 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B8680067 : Blo 1522458 8680067 := bstep (se 1 (by rfl) ⟨6510050, by rfl⟩ : syracuseStep 8680067 = 13020101) B13020101
theorem B3429017 : Blo 1522458 3429017 := bstep (se 2 (by rfl) ⟨1285881, by rfl⟩ : syracuseStep 3429017 = 2571763) B2571763
theorem B3429107 : Blo 1522458 3429107 := bstep (se 1 (by rfl) ⟨2571830, by rfl⟩ : syracuseStep 3429107 = 5143661) B5143661
theorem B7729937 : Blo 1522458 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B3429143 : Blo 1522458 3429143 := bstep (se 1 (by rfl) ⟨2571857, by rfl⟩ : syracuseStep 3429143 = 5143715) B5143715
theorem B1626923 : Blo 1522458 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B7320385 : Blo 1522458 7320385 := bstep (se 2 (by rfl) ⟨2745144, by rfl⟩ : syracuseStep 7320385 = 5490289) B5490289
theorem B3658571 : Blo 1522458 3658571 := bstep (se 1 (by rfl) ⟨2743928, by rfl⟩ : syracuseStep 3658571 = 5487857) B5487857
theorem B8672093 : Blo 1522458 8672093 := bstep (se 3 (by rfl) ⟨1626017, by rfl⟩ : syracuseStep 8672093 = 3252035) B3252035
theorem B7713629 : Blo 1522458 7713629 := bstep (se 3 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 7713629 = 2892611) B2892611
theorem B3298163 : Blo 1522458 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B11572145 : Blo 1522458 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B3429323 : Blo 1522458 3429323 := bstep (se 1 (by rfl) ⟨2571992, by rfl⟩ : syracuseStep 3429323 = 5143985) B5143985
theorem B3429377 : Blo 1522458 3429377 := bstep (se 2 (by rfl) ⟨1286016, by rfl⟩ : syracuseStep 3429377 = 2572033) B2572033
theorem B11719685 : Blo 1522458 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B10425361 : Blo 1522458 10425361 := bstep (se 2 (by rfl) ⟨3909510, by rfl⟩ : syracuseStep 10425361 = 7819021) B7819021
theorem B6509591 : Blo 1522458 6509591 := bstep (se 1 (by rfl) ⟨4882193, by rfl⟩ : syracuseStep 6509591 = 9764387) B9764387
theorem B5141555 : Blo 1522458 5141555 := bstep (se 1 (by rfl) ⟨3856166, by rfl⟩ : syracuseStep 5141555 = 7712333) B7712333
theorem B2315353 : Blo 1522458 2315353 := bstep (se 2 (by rfl) ⟨868257, by rfl⟩ : syracuseStep 2315353 = 1736515) B1736515
theorem B2569367 : Blo 1522458 2569367 := bstep (se 1 (by rfl) ⟨1927025, by rfl⟩ : syracuseStep 2569367 = 3854051) B3854051
theorem B3855539 : Blo 1522458 3855539 := bstep (se 1 (by rfl) ⟨2891654, by rfl⟩ : syracuseStep 3855539 = 5783309) B5783309
theorem B6952139 : Blo 1522458 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B3429593 : Blo 1522458 3429593 := bstep (se 2 (by rfl) ⟨1286097, by rfl⟩ : syracuseStep 3429593 = 2572195) B2572195
theorem B2569495 : Blo 1522458 2569495 := bstep (se 1 (by rfl) ⟨1927121, by rfl⟩ : syracuseStep 2569495 = 3854243) B3854243
theorem B3429683 : Blo 1522458 3429683 := bstep (se 1 (by rfl) ⟨2572262, by rfl⟩ : syracuseStep 3429683 = 5144525) B5144525
theorem B5141825 : Blo 1522458 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B3429719 : Blo 1522458 3429719 := bstep (se 1 (by rfl) ⟨2572289, by rfl⟩ : syracuseStep 3429719 = 5144579) B5144579
theorem B11572631 : Blo 1522458 11572631 := bstep (se 1 (by rfl) ⟨8679473, by rfl⟩ : syracuseStep 11572631 = 17358947) B17358947
theorem B5780909 : Blo 1522458 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B3855833 : Blo 1522458 3855833 := bstep (se 2 (by rfl) ⟨1445937, by rfl⟩ : syracuseStep 3855833 = 2891875) B2891875
theorem B3429899 : Blo 1522458 3429899 := bstep (se 1 (by rfl) ⟨2572424, by rfl⟩ : syracuseStep 3429899 = 5144849) B5144849
theorem B13022765 : Blo 1522458 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B3429953 : Blo 1522458 3429953 := bstep (se 2 (by rfl) ⟨1286232, by rfl⟩ : syracuseStep 3429953 = 2572465) B2572465
theorem B4118323 : Blo 1522458 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B2439001 : Blo 1522458 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B5142365 : Blo 1522458 5142365 := bstep (se 3 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 5142365 = 1928387) B1928387
theorem B13891459 : Blo 1522458 13891459 := bstep (se 1 (by rfl) ⟨10418594, by rfl⟩ : syracuseStep 13891459 = 20837189) B20837189
theorem B2570123 : Blo 1522458 2570123 := bstep (se 1 (by rfl) ⟨1927592, by rfl⟩ : syracuseStep 2570123 = 3855185) B3855185
theorem B10983347 : Blo 1522458 10983347 := bstep (se 1 (by rfl) ⟨8237510, by rfl⟩ : syracuseStep 10983347 = 16475021) B16475021
theorem B2570251 : Blo 1522458 2570251 := bstep (se 1 (by rfl) ⟨1927688, by rfl⟩ : syracuseStep 2570251 = 3855377) B3855377
theorem B13006979 : Blo 1522458 13006979 := bstep (se 1 (by rfl) ⟨9755234, by rfl⟩ : syracuseStep 13006979 = 19510469) B19510469
theorem B2570393 : Blo 1522458 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B2283737 : Blo 1522458 2283737 := bstep (se 2 (by rfl) ⟨856401, by rfl⟩ : syracuseStep 2283737 = 1712803) B1712803
theorem B15644933 : Blo 1522458 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B2570521 : Blo 1522458 2570521 := bstep (se 2 (by rfl) ⟨963945, by rfl⟩ : syracuseStep 2570521 = 1927891) B1927891
theorem B2283851 : Blo 1522458 2283851 := bstep (se 1 (by rfl) ⟨1712888, by rfl⟩ : syracuseStep 2283851 = 3425777) B3425777
theorem B2283863 : Blo 1522458 2283863 := bstep (se 1 (by rfl) ⟨1712897, by rfl⟩ : syracuseStep 2283863 = 3425795) B3425795
theorem B20855141 : Blo 1522458 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B56342897 : Blo 1522458 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B2283929 : Blo 1522458 2283929 := bstep (se 2 (by rfl) ⟨856473, by rfl⟩ : syracuseStep 2283929 = 1712947) B1712947
theorem B4880861 : Blo 1522458 4880861 := bstep (se 3 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 4880861 = 1830323) B1830323
theorem B2284043 : Blo 1522458 2284043 := bstep (se 1 (by rfl) ⟨1713032, by rfl⟩ : syracuseStep 2284043 = 3426065) B3426065
theorem B2284055 : Blo 1522458 2284055 := bstep (se 1 (by rfl) ⟨1713041, by rfl⟩ : syracuseStep 2284055 = 3426083) B3426083
theorem B2284121 : Blo 1522458 2284121 := bstep (se 2 (by rfl) ⟨856545, by rfl⟩ : syracuseStep 2284121 = 1713091) B1713091
theorem B2890379 : Blo 1522458 2890379 := bstep (se 1 (by rfl) ⟨2167784, by rfl⟩ : syracuseStep 2890379 = 4335569) B4335569
theorem B4340375 : Blo 1522458 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B2284235 : Blo 1522458 2284235 := bstep (se 1 (by rfl) ⟨1713176, by rfl⟩ : syracuseStep 2284235 = 3426353) B3426353
theorem B14637773 : Blo 1522458 14637773 := bstep (se 3 (by rfl) ⟨2744582, by rfl⟩ : syracuseStep 14637773 = 5489165) B5489165
theorem B2284247 : Blo 1522458 2284247 := bstep (se 1 (by rfl) ⟨1713185, by rfl⟩ : syracuseStep 2284247 = 3426371) B3426371
theorem B2284313 : Blo 1522458 2284313 := bstep (se 2 (by rfl) ⟨856617, by rfl⟩ : syracuseStep 2284313 = 1713235) B1713235
theorem B1522475 : Blo 1522458 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B1522487 : Blo 1522458 1522487 := bstep (se 1 (by rfl) ⟨1141865, by rfl⟩ : syracuseStep 1522487 = 2283731) B2283731
theorem B2890561 : Blo 1522458 2890561 := bstep (se 2 (by rfl) ⟨1083960, by rfl⟩ : syracuseStep 2890561 = 2167921) B2167921
theorem B5782337 : Blo 1522458 5782337 := bstep (se 2 (by rfl) ⟨2168376, by rfl⟩ : syracuseStep 5782337 = 4336753) B4336753
theorem B1522507 : Blo 1522458 1522507 := bstep (se 1 (by rfl) ⟨1141880, by rfl⟩ : syracuseStep 1522507 = 2283761) B2283761
theorem B1522519 : Blo 1522458 1522519 := bstep (se 1 (by rfl) ⟨1141889, by rfl⟩ : syracuseStep 1522519 = 2283779) B2283779
theorem B1760087 : Blo 1522458 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B2571095 : Blo 1522458 2571095 := bstep (se 1 (by rfl) ⟨1928321, by rfl⟩ : syracuseStep 2571095 = 3856643) B3856643
theorem B55606115 : Blo 1522458 55606115 := bstep (se 1 (by rfl) ⟨41704586, by rfl⟩ : syracuseStep 55606115 = 83409173) B83409173
theorem B1522539 : Blo 1522458 1522539 := bstep (se 1 (by rfl) ⟨1141904, by rfl⟩ : syracuseStep 1522539 = 2283809) B2283809
theorem B1522551 : Blo 1522458 1522551 := bstep (se 1 (by rfl) ⟨1141913, by rfl⟩ : syracuseStep 1522551 = 2283827) B2283827
theorem B1522571 : Blo 1522458 1522571 := bstep (se 1 (by rfl) ⟨1141928, by rfl⟩ : syracuseStep 1522571 = 2283857) B2283857
theorem B2284427 : Blo 1522458 2284427 := bstep (se 1 (by rfl) ⟨1713320, by rfl⟩ : syracuseStep 2284427 = 3426641) B3426641
theorem B1522583 : Blo 1522458 1522583 := bstep (se 1 (by rfl) ⟨1141937, by rfl⟩ : syracuseStep 1522583 = 2283875) B2283875
theorem B2284439 : Blo 1522458 2284439 := bstep (se 1 (by rfl) ⟨1713329, by rfl⟩ : syracuseStep 2284439 = 3426659) B3426659
theorem B7715735 : Blo 1522458 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B1522603 : Blo 1522458 1522603 := bstep (se 1 (by rfl) ⟨1141952, by rfl⟩ : syracuseStep 1522603 = 2283905) B2283905
theorem B6175667 : Blo 1522458 6175667 := bstep (se 1 (by rfl) ⟨4631750, by rfl⟩ : syracuseStep 6175667 = 9263501) B9263501
theorem B1522615 : Blo 1522458 1522615 := bstep (se 1 (by rfl) ⟨1141961, by rfl⟩ : syracuseStep 1522615 = 2283923) B2283923
theorem B1522635 : Blo 1522458 1522635 := bstep (se 1 (by rfl) ⟨1141976, by rfl⟩ : syracuseStep 1522635 = 2283953) B2283953
theorem B5143499 : Blo 1522458 5143499 := bstep (se 1 (by rfl) ⟨3857624, by rfl⟩ : syracuseStep 5143499 = 7715249) B7715249
theorem B1522647 : Blo 1522458 1522647 := bstep (se 1 (by rfl) ⟨1141985, by rfl⟩ : syracuseStep 1522647 = 2283971) B2283971
theorem B2571223 : Blo 1522458 2571223 := bstep (se 1 (by rfl) ⟨1928417, by rfl⟩ : syracuseStep 2571223 = 3856835) B3856835
theorem B2284505 : Blo 1522458 2284505 := bstep (se 2 (by rfl) ⟨856689, by rfl⟩ : syracuseStep 2284505 = 1713379) B1713379
theorem B1522667 : Blo 1522458 1522667 := bstep (se 1 (by rfl) ⟨1142000, by rfl⟩ : syracuseStep 1522667 = 2284001) B2284001
theorem B1522679 : Blo 1522458 1522679 := bstep (se 1 (by rfl) ⟨1142009, by rfl⟩ : syracuseStep 1522679 = 2284019) B2284019
theorem B1522699 : Blo 1522458 1522699 := bstep (se 1 (by rfl) ⟨1142024, by rfl⟩ : syracuseStep 1522699 = 2284049) B2284049
theorem B1522711 : Blo 1522458 1522711 := bstep (se 1 (by rfl) ⟨1142033, by rfl⟩ : syracuseStep 1522711 = 2284067) B2284067
theorem B1522731 : Blo 1522458 1522731 := bstep (se 1 (by rfl) ⟨1142048, by rfl⟩ : syracuseStep 1522731 = 2284097) B2284097
theorem B1522743 : Blo 1522458 1522743 := bstep (se 1 (by rfl) ⟨1142057, by rfl⟩ : syracuseStep 1522743 = 2284115) B2284115
theorem B1522763 : Blo 1522458 1522763 := bstep (se 1 (by rfl) ⟨1142072, by rfl⟩ : syracuseStep 1522763 = 2284145) B2284145
theorem B2284619 : Blo 1522458 2284619 := bstep (se 1 (by rfl) ⟨1713464, by rfl⟩ : syracuseStep 2284619 = 3426929) B3426929
theorem B3857483 : Blo 1522458 3857483 := bstep (se 1 (by rfl) ⟨2893112, by rfl⟩ : syracuseStep 3857483 = 5786225) B5786225
theorem B6511691 : Blo 1522458 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B1522775 : Blo 1522458 1522775 := bstep (se 1 (by rfl) ⟨1142081, by rfl⟩ : syracuseStep 1522775 = 2284163) B2284163
theorem B2284631 : Blo 1522458 2284631 := bstep (se 1 (by rfl) ⟨1713473, by rfl⟩ : syracuseStep 2284631 = 3426947) B3426947
theorem B1522795 : Blo 1522458 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B1522807 : Blo 1522458 1522807 := bstep (se 1 (by rfl) ⟨1142105, by rfl⟩ : syracuseStep 1522807 = 2284211) B2284211
theorem B1522827 : Blo 1522458 1522827 := bstep (se 1 (by rfl) ⟨1142120, by rfl⟩ : syracuseStep 1522827 = 2284241) B2284241
theorem B2890903 : Blo 1522458 2890903 := bstep (se 1 (by rfl) ⟨2168177, by rfl⟩ : syracuseStep 2890903 = 4336355) B4336355
theorem B1522839 : Blo 1522458 1522839 := bstep (se 1 (by rfl) ⟨1142129, by rfl⟩ : syracuseStep 1522839 = 2284259) B2284259
theorem B2284697 : Blo 1522458 2284697 := bstep (se 2 (by rfl) ⟨856761, by rfl⟩ : syracuseStep 2284697 = 1713523) B1713523
theorem B1522859 : Blo 1522458 1522859 := bstep (se 1 (by rfl) ⟨1142144, by rfl⟩ : syracuseStep 1522859 = 2284289) B2284289
theorem B1522871 : Blo 1522458 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B1522891 : Blo 1522458 1522891 := bstep (se 1 (by rfl) ⟨1142168, by rfl⟩ : syracuseStep 1522891 = 2284337) B2284337
theorem B1522903 : Blo 1522458 1522903 := bstep (se 1 (by rfl) ⟨1142177, by rfl⟩ : syracuseStep 1522903 = 2284355) B2284355
theorem B3087575 : Blo 1522458 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B5143769 : Blo 1522458 5143769 := bstep (se 2 (by rfl) ⟨1928913, by rfl⟩ : syracuseStep 5143769 = 3857827) B3857827
theorem B1522923 : Blo 1522458 1522923 := bstep (se 1 (by rfl) ⟨1142192, by rfl⟩ : syracuseStep 1522923 = 2284385) B2284385
theorem B1522935 : Blo 1522458 1522935 := bstep (se 1 (by rfl) ⟨1142201, by rfl⟩ : syracuseStep 1522935 = 2284403) B2284403
theorem B1522955 : Blo 1522458 1522955 := bstep (se 1 (by rfl) ⟨1142216, by rfl⟩ : syracuseStep 1522955 = 2284433) B2284433
theorem B2284811 : Blo 1522458 2284811 := bstep (se 1 (by rfl) ⟨1713608, by rfl⟩ : syracuseStep 2284811 = 3427217) B3427217
theorem B1522967 : Blo 1522458 1522967 := bstep (se 1 (by rfl) ⟨1142225, by rfl⟩ : syracuseStep 1522967 = 2284451) B2284451
theorem B2284823 : Blo 1522458 2284823 := bstep (se 1 (by rfl) ⟨1713617, by rfl⟩ : syracuseStep 2284823 = 3427235) B3427235
theorem B1522987 : Blo 1522458 1522987 := bstep (se 1 (by rfl) ⟨1142240, by rfl⟩ : syracuseStep 1522987 = 2284481) B2284481
theorem B1522999 : Blo 1522458 1522999 := bstep (se 1 (by rfl) ⟨1142249, by rfl⟩ : syracuseStep 1522999 = 2284499) B2284499
theorem B1523019 : Blo 1522458 1523019 := bstep (se 1 (by rfl) ⟨1142264, by rfl⟩ : syracuseStep 1523019 = 2284529) B2284529
theorem B1523031 : Blo 1522458 1523031 := bstep (se 1 (by rfl) ⟨1142273, by rfl⟩ : syracuseStep 1523031 = 2284547) B2284547
theorem B2170199 : Blo 1522458 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B2284889 : Blo 1522458 2284889 := bstep (se 2 (by rfl) ⟨856833, by rfl⟩ : syracuseStep 2284889 = 1713667) B1713667
theorem B1523051 : Blo 1522458 1523051 := bstep (se 1 (by rfl) ⟨1142288, by rfl⟩ : syracuseStep 1523051 = 2284577) B2284577
theorem B2891123 : Blo 1522458 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B1523063 : Blo 1522458 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B1523083 : Blo 1522458 1523083 := bstep (se 1 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 1523083 = 2284625) B2284625
theorem B1523095 : Blo 1522458 1523095 := bstep (se 1 (by rfl) ⟨1142321, by rfl⟩ : syracuseStep 1523095 = 2284643) B2284643
theorem B3087769 : Blo 1522458 3087769 := bstep (se 2 (by rfl) ⟨1157913, by rfl⟩ : syracuseStep 3087769 = 2315827) B2315827
theorem B1523115 : Blo 1522458 1523115 := bstep (se 1 (by rfl) ⟨1142336, by rfl⟩ : syracuseStep 1523115 = 2284673) B2284673
theorem B16465331 : Blo 1522458 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B1523127 : Blo 1522458 1523127 := bstep (se 1 (by rfl) ⟨1142345, by rfl⟩ : syracuseStep 1523127 = 2284691) B2284691
theorem B3251659 : Blo 1522458 3251659 := bstep (se 1 (by rfl) ⟨2438744, by rfl⟩ : syracuseStep 3251659 = 4877489) B4877489
theorem B1523147 : Blo 1522458 1523147 := bstep (se 1 (by rfl) ⟨1142360, by rfl⟩ : syracuseStep 1523147 = 2284721) B2284721
theorem B2285003 : Blo 1522458 2285003 := bstep (se 1 (by rfl) ⟨1713752, by rfl⟩ : syracuseStep 2285003 = 3427505) B3427505
theorem B1523159 : Blo 1522458 1523159 := bstep (se 1 (by rfl) ⟨1142369, by rfl⟩ : syracuseStep 1523159 = 2284739) B2284739
theorem B2285015 : Blo 1522458 2285015 := bstep (se 1 (by rfl) ⟨1713761, by rfl⟩ : syracuseStep 2285015 = 3427523) B3427523
theorem B7708121 : Blo 1522458 7708121 := bstep (se 2 (by rfl) ⟨2890545, by rfl⟩ : syracuseStep 7708121 = 5781091) B5781091
theorem B1523179 : Blo 1522458 1523179 := bstep (se 1 (by rfl) ⟨1142384, by rfl⟩ : syracuseStep 1523179 = 2284769) B2284769
theorem B1523191 : Blo 1522458 1523191 := bstep (se 1 (by rfl) ⟨1142393, by rfl⟩ : syracuseStep 1523191 = 2284787) B2284787
theorem B1523211 : Blo 1522458 1523211 := bstep (se 1 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 1523211 = 2284817) B2284817
theorem B1523223 : Blo 1522458 1523223 := bstep (se 1 (by rfl) ⟨1142417, by rfl⟩ : syracuseStep 1523223 = 2284835) B2284835
theorem B2285081 : Blo 1522458 2285081 := bstep (se 2 (by rfl) ⟨856905, by rfl⟩ : syracuseStep 2285081 = 1713811) B1713811
theorem B1523243 : Blo 1522458 1523243 := bstep (se 1 (by rfl) ⟨1142432, by rfl⟩ : syracuseStep 1523243 = 2284865) B2284865
theorem B1523255 : Blo 1522458 1523255 := bstep (se 1 (by rfl) ⟨1142441, by rfl⟩ : syracuseStep 1523255 = 2284883) B2284883
theorem B1523275 : Blo 1522458 1523275 := bstep (se 1 (by rfl) ⟨1142456, by rfl⟩ : syracuseStep 1523275 = 2284913) B2284913
theorem B2571851 : Blo 1522458 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B2891351 : Blo 1522458 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B1523287 : Blo 1522458 1523287 := bstep (se 1 (by rfl) ⟨1142465, by rfl⟩ : syracuseStep 1523287 = 2284931) B2284931
theorem B1523307 : Blo 1522458 1523307 := bstep (se 1 (by rfl) ⟨1142480, by rfl⟩ : syracuseStep 1523307 = 2284961) B2284961
theorem B1523319 : Blo 1522458 1523319 := bstep (se 1 (by rfl) ⟨1142489, by rfl⟩ : syracuseStep 1523319 = 2284979) B2284979
theorem B1523339 : Blo 1522458 1523339 := bstep (se 1 (by rfl) ⟨1142504, by rfl⟩ : syracuseStep 1523339 = 2285009) B2285009
theorem B2285195 : Blo 1522458 2285195 := bstep (se 1 (by rfl) ⟨1713896, by rfl⟩ : syracuseStep 2285195 = 3427793) B3427793
theorem B24698519 : Blo 1522458 24698519 := bstep (se 1 (by rfl) ⟨18523889, by rfl⟩ : syracuseStep 24698519 = 37047779) B37047779
theorem B1523351 : Blo 1522458 1523351 := bstep (se 1 (by rfl) ⟨1142513, by rfl⟩ : syracuseStep 1523351 = 2285027) B2285027
theorem B2285207 : Blo 1522458 2285207 := bstep (se 1 (by rfl) ⟨1713905, by rfl⟩ : syracuseStep 2285207 = 3427811) B3427811
theorem B1523371 : Blo 1522458 1523371 := bstep (se 1 (by rfl) ⟨1142528, by rfl⟩ : syracuseStep 1523371 = 2285057) B2285057
theorem B1523383 : Blo 1522458 1523383 := bstep (se 1 (by rfl) ⟨1142537, by rfl⟩ : syracuseStep 1523383 = 2285075) B2285075
theorem B1523403 : Blo 1522458 1523403 := bstep (se 1 (by rfl) ⟨1142552, by rfl⟩ : syracuseStep 1523403 = 2285105) B2285105
theorem B2571979 : Blo 1522458 2571979 := bstep (se 1 (by rfl) ⟨1928984, by rfl⟩ : syracuseStep 2571979 = 3857969) B3857969
theorem B10985165 : Blo 1522458 10985165 := bstep (se 3 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 10985165 = 4119437) B4119437
theorem B1523415 : Blo 1522458 1523415 := bstep (se 1 (by rfl) ⟨1142561, by rfl⟩ : syracuseStep 1523415 = 2285123) B2285123
theorem B2285273 : Blo 1522458 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B1523435 : Blo 1522458 1523435 := bstep (se 1 (by rfl) ⟨1142576, by rfl⟩ : syracuseStep 1523435 = 2285153) B2285153
theorem B1523447 : Blo 1522458 1523447 := bstep (se 1 (by rfl) ⟨1142585, by rfl⟩ : syracuseStep 1523447 = 2285171) B2285171
theorem B1523467 : Blo 1522458 1523467 := bstep (se 1 (by rfl) ⟨1142600, by rfl⟩ : syracuseStep 1523467 = 2285201) B2285201
theorem B1523479 : Blo 1522458 1523479 := bstep (se 1 (by rfl) ⟨1142609, by rfl⟩ : syracuseStep 1523479 = 2285219) B2285219
theorem B1523499 : Blo 1522458 1523499 := bstep (se 1 (by rfl) ⟨1142624, by rfl⟩ : syracuseStep 1523499 = 2285249) B2285249
theorem B1523511 : Blo 1522458 1523511 := bstep (se 1 (by rfl) ⟨1142633, by rfl⟩ : syracuseStep 1523511 = 2285267) B2285267
theorem B50085697 : Blo 1522458 50085697 := bstep (se 2 (by rfl) ⟨18782136, by rfl⟩ : syracuseStep 50085697 = 37564273) B37564273
theorem B1523531 : Blo 1522458 1523531 := bstep (se 1 (by rfl) ⟨1142648, by rfl⟩ : syracuseStep 1523531 = 2285297) B2285297
theorem B2285387 : Blo 1522458 2285387 := bstep (se 1 (by rfl) ⟨1714040, by rfl⟩ : syracuseStep 2285387 = 3428081) B3428081
theorem B1523543 : Blo 1522458 1523543 := bstep (se 1 (by rfl) ⟨1142657, by rfl⟩ : syracuseStep 1523543 = 2285315) B2285315
theorem B2285399 : Blo 1522458 2285399 := bstep (se 1 (by rfl) ⟨1714049, by rfl⟩ : syracuseStep 2285399 = 3428099) B3428099
theorem B2891609 : Blo 1522458 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B2572121 : Blo 1522458 2572121 := bstep (se 2 (by rfl) ⟨964545, by rfl⟩ : syracuseStep 2572121 = 1929091) B1929091
theorem B1523563 : Blo 1522458 1523563 := bstep (se 1 (by rfl) ⟨1142672, by rfl⟩ : syracuseStep 1523563 = 2285345) B2285345
theorem B1523575 : Blo 1522458 1523575 := bstep (se 1 (by rfl) ⟨1142681, by rfl⟩ : syracuseStep 1523575 = 2285363) B2285363
theorem B12353411 : Blo 1522458 12353411 := bstep (se 1 (by rfl) ⟨9265058, by rfl⟩ : syracuseStep 12353411 = 18530117) B18530117
theorem B1523595 : Blo 1522458 1523595 := bstep (se 1 (by rfl) ⟨1142696, by rfl⟩ : syracuseStep 1523595 = 2285393) B2285393
theorem B1523607 : Blo 1522458 1523607 := bstep (se 1 (by rfl) ⟨1142705, by rfl⟩ : syracuseStep 1523607 = 2285411) B2285411
theorem B5144471 : Blo 1522458 5144471 := bstep (se 1 (by rfl) ⟨3858353, by rfl⟩ : syracuseStep 5144471 = 7716707) B7716707
theorem B2285465 : Blo 1522458 2285465 := bstep (se 2 (by rfl) ⟨857049, by rfl⟩ : syracuseStep 2285465 = 1714099) B1714099
theorem B1523627 : Blo 1522458 1523627 := bstep (se 1 (by rfl) ⟨1142720, by rfl⟩ : syracuseStep 1523627 = 2285441) B2285441
theorem B1523639 : Blo 1522458 1523639 := bstep (se 1 (by rfl) ⟨1142729, by rfl⟩ : syracuseStep 1523639 = 2285459) B2285459
theorem B1523659 : Blo 1522458 1523659 := bstep (se 1 (by rfl) ⟨1142744, by rfl⟩ : syracuseStep 1523659 = 2285489) B2285489
theorem B1523671 : Blo 1522458 1523671 := bstep (se 1 (by rfl) ⟨1142753, by rfl⟩ : syracuseStep 1523671 = 2285507) B2285507
theorem B2572249 : Blo 1522458 2572249 := bstep (se 2 (by rfl) ⟨964593, by rfl⟩ : syracuseStep 2572249 = 1929187) B1929187
theorem B32964569 : Blo 1522458 32964569 := bstep (se 2 (by rfl) ⟨12361713, by rfl⟩ : syracuseStep 32964569 = 24723427) B24723427
theorem B1523691 : Blo 1522458 1523691 := bstep (se 1 (by rfl) ⟨1142768, by rfl⟩ : syracuseStep 1523691 = 2285537) B2285537
theorem B1523703 : Blo 1522458 1523703 := bstep (se 1 (by rfl) ⟨1142777, by rfl⟩ : syracuseStep 1523703 = 2285555) B2285555
theorem B1523719 : Blo 1522458 1523719 := bstep (se 1 (by rfl) ⟨1142789, by rfl⟩ : syracuseStep 1523719 = 2285579) B2285579
theorem B18530315 : Blo 1522458 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B31252493 : Blo 1522458 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B2891791 : Blo 1522458 2891791 := bstep (se 1 (by rfl) ⟨2168843, by rfl⟩ : syracuseStep 2891791 = 4337687) B4337687
theorem B1523727 : Blo 1522458 1523727 := bstep (se 1 (by rfl) ⟨1142795, by rfl⟩ : syracuseStep 1523727 = 2285591) B2285591
theorem B10985483 : Blo 1522458 10985483 := bstep (se 1 (by rfl) ⟨8239112, by rfl⟩ : syracuseStep 10985483 = 16478225) B16478225
theorem B2572303 : Blo 1522458 2572303 := bstep (se 1 (by rfl) ⟨1929227, by rfl⟩ : syracuseStep 2572303 = 3858455) B3858455
theorem B3858475 : Blo 1522458 3858475 := bstep (se 1 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 3858475 = 5787713) B5787713
theorem B2285627 : Blo 1522458 2285627 := bstep (se 1 (by rfl) ⟨1714220, by rfl⟩ : syracuseStep 2285627 = 3428441) B3428441
theorem B1523771 : Blo 1522458 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B2285687 : Blo 1522458 2285687 := bstep (se 1 (by rfl) ⟨1714265, by rfl⟩ : syracuseStep 2285687 = 3428531) B3428531
theorem B4071559 : Blo 1522458 4071559 := bstep (se 1 (by rfl) ⟨3053669, by rfl⟩ : syracuseStep 4071559 = 6107339) B6107339
theorem B1523847 : Blo 1522458 1523847 := bstep (se 1 (by rfl) ⟨1142885, by rfl⟩ : syracuseStep 1523847 = 2285771) B2285771
theorem B2285711 : Blo 1522458 2285711 := bstep (se 1 (by rfl) ⟨1714283, by rfl⟩ : syracuseStep 2285711 = 3428567) B3428567
theorem B1523855 : Blo 1522458 1523855 := bstep (se 1 (by rfl) ⟨1142891, by rfl⟩ : syracuseStep 1523855 = 2285783) B2285783
theorem B2285753 : Blo 1522458 2285753 := bstep (se 2 (by rfl) ⟨857157, by rfl⟩ : syracuseStep 2285753 = 1714315) B1714315
theorem B3858617 : Blo 1522458 3858617 := bstep (se 2 (by rfl) ⟨1446981, by rfl⟩ : syracuseStep 3858617 = 2893963) B2893963
theorem B1523899 : Blo 1522458 1523899 := bstep (se 1 (by rfl) ⟨1142924, by rfl⟩ : syracuseStep 1523899 = 2285849) B2285849
theorem B2285831 : Blo 1522458 2285831 := bstep (se 1 (by rfl) ⟨1714373, by rfl⟩ : syracuseStep 2285831 = 3428747) B3428747
theorem B1523975 : Blo 1522458 1523975 := bstep (se 1 (by rfl) ⟨1142981, by rfl⟩ : syracuseStep 1523975 = 2285963) B2285963
theorem B1523983 : Blo 1522458 1523983 := bstep (se 1 (by rfl) ⟨1142987, by rfl⟩ : syracuseStep 1523983 = 2285975) B2285975
theorem B2285867 : Blo 1522458 2285867 := bstep (se 1 (by rfl) ⟨1714400, by rfl⟩ : syracuseStep 2285867 = 3428801) B3428801
theorem B1524027 : Blo 1522458 1524027 := bstep (se 1 (by rfl) ⟨1143020, by rfl⟩ : syracuseStep 1524027 = 2286041) B2286041
theorem B2285897 : Blo 1522458 2285897 := bstep (se 2 (by rfl) ⟨857211, by rfl⟩ : syracuseStep 2285897 = 1714423) B1714423
theorem B1524103 : Blo 1522458 1524103 := bstep (se 1 (by rfl) ⟨1143077, by rfl⟩ : syracuseStep 1524103 = 2286155) B2286155
theorem B1524111 : Blo 1522458 1524111 := bstep (se 1 (by rfl) ⟨1143083, by rfl⟩ : syracuseStep 1524111 = 2286167) B2286167
theorem B2892179 : Blo 1522458 2892179 := bstep (se 1 (by rfl) ⟨2169134, by rfl⟩ : syracuseStep 2892179 = 4338269) B4338269
theorem B6504857 : Blo 1522458 6504857 := bstep (se 2 (by rfl) ⟨2439321, by rfl⟩ : syracuseStep 6504857 = 4878643) B4878643
theorem B5783993 : Blo 1522458 5783993 := bstep (se 2 (by rfl) ⟨2168997, by rfl⟩ : syracuseStep 5783993 = 4337995) B4337995
theorem B2286011 : Blo 1522458 2286011 := bstep (se 1 (by rfl) ⟨1714508, by rfl⟩ : syracuseStep 2286011 = 3429017) B3429017
theorem B1524155 : Blo 1522458 1524155 := bstep (se 1 (by rfl) ⟨1143116, by rfl⟩ : syracuseStep 1524155 = 2286233) B2286233
theorem B2286071 : Blo 1522458 2286071 := bstep (se 1 (by rfl) ⟨1714553, by rfl⟩ : syracuseStep 2286071 = 3429107) B3429107
theorem B1524231 : Blo 1522458 1524231 := bstep (se 1 (by rfl) ⟨1143173, by rfl⟩ : syracuseStep 1524231 = 2286347) B2286347
theorem B5153291 : Blo 1522458 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B2286095 : Blo 1522458 2286095 := bstep (se 1 (by rfl) ⟨1714571, by rfl⟩ : syracuseStep 2286095 = 3429143) B3429143
theorem B1524239 : Blo 1522458 1524239 := bstep (se 1 (by rfl) ⟨1143179, by rfl⟩ : syracuseStep 1524239 = 2286359) B2286359
theorem B2286137 : Blo 1522458 2286137 := bstep (se 2 (by rfl) ⟨857301, by rfl⟩ : syracuseStep 2286137 = 1714603) B1714603
theorem B1524283 : Blo 1522458 1524283 := bstep (se 1 (by rfl) ⟨1143212, by rfl⟩ : syracuseStep 1524283 = 2286425) B2286425
theorem B2286215 : Blo 1522458 2286215 := bstep (se 1 (by rfl) ⟨1714661, by rfl⟩ : syracuseStep 2286215 = 3429323) B3429323
theorem B1524359 : Blo 1522458 1524359 := bstep (se 1 (by rfl) ⟨1143269, by rfl⟩ : syracuseStep 1524359 = 2286539) B2286539
theorem B1524367 : Blo 1522458 1524367 := bstep (se 1 (by rfl) ⟨1143275, by rfl⟩ : syracuseStep 1524367 = 2286551) B2286551
theorem B2286251 : Blo 1522458 2286251 := bstep (se 1 (by rfl) ⟨1714688, by rfl⟩ : syracuseStep 2286251 = 3429377) B3429377
theorem B1524411 : Blo 1522458 1524411 := bstep (se 1 (by rfl) ⟨1143308, by rfl⟩ : syracuseStep 1524411 = 2286617) B2286617
theorem B2286281 : Blo 1522458 2286281 := bstep (se 2 (by rfl) ⟨857355, by rfl⟩ : syracuseStep 2286281 = 1714711) B1714711
theorem B6505217 : Blo 1522458 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B1712911 : Blo 1522458 1712911 := bstep (se 1 (by rfl) ⟨1284683, by rfl⟩ : syracuseStep 1712911 = 2569367) B2569367
theorem B24707855 : Blo 1522458 24707855 := bstep (se 1 (by rfl) ⟨18530891, by rfl⟩ : syracuseStep 24707855 = 37061783) B37061783
theorem B2286395 : Blo 1522458 2286395 := bstep (se 1 (by rfl) ⟨1714796, by rfl⟩ : syracuseStep 2286395 = 3429593) B3429593
theorem B2286455 : Blo 1522458 2286455 := bstep (se 1 (by rfl) ⟨1714841, by rfl⟩ : syracuseStep 2286455 = 3429683) B3429683
theorem B2286479 : Blo 1522458 2286479 := bstep (se 1 (by rfl) ⟨1714859, by rfl⟩ : syracuseStep 2286479 = 3429719) B3429719
theorem B20857763 : Blo 1522458 20857763 := bstep (se 1 (by rfl) ⟨15643322, by rfl⟩ : syracuseStep 20857763 = 31286645) B31286645
theorem B2286521 : Blo 1522458 2286521 := bstep (se 2 (by rfl) ⟨857445, by rfl⟩ : syracuseStep 2286521 = 1714891) B1714891
theorem B2745289 : Blo 1522458 2745289 := bstep (se 2 (by rfl) ⟨1029483, by rfl⟩ : syracuseStep 2745289 = 2058967) B2058967
theorem B2286599 : Blo 1522458 2286599 := bstep (se 1 (by rfl) ⟨1714949, by rfl⟩ : syracuseStep 2286599 = 3429899) B3429899
theorem B2286635 : Blo 1522458 2286635 := bstep (se 1 (by rfl) ⟨1714976, by rfl⟩ : syracuseStep 2286635 = 3429953) B3429953
theorem B2286665 : Blo 1522458 2286665 := bstep (se 2 (by rfl) ⟨857499, by rfl⟩ : syracuseStep 2286665 = 1714999) B1714999
theorem B1713415 : Blo 1522458 1713415 := bstep (se 1 (by rfl) ⟨1285061, by rfl⟩ : syracuseStep 1713415 = 2570123) B2570123
theorem B3425579 : Blo 1522458 3425579 := bstep (se 1 (by rfl) ⟨2569184, by rfl⟩ : syracuseStep 3425579 = 5138369) B5138369
theorem B5784979 : Blo 1522458 5784979 := bstep (se 1 (by rfl) ⟨4338734, by rfl⟩ : syracuseStep 5784979 = 8677469) B8677469
theorem B1713595 : Blo 1522458 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B10429955 : Blo 1522458 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B13903427 : Blo 1522458 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B37045835 : Blo 1522458 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B37561931 : Blo 1522458 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B3425939 : Blo 1522458 3425939 := bstep (se 1 (by rfl) ⟨2569454, by rfl⟩ : syracuseStep 3425939 = 5138909) B5138909
theorem B3253907 : Blo 1522458 3253907 := bstep (se 1 (by rfl) ⟨2440430, by rfl⟩ : syracuseStep 3253907 = 4880861) B4880861
theorem B3425993 : Blo 1522458 3425993 := bstep (se 2 (by rfl) ⟨1284747, by rfl⟩ : syracuseStep 3425993 = 2569495) B2569495
theorem B1926919 : Blo 1522458 1926919 := bstep (se 1 (by rfl) ⟨1445189, by rfl⟩ : syracuseStep 1926919 = 2890379) B2890379
theorem B2893583 : Blo 1522458 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B9758515 : Blo 1522458 9758515 := bstep (se 1 (by rfl) ⟨7318886, by rfl⟩ : syracuseStep 9758515 = 14637773) B14637773
theorem B1714063 : Blo 1522458 1714063 := bstep (se 1 (by rfl) ⟨1285547, by rfl⟩ : syracuseStep 1714063 = 2571095) B2571095
theorem B18778007 : Blo 1522458 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B37070743 : Blo 1522458 37070743 := bstep (se 1 (by rfl) ⟨27803057, by rfl⟩ : syracuseStep 37070743 = 55606115) B55606115
theorem B4335545 : Blo 1522458 4335545 := bstep (se 2 (by rfl) ⟨1625829, by rfl⟩ : syracuseStep 4335545 = 3251659) B3251659
theorem B2058383 : Blo 1522458 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B1927415 : Blo 1522458 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B5138747 : Blo 1522458 5138747 := bstep (se 1 (by rfl) ⟨3854060, by rfl⟩ : syracuseStep 5138747 = 7708121) B7708121
theorem B3426695 : Blo 1522458 3426695 := bstep (se 1 (by rfl) ⟨2570021, by rfl⟩ : syracuseStep 3426695 = 5140043) B5140043
theorem B1714567 : Blo 1522458 1714567 := bstep (se 1 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 1714567 = 2571851) B2571851
theorem B1927567 : Blo 1522458 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B5491097 : Blo 1522458 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B9267641 : Blo 1522458 9267641 := bstep (se 2 (by rfl) ⟨3475365, by rfl⟩ : syracuseStep 9267641 = 6950731) B6950731
theorem B3426875 : Blo 1522458 3426875 := bstep (se 1 (by rfl) ⟨2570156, by rfl⟩ : syracuseStep 3426875 = 5140313) B5140313
theorem B1927739 : Blo 1522458 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B1714747 : Blo 1522458 1714747 := bstep (se 1 (by rfl) ⟨1286060, by rfl⟩ : syracuseStep 1714747 = 2572121) B2572121
theorem B8235607 : Blo 1522458 8235607 := bstep (se 1 (by rfl) ⟨6176705, by rfl⟩ : syracuseStep 8235607 = 12353411) B12353411
theorem B3427001 : Blo 1522458 3427001 := bstep (se 2 (by rfl) ⟨1285125, by rfl⟩ : syracuseStep 3427001 = 2570251) B2570251
theorem B5139233 : Blo 1522458 5139233 := bstep (se 2 (by rfl) ⟨1927212, by rfl⟩ : syracuseStep 5139233 = 3854425) B3854425
theorem B8678177 : Blo 1522458 8678177 := bstep (se 2 (by rfl) ⟨3254316, by rfl⟩ : syracuseStep 8678177 = 6508633) B6508633
theorem B16706455 : Blo 1522458 16706455 := bstep (se 1 (by rfl) ⟨12529841, by rfl⟩ : syracuseStep 16706455 = 25059683) B25059683
theorem B4336537 : Blo 1522458 4336537 := bstep (se 2 (by rfl) ⟨1626201, by rfl⟩ : syracuseStep 4336537 = 3252403) B3252403
theorem B3427343 : Blo 1522458 3427343 := bstep (se 1 (by rfl) ⟨2570507, by rfl⟩ : syracuseStep 3427343 = 5141015) B5141015
theorem B3427361 : Blo 1522458 3427361 := bstep (se 2 (by rfl) ⟨1285260, by rfl⟩ : syracuseStep 3427361 = 2570521) B2570521
theorem B26020925 : Blo 1522458 26020925 := bstep (se 3 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 26020925 = 9757847) B9757847
theorem B13896791 : Blo 1522458 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B5786711 : Blo 1522458 5786711 := bstep (se 1 (by rfl) ⟨4340033, by rfl⟩ : syracuseStep 5786711 = 8680067) B8680067
theorem B17345825 : Blo 1522458 17345825 := bstep (se 2 (by rfl) ⟨6504684, by rfl⟩ : syracuseStep 17345825 = 13009369) B13009369
theorem B125062501 : Blo 1522458 125062501 := bstep (se 4 (by rfl) ⟨11724609, by rfl⟩ : syracuseStep 125062501 = 23449219) B23449219
theorem B5139827 : Blo 1522458 5139827 := bstep (se 1 (by rfl) ⟨3854870, by rfl⟩ : syracuseStep 5139827 = 7709741) B7709741
theorem B3427703 : Blo 1522458 3427703 := bstep (se 1 (by rfl) ⟨2570777, by rfl⟩ : syracuseStep 3427703 = 5141555) B5141555
theorem B11562425 : Blo 1522458 11562425 := bstep (se 2 (by rfl) ⟨4335909, by rfl⟩ : syracuseStep 11562425 = 8671819) B8671819
theorem B1928711 : Blo 1522458 1928711 := bstep (se 1 (by rfl) ⟨1446533, by rfl⟩ : syracuseStep 1928711 = 2893067) B2893067
theorem B3427883 : Blo 1522458 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B5787197 : Blo 1522458 5787197 := bstep (se 3 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 5787197 = 2170199) B2170199
theorem B3853939 : Blo 1522458 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B3854081 : Blo 1522458 3854081 := bstep (se 2 (by rfl) ⟨1445280, by rfl⟩ : syracuseStep 3854081 = 2890561) B2890561
theorem B9760513 : Blo 1522458 9760513 := bstep (se 2 (by rfl) ⟨3660192, by rfl⟩ : syracuseStep 9760513 = 7320385) B7320385
theorem B7712657 : Blo 1522458 7712657 := bstep (se 2 (by rfl) ⟨2892246, by rfl⟩ : syracuseStep 7712657 = 5784493) B5784493
theorem B3428243 : Blo 1522458 3428243 := bstep (se 1 (by rfl) ⟨2571182, by rfl⟩ : syracuseStep 3428243 = 5142365) B5142365
theorem B3428297 : Blo 1522458 3428297 := bstep (se 2 (by rfl) ⟨1285611, by rfl⟩ : syracuseStep 3428297 = 2571223) B2571223
theorem B8671319 : Blo 1522458 8671319 := bstep (se 1 (by rfl) ⟨6503489, by rfl⟩ : syracuseStep 8671319 = 13006979) B13006979
theorem B1929359 : Blo 1522458 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B20852909 : Blo 1522458 20852909 := bstep (se 3 (by rfl) ⟨3909920, by rfl⟩ : syracuseStep 20852909 = 7819841) B7819841
theorem B3854537 : Blo 1522458 3854537 := bstep (se 2 (by rfl) ⟨1445451, by rfl⟩ : syracuseStep 3854537 = 2890903) B2890903
theorem B7319753 : Blo 1522458 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B4117025 : Blo 1522458 4117025 := bstep (se 2 (by rfl) ⟨1543884, by rfl⟩ : syracuseStep 4117025 = 3087769) B3087769
theorem B3854891 : Blo 1522458 3854891 := bstep (se 1 (by rfl) ⟨2891168, by rfl⟩ : syracuseStep 3854891 = 5782337) B5782337
theorem B4117111 : Blo 1522458 4117111 := bstep (se 1 (by rfl) ⟨3087833, by rfl⟩ : syracuseStep 4117111 = 6175667) B6175667
theorem B3428999 : Blo 1522458 3428999 := bstep (se 1 (by rfl) ⟨2571749, by rfl⟩ : syracuseStep 3428999 = 5143499) B5143499
theorem B4338461 : Blo 1522458 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B3429179 : Blo 1522458 3429179 := bstep (se 1 (by rfl) ⟨2571884, by rfl⟩ : syracuseStep 3429179 = 5143769) B5143769
theorem B3858263 : Blo 1522458 3858263 := bstep (se 1 (by rfl) ⟨2893697, by rfl⟩ : syracuseStep 3858263 = 5787395) B5787395
theorem B3429305 : Blo 1522458 3429305 := bstep (se 2 (by rfl) ⟨1285989, by rfl⟩ : syracuseStep 3429305 = 2571979) B2571979
theorem B8795101 : Blo 1522458 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B2569259 : Blo 1522458 2569259 := bstep (se 1 (by rfl) ⟨1926944, by rfl⟩ : syracuseStep 2569259 = 3853889) B3853889
theorem B8680567 : Blo 1522458 8680567 := bstep (se 1 (by rfl) ⟨6510425, by rfl⟩ : syracuseStep 8680567 = 13020851) B13020851
theorem B3429647 : Blo 1522458 3429647 := bstep (se 1 (by rfl) ⟨2572235, by rfl⟩ : syracuseStep 3429647 = 5144471) B5144471
theorem B3429665 : Blo 1522458 3429665 := bstep (se 2 (by rfl) ⟨1286124, by rfl⟩ : syracuseStep 3429665 = 2572249) B2572249
theorem B21976379 : Blo 1522458 21976379 := bstep (se 1 (by rfl) ⟨16482284, by rfl⟩ : syracuseStep 21976379 = 32964569) B32964569
theorem B2168137 : Blo 1522458 2168137 := bstep (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) B1626103
theorem B2569657 : Blo 1522458 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B4339145 : Blo 1522458 4339145 := bstep (se 2 (by rfl) ⟨1627179, by rfl⟩ : syracuseStep 4339145 = 3254359) B3254359
theorem B3855883 : Blo 1522458 3855883 := bstep (se 1 (by rfl) ⟨2891912, by rfl⟩ : syracuseStep 3855883 = 5783825) B5783825
theorem B8238635 : Blo 1522458 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B4175479 : Blo 1522458 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B15644279 : Blo 1522458 15644279 := bstep (se 1 (by rfl) ⟨11733209, by rfl⟩ : syracuseStep 15644279 = 23466419) B23466419
theorem B3430007 : Blo 1522458 3430007 := bstep (se 1 (by rfl) ⟨2572505, by rfl⟩ : syracuseStep 3430007 = 5145011) B5145011
theorem B3856025 : Blo 1522458 3856025 := bstep (se 2 (by rfl) ⟨1446009, by rfl⟩ : syracuseStep 3856025 = 2892019) B2892019
theorem B16480037 : Blo 1522458 16480037 := bstep (se 4 (by rfl) ⟨1545003, by rfl⟩ : syracuseStep 16480037 = 3090007) B3090007
theorem B2168633 : Blo 1522458 2168633 := bstep (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) B1626475
theorem B3856187 : Blo 1522458 3856187 := bstep (se 1 (by rfl) ⟨2892140, by rfl⟩ : syracuseStep 3856187 = 5784281) B5784281
theorem B16701299 : Blo 1522458 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B2439047 : Blo 1522458 2439047 := bstep (se 1 (by rfl) ⟨1829285, by rfl⟩ : syracuseStep 2439047 = 3658571) B3658571
theorem B5781395 : Blo 1522458 5781395 := bstep (se 1 (by rfl) ⟨4336046, by rfl⟩ : syracuseStep 5781395 = 8672093) B8672093
theorem B5142419 : Blo 1522458 5142419 := bstep (se 1 (by rfl) ⟨3856814, by rfl⟩ : syracuseStep 5142419 = 7713629) B7713629
theorem B7714763 : Blo 1522458 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B4339727 : Blo 1522458 4339727 := bstep (se 1 (by rfl) ⟨3254795, by rfl⟩ : syracuseStep 4339727 = 6509591) B6509591
theorem B2570359 : Blo 1522458 2570359 := bstep (se 1 (by rfl) ⟨1927769, by rfl⟩ : syracuseStep 2570359 = 3855539) B3855539
theorem B17348741 : Blo 1522458 17348741 := bstep (se 4 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 17348741 = 3252889) B3252889
theorem B4634759 : Blo 1522458 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B3856531 : Blo 1522458 3856531 := bstep (se 1 (by rfl) ⟨2892398, by rfl⟩ : syracuseStep 3856531 = 5784797) B5784797
theorem B2283707 : Blo 1522458 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B2283767 : Blo 1522458 2283767 := bstep (se 1 (by rfl) ⟨1712825, by rfl⟩ : syracuseStep 2283767 = 3425651) B3425651
theorem B2283791 : Blo 1522458 2283791 := bstep (se 1 (by rfl) ⟨1712843, by rfl⟩ : syracuseStep 2283791 = 3425687) B3425687
theorem B8673551 : Blo 1522458 8673551 := bstep (se 1 (by rfl) ⟨6505163, by rfl⟩ : syracuseStep 8673551 = 13010327) B13010327
theorem B7715087 : Blo 1522458 7715087 := bstep (se 1 (by rfl) ⟨5786315, by rfl⟩ : syracuseStep 7715087 = 11572631) B11572631
theorem B3856673 : Blo 1522458 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B105470261 : Blo 1522458 105470261 := bstep (se 5 (by rfl) ⟨4943918, by rfl⟩ : syracuseStep 105470261 = 9887837) B9887837
theorem B2283833 : Blo 1522458 2283833 := bstep (se 2 (by rfl) ⟨856437, by rfl⟩ : syracuseStep 2283833 = 1712875) B1712875
theorem B2570555 : Blo 1522458 2570555 := bstep (se 1 (by rfl) ⟨1927916, by rfl⟩ : syracuseStep 2570555 = 3855833) B3855833
theorem B4118843 : Blo 1522458 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B8681843 : Blo 1522458 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B2283911 : Blo 1522458 2283911 := bstep (se 1 (by rfl) ⟨1712933, by rfl⟩ : syracuseStep 2283911 = 3425867) B3425867
theorem B2283947 : Blo 1522458 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B2283977 : Blo 1522458 2283977 := bstep (se 2 (by rfl) ⟨856491, by rfl⟩ : syracuseStep 2283977 = 1712983) B1712983
theorem B8673803 : Blo 1522458 8673803 := bstep (se 1 (by rfl) ⟨6505352, by rfl⟩ : syracuseStep 8673803 = 13010705) B13010705
theorem B2284091 : Blo 1522458 2284091 := bstep (se 1 (by rfl) ⟨1713068, by rfl⟩ : syracuseStep 2284091 = 3426137) B3426137
theorem B4119101 : Blo 1522458 4119101 := bstep (se 3 (by rfl) ⟨772331, by rfl⟩ : syracuseStep 4119101 = 1544663) B1544663
theorem B2284151 : Blo 1522458 2284151 := bstep (se 1 (by rfl) ⟨1713113, by rfl⟩ : syracuseStep 2284151 = 3426227) B3426227
theorem B7322231 : Blo 1522458 7322231 := bstep (se 1 (by rfl) ⟨5491673, by rfl⟩ : syracuseStep 7322231 = 10983347) B10983347
theorem B2284175 : Blo 1522458 2284175 := bstep (se 1 (by rfl) ⟨1713131, by rfl⟩ : syracuseStep 2284175 = 3426263) B3426263
theorem B17357489 : Blo 1522458 17357489 := bstep (se 2 (by rfl) ⟨6509058, by rfl⟩ : syracuseStep 17357489 = 13018117) B13018117
theorem B2284217 : Blo 1522458 2284217 := bstep (se 2 (by rfl) ⟨856581, by rfl⟩ : syracuseStep 2284217 = 1713163) B1713163
theorem B13900481 : Blo 1522458 13900481 := bstep (se 2 (by rfl) ⟨5212680, by rfl⟩ : syracuseStep 13900481 = 10425361) B10425361
theorem B2570953 : Blo 1522458 2570953 := bstep (se 2 (by rfl) ⟨964107, by rfl⟩ : syracuseStep 2570953 = 1928215) B1928215
theorem B2284295 : Blo 1522458 2284295 := bstep (se 1 (by rfl) ⟨1713221, by rfl⟩ : syracuseStep 2284295 = 3426443) B3426443
theorem B2169607 : Blo 1522458 2169607 := bstep (se 1 (by rfl) ⟨1627205, by rfl⟩ : syracuseStep 2169607 = 3254411) B3254411
theorem B3087137 : Blo 1522458 3087137 := bstep (se 2 (by rfl) ⟨1157676, by rfl⟩ : syracuseStep 3087137 = 2315353) B2315353
theorem B2284331 : Blo 1522458 2284331 := bstep (se 1 (by rfl) ⟨1713248, by rfl⟩ : syracuseStep 2284331 = 3426497) B3426497
theorem B1522491 : Blo 1522458 1522491 := bstep (se 1 (by rfl) ⟨1141868, by rfl⟩ : syracuseStep 1522491 = 2283737) B2283737
theorem B2284361 : Blo 1522458 2284361 := bstep (se 2 (by rfl) ⟨856635, by rfl⟩ : syracuseStep 2284361 = 1713271) B1713271
theorem B1522567 : Blo 1522458 1522567 := bstep (se 1 (by rfl) ⟨1141925, by rfl⟩ : syracuseStep 1522567 = 2283851) B2283851
theorem B1522575 : Blo 1522458 1522575 := bstep (se 1 (by rfl) ⟨1141931, by rfl⟩ : syracuseStep 1522575 = 2283863) B2283863
theorem B7322521 : Blo 1522458 7322521 := bstep (se 2 (by rfl) ⟨2745945, by rfl⟩ : syracuseStep 7322521 = 5491891) B5491891
theorem B1522619 : Blo 1522458 1522619 := bstep (se 1 (by rfl) ⟨1141964, by rfl⟩ : syracuseStep 1522619 = 2283929) B2283929
theorem B2284475 : Blo 1522458 2284475 := bstep (se 1 (by rfl) ⟨1713356, by rfl⟩ : syracuseStep 2284475 = 3426713) B3426713
theorem B2284535 : Blo 1522458 2284535 := bstep (se 1 (by rfl) ⟨1713401, by rfl⟩ : syracuseStep 2284535 = 3426803) B3426803
theorem B1522695 : Blo 1522458 1522695 := bstep (se 1 (by rfl) ⟨1142021, by rfl⟩ : syracuseStep 1522695 = 2284043) B2284043
theorem B29285387 : Blo 1522458 29285387 := bstep (se 1 (by rfl) ⟨21964040, by rfl⟩ : syracuseStep 29285387 = 43928081) B43928081
theorem B1522703 : Blo 1522458 1522703 := bstep (se 1 (by rfl) ⟨1142027, by rfl⟩ : syracuseStep 1522703 = 2284055) B2284055
theorem B2284559 : Blo 1522458 2284559 := bstep (se 1 (by rfl) ⟨1713419, by rfl⟩ : syracuseStep 2284559 = 3426839) B3426839
theorem B2284601 : Blo 1522458 2284601 := bstep (se 2 (by rfl) ⟨856725, by rfl⟩ : syracuseStep 2284601 = 1713451) B1713451
theorem B1522747 : Blo 1522458 1522747 := bstep (se 1 (by rfl) ⟨1142060, by rfl⟩ : syracuseStep 1522747 = 2284121) B2284121
theorem B2317385 : Blo 1522458 2317385 := bstep (se 2 (by rfl) ⟨869019, by rfl⟩ : syracuseStep 2317385 = 1738039) B1738039
theorem B1522823 : Blo 1522458 1522823 := bstep (se 1 (by rfl) ⟨1142117, by rfl⟩ : syracuseStep 1522823 = 2284235) B2284235
theorem B2284679 : Blo 1522458 2284679 := bstep (se 1 (by rfl) ⟨1713509, by rfl⟩ : syracuseStep 2284679 = 3427019) B3427019
theorem B1522831 : Blo 1522458 1522831 := bstep (se 1 (by rfl) ⟨1142123, by rfl⟩ : syracuseStep 1522831 = 2284247) B2284247
theorem B2284715 : Blo 1522458 2284715 := bstep (se 1 (by rfl) ⟨1713536, by rfl⟩ : syracuseStep 2284715 = 3427073) B3427073
theorem B1522875 : Blo 1522458 1522875 := bstep (se 1 (by rfl) ⟨1142156, by rfl⟩ : syracuseStep 1522875 = 2284313) B2284313
theorem B2284745 : Blo 1522458 2284745 := bstep (se 2 (by rfl) ⟨856779, by rfl⟩ : syracuseStep 2284745 = 1713559) B1713559
theorem B3661001 : Blo 1522458 3661001 := bstep (se 2 (by rfl) ⟨1372875, by rfl⟩ : syracuseStep 3661001 = 2745751) B2745751
theorem B3857665 : Blo 1522458 3857665 := bstep (se 2 (by rfl) ⟨1446624, by rfl⟩ : syracuseStep 3857665 = 2893249) B2893249
theorem B1522951 : Blo 1522458 1522951 := bstep (se 1 (by rfl) ⟨1142213, by rfl⟩ : syracuseStep 1522951 = 2284427) B2284427
theorem B1522959 : Blo 1522458 1522959 := bstep (se 1 (by rfl) ⟨1142219, by rfl⟩ : syracuseStep 1522959 = 2284439) B2284439
theorem B5143823 : Blo 1522458 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B1523003 : Blo 1522458 1523003 := bstep (se 1 (by rfl) ⟨1142252, by rfl⟩ : syracuseStep 1523003 = 2284505) B2284505
theorem B2284859 : Blo 1522458 2284859 := bstep (se 1 (by rfl) ⟨1713644, by rfl⟩ : syracuseStep 2284859 = 3427289) B3427289
theorem B2284919 : Blo 1522458 2284919 := bstep (se 1 (by rfl) ⟨1713689, by rfl⟩ : syracuseStep 2284919 = 3427379) B3427379
theorem B3251591 : Blo 1522458 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B1523079 : Blo 1522458 1523079 := bstep (se 1 (by rfl) ⟨1142309, by rfl⟩ : syracuseStep 1523079 = 2284619) B2284619
theorem B2571655 : Blo 1522458 2571655 := bstep (se 1 (by rfl) ⟨1928741, by rfl⟩ : syracuseStep 2571655 = 3857483) B3857483
theorem B4341127 : Blo 1522458 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B1523087 : Blo 1522458 1523087 := bstep (se 1 (by rfl) ⟨1142315, by rfl⟩ : syracuseStep 1523087 = 2284631) B2284631
theorem B2284943 : Blo 1522458 2284943 := bstep (se 1 (by rfl) ⟨1713707, by rfl⟩ : syracuseStep 2284943 = 3427415) B3427415
theorem B2284985 : Blo 1522458 2284985 := bstep (se 2 (by rfl) ⟨856869, by rfl⟩ : syracuseStep 2284985 = 1713739) B1713739
theorem B1523131 : Blo 1522458 1523131 := bstep (se 1 (by rfl) ⟨1142348, by rfl⟩ : syracuseStep 1523131 = 2284697) B2284697
theorem B1523207 : Blo 1522458 1523207 := bstep (se 1 (by rfl) ⟨1142405, by rfl⟩ : syracuseStep 1523207 = 2284811) B2284811
theorem B2285063 : Blo 1522458 2285063 := bstep (se 1 (by rfl) ⟨1713797, by rfl⟩ : syracuseStep 2285063 = 3427595) B3427595
theorem B1523215 : Blo 1522458 1523215 := bstep (se 1 (by rfl) ⟨1142411, by rfl⟩ : syracuseStep 1523215 = 2284823) B2284823
theorem B5144093 : Blo 1522458 5144093 := bstep (se 3 (by rfl) ⟨964517, by rfl⟩ : syracuseStep 5144093 = 1929035) B1929035
theorem B2285099 : Blo 1522458 2285099 := bstep (se 1 (by rfl) ⟨1713824, by rfl⟩ : syracuseStep 2285099 = 3427649) B3427649
theorem B1523259 : Blo 1522458 1523259 := bstep (se 1 (by rfl) ⟨1142444, by rfl⟩ : syracuseStep 1523259 = 2284889) B2284889
theorem B4693565 : Blo 1522458 4693565 := bstep (se 3 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 4693565 = 1760087) B1760087
theorem B2285129 : Blo 1522458 2285129 := bstep (se 2 (by rfl) ⟨856923, by rfl⟩ : syracuseStep 2285129 = 1713847) B1713847
theorem B10976887 : Blo 1522458 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B4120183 : Blo 1522458 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1523335 : Blo 1522458 1523335 := bstep (se 1 (by rfl) ⟨1142501, by rfl⟩ : syracuseStep 1523335 = 2285003) B2285003
theorem B1523343 : Blo 1522458 1523343 := bstep (se 1 (by rfl) ⟨1142507, by rfl⟩ : syracuseStep 1523343 = 2285015) B2285015
theorem B1523387 : Blo 1522458 1523387 := bstep (se 1 (by rfl) ⟨1142540, by rfl⟩ : syracuseStep 1523387 = 2285081) B2285081
theorem B2285243 : Blo 1522458 2285243 := bstep (se 1 (by rfl) ⟨1713932, by rfl⟩ : syracuseStep 2285243 = 3427865) B3427865
theorem B8675009 : Blo 1522458 8675009 := bstep (se 2 (by rfl) ⟨3253128, by rfl⟩ : syracuseStep 8675009 = 6506257) B6506257
theorem B7716545 : Blo 1522458 7716545 := bstep (se 2 (by rfl) ⟨2893704, by rfl⟩ : syracuseStep 7716545 = 5787409) B5787409
theorem B9756389 : Blo 1522458 9756389 := bstep (se 4 (by rfl) ⟨914661, by rfl⟩ : syracuseStep 9756389 = 1829323) B1829323
theorem B2285303 : Blo 1522458 2285303 := bstep (se 1 (by rfl) ⟨1713977, by rfl⟩ : syracuseStep 2285303 = 3427955) B3427955
theorem B66780929 : Blo 1522458 66780929 := bstep (se 2 (by rfl) ⟨25042848, by rfl⟩ : syracuseStep 66780929 = 50085697) B50085697
theorem B1523463 : Blo 1522458 1523463 := bstep (se 1 (by rfl) ⟨1142597, by rfl⟩ : syracuseStep 1523463 = 2285195) B2285195
theorem B16465679 : Blo 1522458 16465679 := bstep (se 1 (by rfl) ⟨12349259, by rfl⟩ : syracuseStep 16465679 = 24698519) B24698519
theorem B1523471 : Blo 1522458 1523471 := bstep (se 1 (by rfl) ⟨1142603, by rfl⟩ : syracuseStep 1523471 = 2285207) B2285207
theorem B2285327 : Blo 1522458 2285327 := bstep (se 1 (by rfl) ⟨1713995, by rfl⟩ : syracuseStep 2285327 = 3427991) B3427991
theorem B3252001 : Blo 1522458 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B7323443 : Blo 1522458 7323443 := bstep (se 1 (by rfl) ⟨5492582, by rfl⟩ : syracuseStep 7323443 = 10985165) B10985165
theorem B2285369 : Blo 1522458 2285369 := bstep (se 2 (by rfl) ⟨857013, by rfl⟩ : syracuseStep 2285369 = 1714027) B1714027
theorem B1523515 : Blo 1522458 1523515 := bstep (se 1 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 1523515 = 2285273) B2285273
theorem B18521945 : Blo 1522458 18521945 := bstep (se 2 (by rfl) ⟨6945729, by rfl⟩ : syracuseStep 18521945 = 13891459) B13891459
theorem B2891639 : Blo 1522458 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B1523591 : Blo 1522458 1523591 := bstep (se 1 (by rfl) ⟨1142693, by rfl⟩ : syracuseStep 1523591 = 2285387) B2285387
theorem B2285447 : Blo 1522458 2285447 := bstep (se 1 (by rfl) ⟨1714085, by rfl⟩ : syracuseStep 2285447 = 3428171) B3428171
theorem B1523599 : Blo 1522458 1523599 := bstep (se 1 (by rfl) ⟨1142699, by rfl⟩ : syracuseStep 1523599 = 2285399) B2285399
theorem B2285483 : Blo 1522458 2285483 := bstep (se 1 (by rfl) ⟨1714112, by rfl⟩ : syracuseStep 2285483 = 3428225) B3428225
theorem B1523643 : Blo 1522458 1523643 := bstep (se 1 (by rfl) ⟨1142732, by rfl⟩ : syracuseStep 1523643 = 2285465) B2285465
theorem B2285513 : Blo 1522458 2285513 := bstep (se 2 (by rfl) ⟨857067, by rfl⟩ : syracuseStep 2285513 = 1714135) B1714135
theorem B12353543 : Blo 1522458 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B7323655 : Blo 1522458 7323655 := bstep (se 1 (by rfl) ⟨5492741, by rfl⟩ : syracuseStep 7323655 = 10985483) B10985483
theorem B1523751 : Blo 1522458 1523751 := bstep (se 1 (by rfl) ⟨1142813, by rfl⟩ : syracuseStep 1523751 = 2285627) B2285627
theorem B5144633 : Blo 1522458 5144633 := bstep (se 2 (by rfl) ⟨1929237, by rfl⟩ : syracuseStep 5144633 = 3858475) B3858475
theorem B1523791 : Blo 1522458 1523791 := bstep (se 1 (by rfl) ⟨1142843, by rfl⟩ : syracuseStep 1523791 = 2285687) B2285687
theorem B1523807 : Blo 1522458 1523807 := bstep (se 1 (by rfl) ⟨1142855, by rfl⟩ : syracuseStep 1523807 = 2285711) B2285711
theorem B13901939 : Blo 1522458 13901939 := bstep (se 1 (by rfl) ⟨10426454, by rfl⟩ : syracuseStep 13901939 = 20852909) B20852909
theorem B1523835 : Blo 1522458 1523835 := bstep (se 1 (by rfl) ⟨1142876, by rfl⟩ : syracuseStep 1523835 = 2285753) B2285753
theorem B2572411 : Blo 1522458 2572411 := bstep (se 1 (by rfl) ⟨1929308, by rfl⟩ : syracuseStep 2572411 = 3858617) B3858617
theorem B1523887 : Blo 1522458 1523887 := bstep (se 1 (by rfl) ⟨1142915, by rfl⟩ : syracuseStep 1523887 = 2285831) B2285831
theorem B1523911 : Blo 1522458 1523911 := bstep (se 1 (by rfl) ⟨1142933, by rfl⟩ : syracuseStep 1523911 = 2285867) B2285867
theorem B1523931 : Blo 1522458 1523931 := bstep (se 1 (by rfl) ⟨1142948, by rfl⟩ : syracuseStep 1523931 = 2285897) B2285897
theorem B1524007 : Blo 1522458 1524007 := bstep (se 1 (by rfl) ⟨1143005, by rfl⟩ : syracuseStep 1524007 = 2286011) B2286011
theorem B1524047 : Blo 1522458 1524047 := bstep (se 1 (by rfl) ⟨1143035, by rfl⟩ : syracuseStep 1524047 = 2286071) B2286071
theorem B1524063 : Blo 1522458 1524063 := bstep (se 1 (by rfl) ⟨1143047, by rfl⟩ : syracuseStep 1524063 = 2286095) B2286095
theorem B1524091 : Blo 1522458 1524091 := bstep (se 1 (by rfl) ⟨1143068, by rfl⟩ : syracuseStep 1524091 = 2286137) B2286137
theorem B5489021 : Blo 1522458 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B5144957 : Blo 1522458 5144957 := bstep (se 3 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 5144957 = 1929359) B1929359
theorem B2285999 : Blo 1522458 2285999 := bstep (se 1 (by rfl) ⟨1714499, by rfl⟩ : syracuseStep 2285999 = 3428999) B3428999
theorem B1524143 : Blo 1522458 1524143 := bstep (se 1 (by rfl) ⟨1143107, by rfl⟩ : syracuseStep 1524143 = 2286215) B2286215
theorem B1524167 : Blo 1522458 1524167 := bstep (se 1 (by rfl) ⟨1143125, by rfl⟩ : syracuseStep 1524167 = 2286251) B2286251
theorem B1524187 : Blo 1522458 1524187 := bstep (se 1 (by rfl) ⟨1143140, by rfl⟩ : syracuseStep 1524187 = 2286281) B2286281
theorem B2286089 : Blo 1522458 2286089 := bstep (se 2 (by rfl) ⟨857283, by rfl⟩ : syracuseStep 2286089 = 1714567) B1714567
theorem B2286119 : Blo 1522458 2286119 := bstep (se 1 (by rfl) ⟨1714589, by rfl⟩ : syracuseStep 2286119 = 3429179) B3429179
theorem B1524263 : Blo 1522458 1524263 := bstep (se 1 (by rfl) ⟨1143197, by rfl⟩ : syracuseStep 1524263 = 2286395) B2286395
theorem B1524303 : Blo 1522458 1524303 := bstep (se 1 (by rfl) ⟨1143227, by rfl⟩ : syracuseStep 1524303 = 2286455) B2286455
theorem B1524319 : Blo 1522458 1524319 := bstep (se 1 (by rfl) ⟨1143239, by rfl⟩ : syracuseStep 1524319 = 2286479) B2286479
theorem B2286203 : Blo 1522458 2286203 := bstep (se 1 (by rfl) ⟨1714652, by rfl⟩ : syracuseStep 2286203 = 3429305) B3429305
theorem B1524347 : Blo 1522458 1524347 := bstep (se 1 (by rfl) ⟨1143260, by rfl⟩ : syracuseStep 1524347 = 2286521) B2286521
theorem B1524399 : Blo 1522458 1524399 := bstep (se 1 (by rfl) ⟨1143299, by rfl⟩ : syracuseStep 1524399 = 2286599) B2286599
theorem B1712839 : Blo 1522458 1712839 := bstep (se 1 (by rfl) ⟨1284629, by rfl⟩ : syracuseStep 1712839 = 2569259) B2569259
theorem B1524423 : Blo 1522458 1524423 := bstep (se 1 (by rfl) ⟨1143317, by rfl⟩ : syracuseStep 1524423 = 2286635) B2286635
theorem B1524443 : Blo 1522458 1524443 := bstep (se 1 (by rfl) ⟨1143332, by rfl⟩ : syracuseStep 1524443 = 2286665) B2286665
theorem B2286329 : Blo 1522458 2286329 := bstep (se 2 (by rfl) ⟨857373, by rfl⟩ : syracuseStep 2286329 = 1714747) B1714747
theorem B2286431 : Blo 1522458 2286431 := bstep (se 1 (by rfl) ⟨1714823, by rfl⟩ : syracuseStep 2286431 = 3429647) B3429647
theorem B2286443 : Blo 1522458 2286443 := bstep (se 1 (by rfl) ⟨1714832, by rfl⟩ : syracuseStep 2286443 = 3429665) B3429665
theorem B2892763 : Blo 1522458 2892763 := bstep (se 1 (by rfl) ⟨2169572, by rfl⟩ : syracuseStep 2892763 = 4339145) B4339145
theorem B2892809 : Blo 1522458 2892809 := bstep (se 2 (by rfl) ⟨1084803, by rfl⟩ : syracuseStep 2892809 = 2169607) B2169607
theorem B10429519 : Blo 1522458 10429519 := bstep (se 1 (by rfl) ⟨7822139, by rfl⟩ : syracuseStep 10429519 = 15644279) B15644279
theorem B2286671 : Blo 1522458 2286671 := bstep (se 1 (by rfl) ⟨1715003, by rfl⟩ : syracuseStep 2286671 = 3430007) B3430007
theorem B10986691 : Blo 1522458 10986691 := bstep (se 1 (by rfl) ⟨8240018, by rfl⟩ : syracuseStep 10986691 = 16480037) B16480037
theorem B11134199 : Blo 1522458 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B12518671 : Blo 1522458 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B2893151 : Blo 1522458 2893151 := bstep (se 1 (by rfl) ⟨2169863, by rfl⟩ : syracuseStep 2893151 = 4339727) B4339727
theorem B10978733 : Blo 1522458 10978733 := bstep (se 3 (by rfl) ⟨2058512, by rfl⟩ : syracuseStep 10978733 = 4117025) B4117025
theorem B3089839 : Blo 1522458 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B70313507 : Blo 1522458 70313507 := bstep (se 1 (by rfl) ⟨52735130, by rfl⟩ : syracuseStep 70313507 = 105470261) B105470261
theorem B3425831 : Blo 1522458 3425831 := bstep (se 1 (by rfl) ⟨2569373, by rfl⟩ : syracuseStep 3425831 = 5138747) B5138747
theorem B1713703 : Blo 1522458 1713703 := bstep (se 1 (by rfl) ⟨1285277, by rfl⟩ : syracuseStep 1713703 = 2570555) B2570555
theorem B2745895 : Blo 1522458 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B6178427 : Blo 1522458 6178427 := bstep (se 1 (by rfl) ⟨4633820, by rfl⟩ : syracuseStep 6178427 = 9267641) B9267641
theorem B2746067 : Blo 1522458 2746067 := bstep (se 1 (by rfl) ⟨2059550, by rfl⟩ : syracuseStep 2746067 = 4119101) B4119101
theorem B9266987 : Blo 1522458 9266987 := bstep (se 1 (by rfl) ⟨6950240, by rfl⟩ : syracuseStep 9266987 = 13900481) B13900481
theorem B166750001 : Blo 1522458 166750001 := bstep (se 2 (by rfl) ⟨62531250, by rfl⟩ : syracuseStep 166750001 = 125062501) B125062501
theorem B3426155 : Blo 1522458 3426155 := bstep (se 1 (by rfl) ⟨2569616, by rfl⟩ : syracuseStep 3426155 = 5139233) B5139233
theorem B2058091 : Blo 1522458 2058091 := bstep (se 1 (by rfl) ⟨1543568, by rfl⟩ : syracuseStep 2058091 = 3087137) B3087137
theorem B5785451 : Blo 1522458 5785451 := bstep (se 1 (by rfl) ⟨4339088, by rfl⟩ : syracuseStep 5785451 = 8678177) B8678177
theorem B3426209 : Blo 1522458 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B19523591 : Blo 1522458 19523591 := bstep (se 1 (by rfl) ⟨14642693, by rfl⟩ : syracuseStep 19523591 = 29285387) B29285387
theorem B11569229 : Blo 1522458 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B5138585 : Blo 1522458 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B3426551 : Blo 1522458 3426551 := bstep (se 1 (by rfl) ⟨2569913, by rfl⟩ : syracuseStep 3426551 = 5139827) B5139827
theorem B7711037 : Blo 1522458 7711037 := bstep (se 3 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 7711037 = 2891639) B2891639
theorem B4336001 : Blo 1522458 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B13011353 : Blo 1522458 13011353 := bstep (se 2 (by rfl) ⟨4879257, by rfl⟩ : syracuseStep 13011353 = 9758515) B9758515
theorem B11561453 : Blo 1522458 11561453 := bstep (se 3 (by rfl) ⟨2167772, by rfl⟩ : syracuseStep 11561453 = 4335545) B4335545
theorem B12347963 : Blo 1522458 12347963 := bstep (se 1 (by rfl) ⟨9260972, by rfl⟩ : syracuseStep 12347963 = 18521945) B18521945
theorem B20834995 : Blo 1522458 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B3427145 : Blo 1522458 3427145 := bstep (se 2 (by rfl) ⟨1285179, by rfl⟩ : syracuseStep 3427145 = 2570359) B2570359
theorem B1928119 : Blo 1522458 1928119 := bstep (se 1 (by rfl) ⟨1446089, by rfl⟩ : syracuseStep 1928119 = 2892179) B2892179
theorem B4336571 : Blo 1522458 4336571 := bstep (se 1 (by rfl) ⟨3252428, by rfl⟩ : syracuseStep 4336571 = 6504857) B6504857
theorem B3435527 : Blo 1522458 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B356404373 : Blo 1522458 356404373 := bstep (se 6 (by rfl) ⟨8353227, by rfl⟩ : syracuseStep 356404373 = 16706455) B16706455
theorem B4336811 : Blo 1522458 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B21957925 : Blo 1522458 21957925 := bstep (se 4 (by rfl) ⟨2058555, by rfl⟩ : syracuseStep 21957925 = 4117111) B4117111
theorem B5139773 : Blo 1522458 5139773 := bstep (se 3 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 5139773 = 1927415) B1927415
theorem B10980809 : Blo 1522458 10980809 := bstep (se 2 (by rfl) ⟨4117803, by rfl⟩ : syracuseStep 10980809 = 8235607) B8235607
theorem B14650919 : Blo 1522458 14650919 := bstep (se 1 (by rfl) ⟨10988189, by rfl⟩ : syracuseStep 14650919 = 21976379) B21976379
theorem B3427937 : Blo 1522458 3427937 := bstep (se 2 (by rfl) ⟨1285476, by rfl⟩ : syracuseStep 3427937 = 2570953) B2570953
theorem B5492423 : Blo 1522458 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B9268951 : Blo 1522458 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B1626031 : Blo 1522458 1626031 := bstep (se 1 (by rfl) ⟨1219523, by rfl⟩ : syracuseStep 1626031 = 2439047) B2439047
theorem B3854263 : Blo 1522458 3854263 := bstep (se 1 (by rfl) ⟨2890697, by rfl⟩ : syracuseStep 3854263 = 5781395) B5781395
theorem B3428279 : Blo 1522458 3428279 := bstep (se 1 (by rfl) ⟨2571209, by rfl⟩ : syracuseStep 3428279 = 5142419) B5142419
theorem B11726801 : Blo 1522458 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B5140637 : Blo 1522458 5140637 := bstep (se 3 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 5140637 = 1927739) B1927739
theorem B5787895 : Blo 1522458 5787895 := bstep (se 1 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 5787895 = 8681843) B8681843
theorem B11563397 : Blo 1522458 11563397 := bstep (se 4 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 11563397 = 2168137) B2168137
theorem B11571659 : Blo 1522458 11571659 := bstep (se 1 (by rfl) ⟨8678744, by rfl⟩ : syracuseStep 11571659 = 17357489) B17357489
theorem B3428873 : Blo 1522458 3428873 := bstep (se 2 (by rfl) ⟨1285827, by rfl⟩ : syracuseStep 3428873 = 2571655) B2571655
theorem B5788169 : Blo 1522458 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B7713305 : Blo 1522458 7713305 := bstep (se 2 (by rfl) ⟨2892489, by rfl⟩ : syracuseStep 7713305 = 5784979) B5784979
theorem B5141177 : Blo 1522458 5141177 := bstep (se 2 (by rfl) ⟨1927941, by rfl⟩ : syracuseStep 5141177 = 3855883) B3855883
theorem B17347283 : Blo 1522458 17347283 := bstep (se 1 (by rfl) ⟨13010462, by rfl⟩ : syracuseStep 17347283 = 26020925) B26020925
theorem B1544923 : Blo 1522458 1544923 := bstep (se 1 (by rfl) ⟨1158692, by rfl⟩ : syracuseStep 1544923 = 2317385) B2317385
theorem B14635849 : Blo 1522458 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B5567305 : Blo 1522458 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B5493577 : Blo 1522458 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B3429215 : Blo 1522458 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B11563883 : Blo 1522458 11563883 := bstep (se 1 (by rfl) ⟨8672912, by rfl⟩ : syracuseStep 11563883 = 17345825) B17345825
theorem B2167727 : Blo 1522458 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B13014017 : Blo 1522458 13014017 := bstep (se 2 (by rfl) ⟨4880256, by rfl⟩ : syracuseStep 13014017 = 9760513) B9760513
theorem B2569225 : Blo 1522458 2569225 := bstep (se 2 (by rfl) ⟨963459, by rfl⟩ : syracuseStep 2569225 = 1926919) B1926919
theorem B3429395 : Blo 1522458 3429395 := bstep (se 1 (by rfl) ⟨2572046, by rfl⟩ : syracuseStep 3429395 = 5144093) B5144093
theorem B55620701 : Blo 1522458 55620701 := bstep (se 3 (by rfl) ⟨10428881, by rfl⟩ : syracuseStep 55620701 = 20857763) B20857763
theorem B44520619 : Blo 1522458 44520619 := bstep (se 1 (by rfl) ⟨33390464, by rfl⟩ : syracuseStep 44520619 = 66780929) B66780929
theorem B2569387 : Blo 1522458 2569387 := bstep (se 1 (by rfl) ⟨1927040, by rfl⟩ : syracuseStep 2569387 = 3854081) B3854081
theorem B49427657 : Blo 1522458 49427657 := bstep (se 2 (by rfl) ⟨18535371, by rfl⟩ : syracuseStep 49427657 = 37070743) B37070743
theorem B5141771 : Blo 1522458 5141771 := bstep (se 1 (by rfl) ⟨3856328, by rfl⟩ : syracuseStep 5141771 = 7712657) B7712657
theorem B3855721 : Blo 1522458 3855721 := bstep (se 2 (by rfl) ⟨1445895, by rfl⟩ : syracuseStep 3855721 = 2891791) B2891791
theorem B3429737 : Blo 1522458 3429737 := bstep (se 2 (by rfl) ⟨1286151, by rfl⟩ : syracuseStep 3429737 = 2572303) B2572303
theorem B5780879 : Blo 1522458 5780879 := bstep (se 1 (by rfl) ⟨4335659, by rfl⟩ : syracuseStep 5780879 = 8671319) B8671319
theorem B2569691 : Blo 1522458 2569691 := bstep (se 1 (by rfl) ⟨1927268, by rfl⟩ : syracuseStep 2569691 = 3854537) B3854537
theorem B4879835 : Blo 1522458 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B5428745 : Blo 1522458 5428745 := bstep (se 2 (by rfl) ⟨2035779, by rfl⟩ : syracuseStep 5428745 = 4071559) B4071559
theorem B5142041 : Blo 1522458 5142041 := bstep (se 2 (by rfl) ⟨1928265, by rfl⟩ : syracuseStep 5142041 = 3856531) B3856531
theorem B3855995 : Blo 1522458 3855995 := bstep (se 1 (by rfl) ⟨2891996, by rfl⟩ : syracuseStep 3855995 = 5783993) B5783993
theorem B2569927 : Blo 1522458 2569927 := bstep (se 1 (by rfl) ⟨1927445, by rfl⟩ : syracuseStep 2569927 = 3854891) B3854891
theorem B2570089 : Blo 1522458 2570089 := bstep (se 2 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 2570089 = 1927567) B1927567
theorem B2283719 : Blo 1522458 2283719 := bstep (se 1 (by rfl) ⟨1712789, by rfl⟩ : syracuseStep 2283719 = 3425579) B3425579
theorem B6953303 : Blo 1522458 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B2283881 : Blo 1522458 2283881 := bstep (se 2 (by rfl) ⟨856455, by rfl⟩ : syracuseStep 2283881 = 1712911) B1712911
theorem B25041287 : Blo 1522458 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B24697223 : Blo 1522458 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B2283959 : Blo 1522458 2283959 := bstep (se 1 (by rfl) ⟨1712969, by rfl⟩ : syracuseStep 2283959 = 3425939) B3425939
theorem B2169271 : Blo 1522458 2169271 := bstep (se 1 (by rfl) ⟨1626953, by rfl⟩ : syracuseStep 2169271 = 3253907) B3253907
theorem B2570683 : Blo 1522458 2570683 := bstep (se 1 (by rfl) ⟨1928012, by rfl⟩ : syracuseStep 2570683 = 3856025) B3856025
theorem B2283995 : Blo 1522458 2283995 := bstep (se 1 (by rfl) ⟨1712996, by rfl⟩ : syracuseStep 2283995 = 3425993) B3425993
theorem B5782049 : Blo 1522458 5782049 := bstep (se 2 (by rfl) ⟨2168268, by rfl⟩ : syracuseStep 5782049 = 4336537) B4336537
theorem B9763361 : Blo 1522458 9763361 := bstep (se 2 (by rfl) ⟨3661260, by rfl⟩ : syracuseStep 9763361 = 7322521) B7322521
theorem B2570791 : Blo 1522458 2570791 := bstep (se 1 (by rfl) ⟨1928093, by rfl⟩ : syracuseStep 2570791 = 3856187) B3856187
theorem B3660385 : Blo 1522458 3660385 := bstep (se 2 (by rfl) ⟨1372644, by rfl⟩ : syracuseStep 3660385 = 2745289) B2745289
theorem B5143175 : Blo 1522458 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B5143229 : Blo 1522458 5143229 := bstep (se 3 (by rfl) ⟨964355, by rfl⟩ : syracuseStep 5143229 = 1928711) B1928711
theorem B11565827 : Blo 1522458 11565827 := bstep (se 1 (by rfl) ⟨8674370, by rfl⟩ : syracuseStep 11565827 = 17348741) B17348741
theorem B1522471 : Blo 1522458 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B11574089 : Blo 1522458 11574089 := bstep (se 2 (by rfl) ⟨4340283, by rfl⟩ : syracuseStep 11574089 = 8680567) B8680567
theorem B1522511 : Blo 1522458 1522511 := bstep (se 1 (by rfl) ⟨1141883, by rfl⟩ : syracuseStep 1522511 = 2283767) B2283767
theorem B1522527 : Blo 1522458 1522527 := bstep (se 1 (by rfl) ⟨1141895, by rfl⟩ : syracuseStep 1522527 = 2283791) B2283791
theorem B5782367 : Blo 1522458 5782367 := bstep (se 1 (by rfl) ⟨4336775, by rfl⟩ : syracuseStep 5782367 = 8673551) B8673551
theorem B5143391 : Blo 1522458 5143391 := bstep (se 1 (by rfl) ⟨3857543, by rfl⟩ : syracuseStep 5143391 = 7715087) B7715087
theorem B2571115 : Blo 1522458 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B1522555 : Blo 1522458 1522555 := bstep (se 1 (by rfl) ⟨1141916, by rfl⟩ : syracuseStep 1522555 = 2283833) B2283833
theorem B1522607 : Blo 1522458 1522607 := bstep (se 1 (by rfl) ⟨1141955, by rfl⟩ : syracuseStep 1522607 = 2283911) B2283911
theorem B2284463 : Blo 1522458 2284463 := bstep (se 1 (by rfl) ⟨1713347, by rfl⟩ : syracuseStep 2284463 = 3426695) B3426695
theorem B3660731 : Blo 1522458 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B1522631 : Blo 1522458 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B1522651 : Blo 1522458 1522651 := bstep (se 1 (by rfl) ⟨1141988, by rfl⟩ : syracuseStep 1522651 = 2283977) B2283977
theorem B5143553 : Blo 1522458 5143553 := bstep (se 2 (by rfl) ⟨1928832, by rfl⟩ : syracuseStep 5143553 = 3857665) B3857665
theorem B5782535 : Blo 1522458 5782535 := bstep (se 1 (by rfl) ⟨4336901, by rfl⟩ : syracuseStep 5782535 = 8673803) B8673803
theorem B2284553 : Blo 1522458 2284553 := bstep (se 2 (by rfl) ⟨856707, by rfl⟩ : syracuseStep 2284553 = 1713415) B1713415
theorem B1522727 : Blo 1522458 1522727 := bstep (se 1 (by rfl) ⟨1142045, by rfl⟩ : syracuseStep 1522727 = 2284091) B2284091
theorem B2284583 : Blo 1522458 2284583 := bstep (se 1 (by rfl) ⟨1713437, by rfl⟩ : syracuseStep 2284583 = 3426875) B3426875
theorem B1522767 : Blo 1522458 1522767 := bstep (se 1 (by rfl) ⟨1142075, by rfl⟩ : syracuseStep 1522767 = 2284151) B2284151
theorem B4881487 : Blo 1522458 4881487 := bstep (se 1 (by rfl) ⟨3661115, by rfl⟩ : syracuseStep 4881487 = 7322231) B7322231
theorem B1522783 : Blo 1522458 1522783 := bstep (se 1 (by rfl) ⟨1142087, by rfl⟩ : syracuseStep 1522783 = 2284175) B2284175
theorem B1522811 : Blo 1522458 1522811 := bstep (se 1 (by rfl) ⟨1142108, by rfl⟩ : syracuseStep 1522811 = 2284217) B2284217
theorem B2284667 : Blo 1522458 2284667 := bstep (se 1 (by rfl) ⟨1713500, by rfl⟩ : syracuseStep 2284667 = 3427001) B3427001
theorem B1522863 : Blo 1522458 1522863 := bstep (se 1 (by rfl) ⟨1142147, by rfl⟩ : syracuseStep 1522863 = 2284295) B2284295
theorem B1522887 : Blo 1522458 1522887 := bstep (se 1 (by rfl) ⟨1142165, by rfl⟩ : syracuseStep 1522887 = 2284331) B2284331
theorem B1522907 : Blo 1522458 1522907 := bstep (se 1 (by rfl) ⟨1142180, by rfl⟩ : syracuseStep 1522907 = 2284361) B2284361
theorem B2284793 : Blo 1522458 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B1522983 : Blo 1522458 1522983 := bstep (se 1 (by rfl) ⟨1142237, by rfl⟩ : syracuseStep 1522983 = 2284475) B2284475
theorem B1523023 : Blo 1522458 1523023 := bstep (se 1 (by rfl) ⟨1142267, by rfl⟩ : syracuseStep 1523023 = 2284535) B2284535
theorem B1523039 : Blo 1522458 1523039 := bstep (se 1 (by rfl) ⟨1142279, by rfl⟩ : syracuseStep 1523039 = 2284559) B2284559
theorem B2284895 : Blo 1522458 2284895 := bstep (se 1 (by rfl) ⟨1713671, by rfl⟩ : syracuseStep 2284895 = 3427343) B3427343
theorem B2284907 : Blo 1522458 2284907 := bstep (se 1 (by rfl) ⟨1713680, by rfl⟩ : syracuseStep 2284907 = 3427361) B3427361
theorem B1523067 : Blo 1522458 1523067 := bstep (se 1 (by rfl) ⟨1142300, by rfl⟩ : syracuseStep 1523067 = 2284601) B2284601
theorem B65887613 : Blo 1522458 65887613 := bstep (se 3 (by rfl) ⟨12353927, by rfl⟩ : syracuseStep 65887613 = 24707855) B24707855
theorem B7716221 : Blo 1522458 7716221 := bstep (se 3 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 7716221 = 2893583) B2893583
theorem B9264527 : Blo 1522458 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B3857807 : Blo 1522458 3857807 := bstep (se 1 (by rfl) ⟨2893355, by rfl⟩ : syracuseStep 3857807 = 5786711) B5786711
theorem B1523119 : Blo 1522458 1523119 := bstep (se 1 (by rfl) ⟨1142339, by rfl⟩ : syracuseStep 1523119 = 2284679) B2284679
theorem B1523143 : Blo 1522458 1523143 := bstep (se 1 (by rfl) ⟨1142357, by rfl⟩ : syracuseStep 1523143 = 2284715) B2284715
theorem B1523163 : Blo 1522458 1523163 := bstep (se 1 (by rfl) ⟨1142372, by rfl⟩ : syracuseStep 1523163 = 2284745) B2284745
theorem B2440667 : Blo 1522458 2440667 := bstep (se 1 (by rfl) ⟨1830500, by rfl⟩ : syracuseStep 2440667 = 3661001) B3661001
theorem B5783021 : Blo 1522458 5783021 := bstep (se 3 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 5783021 = 2168633) B2168633
theorem B1523239 : Blo 1522458 1523239 := bstep (se 1 (by rfl) ⟨1142429, by rfl⟩ : syracuseStep 1523239 = 2284859) B2284859
theorem B1523279 : Blo 1522458 1523279 := bstep (se 1 (by rfl) ⟨1142459, by rfl⟩ : syracuseStep 1523279 = 2284919) B2284919
theorem B2285135 : Blo 1522458 2285135 := bstep (se 1 (by rfl) ⟨1713851, by rfl⟩ : syracuseStep 2285135 = 3427703) B3427703
theorem B1523295 : Blo 1522458 1523295 := bstep (se 1 (by rfl) ⟨1142471, by rfl⟩ : syracuseStep 1523295 = 2284943) B2284943
theorem B7708283 : Blo 1522458 7708283 := bstep (se 1 (by rfl) ⟨5781212, by rfl⟩ : syracuseStep 7708283 = 11562425) B11562425
theorem B1523323 : Blo 1522458 1523323 := bstep (se 1 (by rfl) ⟨1142492, by rfl⟩ : syracuseStep 1523323 = 2284985) B2284985
theorem B1523375 : Blo 1522458 1523375 := bstep (se 1 (by rfl) ⟨1142531, by rfl⟩ : syracuseStep 1523375 = 2285063) B2285063
theorem B1523399 : Blo 1522458 1523399 := bstep (se 1 (by rfl) ⟨1142549, by rfl⟩ : syracuseStep 1523399 = 2285099) B2285099
theorem B2285255 : Blo 1522458 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B3129043 : Blo 1522458 3129043 := bstep (se 1 (by rfl) ⟨2346782, by rfl⟩ : syracuseStep 3129043 = 4693565) B4693565
theorem B3858131 : Blo 1522458 3858131 := bstep (se 1 (by rfl) ⟨2893598, by rfl⟩ : syracuseStep 3858131 = 5787197) B5787197
theorem B1523419 : Blo 1522458 1523419 := bstep (se 1 (by rfl) ⟨1142564, by rfl⟩ : syracuseStep 1523419 = 2285129) B2285129
theorem B1523495 : Blo 1522458 1523495 := bstep (se 1 (by rfl) ⟨1142621, by rfl⟩ : syracuseStep 1523495 = 2285243) B2285243
theorem B5783339 : Blo 1522458 5783339 := bstep (se 1 (by rfl) ⟨4337504, by rfl⟩ : syracuseStep 5783339 = 8675009) B8675009
theorem B5144363 : Blo 1522458 5144363 := bstep (se 1 (by rfl) ⟨3858272, by rfl⟩ : syracuseStep 5144363 = 7716545) B7716545
theorem B6504259 : Blo 1522458 6504259 := bstep (se 1 (by rfl) ⟨4878194, by rfl⟩ : syracuseStep 6504259 = 9756389) B9756389
theorem B1523535 : Blo 1522458 1523535 := bstep (se 1 (by rfl) ⟨1142651, by rfl⟩ : syracuseStep 1523535 = 2285303) B2285303
theorem B10977119 : Blo 1522458 10977119 := bstep (se 1 (by rfl) ⟨8232839, by rfl⟩ : syracuseStep 10977119 = 16465679) B16465679
theorem B1523551 : Blo 1522458 1523551 := bstep (se 1 (by rfl) ⟨1142663, by rfl⟩ : syracuseStep 1523551 = 2285327) B2285327
theorem B2285417 : Blo 1522458 2285417 := bstep (se 2 (by rfl) ⟨857031, by rfl⟩ : syracuseStep 2285417 = 1714063) B1714063
theorem B4882295 : Blo 1522458 4882295 := bstep (se 1 (by rfl) ⟨3661721, by rfl⟩ : syracuseStep 4882295 = 7323443) B7323443
theorem B1523579 : Blo 1522458 1523579 := bstep (se 1 (by rfl) ⟨1142684, by rfl⟩ : syracuseStep 1523579 = 2285369) B2285369
theorem B2572175 : Blo 1522458 2572175 := bstep (se 1 (by rfl) ⟨1929131, by rfl⟩ : syracuseStep 2572175 = 3858263) B3858263
theorem B1523631 : Blo 1522458 1523631 := bstep (se 1 (by rfl) ⟨1142723, by rfl⟩ : syracuseStep 1523631 = 2285447) B2285447
theorem B2285495 : Blo 1522458 2285495 := bstep (se 1 (by rfl) ⟨1714121, by rfl⟩ : syracuseStep 2285495 = 3428243) B3428243
theorem B1523655 : Blo 1522458 1523655 := bstep (se 1 (by rfl) ⟨1142741, by rfl⟩ : syracuseStep 1523655 = 2285483) B2285483
theorem B1523675 : Blo 1522458 1523675 := bstep (se 1 (by rfl) ⟨1142756, by rfl⟩ : syracuseStep 1523675 = 2285513) B2285513
theorem B2285531 : Blo 1522458 2285531 := bstep (se 1 (by rfl) ⟨1714148, by rfl⟩ : syracuseStep 2285531 = 3428297) B3428297
theorem B9764873 : Blo 1522458 9764873 := bstep (se 2 (by rfl) ⟨3661827, by rfl⟩ : syracuseStep 9764873 = 7323655) B7323655
theorem B7708931 : Blo 1522458 7708931 := bstep (se 1 (by rfl) ⟨5781698, by rfl⟩ : syracuseStep 7708931 = 11563397) B11563397
theorem B1523999 : Blo 1522458 1523999 := bstep (se 1 (by rfl) ⟨1142999, by rfl⟩ : syracuseStep 1523999 = 2285999) B2285999
theorem B7717193 : Blo 1522458 7717193 := bstep (se 2 (by rfl) ⟨2893947, by rfl⟩ : syracuseStep 7717193 = 5787895) B5787895
theorem B2285915 : Blo 1522458 2285915 := bstep (se 1 (by rfl) ⟨1714436, by rfl⟩ : syracuseStep 2285915 = 3428873) B3428873
theorem B1524059 : Blo 1522458 1524059 := bstep (se 1 (by rfl) ⟨1143044, by rfl⟩ : syracuseStep 1524059 = 2286089) B2286089
theorem B3858779 : Blo 1522458 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B1524079 : Blo 1522458 1524079 := bstep (se 1 (by rfl) ⟨1143059, by rfl⟩ : syracuseStep 1524079 = 2286119) B2286119
theorem B1524135 : Blo 1522458 1524135 := bstep (se 1 (by rfl) ⟨1143101, by rfl⟩ : syracuseStep 1524135 = 2286203) B2286203
theorem B1524219 : Blo 1522458 1524219 := bstep (se 1 (by rfl) ⟨1143164, by rfl⟩ : syracuseStep 1524219 = 2286329) B2286329
theorem B2286143 : Blo 1522458 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B1524287 : Blo 1522458 1524287 := bstep (se 1 (by rfl) ⟨1143215, by rfl⟩ : syracuseStep 1524287 = 2286431) B2286431
theorem B7709255 : Blo 1522458 7709255 := bstep (se 1 (by rfl) ⟨5781941, by rfl⟩ : syracuseStep 7709255 = 11563883) B11563883
theorem B2892361 : Blo 1522458 2892361 := bstep (se 2 (by rfl) ⟨1084635, by rfl⟩ : syracuseStep 2892361 = 2169271) B2169271
theorem B1524295 : Blo 1522458 1524295 := bstep (se 1 (by rfl) ⟨1143221, by rfl⟩ : syracuseStep 1524295 = 2286443) B2286443
theorem B8676011 : Blo 1522458 8676011 := bstep (se 1 (by rfl) ⟨6507008, by rfl⟩ : syracuseStep 8676011 = 13014017) B13014017
theorem B2286263 : Blo 1522458 2286263 := bstep (se 1 (by rfl) ⟨1714697, by rfl⟩ : syracuseStep 2286263 = 3429395) B3429395
theorem B1524447 : Blo 1522458 1524447 := bstep (se 1 (by rfl) ⟨1143335, by rfl⟩ : syracuseStep 1524447 = 2286671) B2286671
theorem B7422799 : Blo 1522458 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B27779993 : Blo 1522458 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B2286491 : Blo 1522458 2286491 := bstep (se 1 (by rfl) ⟨1714868, by rfl⟩ : syracuseStep 2286491 = 3429737) B3429737
theorem B1713127 : Blo 1522458 1713127 := bstep (se 1 (by rfl) ⟨1284845, by rfl⟩ : syracuseStep 1713127 = 2569691) B2569691
theorem B3253223 : Blo 1522458 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B46875671 : Blo 1522458 46875671 := bstep (se 1 (by rfl) ⟨35156753, by rfl⟩ : syracuseStep 46875671 = 70313507) B70313507
theorem B19514465 : Blo 1522458 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B7423073 : Blo 1522458 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B7324769 : Blo 1522458 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B6177991 : Blo 1522458 6177991 := bstep (se 1 (by rfl) ⟨4633493, by rfl⟩ : syracuseStep 6177991 = 9266987) B9266987
theorem B111166667 : Blo 1522458 111166667 := bstep (se 1 (by rfl) ⟨83375000, by rfl⟩ : syracuseStep 111166667 = 166750001) B166750001
theorem B3425633 : Blo 1522458 3425633 := bstep (se 2 (by rfl) ⟨1284612, by rfl⟩ : syracuseStep 3425633 = 2569225) B2569225
theorem B3425723 : Blo 1522458 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B3425849 : Blo 1522458 3425849 := bstep (se 2 (by rfl) ⟨1284693, by rfl⟩ : syracuseStep 3425849 = 2569387) B2569387
theorem B59360825 : Blo 1522458 59360825 := bstep (se 2 (by rfl) ⟨22260309, by rfl⟩ : syracuseStep 59360825 = 44520619) B44520619
theorem B14648921 : Blo 1522458 14648921 := bstep (se 2 (by rfl) ⟨5493345, by rfl⟩ : syracuseStep 14648921 = 10986691) B10986691
theorem B7710551 : Blo 1522458 7710551 := bstep (se 1 (by rfl) ⟨5782913, by rfl⟩ : syracuseStep 7710551 = 11565827) B11565827
theorem B237602915 : Blo 1522458 237602915 := bstep (se 1 (by rfl) ⟨178202186, by rfl⟩ : syracuseStep 237602915 = 356404373) B356404373
theorem B3426515 : Blo 1522458 3426515 := bstep (se 1 (by rfl) ⟨2569886, by rfl⟩ : syracuseStep 3426515 = 5139773) B5139773
theorem B3426569 : Blo 1522458 3426569 := bstep (se 2 (by rfl) ⟨1284963, by rfl⟩ : syracuseStep 3426569 = 2569927) B2569927
theorem B4172057 : Blo 1522458 4172057 := bstep (se 2 (by rfl) ⟨1564521, by rfl⟩ : syracuseStep 4172057 = 3129043) B3129043
theorem B13019453 : Blo 1522458 13019453 := bstep (se 3 (by rfl) ⟨2441147, by rfl⟩ : syracuseStep 13019453 = 4882295) B4882295
theorem B9767279 : Blo 1522458 9767279 := bstep (se 1 (by rfl) ⟨7325459, by rfl⟩ : syracuseStep 9767279 = 14650919) B14650919
theorem B5138855 : Blo 1522458 5138855 := bstep (se 1 (by rfl) ⟨3854141, by rfl⟩ : syracuseStep 5138855 = 7708283) B7708283
theorem B3426785 : Blo 1522458 3426785 := bstep (se 2 (by rfl) ⟨1285044, by rfl⟩ : syracuseStep 3426785 = 2570089) B2570089
theorem B7318079 : Blo 1522458 7318079 := bstep (se 1 (by rfl) ⟨5488559, by rfl⟩ : syracuseStep 7318079 = 10977119) B10977119
theorem B5139017 : Blo 1522458 5139017 := bstep (se 2 (by rfl) ⟨1927131, by rfl⟩ : syracuseStep 5139017 = 3854263) B3854263
theorem B1714783 : Blo 1522458 1714783 := bstep (se 1 (by rfl) ⟨1286087, by rfl⟩ : syracuseStep 1714783 = 2572175) B2572175
theorem B7817867 : Blo 1522458 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B8235695 : Blo 1522458 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B9267959 : Blo 1522458 9267959 := bstep (se 1 (by rfl) ⟨6950969, by rfl⟩ : syracuseStep 9267959 = 13901939) B13901939
theorem B3427091 : Blo 1522458 3427091 := bstep (se 1 (by rfl) ⟨2570318, by rfl⟩ : syracuseStep 3427091 = 5140637) B5140637
theorem B3427451 : Blo 1522458 3427451 := bstep (se 1 (by rfl) ⟨2570588, by rfl⟩ : syracuseStep 3427451 = 5141177) B5141177
theorem B3427577 : Blo 1522458 3427577 := bstep (se 2 (by rfl) ⟨1285341, by rfl⟩ : syracuseStep 3427577 = 2570683) B2570683
theorem B1928539 : Blo 1522458 1928539 := bstep (se 1 (by rfl) ⟨1446404, by rfl⟩ : syracuseStep 1928539 = 2892809) B2892809
theorem B3427721 : Blo 1522458 3427721 := bstep (se 2 (by rfl) ⟨1285395, by rfl⟩ : syracuseStep 3427721 = 2570791) B2570791
theorem B37080467 : Blo 1522458 37080467 := bstep (se 1 (by rfl) ⟨27810350, by rfl⟩ : syracuseStep 37080467 = 55620701) B55620701
theorem B32951771 : Blo 1522458 32951771 := bstep (se 1 (by rfl) ⟨24713828, by rfl⟩ : syracuseStep 32951771 = 49427657) B49427657
theorem B3427847 : Blo 1522458 3427847 := bstep (se 1 (by rfl) ⟨2570885, by rfl⟩ : syracuseStep 3427847 = 5141771) B5141771
theorem B1928767 : Blo 1522458 1928767 := bstep (se 1 (by rfl) ⟨1446575, by rfl⟩ : syracuseStep 1928767 = 2893151) B2893151
theorem B3853919 : Blo 1522458 3853919 := bstep (se 1 (by rfl) ⟨2890439, by rfl⟩ : syracuseStep 3853919 = 5780879) B5780879
theorem B7319155 : Blo 1522458 7319155 := bstep (se 1 (by rfl) ⟨5489366, by rfl⟩ : syracuseStep 7319155 = 10978733) B10978733
theorem B2059897 : Blo 1522458 2059897 := bstep (se 2 (by rfl) ⟨772461, by rfl⟩ : syracuseStep 2059897 = 1544923) B1544923
theorem B3428027 : Blo 1522458 3428027 := bstep (se 1 (by rfl) ⟨2571020, by rfl⟩ : syracuseStep 3428027 = 5142041) B5142041
theorem B3428153 : Blo 1522458 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B7712819 : Blo 1522458 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B6508649 : Blo 1522458 6508649 := bstep (se 2 (by rfl) ⟨2440743, by rfl⟩ : syracuseStep 6508649 = 4881487) B4881487
theorem B13906025 : Blo 1522458 13906025 := bstep (se 2 (by rfl) ⟨5214759, by rfl⟩ : syracuseStep 13906025 = 10429519) B10429519
theorem B5140691 : Blo 1522458 5140691 := bstep (se 1 (by rfl) ⟨3855518, by rfl⟩ : syracuseStep 5140691 = 7711037) B7711037
theorem B16691561 : Blo 1522458 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B3854699 : Blo 1522458 3854699 := bstep (se 1 (by rfl) ⟨2891024, by rfl⟩ : syracuseStep 3854699 = 5782049) B5782049
theorem B6508907 : Blo 1522458 6508907 := bstep (se 1 (by rfl) ⟨4881680, by rfl⟩ : syracuseStep 6508907 = 9763361) B9763361
theorem B3428783 : Blo 1522458 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B3428819 : Blo 1522458 3428819 := bstep (se 1 (by rfl) ⟨2571614, by rfl⟩ : syracuseStep 3428819 = 5143229) B5143229
theorem B5140961 : Blo 1522458 5140961 := bstep (se 2 (by rfl) ⟨1927860, by rfl⟩ : syracuseStep 5140961 = 3855721) B3855721
theorem B3854911 : Blo 1522458 3854911 := bstep (se 1 (by rfl) ⟨2891183, by rfl⟩ : syracuseStep 3854911 = 5782367) B5782367
theorem B3428927 : Blo 1522458 3428927 := bstep (se 1 (by rfl) ⟨2571695, by rfl⟩ : syracuseStep 3428927 = 5143391) B5143391
theorem B3429035 : Blo 1522458 3429035 := bstep (se 1 (by rfl) ⟨2571776, by rfl⟩ : syracuseStep 3429035 = 5143553) B5143553
theorem B3855023 : Blo 1522458 3855023 := bstep (se 1 (by rfl) ⟨2891267, by rfl⟩ : syracuseStep 3855023 = 5782535) B5782535
theorem B2290351 : Blo 1522458 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B29291381 : Blo 1522458 29291381 := bstep (se 5 (by rfl) ⟨1373033, by rfl⟩ : syracuseStep 29291381 = 2746067) B2746067
theorem B12358601 : Blo 1522458 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B7320539 : Blo 1522458 7320539 := bstep (se 1 (by rfl) ⟨5490404, by rfl⟩ : syracuseStep 7320539 = 10980809) B10980809
theorem B1627111 : Blo 1522458 1627111 := bstep (se 1 (by rfl) ⟨1220333, by rfl⟩ : syracuseStep 1627111 = 2440667) B2440667
theorem B3855347 : Blo 1522458 3855347 := bstep (se 1 (by rfl) ⟨2891510, by rfl⟩ : syracuseStep 3855347 = 5783021) B5783021
theorem B8672345 : Blo 1522458 8672345 := bstep (se 2 (by rfl) ⟨3252129, by rfl⟩ : syracuseStep 8672345 = 6504259) B6504259
theorem B5780605 : Blo 1522458 5780605 := bstep (se 3 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 5780605 = 2167727) B2167727
theorem B3855559 : Blo 1522458 3855559 := bstep (se 1 (by rfl) ⟨2891669, by rfl⟩ : syracuseStep 3855559 = 5783339) B5783339
theorem B3429575 : Blo 1522458 3429575 := bstep (se 1 (by rfl) ⟨2572181, by rfl⟩ : syracuseStep 3429575 = 5144363) B5144363
theorem B2168041 : Blo 1522458 2168041 := bstep (se 2 (by rfl) ⟨813015, by rfl⟩ : syracuseStep 2168041 = 1626031) B1626031
theorem B3429755 : Blo 1522458 3429755 := bstep (se 1 (by rfl) ⟨2572316, by rfl⟩ : syracuseStep 3429755 = 5144633) B5144633
theorem B3429881 : Blo 1522458 3429881 := bstep (se 2 (by rfl) ⟨1286205, by rfl⟩ : syracuseStep 3429881 = 2572411) B2572411
theorem B3659347 : Blo 1522458 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B3429971 : Blo 1522458 3429971 := bstep (se 1 (by rfl) ⟨2572478, by rfl⟩ : syracuseStep 3429971 = 5144957) B5144957
theorem B7714439 : Blo 1522458 7714439 := bstep (se 1 (by rfl) ⟨5785829, by rfl⟩ : syracuseStep 7714439 = 11571659) B11571659
theorem B5142203 : Blo 1522458 5142203 := bstep (se 1 (by rfl) ⟨3856652, by rfl⟩ : syracuseStep 5142203 = 7713305) B7713305
theorem B11564855 : Blo 1522458 11564855 := bstep (se 1 (by rfl) ⟨8673641, by rfl⟩ : syracuseStep 11564855 = 17347283) B17347283
theorem B4880513 : Blo 1522458 4880513 := bstep (se 2 (by rfl) ⟨1830192, by rfl⟩ : syracuseStep 4880513 = 3660385) B3660385
theorem B2283785 : Blo 1522458 2283785 := bstep (se 2 (by rfl) ⟨856419, by rfl⟩ : syracuseStep 2283785 = 1712839) B1712839
theorem B3619163 : Blo 1522458 3619163 := bstep (se 1 (by rfl) ⟨2714372, by rfl⟩ : syracuseStep 3619163 = 5428745) B5428745
theorem B2283887 : Blo 1522458 2283887 := bstep (se 1 (by rfl) ⟨1712915, by rfl⟩ : syracuseStep 2283887 = 3425831) B3425831
theorem B2570663 : Blo 1522458 2570663 := bstep (se 1 (by rfl) ⟨1927997, by rfl⟩ : syracuseStep 2570663 = 3855995) B3855995
theorem B4118951 : Blo 1522458 4118951 := bstep (se 1 (by rfl) ⟨3089213, by rfl⟩ : syracuseStep 4118951 = 6178427) B6178427
theorem B2284103 : Blo 1522458 2284103 := bstep (se 1 (by rfl) ⟨1713077, by rfl⟩ : syracuseStep 2284103 = 3426155) B3426155
theorem B3856967 : Blo 1522458 3856967 := bstep (se 1 (by rfl) ⟨2892725, by rfl⟩ : syracuseStep 3856967 = 5785451) B5785451
theorem B2570825 : Blo 1522458 2570825 := bstep (se 2 (by rfl) ⟨964059, by rfl⟩ : syracuseStep 2570825 = 1928119) B1928119
theorem B2284139 : Blo 1522458 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B3857017 : Blo 1522458 3857017 := bstep (se 2 (by rfl) ⟨1446381, by rfl⟩ : syracuseStep 3857017 = 2892763) B2892763
theorem B13015727 : Blo 1522458 13015727 := bstep (se 1 (by rfl) ⟨9761795, by rfl⟩ : syracuseStep 13015727 = 19523591) B19523591
theorem B1522479 : Blo 1522458 1522479 := bstep (se 1 (by rfl) ⟨1141859, by rfl⟩ : syracuseStep 1522479 = 2283719) B2283719
theorem B2284367 : Blo 1522458 2284367 := bstep (se 1 (by rfl) ⟨1713275, by rfl⟩ : syracuseStep 2284367 = 3426551) B3426551
theorem B4635535 : Blo 1522458 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B1522587 : Blo 1522458 1522587 := bstep (se 1 (by rfl) ⟨1141940, by rfl⟩ : syracuseStep 1522587 = 2283881) B2283881
theorem B2890667 : Blo 1522458 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B16694191 : Blo 1522458 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B16464815 : Blo 1522458 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B8674235 : Blo 1522458 8674235 := bstep (se 1 (by rfl) ⟨6505676, by rfl⟩ : syracuseStep 8674235 = 13011353) B13011353
theorem B1522639 : Blo 1522458 1522639 := bstep (se 1 (by rfl) ⟨1141979, by rfl⟩ : syracuseStep 1522639 = 2283959) B2283959
theorem B1522663 : Blo 1522458 1522663 := bstep (se 1 (by rfl) ⟨1141997, by rfl⟩ : syracuseStep 1522663 = 2283995) B2283995
theorem B7707635 : Blo 1522458 7707635 := bstep (se 1 (by rfl) ⟨5780726, by rfl⟩ : syracuseStep 7707635 = 11561453) B11561453
theorem B8231975 : Blo 1522458 8231975 := bstep (se 1 (by rfl) ⟨6173981, by rfl⟩ : syracuseStep 8231975 = 12347963) B12347963
theorem B29277233 : Blo 1522458 29277233 := bstep (se 2 (by rfl) ⟨10978962, by rfl⟩ : syracuseStep 29277233 = 21957925) B21957925
theorem B2284763 : Blo 1522458 2284763 := bstep (se 1 (by rfl) ⟨1713572, by rfl⟩ : syracuseStep 2284763 = 3427145) B3427145
theorem B7716059 : Blo 1522458 7716059 := bstep (se 1 (by rfl) ⟨5787044, by rfl⟩ : syracuseStep 7716059 = 11574089) B11574089
theorem B10976485 : Blo 1522458 10976485 := bstep (se 4 (by rfl) ⟨1029045, by rfl⟩ : syracuseStep 10976485 = 2058091) B2058091
theorem B4119785 : Blo 1522458 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B1522975 : Blo 1522458 1522975 := bstep (se 1 (by rfl) ⟨1142231, by rfl⟩ : syracuseStep 1522975 = 2284463) B2284463
theorem B2891047 : Blo 1522458 2891047 := bstep (se 1 (by rfl) ⟨2168285, by rfl⟩ : syracuseStep 2891047 = 4336571) B4336571
theorem B2440487 : Blo 1522458 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B1523035 : Blo 1522458 1523035 := bstep (se 1 (by rfl) ⟨1142276, by rfl⟩ : syracuseStep 1523035 = 2284553) B2284553
theorem B1523055 : Blo 1522458 1523055 := bstep (se 1 (by rfl) ⟨1142291, by rfl⟩ : syracuseStep 1523055 = 2284583) B2284583
theorem B2284937 : Blo 1522458 2284937 := bstep (se 2 (by rfl) ⟨856851, by rfl⟩ : syracuseStep 2284937 = 1713703) B1713703
theorem B3661193 : Blo 1522458 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B1523111 : Blo 1522458 1523111 := bstep (se 1 (by rfl) ⟨1142333, by rfl⟩ : syracuseStep 1523111 = 2284667) B2284667
theorem B2891207 : Blo 1522458 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B1523195 : Blo 1522458 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B1523263 : Blo 1522458 1523263 := bstep (se 1 (by rfl) ⟨1142447, by rfl⟩ : syracuseStep 1523263 = 2284895) B2284895
theorem B1523271 : Blo 1522458 1523271 := bstep (se 1 (by rfl) ⟨1142453, by rfl⟩ : syracuseStep 1523271 = 2284907) B2284907
theorem B43925075 : Blo 1522458 43925075 := bstep (se 1 (by rfl) ⟨32943806, by rfl⟩ : syracuseStep 43925075 = 65887613) B65887613
theorem B5144147 : Blo 1522458 5144147 := bstep (se 1 (by rfl) ⟨3858110, by rfl⟩ : syracuseStep 5144147 = 7716221) B7716221
theorem B6176351 : Blo 1522458 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B2571871 : Blo 1522458 2571871 := bstep (se 1 (by rfl) ⟨1928903, by rfl⟩ : syracuseStep 2571871 = 3857807) B3857807
theorem B1523423 : Blo 1522458 1523423 := bstep (se 1 (by rfl) ⟨1142567, by rfl⟩ : syracuseStep 1523423 = 2285135) B2285135
theorem B2285291 : Blo 1522458 2285291 := bstep (se 1 (by rfl) ⟨1713968, by rfl⟩ : syracuseStep 2285291 = 3427937) B3427937
theorem B1523503 : Blo 1522458 1523503 := bstep (se 1 (by rfl) ⟨1142627, by rfl⟩ : syracuseStep 1523503 = 2285255) B2285255
theorem B3661615 : Blo 1522458 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2572087 : Blo 1522458 2572087 := bstep (se 1 (by rfl) ⟨1929065, by rfl⟩ : syracuseStep 2572087 = 3858131) B3858131
theorem B1523611 : Blo 1522458 1523611 := bstep (se 1 (by rfl) ⟨1142708, by rfl⟩ : syracuseStep 1523611 = 2285417) B2285417
theorem B1523663 : Blo 1522458 1523663 := bstep (se 1 (by rfl) ⟨1142747, by rfl⟩ : syracuseStep 1523663 = 2285495) B2285495
theorem B2285519 : Blo 1522458 2285519 := bstep (se 1 (by rfl) ⟨1714139, by rfl⟩ : syracuseStep 2285519 = 3428279) B3428279
theorem B1523687 : Blo 1522458 1523687 := bstep (se 1 (by rfl) ⟨1142765, by rfl⟩ : syracuseStep 1523687 = 2285531) B2285531
theorem B5144795 : Blo 1522458 5144795 := bstep (se 1 (by rfl) ⟨3858596, by rfl⟩ : syracuseStep 5144795 = 7717193) B7717193
theorem B1523943 : Blo 1522458 1523943 := bstep (se 1 (by rfl) ⟨1142957, by rfl⟩ : syracuseStep 1523943 = 2285915) B2285915
theorem B2572519 : Blo 1522458 2572519 := bstep (se 1 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 2572519 = 3858779) B3858779
theorem B2285855 : Blo 1522458 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B2285879 : Blo 1522458 2285879 := bstep (se 1 (by rfl) ⟨1714409, by rfl⟩ : syracuseStep 2285879 = 3428819) B3428819
theorem B2285951 : Blo 1522458 2285951 := bstep (se 1 (by rfl) ⟨1714463, by rfl⟩ : syracuseStep 2285951 = 3428927) B3428927
theorem B1524095 : Blo 1522458 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B5784007 : Blo 1522458 5784007 := bstep (se 1 (by rfl) ⟨4338005, by rfl⟩ : syracuseStep 5784007 = 8676011) B8676011
theorem B2286023 : Blo 1522458 2286023 := bstep (se 1 (by rfl) ⟨1714517, by rfl⟩ : syracuseStep 2286023 = 3429035) B3429035
theorem B1524175 : Blo 1522458 1524175 := bstep (se 1 (by rfl) ⟨1143131, by rfl⟩ : syracuseStep 1524175 = 2286263) B2286263
theorem B1524327 : Blo 1522458 1524327 := bstep (se 1 (by rfl) ⟨1143245, by rfl⟩ : syracuseStep 1524327 = 2286491) B2286491
theorem B13009643 : Blo 1522458 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B4948715 : Blo 1522458 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B4883179 : Blo 1522458 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B2286377 : Blo 1522458 2286377 := bstep (se 2 (by rfl) ⟨857391, by rfl⟩ : syracuseStep 2286377 = 1714783) B1714783
theorem B2286383 : Blo 1522458 2286383 := bstep (se 1 (by rfl) ⟨1714787, by rfl⟩ : syracuseStep 2286383 = 3429575) B3429575
theorem B2286503 : Blo 1522458 2286503 := bstep (se 1 (by rfl) ⟨1714877, by rfl⟩ : syracuseStep 2286503 = 3429755) B3429755
theorem B2286587 : Blo 1522458 2286587 := bstep (se 1 (by rfl) ⟨1714940, by rfl⟩ : syracuseStep 2286587 = 3429881) B3429881
theorem B2286647 : Blo 1522458 2286647 := bstep (se 1 (by rfl) ⟨1714985, by rfl⟩ : syracuseStep 2286647 = 3429971) B3429971
theorem B9765947 : Blo 1522458 9765947 := bstep (se 1 (by rfl) ⟨7324460, by rfl⟩ : syracuseStep 9765947 = 14648921) B14648921
theorem B9897065 : Blo 1522458 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B7709903 : Blo 1522458 7709903 := bstep (se 1 (by rfl) ⟨5782427, by rfl⟩ : syracuseStep 7709903 = 11564855) B11564855
theorem B22258921 : Blo 1522458 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B158401943 : Blo 1522458 158401943 := bstep (se 1 (by rfl) ⟨118801457, by rfl⟩ : syracuseStep 158401943 = 237602915) B237602915
theorem B3425903 : Blo 1522458 3425903 := bstep (se 1 (by rfl) ⟨2569427, by rfl⟩ : syracuseStep 3425903 = 5138855) B5138855
theorem B1713775 : Blo 1522458 1713775 := bstep (se 1 (by rfl) ⟨1285331, by rfl⟩ : syracuseStep 1713775 = 2570663) B2570663
theorem B2745967 : Blo 1522458 2745967 := bstep (se 1 (by rfl) ⟨2059475, by rfl⟩ : syracuseStep 2745967 = 4118951) B4118951
theorem B3426011 : Blo 1522458 3426011 := bstep (se 1 (by rfl) ⟨2569508, by rfl⟩ : syracuseStep 3426011 = 5139017) B5139017
theorem B1713883 : Blo 1522458 1713883 := bstep (se 1 (by rfl) ⟨1285412, by rfl⟩ : syracuseStep 1713883 = 2570825) B2570825
theorem B5211911 : Blo 1522458 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B8677151 : Blo 1522458 8677151 := bstep (se 1 (by rfl) ⟨6507863, by rfl⟩ : syracuseStep 8677151 = 13015727) B13015727
theorem B6178639 : Blo 1522458 6178639 := bstep (se 1 (by rfl) ⟨4633979, by rfl⟩ : syracuseStep 6178639 = 9267959) B9267959
theorem B5138423 : Blo 1522458 5138423 := bstep (se 1 (by rfl) ⟨3853817, by rfl⟩ : syracuseStep 5138423 = 7707635) B7707635
theorem B9758873 : Blo 1522458 9758873 := bstep (se 2 (by rfl) ⟨3659577, by rfl⟩ : syracuseStep 9758873 = 7319155) B7319155
theorem B2746523 : Blo 1522458 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B2746529 : Blo 1522458 2746529 := bstep (se 2 (by rfl) ⟨1029948, by rfl⟩ : syracuseStep 2746529 = 2059897) B2059897
theorem B1927471 : Blo 1522458 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B8677925 : Blo 1522458 8677925 := bstep (se 4 (by rfl) ⟨813555, by rfl⟩ : syracuseStep 8677925 = 1627111) B1627111
theorem B3427127 : Blo 1522458 3427127 := bstep (se 1 (by rfl) ⟨2570345, by rfl⟩ : syracuseStep 3427127 = 5140691) B5140691
theorem B5139287 : Blo 1522458 5139287 := bstep (se 1 (by rfl) ⟨3854465, by rfl⟩ : syracuseStep 5139287 = 7708931) B7708931
theorem B11127707 : Blo 1522458 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B3427307 : Blo 1522458 3427307 := bstep (se 1 (by rfl) ⟨2570480, by rfl⟩ : syracuseStep 3427307 = 5140961) B5140961
theorem B5139503 : Blo 1522458 5139503 := bstep (se 1 (by rfl) ⟨3854627, by rfl⟩ : syracuseStep 5139503 = 7709255) B7709255
theorem B5139881 : Blo 1522458 5139881 := bstep (se 2 (by rfl) ⟨1927455, by rfl⟩ : syracuseStep 5139881 = 3854911) B3854911
theorem B6507965 : Blo 1522458 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B3428135 : Blo 1522458 3428135 := bstep (se 1 (by rfl) ⟨2571101, by rfl⟩ : syracuseStep 3428135 = 5142203) B5142203
theorem B6180713 : Blo 1522458 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B5140367 : Blo 1522458 5140367 := bstep (se 1 (by rfl) ⟨3855275, by rfl⟩ : syracuseStep 5140367 = 7710551) B7710551
theorem B2781371 : Blo 1522458 2781371 := bstep (se 1 (by rfl) ⟨2086028, by rfl⟩ : syracuseStep 2781371 = 4172057) B4172057
theorem B8679635 : Blo 1522458 8679635 := bstep (se 1 (by rfl) ⟨6509726, by rfl⟩ : syracuseStep 8679635 = 13019453) B13019453
theorem B2412775 : Blo 1522458 2412775 := bstep (se 1 (by rfl) ⟨1809581, by rfl⟩ : syracuseStep 2412775 = 3619163) B3619163
theorem B5140745 : Blo 1522458 5140745 := bstep (se 2 (by rfl) ⟨1927779, by rfl⟩ : syracuseStep 5140745 = 3855559) B3855559
theorem B8237321 : Blo 1522458 8237321 := bstep (se 2 (by rfl) ⟨3088995, by rfl⟩ : syracuseStep 8237321 = 6177991) B6177991
theorem B14635313 : Blo 1522458 14635313 := bstep (se 2 (by rfl) ⟨5488242, by rfl⟩ : syracuseStep 14635313 = 10976485) B10976485
theorem B4878719 : Blo 1522458 4878719 := bstep (se 1 (by rfl) ⟨3659039, by rfl⟩ : syracuseStep 4878719 = 7318079) B7318079
theorem B3854729 : Blo 1522458 3854729 := bstep (se 2 (by rfl) ⟨1445523, by rfl⟩ : syracuseStep 3854729 = 2891047) B2891047
theorem B19518155 : Blo 1522458 19518155 := bstep (se 1 (by rfl) ⟨14638616, by rfl⟩ : syracuseStep 19518155 = 29277233) B29277233
theorem B4879129 : Blo 1522458 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B3429161 : Blo 1522458 3429161 := bstep (se 2 (by rfl) ⟨1285935, by rfl⟩ : syracuseStep 3429161 = 2571871) B2571871
theorem B24720311 : Blo 1522458 24720311 := bstep (se 1 (by rfl) ⟨18540233, by rfl⟩ : syracuseStep 24720311 = 37080467) B37080467
theorem B21967847 : Blo 1522458 21967847 := bstep (se 1 (by rfl) ⟨16475885, by rfl⟩ : syracuseStep 21967847 = 32951771) B32951771
theorem B29283383 : Blo 1522458 29283383 := bstep (se 1 (by rfl) ⟨21962537, by rfl⟩ : syracuseStep 29283383 = 43925075) B43925075
theorem B3429431 : Blo 1522458 3429431 := bstep (se 1 (by rfl) ⟨2572073, by rfl⟩ : syracuseStep 3429431 = 5144147) B5144147
theorem B4117567 : Blo 1522458 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B2569279 : Blo 1522458 2569279 := bstep (se 1 (by rfl) ⟨1926959, by rfl⟩ : syracuseStep 2569279 = 3853919) B3853919
theorem B3429449 : Blo 1522458 3429449 := bstep (se 2 (by rfl) ⟨1286043, by rfl⟩ : syracuseStep 3429449 = 2572087) B2572087
theorem B6509915 : Blo 1522458 6509915 := bstep (se 1 (by rfl) ⟨4882436, by rfl⟩ : syracuseStep 6509915 = 9764873) B9764873
theorem B5141879 : Blo 1522458 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B4339099 : Blo 1522458 4339099 := bstep (se 1 (by rfl) ⟨3254324, by rfl⟩ : syracuseStep 4339099 = 6508649) B6508649
theorem B9270683 : Blo 1522458 9270683 := bstep (se 1 (by rfl) ⟨6953012, by rfl⟩ : syracuseStep 9270683 = 13906025) B13906025
theorem B2569799 : Blo 1522458 2569799 := bstep (se 1 (by rfl) ⟨1927349, by rfl⟩ : syracuseStep 2569799 = 3854699) B3854699
theorem B4339271 : Blo 1522458 4339271 := bstep (se 1 (by rfl) ⟨3254453, by rfl⟩ : syracuseStep 4339271 = 6508907) B6508907
theorem B13014701 : Blo 1522458 13014701 := bstep (se 3 (by rfl) ⟨2440256, by rfl⟩ : syracuseStep 13014701 = 4880513) B4880513
theorem B2570015 : Blo 1522458 2570015 := bstep (se 1 (by rfl) ⟨1927511, by rfl⟩ : syracuseStep 2570015 = 3855023) B3855023
theorem B19527587 : Blo 1522458 19527587 := bstep (se 1 (by rfl) ⟨14645690, by rfl⟩ : syracuseStep 19527587 = 29291381) B29291381
theorem B18519995 : Blo 1522458 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B8239067 : Blo 1522458 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B4880359 : Blo 1522458 4880359 := bstep (se 1 (by rfl) ⟨3660269, by rfl⟩ : syracuseStep 4880359 = 7320539) B7320539
theorem B2570231 : Blo 1522458 2570231 := bstep (se 1 (by rfl) ⟨1927673, by rfl⟩ : syracuseStep 2570231 = 3855347) B3855347
theorem B31250447 : Blo 1522458 31250447 := bstep (se 1 (by rfl) ⟨23437835, by rfl⟩ : syracuseStep 31250447 = 46875671) B46875671
theorem B5781563 : Blo 1522458 5781563 := bstep (se 1 (by rfl) ⟨4336172, by rfl⟩ : syracuseStep 5781563 = 8672345) B8672345
theorem B3856481 : Blo 1522458 3856481 := bstep (se 2 (by rfl) ⟨1446180, by rfl⟩ : syracuseStep 3856481 = 2892361) B2892361
theorem B74111111 : Blo 1522458 74111111 := bstep (se 1 (by rfl) ⟨55583333, by rfl⟩ : syracuseStep 74111111 = 111166667) B111166667
theorem B5142689 : Blo 1522458 5142689 := bstep (se 2 (by rfl) ⟨1928508, by rfl⟩ : syracuseStep 5142689 = 3857017) B3857017
theorem B3053801 : Blo 1522458 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B2283755 : Blo 1522458 2283755 := bstep (se 1 (by rfl) ⟨1712816, by rfl⟩ : syracuseStep 2283755 = 3425633) B3425633
theorem B2283815 : Blo 1522458 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B2283899 : Blo 1522458 2283899 := bstep (se 1 (by rfl) ⟨1712924, by rfl⟩ : syracuseStep 2283899 = 3425849) B3425849
theorem B39573883 : Blo 1522458 39573883 := bstep (se 1 (by rfl) ⟨29680412, by rfl⟩ : syracuseStep 39573883 = 59360825) B59360825
theorem B5142959 : Blo 1522458 5142959 := bstep (se 1 (by rfl) ⟨3857219, by rfl⟩ : syracuseStep 5142959 = 7714439) B7714439
theorem B2284169 : Blo 1522458 2284169 := bstep (se 2 (by rfl) ⟨856563, by rfl⟩ : syracuseStep 2284169 = 1713127) B1713127
theorem B2284343 : Blo 1522458 2284343 := bstep (se 1 (by rfl) ⟨1713257, by rfl⟩ : syracuseStep 2284343 = 3426515) B3426515
theorem B7707473 : Blo 1522458 7707473 := bstep (se 2 (by rfl) ⟨2890302, by rfl⟩ : syracuseStep 7707473 = 5780605) B5780605
theorem B1522523 : Blo 1522458 1522523 := bstep (se 1 (by rfl) ⟨1141892, by rfl⟩ : syracuseStep 1522523 = 2283785) B2283785
theorem B2284379 : Blo 1522458 2284379 := bstep (se 1 (by rfl) ⟨1713284, by rfl⟩ : syracuseStep 2284379 = 3426569) B3426569
theorem B1522591 : Blo 1522458 1522591 := bstep (se 1 (by rfl) ⟨1141943, by rfl⟩ : syracuseStep 1522591 = 2283887) B2283887
theorem B6511519 : Blo 1522458 6511519 := bstep (se 1 (by rfl) ⟨4883639, by rfl⟩ : syracuseStep 6511519 = 9767279) B9767279
theorem B19528613 : Blo 1522458 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B2890721 : Blo 1522458 2890721 := bstep (se 2 (by rfl) ⟨1084020, by rfl⟩ : syracuseStep 2890721 = 2168041) B2168041
theorem B2284523 : Blo 1522458 2284523 := bstep (se 1 (by rfl) ⟨1713392, by rfl⟩ : syracuseStep 2284523 = 3426785) B3426785
theorem B1522735 : Blo 1522458 1522735 := bstep (se 1 (by rfl) ⟨1142051, by rfl⟩ : syracuseStep 1522735 = 2284103) B2284103
theorem B2571311 : Blo 1522458 2571311 := bstep (se 1 (by rfl) ⟨1928483, by rfl⟩ : syracuseStep 2571311 = 3856967) B3856967
theorem B1522759 : Blo 1522458 1522759 := bstep (se 1 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 1522759 = 2284139) B2284139
theorem B2571385 : Blo 1522458 2571385 := bstep (se 2 (by rfl) ⟨964269, by rfl⟩ : syracuseStep 2571385 = 1928539) B1928539
theorem B21961853 : Blo 1522458 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B2284727 : Blo 1522458 2284727 := bstep (se 1 (by rfl) ⟨1713545, by rfl⟩ : syracuseStep 2284727 = 3427091) B3427091
theorem B1522911 : Blo 1522458 1522911 := bstep (se 1 (by rfl) ⟨1142183, by rfl⟩ : syracuseStep 1522911 = 2284367) B2284367
theorem B10976543 : Blo 1522458 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B5782823 : Blo 1522458 5782823 := bstep (se 1 (by rfl) ⟨4337117, by rfl⟩ : syracuseStep 5782823 = 8674235) B8674235
theorem B5487983 : Blo 1522458 5487983 := bstep (se 1 (by rfl) ⟨4115987, by rfl⟩ : syracuseStep 5487983 = 8231975) B8231975
theorem B2284967 : Blo 1522458 2284967 := bstep (se 1 (by rfl) ⟨1713725, by rfl⟩ : syracuseStep 2284967 = 3427451) B3427451
theorem B2571689 : Blo 1522458 2571689 := bstep (se 2 (by rfl) ⟨964383, by rfl⟩ : syracuseStep 2571689 = 1928767) B1928767
theorem B1523175 : Blo 1522458 1523175 := bstep (se 1 (by rfl) ⟨1142381, by rfl⟩ : syracuseStep 1523175 = 2284763) B2284763
theorem B5144039 : Blo 1522458 5144039 := bstep (se 1 (by rfl) ⟨3858029, by rfl⟩ : syracuseStep 5144039 = 7716059) B7716059
theorem B2285051 : Blo 1522458 2285051 := bstep (se 1 (by rfl) ⟨1713788, by rfl⟩ : syracuseStep 2285051 = 3427577) B3427577
theorem B1523291 : Blo 1522458 1523291 := bstep (se 1 (by rfl) ⟨1142468, by rfl⟩ : syracuseStep 1523291 = 2284937) B2284937
theorem B2285147 : Blo 1522458 2285147 := bstep (se 1 (by rfl) ⟨1713860, by rfl⟩ : syracuseStep 2285147 = 3427721) B3427721
theorem B2440795 : Blo 1522458 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B2285231 : Blo 1522458 2285231 := bstep (se 1 (by rfl) ⟨1713923, by rfl⟩ : syracuseStep 2285231 = 3427847) B3427847
theorem B7708445 : Blo 1522458 7708445 := bstep (se 3 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 7708445 = 2890667) B2890667
theorem B2285351 : Blo 1522458 2285351 := bstep (se 1 (by rfl) ⟨1714013, by rfl⟩ : syracuseStep 2285351 = 3428027) B3428027
theorem B1523527 : Blo 1522458 1523527 := bstep (se 1 (by rfl) ⟨1142645, by rfl⟩ : syracuseStep 1523527 = 2285291) B2285291
theorem B2285435 : Blo 1522458 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem B8675261 : Blo 1522458 8675261 := bstep (se 3 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 8675261 = 3253223) B3253223
theorem B1523679 : Blo 1522458 1523679 := bstep (se 1 (by rfl) ⟨1142759, by rfl⟩ : syracuseStep 1523679 = 2285519) B2285519
theorem B1523903 : Blo 1522458 1523903 := bstep (se 1 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 1523903 = 2285855) B2285855
theorem B9756875 : Blo 1522458 9756875 := bstep (se 1 (by rfl) ⟨7317656, by rfl⟩ : syracuseStep 9756875 = 14635313) B14635313
theorem B1523919 : Blo 1522458 1523919 := bstep (se 1 (by rfl) ⟨1142939, by rfl⟩ : syracuseStep 1523919 = 2285879) B2285879
theorem B3252479 : Blo 1522458 3252479 := bstep (se 1 (by rfl) ⟨2439359, by rfl⟩ : syracuseStep 3252479 = 4878719) B4878719
theorem B1523967 : Blo 1522458 1523967 := bstep (se 1 (by rfl) ⟨1142975, by rfl⟩ : syracuseStep 1523967 = 2285951) B2285951
theorem B1524015 : Blo 1522458 1524015 := bstep (se 1 (by rfl) ⟨1143011, by rfl⟩ : syracuseStep 1524015 = 2286023) B2286023
theorem B52765177 : Blo 1522458 52765177 := bstep (se 2 (by rfl) ⟨19786941, by rfl⟩ : syracuseStep 52765177 = 39573883) B39573883
theorem B2286107 : Blo 1522458 2286107 := bstep (se 1 (by rfl) ⟨1714580, by rfl⟩ : syracuseStep 2286107 = 3429161) B3429161
theorem B1524251 : Blo 1522458 1524251 := bstep (se 1 (by rfl) ⟨1143188, by rfl⟩ : syracuseStep 1524251 = 2286377) B2286377
theorem B1524255 : Blo 1522458 1524255 := bstep (se 1 (by rfl) ⟨1143191, by rfl⟩ : syracuseStep 1524255 = 2286383) B2286383
theorem B1524335 : Blo 1522458 1524335 := bstep (se 1 (by rfl) ⟨1143251, by rfl⟩ : syracuseStep 1524335 = 2286503) B2286503
theorem B1524391 : Blo 1522458 1524391 := bstep (se 1 (by rfl) ⟨1143293, by rfl⟩ : syracuseStep 1524391 = 2286587) B2286587
theorem B19522255 : Blo 1522458 19522255 := bstep (se 1 (by rfl) ⟨14641691, by rfl⟩ : syracuseStep 19522255 = 29283383) B29283383
theorem B2286287 : Blo 1522458 2286287 := bstep (se 1 (by rfl) ⟨1714715, by rfl⟩ : syracuseStep 2286287 = 3429431) B3429431
theorem B1524431 : Blo 1522458 1524431 := bstep (se 1 (by rfl) ⟨1143323, by rfl⟩ : syracuseStep 1524431 = 2286647) B2286647
theorem B2286299 : Blo 1522458 2286299 := bstep (se 1 (by rfl) ⟨1714724, by rfl⟩ : syracuseStep 2286299 = 3429449) B3429449
theorem B6505505 : Blo 1522458 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B1713199 : Blo 1522458 1713199 := bstep (se 1 (by rfl) ⟨1284899, by rfl⟩ : syracuseStep 1713199 = 2569799) B2569799
theorem B2892847 : Blo 1522458 2892847 := bstep (se 1 (by rfl) ⟨2169635, by rfl⟩ : syracuseStep 2892847 = 4339271) B4339271
theorem B8676467 : Blo 1522458 8676467 := bstep (se 1 (by rfl) ⟨6507350, by rfl⟩ : syracuseStep 8676467 = 13014701) B13014701
theorem B1713343 : Blo 1522458 1713343 := bstep (se 1 (by rfl) ⟨1285007, by rfl⟩ : syracuseStep 1713343 = 2570015) B2570015
theorem B5784767 : Blo 1522458 5784767 := bstep (se 1 (by rfl) ⟨4338575, by rfl⟩ : syracuseStep 5784767 = 8677151) B8677151
theorem B13018391 : Blo 1522458 13018391 := bstep (se 1 (by rfl) ⟨9763793, by rfl⟩ : syracuseStep 13018391 = 19527587) B19527587
theorem B12346663 : Blo 1522458 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B3425615 : Blo 1522458 3425615 := bstep (se 1 (by rfl) ⟨2569211, by rfl⟩ : syracuseStep 3425615 = 5138423) B5138423
theorem B1713487 : Blo 1522458 1713487 := bstep (se 1 (by rfl) ⟨1285115, by rfl⟩ : syracuseStep 1713487 = 2570231) B2570231
theorem B20833631 : Blo 1522458 20833631 := bstep (se 1 (by rfl) ⟨15625223, by rfl⟩ : syracuseStep 20833631 = 31250447) B31250447
theorem B5490089 : Blo 1522458 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B3425705 : Blo 1522458 3425705 := bstep (se 2 (by rfl) ⟨1284639, by rfl⟩ : syracuseStep 3425705 = 2569279) B2569279
theorem B49407407 : Blo 1522458 49407407 := bstep (se 1 (by rfl) ⟨37055555, by rfl⟩ : syracuseStep 49407407 = 74111111) B74111111
theorem B6505915 : Blo 1522458 6505915 := bstep (se 1 (by rfl) ⟨4879436, by rfl⟩ : syracuseStep 6505915 = 9758873) B9758873
theorem B5785283 : Blo 1522458 5785283 := bstep (se 1 (by rfl) ⟨4338962, by rfl⟩ : syracuseStep 5785283 = 8677925) B8677925
theorem B5785465 : Blo 1522458 5785465 := bstep (se 2 (by rfl) ⟨2169549, by rfl⟩ : syracuseStep 5785465 = 4339099) B4339099
theorem B5138315 : Blo 1522458 5138315 := bstep (se 1 (by rfl) ⟨3853736, by rfl⟩ : syracuseStep 5138315 = 7707473) B7707473
theorem B3426191 : Blo 1522458 3426191 := bstep (se 1 (by rfl) ⟨2569643, by rfl⟩ : syracuseStep 3426191 = 5139287) B5139287
theorem B13019075 : Blo 1522458 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1927147 : Blo 1522458 1927147 := bstep (se 1 (by rfl) ⟨1445360, by rfl⟩ : syracuseStep 1927147 = 2890721) B2890721
theorem B3426335 : Blo 1522458 3426335 := bstep (se 1 (by rfl) ⟨2569751, by rfl⟩ : syracuseStep 3426335 = 5139503) B5139503
theorem B1714207 : Blo 1522458 1714207 := bstep (se 1 (by rfl) ⟨1285655, by rfl⟩ : syracuseStep 1714207 = 2571311) B2571311
theorem B14641235 : Blo 1522458 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B3254393 : Blo 1522458 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B7317695 : Blo 1522458 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B3426587 : Blo 1522458 3426587 := bstep (se 1 (by rfl) ⟨2569940, by rfl⟩ : syracuseStep 3426587 = 5139881) B5139881
theorem B1714459 : Blo 1522458 1714459 := bstep (se 1 (by rfl) ⟨1285844, by rfl⟩ : syracuseStep 1714459 = 2571689) B2571689
theorem B5138963 : Blo 1522458 5138963 := bstep (se 1 (by rfl) ⟨3854222, by rfl⟩ : syracuseStep 5138963 = 7708445) B7708445
theorem B3426911 : Blo 1522458 3426911 := bstep (se 1 (by rfl) ⟨2570183, by rfl⟩ : syracuseStep 3426911 = 5140367) B5140367
theorem B6507145 : Blo 1522458 6507145 := bstep (se 2 (by rfl) ⟨2440179, by rfl⟩ : syracuseStep 6507145 = 4880359) B4880359
theorem B1854247 : Blo 1522458 1854247 := bstep (se 1 (by rfl) ⟨1390685, by rfl⟩ : syracuseStep 1854247 = 2781371) B2781371
theorem B5786423 : Blo 1522458 5786423 := bstep (se 1 (by rfl) ⟨4339817, by rfl⟩ : syracuseStep 5786423 = 8679635) B8679635
theorem B3427163 : Blo 1522458 3427163 := bstep (se 1 (by rfl) ⟨2570372, by rfl⟩ : syracuseStep 3427163 = 5140745) B5140745
theorem B5491547 : Blo 1522458 5491547 := bstep (se 1 (by rfl) ⟨4118660, by rfl⟩ : syracuseStep 5491547 = 8237321) B8237321
theorem B13012103 : Blo 1522458 13012103 := bstep (se 1 (by rfl) ⟨9759077, by rfl⟩ : syracuseStep 13012103 = 19518155) B19518155
theorem B7712009 : Blo 1522458 7712009 := bstep (se 2 (by rfl) ⟨2892003, by rfl⟩ : syracuseStep 7712009 = 5784007) B5784007
theorem B6598043 : Blo 1522458 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B5139935 : Blo 1522458 5139935 := bstep (se 1 (by rfl) ⟨3854951, by rfl⟩ : syracuseStep 5139935 = 7709903) B7709903
theorem B3427919 : Blo 1522458 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B6180455 : Blo 1522458 6180455 := bstep (se 1 (by rfl) ⟨4635341, by rfl⟩ : syracuseStep 6180455 = 9270683) B9270683
theorem B17354573 : Blo 1522458 17354573 := bstep (se 3 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 17354573 = 6507965) B6507965
theorem B5492711 : Blo 1522458 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B3854375 : Blo 1522458 3854375 := bstep (se 1 (by rfl) ⟨2890781, by rfl⟩ : syracuseStep 3854375 = 5781563) B5781563
theorem B1831015 : Blo 1522458 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B3428459 : Blo 1522458 3428459 := bstep (se 1 (by rfl) ⟨2571344, by rfl⟩ : syracuseStep 3428459 = 5142689) B5142689
theorem B1831019 : Blo 1522458 1831019 := bstep (se 1 (by rfl) ⟨1373264, by rfl⟩ : syracuseStep 1831019 = 2746529) B2746529
theorem B2035867 : Blo 1522458 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B3428513 : Blo 1522458 3428513 := bstep (se 2 (by rfl) ⟨1285692, by rfl⟩ : syracuseStep 3428513 = 2571385) B2571385
theorem B3428639 : Blo 1522458 3428639 := bstep (se 1 (by rfl) ⟨2571479, by rfl⟩ : syracuseStep 3428639 = 5142959) B5142959
theorem B7418471 : Blo 1522458 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B13898429 : Blo 1522458 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B3855215 : Blo 1522458 3855215 := bstep (se 1 (by rfl) ⟨2891411, by rfl⟩ : syracuseStep 3855215 = 5782823) B5782823
theorem B3658655 : Blo 1522458 3658655 := bstep (se 1 (by rfl) ⟨2743991, by rfl⟩ : syracuseStep 3658655 = 5487983) B5487983
theorem B3429359 : Blo 1522458 3429359 := bstep (se 1 (by rfl) ⟨2572019, by rfl⟩ : syracuseStep 3429359 = 5144039) B5144039
theorem B8238185 : Blo 1522458 8238185 := bstep (se 2 (by rfl) ⟨3089319, by rfl⟩ : syracuseStep 8238185 = 6178639) B6178639
theorem B3429863 : Blo 1522458 3429863 := bstep (se 1 (by rfl) ⟨2572397, by rfl⟩ : syracuseStep 3429863 = 5144795) B5144795
theorem B2569819 : Blo 1522458 2569819 := bstep (se 1 (by rfl) ⟨1927364, by rfl⟩ : syracuseStep 2569819 = 3854729) B3854729
theorem B3217033 : Blo 1522458 3217033 := bstep (se 2 (by rfl) ⟨1206387, by rfl⟩ : syracuseStep 3217033 = 2412775) B2412775
theorem B3430025 : Blo 1522458 3430025 := bstep (se 2 (by rfl) ⟨1286259, by rfl⟩ : syracuseStep 3430025 = 2572519) B2572519
theorem B2569961 : Blo 1522458 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B8673095 : Blo 1522458 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B3299143 : Blo 1522458 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B16480207 : Blo 1522458 16480207 := bstep (se 1 (by rfl) ⟨12360155, by rfl⟩ : syracuseStep 16480207 = 24720311) B24720311
theorem B14645231 : Blo 1522458 14645231 := bstep (se 1 (by rfl) ⟨10983923, by rfl⟩ : syracuseStep 14645231 = 21967847) B21967847
theorem B6510631 : Blo 1522458 6510631 := bstep (se 1 (by rfl) ⟨4882973, by rfl⟩ : syracuseStep 6510631 = 9765947) B9765947
theorem B4339943 : Blo 1522458 4339943 := bstep (se 1 (by rfl) ⟨3254957, by rfl⟩ : syracuseStep 4339943 = 6509915) B6509915
theorem B105601295 : Blo 1522458 105601295 := bstep (se 1 (by rfl) ⟨79200971, by rfl⟩ : syracuseStep 105601295 = 158401943) B158401943
theorem B6510905 : Blo 1522458 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B2283935 : Blo 1522458 2283935 := bstep (se 1 (by rfl) ⟨1712951, by rfl⟩ : syracuseStep 2283935 = 3425903) B3425903
theorem B2284007 : Blo 1522458 2284007 := bstep (se 1 (by rfl) ⟨1713005, by rfl⟩ : syracuseStep 2284007 = 3426011) B3426011
theorem B8682025 : Blo 1522458 8682025 := bstep (se 2 (by rfl) ⟨3255759, by rfl⟩ : syracuseStep 8682025 = 6511519) B6511519
theorem B2570987 : Blo 1522458 2570987 := bstep (se 1 (by rfl) ⟨1928240, by rfl⟩ : syracuseStep 2570987 = 3856481) B3856481
theorem B1522503 : Blo 1522458 1522503 := bstep (se 1 (by rfl) ⟨1141877, by rfl⟩ : syracuseStep 1522503 = 2283755) B2283755
theorem B1522543 : Blo 1522458 1522543 := bstep (se 1 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 1522543 = 2283815) B2283815
theorem B1522599 : Blo 1522458 1522599 := bstep (se 1 (by rfl) ⟨1141949, by rfl⟩ : syracuseStep 1522599 = 2283899) B2283899
theorem B29678561 : Blo 1522458 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B1522779 : Blo 1522458 1522779 := bstep (se 1 (by rfl) ⟨1142084, by rfl⟩ : syracuseStep 1522779 = 2284169) B2284169
theorem B1522895 : Blo 1522458 1522895 := bstep (se 1 (by rfl) ⟨1142171, by rfl⟩ : syracuseStep 1522895 = 2284343) B2284343
theorem B2284751 : Blo 1522458 2284751 := bstep (se 1 (by rfl) ⟨1713563, by rfl⟩ : syracuseStep 2284751 = 3427127) B3427127
theorem B1522919 : Blo 1522458 1522919 := bstep (se 1 (by rfl) ⟨1142189, by rfl⟩ : syracuseStep 1522919 = 2284379) B2284379
theorem B1523015 : Blo 1522458 1523015 := bstep (se 1 (by rfl) ⟨1142261, by rfl⟩ : syracuseStep 1523015 = 2284523) B2284523
theorem B2284871 : Blo 1522458 2284871 := bstep (se 1 (by rfl) ⟨1713653, by rfl⟩ : syracuseStep 2284871 = 3427307) B3427307
theorem B1523151 : Blo 1522458 1523151 := bstep (se 1 (by rfl) ⟨1142363, by rfl⟩ : syracuseStep 1523151 = 2284727) B2284727
theorem B2285033 : Blo 1522458 2285033 := bstep (se 2 (by rfl) ⟨856887, by rfl⟩ : syracuseStep 2285033 = 1713775) B1713775
theorem B3661289 : Blo 1522458 3661289 := bstep (se 2 (by rfl) ⟨1372983, by rfl⟩ : syracuseStep 3661289 = 2745967) B2745967
theorem B1523311 : Blo 1522458 1523311 := bstep (se 1 (by rfl) ⟨1142483, by rfl⟩ : syracuseStep 1523311 = 2284967) B2284967
theorem B2285177 : Blo 1522458 2285177 := bstep (se 2 (by rfl) ⟨856941, by rfl⟩ : syracuseStep 2285177 = 1713883) B1713883
theorem B1523367 : Blo 1522458 1523367 := bstep (se 1 (by rfl) ⟨1142525, by rfl⟩ : syracuseStep 1523367 = 2285051) B2285051
theorem B1523431 : Blo 1522458 1523431 := bstep (se 1 (by rfl) ⟨1142573, by rfl⟩ : syracuseStep 1523431 = 2285147) B2285147
theorem B1523487 : Blo 1522458 1523487 := bstep (se 1 (by rfl) ⟨1142615, by rfl⟩ : syracuseStep 1523487 = 2285231) B2285231
theorem B1523567 : Blo 1522458 1523567 := bstep (se 1 (by rfl) ⟨1142675, by rfl⟩ : syracuseStep 1523567 = 2285351) B2285351
theorem B2285423 : Blo 1522458 2285423 := bstep (se 1 (by rfl) ⟨1714067, by rfl⟩ : syracuseStep 2285423 = 3428135) B3428135
theorem B4120475 : Blo 1522458 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B1523623 : Blo 1522458 1523623 := bstep (se 1 (by rfl) ⟨1142717, by rfl⟩ : syracuseStep 1523623 = 2285435) B2285435
theorem B5783507 : Blo 1522458 5783507 := bstep (se 1 (by rfl) ⟨4337630, by rfl⟩ : syracuseStep 5783507 = 8675261) B8675261
theorem B2285609 : Blo 1522458 2285609 := bstep (se 2 (by rfl) ⟨857103, by rfl⟩ : syracuseStep 2285609 = 1714207) B1714207
theorem B2285639 : Blo 1522458 2285639 := bstep (se 1 (by rfl) ⟨1714229, by rfl⟩ : syracuseStep 2285639 = 3428459) B3428459
theorem B2285675 : Blo 1522458 2285675 := bstep (se 1 (by rfl) ⟨1714256, by rfl⟩ : syracuseStep 2285675 = 3428513) B3428513
theorem B6504583 : Blo 1522458 6504583 := bstep (se 1 (by rfl) ⟨4878437, by rfl⟩ : syracuseStep 6504583 = 9756875) B9756875
theorem B2441353 : Blo 1522458 2441353 := bstep (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) B1831015
theorem B2285759 : Blo 1522458 2285759 := bstep (se 1 (by rfl) ⟨1714319, by rfl⟩ : syracuseStep 2285759 = 3428639) B3428639
theorem B4882717 : Blo 1522458 4882717 := bstep (se 3 (by rfl) ⟨915509, by rfl⟩ : syracuseStep 4882717 = 1831019) B1831019
theorem B1524071 : Blo 1522458 1524071 := bstep (se 1 (by rfl) ⟨1143053, by rfl⟩ : syracuseStep 1524071 = 2286107) B2286107
theorem B2285945 : Blo 1522458 2285945 := bstep (se 2 (by rfl) ⟨857229, by rfl⟩ : syracuseStep 2285945 = 1714459) B1714459
theorem B9265619 : Blo 1522458 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B1524191 : Blo 1522458 1524191 := bstep (se 1 (by rfl) ⟨1143143, by rfl⟩ : syracuseStep 1524191 = 2286287) B2286287
theorem B1524199 : Blo 1522458 1524199 := bstep (se 1 (by rfl) ⟨1143149, by rfl⟩ : syracuseStep 1524199 = 2286299) B2286299
theorem B2286239 : Blo 1522458 2286239 := bstep (se 1 (by rfl) ⟨1714679, by rfl⟩ : syracuseStep 2286239 = 3429359) B3429359
theorem B70353569 : Blo 1522458 70353569 := bstep (se 2 (by rfl) ⟨26382588, by rfl⟩ : syracuseStep 70353569 = 52765177) B52765177
theorem B11576033 : Blo 1522458 11576033 := bstep (se 2 (by rfl) ⟨4341012, by rfl⟩ : syracuseStep 11576033 = 8682025) B8682025
theorem B5784311 : Blo 1522458 5784311 := bstep (se 1 (by rfl) ⟨4338233, by rfl⟩ : syracuseStep 5784311 = 8676467) B8676467
theorem B8676193 : Blo 1522458 8676193 := bstep (se 2 (by rfl) ⟨3253572, by rfl⟩ : syracuseStep 8676193 = 6507145) B6507145
theorem B2286575 : Blo 1522458 2286575 := bstep (se 1 (by rfl) ⟨1714931, by rfl⟩ : syracuseStep 2286575 = 3429863) B3429863
theorem B2286683 : Blo 1522458 2286683 := bstep (se 1 (by rfl) ⟨1715012, by rfl⟩ : syracuseStep 2286683 = 3430025) B3430025
theorem B1713307 : Blo 1522458 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B3425543 : Blo 1522458 3425543 := bstep (se 1 (by rfl) ⟨2569157, by rfl⟩ : syracuseStep 3425543 = 5138315) B5138315
theorem B2893295 : Blo 1522458 2893295 := bstep (se 1 (by rfl) ⟨2169971, by rfl⟩ : syracuseStep 2893295 = 4339943) B4339943
theorem B3425975 : Blo 1522458 3425975 := bstep (se 1 (by rfl) ⟨2569481, by rfl⟩ : syracuseStep 3425975 = 5138963) B5138963
theorem B1713991 : Blo 1522458 1713991 := bstep (se 1 (by rfl) ⟨1285493, by rfl⟩ : syracuseStep 1713991 = 2570987) B2570987
theorem B19785707 : Blo 1522458 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B3426425 : Blo 1522458 3426425 := bstep (se 2 (by rfl) ⟨1284909, by rfl⟩ : syracuseStep 3426425 = 2569819) B2569819
theorem B3426623 : Blo 1522458 3426623 := bstep (se 1 (by rfl) ⟨2569967, by rfl⟩ : syracuseStep 3426623 = 5139935) B5139935
theorem B10987933 : Blo 1522458 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B11569715 : Blo 1522458 11569715 := bstep (se 1 (by rfl) ⟨8677286, by rfl⟩ : syracuseStep 11569715 = 17354573) B17354573
theorem B21973609 : Blo 1522458 21973609 := bstep (se 2 (by rfl) ⟨8240103, by rfl⟩ : syracuseStep 21973609 = 16480207) B16480207
theorem B2714489 : Blo 1522458 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B4337003 : Blo 1522458 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B5492123 : Blo 1522458 5492123 := bstep (se 1 (by rfl) ⟨4119092, by rfl⟩ : syracuseStep 5492123 = 8238185) B8238185
theorem B8678927 : Blo 1522458 8678927 := bstep (se 1 (by rfl) ⟨6509195, by rfl⟩ : syracuseStep 8678927 = 13018391) B13018391
theorem B13889087 : Blo 1522458 13889087 := bstep (se 1 (by rfl) ⟨10416815, by rfl⟩ : syracuseStep 13889087 = 20833631) B20833631
theorem B26029673 : Blo 1522458 26029673 := bstep (se 2 (by rfl) ⟨9761127, by rfl⟩ : syracuseStep 26029673 = 19522255) B19522255
theorem B8679383 : Blo 1522458 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B9760823 : Blo 1522458 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B4878463 : Blo 1522458 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B16462217 : Blo 1522458 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B5141339 : Blo 1522458 5141339 := bstep (se 1 (by rfl) ⟨3856004, by rfl⟩ : syracuseStep 5141339 = 7712009) B7712009
theorem B4289377 : Blo 1522458 4289377 := bstep (se 2 (by rfl) ⟨1608516, by rfl⟩ : syracuseStep 4289377 = 3217033) B3217033
theorem B7713953 : Blo 1522458 7713953 := bstep (se 2 (by rfl) ⟨2892732, by rfl⟩ : syracuseStep 7713953 = 5785465) B5785465
theorem B3855671 : Blo 1522458 3855671 := bstep (se 1 (by rfl) ⟨2891753, by rfl⟩ : syracuseStep 3855671 = 5783507) B5783507
theorem B2569529 : Blo 1522458 2569529 := bstep (se 2 (by rfl) ⟨963573, by rfl⟩ : syracuseStep 2569529 = 1927147) B1927147
theorem B2569583 : Blo 1522458 2569583 := bstep (se 1 (by rfl) ⟨1927187, by rfl⟩ : syracuseStep 2569583 = 3854375) B3854375
theorem B8680841 : Blo 1522458 8680841 := bstep (se 2 (by rfl) ⟨3255315, by rfl⟩ : syracuseStep 8680841 = 6510631) B6510631
theorem B2570143 : Blo 1522458 2570143 := bstep (se 1 (by rfl) ⟨1927607, by rfl⟩ : syracuseStep 2570143 = 3855215) B3855215
theorem B8673277 : Blo 1522458 8673277 := bstep (se 3 (by rfl) ⟨1626239, by rfl⟩ : syracuseStep 8673277 = 3252479) B3252479
theorem B3856511 : Blo 1522458 3856511 := bstep (se 1 (by rfl) ⟨2892383, by rfl⟩ : syracuseStep 3856511 = 5784767) B5784767
theorem B2283743 : Blo 1522458 2283743 := bstep (se 1 (by rfl) ⟨1712807, by rfl⟩ : syracuseStep 2283743 = 3425615) B3425615
theorem B2283803 : Blo 1522458 2283803 := bstep (se 1 (by rfl) ⟨1712852, by rfl⟩ : syracuseStep 2283803 = 3425705) B3425705
theorem B3660059 : Blo 1522458 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B32938271 : Blo 1522458 32938271 := bstep (se 1 (by rfl) ⟨24703703, by rfl⟩ : syracuseStep 32938271 = 49407407) B49407407
theorem B2472329 : Blo 1522458 2472329 := bstep (se 2 (by rfl) ⟨927123, by rfl⟩ : syracuseStep 2472329 = 1854247) B1854247
theorem B3856855 : Blo 1522458 3856855 := bstep (se 1 (by rfl) ⟨2892641, by rfl⟩ : syracuseStep 3856855 = 5785283) B5785283
theorem B5782063 : Blo 1522458 5782063 := bstep (se 1 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 5782063 = 8673095) B8673095
theorem B2284127 : Blo 1522458 2284127 := bstep (se 1 (by rfl) ⟨1713095, by rfl⟩ : syracuseStep 2284127 = 3426191) B3426191
theorem B9763487 : Blo 1522458 9763487 := bstep (se 1 (by rfl) ⟨7322615, by rfl⟩ : syracuseStep 9763487 = 14645231) B14645231
theorem B2284223 : Blo 1522458 2284223 := bstep (se 1 (by rfl) ⟨1713167, by rfl⟩ : syracuseStep 2284223 = 3426335) B3426335
theorem B2284265 : Blo 1522458 2284265 := bstep (se 2 (by rfl) ⟨856599, by rfl⟩ : syracuseStep 2284265 = 1713199) B1713199
theorem B3857129 : Blo 1522458 3857129 := bstep (se 2 (by rfl) ⟨1446423, by rfl⟩ : syracuseStep 3857129 = 2892847) B2892847
theorem B2169595 : Blo 1522458 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B70400863 : Blo 1522458 70400863 := bstep (se 1 (by rfl) ⟨52800647, by rfl⟩ : syracuseStep 70400863 = 105601295) B105601295
theorem B2284391 : Blo 1522458 2284391 := bstep (se 1 (by rfl) ⟨1713293, by rfl⟩ : syracuseStep 2284391 = 3426587) B3426587
theorem B4340603 : Blo 1522458 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B2284457 : Blo 1522458 2284457 := bstep (se 2 (by rfl) ⟨856671, by rfl⟩ : syracuseStep 2284457 = 1713343) B1713343
theorem B19782589 : Blo 1522458 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B1522623 : Blo 1522458 1522623 := bstep (se 1 (by rfl) ⟨1141967, by rfl⟩ : syracuseStep 1522623 = 2283935) B2283935
theorem B1522671 : Blo 1522458 1522671 := bstep (se 1 (by rfl) ⟨1142003, by rfl⟩ : syracuseStep 1522671 = 2284007) B2284007
theorem B2284607 : Blo 1522458 2284607 := bstep (se 1 (by rfl) ⟨1713455, by rfl⟩ : syracuseStep 2284607 = 3426911) B3426911
theorem B2284649 : Blo 1522458 2284649 := bstep (se 2 (by rfl) ⟨856743, by rfl⟩ : syracuseStep 2284649 = 1713487) B1713487
theorem B3857615 : Blo 1522458 3857615 := bstep (se 1 (by rfl) ⟨2893211, by rfl⟩ : syracuseStep 3857615 = 5786423) B5786423
theorem B2284775 : Blo 1522458 2284775 := bstep (se 1 (by rfl) ⟨1713581, by rfl⟩ : syracuseStep 2284775 = 3427163) B3427163
theorem B3661031 : Blo 1522458 3661031 := bstep (se 1 (by rfl) ⟨2745773, by rfl⟩ : syracuseStep 3661031 = 5491547) B5491547
theorem B8674553 : Blo 1522458 8674553 := bstep (se 2 (by rfl) ⟨3252957, by rfl⟩ : syracuseStep 8674553 = 6505915) B6505915
theorem B8674735 : Blo 1522458 8674735 := bstep (se 1 (by rfl) ⟨6506051, by rfl⟩ : syracuseStep 8674735 = 13012103) B13012103
theorem B1523167 : Blo 1522458 1523167 := bstep (se 1 (by rfl) ⟨1142375, by rfl⟩ : syracuseStep 1523167 = 2284751) B2284751
theorem B1523247 : Blo 1522458 1523247 := bstep (se 1 (by rfl) ⟨1142435, by rfl⟩ : syracuseStep 1523247 = 2284871) B2284871
theorem B4398695 : Blo 1522458 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B1523355 : Blo 1522458 1523355 := bstep (se 1 (by rfl) ⟨1142516, by rfl⟩ : syracuseStep 1523355 = 2285033) B2285033
theorem B2440859 : Blo 1522458 2440859 := bstep (se 1 (by rfl) ⟨1830644, by rfl⟩ : syracuseStep 2440859 = 3661289) B3661289
theorem B2285279 : Blo 1522458 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B4120303 : Blo 1522458 4120303 := bstep (se 1 (by rfl) ⟨3090227, by rfl⟩ : syracuseStep 4120303 = 6180455) B6180455
theorem B1523451 : Blo 1522458 1523451 := bstep (se 1 (by rfl) ⟨1142588, by rfl⟩ : syracuseStep 1523451 = 2285177) B2285177
theorem B9756413 : Blo 1522458 9756413 := bstep (se 3 (by rfl) ⟨1829327, by rfl⟩ : syracuseStep 9756413 = 3658655) B3658655
theorem B4398857 : Blo 1522458 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B1523615 : Blo 1522458 1523615 := bstep (se 1 (by rfl) ⟨1142711, by rfl⟩ : syracuseStep 1523615 = 2285423) B2285423
theorem B14647229 : Blo 1522458 14647229 := bstep (se 3 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 14647229 = 5492711) B5492711
theorem B1523739 : Blo 1522458 1523739 := bstep (se 1 (by rfl) ⟨1142804, by rfl⟩ : syracuseStep 1523739 = 2285609) B2285609
theorem B1523759 : Blo 1522458 1523759 := bstep (se 1 (by rfl) ⟨1142819, by rfl⟩ : syracuseStep 1523759 = 2285639) B2285639
theorem B1523783 : Blo 1522458 1523783 := bstep (se 1 (by rfl) ⟨1142837, by rfl⟩ : syracuseStep 1523783 = 2285675) B2285675
theorem B1523839 : Blo 1522458 1523839 := bstep (se 1 (by rfl) ⟨1142879, by rfl⟩ : syracuseStep 1523839 = 2285759) B2285759
theorem B6504617 : Blo 1522458 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B1523963 : Blo 1522458 1523963 := bstep (se 1 (by rfl) ⟨1142972, by rfl⟩ : syracuseStep 1523963 = 2285945) B2285945
theorem B6177079 : Blo 1522458 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B1524159 : Blo 1522458 1524159 := bstep (se 1 (by rfl) ⟨1143119, by rfl⟩ : syracuseStep 1524159 = 2286239) B2286239
theorem B7717355 : Blo 1522458 7717355 := bstep (se 1 (by rfl) ⟨5788016, by rfl⟩ : syracuseStep 7717355 = 11576033) B11576033
theorem B1524383 : Blo 1522458 1524383 := bstep (se 1 (by rfl) ⟨1143287, by rfl⟩ : syracuseStep 1524383 = 2286575) B2286575
theorem B1524455 : Blo 1522458 1524455 := bstep (se 1 (by rfl) ⟨1143341, by rfl⟩ : syracuseStep 1524455 = 2286683) B2286683
theorem B7709417 : Blo 1522458 7709417 := bstep (se 2 (by rfl) ⟨2891031, by rfl⟩ : syracuseStep 7709417 = 5782063) B5782063
theorem B1713019 : Blo 1522458 1713019 := bstep (se 1 (by rfl) ⟨1284764, by rfl⟩ : syracuseStep 1713019 = 2569529) B2569529
theorem B1713055 : Blo 1522458 1713055 := bstep (se 1 (by rfl) ⟨1284791, by rfl⟩ : syracuseStep 1713055 = 2569583) B2569583
theorem B11568257 : Blo 1522458 11568257 := bstep (se 2 (by rfl) ⟨4338096, by rfl⟩ : syracuseStep 11568257 = 8676193) B8676193
theorem B5719169 : Blo 1522458 5719169 := bstep (se 2 (by rfl) ⟨2144688, by rfl⟩ : syracuseStep 5719169 = 4289377) B4289377
theorem B13190471 : Blo 1522458 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B1648219 : Blo 1522458 1648219 := bstep (se 1 (by rfl) ⟨1236164, by rfl⟩ : syracuseStep 1648219 = 2472329) B2472329
theorem B2893735 : Blo 1522458 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B5785951 : Blo 1522458 5785951 := bstep (se 1 (by rfl) ⟨4339463, by rfl⟩ : syracuseStep 5785951 = 8678927) B8678927
theorem B9259391 : Blo 1522458 9259391 := bstep (se 1 (by rfl) ⟨6944543, by rfl⟩ : syracuseStep 9259391 = 13889087) B13889087
theorem B17353115 : Blo 1522458 17353115 := bstep (se 1 (by rfl) ⟨13014836, by rfl⟩ : syracuseStep 17353115 = 26029673) B26029673
theorem B3426857 : Blo 1522458 3426857 := bstep (se 2 (by rfl) ⟨1285071, by rfl⟩ : syracuseStep 3426857 = 2570143) B2570143
theorem B5786255 : Blo 1522458 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B6507215 : Blo 1522458 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B3255137 : Blo 1522458 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B14650577 : Blo 1522458 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B3427559 : Blo 1522458 3427559 := bstep (se 1 (by rfl) ⟨2570669, by rfl⟩ : syracuseStep 3427559 = 5141339) B5141339
theorem B29298145 : Blo 1522458 29298145 := bstep (se 2 (by rfl) ⟨10986804, by rfl⟩ : syracuseStep 29298145 = 21973609) B21973609
theorem B5787227 : Blo 1522458 5787227 := bstep (se 1 (by rfl) ⟨4340420, by rfl⟩ : syracuseStep 5787227 = 8680841) B8680841
theorem B1928863 : Blo 1522458 1928863 := bstep (se 1 (by rfl) ⟨1446647, by rfl⟩ : syracuseStep 1928863 = 2893295) B2893295
theorem B93867817 : Blo 1522458 93867817 := bstep (se 2 (by rfl) ⟨35200431, by rfl⟩ : syracuseStep 93867817 = 70400863) B70400863
theorem B11571173 : Blo 1522458 11571173 := bstep (se 4 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 11571173 = 2169595) B2169595
theorem B21958847 : Blo 1522458 21958847 := bstep (se 1 (by rfl) ⟨16469135, by rfl⟩ : syracuseStep 21958847 = 32938271) B32938271
theorem B7713143 : Blo 1522458 7713143 := bstep (se 1 (by rfl) ⟨5784857, by rfl⟩ : syracuseStep 7713143 = 11569715) B11569715
theorem B6508957 : Blo 1522458 6508957 := bstep (se 3 (by rfl) ⟨1220429, by rfl⟩ : syracuseStep 6508957 = 2440859) B2440859
theorem B187609517 : Blo 1522458 187609517 := bstep (se 3 (by rfl) ⟨35176784, by rfl⟩ : syracuseStep 187609517 = 70353569) B70353569
theorem B6508991 : Blo 1522458 6508991 := bstep (se 1 (by rfl) ⟨4881743, by rfl⟩ : syracuseStep 6508991 = 9763487) B9763487
theorem B5493737 : Blo 1522458 5493737 := bstep (se 2 (by rfl) ⟨2060151, by rfl⟩ : syracuseStep 5493737 = 4120303) B4120303
theorem B11564369 : Blo 1522458 11564369 := bstep (se 2 (by rfl) ⟨4336638, by rfl⟩ : syracuseStep 11564369 = 8673277) B8673277
theorem B8672777 : Blo 1522458 8672777 := bstep (se 2 (by rfl) ⟨3252291, by rfl⟩ : syracuseStep 8672777 = 6504583) B6504583
theorem B10974811 : Blo 1522458 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B6510289 : Blo 1522458 6510289 := bstep (se 2 (by rfl) ⟨2441358, by rfl⟩ : syracuseStep 6510289 = 4882717) B4882717
theorem B3856207 : Blo 1522458 3856207 := bstep (se 1 (by rfl) ⟨2892155, by rfl⟩ : syracuseStep 3856207 = 5784311) B5784311
theorem B5142473 : Blo 1522458 5142473 := bstep (se 2 (by rfl) ⟨1928427, by rfl⟩ : syracuseStep 5142473 = 3856855) B3856855
theorem B5142635 : Blo 1522458 5142635 := bstep (se 1 (by rfl) ⟨3856976, by rfl⟩ : syracuseStep 5142635 = 7713953) B7713953
theorem B2283695 : Blo 1522458 2283695 := bstep (se 1 (by rfl) ⟨1712771, by rfl⟩ : syracuseStep 2283695 = 3425543) B3425543
theorem B2570447 : Blo 1522458 2570447 := bstep (se 1 (by rfl) ⟨1927835, by rfl⟩ : syracuseStep 2570447 = 3855671) B3855671
theorem B11565341 : Blo 1522458 11565341 := bstep (se 3 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 11565341 = 4337003) B4337003
theorem B2283983 : Blo 1522458 2283983 := bstep (se 1 (by rfl) ⟨1712987, by rfl⟩ : syracuseStep 2283983 = 3425975) B3425975
theorem B26376785 : Blo 1522458 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B2284283 : Blo 1522458 2284283 := bstep (se 1 (by rfl) ⟨1713212, by rfl⟩ : syracuseStep 2284283 = 3426425) B3426425
theorem B2571007 : Blo 1522458 2571007 := bstep (se 1 (by rfl) ⟨1928255, by rfl⟩ : syracuseStep 2571007 = 3856511) B3856511
theorem B1522495 : Blo 1522458 1522495 := bstep (se 1 (by rfl) ⟨1141871, by rfl⟩ : syracuseStep 1522495 = 2283743) B2283743
theorem B2440039 : Blo 1522458 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B1522535 : Blo 1522458 1522535 := bstep (se 1 (by rfl) ⟨1141901, by rfl⟩ : syracuseStep 1522535 = 2283803) B2283803
theorem B2284409 : Blo 1522458 2284409 := bstep (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) B1713307
theorem B2284415 : Blo 1522458 2284415 := bstep (se 1 (by rfl) ⟨1713311, by rfl⟩ : syracuseStep 2284415 = 3426623) B3426623
theorem B1522751 : Blo 1522458 1522751 := bstep (se 1 (by rfl) ⟨1142063, by rfl⟩ : syracuseStep 1522751 = 2284127) B2284127
theorem B1522815 : Blo 1522458 1522815 := bstep (se 1 (by rfl) ⟨1142111, by rfl⟩ : syracuseStep 1522815 = 2284223) B2284223
theorem B1522843 : Blo 1522458 1522843 := bstep (se 1 (by rfl) ⟨1142132, by rfl⟩ : syracuseStep 1522843 = 2284265) B2284265
theorem B2571419 : Blo 1522458 2571419 := bstep (se 1 (by rfl) ⟨1928564, by rfl⟩ : syracuseStep 2571419 = 3857129) B3857129
theorem B11566313 : Blo 1522458 11566313 := bstep (se 2 (by rfl) ⟨4337367, by rfl⟩ : syracuseStep 11566313 = 8674735) B8674735
theorem B1522927 : Blo 1522458 1522927 := bstep (se 1 (by rfl) ⟨1142195, by rfl⟩ : syracuseStep 1522927 = 2284391) B2284391
theorem B1809659 : Blo 1522458 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B1522971 : Blo 1522458 1522971 := bstep (se 1 (by rfl) ⟨1142228, by rfl⟩ : syracuseStep 1522971 = 2284457) B2284457
theorem B1523071 : Blo 1522458 1523071 := bstep (se 1 (by rfl) ⟨1142303, by rfl⟩ : syracuseStep 1523071 = 2284607) B2284607
theorem B1523099 : Blo 1522458 1523099 := bstep (se 1 (by rfl) ⟨1142324, by rfl⟩ : syracuseStep 1523099 = 2284649) B2284649
theorem B2571743 : Blo 1522458 2571743 := bstep (se 1 (by rfl) ⟨1928807, by rfl⟩ : syracuseStep 2571743 = 3857615) B3857615
theorem B1523183 : Blo 1522458 1523183 := bstep (se 1 (by rfl) ⟨1142387, by rfl⟩ : syracuseStep 1523183 = 2284775) B2284775
theorem B2440687 : Blo 1522458 2440687 := bstep (se 1 (by rfl) ⟨1830515, by rfl⟩ : syracuseStep 2440687 = 3661031) B3661031
theorem B5783035 : Blo 1522458 5783035 := bstep (se 1 (by rfl) ⟨4337276, by rfl⟩ : syracuseStep 5783035 = 8674553) B8674553
theorem B3661415 : Blo 1522458 3661415 := bstep (se 1 (by rfl) ⟨2746061, by rfl⟩ : syracuseStep 3661415 = 5492123) B5492123
theorem B2932463 : Blo 1522458 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B2285321 : Blo 1522458 2285321 := bstep (se 2 (by rfl) ⟨856995, by rfl⟩ : syracuseStep 2285321 = 1713991) B1713991
theorem B1523519 : Blo 1522458 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B6504275 : Blo 1522458 6504275 := bstep (se 1 (by rfl) ⟨4878206, by rfl⟩ : syracuseStep 6504275 = 9756413) B9756413
theorem B2932571 : Blo 1522458 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B9764819 : Blo 1522458 9764819 := bstep (se 1 (by rfl) ⟨7323614, by rfl⟩ : syracuseStep 9764819 = 14647229) B14647229
theorem B14639231 : Blo 1522458 14639231 := bstep (se 1 (by rfl) ⟨10979423, by rfl⟩ : syracuseStep 14639231 = 21958847) B21958847
theorem B5144903 : Blo 1522458 5144903 := bstep (se 1 (by rfl) ⟨3858677, by rfl⟩ : syracuseStep 5144903 = 7717355) B7717355
theorem B3662491 : Blo 1522458 3662491 := bstep (se 1 (by rfl) ⟨2746868, by rfl⟩ : syracuseStep 3662491 = 5493737) B5493737
theorem B4825757 : Blo 1522458 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B7709579 : Blo 1522458 7709579 := bstep (se 1 (by rfl) ⟨5782184, by rfl⟩ : syracuseStep 7709579 = 11564369) B11564369
theorem B24691709 : Blo 1522458 24691709 := bstep (se 3 (by rfl) ⟨4629695, by rfl⟩ : syracuseStep 24691709 = 9259391) B9259391
theorem B3253385 : Blo 1522458 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B1713631 : Blo 1522458 1713631 := bstep (se 1 (by rfl) ⟨1285223, by rfl⟩ : syracuseStep 1713631 = 2570447) B2570447
theorem B7710227 : Blo 1522458 7710227 := bstep (se 1 (by rfl) ⟨5782670, by rfl⟩ : syracuseStep 7710227 = 11565341) B11565341
theorem B11568743 : Blo 1522458 11568743 := bstep (se 1 (by rfl) ⟨8676557, by rfl⟩ : syracuseStep 11568743 = 17353115) B17353115
theorem B3254249 : Blo 1522458 3254249 := bstep (se 2 (by rfl) ⟨1220343, by rfl⟩ : syracuseStep 3254249 = 2440687) B2440687
theorem B7710713 : Blo 1522458 7710713 := bstep (se 2 (by rfl) ⟨2891517, by rfl⟩ : syracuseStep 7710713 = 5783035) B5783035
theorem B1714279 : Blo 1522458 1714279 := bstep (se 1 (by rfl) ⟨1285709, by rfl⟩ : syracuseStep 1714279 = 2571419) B2571419
theorem B14633081 : Blo 1522458 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B9767051 : Blo 1522458 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B7710875 : Blo 1522458 7710875 := bstep (se 1 (by rfl) ⟨5783156, by rfl⟩ : syracuseStep 7710875 = 11566313) B11566313
theorem B1714495 : Blo 1522458 1714495 := bstep (se 1 (by rfl) ⟨1285871, by rfl⟩ : syracuseStep 1714495 = 2571743) B2571743
theorem B4336183 : Blo 1522458 4336183 := bstep (se 1 (by rfl) ⟨3252137, by rfl⟩ : syracuseStep 4336183 = 6504275) B6504275
theorem B4336411 : Blo 1522458 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B5139611 : Blo 1522458 5139611 := bstep (se 1 (by rfl) ⟨3854708, by rfl⟩ : syracuseStep 5139611 = 7709417) B7709417
theorem B8678609 : Blo 1522458 8678609 := bstep (se 2 (by rfl) ⟨3254478, by rfl⟩ : syracuseStep 8678609 = 6508957) B6508957
theorem B7712171 : Blo 1522458 7712171 := bstep (se 1 (by rfl) ⟨5784128, by rfl⟩ : syracuseStep 7712171 = 11568257) B11568257
theorem B3812779 : Blo 1522458 3812779 := bstep (se 1 (by rfl) ⟨2859584, by rfl⟩ : syracuseStep 3812779 = 5719169) B5719169
theorem B8793647 : Blo 1522458 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B3428009 : Blo 1522458 3428009 := bstep (se 2 (by rfl) ⟨1285503, by rfl⟩ : syracuseStep 3428009 = 2571007) B2571007
theorem B3428315 : Blo 1522458 3428315 := bstep (se 1 (by rfl) ⟨2571236, by rfl⟩ : syracuseStep 3428315 = 5142473) B5142473
theorem B3428423 : Blo 1522458 3428423 := bstep (se 1 (by rfl) ⟨2571317, by rfl⟩ : syracuseStep 3428423 = 5142635) B5142635
theorem B32944421 : Blo 1522458 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B17584523 : Blo 1522458 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B4338143 : Blo 1522458 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B7819901 : Blo 1522458 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B39064193 : Blo 1522458 39064193 := bstep (se 2 (by rfl) ⟨14649072, by rfl⟩ : syracuseStep 39064193 = 29298145) B29298145
theorem B7820189 : Blo 1522458 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B8680385 : Blo 1522458 8680385 := bstep (se 2 (by rfl) ⟨3255144, by rfl⟩ : syracuseStep 8680385 = 6510289) B6510289
theorem B5141609 : Blo 1522458 5141609 := bstep (se 2 (by rfl) ⟨1928103, by rfl⟩ : syracuseStep 5141609 = 3856207) B3856207
theorem B6509879 : Blo 1522458 6509879 := bstep (se 1 (by rfl) ⟨4882409, by rfl⟩ : syracuseStep 6509879 = 9764819) B9764819
theorem B7714115 : Blo 1522458 7714115 := bstep (se 1 (by rfl) ⟨5785586, by rfl⟩ : syracuseStep 7714115 = 11571173) B11571173
theorem B5142095 : Blo 1522458 5142095 := bstep (se 1 (by rfl) ⟨3856571, by rfl⟩ : syracuseStep 5142095 = 7713143) B7713143
theorem B125073011 : Blo 1522458 125073011 := bstep (se 1 (by rfl) ⟨93804758, by rfl⟩ : syracuseStep 125073011 = 187609517) B187609517
theorem B4339327 : Blo 1522458 4339327 := bstep (se 1 (by rfl) ⟨3254495, by rfl⟩ : syracuseStep 4339327 = 6508991) B6508991
theorem B7714601 : Blo 1522458 7714601 := bstep (se 2 (by rfl) ⟨2892975, by rfl⟩ : syracuseStep 7714601 = 5785951) B5785951
theorem B5781851 : Blo 1522458 5781851 := bstep (se 1 (by rfl) ⟨4336388, by rfl⟩ : syracuseStep 5781851 = 8672777) B8672777
theorem B2284025 : Blo 1522458 2284025 := bstep (se 2 (by rfl) ⟨856509, by rfl⟩ : syracuseStep 2284025 = 1713019) B1713019
theorem B2284073 : Blo 1522458 2284073 := bstep (se 2 (by rfl) ⟨856527, by rfl⟩ : syracuseStep 2284073 = 1713055) B1713055
theorem B1522463 : Blo 1522458 1522463 := bstep (se 1 (by rfl) ⟨1141847, by rfl⟩ : syracuseStep 1522463 = 2283695) B2283695
theorem B1522655 : Blo 1522458 1522655 := bstep (se 1 (by rfl) ⟨1141991, by rfl⟩ : syracuseStep 1522655 = 2283983) B2283983
theorem B2284571 : Blo 1522458 2284571 := bstep (se 1 (by rfl) ⟨1713428, by rfl⟩ : syracuseStep 2284571 = 3426857) B3426857
theorem B3857503 : Blo 1522458 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B1522855 : Blo 1522458 1522855 := bstep (se 1 (by rfl) ⟨1142141, by rfl⟩ : syracuseStep 1522855 = 2284283) B2284283
theorem B2170091 : Blo 1522458 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B1522939 : Blo 1522458 1522939 := bstep (se 1 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 1522939 = 2284409) B2284409
theorem B1522943 : Blo 1522458 1522943 := bstep (se 1 (by rfl) ⟨1142207, by rfl⟩ : syracuseStep 1522943 = 2284415) B2284415
theorem B2285039 : Blo 1522458 2285039 := bstep (se 1 (by rfl) ⟨1713779, by rfl⟩ : syracuseStep 2285039 = 3427559) B3427559
theorem B2571817 : Blo 1522458 2571817 := bstep (se 2 (by rfl) ⟨964431, by rfl⟩ : syracuseStep 2571817 = 1928863) B1928863
theorem B140648021 : Blo 1522458 140648021 := bstep (se 8 (by rfl) ⟨824109, by rfl⟩ : syracuseStep 140648021 = 1648219) B1648219
theorem B125157089 : Blo 1522458 125157089 := bstep (se 2 (by rfl) ⟨46933908, by rfl⟩ : syracuseStep 125157089 = 93867817) B93867817
theorem B3858151 : Blo 1522458 3858151 := bstep (se 1 (by rfl) ⟨2893613, by rfl⟩ : syracuseStep 3858151 = 5787227) B5787227
theorem B2440943 : Blo 1522458 2440943 := bstep (se 1 (by rfl) ⟨1830707, by rfl⟩ : syracuseStep 2440943 = 3661415) B3661415
theorem B1523547 : Blo 1522458 1523547 := bstep (se 1 (by rfl) ⟨1142660, by rfl⟩ : syracuseStep 1523547 = 2285321) B2285321
theorem B3858313 : Blo 1522458 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B2285615 : Blo 1522458 2285615 := bstep (se 1 (by rfl) ⟨1714211, by rfl⟩ : syracuseStep 2285615 = 3428423) B3428423
theorem B2285705 : Blo 1522458 2285705 := bstep (se 2 (by rfl) ⟨857139, by rfl⟩ : syracuseStep 2285705 = 1714279) B1714279
theorem B21962947 : Blo 1522458 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B11723015 : Blo 1522458 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B2892095 : Blo 1522458 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B8675693 : Blo 1522458 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B2285993 : Blo 1522458 2285993 := bstep (se 2 (by rfl) ⟨857247, by rfl⟩ : syracuseStep 2285993 = 1714495) B1714495
theorem B26042795 : Blo 1522458 26042795 := bstep (se 1 (by rfl) ⟨19532096, by rfl⟩ : syracuseStep 26042795 = 39064193) B39064193
theorem B4883321 : Blo 1522458 4883321 := bstep (se 2 (by rfl) ⟨1831245, by rfl⟩ : syracuseStep 4883321 = 3662491) B3662491
theorem B3426407 : Blo 1522458 3426407 := bstep (se 1 (by rfl) ⟨2569805, by rfl⟩ : syracuseStep 3426407 = 5139611) B5139611
theorem B5785739 : Blo 1522458 5785739 := bstep (se 1 (by rfl) ⟨4339304, by rfl⟩ : syracuseStep 5785739 = 8678609) B8678609
theorem B5785769 : Blo 1522458 5785769 := bstep (se 2 (by rfl) ⟨2169663, by rfl⟩ : syracuseStep 5785769 = 4339327) B4339327
theorem B83438059 : Blo 1522458 83438059 := bstep (se 1 (by rfl) ⟨62578544, by rfl⟩ : syracuseStep 83438059 = 125157089) B125157089
theorem B39037949 : Blo 1522458 39037949 := bstep (se 3 (by rfl) ⟨7319615, by rfl⟩ : syracuseStep 39037949 = 14639231) B14639231
theorem B5213267 : Blo 1522458 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B5139719 : Blo 1522458 5139719 := bstep (se 1 (by rfl) ⟨3854789, by rfl⟩ : syracuseStep 5139719 = 7709579) B7709579
theorem B5213459 : Blo 1522458 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B5786909 : Blo 1522458 5786909 := bstep (se 3 (by rfl) ⟨1085045, by rfl⟩ : syracuseStep 5786909 = 2170091) B2170091
theorem B5786923 : Blo 1522458 5786923 := bstep (se 1 (by rfl) ⟨4340192, by rfl⟩ : syracuseStep 5786923 = 8680385) B8680385
theorem B16461139 : Blo 1522458 16461139 := bstep (se 1 (by rfl) ⟨12345854, by rfl⟩ : syracuseStep 16461139 = 24691709) B24691709
theorem B3427739 : Blo 1522458 3427739 := bstep (se 1 (by rfl) ⟨2570804, by rfl⟩ : syracuseStep 3427739 = 5141609) B5141609
theorem B5140151 : Blo 1522458 5140151 := bstep (se 1 (by rfl) ⟨3855113, by rfl⟩ : syracuseStep 5140151 = 7710227) B7710227
theorem B3428063 : Blo 1522458 3428063 := bstep (se 1 (by rfl) ⟨2571047, by rfl⟩ : syracuseStep 3428063 = 5142095) B5142095
theorem B7712495 : Blo 1522458 7712495 := bstep (se 1 (by rfl) ⟨5784371, by rfl⟩ : syracuseStep 7712495 = 11568743) B11568743
theorem B83382007 : Blo 1522458 83382007 := bstep (se 1 (by rfl) ⟨62536505, by rfl⟩ : syracuseStep 83382007 = 125073011) B125073011
theorem B5140475 : Blo 1522458 5140475 := bstep (se 1 (by rfl) ⟨3855356, by rfl⟩ : syracuseStep 5140475 = 7710713) B7710713
theorem B5140583 : Blo 1522458 5140583 := bstep (se 1 (by rfl) ⟨3855437, by rfl⟩ : syracuseStep 5140583 = 7710875) B7710875
theorem B3854567 : Blo 1522458 3854567 := bstep (se 1 (by rfl) ⟨2890925, by rfl⟩ : syracuseStep 3854567 = 5781851) B5781851
theorem B5083705 : Blo 1522458 5083705 := bstep (se 2 (by rfl) ⟨1906389, by rfl⟩ : syracuseStep 5083705 = 3812779) B3812779
theorem B3429089 : Blo 1522458 3429089 := bstep (se 2 (by rfl) ⟨1285908, by rfl⟩ : syracuseStep 3429089 = 2571817) B2571817
theorem B5141447 : Blo 1522458 5141447 := bstep (se 1 (by rfl) ⟨3856085, by rfl⟩ : syracuseStep 5141447 = 7712171) B7712171
theorem B5862431 : Blo 1522458 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B1627295 : Blo 1522458 1627295 := bstep (se 1 (by rfl) ⟨1220471, by rfl⟩ : syracuseStep 1627295 = 2440943) B2440943
theorem B3429935 : Blo 1522458 3429935 := bstep (se 1 (by rfl) ⟨2572451, by rfl⟩ : syracuseStep 3429935 = 5144903) B5144903
theorem B3217171 : Blo 1522458 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B5781577 : Blo 1522458 5781577 := bstep (se 2 (by rfl) ⟨2168091, by rfl⟩ : syracuseStep 5781577 = 4336183) B4336183
theorem B4339919 : Blo 1522458 4339919 := bstep (se 1 (by rfl) ⟨3254939, by rfl⟩ : syracuseStep 4339919 = 6509879) B6509879
theorem B5142743 : Blo 1522458 5142743 := bstep (se 1 (by rfl) ⟨3857057, by rfl⟩ : syracuseStep 5142743 = 7714115) B7714115
theorem B5781881 : Blo 1522458 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B5143067 : Blo 1522458 5143067 := bstep (se 1 (by rfl) ⟨3857300, by rfl⟩ : syracuseStep 5143067 = 7714601) B7714601
theorem B2169499 : Blo 1522458 2169499 := bstep (se 1 (by rfl) ⟨1627124, by rfl⟩ : syracuseStep 2169499 = 3254249) B3254249
theorem B9755387 : Blo 1522458 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B6511367 : Blo 1522458 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B5143337 : Blo 1522458 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1522683 : Blo 1522458 1522683 := bstep (se 1 (by rfl) ⟨1142012, by rfl⟩ : syracuseStep 1522683 = 2284025) B2284025
theorem B1522715 : Blo 1522458 1522715 := bstep (se 1 (by rfl) ⟨1142036, by rfl⟩ : syracuseStep 1522715 = 2284073) B2284073
theorem B2284841 : Blo 1522458 2284841 := bstep (se 2 (by rfl) ⟨856815, by rfl⟩ : syracuseStep 2284841 = 1713631) B1713631
theorem B1523047 : Blo 1522458 1523047 := bstep (se 1 (by rfl) ⟨1142285, by rfl⟩ : syracuseStep 1523047 = 2284571) B2284571
theorem B5144201 : Blo 1522458 5144201 := bstep (se 2 (by rfl) ⟨1929075, by rfl⟩ : syracuseStep 5144201 = 3858151) B3858151
theorem B1523359 : Blo 1522458 1523359 := bstep (se 1 (by rfl) ⟨1142519, by rfl⟩ : syracuseStep 1523359 = 2285039) B2285039
theorem B93765347 : Blo 1522458 93765347 := bstep (se 1 (by rfl) ⟨70324010, by rfl⟩ : syracuseStep 93765347 = 140648021) B140648021
theorem B2285339 : Blo 1522458 2285339 := bstep (se 1 (by rfl) ⟨1714004, by rfl⟩ : syracuseStep 2285339 = 3428009) B3428009
theorem B5144417 : Blo 1522458 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B2285543 : Blo 1522458 2285543 := bstep (se 1 (by rfl) ⟨1714157, by rfl⟩ : syracuseStep 2285543 = 3428315) B3428315
theorem B1523743 : Blo 1522458 1523743 := bstep (se 1 (by rfl) ⟨1142807, by rfl⟩ : syracuseStep 1523743 = 2285615) B2285615
theorem B1523803 : Blo 1522458 1523803 := bstep (se 1 (by rfl) ⟨1142852, by rfl⟩ : syracuseStep 1523803 = 2285705) B2285705
theorem B7708769 : Blo 1522458 7708769 := bstep (se 2 (by rfl) ⟨2890788, by rfl⟩ : syracuseStep 7708769 = 5781577) B5781577
theorem B5783795 : Blo 1522458 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B1523995 : Blo 1522458 1523995 := bstep (se 1 (by rfl) ⟨1142996, by rfl⟩ : syracuseStep 1523995 = 2285993) B2285993
theorem B2286059 : Blo 1522458 2286059 := bstep (se 1 (by rfl) ⟨1714544, by rfl⟩ : syracuseStep 2286059 = 3429089) B3429089
theorem B31261373 : Blo 1522458 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B3908287 : Blo 1522458 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B2892665 : Blo 1522458 2892665 := bstep (se 2 (by rfl) ⟨1084749, by rfl⟩ : syracuseStep 2892665 = 2169499) B2169499
theorem B2286623 : Blo 1522458 2286623 := bstep (se 1 (by rfl) ⟨1714967, by rfl⟩ : syracuseStep 2286623 = 3429935) B3429935
theorem B21948185 : Blo 1522458 21948185 := bstep (se 2 (by rfl) ⟨8230569, by rfl⟩ : syracuseStep 21948185 = 16461139) B16461139
theorem B3475511 : Blo 1522458 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B3426479 : Blo 1522458 3426479 := bstep (se 1 (by rfl) ⟨2569859, by rfl⟩ : syracuseStep 3426479 = 5139719) B5139719
theorem B3475639 : Blo 1522458 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B111176009 : Blo 1522458 111176009 := bstep (se 2 (by rfl) ⟨41691003, by rfl⟩ : syracuseStep 111176009 = 83382007) B83382007
theorem B3426767 : Blo 1522458 3426767 := bstep (se 1 (by rfl) ⟨2570075, by rfl⟩ : syracuseStep 3426767 = 5140151) B5140151
theorem B3426983 : Blo 1522458 3426983 := bstep (se 1 (by rfl) ⟨2570237, by rfl⟩ : syracuseStep 3426983 = 5140475) B5140475
theorem B3427055 : Blo 1522458 3427055 := bstep (se 1 (by rfl) ⟨2570291, by rfl⟩ : syracuseStep 3427055 = 5140583) B5140583
theorem B1928063 : Blo 1522458 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B17361863 : Blo 1522458 17361863 := bstep (se 1 (by rfl) ⟨13021397, by rfl⟩ : syracuseStep 17361863 = 26042795) B26042795
theorem B3255547 : Blo 1522458 3255547 := bstep (se 1 (by rfl) ⟨2441660, by rfl⟩ : syracuseStep 3255547 = 4883321) B4883321
theorem B3427631 : Blo 1522458 3427631 := bstep (se 1 (by rfl) ⟨2570723, by rfl⟩ : syracuseStep 3427631 = 5141447) B5141447
theorem B111250745 : Blo 1522458 111250745 := bstep (se 2 (by rfl) ⟨41719029, by rfl⟩ : syracuseStep 111250745 = 83438059) B83438059
theorem B6778273 : Blo 1522458 6778273 := bstep (se 2 (by rfl) ⟨2541852, by rfl⟩ : syracuseStep 6778273 = 5083705) B5083705
theorem B3428495 : Blo 1522458 3428495 := bstep (se 1 (by rfl) ⟨2571371, by rfl⟩ : syracuseStep 3428495 = 5142743) B5142743
theorem B3854587 : Blo 1522458 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B3428711 : Blo 1522458 3428711 := bstep (se 1 (by rfl) ⟨2571533, by rfl⟩ : syracuseStep 3428711 = 5143067) B5143067
theorem B3428891 : Blo 1522458 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B4289561 : Blo 1522458 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B3429467 : Blo 1522458 3429467 := bstep (se 1 (by rfl) ⟨2572100, by rfl⟩ : syracuseStep 3429467 = 5144201) B5144201
theorem B62510231 : Blo 1522458 62510231 := bstep (se 1 (by rfl) ⟨46882673, by rfl⟩ : syracuseStep 62510231 = 93765347) B93765347
theorem B5141663 : Blo 1522458 5141663 := bstep (se 1 (by rfl) ⟨3856247, by rfl⟩ : syracuseStep 5141663 = 7712495) B7712495
theorem B3429611 : Blo 1522458 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B2569711 : Blo 1522458 2569711 := bstep (se 1 (by rfl) ⟨1927283, by rfl⟩ : syracuseStep 2569711 = 3854567) B3854567
theorem B29283929 : Blo 1522458 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B4339453 : Blo 1522458 4339453 := bstep (se 3 (by rfl) ⟨813647, by rfl⟩ : syracuseStep 4339453 = 1627295) B1627295
theorem B11573117 : Blo 1522458 11573117 := bstep (se 3 (by rfl) ⟨2169959, by rfl⟩ : syracuseStep 11573117 = 4339919) B4339919
theorem B2284271 : Blo 1522458 2284271 := bstep (se 1 (by rfl) ⟨1713203, by rfl⟩ : syracuseStep 2284271 = 3426407) B3426407
theorem B3857159 : Blo 1522458 3857159 := bstep (se 1 (by rfl) ⟨2892869, by rfl⟩ : syracuseStep 3857159 = 5785739) B5785739
theorem B3857179 : Blo 1522458 3857179 := bstep (se 1 (by rfl) ⟨2892884, by rfl⟩ : syracuseStep 3857179 = 5785769) B5785769
theorem B7715897 : Blo 1522458 7715897 := bstep (se 2 (by rfl) ⟨2893461, by rfl⟩ : syracuseStep 7715897 = 5786923) B5786923
theorem B6503591 : Blo 1522458 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B4340911 : Blo 1522458 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B26025299 : Blo 1522458 26025299 := bstep (se 1 (by rfl) ⟨19518974, by rfl⟩ : syracuseStep 26025299 = 39037949) B39037949
theorem B3857939 : Blo 1522458 3857939 := bstep (se 1 (by rfl) ⟨2893454, by rfl⟩ : syracuseStep 3857939 = 5786909) B5786909
theorem B1523227 : Blo 1522458 1523227 := bstep (se 1 (by rfl) ⟨1142420, by rfl⟩ : syracuseStep 1523227 = 2284841) B2284841
theorem B2285159 : Blo 1522458 2285159 := bstep (se 1 (by rfl) ⟨1713869, by rfl⟩ : syracuseStep 2285159 = 3427739) B3427739
theorem B2285375 : Blo 1522458 2285375 := bstep (se 1 (by rfl) ⟨1714031, by rfl⟩ : syracuseStep 2285375 = 3428063) B3428063
theorem B1523559 : Blo 1522458 1523559 := bstep (se 1 (by rfl) ⟨1142669, by rfl⟩ : syracuseStep 1523559 = 2285339) B2285339
theorem B1523695 : Blo 1522458 1523695 := bstep (se 1 (by rfl) ⟨1142771, by rfl⟩ : syracuseStep 1523695 = 2285543) B2285543
theorem B2285663 : Blo 1522458 2285663 := bstep (se 1 (by rfl) ⟨1714247, by rfl⟩ : syracuseStep 2285663 = 3428495) B3428495
theorem B2285807 : Blo 1522458 2285807 := bstep (se 1 (by rfl) ⟨1714355, by rfl⟩ : syracuseStep 2285807 = 3428711) B3428711
theorem B1524039 : Blo 1522458 1524039 := bstep (se 1 (by rfl) ⟨1143029, by rfl⟩ : syracuseStep 1524039 = 2286059) B2286059
theorem B2285927 : Blo 1522458 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B17342909 : Blo 1522458 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B20840915 : Blo 1522458 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B2859707 : Blo 1522458 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B1524415 : Blo 1522458 1524415 := bstep (se 1 (by rfl) ⟨1143311, by rfl⟩ : syracuseStep 1524415 = 2286623) B2286623
theorem B2286311 : Blo 1522458 2286311 := bstep (se 1 (by rfl) ⟨1714733, by rfl⟩ : syracuseStep 2286311 = 3429467) B3429467
theorem B41673487 : Blo 1522458 41673487 := bstep (se 1 (by rfl) ⟨31255115, by rfl⟩ : syracuseStep 41673487 = 62510231) B62510231
theorem B2286407 : Blo 1522458 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B5211049 : Blo 1522458 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B19522619 : Blo 1522458 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B14632123 : Blo 1522458 14632123 := bstep (se 1 (by rfl) ⟨10974092, by rfl⟩ : syracuseStep 14632123 = 21948185) B21948185
theorem B3426281 : Blo 1522458 3426281 := bstep (se 2 (by rfl) ⟨1284855, by rfl⟩ : syracuseStep 3426281 = 2569711) B2569711
theorem B5785937 : Blo 1522458 5785937 := bstep (se 2 (by rfl) ⟨2169726, by rfl⟩ : syracuseStep 5785937 = 4339453) B4339453
theorem B5139179 : Blo 1522458 5139179 := bstep (se 1 (by rfl) ⟨3854384, by rfl⟩ : syracuseStep 5139179 = 7708769) B7708769
theorem B5139449 : Blo 1522458 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B1928443 : Blo 1522458 1928443 := bstep (se 1 (by rfl) ⟨1446332, by rfl⟩ : syracuseStep 1928443 = 2892665) B2892665
theorem B3427775 : Blo 1522458 3427775 := bstep (se 1 (by rfl) ⟨2570831, by rfl⟩ : syracuseStep 3427775 = 5141663) B5141663
theorem B74117339 : Blo 1522458 74117339 := bstep (se 1 (by rfl) ⟨55588004, by rfl⟩ : syracuseStep 74117339 = 111176009) B111176009
theorem B5787881 : Blo 1522458 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B74167163 : Blo 1522458 74167163 := bstep (se 1 (by rfl) ⟨55625372, by rfl⟩ : syracuseStep 74167163 = 111250745) B111250745
theorem B5141501 : Blo 1522458 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B3855863 : Blo 1522458 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B4634185 : Blo 1522458 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B144603157 : Blo 1522458 144603157 := bstep (se 6 (by rfl) ⟨3389136, by rfl⟩ : syracuseStep 144603157 = 6778273) B6778273
theorem B5142905 : Blo 1522458 5142905 := bstep (se 2 (by rfl) ⟨1928589, by rfl⟩ : syracuseStep 5142905 = 3857179) B3857179
theorem B7715411 : Blo 1522458 7715411 := bstep (se 1 (by rfl) ⟨5786558, by rfl⟩ : syracuseStep 7715411 = 11573117) B11573117
theorem B2317007 : Blo 1522458 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B2284319 : Blo 1522458 2284319 := bstep (se 1 (by rfl) ⟨1713239, by rfl⟩ : syracuseStep 2284319 = 3426479) B3426479
theorem B2284511 : Blo 1522458 2284511 := bstep (se 1 (by rfl) ⟨1713383, by rfl⟩ : syracuseStep 2284511 = 3426767) B3426767
theorem B4340729 : Blo 1522458 4340729 := bstep (se 2 (by rfl) ⟨1627773, by rfl⟩ : syracuseStep 4340729 = 3255547) B3255547
theorem B2284655 : Blo 1522458 2284655 := bstep (se 1 (by rfl) ⟨1713491, by rfl⟩ : syracuseStep 2284655 = 3426983) B3426983
theorem B1522847 : Blo 1522458 1522847 := bstep (se 1 (by rfl) ⟨1142135, by rfl⟩ : syracuseStep 1522847 = 2284271) B2284271
theorem B2284703 : Blo 1522458 2284703 := bstep (se 1 (by rfl) ⟨1713527, by rfl⟩ : syracuseStep 2284703 = 3427055) B3427055
theorem B2571439 : Blo 1522458 2571439 := bstep (se 1 (by rfl) ⟨1928579, by rfl⟩ : syracuseStep 2571439 = 3857159) B3857159
theorem B11574575 : Blo 1522458 11574575 := bstep (se 1 (by rfl) ⟨8680931, by rfl⟩ : syracuseStep 11574575 = 17361863) B17361863
theorem B5143931 : Blo 1522458 5143931 := bstep (se 1 (by rfl) ⟨3857948, by rfl⟩ : syracuseStep 5143931 = 7715897) B7715897
theorem B2285087 : Blo 1522458 2285087 := bstep (se 1 (by rfl) ⟨1713815, by rfl⟩ : syracuseStep 2285087 = 3427631) B3427631
theorem B17350199 : Blo 1522458 17350199 := bstep (se 1 (by rfl) ⟨13012649, by rfl⟩ : syracuseStep 17350199 = 26025299) B26025299
theorem B2571959 : Blo 1522458 2571959 := bstep (se 1 (by rfl) ⟨1928969, by rfl⟩ : syracuseStep 2571959 = 3857939) B3857939
theorem B1523439 : Blo 1522458 1523439 := bstep (se 1 (by rfl) ⟨1142579, by rfl⟩ : syracuseStep 1523439 = 2285159) B2285159
theorem B1523583 : Blo 1522458 1523583 := bstep (se 1 (by rfl) ⟨1142687, by rfl⟩ : syracuseStep 1523583 = 2285375) B2285375
theorem B1523775 : Blo 1522458 1523775 := bstep (se 1 (by rfl) ⟨1142831, by rfl⟩ : syracuseStep 1523775 = 2285663) B2285663
theorem B3858587 : Blo 1522458 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B1523871 : Blo 1522458 1523871 := bstep (se 1 (by rfl) ⟨1142903, by rfl⟩ : syracuseStep 1523871 = 2285807) B2285807
theorem B1523951 : Blo 1522458 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B13893943 : Blo 1522458 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B1524207 : Blo 1522458 1524207 := bstep (se 1 (by rfl) ⟨1143155, by rfl⟩ : syracuseStep 1524207 = 2286311) B2286311
theorem B1524271 : Blo 1522458 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B6948065 : Blo 1522458 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B3426119 : Blo 1522458 3426119 := bstep (se 1 (by rfl) ⟨2569589, by rfl⟩ : syracuseStep 3426119 = 5139179) B5139179
theorem B6178685 : Blo 1522458 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B3426299 : Blo 1522458 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B2893819 : Blo 1522458 2893819 := bstep (se 1 (by rfl) ⟨2170364, by rfl⟩ : syracuseStep 2893819 = 4340729) B4340729
theorem B6178913 : Blo 1522458 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B1714639 : Blo 1522458 1714639 := bstep (se 1 (by rfl) ⟨1285979, by rfl⟩ : syracuseStep 1714639 = 2571959) B2571959
theorem B11561939 : Blo 1522458 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B3427667 : Blo 1522458 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B3428585 : Blo 1522458 3428585 := bstep (se 2 (by rfl) ⟨1285719, by rfl⟩ : syracuseStep 3428585 = 2571439) B2571439
theorem B19509497 : Blo 1522458 19509497 := bstep (se 2 (by rfl) ⟨7316061, by rfl⟩ : syracuseStep 19509497 = 14632123) B14632123
theorem B3428603 : Blo 1522458 3428603 := bstep (se 1 (by rfl) ⟨2571452, by rfl⟩ : syracuseStep 3428603 = 5142905) B5142905
theorem B3429287 : Blo 1522458 3429287 := bstep (se 1 (by rfl) ⟨2571965, by rfl⟩ : syracuseStep 3429287 = 5143931) B5143931
theorem B192804209 : Blo 1522458 192804209 := bstep (se 2 (by rfl) ⟨72301578, by rfl⟩ : syracuseStep 192804209 = 144603157) B144603157
theorem B49411559 : Blo 1522458 49411559 := bstep (se 1 (by rfl) ⟨37058669, by rfl⟩ : syracuseStep 49411559 = 74117339) B74117339
theorem B1906471 : Blo 1522458 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B49444775 : Blo 1522458 49444775 := bstep (se 1 (by rfl) ⟨37083581, by rfl⟩ : syracuseStep 49444775 = 74167163) B74167163
theorem B13015079 : Blo 1522458 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B2570575 : Blo 1522458 2570575 := bstep (se 1 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 2570575 = 3855863) B3855863
theorem B55564649 : Blo 1522458 55564649 := bstep (se 2 (by rfl) ⟨20836743, by rfl⟩ : syracuseStep 55564649 = 41673487) B41673487
theorem B2284187 : Blo 1522458 2284187 := bstep (se 1 (by rfl) ⟨1713140, by rfl⟩ : syracuseStep 2284187 = 3426281) B3426281
theorem B3857291 : Blo 1522458 3857291 := bstep (se 1 (by rfl) ⟨2892968, by rfl⟩ : syracuseStep 3857291 = 5785937) B5785937
theorem B2571257 : Blo 1522458 2571257 := bstep (se 2 (by rfl) ⟨964221, by rfl⟩ : syracuseStep 2571257 = 1928443) B1928443
theorem B5143607 : Blo 1522458 5143607 := bstep (se 1 (by rfl) ⟨3857705, by rfl⟩ : syracuseStep 5143607 = 7715411) B7715411
theorem B1522879 : Blo 1522458 1522879 := bstep (se 1 (by rfl) ⟨1142159, by rfl⟩ : syracuseStep 1522879 = 2284319) B2284319
theorem B1523007 : Blo 1522458 1523007 := bstep (se 1 (by rfl) ⟨1142255, by rfl⟩ : syracuseStep 1523007 = 2284511) B2284511
theorem B1523103 : Blo 1522458 1523103 := bstep (se 1 (by rfl) ⟨1142327, by rfl⟩ : syracuseStep 1523103 = 2284655) B2284655
theorem B1523135 : Blo 1522458 1523135 := bstep (se 1 (by rfl) ⟨1142351, by rfl⟩ : syracuseStep 1523135 = 2284703) B2284703
theorem B7716383 : Blo 1522458 7716383 := bstep (se 1 (by rfl) ⟨5787287, by rfl⟩ : syracuseStep 7716383 = 11574575) B11574575
theorem B2285183 : Blo 1522458 2285183 := bstep (se 1 (by rfl) ⟨1713887, by rfl⟩ : syracuseStep 2285183 = 3427775) B3427775
theorem B1523391 : Blo 1522458 1523391 := bstep (se 1 (by rfl) ⟨1142543, by rfl⟩ : syracuseStep 1523391 = 2285087) B2285087
theorem B11566799 : Blo 1522458 11566799 := bstep (se 1 (by rfl) ⟨8675099, by rfl⟩ : syracuseStep 11566799 = 17350199) B17350199
theorem B2572391 : Blo 1522458 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B2285723 : Blo 1522458 2285723 := bstep (se 1 (by rfl) ⟨1714292, by rfl⟩ : syracuseStep 2285723 = 3428585) B3428585
theorem B2285735 : Blo 1522458 2285735 := bstep (se 1 (by rfl) ⟨1714301, by rfl⟩ : syracuseStep 2285735 = 3428603) B3428603
theorem B2286185 : Blo 1522458 2286185 := bstep (se 2 (by rfl) ⟨857319, by rfl⟩ : syracuseStep 2286185 = 1714639) B1714639
theorem B2286191 : Blo 1522458 2286191 := bstep (se 1 (by rfl) ⟨1714643, by rfl⟩ : syracuseStep 2286191 = 3429287) B3429287
theorem B32941039 : Blo 1522458 32941039 := bstep (se 1 (by rfl) ⟨24705779, by rfl⟩ : syracuseStep 32941039 = 49411559) B49411559
theorem B8676719 : Blo 1522458 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B1714171 : Blo 1522458 1714171 := bstep (se 1 (by rfl) ⟨1285628, by rfl⟩ : syracuseStep 1714171 = 2571257) B2571257
theorem B16476493 : Blo 1522458 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B2541961 : Blo 1522458 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B7711199 : Blo 1522458 7711199 := bstep (se 1 (by rfl) ⟨5783399, by rfl⟩ : syracuseStep 7711199 = 11566799) B11566799
theorem B18525257 : Blo 1522458 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B3427433 : Blo 1522458 3427433 := bstep (se 2 (by rfl) ⟨1285287, by rfl⟩ : syracuseStep 3427433 = 2570575) B2570575
theorem B128536139 : Blo 1522458 128536139 := bstep (se 1 (by rfl) ⟨96402104, by rfl⟩ : syracuseStep 128536139 = 192804209) B192804209
theorem B3429071 : Blo 1522458 3429071 := bstep (se 1 (by rfl) ⟨2571803, by rfl⟩ : syracuseStep 3429071 = 5143607) B5143607
theorem B13006331 : Blo 1522458 13006331 := bstep (se 1 (by rfl) ⟨9754748, by rfl⟩ : syracuseStep 13006331 = 19509497) B19509497
theorem B3858425 : Blo 1522458 3858425 := bstep (se 2 (by rfl) ⟨1446909, by rfl⟩ : syracuseStep 3858425 = 2893819) B2893819
theorem B18528173 : Blo 1522458 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B2284079 : Blo 1522458 2284079 := bstep (se 1 (by rfl) ⟨1713059, by rfl⟩ : syracuseStep 2284079 = 3426119) B3426119
theorem B32963183 : Blo 1522458 32963183 := bstep (se 1 (by rfl) ⟨24722387, by rfl⟩ : syracuseStep 32963183 = 49444775) B49444775
theorem B2284199 : Blo 1522458 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B4119275 : Blo 1522458 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B37043099 : Blo 1522458 37043099 := bstep (se 1 (by rfl) ⟨27782324, by rfl⟩ : syracuseStep 37043099 = 55564649) B55564649
theorem B1522791 : Blo 1522458 1522791 := bstep (se 1 (by rfl) ⟨1142093, by rfl⟩ : syracuseStep 1522791 = 2284187) B2284187
theorem B2571527 : Blo 1522458 2571527 := bstep (se 1 (by rfl) ⟨1928645, by rfl⟩ : syracuseStep 2571527 = 3857291) B3857291
theorem B7707959 : Blo 1522458 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B2285111 : Blo 1522458 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B5144255 : Blo 1522458 5144255 := bstep (se 1 (by rfl) ⟨3858191, by rfl⟩ : syracuseStep 5144255 = 7716383) B7716383
theorem B1523455 : Blo 1522458 1523455 := bstep (se 1 (by rfl) ⟨1142591, by rfl⟩ : syracuseStep 1523455 = 2285183) B2285183
theorem B1523815 : Blo 1522458 1523815 := bstep (se 1 (by rfl) ⟨1142861, by rfl⟩ : syracuseStep 1523815 = 2285723) B2285723
theorem B1523823 : Blo 1522458 1523823 := bstep (se 1 (by rfl) ⟨1142867, by rfl⟩ : syracuseStep 1523823 = 2285735) B2285735
theorem B1524123 : Blo 1522458 1524123 := bstep (se 1 (by rfl) ⟨1143092, by rfl⟩ : syracuseStep 1524123 = 2286185) B2286185
theorem B1524127 : Blo 1522458 1524127 := bstep (se 1 (by rfl) ⟨1143095, by rfl⟩ : syracuseStep 1524127 = 2286191) B2286191
theorem B2286047 : Blo 1522458 2286047 := bstep (se 1 (by rfl) ⟨1714535, by rfl⟩ : syracuseStep 2286047 = 3429071) B3429071
theorem B5784479 : Blo 1522458 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B1714351 : Blo 1522458 1714351 := bstep (se 1 (by rfl) ⟨1285763, by rfl⟩ : syracuseStep 1714351 = 2571527) B2571527
theorem B5138639 : Blo 1522458 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B85690759 : Blo 1522458 85690759 := bstep (se 1 (by rfl) ⟨64268069, by rfl⟩ : syracuseStep 85690759 = 128536139) B128536139
theorem B1714927 : Blo 1522458 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B8670887 : Blo 1522458 8670887 := bstep (se 1 (by rfl) ⟨6503165, by rfl⟩ : syracuseStep 8670887 = 13006331) B13006331
theorem B43921385 : Blo 1522458 43921385 := bstep (se 2 (by rfl) ⟨16470519, by rfl⟩ : syracuseStep 43921385 = 32941039) B32941039
theorem B5140799 : Blo 1522458 5140799 := bstep (se 1 (by rfl) ⟨3855599, by rfl⟩ : syracuseStep 5140799 = 7711199) B7711199
theorem B21975455 : Blo 1522458 21975455 := bstep (se 1 (by rfl) ⟨16481591, by rfl⟩ : syracuseStep 21975455 = 32963183) B32963183
theorem B24695399 : Blo 1522458 24695399 := bstep (se 1 (by rfl) ⟨18521549, by rfl⟩ : syracuseStep 24695399 = 37043099) B37043099
theorem B12350171 : Blo 1522458 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B3429503 : Blo 1522458 3429503 := bstep (se 1 (by rfl) ⟨2572127, by rfl⟩ : syracuseStep 3429503 = 5144255) B5144255
theorem B21968657 : Blo 1522458 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B2572283 : Blo 1522458 2572283 := bstep (se 1 (by rfl) ⟨1929212, by rfl⟩ : syracuseStep 2572283 = 3858425) B3858425
theorem B12352115 : Blo 1522458 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B1522719 : Blo 1522458 1522719 := bstep (se 1 (by rfl) ⟨1142039, by rfl⟩ : syracuseStep 1522719 = 2284079) B2284079
theorem B1522799 : Blo 1522458 1522799 := bstep (se 1 (by rfl) ⟨1142099, by rfl⟩ : syracuseStep 1522799 = 2284199) B2284199
theorem B10984733 : Blo 1522458 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B13557125 : Blo 1522458 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B2284955 : Blo 1522458 2284955 := bstep (se 1 (by rfl) ⟨1713716, by rfl⟩ : syracuseStep 2284955 = 3427433) B3427433
theorem B1523407 : Blo 1522458 1523407 := bstep (se 1 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 1523407 = 2285111) B2285111
theorem B2285561 : Blo 1522458 2285561 := bstep (se 2 (by rfl) ⟨857085, by rfl⟩ : syracuseStep 2285561 = 1714171) B1714171
theorem B2285801 : Blo 1522458 2285801 := bstep (se 2 (by rfl) ⟨857175, by rfl⟩ : syracuseStep 2285801 = 1714351) B1714351
theorem B1524031 : Blo 1522458 1524031 := bstep (se 1 (by rfl) ⟨1143023, by rfl⟩ : syracuseStep 1524031 = 2286047) B2286047
theorem B8233447 : Blo 1522458 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B114254345 : Blo 1522458 114254345 := bstep (se 2 (by rfl) ⟨42845379, by rfl⟩ : syracuseStep 114254345 = 85690759) B85690759
theorem B2286335 : Blo 1522458 2286335 := bstep (se 1 (by rfl) ⟨1714751, by rfl⟩ : syracuseStep 2286335 = 3429503) B3429503
theorem B2286569 : Blo 1522458 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B3425759 : Blo 1522458 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B8234743 : Blo 1522458 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B9038083 : Blo 1522458 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B29280923 : Blo 1522458 29280923 := bstep (se 1 (by rfl) ⟨21960692, by rfl⟩ : syracuseStep 29280923 = 43921385) B43921385
theorem B1714855 : Blo 1522458 1714855 := bstep (se 1 (by rfl) ⟨1286141, by rfl⟩ : syracuseStep 1714855 = 2572283) B2572283
theorem B3427199 : Blo 1522458 3427199 := bstep (se 1 (by rfl) ⟨2570399, by rfl⟩ : syracuseStep 3427199 = 5140799) B5140799
theorem B14650303 : Blo 1522458 14650303 := bstep (se 1 (by rfl) ⟨10987727, by rfl⟩ : syracuseStep 14650303 = 21975455) B21975455
theorem B5780591 : Blo 1522458 5780591 := bstep (se 1 (by rfl) ⟨4335443, by rfl⟩ : syracuseStep 5780591 = 8670887) B8670887
theorem B3856319 : Blo 1522458 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B14645771 : Blo 1522458 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B65854397 : Blo 1522458 65854397 := bstep (se 3 (by rfl) ⟨12347699, by rfl⟩ : syracuseStep 65854397 = 24695399) B24695399
theorem B7323155 : Blo 1522458 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B1523303 : Blo 1522458 1523303 := bstep (se 1 (by rfl) ⟨1142477, by rfl⟩ : syracuseStep 1523303 = 2284955) B2284955
theorem B1523707 : Blo 1522458 1523707 := bstep (se 1 (by rfl) ⟨1142780, by rfl⟩ : syracuseStep 1523707 = 2285561) B2285561
theorem B1523867 : Blo 1522458 1523867 := bstep (se 1 (by rfl) ⟨1142900, by rfl⟩ : syracuseStep 1523867 = 2285801) B2285801
theorem B12050777 : Blo 1522458 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B1524223 : Blo 1522458 1524223 := bstep (se 1 (by rfl) ⟨1143167, by rfl⟩ : syracuseStep 1524223 = 2286335) B2286335
theorem B10977929 : Blo 1522458 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B1524379 : Blo 1522458 1524379 := bstep (se 1 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 1524379 = 2286569) B2286569
theorem B2286473 : Blo 1522458 2286473 := bstep (se 2 (by rfl) ⟨857427, by rfl⟩ : syracuseStep 2286473 = 1714855) B1714855
theorem B304678253 : Blo 1522458 304678253 := bstep (se 3 (by rfl) ⟨57127172, by rfl⟩ : syracuseStep 304678253 = 114254345) B114254345
theorem B43902931 : Blo 1522458 43902931 := bstep (se 1 (by rfl) ⟨32927198, by rfl⟩ : syracuseStep 43902931 = 65854397) B65854397
theorem B10979657 : Blo 1522458 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B3853727 : Blo 1522458 3853727 := bstep (se 1 (by rfl) ⟨2890295, by rfl⟩ : syracuseStep 3853727 = 5780591) B5780591
theorem B19533737 : Blo 1522458 19533737 := bstep (se 2 (by rfl) ⟨7325151, by rfl⟩ : syracuseStep 19533737 = 14650303) B14650303
theorem B2283839 : Blo 1522458 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B2570879 : Blo 1522458 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B9763847 : Blo 1522458 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B19520615 : Blo 1522458 19520615 := bstep (se 1 (by rfl) ⟨14640461, by rfl⟩ : syracuseStep 19520615 = 29280923) B29280923
theorem B2284799 : Blo 1522458 2284799 := bstep (se 1 (by rfl) ⟨1713599, by rfl⟩ : syracuseStep 2284799 = 3427199) B3427199
theorem B4882103 : Blo 1522458 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B1524315 : Blo 1522458 1524315 := bstep (se 1 (by rfl) ⟨1143236, by rfl⟩ : syracuseStep 1524315 = 2286473) B2286473
theorem B1713919 : Blo 1522458 1713919 := bstep (se 1 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 1713919 = 2570879) B2570879
theorem B3254735 : Blo 1522458 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B7318619 : Blo 1522458 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B7319771 : Blo 1522458 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B6509231 : Blo 1522458 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B13013743 : Blo 1522458 13013743 := bstep (se 1 (by rfl) ⟨9760307, by rfl⟩ : syracuseStep 13013743 = 19520615) B19520615
theorem B2569151 : Blo 1522458 2569151 := bstep (se 1 (by rfl) ⟨1926863, by rfl⟩ : syracuseStep 2569151 = 3853727) B3853727
theorem B58537241 : Blo 1522458 58537241 := bstep (se 2 (by rfl) ⟨21951465, by rfl⟩ : syracuseStep 58537241 = 43902931) B43902931
theorem B13022491 : Blo 1522458 13022491 := bstep (se 1 (by rfl) ⟨9766868, by rfl⟩ : syracuseStep 13022491 = 19533737) B19533737
theorem B8033851 : Blo 1522458 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B203118835 : Blo 1522458 203118835 := bstep (se 1 (by rfl) ⟨152339126, by rfl⟩ : syracuseStep 203118835 = 304678253) B304678253
theorem B1522559 : Blo 1522458 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B1523199 : Blo 1522458 1523199 := bstep (se 1 (by rfl) ⟨1142399, by rfl⟩ : syracuseStep 1523199 = 2284799) B2284799
theorem B1712767 : Blo 1522458 1712767 := bstep (se 1 (by rfl) ⟨1284575, by rfl⟩ : syracuseStep 1712767 = 2569151) B2569151
theorem B17351657 : Blo 1522458 17351657 := bstep (se 2 (by rfl) ⟨6506871, by rfl⟩ : syracuseStep 17351657 = 13013743) B13013743
theorem B17363321 : Blo 1522458 17363321 := bstep (se 2 (by rfl) ⟨6511245, by rfl⟩ : syracuseStep 17363321 = 13022491) B13022491
theorem B4879079 : Blo 1522458 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B10711801 : Blo 1522458 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B4879847 : Blo 1522458 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B270825113 : Blo 1522458 270825113 := bstep (se 2 (by rfl) ⟨101559417, by rfl⟩ : syracuseStep 270825113 = 203118835) B203118835
theorem B4339487 : Blo 1522458 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B39024827 : Blo 1522458 39024827 := bstep (se 1 (by rfl) ⟨29268620, by rfl⟩ : syracuseStep 39024827 = 58537241) B58537241
theorem B2169823 : Blo 1522458 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B2285225 : Blo 1522458 2285225 := bstep (se 2 (by rfl) ⟨856959, by rfl⟩ : syracuseStep 2285225 = 1713919) B1713919
theorem B11575547 : Blo 1522458 11575547 := bstep (se 1 (by rfl) ⟨8681660, by rfl⟩ : syracuseStep 11575547 = 17363321) B17363321
theorem B3252719 : Blo 1522458 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B11567771 : Blo 1522458 11567771 := bstep (se 1 (by rfl) ⟨8675828, by rfl⟩ : syracuseStep 11567771 = 17351657) B17351657
theorem B3253231 : Blo 1522458 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B2892991 : Blo 1522458 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B2893097 : Blo 1522458 2893097 := bstep (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) B2169823
theorem B14282401 : Blo 1522458 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B2283689 : Blo 1522458 2283689 := bstep (se 2 (by rfl) ⟨856383, by rfl⟩ : syracuseStep 2283689 = 1712767) B1712767
theorem B180550075 : Blo 1522458 180550075 := bstep (se 1 (by rfl) ⟨135412556, by rfl⟩ : syracuseStep 180550075 = 270825113) B270825113
theorem B26016551 : Blo 1522458 26016551 := bstep (se 1 (by rfl) ⟨19512413, by rfl⟩ : syracuseStep 26016551 = 39024827) B39024827
theorem B1523483 : Blo 1522458 1523483 := bstep (se 1 (by rfl) ⟨1142612, by rfl⟩ : syracuseStep 1523483 = 2285225) B2285225
theorem B7717031 : Blo 1522458 7717031 := bstep (se 1 (by rfl) ⟨5787773, by rfl⟩ : syracuseStep 7717031 = 11575547) B11575547
theorem B17344367 : Blo 1522458 17344367 := bstep (se 1 (by rfl) ⟨13008275, by rfl⟩ : syracuseStep 17344367 = 26016551) B26016551
theorem B7711847 : Blo 1522458 7711847 := bstep (se 1 (by rfl) ⟨5783885, by rfl⟩ : syracuseStep 7711847 = 11567771) B11567771
theorem B240733433 : Blo 1522458 240733433 := bstep (se 2 (by rfl) ⟨90275037, by rfl⟩ : syracuseStep 240733433 = 180550075) B180550075
theorem B4337641 : Blo 1522458 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B19043201 : Blo 1522458 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B2168479 : Blo 1522458 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B7714925 : Blo 1522458 7714925 := bstep (se 3 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 7714925 = 2893097) B2893097
theorem B1522459 : Blo 1522458 1522459 := bstep (se 1 (by rfl) ⟨1141844, by rfl⟩ : syracuseStep 1522459 = 2283689) B2283689
theorem B3857321 : Blo 1522458 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B5144687 : Blo 1522458 5144687 := bstep (se 1 (by rfl) ⟨3858515, by rfl⟩ : syracuseStep 5144687 = 7717031) B7717031
theorem B11562911 : Blo 1522458 11562911 := bstep (se 1 (by rfl) ⟨8672183, by rfl⟩ : syracuseStep 11562911 = 17344367) B17344367
theorem B5141231 : Blo 1522458 5141231 := bstep (se 1 (by rfl) ⟨3855923, by rfl⟩ : syracuseStep 5141231 = 7711847) B7711847
theorem B12695467 : Blo 1522458 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B5143283 : Blo 1522458 5143283 := bstep (se 1 (by rfl) ⟨3857462, by rfl⟩ : syracuseStep 5143283 = 7714925) B7714925
theorem B2571547 : Blo 1522458 2571547 := bstep (se 1 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 2571547 = 3857321) B3857321
theorem B160488955 : Blo 1522458 160488955 := bstep (se 1 (by rfl) ⟨120366716, by rfl⟩ : syracuseStep 160488955 = 240733433) B240733433
theorem B2891305 : Blo 1522458 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B5783521 : Blo 1522458 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B213985273 : Blo 1522458 213985273 := bstep (se 2 (by rfl) ⟨80244477, by rfl⟩ : syracuseStep 213985273 = 160488955) B160488955
theorem B16927289 : Blo 1522458 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B7711361 : Blo 1522458 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B3427487 : Blo 1522458 3427487 := bstep (se 1 (by rfl) ⟨2570615, by rfl⟩ : syracuseStep 3427487 = 5141231) B5141231
theorem B3428729 : Blo 1522458 3428729 := bstep (se 2 (by rfl) ⟨1285773, by rfl⟩ : syracuseStep 3428729 = 2571547) B2571547
theorem B3428855 : Blo 1522458 3428855 := bstep (se 1 (by rfl) ⟨2571641, by rfl⟩ : syracuseStep 3428855 = 5143283) B5143283
theorem B3855073 : Blo 1522458 3855073 := bstep (se 2 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 3855073 = 2891305) B2891305
theorem B3429791 : Blo 1522458 3429791 := bstep (se 1 (by rfl) ⟨2572343, by rfl⟩ : syracuseStep 3429791 = 5144687) B5144687
theorem B7708607 : Blo 1522458 7708607 := bstep (se 1 (by rfl) ⟨5781455, by rfl⟩ : syracuseStep 7708607 = 11562911) B11562911
theorem B2285819 : Blo 1522458 2285819 := bstep (se 1 (by rfl) ⟨1714364, by rfl⟩ : syracuseStep 2285819 = 3428729) B3428729
theorem B2285903 : Blo 1522458 2285903 := bstep (se 1 (by rfl) ⟨1714427, by rfl⟩ : syracuseStep 2285903 = 3428855) B3428855
theorem B2286527 : Blo 1522458 2286527 := bstep (se 1 (by rfl) ⟨1714895, by rfl⟩ : syracuseStep 2286527 = 3429791) B3429791
theorem B5139071 : Blo 1522458 5139071 := bstep (se 1 (by rfl) ⟨3854303, by rfl⟩ : syracuseStep 5139071 = 7708607) B7708607
theorem B285313697 : Blo 1522458 285313697 := bstep (se 2 (by rfl) ⟨106992636, by rfl⟩ : syracuseStep 285313697 = 213985273) B213985273
theorem B5140097 : Blo 1522458 5140097 := bstep (se 2 (by rfl) ⟨1927536, by rfl⟩ : syracuseStep 5140097 = 3855073) B3855073
theorem B11284859 : Blo 1522458 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B5140907 : Blo 1522458 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B2284991 : Blo 1522458 2284991 := bstep (se 1 (by rfl) ⟨1713743, by rfl⟩ : syracuseStep 2284991 = 3427487) B3427487
theorem B1523879 : Blo 1522458 1523879 := bstep (se 1 (by rfl) ⟨1142909, by rfl⟩ : syracuseStep 1523879 = 2285819) B2285819
theorem B1523935 : Blo 1522458 1523935 := bstep (se 1 (by rfl) ⟨1142951, by rfl⟩ : syracuseStep 1523935 = 2285903) B2285903
theorem B1524351 : Blo 1522458 1524351 := bstep (se 1 (by rfl) ⟨1143263, by rfl⟩ : syracuseStep 1524351 = 2286527) B2286527
theorem B3426047 : Blo 1522458 3426047 := bstep (se 1 (by rfl) ⟨2569535, by rfl⟩ : syracuseStep 3426047 = 5139071) B5139071
theorem B3426731 : Blo 1522458 3426731 := bstep (se 1 (by rfl) ⟨2570048, by rfl⟩ : syracuseStep 3426731 = 5140097) B5140097
theorem B7523239 : Blo 1522458 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B3427271 : Blo 1522458 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B190209131 : Blo 1522458 190209131 := bstep (se 1 (by rfl) ⟨142656848, by rfl⟩ : syracuseStep 190209131 = 285313697) B285313697
theorem B1523327 : Blo 1522458 1523327 := bstep (se 1 (by rfl) ⟨1142495, by rfl⟩ : syracuseStep 1523327 = 2284991) B2284991
theorem B126806087 : Blo 1522458 126806087 := bstep (se 1 (by rfl) ⟨95104565, by rfl⟩ : syracuseStep 126806087 = 190209131) B190209131
theorem B10030985 : Blo 1522458 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B2284031 : Blo 1522458 2284031 := bstep (se 1 (by rfl) ⟨1713023, by rfl⟩ : syracuseStep 2284031 = 3426047) B3426047
theorem B2284487 : Blo 1522458 2284487 := bstep (se 1 (by rfl) ⟨1713365, by rfl⟩ : syracuseStep 2284487 = 3426731) B3426731
theorem B2284847 : Blo 1522458 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B338149565 : Blo 1522458 338149565 := bstep (se 3 (by rfl) ⟨63403043, by rfl⟩ : syracuseStep 338149565 = 126806087) B126806087
theorem B6687323 : Blo 1522458 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B1522687 : Blo 1522458 1522687 := bstep (se 1 (by rfl) ⟨1142015, by rfl⟩ : syracuseStep 1522687 = 2284031) B2284031
theorem B1522991 : Blo 1522458 1522991 := bstep (se 1 (by rfl) ⟨1142243, by rfl⟩ : syracuseStep 1522991 = 2284487) B2284487
theorem B1523231 : Blo 1522458 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B4458215 : Blo 1522458 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B225433043 : Blo 1522458 225433043 := bstep (se 1 (by rfl) ⟨169074782, by rfl⟩ : syracuseStep 225433043 = 338149565) B338149565
theorem B150288695 : Blo 1522458 150288695 := bstep (se 1 (by rfl) ⟨112716521, by rfl⟩ : syracuseStep 150288695 = 225433043) B225433043
theorem B2972143 : Blo 1522458 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B100192463 : Blo 1522458 100192463 := bstep (se 1 (by rfl) ⟨75144347, by rfl⟩ : syracuseStep 100192463 = 150288695) B150288695
theorem B3962857 : Blo 1522458 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B66794975 : Blo 1522458 66794975 := bstep (se 1 (by rfl) ⟨50096231, by rfl⟩ : syracuseStep 66794975 = 100192463) B100192463
theorem B5283809 : Blo 1522458 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B44529983 : Blo 1522458 44529983 := bstep (se 1 (by rfl) ⟨33397487, by rfl⟩ : syracuseStep 44529983 = 66794975) B66794975
theorem B3522539 : Blo 1522458 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B2348359 : Blo 1522458 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B29686655 : Blo 1522458 29686655 := bstep (se 1 (by rfl) ⟨22264991, by rfl⟩ : syracuseStep 29686655 = 44529983) B44529983
theorem B12524581 : Blo 1522458 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B19791103 : Blo 1522458 19791103 := bstep (se 1 (by rfl) ⟨14843327, by rfl⟩ : syracuseStep 19791103 = 29686655) B29686655
theorem B26388137 : Blo 1522458 26388137 := bstep (se 2 (by rfl) ⟨9895551, by rfl⟩ : syracuseStep 26388137 = 19791103) B19791103
theorem B16699441 : Blo 1522458 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B22265921 : Blo 1522458 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B70368365 : Blo 1522458 70368365 := bstep (se 3 (by rfl) ⟨13194068, by rfl⟩ : syracuseStep 70368365 = 26388137) B26388137
theorem B14843947 : Blo 1522458 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B46912243 : Blo 1522458 46912243 := bstep (se 1 (by rfl) ⟨35184182, by rfl⟩ : syracuseStep 46912243 = 70368365) B70368365
theorem B19791929 : Blo 1522458 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B62549657 : Blo 1522458 62549657 := bstep (se 2 (by rfl) ⟨23456121, by rfl⟩ : syracuseStep 62549657 = 46912243) B46912243
theorem B41699771 : Blo 1522458 41699771 := bstep (se 1 (by rfl) ⟨31274828, by rfl⟩ : syracuseStep 41699771 = 62549657) B62549657
theorem B13194619 : Blo 1522458 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B70371301 : Blo 1522458 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B27799847 : Blo 1522458 27799847 := bstep (se 1 (by rfl) ⟨20849885, by rfl⟩ : syracuseStep 27799847 = 41699771) B41699771
theorem B18533231 : Blo 1522458 18533231 := bstep (se 1 (by rfl) ⟨13899923, by rfl⟩ : syracuseStep 18533231 = 27799847) B27799847
theorem B93828401 : Blo 1522458 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B12355487 : Blo 1522458 12355487 := bstep (se 1 (by rfl) ⟨9266615, by rfl⟩ : syracuseStep 12355487 = 18533231) B18533231
theorem B62552267 : Blo 1522458 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B8236991 : Blo 1522458 8236991 := bstep (se 1 (by rfl) ⟨6177743, by rfl⟩ : syracuseStep 8236991 = 12355487) B12355487
theorem B41701511 : Blo 1522458 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B5491327 : Blo 1522458 5491327 := bstep (se 1 (by rfl) ⟨4118495, by rfl⟩ : syracuseStep 5491327 = 8236991) B8236991
theorem B111204029 : Blo 1522458 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B296544077 : Blo 1522458 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B7321769 : Blo 1522458 7321769 := bstep (se 2 (by rfl) ⟨2745663, by rfl⟩ : syracuseStep 7321769 = 5491327) B5491327
theorem B197696051 : Blo 1522458 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B4881179 : Blo 1522458 4881179 := bstep (se 1 (by rfl) ⟨3660884, by rfl⟩ : syracuseStep 4881179 = 7321769) B7321769
theorem B131797367 : Blo 1522458 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B13016477 : Blo 1522458 13016477 := bstep (se 3 (by rfl) ⟨2440589, by rfl⟩ : syracuseStep 13016477 = 4881179) B4881179
theorem B8677651 : Blo 1522458 8677651 := bstep (se 1 (by rfl) ⟨6508238, by rfl⟩ : syracuseStep 8677651 = 13016477) B13016477
theorem B87864911 : Blo 1522458 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B11570201 : Blo 1522458 11570201 := bstep (se 2 (by rfl) ⟨4338825, by rfl⟩ : syracuseStep 11570201 = 8677651) B8677651
theorem B58576607 : Blo 1522458 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B7713467 : Blo 1522458 7713467 := bstep (se 1 (by rfl) ⟨5785100, by rfl⟩ : syracuseStep 7713467 = 11570201) B11570201
theorem B39051071 : Blo 1522458 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B5142311 : Blo 1522458 5142311 := bstep (se 1 (by rfl) ⟨3856733, by rfl⟩ : syracuseStep 5142311 = 7713467) B7713467
theorem B26034047 : Blo 1522458 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B3428207 : Blo 1522458 3428207 := bstep (se 1 (by rfl) ⟨2571155, by rfl⟩ : syracuseStep 3428207 = 5142311) B5142311
theorem B17356031 : Blo 1522458 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B11570687 : Blo 1522458 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B2285471 : Blo 1522458 2285471 := bstep (se 1 (by rfl) ⟨1714103, by rfl⟩ : syracuseStep 2285471 = 3428207) B3428207
theorem B7713791 : Blo 1522458 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B1523647 : Blo 1522458 1523647 := bstep (se 1 (by rfl) ⟨1142735, by rfl⟩ : syracuseStep 1523647 = 2285471) B2285471
theorem B5142527 : Blo 1522458 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B3428351 : Blo 1522458 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B2285567 : Blo 1522458 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B1523711 : Blo 1522458 1523711 := bstep (se 1 (by rfl) ⟨1142783, by rfl⟩ : syracuseStep 1523711 = 2285567) B2285567

theorem C0 (j : ℕ) (h1 : 380614 ≤ j) (h2 : j ≤ 381113) : Blo 1522458 (4 * j + 3) := by
  interval_cases j
  · exact B1522459
  · exact B1522463
  · exact B1522467
  · exact B1522471
  · exact B1522475
  · exact B1522479
  · exact B1522483
  · exact B1522487
  · exact B1522491
  · exact B1522495
  · exact B1522499
  · exact B1522503
  · exact B1522507
  · exact B1522511
  · exact B1522515
  · exact B1522519
  · exact B1522523
  · exact B1522527
  · exact B1522531
  · exact B1522535
  · exact B1522539
  · exact B1522543
  · exact B1522547
  · exact B1522551
  · exact B1522555
  · exact B1522559
  · exact B1522563
  · exact B1522567
  · exact B1522571
  · exact B1522575
  · exact B1522579
  · exact B1522583
  · exact B1522587
  · exact B1522591
  · exact B1522595
  · exact B1522599
  · exact B1522603
  · exact B1522607
  · exact B1522611
  · exact B1522615
  · exact B1522619
  · exact B1522623
  · exact B1522627
  · exact B1522631
  · exact B1522635
  · exact B1522639
  · exact B1522643
  · exact B1522647
  · exact B1522651
  · exact B1522655
  · exact B1522659
  · exact B1522663
  · exact B1522667
  · exact B1522671
  · exact B1522675
  · exact B1522679
  · exact B1522683
  · exact B1522687
  · exact B1522691
  · exact B1522695
  · exact B1522699
  · exact B1522703
  · exact B1522707
  · exact B1522711
  · exact B1522715
  · exact B1522719
  · exact B1522723
  · exact B1522727
  · exact B1522731
  · exact B1522735
  · exact B1522739
  · exact B1522743
  · exact B1522747
  · exact B1522751
  · exact B1522755
  · exact B1522759
  · exact B1522763
  · exact B1522767
  · exact B1522771
  · exact B1522775
  · exact B1522779
  · exact B1522783
  · exact B1522787
  · exact B1522791
  · exact B1522795
  · exact B1522799
  · exact B1522803
  · exact B1522807
  · exact B1522811
  · exact B1522815
  · exact B1522819
  · exact B1522823
  · exact B1522827
  · exact B1522831
  · exact B1522835
  · exact B1522839
  · exact B1522843
  · exact B1522847
  · exact B1522851
  · exact B1522855
  · exact B1522859
  · exact B1522863
  · exact B1522867
  · exact B1522871
  · exact B1522875
  · exact B1522879
  · exact B1522883
  · exact B1522887
  · exact B1522891
  · exact B1522895
  · exact B1522899
  · exact B1522903
  · exact B1522907
  · exact B1522911
  · exact B1522915
  · exact B1522919
  · exact B1522923
  · exact B1522927
  · exact B1522931
  · exact B1522935
  · exact B1522939
  · exact B1522943
  · exact B1522947
  · exact B1522951
  · exact B1522955
  · exact B1522959
  · exact B1522963
  · exact B1522967
  · exact B1522971
  · exact B1522975
  · exact B1522979
  · exact B1522983
  · exact B1522987
  · exact B1522991
  · exact B1522995
  · exact B1522999
  · exact B1523003
  · exact B1523007
  · exact B1523011
  · exact B1523015
  · exact B1523019
  · exact B1523023
  · exact B1523027
  · exact B1523031
  · exact B1523035
  · exact B1523039
  · exact B1523043
  · exact B1523047
  · exact B1523051
  · exact B1523055
  · exact B1523059
  · exact B1523063
  · exact B1523067
  · exact B1523071
  · exact B1523075
  · exact B1523079
  · exact B1523083
  · exact B1523087
  · exact B1523091
  · exact B1523095
  · exact B1523099
  · exact B1523103
  · exact B1523107
  · exact B1523111
  · exact B1523115
  · exact B1523119
  · exact B1523123
  · exact B1523127
  · exact B1523131
  · exact B1523135
  · exact B1523139
  · exact B1523143
  · exact B1523147
  · exact B1523151
  · exact B1523155
  · exact B1523159
  · exact B1523163
  · exact B1523167
  · exact B1523171
  · exact B1523175
  · exact B1523179
  · exact B1523183
  · exact B1523187
  · exact B1523191
  · exact B1523195
  · exact B1523199
  · exact B1523203
  · exact B1523207
  · exact B1523211
  · exact B1523215
  · exact B1523219
  · exact B1523223
  · exact B1523227
  · exact B1523231
  · exact B1523235
  · exact B1523239
  · exact B1523243
  · exact B1523247
  · exact B1523251
  · exact B1523255
  · exact B1523259
  · exact B1523263
  · exact B1523267
  · exact B1523271
  · exact B1523275
  · exact B1523279
  · exact B1523283
  · exact B1523287
  · exact B1523291
  · exact B1523295
  · exact B1523299
  · exact B1523303
  · exact B1523307
  · exact B1523311
  · exact B1523315
  · exact B1523319
  · exact B1523323
  · exact B1523327
  · exact B1523331
  · exact B1523335
  · exact B1523339
  · exact B1523343
  · exact B1523347
  · exact B1523351
  · exact B1523355
  · exact B1523359
  · exact B1523363
  · exact B1523367
  · exact B1523371
  · exact B1523375
  · exact B1523379
  · exact B1523383
  · exact B1523387
  · exact B1523391
  · exact B1523395
  · exact B1523399
  · exact B1523403
  · exact B1523407
  · exact B1523411
  · exact B1523415
  · exact B1523419
  · exact B1523423
  · exact B1523427
  · exact B1523431
  · exact B1523435
  · exact B1523439
  · exact B1523443
  · exact B1523447
  · exact B1523451
  · exact B1523455
  · exact B1523459
  · exact B1523463
  · exact B1523467
  · exact B1523471
  · exact B1523475
  · exact B1523479
  · exact B1523483
  · exact B1523487
  · exact B1523491
  · exact B1523495
  · exact B1523499
  · exact B1523503
  · exact B1523507
  · exact B1523511
  · exact B1523515
  · exact B1523519
  · exact B1523523
  · exact B1523527
  · exact B1523531
  · exact B1523535
  · exact B1523539
  · exact B1523543
  · exact B1523547
  · exact B1523551
  · exact B1523555
  · exact B1523559
  · exact B1523563
  · exact B1523567
  · exact B1523571
  · exact B1523575
  · exact B1523579
  · exact B1523583
  · exact B1523587
  · exact B1523591
  · exact B1523595
  · exact B1523599
  · exact B1523603
  · exact B1523607
  · exact B1523611
  · exact B1523615
  · exact B1523619
  · exact B1523623
  · exact B1523627
  · exact B1523631
  · exact B1523635
  · exact B1523639
  · exact B1523643
  · exact B1523647
  · exact B1523651
  · exact B1523655
  · exact B1523659
  · exact B1523663
  · exact B1523667
  · exact B1523671
  · exact B1523675
  · exact B1523679
  · exact B1523683
  · exact B1523687
  · exact B1523691
  · exact B1523695
  · exact B1523699
  · exact B1523703
  · exact B1523707
  · exact B1523711
  · exact B1523715
  · exact B1523719
  · exact B1523723
  · exact B1523727
  · exact B1523731
  · exact B1523735
  · exact B1523739
  · exact B1523743
  · exact B1523747
  · exact B1523751
  · exact B1523755
  · exact B1523759
  · exact B1523763
  · exact B1523767
  · exact B1523771
  · exact B1523775
  · exact B1523779
  · exact B1523783
  · exact B1523787
  · exact B1523791
  · exact B1523795
  · exact B1523799
  · exact B1523803
  · exact B1523807
  · exact B1523811
  · exact B1523815
  · exact B1523819
  · exact B1523823
  · exact B1523827
  · exact B1523831
  · exact B1523835
  · exact B1523839
  · exact B1523843
  · exact B1523847
  · exact B1523851
  · exact B1523855
  · exact B1523859
  · exact B1523863
  · exact B1523867
  · exact B1523871
  · exact B1523875
  · exact B1523879
  · exact B1523883
  · exact B1523887
  · exact B1523891
  · exact B1523895
  · exact B1523899
  · exact B1523903
  · exact B1523907
  · exact B1523911
  · exact B1523915
  · exact B1523919
  · exact B1523923
  · exact B1523927
  · exact B1523931
  · exact B1523935
  · exact B1523939
  · exact B1523943
  · exact B1523947
  · exact B1523951
  · exact B1523955
  · exact B1523959
  · exact B1523963
  · exact B1523967
  · exact B1523971
  · exact B1523975
  · exact B1523979
  · exact B1523983
  · exact B1523987
  · exact B1523991
  · exact B1523995
  · exact B1523999
  · exact B1524003
  · exact B1524007
  · exact B1524011
  · exact B1524015
  · exact B1524019
  · exact B1524023
  · exact B1524027
  · exact B1524031
  · exact B1524035
  · exact B1524039
  · exact B1524043
  · exact B1524047
  · exact B1524051
  · exact B1524055
  · exact B1524059
  · exact B1524063
  · exact B1524067
  · exact B1524071
  · exact B1524075
  · exact B1524079
  · exact B1524083
  · exact B1524087
  · exact B1524091
  · exact B1524095
  · exact B1524099
  · exact B1524103
  · exact B1524107
  · exact B1524111
  · exact B1524115
  · exact B1524119
  · exact B1524123
  · exact B1524127
  · exact B1524131
  · exact B1524135
  · exact B1524139
  · exact B1524143
  · exact B1524147
  · exact B1524151
  · exact B1524155
  · exact B1524159
  · exact B1524163
  · exact B1524167
  · exact B1524171
  · exact B1524175
  · exact B1524179
  · exact B1524183
  · exact B1524187
  · exact B1524191
  · exact B1524195
  · exact B1524199
  · exact B1524203
  · exact B1524207
  · exact B1524211
  · exact B1524215
  · exact B1524219
  · exact B1524223
  · exact B1524227
  · exact B1524231
  · exact B1524235
  · exact B1524239
  · exact B1524243
  · exact B1524247
  · exact B1524251
  · exact B1524255
  · exact B1524259
  · exact B1524263
  · exact B1524267
  · exact B1524271
  · exact B1524275
  · exact B1524279
  · exact B1524283
  · exact B1524287
  · exact B1524291
  · exact B1524295
  · exact B1524299
  · exact B1524303
  · exact B1524307
  · exact B1524311
  · exact B1524315
  · exact B1524319
  · exact B1524323
  · exact B1524327
  · exact B1524331
  · exact B1524335
  · exact B1524339
  · exact B1524343
  · exact B1524347
  · exact B1524351
  · exact B1524355
  · exact B1524359
  · exact B1524363
  · exact B1524367
  · exact B1524371
  · exact B1524375
  · exact B1524379
  · exact B1524383
  · exact B1524387
  · exact B1524391
  · exact B1524395
  · exact B1524399
  · exact B1524403
  · exact B1524407
  · exact B1524411
  · exact B1524415
  · exact B1524419
  · exact B1524423
  · exact B1524427
  · exact B1524431
  · exact B1524435
  · exact B1524439
  · exact B1524443
  · exact B1524447
  · exact B1524451
  · exact B1524455

theorem solution (m : ℕ) (hlo : 1522458 ≤ m) (hhi : m ≤ 1524458) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 380614 ≤ j := by omega
    have hj2 : j ≤ 381113 := by omega
    have hb : Blo 1522458 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
