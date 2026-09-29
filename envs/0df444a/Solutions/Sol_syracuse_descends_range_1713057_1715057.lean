-- Prove2me | solution 1 for syracuse_descends_range_1713057_1715057
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:28:12.995317+00:00
-- url     : https://prove2.me/submissions/607f703f-4e07-4fbc-a688-c26eedae11f2

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


theorem B2572301 : Blo 1713057 2572301 := bbase (se 3 (by rfl) ⟨482306, by rfl⟩ : syracuseStep 2572301 = 964613) (by norm_num)
theorem B16482325 : Blo 1713057 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B3858461 : Blo 1713057 3858461 := bbase (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) (by norm_num)
theorem B5865509 : Blo 1713057 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B2572325 : Blo 1713057 2572325 := bbase (se 4 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 2572325 = 482311) (by norm_num)
theorem B2891821 : Blo 1713057 2891821 := bbase (se 3 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 2891821 = 1084433) (by norm_num)
theorem B2572349 : Blo 1713057 2572349 := bbase (se 3 (by rfl) ⟨482315, by rfl⟩ : syracuseStep 2572349 = 964631) (by norm_num)
theorem B2744389 : Blo 1713057 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B1736785 : Blo 1713057 1736785 := bbase (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) (by norm_num)
theorem B6504533 : Blo 1713057 6504533 := bbase (se 8 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 6504533 = 76225) (by norm_num)
theorem B2572373 : Blo 1713057 2572373 := bbase (se 8 (by rfl) ⟨15072, by rfl⟩ : syracuseStep 2572373 = 30145) (by norm_num)
theorem B3858533 : Blo 1713057 3858533 := bbase (se 4 (by rfl) ⟨361737, by rfl⟩ : syracuseStep 3858533 = 723475) (by norm_num)
theorem B2572397 : Blo 1713057 2572397 := bbase (se 3 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 2572397 = 964649) (by norm_num)
theorem B5783669 : Blo 1713057 5783669 := bbase (se 5 (by rfl) ⟨271109, by rfl⟩ : syracuseStep 5783669 = 542219) (by norm_num)
theorem B2891909 : Blo 1713057 2891909 := bbase (se 4 (by rfl) ⟨271116, by rfl⟩ : syracuseStep 2891909 = 542233) (by norm_num)
theorem B2572421 : Blo 1713057 2572421 := bbase (se 4 (by rfl) ⟨241164, by rfl⟩ : syracuseStep 2572421 = 482329) (by norm_num)
theorem B2474125 : Blo 1713057 2474125 := bbase (se 3 (by rfl) ⟨463898, by rfl⟩ : syracuseStep 2474125 = 927797) (by norm_num)
theorem B2572445 : Blo 1713057 2572445 := bbase (se 3 (by rfl) ⟨482333, by rfl⟩ : syracuseStep 2572445 = 964667) (by norm_num)
theorem B3858605 : Blo 1713057 3858605 := bbase (se 3 (by rfl) ⟨723488, by rfl⟩ : syracuseStep 3858605 = 1446977) (by norm_num)
theorem B2572469 : Blo 1713057 2572469 := bbase (se 5 (by rfl) ⟨120584, by rfl⟩ : syracuseStep 2572469 = 241169) (by norm_num)
theorem B2572493 : Blo 1713057 2572493 := bbase (se 3 (by rfl) ⟨482342, by rfl⟩ : syracuseStep 2572493 = 964685) (by norm_num)
theorem B6947045 : Blo 1713057 6947045 := bbase (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) (by norm_num)
theorem B2572517 : Blo 1713057 2572517 := bbase (se 4 (by rfl) ⟨241173, by rfl⟩ : syracuseStep 2572517 = 482347) (by norm_num)
theorem B3858677 : Blo 1713057 3858677 := bbase (se 5 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 3858677 = 361751) (by norm_num)
theorem B2572541 : Blo 1713057 2572541 := bbase (se 3 (by rfl) ⟨482351, by rfl⟩ : syracuseStep 2572541 = 964703) (by norm_num)
theorem B2892037 : Blo 1713057 2892037 := bbase (se 4 (by rfl) ⟨271128, by rfl⟩ : syracuseStep 2892037 = 542257) (by norm_num)
theorem B6521093 : Blo 1713057 6521093 := bbase (se 4 (by rfl) ⟨611352, by rfl⟩ : syracuseStep 6521093 = 1222705) (by norm_num)
theorem B2572565 : Blo 1713057 2572565 := bbase (se 6 (by rfl) ⟨60294, by rfl⟩ : syracuseStep 2572565 = 120589) (by norm_num)
theorem B2007349 : Blo 1713057 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B3858749 : Blo 1713057 3858749 := bbase (se 3 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 3858749 = 1447031) (by norm_num)
theorem B2892125 : Blo 1713057 2892125 := bbase (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) (by norm_num)
theorem B2605421 : Blo 1713057 2605421 := bbase (se 3 (by rfl) ⟨488516, by rfl⟩ : syracuseStep 2605421 = 977033) (by norm_num)
theorem B3858821 : Blo 1713057 3858821 := bbase (se 4 (by rfl) ⟨361764, by rfl⟩ : syracuseStep 3858821 = 723529) (by norm_num)
theorem B3088829 : Blo 1713057 3088829 := bbase (se 3 (by rfl) ⟨579155, by rfl⟩ : syracuseStep 3088829 = 1158311) (by norm_num)
theorem B2892253 : Blo 1713057 2892253 := bbase (se 3 (by rfl) ⟨542297, by rfl⟩ : syracuseStep 2892253 = 1084595) (by norm_num)
theorem B3523061 : Blo 1713057 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B4882933 : Blo 1713057 4882933 := bbase (se 5 (by rfl) ⟨228887, by rfl⟩ : syracuseStep 4882933 = 457775) (by norm_num)
theorem B6595093 : Blo 1713057 6595093 := bbase (se 6 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 6595093 = 309145) (by norm_num)
theorem B5784101 : Blo 1713057 5784101 := bbase (se 4 (by rfl) ⟨542259, by rfl⟩ : syracuseStep 5784101 = 1084519) (by norm_num)
theorem B2892341 : Blo 1713057 2892341 := bbase (se 5 (by rfl) ⟨135578, by rfl⟩ : syracuseStep 2892341 = 271157) (by norm_num)
theorem B8675909 : Blo 1713057 8675909 := bbase (se 4 (by rfl) ⟨813366, by rfl⟩ : syracuseStep 8675909 = 1626733) (by norm_num)
theorem B21955157 : Blo 1713057 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B2744933 : Blo 1713057 2744933 := bbase (se 4 (by rfl) ⟨257337, by rfl⟩ : syracuseStep 2744933 = 514675) (by norm_num)
theorem B17588885 : Blo 1713057 17588885 := bbase (se 6 (by rfl) ⟨412239, by rfl⟩ : syracuseStep 17588885 = 824479) (by norm_num)
theorem B2892469 : Blo 1713057 2892469 := bbase (se 5 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 2892469 = 271169) (by norm_num)
theorem B2441917 : Blo 1713057 2441917 := bbase (se 3 (by rfl) ⟨457859, by rfl⟩ : syracuseStep 2441917 = 915719) (by norm_num)
theorem B3089117 : Blo 1713057 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B3252973 : Blo 1713057 3252973 := bbase (se 3 (by rfl) ⟨609932, by rfl⟩ : syracuseStep 3252973 = 1219865) (by norm_num)
theorem B6177541 : Blo 1713057 6177541 := bbase (se 4 (by rfl) ⟨579144, by rfl⟩ : syracuseStep 6177541 = 1158289) (by norm_num)
theorem B2892557 : Blo 1713057 2892557 := bbase (se 3 (by rfl) ⟨542354, by rfl⟩ : syracuseStep 2892557 = 1084709) (by norm_num)
theorem B6259477 : Blo 1713057 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B3089189 : Blo 1713057 3089189 := bbase (se 4 (by rfl) ⟨289611, by rfl⟩ : syracuseStep 3089189 = 579223) (by norm_num)
theorem B10986293 : Blo 1713057 10986293 := bbase (se 5 (by rfl) ⟨514982, by rfl⟩ : syracuseStep 10986293 = 1029965) (by norm_num)
theorem B7324469 : Blo 1713057 7324469 := bbase (se 5 (by rfl) ⟨343334, by rfl⟩ : syracuseStep 7324469 = 686669) (by norm_num)
theorem B4399933 : Blo 1713057 4399933 := bbase (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) (by norm_num)
theorem B3253117 : Blo 1713057 3253117 := bbase (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) (by norm_num)
theorem B2892685 : Blo 1713057 2892685 := bbase (se 3 (by rfl) ⟨542378, by rfl⟩ : syracuseStep 2892685 = 1084757) (by norm_num)
theorem B1737677 : Blo 1713057 1737677 := bbase (se 3 (by rfl) ⟨325814, by rfl⟩ : syracuseStep 1737677 = 651629) (by norm_num)
theorem B5784533 : Blo 1713057 5784533 := bbase (se 7 (by rfl) ⟨67787, by rfl⟩ : syracuseStep 5784533 = 135575) (by norm_num)
theorem B9765845 : Blo 1713057 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B2892773 : Blo 1713057 2892773 := bbase (se 4 (by rfl) ⟨271197, by rfl⟩ : syracuseStep 2892773 = 542395) (by norm_num)
theorem B3253277 : Blo 1713057 3253277 := bbase (se 3 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 3253277 = 1219979) (by norm_num)
theorem B5489765 : Blo 1713057 5489765 := bbase (se 4 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 5489765 = 1029331) (by norm_num)
theorem B2892901 : Blo 1713057 2892901 := bbase (se 4 (by rfl) ⟨271209, by rfl⟩ : syracuseStep 2892901 = 542419) (by norm_num)
theorem B2745485 : Blo 1713057 2745485 := bbase (se 3 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 2745485 = 1029557) (by norm_num)
theorem B2507933 : Blo 1713057 2507933 := bbase (se 3 (by rfl) ⟨470237, by rfl⟩ : syracuseStep 2507933 = 940475) (by norm_num)
theorem B3253421 : Blo 1713057 3253421 := bbase (se 3 (by rfl) ⟨610016, by rfl⟩ : syracuseStep 3253421 = 1220033) (by norm_num)
theorem B2745517 : Blo 1713057 2745517 := bbase (se 3 (by rfl) ⟨514784, by rfl⟩ : syracuseStep 2745517 = 1029569) (by norm_num)
theorem B2892989 : Blo 1713057 2892989 := bbase (se 3 (by rfl) ⟨542435, by rfl⟩ : syracuseStep 2892989 = 1084871) (by norm_num)
theorem B2507981 : Blo 1713057 2507981 := bbase (se 3 (by rfl) ⟨470246, by rfl⟩ : syracuseStep 2507981 = 940493) (by norm_num)
theorem B6505717 : Blo 1713057 6505717 := bbase (se 5 (by rfl) ⟨304955, by rfl⟩ : syracuseStep 6505717 = 609911) (by norm_num)
theorem B8234261 : Blo 1713057 8234261 := bbase (se 6 (by rfl) ⟨192990, by rfl⟩ : syracuseStep 8234261 = 385981) (by norm_num)
theorem B4695317 : Blo 1713057 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B2893117 : Blo 1713057 2893117 := bbase (se 3 (by rfl) ⟨542459, by rfl⟩ : syracuseStep 2893117 = 1084919) (by norm_num)
theorem B2712917 : Blo 1713057 2712917 := bbase (se 12 (by rfl) ⟨993, by rfl⟩ : syracuseStep 2712917 = 1987) (by norm_num)
theorem B5784965 : Blo 1713057 5784965 := bbase (se 4 (by rfl) ⟨542340, by rfl⟩ : syracuseStep 5784965 = 1084681) (by norm_num)
theorem B2893205 : Blo 1713057 2893205 := bbase (se 6 (by rfl) ⟨67809, by rfl⟩ : syracuseStep 2893205 = 135619) (by norm_num)
theorem B3253709 : Blo 1713057 3253709 := bbase (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) (by norm_num)
theorem B2229773 : Blo 1713057 2229773 := bbase (se 3 (by rfl) ⟨418082, by rfl⟩ : syracuseStep 2229773 = 836165) (by norm_num)
theorem B2893333 : Blo 1713057 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B6506021 : Blo 1713057 6506021 := bbase (se 4 (by rfl) ⟨609939, by rfl⟩ : syracuseStep 6506021 = 1219879) (by norm_num)
theorem B3712549 : Blo 1713057 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B3253861 : Blo 1713057 3253861 := bbase (se 4 (by rfl) ⟨305049, by rfl⟩ : syracuseStep 3253861 = 610099) (by norm_num)
theorem B2893421 : Blo 1713057 2893421 := bbase (se 3 (by rfl) ⟨542516, by rfl⟩ : syracuseStep 2893421 = 1085033) (by norm_num)
theorem B2893549 : Blo 1713057 2893549 := bbase (se 3 (by rfl) ⟨542540, by rfl⟩ : syracuseStep 2893549 = 1085081) (by norm_num)
theorem B2606845 : Blo 1713057 2606845 := bbase (se 3 (by rfl) ⟨488783, by rfl⟩ : syracuseStep 2606845 = 977567) (by norm_num)
theorem B5785397 : Blo 1713057 5785397 := bbase (se 5 (by rfl) ⟨271190, by rfl⟩ : syracuseStep 5785397 = 542381) (by norm_num)
theorem B2893637 : Blo 1713057 2893637 := bbase (se 4 (by rfl) ⟨271278, by rfl⟩ : syracuseStep 2893637 = 542557) (by norm_num)
theorem B8677205 : Blo 1713057 8677205 := bbase (se 9 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 8677205 = 50843) (by norm_num)
theorem B2058085 : Blo 1713057 2058085 := bbase (se 4 (by rfl) ⟨192945, by rfl⟩ : syracuseStep 2058085 = 385891) (by norm_num)
theorem B3254165 : Blo 1713057 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B2893765 : Blo 1713057 2893765 := bbase (se 4 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 2893765 = 542581) (by norm_num)
theorem B5490661 : Blo 1713057 5490661 := bbase (se 4 (by rfl) ⟨514749, by rfl⟩ : syracuseStep 5490661 = 1029499) (by norm_num)
theorem B2058229 : Blo 1713057 2058229 := bbase (se 5 (by rfl) ⟨96479, by rfl⟩ : syracuseStep 2058229 = 192959) (by norm_num)
theorem B2893853 : Blo 1713057 2893853 := bbase (se 3 (by rfl) ⟨542597, by rfl⟩ : syracuseStep 2893853 = 1085195) (by norm_num)
theorem B1927201 : Blo 1713057 1927201 := bbase (se 2 (by rfl) ⟨722700, by rfl⟩ : syracuseStep 1927201 = 1445401) (by norm_num)
theorem B1927237 : Blo 1713057 1927237 := bbase (se 4 (by rfl) ⟨180678, by rfl⟩ : syracuseStep 1927237 = 361357) (by norm_num)
theorem B2746445 : Blo 1713057 2746445 := bbase (se 3 (by rfl) ⟨514958, by rfl⟩ : syracuseStep 2746445 = 1029917) (by norm_num)
theorem B1927273 : Blo 1713057 1927273 := bbase (se 2 (by rfl) ⟨722727, by rfl⟩ : syracuseStep 1927273 = 1445455) (by norm_num)
theorem B1927309 : Blo 1713057 1927309 := bbase (se 3 (by rfl) ⟨361370, by rfl⟩ : syracuseStep 1927309 = 722741) (by norm_num)
theorem B3475613 : Blo 1713057 3475613 := bbase (se 3 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 3475613 = 1303355) (by norm_num)
theorem B2893981 : Blo 1713057 2893981 := bbase (se 3 (by rfl) ⟨542621, by rfl⟩ : syracuseStep 2893981 = 1085243) (by norm_num)
theorem B1927345 : Blo 1713057 1927345 := bbase (se 2 (by rfl) ⟨722754, by rfl⟩ : syracuseStep 1927345 = 1445509) (by norm_num)
theorem B1927381 : Blo 1713057 1927381 := bbase (se 7 (by rfl) ⟨22586, by rfl⟩ : syracuseStep 1927381 = 45173) (by norm_num)
theorem B7817429 : Blo 1713057 7817429 := bbase (se 7 (by rfl) ⟨91610, by rfl⟩ : syracuseStep 7817429 = 183221) (by norm_num)
theorem B5785829 : Blo 1713057 5785829 := bbase (se 4 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 5785829 = 1084843) (by norm_num)
theorem B2894069 : Blo 1713057 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1927417 : Blo 1713057 1927417 := bbase (se 2 (by rfl) ⟨722781, by rfl⟩ : syracuseStep 1927417 = 1445563) (by norm_num)
theorem B1927453 : Blo 1713057 1927453 := bbase (se 3 (by rfl) ⟨361397, by rfl⟩ : syracuseStep 1927453 = 722795) (by norm_num)
theorem B1927489 : Blo 1713057 1927489 := bbase (se 2 (by rfl) ⟨722808, by rfl⟩ : syracuseStep 1927489 = 1445617) (by norm_num)
theorem B1927525 : Blo 1713057 1927525 := bbase (se 4 (by rfl) ⟨180705, by rfl⟩ : syracuseStep 1927525 = 361411) (by norm_num)
theorem B1927561 : Blo 1713057 1927561 := bbase (se 2 (by rfl) ⟨722835, by rfl⟩ : syracuseStep 1927561 = 1445671) (by norm_num)
theorem B1927597 : Blo 1713057 1927597 := bbase (se 3 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 1927597 = 722849) (by norm_num)
theorem B1927633 : Blo 1713057 1927633 := bbase (se 2 (by rfl) ⟨722862, by rfl⟩ : syracuseStep 1927633 = 1445725) (by norm_num)
theorem B1927669 : Blo 1713057 1927669 := bbase (se 5 (by rfl) ⟨90359, by rfl⟩ : syracuseStep 1927669 = 180719) (by norm_num)
theorem B13199861 : Blo 1713057 13199861 := bbase (se 5 (by rfl) ⟨618743, by rfl⟩ : syracuseStep 13199861 = 1237487) (by norm_num)
theorem B3344909 : Blo 1713057 3344909 := bbase (se 3 (by rfl) ⟨627170, by rfl⟩ : syracuseStep 3344909 = 1254341) (by norm_num)
theorem B1927705 : Blo 1713057 1927705 := bbase (se 2 (by rfl) ⟨722889, by rfl⟩ : syracuseStep 1927705 = 1445779) (by norm_num)
theorem B1927741 : Blo 1713057 1927741 := bbase (se 3 (by rfl) ⟨361451, by rfl⟩ : syracuseStep 1927741 = 722903) (by norm_num)
theorem B4336213 : Blo 1713057 4336213 := bbase (se 8 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 4336213 = 50815) (by norm_num)
theorem B1927777 : Blo 1713057 1927777 := bbase (se 2 (by rfl) ⟨722916, by rfl⟩ : syracuseStep 1927777 = 1445833) (by norm_num)
theorem B1829477 : Blo 1713057 1829477 := bbase (se 4 (by rfl) ⟨171513, by rfl⟩ : syracuseStep 1829477 = 343027) (by norm_num)
theorem B1927813 : Blo 1713057 1927813 := bbase (se 4 (by rfl) ⟨180732, by rfl⟩ : syracuseStep 1927813 = 361465) (by norm_num)
theorem B3254917 : Blo 1713057 3254917 := bbase (se 4 (by rfl) ⟨305148, by rfl⟩ : syracuseStep 3254917 = 610297) (by norm_num)
theorem B5786261 : Blo 1713057 5786261 := bbase (se 6 (by rfl) ⟨135615, by rfl⟩ : syracuseStep 5786261 = 271231) (by norm_num)
theorem B7318181 : Blo 1713057 7318181 := bbase (se 4 (by rfl) ⟨686079, by rfl⟩ : syracuseStep 7318181 = 1372159) (by norm_num)
theorem B1927849 : Blo 1713057 1927849 := bbase (se 2 (by rfl) ⟨722943, by rfl⟩ : syracuseStep 1927849 = 1445887) (by norm_num)
theorem B4336325 : Blo 1713057 4336325 := bbase (se 4 (by rfl) ⟨406530, by rfl⟩ : syracuseStep 4336325 = 813061) (by norm_num)
theorem B1927885 : Blo 1713057 1927885 := bbase (se 3 (by rfl) ⟨361478, by rfl⟩ : syracuseStep 1927885 = 722957) (by norm_num)
theorem B13191893 : Blo 1713057 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B1927921 : Blo 1713057 1927921 := bbase (se 2 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 1927921 = 1445941) (by norm_num)
theorem B2747125 : Blo 1713057 2747125 := bbase (se 5 (by rfl) ⟨128771, by rfl⟩ : syracuseStep 2747125 = 257543) (by norm_num)
theorem B1927957 : Blo 1713057 1927957 := bbase (se 6 (by rfl) ⟨45186, by rfl⟩ : syracuseStep 1927957 = 90373) (by norm_num)
theorem B3255061 : Blo 1713057 3255061 := bbase (se 6 (by rfl) ⟨76290, by rfl⟩ : syracuseStep 3255061 = 152581) (by norm_num)
theorem B1829665 : Blo 1713057 1829665 := bbase (se 2 (by rfl) ⟨686124, by rfl⟩ : syracuseStep 1829665 = 1372249) (by norm_num)
theorem B2747189 : Blo 1713057 2747189 := bbase (se 5 (by rfl) ⟨128774, by rfl⟩ : syracuseStep 2747189 = 257549) (by norm_num)
theorem B1927993 : Blo 1713057 1927993 := bbase (se 2 (by rfl) ⟨722997, by rfl⟩ : syracuseStep 1927993 = 1445995) (by norm_num)
theorem B1928029 : Blo 1713057 1928029 := bbase (se 3 (by rfl) ⟨361505, by rfl⟩ : syracuseStep 1928029 = 723011) (by norm_num)
theorem B8235877 : Blo 1713057 8235877 := bbase (se 4 (by rfl) ⟨772113, by rfl⟩ : syracuseStep 8235877 = 1544227) (by norm_num)
theorem B1928065 : Blo 1713057 1928065 := bbase (se 2 (by rfl) ⟨723024, by rfl⟩ : syracuseStep 1928065 = 1446049) (by norm_num)
theorem B4336517 : Blo 1713057 4336517 := bbase (se 4 (by rfl) ⟨406548, by rfl⟩ : syracuseStep 4336517 = 813097) (by norm_num)
theorem B7318421 : Blo 1713057 7318421 := bbase (se 6 (by rfl) ⟨171525, by rfl⟩ : syracuseStep 7318421 = 343051) (by norm_num)
theorem B1928101 : Blo 1713057 1928101 := bbase (se 4 (by rfl) ⟨180759, by rfl⟩ : syracuseStep 1928101 = 361519) (by norm_num)
theorem B5721013 : Blo 1713057 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B3255221 : Blo 1713057 3255221 := bbase (se 5 (by rfl) ⟨152588, by rfl⟩ : syracuseStep 3255221 = 305177) (by norm_num)
theorem B1928137 : Blo 1713057 1928137 := bbase (se 2 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 1928137 = 1446103) (by norm_num)
theorem B2059229 : Blo 1713057 2059229 := bbase (se 3 (by rfl) ⟨386105, by rfl⟩ : syracuseStep 2059229 = 772211) (by norm_num)
theorem B1928173 : Blo 1713057 1928173 := bbase (se 3 (by rfl) ⟨361532, by rfl⟩ : syracuseStep 1928173 = 723065) (by norm_num)
theorem B1928209 : Blo 1713057 1928209 := bbase (se 2 (by rfl) ⟨723078, by rfl⟩ : syracuseStep 1928209 = 1446157) (by norm_num)
theorem B1928245 : Blo 1713057 1928245 := bbase (se 5 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 1928245 = 180773) (by norm_num)
theorem B5786693 : Blo 1713057 5786693 := bbase (se 4 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 5786693 = 1085005) (by norm_num)
theorem B3255365 : Blo 1713057 3255365 := bbase (se 4 (by rfl) ⟨305190, by rfl⟩ : syracuseStep 3255365 = 610381) (by norm_num)
theorem B1928281 : Blo 1713057 1928281 := bbase (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) (by norm_num)
theorem B2174045 : Blo 1713057 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B8678501 : Blo 1713057 8678501 := bbase (se 4 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 8678501 = 1627219) (by norm_num)
theorem B1928317 : Blo 1713057 1928317 := bbase (se 3 (by rfl) ⟨361559, by rfl⟩ : syracuseStep 1928317 = 723119) (by norm_num)
theorem B1928353 : Blo 1713057 1928353 := bbase (se 2 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 1928353 = 1446265) (by norm_num)
theorem B1928389 : Blo 1713057 1928389 := bbase (se 4 (by rfl) ⟨180786, by rfl⟩ : syracuseStep 1928389 = 361573) (by norm_num)
theorem B3476677 : Blo 1713057 3476677 := bbase (se 4 (by rfl) ⟨325938, by rfl⟩ : syracuseStep 3476677 = 651877) (by norm_num)
theorem B4336861 : Blo 1713057 4336861 := bbase (se 3 (by rfl) ⟨813161, by rfl⟩ : syracuseStep 4336861 = 1626323) (by norm_num)
theorem B1928425 : Blo 1713057 1928425 := bbase (se 2 (by rfl) ⟨723159, by rfl⟩ : syracuseStep 1928425 = 1446319) (by norm_num)
theorem B1928461 : Blo 1713057 1928461 := bbase (se 3 (by rfl) ⟨361586, by rfl⟩ : syracuseStep 1928461 = 723173) (by norm_num)
theorem B1928497 : Blo 1713057 1928497 := bbase (se 2 (by rfl) ⟨723186, by rfl⟩ : syracuseStep 1928497 = 1446373) (by norm_num)
theorem B4336973 : Blo 1713057 4336973 := bbase (se 3 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 4336973 = 1626365) (by norm_num)
theorem B1928533 : Blo 1713057 1928533 := bbase (se 11 (by rfl) ⟨1412, by rfl⟩ : syracuseStep 1928533 = 2825) (by norm_num)
theorem B3255653 : Blo 1713057 3255653 := bbase (se 4 (by rfl) ⟨305217, by rfl⟩ : syracuseStep 3255653 = 610435) (by norm_num)
theorem B1928569 : Blo 1713057 1928569 := bbase (se 2 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 1928569 = 1446427) (by norm_num)
theorem B1928605 : Blo 1713057 1928605 := bbase (se 3 (by rfl) ⟨361613, by rfl⟩ : syracuseStep 1928605 = 723227) (by norm_num)
theorem B1928641 : Blo 1713057 1928641 := bbase (se 2 (by rfl) ⟨723240, by rfl⟩ : syracuseStep 1928641 = 1446481) (by norm_num)
theorem B1928677 : Blo 1713057 1928677 := bbase (se 4 (by rfl) ⟨180813, by rfl⟩ : syracuseStep 1928677 = 361627) (by norm_num)
theorem B5787125 : Blo 1713057 5787125 := bbase (se 5 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 5787125 = 542543) (by norm_num)
theorem B3255805 : Blo 1713057 3255805 := bbase (se 3 (by rfl) ⟨610463, by rfl⟩ : syracuseStep 3255805 = 1220927) (by norm_num)
theorem B1928713 : Blo 1713057 1928713 := bbase (se 2 (by rfl) ⟨723267, by rfl⟩ : syracuseStep 1928713 = 1446535) (by norm_num)
theorem B4337165 : Blo 1713057 4337165 := bbase (se 3 (by rfl) ⟨813218, by rfl⟩ : syracuseStep 4337165 = 1626437) (by norm_num)
theorem B5565989 : Blo 1713057 5565989 := bbase (se 4 (by rfl) ⟨521811, by rfl⟩ : syracuseStep 5565989 = 1043623) (by norm_num)
theorem B1928749 : Blo 1713057 1928749 := bbase (se 3 (by rfl) ⟨361640, by rfl⟩ : syracuseStep 1928749 = 723281) (by norm_num)
theorem B1928785 : Blo 1713057 1928785 := bbase (se 2 (by rfl) ⟨723294, by rfl⟩ : syracuseStep 1928785 = 1446589) (by norm_num)
theorem B1830485 : Blo 1713057 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B6508133 : Blo 1713057 6508133 := bbase (se 4 (by rfl) ⟨610137, by rfl⟩ : syracuseStep 6508133 = 1220275) (by norm_num)
theorem B1928821 : Blo 1713057 1928821 := bbase (se 5 (by rfl) ⟨90413, by rfl⟩ : syracuseStep 1928821 = 180827) (by norm_num)
theorem B2059921 : Blo 1713057 2059921 := bbase (se 2 (by rfl) ⟨772470, by rfl⟩ : syracuseStep 2059921 = 1544941) (by norm_num)
theorem B6950549 : Blo 1713057 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B1928857 : Blo 1713057 1928857 := bbase (se 2 (by rfl) ⟨723321, by rfl⟩ : syracuseStep 1928857 = 1446643) (by norm_num)
theorem B1928893 : Blo 1713057 1928893 := bbase (se 3 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 1928893 = 723335) (by norm_num)
theorem B7417541 : Blo 1713057 7417541 := bbase (se 4 (by rfl) ⟨695394, by rfl⟩ : syracuseStep 7417541 = 1390789) (by norm_num)
theorem B1928929 : Blo 1713057 1928929 := bbase (se 2 (by rfl) ⟨723348, by rfl⟩ : syracuseStep 1928929 = 1446697) (by norm_num)
theorem B1855217 : Blo 1713057 1855217 := bbase (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) (by norm_num)
theorem B1928965 : Blo 1713057 1928965 := bbase (se 4 (by rfl) ⟨180840, by rfl⟩ : syracuseStep 1928965 = 361681) (by norm_num)
theorem B1929001 : Blo 1713057 1929001 := bbase (se 2 (by rfl) ⟨723375, by rfl⟩ : syracuseStep 1929001 = 1446751) (by norm_num)
theorem B1929037 : Blo 1713057 1929037 := bbase (se 3 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 1929037 = 723389) (by norm_num)
theorem B35163989 : Blo 1713057 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B4337509 : Blo 1713057 4337509 := bbase (se 4 (by rfl) ⟨406641, by rfl⟩ : syracuseStep 4337509 = 813283) (by norm_num)
theorem B2060137 : Blo 1713057 2060137 := bbase (se 2 (by rfl) ⟨772551, by rfl⟩ : syracuseStep 2060137 = 1545103) (by norm_num)
theorem B1929073 : Blo 1713057 1929073 := bbase (se 2 (by rfl) ⟨723402, by rfl⟩ : syracuseStep 1929073 = 1446805) (by norm_num)
theorem B6508421 : Blo 1713057 6508421 := bbase (se 4 (by rfl) ⟨610164, by rfl⟩ : syracuseStep 6508421 = 1220329) (by norm_num)
theorem B1929109 : Blo 1713057 1929109 := bbase (se 6 (by rfl) ⟨45213, by rfl⟩ : syracuseStep 1929109 = 90427) (by norm_num)
theorem B5787557 : Blo 1713057 5787557 := bbase (se 4 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 5787557 = 1085167) (by norm_num)
theorem B1929145 : Blo 1713057 1929145 := bbase (se 2 (by rfl) ⟨723429, by rfl⟩ : syracuseStep 1929145 = 1446859) (by norm_num)
theorem B4337621 : Blo 1713057 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B1929181 : Blo 1713057 1929181 := bbase (se 3 (by rfl) ⟨361721, by rfl⟩ : syracuseStep 1929181 = 723443) (by norm_num)
theorem B1929217 : Blo 1713057 1929217 := bbase (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) (by norm_num)
theorem B1830929 : Blo 1713057 1830929 := bbase (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) (by norm_num)
theorem B1929253 : Blo 1713057 1929253 := bbase (se 4 (by rfl) ⟨180867, by rfl⟩ : syracuseStep 1929253 = 361735) (by norm_num)
theorem B1953865 : Blo 1713057 1953865 := bbase (se 2 (by rfl) ⟨732699, by rfl⟩ : syracuseStep 1953865 = 1465399) (by norm_num)
theorem B1929289 : Blo 1713057 1929289 := bbase (se 2 (by rfl) ⟨723483, by rfl⟩ : syracuseStep 1929289 = 1446967) (by norm_num)
theorem B11751509 : Blo 1713057 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B3854429 : Blo 1713057 3854429 := bbase (se 3 (by rfl) ⟨722705, by rfl⟩ : syracuseStep 3854429 = 1445411) (by norm_num)
theorem B1929325 : Blo 1713057 1929325 := bbase (se 3 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 1929325 = 723497) (by norm_num)
theorem B1929361 : Blo 1713057 1929361 := bbase (se 2 (by rfl) ⟨723510, by rfl⟩ : syracuseStep 1929361 = 1447021) (by norm_num)
theorem B4337813 : Blo 1713057 4337813 := bbase (se 6 (by rfl) ⟨101667, by rfl⟩ : syracuseStep 4337813 = 203335) (by norm_num)
theorem B3854501 : Blo 1713057 3854501 := bbase (se 4 (by rfl) ⟨361359, by rfl⟩ : syracuseStep 3854501 = 722719) (by norm_num)
theorem B1929397 : Blo 1713057 1929397 := bbase (se 5 (by rfl) ⟨90440, by rfl⟩ : syracuseStep 1929397 = 180881) (by norm_num)
theorem B13021397 : Blo 1713057 13021397 := bbase (se 7 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 13021397 = 305189) (by norm_num)
theorem B1929433 : Blo 1713057 1929433 := bbase (se 2 (by rfl) ⟨723537, by rfl⟩ : syracuseStep 1929433 = 1447075) (by norm_num)
theorem B1855721 : Blo 1713057 1855721 := bbase (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) (by norm_num)
theorem B3854573 : Blo 1713057 3854573 := bbase (se 3 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 3854573 = 1445465) (by norm_num)
theorem B6598901 : Blo 1713057 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1831177 : Blo 1713057 1831177 := bbase (se 2 (by rfl) ⟨686691, by rfl⟩ : syracuseStep 1831177 = 1373383) (by norm_num)
theorem B3854645 : Blo 1713057 3854645 := bbase (se 5 (by rfl) ⟨180686, by rfl⟩ : syracuseStep 3854645 = 361373) (by norm_num)
theorem B5787989 : Blo 1713057 5787989 := bbase (se 10 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 5787989 = 16957) (by norm_num)
theorem B8679797 : Blo 1713057 8679797 := bbase (se 5 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 8679797 = 813731) (by norm_num)
theorem B3854717 : Blo 1713057 3854717 := bbase (se 3 (by rfl) ⟨722759, by rfl⟩ : syracuseStep 3854717 = 1445519) (by norm_num)
theorem B14643605 : Blo 1713057 14643605 := bbase (se 6 (by rfl) ⟨343209, by rfl⟩ : syracuseStep 14643605 = 686419) (by norm_num)
theorem B3854789 : Blo 1713057 3854789 := bbase (se 4 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 3854789 = 722773) (by norm_num)
theorem B4338157 : Blo 1713057 4338157 := bbase (se 3 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 4338157 = 1626809) (by norm_num)
theorem B4116997 : Blo 1713057 4116997 := bbase (se 4 (by rfl) ⟨385968, by rfl⟩ : syracuseStep 4116997 = 771937) (by norm_num)
theorem B2200069 : Blo 1713057 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B3854861 : Blo 1713057 3854861 := bbase (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) (by norm_num)
theorem B3854933 : Blo 1713057 3854933 := bbase (se 8 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 3854933 = 45175) (by norm_num)
theorem B4338269 : Blo 1713057 4338269 := bbase (se 3 (by rfl) ⟨813425, by rfl⟩ : syracuseStep 4338269 = 1626851) (by norm_num)
theorem B13013621 : Blo 1713057 13013621 := bbase (se 5 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 13013621 = 1220027) (by norm_num)
theorem B3855005 : Blo 1713057 3855005 := bbase (se 3 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 3855005 = 1445627) (by norm_num)
theorem B4879061 : Blo 1713057 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B3855077 : Blo 1713057 3855077 := bbase (se 4 (by rfl) ⟨361413, by rfl⟩ : syracuseStep 3855077 = 722827) (by norm_num)
theorem B4338461 : Blo 1713057 4338461 := bbase (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) (by norm_num)
theorem B3855149 : Blo 1713057 3855149 := bbase (se 3 (by rfl) ⟨722840, by rfl⟩ : syracuseStep 3855149 = 1445681) (by norm_num)
theorem B5493557 : Blo 1713057 5493557 := bbase (se 5 (by rfl) ⟨257510, by rfl⟩ : syracuseStep 5493557 = 515021) (by norm_num)
theorem B3855221 : Blo 1713057 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B3855293 : Blo 1713057 3855293 := bbase (se 3 (by rfl) ⟨722867, by rfl⟩ : syracuseStep 3855293 = 1445735) (by norm_num)
theorem B3855365 : Blo 1713057 3855365 := bbase (se 4 (by rfl) ⟨361440, by rfl⟩ : syracuseStep 3855365 = 722881) (by norm_num)
theorem B6509605 : Blo 1713057 6509605 := bbase (se 4 (by rfl) ⟨610275, by rfl⟩ : syracuseStep 6509605 = 1220551) (by norm_num)
theorem B13906997 : Blo 1713057 13906997 := bbase (se 5 (by rfl) ⟨651890, by rfl⟩ : syracuseStep 13906997 = 1303781) (by norm_num)
theorem B3855437 : Blo 1713057 3855437 := bbase (se 3 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 3855437 = 1445789) (by norm_num)
theorem B17585237 : Blo 1713057 17585237 := bbase (se 8 (by rfl) ⟨103038, by rfl⟩ : syracuseStep 17585237 = 206077) (by norm_num)
theorem B4338805 : Blo 1713057 4338805 := bbase (se 5 (by rfl) ⟨203381, by rfl⟩ : syracuseStep 4338805 = 406763) (by norm_num)
theorem B7320709 : Blo 1713057 7320709 := bbase (se 4 (by rfl) ⟨686316, by rfl⟩ : syracuseStep 7320709 = 1372633) (by norm_num)
theorem B6952069 : Blo 1713057 6952069 := bbase (se 4 (by rfl) ⟨651756, by rfl⟩ : syracuseStep 6952069 = 1303513) (by norm_num)
theorem B3855509 : Blo 1713057 3855509 := bbase (se 6 (by rfl) ⟨90363, by rfl⟩ : syracuseStep 3855509 = 180727) (by norm_num)
theorem B4117661 : Blo 1713057 4117661 := bbase (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) (by norm_num)
theorem B4945109 : Blo 1713057 4945109 := bbase (se 7 (by rfl) ⟨57950, by rfl⟩ : syracuseStep 4945109 = 115901) (by norm_num)
theorem B3855581 : Blo 1713057 3855581 := bbase (se 3 (by rfl) ⟨722921, by rfl⟩ : syracuseStep 3855581 = 1445843) (by norm_num)
theorem B4338917 : Blo 1713057 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B3855653 : Blo 1713057 3855653 := bbase (se 4 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 3855653 = 722935) (by norm_num)
theorem B2168137 : Blo 1713057 2168137 := bbase (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) (by norm_num)
theorem B6509909 : Blo 1713057 6509909 := bbase (se 17 (by rfl) ⟨74, by rfl⟩ : syracuseStep 6509909 = 149) (by norm_num)
theorem B4633957 : Blo 1713057 4633957 := bbase (se 4 (by rfl) ⟨434433, by rfl⟩ : syracuseStep 4633957 = 868867) (by norm_num)
theorem B3855725 : Blo 1713057 3855725 := bbase (se 3 (by rfl) ⟨722948, by rfl⟩ : syracuseStep 3855725 = 1445897) (by norm_num)
theorem B2569589 : Blo 1713057 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B2569613 : Blo 1713057 2569613 := bbase (se 3 (by rfl) ⟨481802, by rfl⟩ : syracuseStep 2569613 = 963605) (by norm_num)
theorem B2569637 : Blo 1713057 2569637 := bbase (se 4 (by rfl) ⟨240903, by rfl⟩ : syracuseStep 2569637 = 481807) (by norm_num)
theorem B4339109 : Blo 1713057 4339109 := bbase (se 4 (by rfl) ⟨406791, by rfl⟩ : syracuseStep 4339109 = 813583) (by norm_num)
theorem B3855797 : Blo 1713057 3855797 := bbase (se 5 (by rfl) ⟨180740, by rfl⟩ : syracuseStep 3855797 = 361481) (by norm_num)
theorem B2569661 : Blo 1713057 2569661 := bbase (se 3 (by rfl) ⟨481811, by rfl⟩ : syracuseStep 2569661 = 963623) (by norm_num)
theorem B2569685 : Blo 1713057 2569685 := bbase (se 7 (by rfl) ⟨30113, by rfl⟩ : syracuseStep 2569685 = 60227) (by norm_num)
theorem B2569709 : Blo 1713057 2569709 := bbase (se 3 (by rfl) ⟨481820, by rfl⟩ : syracuseStep 2569709 = 963641) (by norm_num)
theorem B2168309 : Blo 1713057 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B3659261 : Blo 1713057 3659261 := bbase (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) (by norm_num)
theorem B3855869 : Blo 1713057 3855869 := bbase (se 3 (by rfl) ⟨722975, by rfl⟩ : syracuseStep 3855869 = 1445951) (by norm_num)
theorem B2569733 : Blo 1713057 2569733 := bbase (se 4 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 2569733 = 481825) (by norm_num)
theorem B2569757 : Blo 1713057 2569757 := bbase (se 3 (by rfl) ⟨481829, by rfl⟩ : syracuseStep 2569757 = 963659) (by norm_num)
theorem B2168365 : Blo 1713057 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B2569781 : Blo 1713057 2569781 := bbase (se 5 (by rfl) ⟨120458, by rfl⟩ : syracuseStep 2569781 = 240917) (by norm_num)
theorem B3855941 : Blo 1713057 3855941 := bbase (se 4 (by rfl) ⟨361494, by rfl⟩ : syracuseStep 3855941 = 722989) (by norm_num)
theorem B2569805 : Blo 1713057 2569805 := bbase (se 3 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 2569805 = 963677) (by norm_num)
theorem B2569829 : Blo 1713057 2569829 := bbase (se 4 (by rfl) ⟨240921, by rfl⟩ : syracuseStep 2569829 = 481843) (by norm_num)
theorem B1955449 : Blo 1713057 1955449 := bbase (se 2 (by rfl) ⟨733293, by rfl⟩ : syracuseStep 1955449 = 1466587) (by norm_num)
theorem B2569853 : Blo 1713057 2569853 := bbase (se 3 (by rfl) ⟨481847, by rfl⟩ : syracuseStep 2569853 = 963695) (by norm_num)
theorem B8681093 : Blo 1713057 8681093 := bbase (se 4 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 8681093 = 1627705) (by norm_num)
theorem B2168461 : Blo 1713057 2168461 := bbase (se 3 (by rfl) ⟨406586, by rfl⟩ : syracuseStep 2168461 = 813173) (by norm_num)
theorem B3856013 : Blo 1713057 3856013 := bbase (se 3 (by rfl) ⟨723002, by rfl⟩ : syracuseStep 3856013 = 1446005) (by norm_num)
theorem B2569877 : Blo 1713057 2569877 := bbase (se 6 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 2569877 = 120463) (by norm_num)
theorem B2569901 : Blo 1713057 2569901 := bbase (se 3 (by rfl) ⟨481856, by rfl⟩ : syracuseStep 2569901 = 963713) (by norm_num)
theorem B2569925 : Blo 1713057 2569925 := bbase (se 4 (by rfl) ⟨240930, by rfl⟩ : syracuseStep 2569925 = 481861) (by norm_num)
theorem B3856085 : Blo 1713057 3856085 := bbase (se 7 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 3856085 = 90377) (by norm_num)
theorem B2569949 : Blo 1713057 2569949 := bbase (se 3 (by rfl) ⟨481865, by rfl⟩ : syracuseStep 2569949 = 963731) (by norm_num)
theorem B3659501 : Blo 1713057 3659501 := bbase (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) (by norm_num)
theorem B2569973 : Blo 1713057 2569973 := bbase (se 5 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 2569973 = 240935) (by norm_num)
theorem B4339453 : Blo 1713057 4339453 := bbase (se 3 (by rfl) ⟨813647, by rfl⟩ : syracuseStep 4339453 = 1627295) (by norm_num)
theorem B2569997 : Blo 1713057 2569997 := bbase (se 3 (by rfl) ⟨481874, by rfl⟩ : syracuseStep 2569997 = 963749) (by norm_num)
theorem B3856157 : Blo 1713057 3856157 := bbase (se 3 (by rfl) ⟨723029, by rfl⟩ : syracuseStep 3856157 = 1446059) (by norm_num)
theorem B2570021 : Blo 1713057 2570021 := bbase (se 4 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 2570021 = 481879) (by norm_num)
theorem B2168633 : Blo 1713057 2168633 := bbase (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) (by norm_num)
theorem B2570045 : Blo 1713057 2570045 := bbase (se 3 (by rfl) ⟨481883, by rfl⟩ : syracuseStep 2570045 = 963767) (by norm_num)
theorem B2570069 : Blo 1713057 2570069 := bbase (se 9 (by rfl) ⟨7529, by rfl⟩ : syracuseStep 2570069 = 15059) (by norm_num)
theorem B3856229 : Blo 1713057 3856229 := bbase (se 4 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 3856229 = 723043) (by norm_num)
theorem B7821157 : Blo 1713057 7821157 := bbase (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) (by norm_num)
theorem B2570093 : Blo 1713057 2570093 := bbase (se 3 (by rfl) ⟨481892, by rfl⟩ : syracuseStep 2570093 = 963785) (by norm_num)
theorem B4339565 : Blo 1713057 4339565 := bbase (se 3 (by rfl) ⟨813668, by rfl⟩ : syracuseStep 4339565 = 1627337) (by norm_num)
theorem B2168689 : Blo 1713057 2168689 := bbase (se 2 (by rfl) ⟨813258, by rfl⟩ : syracuseStep 2168689 = 1626517) (by norm_num)
theorem B4880245 : Blo 1713057 4880245 := bbase (se 5 (by rfl) ⟨228761, by rfl⟩ : syracuseStep 4880245 = 457523) (by norm_num)
theorem B9762677 : Blo 1713057 9762677 := bbase (se 5 (by rfl) ⟨457625, by rfl⟩ : syracuseStep 9762677 = 915251) (by norm_num)
theorem B2570117 : Blo 1713057 2570117 := bbase (se 4 (by rfl) ⟨240948, by rfl⟩ : syracuseStep 2570117 = 481897) (by norm_num)
theorem B2570141 : Blo 1713057 2570141 := bbase (se 3 (by rfl) ⟨481901, by rfl⟩ : syracuseStep 2570141 = 963803) (by norm_num)
theorem B3856301 : Blo 1713057 3856301 := bbase (se 3 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 3856301 = 1446113) (by norm_num)
theorem B2570165 : Blo 1713057 2570165 := bbase (se 5 (by rfl) ⟨120476, by rfl⟩ : syracuseStep 2570165 = 240953) (by norm_num)
theorem B2439109 : Blo 1713057 2439109 := bbase (se 4 (by rfl) ⟨228666, by rfl⟩ : syracuseStep 2439109 = 457333) (by norm_num)
theorem B2570189 : Blo 1713057 2570189 := bbase (se 3 (by rfl) ⟨481910, by rfl⟩ : syracuseStep 2570189 = 963821) (by norm_num)
theorem B2168785 : Blo 1713057 2168785 := bbase (se 2 (by rfl) ⟨813294, by rfl⟩ : syracuseStep 2168785 = 1626589) (by norm_num)
theorem B2570213 : Blo 1713057 2570213 := bbase (se 4 (by rfl) ⟨240957, by rfl⟩ : syracuseStep 2570213 = 481915) (by norm_num)
theorem B3856373 : Blo 1713057 3856373 := bbase (se 5 (by rfl) ⟨180767, by rfl⟩ : syracuseStep 3856373 = 361535) (by norm_num)
theorem B2570237 : Blo 1713057 2570237 := bbase (se 3 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 2570237 = 963839) (by norm_num)
theorem B2570261 : Blo 1713057 2570261 := bbase (se 6 (by rfl) ⟨60240, by rfl⟩ : syracuseStep 2570261 = 120481) (by norm_num)
theorem B4880405 : Blo 1713057 4880405 := bbase (se 6 (by rfl) ⟨114384, by rfl⟩ : syracuseStep 4880405 = 228769) (by norm_num)
theorem B8673317 : Blo 1713057 8673317 := bbase (se 4 (by rfl) ⟨813123, by rfl⟩ : syracuseStep 8673317 = 1626247) (by norm_num)
theorem B2570285 : Blo 1713057 2570285 := bbase (se 3 (by rfl) ⟨481928, by rfl⟩ : syracuseStep 2570285 = 963857) (by norm_num)
theorem B4339757 : Blo 1713057 4339757 := bbase (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) (by norm_num)
theorem B6174773 : Blo 1713057 6174773 := bbase (se 5 (by rfl) ⟨289442, by rfl⟩ : syracuseStep 6174773 = 578885) (by norm_num)
theorem B2439229 : Blo 1713057 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B3856445 : Blo 1713057 3856445 := bbase (se 3 (by rfl) ⟨723083, by rfl⟩ : syracuseStep 3856445 = 1446167) (by norm_num)
theorem B2570309 : Blo 1713057 2570309 := bbase (se 4 (by rfl) ⟨240966, by rfl⟩ : syracuseStep 2570309 = 481933) (by norm_num)
theorem B2570333 : Blo 1713057 2570333 := bbase (se 3 (by rfl) ⟨481937, by rfl⟩ : syracuseStep 2570333 = 963875) (by norm_num)
theorem B2570357 : Blo 1713057 2570357 := bbase (se 5 (by rfl) ⟨120485, by rfl⟩ : syracuseStep 2570357 = 240971) (by norm_num)
theorem B2168957 : Blo 1713057 2168957 := bbase (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) (by norm_num)
theorem B3856517 : Blo 1713057 3856517 := bbase (se 4 (by rfl) ⟨361548, by rfl⟩ : syracuseStep 3856517 = 723097) (by norm_num)
theorem B2570381 : Blo 1713057 2570381 := bbase (se 3 (by rfl) ⟨481946, by rfl⟩ : syracuseStep 2570381 = 963893) (by norm_num)
theorem B2439325 : Blo 1713057 2439325 := bbase (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) (by norm_num)
theorem B2570405 : Blo 1713057 2570405 := bbase (se 4 (by rfl) ⟨240975, by rfl⟩ : syracuseStep 2570405 = 481951) (by norm_num)
theorem B2169013 : Blo 1713057 2169013 := bbase (se 5 (by rfl) ⟨101672, by rfl⟩ : syracuseStep 2169013 = 203345) (by norm_num)
theorem B2570429 : Blo 1713057 2570429 := bbase (se 3 (by rfl) ⟨481955, by rfl⟩ : syracuseStep 2570429 = 963911) (by norm_num)
theorem B3856589 : Blo 1713057 3856589 := bbase (se 3 (by rfl) ⟨723110, by rfl⟩ : syracuseStep 3856589 = 1446221) (by norm_num)
theorem B2570453 : Blo 1713057 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B3660005 : Blo 1713057 3660005 := bbase (se 4 (by rfl) ⟨343125, by rfl⟩ : syracuseStep 3660005 = 686251) (by norm_num)
theorem B2570477 : Blo 1713057 2570477 := bbase (se 3 (by rfl) ⟨481964, by rfl⟩ : syracuseStep 2570477 = 963929) (by norm_num)
theorem B3660013 : Blo 1713057 3660013 := bbase (se 3 (by rfl) ⟨686252, by rfl⟩ : syracuseStep 3660013 = 1372505) (by norm_num)
theorem B2570501 : Blo 1713057 2570501 := bbase (se 4 (by rfl) ⟨240984, by rfl⟩ : syracuseStep 2570501 = 481969) (by norm_num)
theorem B4880645 : Blo 1713057 4880645 := bbase (se 4 (by rfl) ⟨457560, by rfl⟩ : syracuseStep 4880645 = 915121) (by norm_num)
theorem B2316557 : Blo 1713057 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B2169109 : Blo 1713057 2169109 := bbase (se 6 (by rfl) ⟨50838, by rfl⟩ : syracuseStep 2169109 = 101677) (by norm_num)
theorem B3856661 : Blo 1713057 3856661 := bbase (se 6 (by rfl) ⟨90390, by rfl⟩ : syracuseStep 3856661 = 180781) (by norm_num)
theorem B2570525 : Blo 1713057 2570525 := bbase (se 3 (by rfl) ⟨481973, by rfl⟩ : syracuseStep 2570525 = 963947) (by norm_num)
theorem B2570549 : Blo 1713057 2570549 := bbase (se 5 (by rfl) ⟨120494, by rfl⟩ : syracuseStep 2570549 = 240989) (by norm_num)
theorem B2570573 : Blo 1713057 2570573 := bbase (se 3 (by rfl) ⟨481982, by rfl⟩ : syracuseStep 2570573 = 963965) (by norm_num)
theorem B3856733 : Blo 1713057 3856733 := bbase (se 3 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 3856733 = 1446275) (by norm_num)
theorem B2570597 : Blo 1713057 2570597 := bbase (se 4 (by rfl) ⟨240993, by rfl⟩ : syracuseStep 2570597 = 481987) (by norm_num)
theorem B2570621 : Blo 1713057 2570621 := bbase (se 3 (by rfl) ⟨481991, by rfl⟩ : syracuseStep 2570621 = 963983) (by norm_num)
theorem B2783621 : Blo 1713057 2783621 := bbase (se 4 (by rfl) ⟨260964, by rfl⟩ : syracuseStep 2783621 = 521929) (by norm_num)
theorem B4340101 : Blo 1713057 4340101 := bbase (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) (by norm_num)
theorem B2570645 : Blo 1713057 2570645 := bbase (se 6 (by rfl) ⟨60249, by rfl⟩ : syracuseStep 2570645 = 120499) (by norm_num)
theorem B3856805 : Blo 1713057 3856805 := bbase (se 4 (by rfl) ⟨361575, by rfl⟩ : syracuseStep 3856805 = 723151) (by norm_num)
theorem B2570669 : Blo 1713057 2570669 := bbase (se 3 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 2570669 = 964001) (by norm_num)
theorem B5781941 : Blo 1713057 5781941 := bbase (se 5 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 5781941 = 542057) (by norm_num)
theorem B2169281 : Blo 1713057 2169281 := bbase (se 2 (by rfl) ⟨813480, by rfl⟩ : syracuseStep 2169281 = 1626961) (by norm_num)
theorem B2570693 : Blo 1713057 2570693 := bbase (se 4 (by rfl) ⟨241002, by rfl⟩ : syracuseStep 2570693 = 482005) (by norm_num)
theorem B4880837 : Blo 1713057 4880837 := bbase (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) (by norm_num)
theorem B2570717 : Blo 1713057 2570717 := bbase (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) (by norm_num)
theorem B3856877 : Blo 1713057 3856877 := bbase (se 3 (by rfl) ⟨723164, by rfl⟩ : syracuseStep 3856877 = 1446329) (by norm_num)
theorem B2570741 : Blo 1713057 2570741 := bbase (se 5 (by rfl) ⟨120503, by rfl⟩ : syracuseStep 2570741 = 241007) (by norm_num)
theorem B4340213 : Blo 1713057 4340213 := bbase (se 5 (by rfl) ⟨203447, by rfl⟩ : syracuseStep 4340213 = 406895) (by norm_num)
theorem B2169337 : Blo 1713057 2169337 := bbase (se 2 (by rfl) ⟨813501, by rfl⟩ : syracuseStep 2169337 = 1627003) (by norm_num)
theorem B2570765 : Blo 1713057 2570765 := bbase (se 3 (by rfl) ⟨482018, by rfl⟩ : syracuseStep 2570765 = 964037) (by norm_num)
theorem B2570789 : Blo 1713057 2570789 := bbase (se 4 (by rfl) ⟨241011, by rfl⟩ : syracuseStep 2570789 = 482023) (by norm_num)
theorem B3856949 : Blo 1713057 3856949 := bbase (se 5 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 3856949 = 361589) (by norm_num)
theorem B2570813 : Blo 1713057 2570813 := bbase (se 3 (by rfl) ⟨482027, by rfl⟩ : syracuseStep 2570813 = 964055) (by norm_num)
theorem B12352085 : Blo 1713057 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B2570837 : Blo 1713057 2570837 := bbase (se 8 (by rfl) ⟨15063, by rfl⟩ : syracuseStep 2570837 = 30127) (by norm_num)
theorem B7322197 : Blo 1713057 7322197 := bbase (se 8 (by rfl) ⟨42903, by rfl⟩ : syracuseStep 7322197 = 85807) (by norm_num)
theorem B2169433 : Blo 1713057 2169433 := bbase (se 2 (by rfl) ⟨813537, by rfl⟩ : syracuseStep 2169433 = 1627075) (by norm_num)
theorem B7322213 : Blo 1713057 7322213 := bbase (se 4 (by rfl) ⟨686457, by rfl⟩ : syracuseStep 7322213 = 1372915) (by norm_num)
theorem B2570861 : Blo 1713057 2570861 := bbase (se 3 (by rfl) ⟨482036, by rfl⟩ : syracuseStep 2570861 = 964073) (by norm_num)
theorem B3857021 : Blo 1713057 3857021 := bbase (se 3 (by rfl) ⟨723191, by rfl⟩ : syracuseStep 3857021 = 1446383) (by norm_num)
theorem B2570885 : Blo 1713057 2570885 := bbase (se 4 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 2570885 = 482041) (by norm_num)
theorem B2439821 : Blo 1713057 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B2570909 : Blo 1713057 2570909 := bbase (se 3 (by rfl) ⟨482045, by rfl⟩ : syracuseStep 2570909 = 964091) (by norm_num)
theorem B2570933 : Blo 1713057 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B4340405 : Blo 1713057 4340405 := bbase (se 5 (by rfl) ⟨203456, by rfl⟩ : syracuseStep 4340405 = 406913) (by norm_num)
theorem B3857093 : Blo 1713057 3857093 := bbase (se 4 (by rfl) ⟨361602, by rfl⟩ : syracuseStep 3857093 = 723205) (by norm_num)
theorem B2570957 : Blo 1713057 2570957 := bbase (se 3 (by rfl) ⟨482054, by rfl⟩ : syracuseStep 2570957 = 964109) (by norm_num)
theorem B4946645 : Blo 1713057 4946645 := bbase (se 7 (by rfl) ⟨57968, by rfl⟩ : syracuseStep 4946645 = 115937) (by norm_num)
theorem B2570981 : Blo 1713057 2570981 := bbase (se 4 (by rfl) ⟨241029, by rfl⟩ : syracuseStep 2570981 = 482059) (by norm_num)
theorem B2571005 : Blo 1713057 2571005 := bbase (se 3 (by rfl) ⟨482063, by rfl⟩ : syracuseStep 2571005 = 964127) (by norm_num)
theorem B2169605 : Blo 1713057 2169605 := bbase (se 4 (by rfl) ⟨203400, by rfl⟩ : syracuseStep 2169605 = 406801) (by norm_num)
theorem B3857165 : Blo 1713057 3857165 := bbase (se 3 (by rfl) ⟨723218, by rfl⟩ : syracuseStep 3857165 = 1446437) (by norm_num)
theorem B2571029 : Blo 1713057 2571029 := bbase (se 6 (by rfl) ⟨60258, by rfl⟩ : syracuseStep 2571029 = 120517) (by norm_num)
theorem B2571053 : Blo 1713057 2571053 := bbase (se 3 (by rfl) ⟨482072, by rfl⟩ : syracuseStep 2571053 = 964145) (by norm_num)
theorem B2169661 : Blo 1713057 2169661 := bbase (se 3 (by rfl) ⟨406811, by rfl⟩ : syracuseStep 2169661 = 813623) (by norm_num)
theorem B2571077 : Blo 1713057 2571077 := bbase (se 4 (by rfl) ⟨241038, by rfl⟩ : syracuseStep 2571077 = 482077) (by norm_num)
theorem B3857237 : Blo 1713057 3857237 := bbase (se 9 (by rfl) ⟨11300, by rfl⟩ : syracuseStep 3857237 = 22601) (by norm_num)
theorem B2571101 : Blo 1713057 2571101 := bbase (se 3 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 2571101 = 964163) (by norm_num)
theorem B5782373 : Blo 1713057 5782373 := bbase (se 4 (by rfl) ⟨542097, by rfl⟩ : syracuseStep 5782373 = 1084195) (by norm_num)
theorem B2571125 : Blo 1713057 2571125 := bbase (se 5 (by rfl) ⟨120521, by rfl⟩ : syracuseStep 2571125 = 241043) (by norm_num)
theorem B2571149 : Blo 1713057 2571149 := bbase (se 3 (by rfl) ⟨482090, by rfl⟩ : syracuseStep 2571149 = 964181) (by norm_num)
theorem B4119437 : Blo 1713057 4119437 := bbase (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) (by norm_num)
theorem B8682389 : Blo 1713057 8682389 := bbase (se 6 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 8682389 = 406987) (by norm_num)
theorem B3857309 : Blo 1713057 3857309 := bbase (se 3 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 3857309 = 1446491) (by norm_num)
theorem B2169757 : Blo 1713057 2169757 := bbase (se 3 (by rfl) ⟨406829, by rfl⟩ : syracuseStep 2169757 = 813659) (by norm_num)
theorem B2571173 : Blo 1713057 2571173 := bbase (se 4 (by rfl) ⟨241047, by rfl⟩ : syracuseStep 2571173 = 482095) (by norm_num)
theorem B2571197 : Blo 1713057 2571197 := bbase (se 3 (by rfl) ⟨482099, by rfl⟩ : syracuseStep 2571197 = 964199) (by norm_num)
theorem B2571221 : Blo 1713057 2571221 := bbase (se 7 (by rfl) ⟨30131, by rfl⟩ : syracuseStep 2571221 = 60263) (by norm_num)
theorem B3857381 : Blo 1713057 3857381 := bbase (se 4 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 3857381 = 723259) (by norm_num)
theorem B2571245 : Blo 1713057 2571245 := bbase (se 3 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 2571245 = 964217) (by norm_num)
theorem B2571269 : Blo 1713057 2571269 := bbase (se 4 (by rfl) ⟨241056, by rfl⟩ : syracuseStep 2571269 = 482113) (by norm_num)
theorem B4340749 : Blo 1713057 4340749 := bbase (se 3 (by rfl) ⟨813890, by rfl⟩ : syracuseStep 4340749 = 1627781) (by norm_num)
theorem B9763861 : Blo 1713057 9763861 := bbase (se 6 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 9763861 = 457681) (by norm_num)
theorem B2571293 : Blo 1713057 2571293 := bbase (se 3 (by rfl) ⟨482117, by rfl⟩ : syracuseStep 2571293 = 964235) (by norm_num)
theorem B3857453 : Blo 1713057 3857453 := bbase (se 3 (by rfl) ⟨723272, by rfl⟩ : syracuseStep 3857453 = 1446545) (by norm_num)
theorem B2571317 : Blo 1713057 2571317 := bbase (se 5 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 2571317 = 241061) (by norm_num)
theorem B2169929 : Blo 1713057 2169929 := bbase (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) (by norm_num)
theorem B2890829 : Blo 1713057 2890829 := bbase (se 3 (by rfl) ⟨542030, by rfl⟩ : syracuseStep 2890829 = 1084061) (by norm_num)
theorem B2571341 : Blo 1713057 2571341 := bbase (se 3 (by rfl) ⟨482126, by rfl⟩ : syracuseStep 2571341 = 964253) (by norm_num)
theorem B2571365 : Blo 1713057 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B3857525 : Blo 1713057 3857525 := bbase (se 5 (by rfl) ⟨180821, by rfl⟩ : syracuseStep 3857525 = 361643) (by norm_num)
theorem B2571389 : Blo 1713057 2571389 := bbase (se 3 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 2571389 = 964271) (by norm_num)
theorem B4340861 : Blo 1713057 4340861 := bbase (se 3 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 4340861 = 1627823) (by norm_num)
theorem B2169985 : Blo 1713057 2169985 := bbase (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) (by norm_num)
theorem B2571413 : Blo 1713057 2571413 := bbase (se 6 (by rfl) ⟨60267, by rfl⟩ : syracuseStep 2571413 = 120535) (by norm_num)
theorem B2571437 : Blo 1713057 2571437 := bbase (se 3 (by rfl) ⟨482144, by rfl⟩ : syracuseStep 2571437 = 964289) (by norm_num)
theorem B2440373 : Blo 1713057 2440373 := bbase (se 5 (by rfl) ⟨114392, by rfl⟩ : syracuseStep 2440373 = 228785) (by norm_num)
theorem B3857597 : Blo 1713057 3857597 := bbase (se 3 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 3857597 = 1446599) (by norm_num)
theorem B2571461 : Blo 1713057 2571461 := bbase (se 4 (by rfl) ⟨241074, by rfl⟩ : syracuseStep 2571461 = 482149) (by norm_num)
theorem B2890957 : Blo 1713057 2890957 := bbase (se 3 (by rfl) ⟨542054, by rfl⟩ : syracuseStep 2890957 = 1084109) (by norm_num)
theorem B2571485 : Blo 1713057 2571485 := bbase (se 3 (by rfl) ⟨482153, by rfl⟩ : syracuseStep 2571485 = 964307) (by norm_num)
theorem B2170081 : Blo 1713057 2170081 := bbase (se 2 (by rfl) ⟨813780, by rfl⟩ : syracuseStep 2170081 = 1627561) (by norm_num)
theorem B2571509 : Blo 1713057 2571509 := bbase (se 5 (by rfl) ⟨120539, by rfl⟩ : syracuseStep 2571509 = 241079) (by norm_num)
theorem B3857669 : Blo 1713057 3857669 := bbase (se 4 (by rfl) ⟨361656, by rfl⟩ : syracuseStep 3857669 = 723313) (by norm_num)
theorem B2571533 : Blo 1713057 2571533 := bbase (se 3 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 2571533 = 964325) (by norm_num)
theorem B5782805 : Blo 1713057 5782805 := bbase (se 6 (by rfl) ⟨135534, by rfl⟩ : syracuseStep 5782805 = 271069) (by norm_num)
theorem B5209381 : Blo 1713057 5209381 := bbase (se 4 (by rfl) ⟨488379, by rfl⟩ : syracuseStep 5209381 = 976759) (by norm_num)
theorem B2891045 : Blo 1713057 2891045 := bbase (se 4 (by rfl) ⟨271035, by rfl⟩ : syracuseStep 2891045 = 542071) (by norm_num)
theorem B2571557 : Blo 1713057 2571557 := bbase (se 4 (by rfl) ⟨241083, by rfl⟩ : syracuseStep 2571557 = 482167) (by norm_num)
theorem B8674613 : Blo 1713057 8674613 := bbase (se 5 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 8674613 = 813245) (by norm_num)
theorem B14646581 : Blo 1713057 14646581 := bbase (se 5 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 14646581 = 1373117) (by norm_num)
theorem B2571581 : Blo 1713057 2571581 := bbase (se 3 (by rfl) ⟨482171, by rfl⟩ : syracuseStep 2571581 = 964343) (by norm_num)
theorem B4341053 : Blo 1713057 4341053 := bbase (se 3 (by rfl) ⟨813947, by rfl⟩ : syracuseStep 4341053 = 1627895) (by norm_num)
theorem B7929157 : Blo 1713057 7929157 := bbase (se 4 (by rfl) ⟨743358, by rfl⟩ : syracuseStep 7929157 = 1486717) (by norm_num)
theorem B3857741 : Blo 1713057 3857741 := bbase (se 3 (by rfl) ⟨723326, by rfl⟩ : syracuseStep 3857741 = 1446653) (by norm_num)
theorem B3661141 : Blo 1713057 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B2571605 : Blo 1713057 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B2088289 : Blo 1713057 2088289 := bbase (se 2 (by rfl) ⟨783108, by rfl⟩ : syracuseStep 2088289 = 1566217) (by norm_num)
theorem B2571629 : Blo 1713057 2571629 := bbase (se 3 (by rfl) ⟨482180, by rfl⟩ : syracuseStep 2571629 = 964361) (by norm_num)
theorem B3087733 : Blo 1713057 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B2571653 : Blo 1713057 2571653 := bbase (se 4 (by rfl) ⟨241092, by rfl⟩ : syracuseStep 2571653 = 482185) (by norm_num)
theorem B2170253 : Blo 1713057 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B3857813 : Blo 1713057 3857813 := bbase (se 6 (by rfl) ⟨90417, by rfl⟩ : syracuseStep 3857813 = 180835) (by norm_num)
theorem B2571677 : Blo 1713057 2571677 := bbase (se 3 (by rfl) ⟨482189, by rfl⟩ : syracuseStep 2571677 = 964379) (by norm_num)
theorem B2891173 : Blo 1713057 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B2932133 : Blo 1713057 2932133 := bbase (se 4 (by rfl) ⟨274887, by rfl⟩ : syracuseStep 2932133 = 549775) (by norm_num)
theorem B4881829 : Blo 1713057 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B2571701 : Blo 1713057 2571701 := bbase (se 5 (by rfl) ⟨120548, by rfl⟩ : syracuseStep 2571701 = 241097) (by norm_num)
theorem B3087805 : Blo 1713057 3087805 := bbase (se 3 (by rfl) ⟨578963, by rfl⟩ : syracuseStep 3087805 = 1157927) (by norm_num)
theorem B2170309 : Blo 1713057 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B2571725 : Blo 1713057 2571725 := bbase (se 3 (by rfl) ⟨482198, by rfl⟩ : syracuseStep 2571725 = 964397) (by norm_num)
theorem B3857885 : Blo 1713057 3857885 := bbase (se 3 (by rfl) ⟨723353, by rfl⟩ : syracuseStep 3857885 = 1446707) (by norm_num)
theorem B2317789 : Blo 1713057 2317789 := bbase (se 3 (by rfl) ⟨434585, by rfl⟩ : syracuseStep 2317789 = 869171) (by norm_num)
theorem B2571749 : Blo 1713057 2571749 := bbase (se 4 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 2571749 = 482203) (by norm_num)
theorem B2891261 : Blo 1713057 2891261 := bbase (se 3 (by rfl) ⟨542111, by rfl⟩ : syracuseStep 2891261 = 1084223) (by norm_num)
theorem B2571773 : Blo 1713057 2571773 := bbase (se 3 (by rfl) ⟨482207, by rfl⟩ : syracuseStep 2571773 = 964415) (by norm_num)
theorem B2571797 : Blo 1713057 2571797 := bbase (se 6 (by rfl) ⟨60276, by rfl⟩ : syracuseStep 2571797 = 120553) (by norm_num)
theorem B8797733 : Blo 1713057 8797733 := bbase (se 4 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 8797733 = 1649575) (by norm_num)
theorem B3857957 : Blo 1713057 3857957 := bbase (se 4 (by rfl) ⟨361683, by rfl⟩ : syracuseStep 3857957 = 723367) (by norm_num)
theorem B2170405 : Blo 1713057 2170405 := bbase (se 4 (by rfl) ⟨203475, by rfl⟩ : syracuseStep 2170405 = 406951) (by norm_num)
theorem B2571821 : Blo 1713057 2571821 := bbase (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) (by norm_num)
theorem B2571845 : Blo 1713057 2571845 := bbase (se 4 (by rfl) ⟨241110, by rfl⟩ : syracuseStep 2571845 = 482221) (by norm_num)
theorem B2571869 : Blo 1713057 2571869 := bbase (se 3 (by rfl) ⟨482225, by rfl⟩ : syracuseStep 2571869 = 964451) (by norm_num)
theorem B3858029 : Blo 1713057 3858029 := bbase (se 3 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 3858029 = 1446761) (by norm_num)
theorem B2571893 : Blo 1713057 2571893 := bbase (se 5 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 2571893 = 241115) (by norm_num)
theorem B2891389 : Blo 1713057 2891389 := bbase (se 3 (by rfl) ⟨542135, by rfl⟩ : syracuseStep 2891389 = 1084271) (by norm_num)
theorem B7814789 : Blo 1713057 7814789 := bbase (se 4 (by rfl) ⟨732636, by rfl⟩ : syracuseStep 7814789 = 1465273) (by norm_num)
theorem B2571917 : Blo 1713057 2571917 := bbase (se 3 (by rfl) ⟨482234, by rfl⟩ : syracuseStep 2571917 = 964469) (by norm_num)
theorem B3088037 : Blo 1713057 3088037 := bbase (se 4 (by rfl) ⟨289503, by rfl⟩ : syracuseStep 3088037 = 579007) (by norm_num)
theorem B2571941 : Blo 1713057 2571941 := bbase (se 4 (by rfl) ⟨241119, by rfl⟩ : syracuseStep 2571941 = 482239) (by norm_num)
theorem B3858101 : Blo 1713057 3858101 := bbase (se 5 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 3858101 = 361697) (by norm_num)
theorem B2571965 : Blo 1713057 2571965 := bbase (se 3 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 2571965 = 964487) (by norm_num)
theorem B5783237 : Blo 1713057 5783237 := bbase (se 4 (by rfl) ⟨542178, by rfl⟩ : syracuseStep 5783237 = 1084357) (by norm_num)
theorem B3661517 : Blo 1713057 3661517 := bbase (se 3 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 3661517 = 1373069) (by norm_num)
theorem B2170577 : Blo 1713057 2170577 := bbase (se 2 (by rfl) ⟨813966, by rfl⟩ : syracuseStep 2170577 = 1627933) (by norm_num)
theorem B2891477 : Blo 1713057 2891477 := bbase (se 7 (by rfl) ⟨33884, by rfl⟩ : syracuseStep 2891477 = 67769) (by norm_num)
theorem B2571989 : Blo 1713057 2571989 := bbase (se 7 (by rfl) ⟨30140, by rfl⟩ : syracuseStep 2571989 = 60281) (by norm_num)
theorem B2572013 : Blo 1713057 2572013 := bbase (se 3 (by rfl) ⟨482252, by rfl⟩ : syracuseStep 2572013 = 964505) (by norm_num)
theorem B3858173 : Blo 1713057 3858173 := bbase (se 3 (by rfl) ⟨723407, by rfl⟩ : syracuseStep 3858173 = 1446815) (by norm_num)
theorem B2572037 : Blo 1713057 2572037 := bbase (se 4 (by rfl) ⟨241128, by rfl⟩ : syracuseStep 2572037 = 482257) (by norm_num)
theorem B6176533 : Blo 1713057 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B17841941 : Blo 1713057 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B2572061 : Blo 1713057 2572061 := bbase (se 3 (by rfl) ⟨482261, by rfl⟩ : syracuseStep 2572061 = 964523) (by norm_num)
theorem B2572085 : Blo 1713057 2572085 := bbase (se 5 (by rfl) ⟨120566, by rfl⟩ : syracuseStep 2572085 = 241133) (by norm_num)
theorem B3858245 : Blo 1713057 3858245 := bbase (se 4 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 3858245 = 723421) (by norm_num)
theorem B2572109 : Blo 1713057 2572109 := bbase (se 3 (by rfl) ⟨482270, by rfl⟩ : syracuseStep 2572109 = 964541) (by norm_num)
theorem B2891605 : Blo 1713057 2891605 := bbase (se 9 (by rfl) ⟨8471, by rfl⟩ : syracuseStep 2891605 = 16943) (by norm_num)
theorem B2572133 : Blo 1713057 2572133 := bbase (se 4 (by rfl) ⟨241137, by rfl⟩ : syracuseStep 2572133 = 482275) (by norm_num)
theorem B3964781 : Blo 1713057 3964781 := bbase (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) (by norm_num)
theorem B2572157 : Blo 1713057 2572157 := bbase (se 3 (by rfl) ⟨482279, by rfl⟩ : syracuseStep 2572157 = 964559) (by norm_num)
theorem B3858317 : Blo 1713057 3858317 := bbase (se 3 (by rfl) ⟨723434, by rfl⟩ : syracuseStep 3858317 = 1446869) (by norm_num)
theorem B2572181 : Blo 1713057 2572181 := bbase (se 6 (by rfl) ⟨60285, by rfl⟩ : syracuseStep 2572181 = 120571) (by norm_num)
theorem B2441125 : Blo 1713057 2441125 := bbase (se 4 (by rfl) ⟨228855, by rfl⟩ : syracuseStep 2441125 = 457711) (by norm_num)
theorem B2891693 : Blo 1713057 2891693 := bbase (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) (by norm_num)
theorem B2572205 : Blo 1713057 2572205 := bbase (se 3 (by rfl) ⟨482288, by rfl⟩ : syracuseStep 2572205 = 964577) (by norm_num)
theorem B2572229 : Blo 1713057 2572229 := bbase (se 4 (by rfl) ⟨241146, by rfl⟩ : syracuseStep 2572229 = 482293) (by norm_num)
theorem B3858389 : Blo 1713057 3858389 := bbase (se 7 (by rfl) ⟨45215, by rfl⟩ : syracuseStep 3858389 = 90431) (by norm_num)
theorem B2572253 : Blo 1713057 2572253 := bbase (se 3 (by rfl) ⟨482297, by rfl⟩ : syracuseStep 2572253 = 964595) (by norm_num)
theorem B2572277 : Blo 1713057 2572277 := bbase (se 5 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 2572277 = 241151) (by norm_num)
theorem B3252221 : Blo 1713057 3252221 := bbase (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) (by norm_num)
theorem B2572289 : Blo 1713057 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B2572307 : Blo 1713057 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B2572337 : Blo 1713057 2572337 := bstep (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) B1929253
theorem B2572355 : Blo 1713057 2572355 := bstep (se 1 (by rfl) ⟨1929266, by rfl⟩ : syracuseStep 2572355 = 3858533) B3858533
theorem B3252305 : Blo 1713057 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B2605153 : Blo 1713057 2605153 := bstep (se 2 (by rfl) ⟨976932, by rfl⟩ : syracuseStep 2605153 = 1953865) B1953865
theorem B2572385 : Blo 1713057 2572385 := bstep (se 2 (by rfl) ⟨964644, by rfl⟩ : syracuseStep 2572385 = 1929289) B1929289
theorem B2891875 : Blo 1713057 2891875 := bstep (se 1 (by rfl) ⟨2168906, by rfl⟩ : syracuseStep 2891875 = 4337813) B4337813
theorem B2572403 : Blo 1713057 2572403 := bstep (se 1 (by rfl) ⟨1929302, by rfl⟩ : syracuseStep 2572403 = 3858605) B3858605
theorem B2572433 : Blo 1713057 2572433 := bstep (se 2 (by rfl) ⟨964662, by rfl⟩ : syracuseStep 2572433 = 1929325) B1929325
theorem B4399267 : Blo 1713057 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B2572451 : Blo 1713057 2572451 := bstep (se 1 (by rfl) ⟨1929338, by rfl⟩ : syracuseStep 2572451 = 3858677) B3858677
theorem B19529909 : Blo 1713057 19529909 := bstep (se 5 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 19529909 = 1830929) B1830929
theorem B2572481 : Blo 1713057 2572481 := bstep (se 2 (by rfl) ⟨964680, by rfl⟩ : syracuseStep 2572481 = 1929361) B1929361
theorem B7323853 : Blo 1713057 7323853 := bstep (se 3 (by rfl) ⟨1373222, by rfl⟩ : syracuseStep 7323853 = 2746445) B2746445
theorem B3858641 : Blo 1713057 3858641 := bstep (se 2 (by rfl) ⟨1446990, by rfl⟩ : syracuseStep 3858641 = 2893981) B2893981
theorem B2572499 : Blo 1713057 2572499 := bstep (se 1 (by rfl) ⟨1929374, by rfl⟩ : syracuseStep 2572499 = 3858749) B3858749
theorem B3858659 : Blo 1713057 3858659 := bstep (se 1 (by rfl) ⟨2893994, by rfl⟩ : syracuseStep 3858659 = 5787989) B5787989
theorem B2892017 : Blo 1713057 2892017 := bstep (se 2 (by rfl) ⟨1084506, by rfl⟩ : syracuseStep 2892017 = 2169013) B2169013
theorem B2572529 : Blo 1713057 2572529 := bstep (se 2 (by rfl) ⟨964698, by rfl⟩ : syracuseStep 2572529 = 1929397) B1929397
theorem B1736947 : Blo 1713057 1736947 := bstep (se 1 (by rfl) ⟨1302710, by rfl⟩ : syracuseStep 1736947 = 2605421) B2605421
theorem B2572547 : Blo 1713057 2572547 := bstep (se 1 (by rfl) ⟨1929410, by rfl⟩ : syracuseStep 2572547 = 3858821) B3858821
theorem B2572577 : Blo 1713057 2572577 := bstep (se 2 (by rfl) ⟨964716, by rfl⟩ : syracuseStep 2572577 = 1929433) B1929433
theorem B5783885 : Blo 1713057 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B2892145 : Blo 1713057 2892145 := bstep (se 2 (by rfl) ⟨1084554, by rfl⟩ : syracuseStep 2892145 = 2169109) B2169109
theorem B5783939 : Blo 1713057 5783939 := bstep (se 1 (by rfl) ⟨4337954, by rfl⟩ : syracuseStep 5783939 = 8675909) B8675909
theorem B2892179 : Blo 1713057 2892179 := bstep (se 1 (by rfl) ⟨2169134, by rfl⟩ : syracuseStep 2892179 = 4338269) B4338269
theorem B8675747 : Blo 1713057 8675747 := bstep (se 1 (by rfl) ⟨6506810, by rfl⟩ : syracuseStep 8675747 = 13013621) B13013621
theorem B3252707 : Blo 1713057 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B2892307 : Blo 1713057 2892307 := bstep (se 1 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 2892307 = 4338461) B4338461
theorem B7324195 : Blo 1713057 7324195 := bstep (se 1 (by rfl) ⟨5493146, by rfl⟩ : syracuseStep 7324195 = 10986293) B10986293
theorem B4882979 : Blo 1713057 4882979 := bstep (se 1 (by rfl) ⟨3662234, by rfl⟩ : syracuseStep 4882979 = 7324469) B7324469
theorem B3662371 : Blo 1713057 3662371 := bstep (se 1 (by rfl) ⟨2746778, by rfl⟩ : syracuseStep 3662371 = 5493557) B5493557
theorem B4948589 : Blo 1713057 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B5784209 : Blo 1713057 5784209 := bstep (se 2 (by rfl) ⟨2169078, by rfl⟩ : syracuseStep 5784209 = 4338157) B4338157
theorem B2892449 : Blo 1713057 2892449 := bstep (se 2 (by rfl) ⟨1084668, by rfl⟩ : syracuseStep 2892449 = 2169337) B2169337
theorem B5489329 : Blo 1713057 5489329 := bstep (se 2 (by rfl) ⟨2058498, by rfl⟩ : syracuseStep 5489329 = 4116997) B4116997
theorem B2933425 : Blo 1713057 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B6177485 : Blo 1713057 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B11723491 : Blo 1713057 11723491 := bstep (se 1 (by rfl) ⟨8792618, by rfl⟩ : syracuseStep 11723491 = 17585237) B17585237
theorem B2745107 : Blo 1713057 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B2892577 : Blo 1713057 2892577 := bstep (se 2 (by rfl) ⟨1084716, by rfl⟩ : syracuseStep 2892577 = 2169433) B2169433
theorem B2892611 : Blo 1713057 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B13009733 : Blo 1713057 13009733 := bstep (se 4 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 13009733 = 2439325) B2439325
theorem B5489507 : Blo 1713057 5489507 := bstep (se 1 (by rfl) ⟨4117130, by rfl⟩ : syracuseStep 5489507 = 8234261) B8234261
theorem B3130211 : Blo 1713057 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B1713059 : Blo 1713057 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1713075 : Blo 1713057 1713075 := bstep (se 1 (by rfl) ⟨1284806, by rfl⟩ : syracuseStep 1713075 = 2569613) B2569613
theorem B1713091 : Blo 1713057 1713091 := bstep (se 1 (by rfl) ⟨1284818, by rfl⟩ : syracuseStep 1713091 = 2569637) B2569637
theorem B2892739 : Blo 1713057 2892739 := bstep (se 1 (by rfl) ⟨2169554, by rfl⟩ : syracuseStep 2892739 = 4339109) B4339109
theorem B1713107 : Blo 1713057 1713107 := bstep (se 1 (by rfl) ⟨1284830, by rfl⟩ : syracuseStep 1713107 = 2569661) B2569661
theorem B1713123 : Blo 1713057 1713123 := bstep (se 1 (by rfl) ⟨1284842, by rfl⟩ : syracuseStep 1713123 = 2569685) B2569685
theorem B3662833 : Blo 1713057 3662833 := bstep (se 2 (by rfl) ⟨1373562, by rfl⟩ : syracuseStep 3662833 = 2747125) B2747125
theorem B1713139 : Blo 1713057 1713139 := bstep (se 1 (by rfl) ⟨1284854, by rfl⟩ : syracuseStep 1713139 = 2569709) B2569709
theorem B1713155 : Blo 1713057 1713155 := bstep (se 1 (by rfl) ⟨1284866, by rfl⟩ : syracuseStep 1713155 = 2569733) B2569733
theorem B1713171 : Blo 1713057 1713171 := bstep (se 1 (by rfl) ⟨1284878, by rfl⟩ : syracuseStep 1713171 = 2569757) B2569757
theorem B1713187 : Blo 1713057 1713187 := bstep (se 1 (by rfl) ⟨1284890, by rfl⟩ : syracuseStep 1713187 = 2569781) B2569781
theorem B1713203 : Blo 1713057 1713203 := bstep (se 1 (by rfl) ⟨1284902, by rfl⟩ : syracuseStep 1713203 = 2569805) B2569805
theorem B1713219 : Blo 1713057 1713219 := bstep (se 1 (by rfl) ⟨1284914, by rfl⟩ : syracuseStep 1713219 = 2569829) B2569829
theorem B2892881 : Blo 1713057 2892881 := bstep (se 2 (by rfl) ⟨1084830, by rfl⟩ : syracuseStep 2892881 = 2169661) B2169661
theorem B5866577 : Blo 1713057 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B1713235 : Blo 1713057 1713235 := bstep (se 1 (by rfl) ⟨1284926, by rfl⟩ : syracuseStep 1713235 = 2569853) B2569853
theorem B1713251 : Blo 1713057 1713251 := bstep (se 1 (by rfl) ⟨1284938, by rfl⟩ : syracuseStep 1713251 = 2569877) B2569877
theorem B1713267 : Blo 1713057 1713267 := bstep (se 1 (by rfl) ⟨1284950, by rfl⟩ : syracuseStep 1713267 = 2569901) B2569901
theorem B1713283 : Blo 1713057 1713283 := bstep (se 1 (by rfl) ⟨1284962, by rfl⟩ : syracuseStep 1713283 = 2569925) B2569925
theorem B1713299 : Blo 1713057 1713299 := bstep (se 1 (by rfl) ⟨1284974, by rfl⟩ : syracuseStep 1713299 = 2569949) B2569949
theorem B1713315 : Blo 1713057 1713315 := bstep (se 1 (by rfl) ⟨1284986, by rfl⟩ : syracuseStep 1713315 = 2569973) B2569973
theorem B5784749 : Blo 1713057 5784749 := bstep (se 3 (by rfl) ⟨1084640, by rfl⟩ : syracuseStep 5784749 = 2169281) B2169281
theorem B1713331 : Blo 1713057 1713331 := bstep (se 1 (by rfl) ⟨1284998, by rfl⟩ : syracuseStep 1713331 = 2569997) B2569997
theorem B1713347 : Blo 1713057 1713347 := bstep (se 1 (by rfl) ⟨1285010, by rfl⟩ : syracuseStep 1713347 = 2570021) B2570021
theorem B8676557 : Blo 1713057 8676557 := bstep (se 3 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 8676557 = 3253709) B3253709
theorem B2893009 : Blo 1713057 2893009 := bstep (se 2 (by rfl) ⟨1084878, by rfl⟩ : syracuseStep 2893009 = 2169757) B2169757
theorem B1713363 : Blo 1713057 1713363 := bstep (se 1 (by rfl) ⟨1285022, by rfl⟩ : syracuseStep 1713363 = 2570045) B2570045
theorem B1713379 : Blo 1713057 1713379 := bstep (se 1 (by rfl) ⟨1285034, by rfl⟩ : syracuseStep 1713379 = 2570069) B2570069
theorem B5784803 : Blo 1713057 5784803 := bstep (se 1 (by rfl) ⟨4338602, by rfl⟩ : syracuseStep 5784803 = 8677205) B8677205
theorem B7628017 : Blo 1713057 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B1713395 : Blo 1713057 1713395 := bstep (se 1 (by rfl) ⟨1285046, by rfl⟩ : syracuseStep 1713395 = 2570093) B2570093
theorem B2893043 : Blo 1713057 2893043 := bstep (se 1 (by rfl) ⟨2169782, by rfl⟩ : syracuseStep 2893043 = 4339565) B4339565
theorem B1713411 : Blo 1713057 1713411 := bstep (se 1 (by rfl) ⟨1285058, by rfl⟩ : syracuseStep 1713411 = 2570117) B2570117
theorem B1713427 : Blo 1713057 1713427 := bstep (se 1 (by rfl) ⟨1285070, by rfl⟩ : syracuseStep 1713427 = 2570141) B2570141
theorem B1713443 : Blo 1713057 1713443 := bstep (se 1 (by rfl) ⟨1285082, by rfl⟩ : syracuseStep 1713443 = 2570165) B2570165
theorem B1713459 : Blo 1713057 1713459 := bstep (se 1 (by rfl) ⟨1285094, by rfl⟩ : syracuseStep 1713459 = 2570189) B2570189
theorem B1713475 : Blo 1713057 1713475 := bstep (se 1 (by rfl) ⟨1285106, by rfl⟩ : syracuseStep 1713475 = 2570213) B2570213
theorem B9758029 : Blo 1713057 9758029 := bstep (se 3 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 9758029 = 3659261) B3659261
theorem B1713491 : Blo 1713057 1713491 := bstep (se 1 (by rfl) ⟨1285118, by rfl⟩ : syracuseStep 1713491 = 2570237) B2570237
theorem B1713507 : Blo 1713057 1713507 := bstep (se 1 (by rfl) ⟨1285130, by rfl⟩ : syracuseStep 1713507 = 2570261) B2570261
theorem B3253603 : Blo 1713057 3253603 := bstep (se 1 (by rfl) ⟨2440202, by rfl⟩ : syracuseStep 3253603 = 4880405) B4880405
theorem B13018481 : Blo 1713057 13018481 := bstep (se 2 (by rfl) ⟨4881930, by rfl⟩ : syracuseStep 13018481 = 9763861) B9763861
theorem B1713523 : Blo 1713057 1713523 := bstep (se 1 (by rfl) ⟨1285142, by rfl⟩ : syracuseStep 1713523 = 2570285) B2570285
theorem B2893171 : Blo 1713057 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B1713539 : Blo 1713057 1713539 := bstep (se 1 (by rfl) ⟨1285154, by rfl⟩ : syracuseStep 1713539 = 2570309) B2570309
theorem B9766277 : Blo 1713057 9766277 := bstep (se 4 (by rfl) ⟨915588, by rfl⟩ : syracuseStep 9766277 = 1831177) B1831177
theorem B1713555 : Blo 1713057 1713555 := bstep (se 1 (by rfl) ⟨1285166, by rfl⟩ : syracuseStep 1713555 = 2570333) B2570333
theorem B1713571 : Blo 1713057 1713571 := bstep (se 1 (by rfl) ⟨1285178, by rfl⟩ : syracuseStep 1713571 = 2570357) B2570357
theorem B1713587 : Blo 1713057 1713587 := bstep (se 1 (by rfl) ⟨1285190, by rfl⟩ : syracuseStep 1713587 = 2570381) B2570381
theorem B1713603 : Blo 1713057 1713603 := bstep (se 1 (by rfl) ⟨1285202, by rfl⟩ : syracuseStep 1713603 = 2570405) B2570405
theorem B1713619 : Blo 1713057 1713619 := bstep (se 1 (by rfl) ⟨1285214, by rfl⟩ : syracuseStep 1713619 = 2570429) B2570429
theorem B1713635 : Blo 1713057 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B5785073 : Blo 1713057 5785073 := bstep (se 2 (by rfl) ⟨2169402, by rfl⟩ : syracuseStep 5785073 = 4338805) B4338805
theorem B1713651 : Blo 1713057 1713651 := bstep (se 1 (by rfl) ⟨1285238, by rfl⟩ : syracuseStep 1713651 = 2570477) B2570477
theorem B2893313 : Blo 1713057 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B1713667 : Blo 1713057 1713667 := bstep (se 1 (by rfl) ⟨1285250, by rfl⟩ : syracuseStep 1713667 = 2570501) B2570501
theorem B3253763 : Blo 1713057 3253763 := bstep (se 1 (by rfl) ⟨2440322, by rfl⟩ : syracuseStep 3253763 = 4880645) B4880645
theorem B1713683 : Blo 1713057 1713683 := bstep (se 1 (by rfl) ⟨1285262, by rfl⟩ : syracuseStep 1713683 = 2570525) B2570525
theorem B1713699 : Blo 1713057 1713699 := bstep (se 1 (by rfl) ⟨1285274, by rfl⟩ : syracuseStep 1713699 = 2570549) B2570549
theorem B1713715 : Blo 1713057 1713715 := bstep (se 1 (by rfl) ⟨1285286, by rfl⟩ : syracuseStep 1713715 = 2570573) B2570573
theorem B1713731 : Blo 1713057 1713731 := bstep (se 1 (by rfl) ⟨1285298, by rfl⟩ : syracuseStep 1713731 = 2570597) B2570597
theorem B1713747 : Blo 1713057 1713747 := bstep (se 1 (by rfl) ⟨1285310, by rfl⟩ : syracuseStep 1713747 = 2570621) B2570621
theorem B1713763 : Blo 1713057 1713763 := bstep (se 1 (by rfl) ⟨1285322, by rfl⟩ : syracuseStep 1713763 = 2570645) B2570645
theorem B1713779 : Blo 1713057 1713779 := bstep (se 1 (by rfl) ⟨1285334, by rfl⟩ : syracuseStep 1713779 = 2570669) B2570669
theorem B2893441 : Blo 1713057 2893441 := bstep (se 2 (by rfl) ⟨1085040, by rfl⟩ : syracuseStep 2893441 = 2170081) B2170081
theorem B1713795 : Blo 1713057 1713795 := bstep (se 1 (by rfl) ⟨1285346, by rfl⟩ : syracuseStep 1713795 = 2570693) B2570693
theorem B1713811 : Blo 1713057 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B1713827 : Blo 1713057 1713827 := bstep (se 1 (by rfl) ⟨1285370, by rfl⟩ : syracuseStep 1713827 = 2570741) B2570741
theorem B2893475 : Blo 1713057 2893475 := bstep (se 1 (by rfl) ⟨2170106, by rfl⟩ : syracuseStep 2893475 = 4340213) B4340213
theorem B1713843 : Blo 1713057 1713843 := bstep (se 1 (by rfl) ⟨1285382, by rfl⟩ : syracuseStep 1713843 = 2570765) B2570765
theorem B1713859 : Blo 1713057 1713859 := bstep (se 1 (by rfl) ⟨1285394, by rfl⟩ : syracuseStep 1713859 = 2570789) B2570789
theorem B6506189 : Blo 1713057 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B1713875 : Blo 1713057 1713875 := bstep (se 1 (by rfl) ⟨1285406, by rfl⟩ : syracuseStep 1713875 = 2570813) B2570813
theorem B8234723 : Blo 1713057 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B1713891 : Blo 1713057 1713891 := bstep (se 1 (by rfl) ⟨1285418, by rfl⟩ : syracuseStep 1713891 = 2570837) B2570837
theorem B1713907 : Blo 1713057 1713907 := bstep (se 1 (by rfl) ⟨1285430, by rfl⟩ : syracuseStep 1713907 = 2570861) B2570861
theorem B1713923 : Blo 1713057 1713923 := bstep (se 1 (by rfl) ⟨1285442, by rfl⟩ : syracuseStep 1713923 = 2570885) B2570885
theorem B1713939 : Blo 1713057 1713939 := bstep (se 1 (by rfl) ⟨1285454, by rfl⟩ : syracuseStep 1713939 = 2570909) B2570909
theorem B1713955 : Blo 1713057 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B2893603 : Blo 1713057 2893603 := bstep (se 1 (by rfl) ⟨2170202, by rfl⟩ : syracuseStep 2893603 = 4340405) B4340405
theorem B6178609 : Blo 1713057 6178609 := bstep (se 2 (by rfl) ⟨2316978, by rfl⟩ : syracuseStep 6178609 = 4633957) B4633957
theorem B1713971 : Blo 1713057 1713971 := bstep (se 1 (by rfl) ⟨1285478, by rfl⟩ : syracuseStep 1713971 = 2570957) B2570957
theorem B1713987 : Blo 1713057 1713987 := bstep (se 1 (by rfl) ⟨1285490, by rfl⟩ : syracuseStep 1713987 = 2570981) B2570981
theorem B1714003 : Blo 1713057 1714003 := bstep (se 1 (by rfl) ⟨1285502, by rfl⟩ : syracuseStep 1714003 = 2571005) B2571005
theorem B1714019 : Blo 1713057 1714019 := bstep (se 1 (by rfl) ⟨1285514, by rfl⟩ : syracuseStep 1714019 = 2571029) B2571029
theorem B1714035 : Blo 1713057 1714035 := bstep (se 1 (by rfl) ⟨1285526, by rfl⟩ : syracuseStep 1714035 = 2571053) B2571053
theorem B1714051 : Blo 1713057 1714051 := bstep (se 1 (by rfl) ⟨1285538, by rfl⟩ : syracuseStep 1714051 = 2571077) B2571077
theorem B10987397 : Blo 1713057 10987397 := bstep (se 4 (by rfl) ⟨1030068, by rfl⟩ : syracuseStep 10987397 = 2060137) B2060137
theorem B1714067 : Blo 1713057 1714067 := bstep (se 1 (by rfl) ⟨1285550, by rfl⟩ : syracuseStep 1714067 = 2571101) B2571101
theorem B1714083 : Blo 1713057 1714083 := bstep (se 1 (by rfl) ⟨1285562, by rfl⟩ : syracuseStep 1714083 = 2571125) B2571125
theorem B2893745 : Blo 1713057 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B1714099 : Blo 1713057 1714099 := bstep (se 1 (by rfl) ⟨1285574, by rfl⟩ : syracuseStep 1714099 = 2571149) B2571149
theorem B1714115 : Blo 1713057 1714115 := bstep (se 1 (by rfl) ⟨1285586, by rfl⟩ : syracuseStep 1714115 = 2571173) B2571173
theorem B3090385 : Blo 1713057 3090385 := bstep (se 2 (by rfl) ⟨1158894, by rfl⟩ : syracuseStep 3090385 = 2317789) B2317789
theorem B1714131 : Blo 1713057 1714131 := bstep (se 1 (by rfl) ⟨1285598, by rfl⟩ : syracuseStep 1714131 = 2571197) B2571197
theorem B1714147 : Blo 1713057 1714147 := bstep (se 1 (by rfl) ⟨1285610, by rfl⟩ : syracuseStep 1714147 = 2571221) B2571221
theorem B1714163 : Blo 1713057 1714163 := bstep (se 1 (by rfl) ⟨1285622, by rfl⟩ : syracuseStep 1714163 = 2571245) B2571245
theorem B1714179 : Blo 1713057 1714179 := bstep (se 1 (by rfl) ⟨1285634, by rfl⟩ : syracuseStep 1714179 = 2571269) B2571269
theorem B5785613 : Blo 1713057 5785613 := bstep (se 3 (by rfl) ⟨1084802, by rfl⟩ : syracuseStep 5785613 = 2169605) B2169605
theorem B1714195 : Blo 1713057 1714195 := bstep (se 1 (by rfl) ⟨1285646, by rfl⟩ : syracuseStep 1714195 = 2571293) B2571293
theorem B1714211 : Blo 1713057 1714211 := bstep (se 1 (by rfl) ⟨1285658, by rfl⟩ : syracuseStep 1714211 = 2571317) B2571317
theorem B2893873 : Blo 1713057 2893873 := bstep (se 2 (by rfl) ⟨1085202, by rfl⟩ : syracuseStep 2893873 = 2170405) B2170405
theorem B4950065 : Blo 1713057 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B1927219 : Blo 1713057 1927219 := bstep (se 1 (by rfl) ⟨1445414, by rfl⟩ : syracuseStep 1927219 = 2890829) B2890829
theorem B1714227 : Blo 1713057 1714227 := bstep (se 1 (by rfl) ⟨1285670, by rfl⟩ : syracuseStep 1714227 = 2571341) B2571341
theorem B1714243 : Blo 1713057 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B5785667 : Blo 1713057 5785667 := bstep (se 1 (by rfl) ⟨4339250, by rfl⟩ : syracuseStep 5785667 = 8678501) B8678501
theorem B1714259 : Blo 1713057 1714259 := bstep (se 1 (by rfl) ⟨1285694, by rfl⟩ : syracuseStep 1714259 = 2571389) B2571389
theorem B2893907 : Blo 1713057 2893907 := bstep (se 1 (by rfl) ⟨2170430, by rfl⟩ : syracuseStep 2893907 = 4340861) B4340861
theorem B1714275 : Blo 1713057 1714275 := bstep (se 1 (by rfl) ⟨1285706, by rfl⟩ : syracuseStep 1714275 = 2571413) B2571413
theorem B1714291 : Blo 1713057 1714291 := bstep (se 1 (by rfl) ⟨1285718, by rfl⟩ : syracuseStep 1714291 = 2571437) B2571437
theorem B1714307 : Blo 1713057 1714307 := bstep (se 1 (by rfl) ⟨1285730, by rfl⟩ : syracuseStep 1714307 = 2571461) B2571461
theorem B1714323 : Blo 1713057 1714323 := bstep (se 1 (by rfl) ⟨1285742, by rfl⟩ : syracuseStep 1714323 = 2571485) B2571485
theorem B2607265 : Blo 1713057 2607265 := bstep (se 2 (by rfl) ⟨977724, by rfl⟩ : syracuseStep 2607265 = 1955449) B1955449
theorem B1714339 : Blo 1713057 1714339 := bstep (se 1 (by rfl) ⟨1285754, by rfl⟩ : syracuseStep 1714339 = 2571509) B2571509
theorem B1714355 : Blo 1713057 1714355 := bstep (se 1 (by rfl) ⟨1285766, by rfl⟩ : syracuseStep 1714355 = 2571533) B2571533
theorem B2746561 : Blo 1713057 2746561 := bstep (se 2 (by rfl) ⟨1029960, by rfl⟩ : syracuseStep 2746561 = 2059921) B2059921
theorem B1927363 : Blo 1713057 1927363 := bstep (se 1 (by rfl) ⟨1445522, by rfl⟩ : syracuseStep 1927363 = 2891045) B2891045
theorem B1714371 : Blo 1713057 1714371 := bstep (se 1 (by rfl) ⟨1285778, by rfl⟩ : syracuseStep 1714371 = 2571557) B2571557
theorem B1714387 : Blo 1713057 1714387 := bstep (se 1 (by rfl) ⟨1285790, by rfl⟩ : syracuseStep 1714387 = 2571581) B2571581
theorem B2894035 : Blo 1713057 2894035 := bstep (se 1 (by rfl) ⟨2170526, by rfl⟩ : syracuseStep 2894035 = 4341053) B4341053
theorem B1714403 : Blo 1713057 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1714419 : Blo 1713057 1714419 := bstep (se 1 (by rfl) ⟨1285814, by rfl⟩ : syracuseStep 1714419 = 2571629) B2571629
theorem B1714435 : Blo 1713057 1714435 := bstep (se 1 (by rfl) ⟨1285826, by rfl⟩ : syracuseStep 1714435 = 2571653) B2571653
theorem B1714451 : Blo 1713057 1714451 := bstep (se 1 (by rfl) ⟨1285838, by rfl⟩ : syracuseStep 1714451 = 2571677) B2571677
theorem B1714467 : Blo 1713057 1714467 := bstep (se 1 (by rfl) ⟨1285850, by rfl⟩ : syracuseStep 1714467 = 2571701) B2571701
theorem B1714483 : Blo 1713057 1714483 := bstep (se 1 (by rfl) ⟨1285862, by rfl⟩ : syracuseStep 1714483 = 2571725) B2571725
theorem B1714499 : Blo 1713057 1714499 := bstep (se 1 (by rfl) ⟨1285874, by rfl⟩ : syracuseStep 1714499 = 2571749) B2571749
theorem B5785937 : Blo 1713057 5785937 := bstep (se 2 (by rfl) ⟨2169726, by rfl⟩ : syracuseStep 5785937 = 4339453) B4339453
theorem B3475793 : Blo 1713057 3475793 := bstep (se 2 (by rfl) ⟨1303422, by rfl⟩ : syracuseStep 3475793 = 2606845) B2606845
theorem B1927507 : Blo 1713057 1927507 := bstep (se 1 (by rfl) ⟨1445630, by rfl⟩ : syracuseStep 1927507 = 2891261) B2891261
theorem B1714515 : Blo 1713057 1714515 := bstep (se 1 (by rfl) ⟨1285886, by rfl⟩ : syracuseStep 1714515 = 2571773) B2571773
theorem B1714531 : Blo 1713057 1714531 := bstep (se 1 (by rfl) ⟨1285898, by rfl⟩ : syracuseStep 1714531 = 2571797) B2571797
theorem B8235377 : Blo 1713057 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B1714547 : Blo 1713057 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B1714563 : Blo 1713057 1714563 := bstep (se 1 (by rfl) ⟨1285922, by rfl⟩ : syracuseStep 1714563 = 2571845) B2571845
theorem B1714579 : Blo 1713057 1714579 := bstep (se 1 (by rfl) ⟨1285934, by rfl⟩ : syracuseStep 1714579 = 2571869) B2571869
theorem B1714595 : Blo 1713057 1714595 := bstep (se 1 (by rfl) ⟨1285946, by rfl⟩ : syracuseStep 1714595 = 2571893) B2571893
theorem B1714611 : Blo 1713057 1714611 := bstep (se 1 (by rfl) ⟨1285958, by rfl⟩ : syracuseStep 1714611 = 2571917) B2571917
theorem B2058691 : Blo 1713057 2058691 := bstep (se 1 (by rfl) ⟨1544018, by rfl⟩ : syracuseStep 2058691 = 3088037) B3088037
theorem B1714627 : Blo 1713057 1714627 := bstep (se 1 (by rfl) ⟨1285970, by rfl⟩ : syracuseStep 1714627 = 2571941) B2571941
theorem B1714643 : Blo 1713057 1714643 := bstep (se 1 (by rfl) ⟨1285982, by rfl⟩ : syracuseStep 1714643 = 2571965) B2571965
theorem B1927651 : Blo 1713057 1927651 := bstep (se 1 (by rfl) ⟨1445738, by rfl⟩ : syracuseStep 1927651 = 2891477) B2891477
theorem B1714659 : Blo 1713057 1714659 := bstep (se 1 (by rfl) ⟨1285994, by rfl⟩ : syracuseStep 1714659 = 2571989) B2571989
theorem B6506993 : Blo 1713057 6506993 := bstep (se 2 (by rfl) ⟨2440122, by rfl⟩ : syracuseStep 6506993 = 4880245) B4880245
theorem B1714675 : Blo 1713057 1714675 := bstep (se 1 (by rfl) ⟨1286006, by rfl⟩ : syracuseStep 1714675 = 2572013) B2572013
theorem B1714691 : Blo 1713057 1714691 := bstep (se 1 (by rfl) ⟨1286018, by rfl⟩ : syracuseStep 1714691 = 2572037) B2572037
theorem B1714707 : Blo 1713057 1714707 := bstep (se 1 (by rfl) ⟨1286030, by rfl⟩ : syracuseStep 1714707 = 2572061) B2572061
theorem B1714723 : Blo 1713057 1714723 := bstep (se 1 (by rfl) ⟨1286042, by rfl⟩ : syracuseStep 1714723 = 2572085) B2572085
theorem B3254833 : Blo 1713057 3254833 := bstep (se 2 (by rfl) ⟨1220562, by rfl⟩ : syracuseStep 3254833 = 2441125) B2441125
theorem B1714739 : Blo 1713057 1714739 := bstep (se 1 (by rfl) ⟨1286054, by rfl⟩ : syracuseStep 1714739 = 2572109) B2572109
theorem B1714755 : Blo 1713057 1714755 := bstep (se 1 (by rfl) ⟨1286066, by rfl⟩ : syracuseStep 1714755 = 2572133) B2572133
theorem B5491277 : Blo 1713057 5491277 := bstep (se 3 (by rfl) ⟨1029614, by rfl⟩ : syracuseStep 5491277 = 2059229) B2059229
theorem B1714771 : Blo 1713057 1714771 := bstep (se 1 (by rfl) ⟨1286078, by rfl⟩ : syracuseStep 1714771 = 2572157) B2572157
theorem B1714787 : Blo 1713057 1714787 := bstep (se 1 (by rfl) ⟨1286090, by rfl⟩ : syracuseStep 1714787 = 2572181) B2572181
theorem B1927795 : Blo 1713057 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B1714803 : Blo 1713057 1714803 := bstep (se 1 (by rfl) ⟨1286102, by rfl⟩ : syracuseStep 1714803 = 2572205) B2572205
theorem B1714819 : Blo 1713057 1714819 := bstep (se 1 (by rfl) ⟨1286114, by rfl⟩ : syracuseStep 1714819 = 2572229) B2572229
theorem B1714835 : Blo 1713057 1714835 := bstep (se 1 (by rfl) ⟨1286126, by rfl⟩ : syracuseStep 1714835 = 2572253) B2572253
theorem B1714851 : Blo 1713057 1714851 := bstep (se 1 (by rfl) ⟨1286138, by rfl⟩ : syracuseStep 1714851 = 2572277) B2572277
theorem B1714867 : Blo 1713057 1714867 := bstep (se 1 (by rfl) ⟨1286150, by rfl⟩ : syracuseStep 1714867 = 2572301) B2572301
theorem B3910339 : Blo 1713057 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B1714883 : Blo 1713057 1714883 := bstep (se 1 (by rfl) ⟨1286162, by rfl⟩ : syracuseStep 1714883 = 2572325) B2572325
theorem B1714899 : Blo 1713057 1714899 := bstep (se 1 (by rfl) ⟨1286174, by rfl⟩ : syracuseStep 1714899 = 2572349) B2572349
theorem B4336355 : Blo 1713057 4336355 := bstep (se 1 (by rfl) ⟨3252266, by rfl⟩ : syracuseStep 4336355 = 6504533) B6504533
theorem B7834339 : Blo 1713057 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B1714915 : Blo 1713057 1714915 := bstep (se 1 (by rfl) ⟨1286186, by rfl⟩ : syracuseStep 1714915 = 2572373) B2572373
theorem B1714931 : Blo 1713057 1714931 := bstep (se 1 (by rfl) ⟨1286198, by rfl⟩ : syracuseStep 1714931 = 2572397) B2572397
theorem B1927939 : Blo 1713057 1927939 := bstep (se 1 (by rfl) ⟨1445954, by rfl⟩ : syracuseStep 1927939 = 2891909) B2891909
theorem B1714947 : Blo 1713057 1714947 := bstep (se 1 (by rfl) ⟨1286210, by rfl⟩ : syracuseStep 1714947 = 2572421) B2572421
theorem B1714963 : Blo 1713057 1714963 := bstep (se 1 (by rfl) ⟨1286222, by rfl⟩ : syracuseStep 1714963 = 2572445) B2572445
theorem B1714979 : Blo 1713057 1714979 := bstep (se 1 (by rfl) ⟨1286234, by rfl⟩ : syracuseStep 1714979 = 2572469) B2572469
theorem B1714995 : Blo 1713057 1714995 := bstep (se 1 (by rfl) ⟨1286246, by rfl⟩ : syracuseStep 1714995 = 2572493) B2572493
theorem B4631363 : Blo 1713057 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B1715011 : Blo 1713057 1715011 := bstep (se 1 (by rfl) ⟨1286258, by rfl⟩ : syracuseStep 1715011 = 2572517) B2572517
theorem B1715027 : Blo 1713057 1715027 := bstep (se 1 (by rfl) ⟨1286270, by rfl⟩ : syracuseStep 1715027 = 2572541) B2572541
theorem B1715043 : Blo 1713057 1715043 := bstep (se 1 (by rfl) ⟨1286282, by rfl⟩ : syracuseStep 1715043 = 2572565) B2572565
theorem B5786477 : Blo 1713057 5786477 := bstep (se 3 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 5786477 = 2169929) B2169929
theorem B1928083 : Blo 1713057 1928083 := bstep (se 1 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 1928083 = 2892125) B2892125
theorem B5786531 : Blo 1713057 5786531 := bstep (se 1 (by rfl) ⟨4339898, by rfl⟩ : syracuseStep 5786531 = 8679797) B8679797
theorem B2059219 : Blo 1713057 2059219 := bstep (se 1 (by rfl) ⟨1544414, by rfl⟩ : syracuseStep 2059219 = 3088829) B3088829
theorem B1928227 : Blo 1713057 1928227 := bstep (se 1 (by rfl) ⟨1446170, by rfl⟩ : syracuseStep 1928227 = 2892341) B2892341
theorem B6687821 : Blo 1713057 6687821 := bstep (se 3 (by rfl) ⟨1253966, by rfl⟩ : syracuseStep 6687821 = 2507933) B2507933
theorem B9268301 : Blo 1713057 9268301 := bstep (se 3 (by rfl) ⟨1737806, by rfl⟩ : syracuseStep 9268301 = 3475613) B3475613
theorem B6507661 : Blo 1713057 6507661 := bstep (se 3 (by rfl) ⟨1220186, by rfl⟩ : syracuseStep 6507661 = 2440373) B2440373
theorem B5786801 : Blo 1713057 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B1928371 : Blo 1713057 1928371 := bstep (se 1 (by rfl) ⟨1446278, by rfl⟩ : syracuseStep 1928371 = 2892557) B2892557
theorem B6687949 : Blo 1713057 6687949 := bstep (se 3 (by rfl) ⟨1253990, by rfl⟩ : syracuseStep 6687949 = 2507981) B2507981
theorem B9760013 : Blo 1713057 9760013 := bstep (se 3 (by rfl) ⟨1830002, by rfl⟩ : syracuseStep 9760013 = 3660005) B3660005
theorem B1928515 : Blo 1713057 1928515 := bstep (se 1 (by rfl) ⟨1446386, by rfl⟩ : syracuseStep 1928515 = 2892773) B2892773
theorem B1830323 : Blo 1713057 1830323 := bstep (se 1 (by rfl) ⟨1372742, by rfl⟩ : syracuseStep 1830323 = 2745485) B2745485
theorem B1928659 : Blo 1713057 1928659 := bstep (se 1 (by rfl) ⟨1446494, by rfl⟩ : syracuseStep 1928659 = 2892989) B2892989
theorem B3255889 : Blo 1713057 3255889 := bstep (se 2 (by rfl) ⟨1220958, by rfl⟩ : syracuseStep 3255889 = 2441917) B2441917
theorem B1928803 : Blo 1713057 1928803 := bstep (se 1 (by rfl) ⟨1446602, by rfl⟩ : syracuseStep 1928803 = 2893205) B2893205
theorem B4337297 : Blo 1713057 4337297 := bstep (se 2 (by rfl) ⟨1626486, by rfl⟩ : syracuseStep 4337297 = 3252973) B3252973
theorem B8236721 : Blo 1713057 8236721 := bstep (se 2 (by rfl) ⟨3088770, by rfl⟩ : syracuseStep 8236721 = 6177541) B6177541
theorem B4337347 : Blo 1713057 4337347 := bstep (se 1 (by rfl) ⟨3253010, by rfl⟩ : syracuseStep 4337347 = 6506021) B6506021
theorem B5787341 : Blo 1713057 5787341 := bstep (se 3 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 5787341 = 2170253) B2170253
theorem B1928947 : Blo 1713057 1928947 := bstep (se 1 (by rfl) ⟨1446710, by rfl⟩ : syracuseStep 1928947 = 2893421) B2893421
theorem B5787395 : Blo 1713057 5787395 := bstep (se 1 (by rfl) ⟨4340546, by rfl⟩ : syracuseStep 5787395 = 8681093) B8681093
theorem B7819021 : Blo 1713057 7819021 := bstep (se 3 (by rfl) ⟨1466066, by rfl⟩ : syracuseStep 7819021 = 2932133) B2932133
theorem B10981169 : Blo 1713057 10981169 := bstep (se 2 (by rfl) ⟨4117938, by rfl⟩ : syracuseStep 10981169 = 8235877) B8235877
theorem B4337489 : Blo 1713057 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B1929091 : Blo 1713057 1929091 := bstep (se 1 (by rfl) ⟨1446818, by rfl⟩ : syracuseStep 1929091 = 2893637) B2893637
theorem B6508451 : Blo 1713057 6508451 := bstep (se 1 (by rfl) ⟨4881338, by rfl⟩ : syracuseStep 6508451 = 9762677) B9762677
theorem B5787665 : Blo 1713057 5787665 := bstep (se 2 (by rfl) ⟨2170374, by rfl⟩ : syracuseStep 5787665 = 4340749) B4340749
theorem B1929235 : Blo 1713057 1929235 := bstep (se 1 (by rfl) ⟨1446926, by rfl⟩ : syracuseStep 1929235 = 2893853) B2893853
theorem B4116515 : Blo 1713057 4116515 := bstep (se 1 (by rfl) ⟨3087386, by rfl⟩ : syracuseStep 4116515 = 6174773) B6174773
theorem B8679473 : Blo 1713057 8679473 := bstep (se 2 (by rfl) ⟨3254802, by rfl⟩ : syracuseStep 8679473 = 6509605) B6509605
theorem B1929379 : Blo 1713057 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B9760945 : Blo 1713057 9760945 := bstep (se 2 (by rfl) ⟨3660354, by rfl⟩ : syracuseStep 9760945 = 7320709) B7320709
theorem B9269425 : Blo 1713057 9269425 := bstep (se 2 (by rfl) ⟨3476034, by rfl⟩ : syracuseStep 9269425 = 6952069) B6952069
theorem B1855747 : Blo 1713057 1855747 := bstep (se 1 (by rfl) ⟨1391810, by rfl⟩ : syracuseStep 1855747 = 2783621) B2783621
theorem B4878605 : Blo 1713057 4878605 := bstep (se 3 (by rfl) ⟨914738, by rfl⟩ : syracuseStep 4878605 = 1829477) B1829477
theorem B7319821 : Blo 1713057 7319821 := bstep (se 3 (by rfl) ⟨1372466, by rfl⟩ : syracuseStep 7319821 = 2744933) B2744933
theorem B3854609 : Blo 1713057 3854609 := bstep (se 2 (by rfl) ⟨1445478, by rfl⟩ : syracuseStep 3854609 = 2890957) B2890957
theorem B3854627 : Blo 1713057 3854627 := bstep (se 1 (by rfl) ⟨2890970, by rfl⟩ : syracuseStep 3854627 = 5781941) B5781941
theorem B46903693 : Blo 1713057 46903693 := bstep (se 3 (by rfl) ⟨8794442, by rfl⟩ : syracuseStep 46903693 = 17588885) B17588885
theorem B10572209 : Blo 1713057 10572209 := bstep (se 2 (by rfl) ⟨3964578, by rfl⟩ : syracuseStep 10572209 = 7929157) B7929157
theorem B4878787 : Blo 1713057 4878787 := bstep (se 1 (by rfl) ⟨3659090, by rfl⟩ : syracuseStep 4878787 = 7318181) B7318181
theorem B3297763 : Blo 1713057 3297763 := bstep (se 1 (by rfl) ⟨2473322, by rfl⟩ : syracuseStep 3297763 = 4946645) B4946645
theorem B8794595 : Blo 1713057 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B4116977 : Blo 1713057 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B19780109 : Blo 1713057 19780109 := bstep (se 3 (by rfl) ⟨3708770, by rfl⟩ : syracuseStep 19780109 = 7417541) B7417541
theorem B1831459 : Blo 1713057 1831459 := bstep (se 1 (by rfl) ⟨1373594, by rfl⟩ : syracuseStep 1831459 = 2747189) B2747189
theorem B5788205 : Blo 1713057 5788205 := bstep (se 3 (by rfl) ⟨1085288, by rfl⟩ : syracuseStep 5788205 = 2170577) B2170577
theorem B3854897 : Blo 1713057 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B6509105 : Blo 1713057 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B3854915 : Blo 1713057 3854915 := bstep (se 1 (by rfl) ⟨2891186, by rfl⟩ : syracuseStep 3854915 = 5782373) B5782373
theorem B8237645 : Blo 1713057 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B4117073 : Blo 1713057 4117073 := bstep (se 2 (by rfl) ⟨1543902, by rfl⟩ : syracuseStep 4117073 = 3087805) B3087805
theorem B4878947 : Blo 1713057 4878947 := bstep (se 1 (by rfl) ⟨3659210, by rfl⟩ : syracuseStep 4878947 = 7318421) B7318421
theorem B5788259 : Blo 1713057 5788259 := bstep (se 1 (by rfl) ⟨4341194, by rfl⟩ : syracuseStep 5788259 = 8682389) B8682389
theorem B8237837 : Blo 1713057 8237837 := bstep (se 3 (by rfl) ⟨1544594, by rfl⟩ : syracuseStep 8237837 = 3089189) B3089189
theorem B4338481 : Blo 1713057 4338481 := bstep (se 2 (by rfl) ⟨1626930, by rfl⟩ : syracuseStep 4338481 = 3253861) B3253861
theorem B3855185 : Blo 1713057 3855185 := bstep (se 2 (by rfl) ⟨1445694, by rfl⟩ : syracuseStep 3855185 = 2891389) B2891389
theorem B3855203 : Blo 1713057 3855203 := bstep (se 1 (by rfl) ⟨2891402, by rfl⟩ : syracuseStep 3855203 = 5782805) B5782805
theorem B10572749 : Blo 1713057 10572749 := bstep (se 3 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 10572749 = 3964781) B3964781
theorem B4338755 : Blo 1713057 4338755 := bstep (se 1 (by rfl) ⟨3254066, by rfl⟩ : syracuseStep 4338755 = 6508133) B6508133
theorem B4633699 : Blo 1713057 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B3855473 : Blo 1713057 3855473 := bstep (se 2 (by rfl) ⟨1445802, by rfl⟩ : syracuseStep 3855473 = 2891605) B2891605
theorem B3855491 : Blo 1713057 3855491 := bstep (se 1 (by rfl) ⟨2891618, by rfl⟩ : syracuseStep 3855491 = 5783237) B5783237
theorem B4633805 : Blo 1713057 4633805 := bstep (se 3 (by rfl) ⟨868838, by rfl⟩ : syracuseStep 4633805 = 1737677) B1737677
theorem B23442659 : Blo 1713057 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B4338947 : Blo 1713057 4338947 := bstep (se 1 (by rfl) ⟨3254210, by rfl⟩ : syracuseStep 4338947 = 6508421) B6508421
theorem B7320881 : Blo 1713057 7320881 := bstep (se 2 (by rfl) ⟨2745330, by rfl⟩ : syracuseStep 7320881 = 5490661) B5490661
theorem B2168147 : Blo 1713057 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B21976433 : Blo 1713057 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B2569601 : Blo 1713057 2569601 := bstep (se 2 (by rfl) ⟨963600, by rfl⟩ : syracuseStep 2569601 = 1927201) B1927201
theorem B3855761 : Blo 1713057 3855761 := bstep (se 2 (by rfl) ⟨1445910, by rfl⟩ : syracuseStep 3855761 = 2891821) B2891821
theorem B2569619 : Blo 1713057 2569619 := bstep (se 1 (by rfl) ⟨1927214, by rfl⟩ : syracuseStep 2569619 = 3854429) B3854429
theorem B3855779 : Blo 1713057 3855779 := bstep (se 1 (by rfl) ⟨2891834, by rfl⟩ : syracuseStep 3855779 = 5783669) B5783669
theorem B2569649 : Blo 1713057 2569649 := bstep (se 2 (by rfl) ⟨963618, by rfl⟩ : syracuseStep 2569649 = 1927237) B1927237
theorem B3659185 : Blo 1713057 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B2315713 : Blo 1713057 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B2569667 : Blo 1713057 2569667 := bstep (se 1 (by rfl) ⟨1927250, by rfl⟩ : syracuseStep 2569667 = 3854501) B3854501
theorem B35173829 : Blo 1713057 35173829 := bstep (se 4 (by rfl) ⟨3297546, by rfl⟩ : syracuseStep 35173829 = 6595093) B6595093
theorem B2569697 : Blo 1713057 2569697 := bstep (se 2 (by rfl) ⟨963636, by rfl⟩ : syracuseStep 2569697 = 1927273) B1927273
theorem B8680931 : Blo 1713057 8680931 := bstep (se 1 (by rfl) ⟨6510698, by rfl⟩ : syracuseStep 8680931 = 13021397) B13021397
theorem B2569715 : Blo 1713057 2569715 := bstep (se 1 (by rfl) ⟨1927286, by rfl⟩ : syracuseStep 2569715 = 3854573) B3854573
theorem B4347395 : Blo 1713057 4347395 := bstep (se 1 (by rfl) ⟨3260546, by rfl⟩ : syracuseStep 4347395 = 6521093) B6521093
theorem B2569745 : Blo 1713057 2569745 := bstep (se 2 (by rfl) ⟨963654, by rfl⟩ : syracuseStep 2569745 = 1927309) B1927309
theorem B2569763 : Blo 1713057 2569763 := bstep (se 1 (by rfl) ⟨1927322, by rfl⟩ : syracuseStep 2569763 = 3854645) B3854645
theorem B2569793 : Blo 1713057 2569793 := bstep (se 2 (by rfl) ⟨963672, by rfl⟩ : syracuseStep 2569793 = 1927345) B1927345
theorem B5797453 : Blo 1713057 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B2569811 : Blo 1713057 2569811 := bstep (se 1 (by rfl) ⟨1927358, by rfl⟩ : syracuseStep 2569811 = 3854717) B3854717
theorem B9762403 : Blo 1713057 9762403 := bstep (se 1 (by rfl) ⟨7321802, by rfl⟩ : syracuseStep 9762403 = 14643605) B14643605
theorem B2569841 : Blo 1713057 2569841 := bstep (se 2 (by rfl) ⟨963690, by rfl⟩ : syracuseStep 2569841 = 1927381) B1927381
theorem B2569859 : Blo 1713057 2569859 := bstep (se 1 (by rfl) ⟨1927394, by rfl⟩ : syracuseStep 2569859 = 3854789) B3854789
theorem B4880017 : Blo 1713057 4880017 := bstep (se 2 (by rfl) ⟨1830006, by rfl⟩ : syracuseStep 4880017 = 3660013) B3660013
theorem B2569889 : Blo 1713057 2569889 := bstep (se 2 (by rfl) ⟨963708, by rfl⟩ : syracuseStep 2569889 = 1927417) B1927417
theorem B3856049 : Blo 1713057 3856049 := bstep (se 2 (by rfl) ⟨1446018, by rfl⟩ : syracuseStep 3856049 = 2892037) B2892037
theorem B2569907 : Blo 1713057 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B3856067 : Blo 1713057 3856067 := bstep (se 1 (by rfl) ⟨2892050, by rfl⟩ : syracuseStep 3856067 = 5784101) B5784101
theorem B2569937 : Blo 1713057 2569937 := bstep (se 2 (by rfl) ⟨963726, by rfl⟩ : syracuseStep 2569937 = 1927453) B1927453
theorem B2569955 : Blo 1713057 2569955 := bstep (se 1 (by rfl) ⟨1927466, by rfl⟩ : syracuseStep 2569955 = 3854933) B3854933
theorem B14636771 : Blo 1713057 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B2569985 : Blo 1713057 2569985 := bstep (se 2 (by rfl) ⟨963744, by rfl⟩ : syracuseStep 2569985 = 1927489) B1927489
theorem B2570003 : Blo 1713057 2570003 := bstep (se 1 (by rfl) ⟨1927502, by rfl⟩ : syracuseStep 2570003 = 3855005) B3855005
theorem B2570033 : Blo 1713057 2570033 := bstep (se 2 (by rfl) ⟨963762, by rfl⟩ : syracuseStep 2570033 = 1927525) B1927525
theorem B2570051 : Blo 1713057 2570051 := bstep (se 1 (by rfl) ⟨1927538, by rfl⟩ : syracuseStep 2570051 = 3855077) B3855077
theorem B2570081 : Blo 1713057 2570081 := bstep (se 2 (by rfl) ⟨963780, by rfl⟩ : syracuseStep 2570081 = 1927561) B1927561
theorem B2570099 : Blo 1713057 2570099 := bstep (se 1 (by rfl) ⟨1927574, by rfl⟩ : syracuseStep 2570099 = 3855149) B3855149
theorem B13186957 : Blo 1713057 13186957 := bstep (se 3 (by rfl) ⟨2472554, by rfl⟩ : syracuseStep 13186957 = 4945109) B4945109
theorem B20846477 : Blo 1713057 20846477 := bstep (se 3 (by rfl) ⟨3908714, by rfl⟩ : syracuseStep 20846477 = 7817429) B7817429
theorem B2570129 : Blo 1713057 2570129 := bstep (se 2 (by rfl) ⟨963798, by rfl⟩ : syracuseStep 2570129 = 1927597) B1927597
theorem B2570147 : Blo 1713057 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B2570177 : Blo 1713057 2570177 := bstep (se 2 (by rfl) ⟨963816, by rfl⟩ : syracuseStep 2570177 = 1927633) B1927633
theorem B3856337 : Blo 1713057 3856337 := bstep (se 2 (by rfl) ⟨1446126, by rfl⟩ : syracuseStep 3856337 = 2892253) B2892253
theorem B2570195 : Blo 1713057 2570195 := bstep (se 1 (by rfl) ⟨1927646, by rfl⟩ : syracuseStep 2570195 = 3855293) B3855293
theorem B3856355 : Blo 1713057 3856355 := bstep (se 1 (by rfl) ⟨2892266, by rfl⟩ : syracuseStep 3856355 = 5784533) B5784533
theorem B6510563 : Blo 1713057 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B2570225 : Blo 1713057 2570225 := bstep (se 2 (by rfl) ⟨963834, by rfl⟩ : syracuseStep 2570225 = 1927669) B1927669
theorem B6510577 : Blo 1713057 6510577 := bstep (se 2 (by rfl) ⟨2441466, by rfl⟩ : syracuseStep 6510577 = 4882933) B4882933
theorem B2570243 : Blo 1713057 2570243 := bstep (se 1 (by rfl) ⟨1927682, by rfl⟩ : syracuseStep 2570243 = 3855365) B3855365
theorem B2168851 : Blo 1713057 2168851 := bstep (se 1 (by rfl) ⟨1626638, by rfl⟩ : syracuseStep 2168851 = 3253277) B3253277
theorem B2570273 : Blo 1713057 2570273 := bstep (se 2 (by rfl) ⟨963852, by rfl⟩ : syracuseStep 2570273 = 1927705) B1927705
theorem B9271331 : Blo 1713057 9271331 := bstep (se 1 (by rfl) ⟨6953498, by rfl⟩ : syracuseStep 9271331 = 13906997) B13906997
theorem B2570291 : Blo 1713057 2570291 := bstep (se 1 (by rfl) ⟨1927718, by rfl⟩ : syracuseStep 2570291 = 3855437) B3855437
theorem B3659843 : Blo 1713057 3659843 := bstep (se 1 (by rfl) ⟨2744882, by rfl⟩ : syracuseStep 3659843 = 5489765) B5489765
theorem B13195333 : Blo 1713057 13195333 := bstep (se 4 (by rfl) ⟨1237062, by rfl⟩ : syracuseStep 13195333 = 2474125) B2474125
theorem B2570321 : Blo 1713057 2570321 := bstep (se 2 (by rfl) ⟨963870, by rfl⟩ : syracuseStep 2570321 = 1927741) B1927741
theorem B2570339 : Blo 1713057 2570339 := bstep (se 1 (by rfl) ⟨1927754, by rfl⟩ : syracuseStep 2570339 = 3855509) B3855509
theorem B5781617 : Blo 1713057 5781617 := bstep (se 2 (by rfl) ⟨2168106, by rfl⟩ : syracuseStep 5781617 = 4336213) B4336213
theorem B9762929 : Blo 1713057 9762929 := bstep (se 2 (by rfl) ⟨3661098, by rfl⟩ : syracuseStep 9762929 = 7322197) B7322197
theorem B2168947 : Blo 1713057 2168947 := bstep (se 1 (by rfl) ⟨1626710, by rfl⟩ : syracuseStep 2168947 = 3253421) B3253421
theorem B2570369 : Blo 1713057 2570369 := bstep (se 2 (by rfl) ⟨963888, by rfl⟩ : syracuseStep 2570369 = 1927777) B1927777
theorem B2570387 : Blo 1713057 2570387 := bstep (se 1 (by rfl) ⟨1927790, by rfl⟩ : syracuseStep 2570387 = 3855581) B3855581
theorem B2570417 : Blo 1713057 2570417 := bstep (se 2 (by rfl) ⟨963906, by rfl⟩ : syracuseStep 2570417 = 1927813) B1927813
theorem B4339889 : Blo 1713057 4339889 := bstep (se 2 (by rfl) ⟨1627458, by rfl⟩ : syracuseStep 4339889 = 3254917) B3254917
theorem B2570435 : Blo 1713057 2570435 := bstep (se 1 (by rfl) ⟨1927826, by rfl⟩ : syracuseStep 2570435 = 3855653) B3855653
theorem B2570465 : Blo 1713057 2570465 := bstep (se 2 (by rfl) ⟨963924, by rfl⟩ : syracuseStep 2570465 = 1927849) B1927849
theorem B1808611 : Blo 1713057 1808611 := bstep (se 1 (by rfl) ⟨1356458, by rfl⟩ : syracuseStep 1808611 = 2712917) B2712917
theorem B4339939 : Blo 1713057 4339939 := bstep (se 1 (by rfl) ⟨3254954, by rfl⟩ : syracuseStep 4339939 = 6509909) B6509909
theorem B3856625 : Blo 1713057 3856625 := bstep (se 2 (by rfl) ⟨1446234, by rfl⟩ : syracuseStep 3856625 = 2892469) B2892469
theorem B2570483 : Blo 1713057 2570483 := bstep (se 1 (by rfl) ⟨1927862, by rfl⟩ : syracuseStep 2570483 = 3855725) B3855725
theorem B3856643 : Blo 1713057 3856643 := bstep (se 1 (by rfl) ⟨2892482, by rfl⟩ : syracuseStep 3856643 = 5784965) B5784965
theorem B8681741 : Blo 1713057 8681741 := bstep (se 3 (by rfl) ⟨1627826, by rfl⟩ : syracuseStep 8681741 = 3255653) B3255653
theorem B2570513 : Blo 1713057 2570513 := bstep (se 2 (by rfl) ⟨963942, by rfl⟩ : syracuseStep 2570513 = 1927885) B1927885
theorem B2570531 : Blo 1713057 2570531 := bstep (se 1 (by rfl) ⟨1927898, by rfl⟩ : syracuseStep 2570531 = 3855797) B3855797
theorem B2570561 : Blo 1713057 2570561 := bstep (se 2 (by rfl) ⟨963960, by rfl⟩ : syracuseStep 2570561 = 1927921) B1927921
theorem B2570579 : Blo 1713057 2570579 := bstep (se 1 (by rfl) ⟨1927934, by rfl⟩ : syracuseStep 2570579 = 3855869) B3855869
theorem B8345969 : Blo 1713057 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B2570609 : Blo 1713057 2570609 := bstep (se 2 (by rfl) ⟨963978, by rfl⟩ : syracuseStep 2570609 = 1927957) B1927957
theorem B4340081 : Blo 1713057 4340081 := bstep (se 2 (by rfl) ⟨1627530, by rfl⟩ : syracuseStep 4340081 = 3255061) B3255061
theorem B2439553 : Blo 1713057 2439553 := bstep (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) B1829665
theorem B2570627 : Blo 1713057 2570627 := bstep (se 1 (by rfl) ⟨1927970, by rfl⟩ : syracuseStep 2570627 = 3855941) B3855941
theorem B2570657 : Blo 1713057 2570657 := bstep (se 2 (by rfl) ⟨963996, by rfl⟩ : syracuseStep 2570657 = 1927993) B1927993
theorem B2570675 : Blo 1713057 2570675 := bstep (se 1 (by rfl) ⟨1928006, by rfl⟩ : syracuseStep 2570675 = 3856013) B3856013
theorem B2570705 : Blo 1713057 2570705 := bstep (se 2 (by rfl) ⟨964014, by rfl⟩ : syracuseStep 2570705 = 1928029) B1928029
theorem B2570723 : Blo 1713057 2570723 := bstep (se 1 (by rfl) ⟨1928042, by rfl⟩ : syracuseStep 2570723 = 3856085) B3856085
theorem B2439667 : Blo 1713057 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B2570753 : Blo 1713057 2570753 := bstep (se 2 (by rfl) ⟨964032, by rfl⟩ : syracuseStep 2570753 = 1928065) B1928065
theorem B13015565 : Blo 1713057 13015565 := bstep (se 3 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 13015565 = 4880837) B4880837
theorem B3856913 : Blo 1713057 3856913 := bstep (se 2 (by rfl) ⟨1446342, by rfl⟩ : syracuseStep 3856913 = 2892685) B2892685
theorem B2570771 : Blo 1713057 2570771 := bstep (se 1 (by rfl) ⟨1928078, by rfl⟩ : syracuseStep 2570771 = 3856157) B3856157
theorem B3856931 : Blo 1713057 3856931 := bstep (se 1 (by rfl) ⟨2892698, by rfl⟩ : syracuseStep 3856931 = 5785397) B5785397
theorem B2570801 : Blo 1713057 2570801 := bstep (se 2 (by rfl) ⟨964050, by rfl⟩ : syracuseStep 2570801 = 1928101) B1928101
theorem B2570819 : Blo 1713057 2570819 := bstep (se 1 (by rfl) ⟨1928114, by rfl⟩ : syracuseStep 2570819 = 3856229) B3856229
theorem B2570849 : Blo 1713057 2570849 := bstep (se 2 (by rfl) ⟨964068, by rfl⟩ : syracuseStep 2570849 = 1928137) B1928137
theorem B2169443 : Blo 1713057 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B2570867 : Blo 1713057 2570867 := bstep (se 1 (by rfl) ⟨1928150, by rfl⟩ : syracuseStep 2570867 = 3856301) B3856301
theorem B5782157 : Blo 1713057 5782157 := bstep (se 3 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 5782157 = 2168309) B2168309
theorem B9394829 : Blo 1713057 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B2570897 : Blo 1713057 2570897 := bstep (se 2 (by rfl) ⟨964086, by rfl⟩ : syracuseStep 2570897 = 1928173) B1928173
theorem B35199629 : Blo 1713057 35199629 := bstep (se 3 (by rfl) ⟨6599930, by rfl⟩ : syracuseStep 35199629 = 13199861) B13199861
theorem B2570915 : Blo 1713057 2570915 := bstep (se 1 (by rfl) ⟨1928186, by rfl⟩ : syracuseStep 2570915 = 3856373) B3856373
theorem B2570945 : Blo 1713057 2570945 := bstep (se 2 (by rfl) ⟨964104, by rfl⟩ : syracuseStep 2570945 = 1928209) B1928209
theorem B5782211 : Blo 1713057 5782211 := bstep (se 1 (by rfl) ⟨4336658, by rfl⟩ : syracuseStep 5782211 = 8673317) B8673317
theorem B5946061 : Blo 1713057 5946061 := bstep (se 3 (by rfl) ⟨1114886, by rfl⟩ : syracuseStep 5946061 = 2229773) B2229773
theorem B8919757 : Blo 1713057 8919757 := bstep (se 3 (by rfl) ⟨1672454, by rfl⟩ : syracuseStep 8919757 = 3344909) B3344909
theorem B2570963 : Blo 1713057 2570963 := bstep (se 1 (by rfl) ⟨1928222, by rfl⟩ : syracuseStep 2570963 = 3856445) B3856445
theorem B2570993 : Blo 1713057 2570993 := bstep (se 2 (by rfl) ⟨964122, by rfl⟩ : syracuseStep 2570993 = 1928245) B1928245
theorem B2571011 : Blo 1713057 2571011 := bstep (se 1 (by rfl) ⟨1928258, by rfl⟩ : syracuseStep 2571011 = 3856517) B3856517
theorem B2571041 : Blo 1713057 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B3857201 : Blo 1713057 3857201 := bstep (se 2 (by rfl) ⟨1446450, by rfl⟩ : syracuseStep 3857201 = 2892901) B2892901
theorem B2571059 : Blo 1713057 2571059 := bstep (se 1 (by rfl) ⟨1928294, by rfl⟩ : syracuseStep 2571059 = 3856589) B3856589
theorem B3857219 : Blo 1713057 3857219 := bstep (se 1 (by rfl) ⟨2892914, by rfl⟩ : syracuseStep 3857219 = 5785829) B5785829
theorem B2571089 : Blo 1713057 2571089 := bstep (se 2 (by rfl) ⟨964158, by rfl⟩ : syracuseStep 2571089 = 1928317) B1928317
theorem B2571107 : Blo 1713057 2571107 := bstep (se 1 (by rfl) ⟨1928330, by rfl⟩ : syracuseStep 2571107 = 3856661) B3856661
theorem B2571137 : Blo 1713057 2571137 := bstep (se 2 (by rfl) ⟨964176, by rfl⟩ : syracuseStep 2571137 = 1928353) B1928353
theorem B4881293 : Blo 1713057 4881293 := bstep (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) B1830485
theorem B3660689 : Blo 1713057 3660689 := bstep (se 2 (by rfl) ⟨1372758, by rfl⟩ : syracuseStep 3660689 = 2745517) B2745517
theorem B2571155 : Blo 1713057 2571155 := bstep (se 1 (by rfl) ⟨1928366, by rfl⟩ : syracuseStep 2571155 = 3856733) B3856733
theorem B2571185 : Blo 1713057 2571185 := bstep (se 2 (by rfl) ⟨964194, by rfl⟩ : syracuseStep 2571185 = 1928389) B1928389
theorem B4635569 : Blo 1713057 4635569 := bstep (se 2 (by rfl) ⟨1738338, by rfl⟩ : syracuseStep 4635569 = 3476677) B3476677
theorem B2571203 : Blo 1713057 2571203 := bstep (se 1 (by rfl) ⟨1928402, by rfl⟩ : syracuseStep 2571203 = 3856805) B3856805
theorem B10705861 : Blo 1713057 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B5782481 : Blo 1713057 5782481 := bstep (se 2 (by rfl) ⟨2168430, by rfl⟩ : syracuseStep 5782481 = 4336861) B4336861
theorem B2571233 : Blo 1713057 2571233 := bstep (se 2 (by rfl) ⟨964212, by rfl⟩ : syracuseStep 2571233 = 1928425) B1928425
theorem B8674289 : Blo 1713057 8674289 := bstep (se 2 (by rfl) ⟨3252858, by rfl⟩ : syracuseStep 8674289 = 6505717) B6505717
theorem B2571251 : Blo 1713057 2571251 := bstep (se 1 (by rfl) ⟨1928438, by rfl⟩ : syracuseStep 2571251 = 3856877) B3856877
theorem B2571281 : Blo 1713057 2571281 := bstep (se 2 (by rfl) ⟨964230, by rfl⟩ : syracuseStep 2571281 = 1928461) B1928461
theorem B2571299 : Blo 1713057 2571299 := bstep (se 1 (by rfl) ⟨1928474, by rfl⟩ : syracuseStep 2571299 = 3856949) B3856949
theorem B6945841 : Blo 1713057 6945841 := bstep (se 2 (by rfl) ⟨2604690, by rfl⟩ : syracuseStep 6945841 = 5209381) B5209381
theorem B2571329 : Blo 1713057 2571329 := bstep (se 2 (by rfl) ⟨964248, by rfl⟩ : syracuseStep 2571329 = 1928497) B1928497
theorem B4881475 : Blo 1713057 4881475 := bstep (se 1 (by rfl) ⟨3661106, by rfl⟩ : syracuseStep 4881475 = 7322213) B7322213
theorem B3857489 : Blo 1713057 3857489 := bstep (se 2 (by rfl) ⟨1446558, by rfl⟩ : syracuseStep 3857489 = 2893117) B2893117
theorem B2571347 : Blo 1713057 2571347 := bstep (se 1 (by rfl) ⟨1928510, by rfl⟩ : syracuseStep 2571347 = 3857021) B3857021
theorem B2890849 : Blo 1713057 2890849 := bstep (se 2 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 2890849 = 2168137) B2168137
theorem B3857507 : Blo 1713057 3857507 := bstep (se 1 (by rfl) ⟨2893130, by rfl⟩ : syracuseStep 3857507 = 5786261) B5786261
theorem B4881521 : Blo 1713057 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B2571377 : Blo 1713057 2571377 := bstep (se 2 (by rfl) ⟨964266, by rfl⟩ : syracuseStep 2571377 = 1928533) B1928533
theorem B2784385 : Blo 1713057 2784385 := bstep (se 2 (by rfl) ⟨1044144, by rfl⟩ : syracuseStep 2784385 = 2088289) B2088289
theorem B2890883 : Blo 1713057 2890883 := bstep (se 1 (by rfl) ⟨2168162, by rfl⟩ : syracuseStep 2890883 = 4336325) B4336325
theorem B2571395 : Blo 1713057 2571395 := bstep (se 1 (by rfl) ⟨1928546, by rfl⟩ : syracuseStep 2571395 = 3857093) B3857093
theorem B2571425 : Blo 1713057 2571425 := bstep (se 2 (by rfl) ⟨964284, by rfl⟩ : syracuseStep 2571425 = 1928569) B1928569
theorem B2571443 : Blo 1713057 2571443 := bstep (se 1 (by rfl) ⟨1928582, by rfl⟩ : syracuseStep 2571443 = 3857165) B3857165
theorem B2571473 : Blo 1713057 2571473 := bstep (se 2 (by rfl) ⟨964302, by rfl⟩ : syracuseStep 2571473 = 1928605) B1928605
theorem B2571491 : Blo 1713057 2571491 := bstep (se 1 (by rfl) ⟨1928618, by rfl⟩ : syracuseStep 2571491 = 3857237) B3857237
theorem B2571521 : Blo 1713057 2571521 := bstep (se 2 (by rfl) ⟨964320, by rfl⟩ : syracuseStep 2571521 = 1928641) B1928641
theorem B2891011 : Blo 1713057 2891011 := bstep (se 1 (by rfl) ⟨2168258, by rfl⟩ : syracuseStep 2891011 = 4336517) B4336517
theorem B2571539 : Blo 1713057 2571539 := bstep (se 1 (by rfl) ⟨1928654, by rfl⟩ : syracuseStep 2571539 = 3857309) B3857309
theorem B2170147 : Blo 1713057 2170147 := bstep (se 1 (by rfl) ⟨1627610, by rfl⟩ : syracuseStep 2170147 = 3255221) B3255221
theorem B4947245 : Blo 1713057 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B2571569 : Blo 1713057 2571569 := bstep (se 2 (by rfl) ⟨964338, by rfl⟩ : syracuseStep 2571569 = 1928677) B1928677
theorem B2571587 : Blo 1713057 2571587 := bstep (se 1 (by rfl) ⟨1928690, by rfl⟩ : syracuseStep 2571587 = 3857381) B3857381
theorem B4341073 : Blo 1713057 4341073 := bstep (se 2 (by rfl) ⟨1627902, by rfl⟩ : syracuseStep 4341073 = 3255805) B3255805
theorem B2571617 : Blo 1713057 2571617 := bstep (se 2 (by rfl) ⟨964356, by rfl⟩ : syracuseStep 2571617 = 1928713) B1928713
theorem B3857777 : Blo 1713057 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B2571635 : Blo 1713057 2571635 := bstep (se 1 (by rfl) ⟨1928726, by rfl⟩ : syracuseStep 2571635 = 3857453) B3857453
theorem B3857795 : Blo 1713057 3857795 := bstep (se 1 (by rfl) ⟨2893346, by rfl⟩ : syracuseStep 3857795 = 5786693) B5786693
theorem B2170243 : Blo 1713057 2170243 := bstep (se 1 (by rfl) ⟨1627682, by rfl⟩ : syracuseStep 2170243 = 3255365) B3255365
theorem B2891153 : Blo 1713057 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B2571665 : Blo 1713057 2571665 := bstep (se 2 (by rfl) ⟨964374, by rfl⟩ : syracuseStep 2571665 = 1928749) B1928749
theorem B2571683 : Blo 1713057 2571683 := bstep (se 1 (by rfl) ⟨1928762, by rfl⟩ : syracuseStep 2571683 = 3857525) B3857525
theorem B2571713 : Blo 1713057 2571713 := bstep (se 2 (by rfl) ⟨964392, by rfl⟩ : syracuseStep 2571713 = 1928785) B1928785
theorem B2571731 : Blo 1713057 2571731 := bstep (se 1 (by rfl) ⟨1928798, by rfl⟩ : syracuseStep 2571731 = 3857597) B3857597
theorem B5783021 : Blo 1713057 5783021 := bstep (se 3 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 5783021 = 2168633) B2168633
theorem B2571761 : Blo 1713057 2571761 := bstep (se 2 (by rfl) ⟨964410, by rfl⟩ : syracuseStep 2571761 = 1928821) B1928821
theorem B2571779 : Blo 1713057 2571779 := bstep (se 1 (by rfl) ⟨1928834, by rfl⟩ : syracuseStep 2571779 = 3857669) B3857669
theorem B2891281 : Blo 1713057 2891281 := bstep (se 2 (by rfl) ⟨1084230, by rfl⟩ : syracuseStep 2891281 = 2168461) B2168461
theorem B2571809 : Blo 1713057 2571809 := bstep (se 2 (by rfl) ⟨964428, by rfl⟩ : syracuseStep 2571809 = 1928857) B1928857
theorem B5783075 : Blo 1713057 5783075 := bstep (se 1 (by rfl) ⟨4337306, by rfl⟩ : syracuseStep 5783075 = 8674613) B8674613
theorem B9764387 : Blo 1713057 9764387 := bstep (se 1 (by rfl) ⟨7323290, by rfl⟩ : syracuseStep 9764387 = 14646581) B14646581
theorem B2891315 : Blo 1713057 2891315 := bstep (se 1 (by rfl) ⟨2168486, by rfl⟩ : syracuseStep 2891315 = 4336973) B4336973
theorem B2571827 : Blo 1713057 2571827 := bstep (se 1 (by rfl) ⟨1928870, by rfl⟩ : syracuseStep 2571827 = 3857741) B3857741
theorem B2571857 : Blo 1713057 2571857 := bstep (se 2 (by rfl) ⟨964446, by rfl⟩ : syracuseStep 2571857 = 1928893) B1928893
theorem B2571875 : Blo 1713057 2571875 := bstep (se 1 (by rfl) ⟨1928906, by rfl⟩ : syracuseStep 2571875 = 3857813) B3857813
theorem B2571905 : Blo 1713057 2571905 := bstep (se 2 (by rfl) ⟨964464, by rfl⟩ : syracuseStep 2571905 = 1928929) B1928929
theorem B3858065 : Blo 1713057 3858065 := bstep (se 2 (by rfl) ⟨1446774, by rfl⟩ : syracuseStep 3858065 = 2893549) B2893549
theorem B2571923 : Blo 1713057 2571923 := bstep (se 1 (by rfl) ⟨1928942, by rfl⟩ : syracuseStep 2571923 = 3857885) B3857885
theorem B3858083 : Blo 1713057 3858083 := bstep (se 1 (by rfl) ⟨2893562, by rfl⟩ : syracuseStep 3858083 = 5787125) B5787125
theorem B2571953 : Blo 1713057 2571953 := bstep (se 2 (by rfl) ⟨964482, by rfl⟩ : syracuseStep 2571953 = 1928965) B1928965
theorem B2891443 : Blo 1713057 2891443 := bstep (se 1 (by rfl) ⟨2168582, by rfl⟩ : syracuseStep 2891443 = 4337165) B4337165
theorem B3710659 : Blo 1713057 3710659 := bstep (se 1 (by rfl) ⟨2782994, by rfl⟩ : syracuseStep 3710659 = 5565989) B5565989
theorem B5865155 : Blo 1713057 5865155 := bstep (se 1 (by rfl) ⟨4398866, by rfl⟩ : syracuseStep 5865155 = 8797733) B8797733
theorem B2571971 : Blo 1713057 2571971 := bstep (se 1 (by rfl) ⟨1928978, by rfl⟩ : syracuseStep 2571971 = 3857957) B3857957
theorem B10985165 : Blo 1713057 10985165 := bstep (se 3 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 10985165 = 4119437) B4119437
theorem B2572001 : Blo 1713057 2572001 := bstep (se 2 (by rfl) ⟨964500, by rfl⟩ : syracuseStep 2572001 = 1929001) B1929001
theorem B2572019 : Blo 1713057 2572019 := bstep (se 1 (by rfl) ⟨1929014, by rfl⟩ : syracuseStep 2572019 = 3858029) B3858029
theorem B5209859 : Blo 1713057 5209859 := bstep (se 1 (by rfl) ⟨3907394, by rfl⟩ : syracuseStep 5209859 = 7814789) B7814789
theorem B2572049 : Blo 1713057 2572049 := bstep (se 2 (by rfl) ⟨964518, by rfl⟩ : syracuseStep 2572049 = 1929037) B1929037
theorem B2572067 : Blo 1713057 2572067 := bstep (se 1 (by rfl) ⟨1929050, by rfl⟩ : syracuseStep 2572067 = 3858101) B3858101
theorem B2744113 : Blo 1713057 2744113 := bstep (se 2 (by rfl) ⟨1029042, by rfl⟩ : syracuseStep 2744113 = 2058085) B2058085
theorem B5783345 : Blo 1713057 5783345 := bstep (se 2 (by rfl) ⟨2168754, by rfl⟩ : syracuseStep 5783345 = 4337509) B4337509
theorem B2441011 : Blo 1713057 2441011 := bstep (se 1 (by rfl) ⟨1830758, by rfl⟩ : syracuseStep 2441011 = 3661517) B3661517
theorem B10428209 : Blo 1713057 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B2891585 : Blo 1713057 2891585 := bstep (se 2 (by rfl) ⟨1084344, by rfl⟩ : syracuseStep 2891585 = 2168689) B2168689
theorem B2572097 : Blo 1713057 2572097 := bstep (se 2 (by rfl) ⟨964536, by rfl⟩ : syracuseStep 2572097 = 1929073) B1929073
theorem B2572115 : Blo 1713057 2572115 := bstep (se 1 (by rfl) ⟨1929086, by rfl⟩ : syracuseStep 2572115 = 3858173) B3858173
theorem B11894627 : Blo 1713057 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B2572145 : Blo 1713057 2572145 := bstep (se 2 (by rfl) ⟨964554, by rfl⟩ : syracuseStep 2572145 = 1929109) B1929109
theorem B2572163 : Blo 1713057 2572163 := bstep (se 1 (by rfl) ⟨1929122, by rfl⟩ : syracuseStep 2572163 = 3858245) B3858245
theorem B2572193 : Blo 1713057 2572193 := bstep (se 2 (by rfl) ⟨964572, by rfl⟩ : syracuseStep 2572193 = 1929145) B1929145
theorem B3252145 : Blo 1713057 3252145 := bstep (se 2 (by rfl) ⟨1219554, by rfl⟩ : syracuseStep 3252145 = 2439109) B2439109
theorem B3858353 : Blo 1713057 3858353 := bstep (se 2 (by rfl) ⟨1446882, by rfl⟩ : syracuseStep 3858353 = 2893765) B2893765
theorem B2572211 : Blo 1713057 2572211 := bstep (se 1 (by rfl) ⟨1929158, by rfl⟩ : syracuseStep 2572211 = 3858317) B3858317
theorem B2891713 : Blo 1713057 2891713 := bstep (se 2 (by rfl) ⟨1084392, by rfl⟩ : syracuseStep 2891713 = 2168785) B2168785
theorem B3858371 : Blo 1713057 3858371 := bstep (se 1 (by rfl) ⟨2893778, by rfl⟩ : syracuseStep 3858371 = 5787557) B5787557
theorem B10977221 : Blo 1713057 10977221 := bstep (se 4 (by rfl) ⟨1029114, by rfl⟩ : syracuseStep 10977221 = 2058229) B2058229
theorem B2572241 : Blo 1713057 2572241 := bstep (se 2 (by rfl) ⟨964590, by rfl⟩ : syracuseStep 2572241 = 1929181) B1929181
theorem B2891747 : Blo 1713057 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B2572259 : Blo 1713057 2572259 := bstep (se 1 (by rfl) ⟨1929194, by rfl⟩ : syracuseStep 2572259 = 3858389) B3858389
theorem B3858443 : Blo 1713057 3858443 := bstep (se 1 (by rfl) ⟨2893832, by rfl⟩ : syracuseStep 3858443 = 5787665) B5787665
theorem B2891801 : Blo 1713057 2891801 := bstep (se 2 (by rfl) ⟨1084425, by rfl⟩ : syracuseStep 2891801 = 2168851) B2168851
theorem B2572313 : Blo 1713057 2572313 := bstep (se 2 (by rfl) ⟨964617, by rfl⟩ : syracuseStep 2572313 = 1929235) B1929235
theorem B3858497 : Blo 1713057 3858497 := bstep (se 2 (by rfl) ⟨1446936, by rfl⟩ : syracuseStep 3858497 = 2893873) B2893873
theorem B10977373 : Blo 1713057 10977373 := bstep (se 3 (by rfl) ⟨2058257, by rfl⟩ : syracuseStep 10977373 = 4116515) B4116515
theorem B3473537 : Blo 1713057 3473537 := bstep (se 2 (by rfl) ⟨1302576, by rfl⟩ : syracuseStep 3473537 = 2605153) B2605153
theorem B2572427 : Blo 1713057 2572427 := bstep (se 1 (by rfl) ⟨1929320, by rfl⟩ : syracuseStep 2572427 = 3858641) B3858641
theorem B2572439 : Blo 1713057 2572439 := bstep (se 1 (by rfl) ⟨1929329, by rfl⟩ : syracuseStep 2572439 = 3858659) B3858659
theorem B2891929 : Blo 1713057 2891929 := bstep (se 2 (by rfl) ⟨1084473, by rfl⟩ : syracuseStep 2891929 = 2168947) B2168947
theorem B3252403 : Blo 1713057 3252403 := bstep (se 1 (by rfl) ⟨2439302, by rfl⟩ : syracuseStep 3252403 = 4878605) B4878605
theorem B24715469 : Blo 1713057 24715469 := bstep (se 3 (by rfl) ⟨4634150, by rfl⟩ : syracuseStep 24715469 = 9268301) B9268301
theorem B5865689 : Blo 1713057 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B2572505 : Blo 1713057 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B3662081 : Blo 1713057 3662081 := bstep (se 2 (by rfl) ⟨1373280, by rfl⟩ : syracuseStep 3662081 = 2746561) B2746561
theorem B37044485 : Blo 1713057 37044485 := bstep (se 4 (by rfl) ⟨3472920, by rfl⟩ : syracuseStep 37044485 = 6945841) B6945841
theorem B9765137 : Blo 1713057 9765137 := bstep (se 2 (by rfl) ⟨3661926, by rfl⟩ : syracuseStep 9765137 = 7323853) B7323853
theorem B5783831 : Blo 1713057 5783831 := bstep (se 1 (by rfl) ⟨4337873, by rfl⟩ : syracuseStep 5783831 = 8675747) B8675747
theorem B3858713 : Blo 1713057 3858713 := bstep (se 2 (by rfl) ⟨1447017, by rfl⟩ : syracuseStep 3858713 = 2894035) B2894035
theorem B2744651 : Blo 1713057 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B2474329 : Blo 1713057 2474329 := bstep (se 2 (by rfl) ⟨927873, by rfl⟩ : syracuseStep 2474329 = 1855747) B1855747
theorem B3858803 : Blo 1713057 3858803 := bstep (se 1 (by rfl) ⟨2894102, by rfl⟩ : syracuseStep 3858803 = 5788205) B5788205
theorem B3252631 : Blo 1713057 3252631 := bstep (se 1 (by rfl) ⟨2439473, by rfl⟩ : syracuseStep 3252631 = 4878947) B4878947
theorem B3858839 : Blo 1713057 3858839 := bstep (se 1 (by rfl) ⟨2894129, by rfl⟩ : syracuseStep 3858839 = 5788259) B5788259
theorem B3252737 : Blo 1713057 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B62538257 : Blo 1713057 62538257 := bstep (se 2 (by rfl) ⟨23451846, by rfl⟩ : syracuseStep 62538257 = 46903693) B46903693
theorem B6505049 : Blo 1713057 6505049 := bstep (se 2 (by rfl) ⟨2439393, by rfl⟩ : syracuseStep 6505049 = 4878787) B4878787
theorem B2744921 : Blo 1713057 2744921 := bstep (se 2 (by rfl) ⟨1029345, by rfl⟩ : syracuseStep 2744921 = 2058691) B2058691
theorem B3252889 : Blo 1713057 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B2892503 : Blo 1713057 2892503 := bstep (se 1 (by rfl) ⟨2169377, by rfl⟩ : syracuseStep 2892503 = 4338755) B4338755
theorem B9765593 : Blo 1713057 9765593 := bstep (se 2 (by rfl) ⟨3662097, by rfl⟩ : syracuseStep 9765593 = 7324195) B7324195
theorem B4883161 : Blo 1713057 4883161 := bstep (se 2 (by rfl) ⟨1831185, by rfl⟩ : syracuseStep 4883161 = 3662371) B3662371
theorem B2441945 : Blo 1713057 2441945 := bstep (se 2 (by rfl) ⟨915729, by rfl⟩ : syracuseStep 2441945 = 1831459) B1831459
theorem B5784371 : Blo 1713057 5784371 := bstep (se 1 (by rfl) ⟨4338278, by rfl⟩ : syracuseStep 5784371 = 8676557) B8676557
theorem B2892631 : Blo 1713057 2892631 := bstep (se 1 (by rfl) ⟨2169473, by rfl⟩ : syracuseStep 2892631 = 4338947) B4338947
theorem B1713067 : Blo 1713057 1713067 := bstep (se 1 (by rfl) ⟨1284800, by rfl⟩ : syracuseStep 1713067 = 2569601) B2569601
theorem B1713079 : Blo 1713057 1713079 := bstep (se 1 (by rfl) ⟨1284809, by rfl⟩ : syracuseStep 1713079 = 2569619) B2569619
theorem B1713099 : Blo 1713057 1713099 := bstep (se 1 (by rfl) ⟨1284824, by rfl⟩ : syracuseStep 1713099 = 2569649) B2569649
theorem B1713111 : Blo 1713057 1713111 := bstep (se 1 (by rfl) ⟨1284833, by rfl⟩ : syracuseStep 1713111 = 2569667) B2569667
theorem B15631321 : Blo 1713057 15631321 := bstep (se 2 (by rfl) ⟨5861745, by rfl⟩ : syracuseStep 15631321 = 11723491) B11723491
theorem B1713131 : Blo 1713057 1713131 := bstep (se 1 (by rfl) ⟨1284848, by rfl⟩ : syracuseStep 1713131 = 2569697) B2569697
theorem B1713143 : Blo 1713057 1713143 := bstep (se 1 (by rfl) ⟨1284857, by rfl⟩ : syracuseStep 1713143 = 2569715) B2569715
theorem B1713163 : Blo 1713057 1713163 := bstep (se 1 (by rfl) ⟨1284872, by rfl⟩ : syracuseStep 1713163 = 2569745) B2569745
theorem B1713175 : Blo 1713057 1713175 := bstep (se 1 (by rfl) ⟨1284881, by rfl⟩ : syracuseStep 1713175 = 2569763) B2569763
theorem B1713195 : Blo 1713057 1713195 := bstep (se 1 (by rfl) ⟨1284896, by rfl⟩ : syracuseStep 1713195 = 2569793) B2569793
theorem B1713207 : Blo 1713057 1713207 := bstep (se 1 (by rfl) ⟨1284905, by rfl⟩ : syracuseStep 1713207 = 2569811) B2569811
theorem B5784641 : Blo 1713057 5784641 := bstep (se 2 (by rfl) ⟨2169240, by rfl⟩ : syracuseStep 5784641 = 4338481) B4338481
theorem B1713227 : Blo 1713057 1713227 := bstep (se 1 (by rfl) ⟨1284920, by rfl⟩ : syracuseStep 1713227 = 2569841) B2569841
theorem B1713239 : Blo 1713057 1713239 := bstep (se 1 (by rfl) ⟨1284929, by rfl⟩ : syracuseStep 1713239 = 2569859) B2569859
theorem B1713259 : Blo 1713057 1713259 := bstep (se 1 (by rfl) ⟨1284944, by rfl⟩ : syracuseStep 1713259 = 2569889) B2569889
theorem B1713271 : Blo 1713057 1713271 := bstep (se 1 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 1713271 = 2569907) B2569907
theorem B1713291 : Blo 1713057 1713291 := bstep (se 1 (by rfl) ⟨1284968, by rfl⟩ : syracuseStep 1713291 = 2569937) B2569937
theorem B1713303 : Blo 1713057 1713303 := bstep (se 1 (by rfl) ⟨1284977, by rfl⟩ : syracuseStep 1713303 = 2569955) B2569955
theorem B9757847 : Blo 1713057 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B5489815 : Blo 1713057 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B1713323 : Blo 1713057 1713323 := bstep (se 1 (by rfl) ⟨1284992, by rfl⟩ : syracuseStep 1713323 = 2569985) B2569985
theorem B1713335 : Blo 1713057 1713335 := bstep (se 1 (by rfl) ⟨1285001, by rfl⟩ : syracuseStep 1713335 = 2570003) B2570003
theorem B1713355 : Blo 1713057 1713355 := bstep (se 1 (by rfl) ⟨1285016, by rfl⟩ : syracuseStep 1713355 = 2570033) B2570033
theorem B1713367 : Blo 1713057 1713367 := bstep (se 1 (by rfl) ⟨1285025, by rfl⟩ : syracuseStep 1713367 = 2570051) B2570051
theorem B1713387 : Blo 1713057 1713387 := bstep (se 1 (by rfl) ⟨1285040, by rfl⟩ : syracuseStep 1713387 = 2570081) B2570081
theorem B1713399 : Blo 1713057 1713399 := bstep (se 1 (by rfl) ⟨1285049, by rfl⟩ : syracuseStep 1713399 = 2570099) B2570099
theorem B7324931 : Blo 1713057 7324931 := bstep (se 1 (by rfl) ⟨5493698, by rfl⟩ : syracuseStep 7324931 = 10987397) B10987397
theorem B1713419 : Blo 1713057 1713419 := bstep (se 1 (by rfl) ⟨1285064, by rfl⟩ : syracuseStep 1713419 = 2570129) B2570129
theorem B1713431 : Blo 1713057 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B2745625 : Blo 1713057 2745625 := bstep (se 2 (by rfl) ⟨1029609, by rfl⟩ : syracuseStep 2745625 = 2059219) B2059219
theorem B1713451 : Blo 1713057 1713451 := bstep (se 1 (by rfl) ⟨1285088, by rfl⟩ : syracuseStep 1713451 = 2570177) B2570177
theorem B1713463 : Blo 1713057 1713463 := bstep (se 1 (by rfl) ⟨1285097, by rfl⟩ : syracuseStep 1713463 = 2570195) B2570195
theorem B4883777 : Blo 1713057 4883777 := bstep (se 2 (by rfl) ⟨1831416, by rfl⟩ : syracuseStep 4883777 = 3662833) B3662833
theorem B1713483 : Blo 1713057 1713483 := bstep (se 1 (by rfl) ⟨1285112, by rfl⟩ : syracuseStep 1713483 = 2570225) B2570225
theorem B1713495 : Blo 1713057 1713495 := bstep (se 1 (by rfl) ⟨1285121, by rfl⟩ : syracuseStep 1713495 = 2570243) B2570243
theorem B1713515 : Blo 1713057 1713515 := bstep (se 1 (by rfl) ⟨1285136, by rfl⟩ : syracuseStep 1713515 = 2570273) B2570273
theorem B1713527 : Blo 1713057 1713527 := bstep (se 1 (by rfl) ⟨1285145, by rfl⟩ : syracuseStep 1713527 = 2570291) B2570291
theorem B1713547 : Blo 1713057 1713547 := bstep (se 1 (by rfl) ⟨1285160, by rfl⟩ : syracuseStep 1713547 = 2570321) B2570321
theorem B1713559 : Blo 1713057 1713559 := bstep (se 1 (by rfl) ⟨1285169, by rfl⟩ : syracuseStep 1713559 = 2570339) B2570339
theorem B1713579 : Blo 1713057 1713579 := bstep (se 1 (by rfl) ⟨1285184, by rfl⟩ : syracuseStep 1713579 = 2570369) B2570369
theorem B1713591 : Blo 1713057 1713591 := bstep (se 1 (by rfl) ⟨1285193, by rfl⟩ : syracuseStep 1713591 = 2570387) B2570387
theorem B1713611 : Blo 1713057 1713611 := bstep (se 1 (by rfl) ⟨1285208, by rfl⟩ : syracuseStep 1713611 = 2570417) B2570417
theorem B2893259 : Blo 1713057 2893259 := bstep (se 1 (by rfl) ⟨2169944, by rfl⟩ : syracuseStep 2893259 = 4339889) B4339889
theorem B1713623 : Blo 1713057 1713623 := bstep (se 1 (by rfl) ⟨1285217, by rfl⟩ : syracuseStep 1713623 = 2570435) B2570435
theorem B6178265 : Blo 1713057 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B1713643 : Blo 1713057 1713643 := bstep (se 1 (by rfl) ⟨1285232, by rfl⟩ : syracuseStep 1713643 = 2570465) B2570465
theorem B1713655 : Blo 1713057 1713655 := bstep (se 1 (by rfl) ⟨1285241, by rfl⟩ : syracuseStep 1713655 = 2570483) B2570483
theorem B3712513 : Blo 1713057 3712513 := bstep (se 2 (by rfl) ⟨1392192, by rfl⟩ : syracuseStep 3712513 = 2784385) B2784385
theorem B1713675 : Blo 1713057 1713675 := bstep (se 1 (by rfl) ⟨1285256, by rfl⟩ : syracuseStep 1713675 = 2570513) B2570513
theorem B8676881 : Blo 1713057 8676881 := bstep (se 2 (by rfl) ⟨3253830, by rfl⟩ : syracuseStep 8676881 = 6507661) B6507661
theorem B1713687 : Blo 1713057 1713687 := bstep (se 1 (by rfl) ⟨1285265, by rfl⟩ : syracuseStep 1713687 = 2570531) B2570531
theorem B1713707 : Blo 1713057 1713707 := bstep (se 1 (by rfl) ⟨1285280, by rfl⟩ : syracuseStep 1713707 = 2570561) B2570561
theorem B10978861 : Blo 1713057 10978861 := bstep (se 3 (by rfl) ⟨2058536, by rfl⟩ : syracuseStep 10978861 = 4117073) B4117073
theorem B1713719 : Blo 1713057 1713719 := bstep (se 1 (by rfl) ⟨1285289, by rfl⟩ : syracuseStep 1713719 = 2570579) B2570579
theorem B5563979 : Blo 1713057 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B1713739 : Blo 1713057 1713739 := bstep (se 1 (by rfl) ⟨1285304, by rfl⟩ : syracuseStep 1713739 = 2570609) B2570609
theorem B5490251 : Blo 1713057 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B2893387 : Blo 1713057 2893387 := bstep (se 1 (by rfl) ⟨2170040, by rfl⟩ : syracuseStep 2893387 = 4340081) B4340081
theorem B1713751 : Blo 1713057 1713751 := bstep (se 1 (by rfl) ⟨1285313, by rfl⟩ : syracuseStep 1713751 = 2570627) B2570627
theorem B5785181 : Blo 1713057 5785181 := bstep (se 3 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 5785181 = 2169443) B2169443
theorem B1713771 : Blo 1713057 1713771 := bstep (se 1 (by rfl) ⟨1285328, by rfl⟩ : syracuseStep 1713771 = 2570657) B2570657
theorem B1713783 : Blo 1713057 1713783 := bstep (se 1 (by rfl) ⟨1285337, by rfl⟩ : syracuseStep 1713783 = 2570675) B2570675
theorem B1713803 : Blo 1713057 1713803 := bstep (se 1 (by rfl) ⟨1285352, by rfl⟩ : syracuseStep 1713803 = 2570705) B2570705
theorem B1713815 : Blo 1713057 1713815 := bstep (se 1 (by rfl) ⟨1285361, by rfl⟩ : syracuseStep 1713815 = 2570723) B2570723
theorem B1713835 : Blo 1713057 1713835 := bstep (se 1 (by rfl) ⟨1285376, by rfl⟩ : syracuseStep 1713835 = 2570753) B2570753
theorem B8677043 : Blo 1713057 8677043 := bstep (se 1 (by rfl) ⟨6507782, by rfl⟩ : syracuseStep 8677043 = 13015565) B13015565
theorem B1713847 : Blo 1713057 1713847 := bstep (se 1 (by rfl) ⟨1285385, by rfl⟩ : syracuseStep 1713847 = 2570771) B2570771
theorem B1713867 : Blo 1713057 1713867 := bstep (se 1 (by rfl) ⟨1285400, by rfl⟩ : syracuseStep 1713867 = 2570801) B2570801
theorem B1713879 : Blo 1713057 1713879 := bstep (se 1 (by rfl) ⟨1285409, by rfl⟩ : syracuseStep 1713879 = 2570819) B2570819
theorem B2893529 : Blo 1713057 2893529 := bstep (se 2 (by rfl) ⟨1085073, by rfl⟩ : syracuseStep 2893529 = 2170147) B2170147
theorem B1713899 : Blo 1713057 1713899 := bstep (se 1 (by rfl) ⟨1285424, by rfl⟩ : syracuseStep 1713899 = 2570849) B2570849
theorem B1713911 : Blo 1713057 1713911 := bstep (se 1 (by rfl) ⟨1285433, by rfl⟩ : syracuseStep 1713911 = 2570867) B2570867
theorem B1713931 : Blo 1713057 1713931 := bstep (se 1 (by rfl) ⟨1285448, by rfl⟩ : syracuseStep 1713931 = 2570897) B2570897
theorem B13010705 : Blo 1713057 13010705 := bstep (se 2 (by rfl) ⟨4879014, by rfl⟩ : syracuseStep 13010705 = 9758029) B9758029
theorem B1713943 : Blo 1713057 1713943 := bstep (se 1 (by rfl) ⟨1285457, by rfl⟩ : syracuseStep 1713943 = 2570915) B2570915
theorem B1713963 : Blo 1713057 1713963 := bstep (se 1 (by rfl) ⟨1285472, by rfl⟩ : syracuseStep 1713963 = 2570945) B2570945
theorem B1713975 : Blo 1713057 1713975 := bstep (se 1 (by rfl) ⟨1285481, by rfl⟩ : syracuseStep 1713975 = 2570963) B2570963
theorem B1713995 : Blo 1713057 1713995 := bstep (se 1 (by rfl) ⟨1285496, by rfl⟩ : syracuseStep 1713995 = 2570993) B2570993
theorem B1714007 : Blo 1713057 1714007 := bstep (se 1 (by rfl) ⟨1285505, by rfl⟩ : syracuseStep 1714007 = 2571011) B2571011
theorem B2893657 : Blo 1713057 2893657 := bstep (se 2 (by rfl) ⟨1085121, by rfl⟩ : syracuseStep 2893657 = 2170243) B2170243
theorem B1714027 : Blo 1713057 1714027 := bstep (se 1 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 1714027 = 2571041) B2571041
theorem B1714039 : Blo 1713057 1714039 := bstep (se 1 (by rfl) ⟨1285529, by rfl⟩ : syracuseStep 1714039 = 2571059) B2571059
theorem B1714059 : Blo 1713057 1714059 := bstep (se 1 (by rfl) ⟨1285544, by rfl⟩ : syracuseStep 1714059 = 2571089) B2571089
theorem B1714071 : Blo 1713057 1714071 := bstep (se 1 (by rfl) ⟨1285553, by rfl⟩ : syracuseStep 1714071 = 2571107) B2571107
theorem B1714091 : Blo 1713057 1714091 := bstep (se 1 (by rfl) ⟨1285568, by rfl⟩ : syracuseStep 1714091 = 2571137) B2571137
theorem B3254195 : Blo 1713057 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B1714103 : Blo 1713057 1714103 := bstep (se 1 (by rfl) ⟨1285577, by rfl⟩ : syracuseStep 1714103 = 2571155) B2571155
theorem B1714123 : Blo 1713057 1714123 := bstep (se 1 (by rfl) ⟨1285592, by rfl⟩ : syracuseStep 1714123 = 2571185) B2571185
theorem B1714135 : Blo 1713057 1714135 := bstep (se 1 (by rfl) ⟨1285601, by rfl⟩ : syracuseStep 1714135 = 2571203) B2571203
theorem B1714155 : Blo 1713057 1714155 := bstep (se 1 (by rfl) ⟨1285616, by rfl⟩ : syracuseStep 1714155 = 2571233) B2571233
theorem B1714167 : Blo 1713057 1714167 := bstep (se 1 (by rfl) ⟨1285625, by rfl⟩ : syracuseStep 1714167 = 2571251) B2571251
theorem B1714187 : Blo 1713057 1714187 := bstep (se 1 (by rfl) ⟨1285640, by rfl⟩ : syracuseStep 1714187 = 2571281) B2571281
theorem B1714199 : Blo 1713057 1714199 := bstep (se 1 (by rfl) ⟨1285649, by rfl⟩ : syracuseStep 1714199 = 2571299) B2571299
theorem B1714219 : Blo 1713057 1714219 := bstep (se 1 (by rfl) ⟨1285664, by rfl⟩ : syracuseStep 1714219 = 2571329) B2571329
theorem B4458547 : Blo 1713057 4458547 := bstep (se 1 (by rfl) ⟨3343910, by rfl⟩ : syracuseStep 4458547 = 6687821) B6687821
theorem B1714231 : Blo 1713057 1714231 := bstep (se 1 (by rfl) ⟨1285673, by rfl⟩ : syracuseStep 1714231 = 2571347) B2571347
theorem B3254347 : Blo 1713057 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B1714251 : Blo 1713057 1714251 := bstep (se 1 (by rfl) ⟨1285688, by rfl⟩ : syracuseStep 1714251 = 2571377) B2571377
theorem B1927255 : Blo 1713057 1927255 := bstep (se 1 (by rfl) ⟨1445441, by rfl⟩ : syracuseStep 1927255 = 2890883) B2890883
theorem B1714263 : Blo 1713057 1714263 := bstep (se 1 (by rfl) ⟨1285697, by rfl⟩ : syracuseStep 1714263 = 2571395) B2571395
theorem B1714283 : Blo 1713057 1714283 := bstep (se 1 (by rfl) ⟨1285712, by rfl⟩ : syracuseStep 1714283 = 2571425) B2571425
theorem B1714295 : Blo 1713057 1714295 := bstep (se 1 (by rfl) ⟨1285721, by rfl⟩ : syracuseStep 1714295 = 2571443) B2571443
theorem B1714315 : Blo 1713057 1714315 := bstep (se 1 (by rfl) ⟨1285736, by rfl⟩ : syracuseStep 1714315 = 2571473) B2571473
theorem B1714327 : Blo 1713057 1714327 := bstep (se 1 (by rfl) ⟨1285745, by rfl⟩ : syracuseStep 1714327 = 2571491) B2571491
theorem B1714347 : Blo 1713057 1714347 := bstep (se 1 (by rfl) ⟨1285760, by rfl⟩ : syracuseStep 1714347 = 2571521) B2571521
theorem B6506675 : Blo 1713057 6506675 := bstep (se 1 (by rfl) ⟨4880006, by rfl⟩ : syracuseStep 6506675 = 9760013) B9760013
theorem B1714359 : Blo 1713057 1714359 := bstep (se 1 (by rfl) ⟨1285769, by rfl⟩ : syracuseStep 1714359 = 2571539) B2571539
theorem B6506689 : Blo 1713057 6506689 := bstep (se 2 (by rfl) ⟨2440008, by rfl⟩ : syracuseStep 6506689 = 4880017) B4880017
theorem B1714379 : Blo 1713057 1714379 := bstep (se 1 (by rfl) ⟨1285784, by rfl⟩ : syracuseStep 1714379 = 2571569) B2571569
theorem B1714391 : Blo 1713057 1714391 := bstep (se 1 (by rfl) ⟨1285793, by rfl⟩ : syracuseStep 1714391 = 2571587) B2571587
theorem B1714411 : Blo 1713057 1714411 := bstep (se 1 (by rfl) ⟨1285808, by rfl⟩ : syracuseStep 1714411 = 2571617) B2571617
theorem B1714423 : Blo 1713057 1714423 := bstep (se 1 (by rfl) ⟨1285817, by rfl⟩ : syracuseStep 1714423 = 2571635) B2571635
theorem B1927435 : Blo 1713057 1927435 := bstep (se 1 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 1927435 = 2891153) B2891153
theorem B1714443 : Blo 1713057 1714443 := bstep (se 1 (by rfl) ⟨1285832, by rfl⟩ : syracuseStep 1714443 = 2571665) B2571665
theorem B1714455 : Blo 1713057 1714455 := bstep (se 1 (by rfl) ⟨1285841, by rfl⟩ : syracuseStep 1714455 = 2571683) B2571683
theorem B1714475 : Blo 1713057 1714475 := bstep (se 1 (by rfl) ⟨1285856, by rfl⟩ : syracuseStep 1714475 = 2571713) B2571713
theorem B1714487 : Blo 1713057 1714487 := bstep (se 1 (by rfl) ⟨1285865, by rfl⟩ : syracuseStep 1714487 = 2571731) B2571731
theorem B1714507 : Blo 1713057 1714507 := bstep (se 1 (by rfl) ⟨1285880, by rfl⟩ : syracuseStep 1714507 = 2571761) B2571761
theorem B1714519 : Blo 1713057 1714519 := bstep (se 1 (by rfl) ⟨1285889, by rfl⟩ : syracuseStep 1714519 = 2571779) B2571779
theorem B1714539 : Blo 1713057 1714539 := bstep (se 1 (by rfl) ⟨1285904, by rfl⟩ : syracuseStep 1714539 = 2571809) B2571809
theorem B1927543 : Blo 1713057 1927543 := bstep (se 1 (by rfl) ⟨1445657, by rfl⟩ : syracuseStep 1927543 = 2891315) B2891315
theorem B1714551 : Blo 1713057 1714551 := bstep (se 1 (by rfl) ⟨1285913, by rfl⟩ : syracuseStep 1714551 = 2571827) B2571827
theorem B1714571 : Blo 1713057 1714571 := bstep (se 1 (by rfl) ⟨1285928, by rfl⟩ : syracuseStep 1714571 = 2571857) B2571857
theorem B1714583 : Blo 1713057 1714583 := bstep (se 1 (by rfl) ⟨1285937, by rfl⟩ : syracuseStep 1714583 = 2571875) B2571875
theorem B3254681 : Blo 1713057 3254681 := bstep (se 2 (by rfl) ⟨1220505, by rfl⟩ : syracuseStep 3254681 = 2441011) B2441011
theorem B1714603 : Blo 1713057 1714603 := bstep (se 1 (by rfl) ⟨1285952, by rfl⟩ : syracuseStep 1714603 = 2571905) B2571905
theorem B1714615 : Blo 1713057 1714615 := bstep (se 1 (by rfl) ⟨1285961, by rfl⟩ : syracuseStep 1714615 = 2571923) B2571923
theorem B5491147 : Blo 1713057 5491147 := bstep (se 1 (by rfl) ⟨4118360, by rfl⟩ : syracuseStep 5491147 = 8236721) B8236721
theorem B1714635 : Blo 1713057 1714635 := bstep (se 1 (by rfl) ⟨1285976, by rfl⟩ : syracuseStep 1714635 = 2571953) B2571953
theorem B3910103 : Blo 1713057 3910103 := bstep (se 1 (by rfl) ⟨2932577, by rfl⟩ : syracuseStep 3910103 = 5865155) B5865155
theorem B1714647 : Blo 1713057 1714647 := bstep (se 1 (by rfl) ⟨1285985, by rfl⟩ : syracuseStep 1714647 = 2571971) B2571971
theorem B1714667 : Blo 1713057 1714667 := bstep (se 1 (by rfl) ⟨1286000, by rfl⟩ : syracuseStep 1714667 = 2572001) B2572001
theorem B1714679 : Blo 1713057 1714679 := bstep (se 1 (by rfl) ⟨1286009, by rfl⟩ : syracuseStep 1714679 = 2572019) B2572019
theorem B1714699 : Blo 1713057 1714699 := bstep (se 1 (by rfl) ⟨1286024, by rfl⟩ : syracuseStep 1714699 = 2572049) B2572049
theorem B17582609 : Blo 1713057 17582609 := bstep (se 2 (by rfl) ⟨6593478, by rfl⟩ : syracuseStep 17582609 = 13186957) B13186957
theorem B1714711 : Blo 1713057 1714711 := bstep (se 1 (by rfl) ⟨1286033, by rfl⟩ : syracuseStep 1714711 = 2572067) B2572067
theorem B1927723 : Blo 1713057 1927723 := bstep (se 1 (by rfl) ⟨1445792, by rfl⟩ : syracuseStep 1927723 = 2891585) B2891585
theorem B1714731 : Blo 1713057 1714731 := bstep (se 1 (by rfl) ⟨1286048, by rfl⟩ : syracuseStep 1714731 = 2572097) B2572097
theorem B1714743 : Blo 1713057 1714743 := bstep (se 1 (by rfl) ⟨1286057, by rfl⟩ : syracuseStep 1714743 = 2572115) B2572115
theorem B4336193 : Blo 1713057 4336193 := bstep (se 2 (by rfl) ⟨1626072, by rfl⟩ : syracuseStep 4336193 = 3252145) B3252145
theorem B1714763 : Blo 1713057 1714763 := bstep (se 1 (by rfl) ⟨1286072, by rfl⟩ : syracuseStep 1714763 = 2572145) B2572145
theorem B1714775 : Blo 1713057 1714775 := bstep (se 1 (by rfl) ⟨1286081, by rfl⟩ : syracuseStep 1714775 = 2572163) B2572163
theorem B1714795 : Blo 1713057 1714795 := bstep (se 1 (by rfl) ⟨1286096, by rfl⟩ : syracuseStep 1714795 = 2572193) B2572193
theorem B1714807 : Blo 1713057 1714807 := bstep (se 1 (by rfl) ⟨1286105, by rfl⟩ : syracuseStep 1714807 = 2572211) B2572211
theorem B7318147 : Blo 1713057 7318147 := bstep (se 1 (by rfl) ⟨5488610, by rfl⟩ : syracuseStep 7318147 = 10977221) B10977221
theorem B1714827 : Blo 1713057 1714827 := bstep (se 1 (by rfl) ⟨1286120, by rfl⟩ : syracuseStep 1714827 = 2572241) B2572241
theorem B1927831 : Blo 1713057 1927831 := bstep (se 1 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 1927831 = 2891747) B2891747
theorem B1714839 : Blo 1713057 1714839 := bstep (se 1 (by rfl) ⟨1286129, by rfl⟩ : syracuseStep 1714839 = 2572259) B2572259
theorem B1714859 : Blo 1713057 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B1714871 : Blo 1713057 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B5786315 : Blo 1713057 5786315 := bstep (se 1 (by rfl) ⟨4339736, by rfl⟩ : syracuseStep 5786315 = 8679473) B8679473
theorem B1714891 : Blo 1713057 1714891 := bstep (se 1 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 1714891 = 2572337) B2572337
theorem B1714903 : Blo 1713057 1714903 := bstep (se 1 (by rfl) ⟨1286177, by rfl⟩ : syracuseStep 1714903 = 2572355) B2572355
theorem B1714923 : Blo 1713057 1714923 := bstep (se 1 (by rfl) ⟨1286192, by rfl⟩ : syracuseStep 1714923 = 2572385) B2572385
theorem B1714935 : Blo 1713057 1714935 := bstep (se 1 (by rfl) ⟨1286201, by rfl⟩ : syracuseStep 1714935 = 2572403) B2572403
theorem B1714955 : Blo 1713057 1714955 := bstep (se 1 (by rfl) ⟨1286216, by rfl⟩ : syracuseStep 1714955 = 2572433) B2572433
theorem B1714967 : Blo 1713057 1714967 := bstep (se 1 (by rfl) ⟨1286225, by rfl⟩ : syracuseStep 1714967 = 2572451) B2572451
theorem B13019939 : Blo 1713057 13019939 := bstep (se 1 (by rfl) ⟨9764954, by rfl⟩ : syracuseStep 13019939 = 19529909) B19529909
theorem B1714987 : Blo 1713057 1714987 := bstep (se 1 (by rfl) ⟨1286240, by rfl⟩ : syracuseStep 1714987 = 2572481) B2572481
theorem B1714999 : Blo 1713057 1714999 := bstep (se 1 (by rfl) ⟨1286249, by rfl⟩ : syracuseStep 1714999 = 2572499) B2572499
theorem B1928011 : Blo 1713057 1928011 := bstep (se 1 (by rfl) ⟨1446008, by rfl⟩ : syracuseStep 1928011 = 2892017) B2892017
theorem B1715019 : Blo 1713057 1715019 := bstep (se 1 (by rfl) ⟨1286264, by rfl⟩ : syracuseStep 1715019 = 2572529) B2572529
theorem B1715031 : Blo 1713057 1715031 := bstep (se 1 (by rfl) ⟨1286273, by rfl⟩ : syracuseStep 1715031 = 2572547) B2572547
theorem B1715051 : Blo 1713057 1715051 := bstep (se 1 (by rfl) ⟨1286288, by rfl⟩ : syracuseStep 1715051 = 2572577) B2572577
theorem B3476353 : Blo 1713057 3476353 := bstep (se 2 (by rfl) ⟨1303632, by rfl⟩ : syracuseStep 3476353 = 2607265) B2607265
theorem B1928119 : Blo 1713057 1928119 := bstep (se 1 (by rfl) ⟨1446089, by rfl⟩ : syracuseStep 1928119 = 2892179) B2892179
theorem B7048139 : Blo 1713057 7048139 := bstep (se 1 (by rfl) ⟨5286104, by rfl⟩ : syracuseStep 7048139 = 10572209) B10572209
theorem B5786585 : Blo 1713057 5786585 := bstep (se 2 (by rfl) ⟨2169969, by rfl⟩ : syracuseStep 5786585 = 4339939) B4339939
theorem B9759761 : Blo 1713057 9759761 := bstep (se 2 (by rfl) ⟨3659910, by rfl⟩ : syracuseStep 9759761 = 7319821) B7319821
theorem B3255319 : Blo 1713057 3255319 := bstep (se 1 (by rfl) ⟨2441489, by rfl⟩ : syracuseStep 3255319 = 4882979) B4882979
theorem B5491763 : Blo 1713057 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B1928299 : Blo 1713057 1928299 := bstep (se 1 (by rfl) ⟨1446224, by rfl⟩ : syracuseStep 1928299 = 2892449) B2892449
theorem B5491891 : Blo 1713057 5491891 := bstep (se 1 (by rfl) ⟨4118918, by rfl⟩ : syracuseStep 5491891 = 8237837) B8237837
theorem B1830071 : Blo 1713057 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B12356813 : Blo 1713057 12356813 := bstep (se 3 (by rfl) ⟨2316902, by rfl⟩ : syracuseStep 12356813 = 4633805) B4633805
theorem B1928407 : Blo 1713057 1928407 := bstep (se 1 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 1928407 = 2892611) B2892611
theorem B7048499 : Blo 1713057 7048499 := bstep (se 1 (by rfl) ⟨5286374, by rfl⟩ : syracuseStep 7048499 = 10572749) B10572749
theorem B1928587 : Blo 1713057 1928587 := bstep (se 1 (by rfl) ⟨1446440, by rfl⟩ : syracuseStep 1928587 = 2892881) B2892881
theorem B3911051 : Blo 1713057 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B1928695 : Blo 1713057 1928695 := bstep (se 1 (by rfl) ⟨1446521, by rfl⟩ : syracuseStep 1928695 = 2893043) B2893043
theorem B7319105 : Blo 1713057 7319105 := bstep (se 2 (by rfl) ⟨2744664, by rfl⟩ : syracuseStep 7319105 = 5489329) B5489329
theorem B8678987 : Blo 1713057 8678987 := bstep (se 1 (by rfl) ⟨6509240, by rfl⟩ : syracuseStep 8678987 = 13018481) B13018481
theorem B14650955 : Blo 1713057 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B23449219 : Blo 1713057 23449219 := bstep (se 1 (by rfl) ⟨17586914, by rfl⟩ : syracuseStep 23449219 = 35173829) B35173829
theorem B5787287 : Blo 1713057 5787287 := bstep (se 1 (by rfl) ⟨4340465, by rfl⟩ : syracuseStep 5787287 = 8680931) B8680931
theorem B1928875 : Blo 1713057 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B1928983 : Blo 1713057 1928983 := bstep (se 1 (by rfl) ⟨1446737, by rfl⟩ : syracuseStep 1928983 = 2893475) B2893475
theorem B4337459 : Blo 1713057 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B41783141 : Blo 1713057 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B14274481 : Blo 1713057 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B13897651 : Blo 1713057 13897651 := bstep (se 1 (by rfl) ⟨10423238, by rfl⟩ : syracuseStep 13897651 = 20846477) B20846477
theorem B1929163 : Blo 1713057 1929163 := bstep (se 1 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 1929163 = 2893745) B2893745
theorem B6180887 : Blo 1713057 6180887 := bstep (se 1 (by rfl) ⟨4635665, by rfl⟩ : syracuseStep 6180887 = 9271331) B9271331
theorem B1929271 : Blo 1713057 1929271 := bstep (se 1 (by rfl) ⟨1446953, by rfl⟩ : syracuseStep 1929271 = 2893907) B2893907
theorem B3854411 : Blo 1713057 3854411 := bstep (se 1 (by rfl) ⟨2890808, by rfl⟩ : syracuseStep 3854411 = 5781617) B5781617
theorem B6508619 : Blo 1713057 6508619 := bstep (se 1 (by rfl) ⟨4881464, by rfl⟩ : syracuseStep 6508619 = 9762929) B9762929
theorem B6508633 : Blo 1713057 6508633 := bstep (se 2 (by rfl) ⟨2440737, by rfl⟩ : syracuseStep 6508633 = 4881475) B4881475
theorem B3854465 : Blo 1713057 3854465 := bstep (se 2 (by rfl) ⟨1445424, by rfl⟩ : syracuseStep 3854465 = 2890849) B2890849
theorem B5787827 : Blo 1713057 5787827 := bstep (se 1 (by rfl) ⟨4340870, by rfl⟩ : syracuseStep 5787827 = 8681741) B8681741
theorem B8917265 : Blo 1713057 8917265 := bstep (se 2 (by rfl) ⟨3343974, by rfl⟩ : syracuseStep 8917265 = 6687949) B6687949
theorem B10170689 : Blo 1713057 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B4337995 : Blo 1713057 4337995 := bstep (se 1 (by rfl) ⟨3253496, by rfl⟩ : syracuseStep 4337995 = 6506993) B6506993
theorem B3854681 : Blo 1713057 3854681 := bstep (se 2 (by rfl) ⟨1445505, by rfl⟩ : syracuseStep 3854681 = 2891011) B2891011
theorem B3854771 : Blo 1713057 3854771 := bstep (se 1 (by rfl) ⟨2891078, by rfl⟩ : syracuseStep 3854771 = 5782157) B5782157
theorem B6263219 : Blo 1713057 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B23466419 : Blo 1713057 23466419 := bstep (se 1 (by rfl) ⟨17599814, by rfl⟩ : syracuseStep 23466419 = 35199629) B35199629
theorem B5788097 : Blo 1713057 5788097 := bstep (se 2 (by rfl) ⟨2170536, by rfl⟩ : syracuseStep 5788097 = 4341073) B4341073
theorem B3854807 : Blo 1713057 3854807 := bstep (se 1 (by rfl) ⟨2891105, by rfl⟩ : syracuseStep 3854807 = 5782211) B5782211
theorem B4338137 : Blo 1713057 4338137 := bstep (se 2 (by rfl) ⟨1626801, by rfl⟩ : syracuseStep 4338137 = 3253603) B3253603
theorem B4878913 : Blo 1713057 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B3854987 : Blo 1713057 3854987 := bstep (se 1 (by rfl) ⟨2891240, by rfl⟩ : syracuseStep 3854987 = 5782481) B5782481
theorem B3855041 : Blo 1713057 3855041 := bstep (se 2 (by rfl) ⟨1445640, by rfl⟩ : syracuseStep 3855041 = 2891281) B2891281
theorem B7729937 : Blo 1713057 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B3298163 : Blo 1713057 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B3855257 : Blo 1713057 3855257 := bstep (se 2 (by rfl) ⟨1445721, by rfl⟩ : syracuseStep 3855257 = 2891443) B2891443
theorem B3855347 : Blo 1713057 3855347 := bstep (se 1 (by rfl) ⟨2891510, by rfl⟩ : syracuseStep 3855347 = 5783021) B5783021
theorem B10425361 : Blo 1713057 10425361 := bstep (se 2 (by rfl) ⟨3909510, by rfl⟩ : syracuseStep 10425361 = 7819021) B7819021
theorem B3855383 : Blo 1713057 3855383 := bstep (se 1 (by rfl) ⟨2891537, by rfl⟩ : syracuseStep 3855383 = 5783075) B5783075
theorem B6509591 : Blo 1713057 6509591 := bstep (se 1 (by rfl) ⟨4882193, by rfl⟩ : syracuseStep 6509591 = 9764387) B9764387
theorem B3658817 : Blo 1713057 3658817 := bstep (se 2 (by rfl) ⟨1372056, by rfl⟩ : syracuseStep 3658817 = 2744113) B2744113
theorem B8238145 : Blo 1713057 8238145 := bstep (se 2 (by rfl) ⟨3089304, by rfl⟩ : syracuseStep 8238145 = 6178609) B6178609
theorem B3855563 : Blo 1713057 3855563 := bstep (se 1 (by rfl) ⟨2891672, by rfl⟩ : syracuseStep 3855563 = 5783345) B5783345
theorem B7320779 : Blo 1713057 7320779 := bstep (se 1 (by rfl) ⟨5490584, by rfl⟩ : syracuseStep 7320779 = 10981169) B10981169
theorem B6952139 : Blo 1713057 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B3855617 : Blo 1713057 3855617 := bstep (se 2 (by rfl) ⟨1445856, by rfl⟩ : syracuseStep 3855617 = 2891713) B2891713
theorem B4338967 : Blo 1713057 4338967 := bstep (se 1 (by rfl) ⟨3254225, by rfl⟩ : syracuseStep 4338967 = 6508451) B6508451
theorem B8680769 : Blo 1713057 8680769 := bstep (se 2 (by rfl) ⟨3255288, by rfl⟩ : syracuseStep 8680769 = 6510577) B6510577
theorem B2168203 : Blo 1713057 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B2569625 : Blo 1713057 2569625 := bstep (se 2 (by rfl) ⟨963609, by rfl⟩ : syracuseStep 2569625 = 1927219) B1927219
theorem B17593777 : Blo 1713057 17593777 := bstep (se 2 (by rfl) ⟨6597666, by rfl⟩ : syracuseStep 17593777 = 13195333) B13195333
theorem B3855833 : Blo 1713057 3855833 := bstep (se 2 (by rfl) ⟨1445937, by rfl⟩ : syracuseStep 3855833 = 2891875) B2891875
theorem B2569739 : Blo 1713057 2569739 := bstep (se 1 (by rfl) ⟨1927304, by rfl⟩ : syracuseStep 2569739 = 3854609) B3854609
theorem B2569751 : Blo 1713057 2569751 := bstep (se 1 (by rfl) ⟨1927313, by rfl⟩ : syracuseStep 2569751 = 3854627) B3854627
theorem B3855923 : Blo 1713057 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B13014593 : Blo 1713057 13014593 := bstep (se 2 (by rfl) ⟨4880472, by rfl⟩ : syracuseStep 13014593 = 9760945) B9760945
theorem B12359233 : Blo 1713057 12359233 := bstep (se 2 (by rfl) ⟨4634712, by rfl⟩ : syracuseStep 12359233 = 9269425) B9269425
theorem B3855959 : Blo 1713057 3855959 := bstep (se 1 (by rfl) ⟨2891969, by rfl⟩ : syracuseStep 3855959 = 5783939) B5783939
theorem B2569817 : Blo 1713057 2569817 := bstep (se 2 (by rfl) ⟨963681, by rfl⟩ : syracuseStep 2569817 = 1927363) B1927363
theorem B2168471 : Blo 1713057 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B5863063 : Blo 1713057 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B13186739 : Blo 1713057 13186739 := bstep (se 1 (by rfl) ⟨9890054, by rfl⟩ : syracuseStep 13186739 = 19780109) B19780109
theorem B2569931 : Blo 1713057 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B4339403 : Blo 1713057 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B2569943 : Blo 1713057 2569943 := bstep (se 1 (by rfl) ⟨1927457, by rfl⟩ : syracuseStep 2569943 = 3854915) B3854915
theorem B3299059 : Blo 1713057 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B3856139 : Blo 1713057 3856139 := bstep (se 1 (by rfl) ⟨2892104, by rfl⟩ : syracuseStep 3856139 = 5784209) B5784209
theorem B2570009 : Blo 1713057 2570009 := bstep (se 2 (by rfl) ⟨963753, by rfl⟩ : syracuseStep 2570009 = 1927507) B1927507
theorem B4118323 : Blo 1713057 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B3856193 : Blo 1713057 3856193 := bstep (se 2 (by rfl) ⟨1446072, by rfl⟩ : syracuseStep 3856193 = 2892145) B2892145
theorem B8673155 : Blo 1713057 8673155 := bstep (se 1 (by rfl) ⟨6504866, by rfl⟩ : syracuseStep 8673155 = 13009733) B13009733
theorem B2570123 : Blo 1713057 2570123 := bstep (se 1 (by rfl) ⟨1927592, by rfl⟩ : syracuseStep 2570123 = 3855185) B3855185
theorem B2570135 : Blo 1713057 2570135 := bstep (se 1 (by rfl) ⟨1927601, by rfl⟩ : syracuseStep 2570135 = 3855203) B3855203
theorem B3659671 : Blo 1713057 3659671 := bstep (se 1 (by rfl) ⟨2744753, by rfl⟩ : syracuseStep 3659671 = 5489507) B5489507
theorem B2570201 : Blo 1713057 2570201 := bstep (se 2 (by rfl) ⟨963825, by rfl⟩ : syracuseStep 2570201 = 1927651) B1927651
theorem B3856409 : Blo 1713057 3856409 := bstep (se 2 (by rfl) ⟨1446153, by rfl⟩ : syracuseStep 3856409 = 2892307) B2892307
theorem B4339777 : Blo 1713057 4339777 := bstep (se 2 (by rfl) ⟨1627416, by rfl⟩ : syracuseStep 4339777 = 3254833) B3254833
theorem B2570315 : Blo 1713057 2570315 := bstep (se 1 (by rfl) ⟨1927736, by rfl⟩ : syracuseStep 2570315 = 3855473) B3855473
theorem B2570327 : Blo 1713057 2570327 := bstep (se 1 (by rfl) ⟨1927745, by rfl⟩ : syracuseStep 2570327 = 3855491) B3855491
theorem B3856499 : Blo 1713057 3856499 := bstep (se 1 (by rfl) ⟨2892374, by rfl⟩ : syracuseStep 3856499 = 5784749) B5784749
theorem B15628439 : Blo 1713057 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B3856535 : Blo 1713057 3856535 := bstep (se 1 (by rfl) ⟨2892401, by rfl⟩ : syracuseStep 3856535 = 5784803) B5784803
theorem B2570393 : Blo 1713057 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B4880587 : Blo 1713057 4880587 := bstep (se 1 (by rfl) ⟨3660440, by rfl⟩ : syracuseStep 4880587 = 7320881) B7320881
theorem B5781725 : Blo 1713057 5781725 := bstep (se 3 (by rfl) ⟨1084073, by rfl⟩ : syracuseStep 5781725 = 2168147) B2168147
theorem B6510851 : Blo 1713057 6510851 := bstep (se 1 (by rfl) ⟨4883138, by rfl⟩ : syracuseStep 6510851 = 9766277) B9766277
theorem B15644933 : Blo 1713057 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B2570507 : Blo 1713057 2570507 := bstep (se 1 (by rfl) ⟨1927880, by rfl⟩ : syracuseStep 2570507 = 3855761) B3855761
theorem B7928081 : Blo 1713057 7928081 := bstep (se 2 (by rfl) ⟨2973030, by rfl⟩ : syracuseStep 7928081 = 5946061) B5946061
theorem B11893009 : Blo 1713057 11893009 := bstep (se 2 (by rfl) ⟨4459878, by rfl⟩ : syracuseStep 11893009 = 8919757) B8919757
theorem B2570519 : Blo 1713057 2570519 := bstep (se 1 (by rfl) ⟨1927889, by rfl⟩ : syracuseStep 2570519 = 3855779) B3855779
theorem B3856715 : Blo 1713057 3856715 := bstep (se 1 (by rfl) ⟨2892536, by rfl⟩ : syracuseStep 3856715 = 5785073) B5785073
theorem B2898263 : Blo 1713057 2898263 := bstep (se 1 (by rfl) ⟨2173697, by rfl⟩ : syracuseStep 2898263 = 4347395) B4347395
theorem B2570585 : Blo 1713057 2570585 := bstep (se 2 (by rfl) ⟨963969, by rfl⟩ : syracuseStep 2570585 = 1927939) B1927939
theorem B2169175 : Blo 1713057 2169175 := bstep (se 1 (by rfl) ⟨1626881, by rfl⟩ : syracuseStep 2169175 = 3253763) B3253763
theorem B20855141 : Blo 1713057 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B3856769 : Blo 1713057 3856769 := bstep (se 2 (by rfl) ⟨1446288, by rfl⟩ : syracuseStep 3856769 = 2892577) B2892577
theorem B2570699 : Blo 1713057 2570699 := bstep (se 1 (by rfl) ⟨1928024, by rfl⟩ : syracuseStep 2570699 = 3856049) B3856049
theorem B2570711 : Blo 1713057 2570711 := bstep (se 1 (by rfl) ⟨1928033, by rfl⟩ : syracuseStep 2570711 = 3856067) B3856067
theorem B4880861 : Blo 1713057 4880861 := bstep (se 3 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 4880861 = 1830323) B1830323
theorem B2570777 : Blo 1713057 2570777 := bstep (se 2 (by rfl) ⟨964041, by rfl⟩ : syracuseStep 2570777 = 1928083) B1928083
theorem B3856985 : Blo 1713057 3856985 := bstep (se 2 (by rfl) ⟨1446369, by rfl⟩ : syracuseStep 3856985 = 2892739) B2892739
theorem B9263717 : Blo 1713057 9263717 := bstep (se 4 (by rfl) ⟨868473, by rfl⟩ : syracuseStep 9263717 = 1736947) B1736947
theorem B2570891 : Blo 1713057 2570891 := bstep (se 1 (by rfl) ⟨1928168, by rfl⟩ : syracuseStep 2570891 = 3856337) B3856337
theorem B2570903 : Blo 1713057 2570903 := bstep (se 1 (by rfl) ⟨1928177, by rfl⟩ : syracuseStep 2570903 = 3856355) B3856355
theorem B4340375 : Blo 1713057 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B3857075 : Blo 1713057 3857075 := bstep (se 1 (by rfl) ⟨2892806, by rfl⟩ : syracuseStep 3857075 = 5785613) B5785613
theorem B3300043 : Blo 1713057 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B2439895 : Blo 1713057 2439895 := bstep (se 1 (by rfl) ⟨1829921, by rfl⟩ : syracuseStep 2439895 = 3659843) B3659843
theorem B3857111 : Blo 1713057 3857111 := bstep (se 1 (by rfl) ⟨2892833, by rfl⟩ : syracuseStep 3857111 = 5785667) B5785667
theorem B2570969 : Blo 1713057 2570969 := bstep (se 2 (by rfl) ⟨964113, by rfl⟩ : syracuseStep 2570969 = 1928227) B1928227
theorem B2571083 : Blo 1713057 2571083 := bstep (se 1 (by rfl) ⟨1928312, by rfl⟩ : syracuseStep 2571083 = 3856625) B3856625
theorem B2571095 : Blo 1713057 2571095 := bstep (se 1 (by rfl) ⟨1928321, by rfl⟩ : syracuseStep 2571095 = 3856643) B3856643
theorem B3857291 : Blo 1713057 3857291 := bstep (se 1 (by rfl) ⟨2892968, by rfl⟩ : syracuseStep 3857291 = 5785937) B5785937
theorem B2317195 : Blo 1713057 2317195 := bstep (se 1 (by rfl) ⟨1737896, by rfl⟩ : syracuseStep 2317195 = 3475793) B3475793
theorem B2571161 : Blo 1713057 2571161 := bstep (se 2 (by rfl) ⟨964185, by rfl⟩ : syracuseStep 2571161 = 1928371) B1928371
theorem B3857345 : Blo 1713057 3857345 := bstep (se 2 (by rfl) ⟨1446504, by rfl⟩ : syracuseStep 3857345 = 2893009) B2893009
theorem B2571275 : Blo 1713057 2571275 := bstep (se 1 (by rfl) ⟨1928456, by rfl⟩ : syracuseStep 2571275 = 3856913) B3856913
theorem B2571287 : Blo 1713057 2571287 := bstep (se 1 (by rfl) ⟨1928465, by rfl⟩ : syracuseStep 2571287 = 3856931) B3856931
theorem B3660851 : Blo 1713057 3660851 := bstep (se 1 (by rfl) ⟨2745638, by rfl⟩ : syracuseStep 3660851 = 5491277) B5491277
theorem B2571353 : Blo 1713057 2571353 := bstep (se 2 (by rfl) ⟨964257, by rfl⟩ : syracuseStep 2571353 = 1928515) B1928515
theorem B2890903 : Blo 1713057 2890903 := bstep (se 1 (by rfl) ⟨2168177, by rfl⟩ : syracuseStep 2890903 = 4336355) B4336355
theorem B3857561 : Blo 1713057 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B2571467 : Blo 1713057 2571467 := bstep (se 1 (by rfl) ⟨1928600, by rfl⟩ : syracuseStep 2571467 = 3857201) B3857201
theorem B3087575 : Blo 1713057 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B2571479 : Blo 1713057 2571479 := bstep (se 1 (by rfl) ⟨1928609, by rfl⟩ : syracuseStep 2571479 = 3857219) B3857219
theorem B3857651 : Blo 1713057 3857651 := bstep (se 1 (by rfl) ⟨2893238, by rfl⟩ : syracuseStep 3857651 = 5786477) B5786477
theorem B3087617 : Blo 1713057 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B2440459 : Blo 1713057 2440459 := bstep (se 1 (by rfl) ⟨1830344, by rfl⟩ : syracuseStep 2440459 = 3660689) B3660689
theorem B3857687 : Blo 1713057 3857687 := bstep (se 1 (by rfl) ⟨2893265, by rfl⟩ : syracuseStep 3857687 = 5786531) B5786531
theorem B2571545 : Blo 1713057 2571545 := bstep (se 2 (by rfl) ⟨964329, by rfl⟩ : syracuseStep 2571545 = 1928659) B1928659
theorem B5782859 : Blo 1713057 5782859 := bstep (se 1 (by rfl) ⟨4337144, by rfl⟩ : syracuseStep 5782859 = 8674289) B8674289
theorem B2571659 : Blo 1713057 2571659 := bstep (se 1 (by rfl) ⟨1928744, by rfl⟩ : syracuseStep 2571659 = 3857489) B3857489
theorem B38583701 : Blo 1713057 38583701 := bstep (se 6 (by rfl) ⟨904305, by rfl⟩ : syracuseStep 38583701 = 1808611) B1808611
theorem B2571671 : Blo 1713057 2571671 := bstep (se 1 (by rfl) ⟨1928753, by rfl⟩ : syracuseStep 2571671 = 3857507) B3857507
theorem B4341185 : Blo 1713057 4341185 := bstep (se 2 (by rfl) ⟨1627944, by rfl⟩ : syracuseStep 4341185 = 3255889) B3255889
theorem B3857867 : Blo 1713057 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B13016537 : Blo 1713057 13016537 := bstep (se 2 (by rfl) ⟨4881201, by rfl⟩ : syracuseStep 13016537 = 9762403) B9762403
theorem B2571737 : Blo 1713057 2571737 := bstep (se 2 (by rfl) ⟨964401, by rfl⟩ : syracuseStep 2571737 = 1928803) B1928803
theorem B3857921 : Blo 1713057 3857921 := bstep (se 2 (by rfl) ⟨1446720, by rfl⟩ : syracuseStep 3857921 = 2893441) B2893441
theorem B2571851 : Blo 1713057 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B2571863 : Blo 1713057 2571863 := bstep (se 1 (by rfl) ⟨1928897, by rfl⟩ : syracuseStep 2571863 = 3857795) B3857795
theorem B5783129 : Blo 1713057 5783129 := bstep (se 2 (by rfl) ⟨2168673, by rfl⟩ : syracuseStep 5783129 = 4337347) B4337347
theorem B4947545 : Blo 1713057 4947545 := bstep (se 2 (by rfl) ⟨1855329, by rfl⟩ : syracuseStep 4947545 = 3710659) B3710659
theorem B8347229 : Blo 1713057 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B2571929 : Blo 1713057 2571929 := bstep (se 2 (by rfl) ⟨964473, by rfl⟩ : syracuseStep 2571929 = 1928947) B1928947
theorem B3858137 : Blo 1713057 3858137 := bstep (se 2 (by rfl) ⟨1446801, by rfl⟩ : syracuseStep 3858137 = 2893603) B2893603
theorem B2891531 : Blo 1713057 2891531 := bstep (se 1 (by rfl) ⟨2168648, by rfl⟩ : syracuseStep 2891531 = 4337297) B4337297
theorem B2572043 : Blo 1713057 2572043 := bstep (se 1 (by rfl) ⟨1929032, by rfl⟩ : syracuseStep 2572043 = 3858065) B3858065
theorem B2572055 : Blo 1713057 2572055 := bstep (se 1 (by rfl) ⟨1929041, by rfl⟩ : syracuseStep 2572055 = 3858083) B3858083
theorem B12361517 : Blo 1713057 12361517 := bstep (se 3 (by rfl) ⟨2317784, by rfl⟩ : syracuseStep 12361517 = 4635569) B4635569
theorem B7323443 : Blo 1713057 7323443 := bstep (se 1 (by rfl) ⟨5492582, by rfl⟩ : syracuseStep 7323443 = 10985165) B10985165
theorem B3858227 : Blo 1713057 3858227 := bstep (se 1 (by rfl) ⟨2893670, by rfl⟩ : syracuseStep 3858227 = 5787341) B5787341
theorem B3473239 : Blo 1713057 3473239 := bstep (se 1 (by rfl) ⟨2604929, by rfl⟩ : syracuseStep 3473239 = 5209859) B5209859
theorem B2572121 : Blo 1713057 2572121 := bstep (se 2 (by rfl) ⟨964545, by rfl⟩ : syracuseStep 2572121 = 1929091) B1929091
theorem B3858263 : Blo 1713057 3858263 := bstep (se 1 (by rfl) ⟨2893697, by rfl⟩ : syracuseStep 3858263 = 5787395) B5787395
theorem B17588069 : Blo 1713057 17588069 := bstep (se 4 (by rfl) ⟨1648881, by rfl⟩ : syracuseStep 17588069 = 3297763) B3297763
theorem B2891659 : Blo 1713057 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B7929751 : Blo 1713057 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B4120513 : Blo 1713057 4120513 := bstep (se 2 (by rfl) ⟨1545192, by rfl⟩ : syracuseStep 4120513 = 3090385) B3090385
theorem B2572235 : Blo 1713057 2572235 := bstep (se 1 (by rfl) ⟨1929176, by rfl⟩ : syracuseStep 2572235 = 3858353) B3858353
theorem B2572247 : Blo 1713057 2572247 := bstep (se 1 (by rfl) ⟨1929185, by rfl⟩ : syracuseStep 2572247 = 3858371) B3858371
theorem B2572295 : Blo 1713057 2572295 := bstep (se 1 (by rfl) ⟨1929221, by rfl⟩ : syracuseStep 2572295 = 3858443) B3858443
theorem B4120591 : Blo 1713057 4120591 := bstep (se 1 (by rfl) ⟨3090443, by rfl⟩ : syracuseStep 4120591 = 6180887) B6180887
theorem B2572331 : Blo 1713057 2572331 := bstep (se 1 (by rfl) ⟨1929248, by rfl⟩ : syracuseStep 2572331 = 3858497) B3858497
theorem B2572361 : Blo 1713057 2572361 := bstep (se 2 (by rfl) ⟨964635, by rfl⟩ : syracuseStep 2572361 = 1929271) B1929271
theorem B3858551 : Blo 1713057 3858551 := bstep (se 1 (by rfl) ⟨2893913, by rfl⟩ : syracuseStep 3858551 = 5787827) B5787827
theorem B2441387 : Blo 1713057 2441387 := bstep (se 1 (by rfl) ⟨1831040, by rfl⟩ : syracuseStep 2441387 = 3662081) B3662081
theorem B9756845 : Blo 1713057 9756845 := bstep (se 3 (by rfl) ⟨1829408, by rfl⟩ : syracuseStep 9756845 = 3658817) B3658817
theorem B2572475 : Blo 1713057 2572475 := bstep (se 1 (by rfl) ⟨1929356, by rfl⟩ : syracuseStep 2572475 = 3858713) B3858713
theorem B2572535 : Blo 1713057 2572535 := bstep (se 1 (by rfl) ⟨1929401, by rfl⟩ : syracuseStep 2572535 = 3858803) B3858803
theorem B8675585 : Blo 1713057 8675585 := bstep (se 2 (by rfl) ⟨3253344, by rfl⟩ : syracuseStep 8675585 = 6506689) B6506689
theorem B2572559 : Blo 1713057 2572559 := bstep (se 1 (by rfl) ⟨1929419, by rfl⟩ : syracuseStep 2572559 = 3858839) B3858839
theorem B3858731 : Blo 1713057 3858731 := bstep (se 1 (by rfl) ⟨2894048, by rfl⟩ : syracuseStep 3858731 = 5788097) B5788097
theorem B2892091 : Blo 1713057 2892091 := bstep (se 1 (by rfl) ⟨2169068, by rfl⟩ : syracuseStep 2892091 = 4338137) B4338137
theorem B5783993 : Blo 1713057 5783993 := bstep (se 2 (by rfl) ⟨2168997, by rfl⟩ : syracuseStep 5783993 = 4337995) B4337995
theorem B2892233 : Blo 1713057 2892233 := bstep (se 2 (by rfl) ⟨1084587, by rfl⟩ : syracuseStep 2892233 = 2169175) B2169175
theorem B5153291 : Blo 1713057 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B8233645 : Blo 1713057 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B6505217 : Blo 1713057 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B6505231 : Blo 1713057 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B4883287 : Blo 1713057 4883287 := bstep (se 1 (by rfl) ⟨3662465, by rfl⟩ : syracuseStep 4883287 = 7324931) B7324931
theorem B9757529 : Blo 1713057 9757529 := bstep (se 2 (by rfl) ⟨3659073, by rfl⟩ : syracuseStep 9757529 = 7318147) B7318147
theorem B4400057 : Blo 1713057 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B1713083 : Blo 1713057 1713083 := bstep (se 1 (by rfl) ⟨1284812, by rfl⟩ : syracuseStep 1713083 = 2569625) B2569625
theorem B3253193 : Blo 1713057 3253193 := bstep (se 2 (by rfl) ⟨1219947, by rfl⟩ : syracuseStep 3253193 = 2439895) B2439895
theorem B1713159 : Blo 1713057 1713159 := bstep (se 1 (by rfl) ⟨1284869, by rfl⟩ : syracuseStep 1713159 = 2569739) B2569739
theorem B5784587 : Blo 1713057 5784587 := bstep (se 1 (by rfl) ⟨4338440, by rfl⟩ : syracuseStep 5784587 = 8676881) B8676881
theorem B1713167 : Blo 1713057 1713167 := bstep (se 1 (by rfl) ⟨1284875, by rfl⟩ : syracuseStep 1713167 = 2569751) B2569751
theorem B10429469 : Blo 1713057 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B8676395 : Blo 1713057 8676395 := bstep (se 1 (by rfl) ⟨6507296, by rfl⟩ : syracuseStep 8676395 = 13014593) B13014593
theorem B1713211 : Blo 1713057 1713211 := bstep (se 1 (by rfl) ⟨1284908, by rfl⟩ : syracuseStep 1713211 = 2569817) B2569817
theorem B5784695 : Blo 1713057 5784695 := bstep (se 1 (by rfl) ⟨4338521, by rfl⟩ : syracuseStep 5784695 = 8677043) B8677043
theorem B1713287 : Blo 1713057 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B2892935 : Blo 1713057 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B1713295 : Blo 1713057 1713295 := bstep (se 1 (by rfl) ⟨1284971, by rfl⟩ : syracuseStep 1713295 = 2569943) B2569943
theorem B3089593 : Blo 1713057 3089593 := bstep (se 2 (by rfl) ⟨1158597, by rfl⟩ : syracuseStep 3089593 = 2317195) B2317195
theorem B1713339 : Blo 1713057 1713339 := bstep (se 1 (by rfl) ⟨1285004, by rfl⟩ : syracuseStep 1713339 = 2570009) B2570009
theorem B1713415 : Blo 1713057 1713415 := bstep (se 1 (by rfl) ⟨1285061, by rfl⟩ : syracuseStep 1713415 = 2570123) B2570123
theorem B1713423 : Blo 1713057 1713423 := bstep (se 1 (by rfl) ⟨1285067, by rfl⟩ : syracuseStep 1713423 = 2570135) B2570135
theorem B20841761 : Blo 1713057 20841761 := bstep (se 2 (by rfl) ⟨7815660, by rfl⟩ : syracuseStep 20841761 = 15631321) B15631321
theorem B1713467 : Blo 1713057 1713467 := bstep (se 1 (by rfl) ⟨1285100, by rfl⟩ : syracuseStep 1713467 = 2570201) B2570201
theorem B1713543 : Blo 1713057 1713543 := bstep (se 1 (by rfl) ⟨1285157, by rfl⟩ : syracuseStep 1713543 = 2570315) B2570315
theorem B1713551 : Blo 1713057 1713551 := bstep (se 1 (by rfl) ⟨1285163, by rfl⟩ : syracuseStep 1713551 = 2570327) B2570327
theorem B1713595 : Blo 1713057 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B10429955 : Blo 1713057 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B1713671 : Blo 1713057 1713671 := bstep (se 1 (by rfl) ⟨1285253, by rfl⟩ : syracuseStep 1713671 = 2570507) B2570507
theorem B5285387 : Blo 1713057 5285387 := bstep (se 1 (by rfl) ⟨3964040, by rfl⟩ : syracuseStep 5285387 = 7928081) B7928081
theorem B1713679 : Blo 1713057 1713679 := bstep (se 1 (by rfl) ⟨1285259, by rfl⟩ : syracuseStep 1713679 = 2570519) B2570519
theorem B1713723 : Blo 1713057 1713723 := bstep (se 1 (by rfl) ⟨1285292, by rfl⟩ : syracuseStep 1713723 = 2570585) B2570585
theorem B13903427 : Blo 1713057 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B1713799 : Blo 1713057 1713799 := bstep (se 1 (by rfl) ⟨1285349, by rfl⟩ : syracuseStep 1713799 = 2570699) B2570699
theorem B1713807 : Blo 1713057 1713807 := bstep (se 1 (by rfl) ⟨1285355, by rfl⟩ : syracuseStep 1713807 = 2570711) B2570711
theorem B2606735 : Blo 1713057 2606735 := bstep (se 1 (by rfl) ⟨1955051, by rfl⟩ : syracuseStep 2606735 = 3910103) B3910103
theorem B3253907 : Blo 1713057 3253907 := bstep (se 1 (by rfl) ⟨2440430, by rfl⟩ : syracuseStep 3253907 = 4880861) B4880861
theorem B3253945 : Blo 1713057 3253945 := bstep (se 2 (by rfl) ⟨1220229, by rfl⟩ : syracuseStep 3253945 = 2440459) B2440459
theorem B1713851 : Blo 1713057 1713851 := bstep (se 1 (by rfl) ⟨1285388, by rfl⟩ : syracuseStep 1713851 = 2570777) B2570777
theorem B5785289 : Blo 1713057 5785289 := bstep (se 2 (by rfl) ⟨2169483, by rfl⟩ : syracuseStep 5785289 = 4338967) B4338967
theorem B1713927 : Blo 1713057 1713927 := bstep (se 1 (by rfl) ⟨1285445, by rfl⟩ : syracuseStep 1713927 = 2570891) B2570891
theorem B1713935 : Blo 1713057 1713935 := bstep (se 1 (by rfl) ⟨1285451, by rfl⟩ : syracuseStep 1713935 = 2570903) B2570903
theorem B2893583 : Blo 1713057 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B1713979 : Blo 1713057 1713979 := bstep (se 1 (by rfl) ⟨1285484, by rfl⟩ : syracuseStep 1713979 = 2570969) B2570969
theorem B1714055 : Blo 1713057 1714055 := bstep (se 1 (by rfl) ⟨1285541, by rfl⟩ : syracuseStep 1714055 = 2571083) B2571083
theorem B1714063 : Blo 1713057 1714063 := bstep (se 1 (by rfl) ⟨1285547, by rfl⟩ : syracuseStep 1714063 = 2571095) B2571095
theorem B1714107 : Blo 1713057 1714107 := bstep (se 1 (by rfl) ⟨1285580, by rfl⟩ : syracuseStep 1714107 = 2571161) B2571161
theorem B4950017 : Blo 1713057 4950017 := bstep (se 2 (by rfl) ⟨1856256, by rfl⟩ : syracuseStep 4950017 = 3712513) B3712513
theorem B1714183 : Blo 1713057 1714183 := bstep (se 1 (by rfl) ⟨1285637, by rfl⟩ : syracuseStep 1714183 = 2571275) B2571275
theorem B6506507 : Blo 1713057 6506507 := bstep (se 1 (by rfl) ⟨4879880, by rfl⟩ : syracuseStep 6506507 = 9759761) B9759761
theorem B1714191 : Blo 1713057 1714191 := bstep (se 1 (by rfl) ⟨1285643, by rfl⟩ : syracuseStep 1714191 = 2571287) B2571287
theorem B1714235 : Blo 1713057 1714235 := bstep (se 1 (by rfl) ⟨1285676, by rfl⟩ : syracuseStep 1714235 = 2571353) B2571353
theorem B1714311 : Blo 1713057 1714311 := bstep (se 1 (by rfl) ⟨1285733, by rfl⟩ : syracuseStep 1714311 = 2571467) B2571467
theorem B2058383 : Blo 1713057 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B1714319 : Blo 1713057 1714319 := bstep (se 1 (by rfl) ⟨1285739, by rfl⟩ : syracuseStep 1714319 = 2571479) B2571479
theorem B1714363 : Blo 1713057 1714363 := bstep (se 1 (by rfl) ⟨1285772, by rfl⟩ : syracuseStep 1714363 = 2571545) B2571545
theorem B7817417 : Blo 1713057 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B93833477 : Blo 1713057 93833477 := bstep (se 4 (by rfl) ⟨8796888, by rfl⟩ : syracuseStep 93833477 = 17593777) B17593777
theorem B1714439 : Blo 1713057 1714439 := bstep (se 1 (by rfl) ⟨1285829, by rfl⟩ : syracuseStep 1714439 = 2571659) B2571659
theorem B1714447 : Blo 1713057 1714447 := bstep (se 1 (by rfl) ⟨1285835, by rfl⟩ : syracuseStep 1714447 = 2571671) B2571671
theorem B2894123 : Blo 1713057 2894123 := bstep (se 1 (by rfl) ⟨2170592, by rfl⟩ : syracuseStep 2894123 = 4341185) B4341185
theorem B8677691 : Blo 1713057 8677691 := bstep (se 1 (by rfl) ⟨6508268, by rfl⟩ : syracuseStep 8677691 = 13016537) B13016537
theorem B1714491 : Blo 1713057 1714491 := bstep (se 1 (by rfl) ⟨1285868, by rfl⟩ : syracuseStep 1714491 = 2571737) B2571737
theorem B5785991 : Blo 1713057 5785991 := bstep (se 1 (by rfl) ⟨4339493, by rfl⟩ : syracuseStep 5785991 = 8678987) B8678987
theorem B1714567 : Blo 1713057 1714567 := bstep (se 1 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 1714567 = 2571851) B2571851
theorem B9767303 : Blo 1713057 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B1714575 : Blo 1713057 1714575 := bstep (se 1 (by rfl) ⟨1285931, by rfl⟩ : syracuseStep 1714575 = 2571863) B2571863
theorem B5564819 : Blo 1713057 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B5491097 : Blo 1713057 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B1714619 : Blo 1713057 1714619 := bstep (se 1 (by rfl) ⟨1285964, by rfl⟩ : syracuseStep 1714619 = 2571929) B2571929
theorem B4630985 : Blo 1713057 4630985 := bstep (se 2 (by rfl) ⟨1736619, by rfl⟩ : syracuseStep 4630985 = 3473239) B3473239
theorem B8677853 : Blo 1713057 8677853 := bstep (se 3 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 8677853 = 3254195) B3254195
theorem B1927687 : Blo 1713057 1927687 := bstep (se 1 (by rfl) ⟨1445765, by rfl⟩ : syracuseStep 1927687 = 2891531) B2891531
theorem B1714695 : Blo 1713057 1714695 := bstep (se 1 (by rfl) ⟨1286021, by rfl⟩ : syracuseStep 1714695 = 2572043) B2572043
theorem B1714703 : Blo 1713057 1714703 := bstep (se 1 (by rfl) ⟨1286027, by rfl⟩ : syracuseStep 1714703 = 2572055) B2572055
theorem B18795037 : Blo 1713057 18795037 := bstep (se 3 (by rfl) ⟨3524069, by rfl⟩ : syracuseStep 18795037 = 7048139) B7048139
theorem B1714747 : Blo 1713057 1714747 := bstep (se 1 (by rfl) ⟨1286060, by rfl⟩ : syracuseStep 1714747 = 2572121) B2572121
theorem B19032641 : Blo 1713057 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B11725379 : Blo 1713057 11725379 := bstep (se 1 (by rfl) ⟨8794034, by rfl⟩ : syracuseStep 11725379 = 17588069) B17588069
theorem B27855427 : Blo 1713057 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B1714823 : Blo 1713057 1714823 := bstep (se 1 (by rfl) ⟨1286117, by rfl⟩ : syracuseStep 1714823 = 2572235) B2572235
theorem B1714831 : Blo 1713057 1714831 := bstep (se 1 (by rfl) ⟨1286123, by rfl⟩ : syracuseStep 1714831 = 2572247) B2572247
theorem B1927867 : Blo 1713057 1927867 := bstep (se 1 (by rfl) ⟨1445900, by rfl⟩ : syracuseStep 1927867 = 2891801) B2891801
theorem B1714875 : Blo 1713057 1714875 := bstep (se 1 (by rfl) ⟨1286156, by rfl⟩ : syracuseStep 1714875 = 2572313) B2572313
theorem B5786369 : Blo 1713057 5786369 := bstep (se 2 (by rfl) ⟨2169888, by rfl⟩ : syracuseStep 5786369 = 4339777) B4339777
theorem B1714951 : Blo 1713057 1714951 := bstep (se 1 (by rfl) ⟨1286213, by rfl⟩ : syracuseStep 1714951 = 2572427) B2572427
theorem B1714959 : Blo 1713057 1714959 := bstep (se 1 (by rfl) ⟨1286219, by rfl⟩ : syracuseStep 1714959 = 2572439) B2572439
theorem B8678177 : Blo 1713057 8678177 := bstep (se 2 (by rfl) ⟨3254316, by rfl⟩ : syracuseStep 8678177 = 6508633) B6508633
theorem B16476979 : Blo 1713057 16476979 := bstep (se 1 (by rfl) ⟨12357734, by rfl⟩ : syracuseStep 16476979 = 24715469) B24715469
theorem B3910459 : Blo 1713057 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B1715003 : Blo 1713057 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B4336537 : Blo 1713057 4336537 := bstep (se 2 (by rfl) ⟨1626201, by rfl⟩ : syracuseStep 4336537 = 3252403) B3252403
theorem B6507449 : Blo 1713057 6507449 := bstep (se 2 (by rfl) ⟨2440293, by rfl⟩ : syracuseStep 6507449 = 4880587) B4880587
theorem B41692171 : Blo 1713057 41692171 := bstep (se 1 (by rfl) ⟨31269128, by rfl⟩ : syracuseStep 41692171 = 62538257) B62538257
theorem B4336699 : Blo 1713057 4336699 := bstep (se 1 (by rfl) ⟨3252524, by rfl⟩ : syracuseStep 4336699 = 6505049) B6505049
theorem B1829947 : Blo 1713057 1829947 := bstep (se 1 (by rfl) ⟨1372460, by rfl⟩ : syracuseStep 1829947 = 2744921) B2744921
theorem B1928335 : Blo 1713057 1928335 := bstep (se 1 (by rfl) ⟨1446251, by rfl⟩ : syracuseStep 1928335 = 2892503) B2892503
theorem B4336841 : Blo 1713057 4336841 := bstep (se 2 (by rfl) ⟨1626315, by rfl⟩ : syracuseStep 4336841 = 3252631) B3252631
theorem B125062501 : Blo 1713057 125062501 := bstep (se 4 (by rfl) ⟨11724609, by rfl⟩ : syracuseStep 125062501 = 23449219) B23449219
theorem B18795997 : Blo 1713057 18795997 := bstep (se 3 (by rfl) ⟨3524249, by rfl⟩ : syracuseStep 18795997 = 7048499) B7048499
theorem B7319069 : Blo 1713057 7319069 := bstep (se 3 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 7319069 = 2744651) B2744651
theorem B4337185 : Blo 1713057 4337185 := bstep (se 2 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 4337185 = 3252889) B3252889
theorem B5787179 : Blo 1713057 5787179 := bstep (se 1 (by rfl) ⟨4340384, by rfl⟩ : syracuseStep 5787179 = 8680769) B8680769
theorem B3255851 : Blo 1713057 3255851 := bstep (se 1 (by rfl) ⟨2441888, by rfl⟩ : syracuseStep 3255851 = 4883777) B4883777
theorem B1928839 : Blo 1713057 1928839 := bstep (se 1 (by rfl) ⟨1446629, by rfl⟩ : syracuseStep 1928839 = 2893259) B2893259
theorem B8679149 : Blo 1713057 8679149 := bstep (se 3 (by rfl) ⟨1627340, by rfl⟩ : syracuseStep 8679149 = 3254681) B3254681
theorem B1929019 : Blo 1713057 1929019 := bstep (se 1 (by rfl) ⟨1446764, by rfl⟩ : syracuseStep 1929019 = 2893529) B2893529
theorem B46886957 : Blo 1713057 46886957 := bstep (se 3 (by rfl) ⟨8791304, by rfl⟩ : syracuseStep 46886957 = 17582609) B17582609
theorem B4337783 : Blo 1713057 4337783 := bstep (se 1 (by rfl) ⟨3253337, by rfl⟩ : syracuseStep 4337783 = 6506675) B6506675
theorem B3854483 : Blo 1713057 3854483 := bstep (se 1 (by rfl) ⟨2890862, by rfl⟩ : syracuseStep 3854483 = 5781725) B5781725
theorem B3854537 : Blo 1713057 3854537 := bstep (se 2 (by rfl) ⟨1445451, by rfl⟩ : syracuseStep 3854537 = 2890903) B2890903
theorem B7319753 : Blo 1713057 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B35164637 : Blo 1713057 35164637 := bstep (se 3 (by rfl) ⟨6593369, by rfl⟩ : syracuseStep 35164637 = 13186739) B13186739
theorem B8679959 : Blo 1713057 8679959 := bstep (se 1 (by rfl) ⟨6509969, by rfl⟩ : syracuseStep 8679959 = 13019939) B13019939
theorem B16478977 : Blo 1713057 16478977 := bstep (se 2 (by rfl) ⟨6179616, by rfl⟩ : syracuseStep 16478977 = 12359233) B12359233
theorem B19518245 : Blo 1713057 19518245 := bstep (se 4 (by rfl) ⟨1829835, by rfl⟩ : syracuseStep 19518245 = 3659671) B3659671
theorem B8237875 : Blo 1713057 8237875 := bstep (se 1 (by rfl) ⟨6178406, by rfl⟩ : syracuseStep 8237875 = 12356813) B12356813
theorem B3855239 : Blo 1713057 3855239 := bstep (se 1 (by rfl) ⟨2891429, by rfl⟩ : syracuseStep 3855239 = 5782859) B5782859
theorem B8795101 : Blo 1713057 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B21976069 : Blo 1713057 21976069 := bstep (se 4 (by rfl) ⟨2060256, by rfl⟩ : syracuseStep 21976069 = 4120513) B4120513
theorem B4879403 : Blo 1713057 4879403 := bstep (se 1 (by rfl) ⟨3659552, by rfl⟩ : syracuseStep 4879403 = 7319105) B7319105
theorem B3855419 : Blo 1713057 3855419 := bstep (se 1 (by rfl) ⟨2891564, by rfl⟩ : syracuseStep 3855419 = 5783129) B5783129
theorem B3298363 : Blo 1713057 3298363 := bstep (se 1 (by rfl) ⟨2473772, by rfl⟩ : syracuseStep 3298363 = 4947545) B4947545
theorem B3855545 : Blo 1713057 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B10573001 : Blo 1713057 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B2569607 : Blo 1713057 2569607 := bstep (se 1 (by rfl) ⟨1927205, by rfl⟩ : syracuseStep 2569607 = 3854411) B3854411
theorem B4339079 : Blo 1713057 4339079 := bstep (se 1 (by rfl) ⟨3254309, by rfl⟩ : syracuseStep 4339079 = 6508619) B6508619
theorem B2569643 : Blo 1713057 2569643 := bstep (se 1 (by rfl) ⟨1927232, by rfl⟩ : syracuseStep 2569643 = 3854465) B3854465
theorem B4339129 : Blo 1713057 4339129 := bstep (se 2 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 4339129 = 3254347) B3254347
theorem B2569673 : Blo 1713057 2569673 := bstep (se 2 (by rfl) ⟨963627, by rfl⟩ : syracuseStep 2569673 = 1927255) B1927255
theorem B14636497 : Blo 1713057 14636497 := bstep (se 2 (by rfl) ⟨5488686, by rfl⟩ : syracuseStep 14636497 = 10977373) B10977373
theorem B24696323 : Blo 1713057 24696323 := bstep (se 1 (by rfl) ⟨18522242, by rfl⟩ : syracuseStep 24696323 = 37044485) B37044485
theorem B5944843 : Blo 1713057 5944843 := bstep (se 1 (by rfl) ⟨4458632, by rfl⟩ : syracuseStep 5944843 = 8917265) B8917265
theorem B6510091 : Blo 1713057 6510091 := bstep (se 1 (by rfl) ⟨4882568, by rfl⟩ : syracuseStep 6510091 = 9765137) B9765137
theorem B3855887 : Blo 1713057 3855887 := bstep (se 1 (by rfl) ⟨2891915, by rfl⟩ : syracuseStep 3855887 = 5783831) B5783831
theorem B3855905 : Blo 1713057 3855905 := bstep (se 2 (by rfl) ⟨1445964, by rfl⟩ : syracuseStep 3855905 = 2891929) B2891929
theorem B2569787 : Blo 1713057 2569787 := bstep (se 1 (by rfl) ⟨1927340, by rfl⟩ : syracuseStep 2569787 = 3854681) B3854681
theorem B23778917 : Blo 1713057 23778917 := bstep (se 4 (by rfl) ⟨2229273, by rfl⟩ : syracuseStep 23778917 = 4458547) B4458547
theorem B2569847 : Blo 1713057 2569847 := bstep (se 1 (by rfl) ⟨1927385, by rfl⟩ : syracuseStep 2569847 = 3854771) B3854771
theorem B4175479 : Blo 1713057 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B15644279 : Blo 1713057 15644279 := bstep (se 1 (by rfl) ⟨11733209, by rfl⟩ : syracuseStep 15644279 = 23466419) B23466419
theorem B2569871 : Blo 1713057 2569871 := bstep (se 1 (by rfl) ⟨1927403, by rfl⟩ : syracuseStep 2569871 = 3854807) B3854807
theorem B9262765 : Blo 1713057 9262765 := bstep (se 3 (by rfl) ⟨1736768, by rfl⟩ : syracuseStep 9262765 = 3473537) B3473537
theorem B2569913 : Blo 1713057 2569913 := bstep (se 2 (by rfl) ⟨963717, by rfl⟩ : syracuseStep 2569913 = 1927435) B1927435
theorem B15857345 : Blo 1713057 15857345 := bstep (se 2 (by rfl) ⟨5946504, by rfl⟩ : syracuseStep 15857345 = 11893009) B11893009
theorem B2569991 : Blo 1713057 2569991 := bstep (se 1 (by rfl) ⟨1927493, by rfl⟩ : syracuseStep 2569991 = 3854987) B3854987
theorem B3299105 : Blo 1713057 3299105 := bstep (se 2 (by rfl) ⟨1237164, by rfl⟩ : syracuseStep 3299105 = 2474329) B2474329
theorem B2570027 : Blo 1713057 2570027 := bstep (se 1 (by rfl) ⟨1927520, by rfl⟩ : syracuseStep 2570027 = 3855041) B3855041
theorem B6510395 : Blo 1713057 6510395 := bstep (se 1 (by rfl) ⟨4882796, by rfl⟩ : syracuseStep 6510395 = 9765593) B9765593
theorem B4880189 : Blo 1713057 4880189 := bstep (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) B1830071
theorem B2570057 : Blo 1713057 2570057 := bstep (se 2 (by rfl) ⟨963771, by rfl⟩ : syracuseStep 2570057 = 1927543) B1927543
theorem B3856247 : Blo 1713057 3856247 := bstep (se 1 (by rfl) ⟨2892185, by rfl⟩ : syracuseStep 3856247 = 5784371) B5784371
theorem B7321529 : Blo 1713057 7321529 := bstep (se 2 (by rfl) ⟨2745573, by rfl⟩ : syracuseStep 7321529 = 5491147) B5491147
theorem B2570171 : Blo 1713057 2570171 := bstep (se 1 (by rfl) ⟨1927628, by rfl⟩ : syracuseStep 2570171 = 3855257) B3855257
theorem B2570231 : Blo 1713057 2570231 := bstep (se 1 (by rfl) ⟨1927673, by rfl⟩ : syracuseStep 2570231 = 3855347) B3855347
theorem B2570255 : Blo 1713057 2570255 := bstep (se 1 (by rfl) ⟨1927691, by rfl⟩ : syracuseStep 2570255 = 3855383) B3855383
theorem B4339727 : Blo 1713057 4339727 := bstep (se 1 (by rfl) ⟨3254795, by rfl⟩ : syracuseStep 4339727 = 6509591) B6509591
theorem B3856427 : Blo 1713057 3856427 := bstep (se 1 (by rfl) ⟨2892320, by rfl⟩ : syracuseStep 3856427 = 5784641) B5784641
theorem B2570297 : Blo 1713057 2570297 := bstep (se 2 (by rfl) ⟨963861, by rfl⟩ : syracuseStep 2570297 = 1927723) B1927723
theorem B2570375 : Blo 1713057 2570375 := bstep (se 1 (by rfl) ⟨1927781, by rfl⟩ : syracuseStep 2570375 = 3855563) B3855563
theorem B4880519 : Blo 1713057 4880519 := bstep (se 1 (by rfl) ⟨3660389, by rfl⟩ : syracuseStep 4880519 = 7320779) B7320779
theorem B4634759 : Blo 1713057 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B2570411 : Blo 1713057 2570411 := bstep (se 1 (by rfl) ⟨1927808, by rfl⟩ : syracuseStep 2570411 = 3855617) B3855617
theorem B27121837 : Blo 1713057 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B2570441 : Blo 1713057 2570441 := bstep (se 2 (by rfl) ⟨963915, by rfl⟩ : syracuseStep 2570441 = 1927831) B1927831
theorem B6510881 : Blo 1713057 6510881 := bstep (se 2 (by rfl) ⟨2441580, by rfl⟩ : syracuseStep 6510881 = 4883161) B4883161
theorem B2570555 : Blo 1713057 2570555 := bstep (se 1 (by rfl) ⟨1927916, by rfl⟩ : syracuseStep 2570555 = 3855833) B3855833
theorem B4118843 : Blo 1713057 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B2570615 : Blo 1713057 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B3709319 : Blo 1713057 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B3660167 : Blo 1713057 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B2570639 : Blo 1713057 2570639 := bstep (se 1 (by rfl) ⟨1927979, by rfl⟩ : syracuseStep 2570639 = 3855959) B3855959
theorem B3856787 : Blo 1713057 3856787 := bstep (se 1 (by rfl) ⟨2892590, by rfl⟩ : syracuseStep 3856787 = 5785181) B5785181
theorem B2570681 : Blo 1713057 2570681 := bstep (se 2 (by rfl) ⟨964005, by rfl⟩ : syracuseStep 2570681 = 1928011) B1928011
theorem B3856841 : Blo 1713057 3856841 := bstep (se 2 (by rfl) ⟨1446315, by rfl⟩ : syracuseStep 3856841 = 2892631) B2892631
theorem B4635137 : Blo 1713057 4635137 := bstep (se 2 (by rfl) ⟨1738176, by rfl⟩ : syracuseStep 4635137 = 3476353) B3476353
theorem B2570759 : Blo 1713057 2570759 := bstep (se 1 (by rfl) ⟨1928069, by rfl⟩ : syracuseStep 2570759 = 3856139) B3856139
theorem B8673803 : Blo 1713057 8673803 := bstep (se 1 (by rfl) ⟨6505352, by rfl⟩ : syracuseStep 8673803 = 13010705) B13010705
theorem B2570795 : Blo 1713057 2570795 := bstep (se 1 (by rfl) ⟨1928096, by rfl⟩ : syracuseStep 2570795 = 3856193) B3856193
theorem B2570825 : Blo 1713057 2570825 := bstep (se 2 (by rfl) ⟨964059, by rfl⟩ : syracuseStep 2570825 = 1928119) B1928119
theorem B5782103 : Blo 1713057 5782103 := bstep (se 1 (by rfl) ⟨4336577, by rfl⟩ : syracuseStep 5782103 = 8673155) B8673155
theorem B8673965 : Blo 1713057 8673965 := bstep (se 3 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 8673965 = 3252737) B3252737
theorem B2570939 : Blo 1713057 2570939 := bstep (se 1 (by rfl) ⟨1928204, by rfl⟩ : syracuseStep 2570939 = 3856409) B3856409
theorem B13900481 : Blo 1713057 13900481 := bstep (se 2 (by rfl) ⟨5212680, by rfl⟩ : syracuseStep 13900481 = 10425361) B10425361
theorem B4340425 : Blo 1713057 4340425 := bstep (se 2 (by rfl) ⟨1627659, by rfl⟩ : syracuseStep 4340425 = 3255319) B3255319
theorem B2570999 : Blo 1713057 2570999 := bstep (se 1 (by rfl) ⟨1928249, by rfl⟩ : syracuseStep 2570999 = 3856499) B3856499
theorem B10984193 : Blo 1713057 10984193 := bstep (se 2 (by rfl) ⟨4119072, by rfl⟩ : syracuseStep 10984193 = 8238145) B8238145
theorem B10418959 : Blo 1713057 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B2571023 : Blo 1713057 2571023 := bstep (se 1 (by rfl) ⟨1928267, by rfl⟩ : syracuseStep 2571023 = 3856535) B3856535
theorem B2571065 : Blo 1713057 2571065 := bstep (se 2 (by rfl) ⟨964149, by rfl⟩ : syracuseStep 2571065 = 1928299) B1928299
theorem B4340567 : Blo 1713057 4340567 := bstep (se 1 (by rfl) ⟨3255425, by rfl⟩ : syracuseStep 4340567 = 6510851) B6510851
theorem B2571143 : Blo 1713057 2571143 := bstep (se 1 (by rfl) ⟨1928357, by rfl⟩ : syracuseStep 2571143 = 3856715) B3856715
theorem B1932175 : Blo 1713057 1932175 := bstep (se 1 (by rfl) ⟨1449131, by rfl⟩ : syracuseStep 1932175 = 2898263) B2898263
theorem B7322521 : Blo 1713057 7322521 := bstep (se 2 (by rfl) ⟨2745945, by rfl⟩ : syracuseStep 7322521 = 5491891) B5491891
theorem B2571179 : Blo 1713057 2571179 := bstep (se 1 (by rfl) ⟨1928384, by rfl⟩ : syracuseStep 2571179 = 3856769) B3856769
theorem B2571209 : Blo 1713057 2571209 := bstep (se 2 (by rfl) ⟨964203, by rfl⟩ : syracuseStep 2571209 = 1928407) B1928407
theorem B3660833 : Blo 1713057 3660833 := bstep (se 2 (by rfl) ⟨1372812, by rfl⟩ : syracuseStep 3660833 = 2745625) B2745625
theorem B2890795 : Blo 1713057 2890795 := bstep (se 1 (by rfl) ⟨2168096, by rfl⟩ : syracuseStep 2890795 = 4336193) B4336193
theorem B2571323 : Blo 1713057 2571323 := bstep (se 1 (by rfl) ⟨1928492, by rfl⟩ : syracuseStep 2571323 = 3856985) B3856985
theorem B5782589 : Blo 1713057 5782589 := bstep (se 3 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 5782589 = 2168471) B2168471
theorem B6175811 : Blo 1713057 6175811 := bstep (se 1 (by rfl) ⟨4631858, by rfl⟩ : syracuseStep 6175811 = 9263717) B9263717
theorem B2571383 : Blo 1713057 2571383 := bstep (se 1 (by rfl) ⟨1928537, by rfl⟩ : syracuseStep 2571383 = 3857075) B3857075
theorem B3857543 : Blo 1713057 3857543 := bstep (se 1 (by rfl) ⟨2893157, by rfl⟩ : syracuseStep 3857543 = 5786315) B5786315
theorem B2571407 : Blo 1713057 2571407 := bstep (se 1 (by rfl) ⟨1928555, by rfl⟩ : syracuseStep 2571407 = 3857111) B3857111
theorem B2890937 : Blo 1713057 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B2571449 : Blo 1713057 2571449 := bstep (se 2 (by rfl) ⟨964293, by rfl⟩ : syracuseStep 2571449 = 1928587) B1928587
theorem B6511853 : Blo 1713057 6511853 := bstep (se 3 (by rfl) ⟨1220972, by rfl⟩ : syracuseStep 6511853 = 2441945) B2441945
theorem B2571527 : Blo 1713057 2571527 := bstep (se 1 (by rfl) ⟨1928645, by rfl⟩ : syracuseStep 2571527 = 3857291) B3857291
theorem B2571563 : Blo 1713057 2571563 := bstep (se 1 (by rfl) ⟨1928672, by rfl⟩ : syracuseStep 2571563 = 3857345) B3857345
theorem B3857723 : Blo 1713057 3857723 := bstep (se 1 (by rfl) ⟨2893292, by rfl⟩ : syracuseStep 3857723 = 5786585) B5786585
theorem B2571593 : Blo 1713057 2571593 := bstep (se 2 (by rfl) ⟨964347, by rfl⟩ : syracuseStep 2571593 = 1928695) B1928695
theorem B2440567 : Blo 1713057 2440567 := bstep (se 1 (by rfl) ⟨1830425, by rfl⟩ : syracuseStep 2440567 = 3660851) B3660851
theorem B3661175 : Blo 1713057 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B14638481 : Blo 1713057 14638481 := bstep (se 2 (by rfl) ⟨5489430, by rfl⟩ : syracuseStep 14638481 = 10978861) B10978861
theorem B3857849 : Blo 1713057 3857849 := bstep (se 2 (by rfl) ⟨1446693, by rfl⟩ : syracuseStep 3857849 = 2893387) B2893387
theorem B2571707 : Blo 1713057 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B2571767 : Blo 1713057 2571767 := bstep (se 1 (by rfl) ⟨1928825, by rfl⟩ : syracuseStep 2571767 = 3857651) B3857651
theorem B2571791 : Blo 1713057 2571791 := bstep (se 1 (by rfl) ⟨1928843, by rfl⟩ : syracuseStep 2571791 = 3857687) B3857687
theorem B2571833 : Blo 1713057 2571833 := bstep (se 2 (by rfl) ⟨964437, by rfl⟩ : syracuseStep 2571833 = 1928875) B1928875
theorem B25722467 : Blo 1713057 25722467 := bstep (se 1 (by rfl) ⟨19291850, by rfl⟩ : syracuseStep 25722467 = 38583701) B38583701
theorem B2571911 : Blo 1713057 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B4398745 : Blo 1713057 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B2571947 : Blo 1713057 2571947 := bstep (se 1 (by rfl) ⟨1928960, by rfl⟩ : syracuseStep 2571947 = 3857921) B3857921
theorem B2571977 : Blo 1713057 2571977 := bstep (se 2 (by rfl) ⟨964491, by rfl⟩ : syracuseStep 2571977 = 1928983) B1928983
theorem B3858191 : Blo 1713057 3858191 := bstep (se 1 (by rfl) ⟨2893643, by rfl⟩ : syracuseStep 3858191 = 5787287) B5787287
theorem B3858209 : Blo 1713057 3858209 := bstep (se 2 (by rfl) ⟨1446828, by rfl⟩ : syracuseStep 3858209 = 2893657) B2893657
theorem B2572091 : Blo 1713057 2572091 := bstep (se 1 (by rfl) ⟨1929068, by rfl⟩ : syracuseStep 2572091 = 3858137) B3858137
theorem B8241011 : Blo 1713057 8241011 := bstep (se 1 (by rfl) ⟨6180758, by rfl⟩ : syracuseStep 8241011 = 12361517) B12361517
theorem B2891639 : Blo 1713057 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B4882295 : Blo 1713057 4882295 := bstep (se 1 (by rfl) ⟨3661721, by rfl⟩ : syracuseStep 4882295 = 7323443) B7323443
theorem B2572151 : Blo 1713057 2572151 := bstep (se 1 (by rfl) ⟨1929113, by rfl⟩ : syracuseStep 2572151 = 3858227) B3858227
theorem B2572175 : Blo 1713057 2572175 := bstep (se 1 (by rfl) ⟨1929131, by rfl⟩ : syracuseStep 2572175 = 3858263) B3858263
theorem B18530201 : Blo 1713057 18530201 := bstep (se 2 (by rfl) ⟨6948825, by rfl⟩ : syracuseStep 18530201 = 13897651) B13897651
theorem B2572217 : Blo 1713057 2572217 := bstep (se 2 (by rfl) ⟨964581, by rfl⟩ : syracuseStep 2572217 = 1929163) B1929163
theorem B2891855 : Blo 1713057 2891855 := bstep (se 1 (by rfl) ⟨2168891, by rfl⟩ : syracuseStep 2891855 = 4337783) B4337783
theorem B2572367 : Blo 1713057 2572367 := bstep (se 1 (by rfl) ⟨1929275, by rfl⟩ : syracuseStep 2572367 = 3858551) B3858551
theorem B6504563 : Blo 1713057 6504563 := bstep (se 1 (by rfl) ⟨4878422, by rfl⟩ : syracuseStep 6504563 = 9756845) B9756845
theorem B5783723 : Blo 1713057 5783723 := bstep (se 1 (by rfl) ⟨4337792, by rfl⟩ : syracuseStep 5783723 = 8675585) B8675585
theorem B2572487 : Blo 1713057 2572487 := bstep (se 1 (by rfl) ⟨1929365, by rfl⟩ : syracuseStep 2572487 = 3858731) B3858731
theorem B5489021 : Blo 1713057 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B6505019 : Blo 1713057 6505019 := bstep (se 1 (by rfl) ⟨4878764, by rfl⟩ : syracuseStep 6505019 = 9757529) B9757529
theorem B2933371 : Blo 1713057 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B3252935 : Blo 1713057 3252935 := bstep (se 1 (by rfl) ⟨2439701, by rfl⟩ : syracuseStep 3252935 = 4879403) B4879403
theorem B5784263 : Blo 1713057 5784263 := bstep (se 1 (by rfl) ⟨4338197, by rfl⟩ : syracuseStep 5784263 = 8676395) B8676395
theorem B25060049 : Blo 1713057 25060049 := bstep (se 2 (by rfl) ⟨9397518, by rfl⟩ : syracuseStep 25060049 = 18795037) B18795037
theorem B13894507 : Blo 1713057 13894507 := bstep (se 1 (by rfl) ⟨10420880, by rfl⟩ : syracuseStep 13894507 = 20841761) B20841761
theorem B10978193 : Blo 1713057 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B1713071 : Blo 1713057 1713071 := bstep (se 1 (by rfl) ⟨1284803, by rfl⟩ : syracuseStep 1713071 = 2569607) B2569607
theorem B2892719 : Blo 1713057 2892719 := bstep (se 1 (by rfl) ⟨2169539, by rfl⟩ : syracuseStep 2892719 = 4339079) B4339079
theorem B1713095 : Blo 1713057 1713095 := bstep (se 1 (by rfl) ⟨1284821, by rfl⟩ : syracuseStep 1713095 = 2569643) B2569643
theorem B1713115 : Blo 1713057 1713115 := bstep (se 1 (by rfl) ⟨1284836, by rfl⟩ : syracuseStep 1713115 = 2569673) B2569673
theorem B21971969 : Blo 1713057 21971969 := bstep (se 2 (by rfl) ⟨8239488, by rfl⟩ : syracuseStep 21971969 = 16478977) B16478977
theorem B3523591 : Blo 1713057 3523591 := bstep (se 1 (by rfl) ⟨2642693, by rfl⟩ : syracuseStep 3523591 = 5285387) B5285387
theorem B1713191 : Blo 1713057 1713191 := bstep (se 1 (by rfl) ⟨1284893, by rfl⟩ : syracuseStep 1713191 = 2569787) B2569787
theorem B15852611 : Blo 1713057 15852611 := bstep (se 1 (by rfl) ⟨11889458, by rfl⟩ : syracuseStep 15852611 = 23778917) B23778917
theorem B1713231 : Blo 1713057 1713231 := bstep (se 1 (by rfl) ⟨1284923, by rfl⟩ : syracuseStep 1713231 = 2569847) B2569847
theorem B10429519 : Blo 1713057 10429519 := bstep (se 1 (by rfl) ⟨7822139, by rfl⟩ : syracuseStep 10429519 = 15644279) B15644279
theorem B1713247 : Blo 1713057 1713247 := bstep (se 1 (by rfl) ⟨1284935, by rfl⟩ : syracuseStep 1713247 = 2569871) B2569871
theorem B1737823 : Blo 1713057 1737823 := bstep (se 1 (by rfl) ⟨1303367, by rfl⟩ : syracuseStep 1737823 = 2606735) B2606735
theorem B1713275 : Blo 1713057 1713275 := bstep (se 1 (by rfl) ⟨1284956, by rfl⟩ : syracuseStep 1713275 = 2569913) B2569913
theorem B1713327 : Blo 1713057 1713327 := bstep (se 1 (by rfl) ⟨1284995, by rfl⟩ : syracuseStep 1713327 = 2569991) B2569991
theorem B1713351 : Blo 1713057 1713351 := bstep (se 1 (by rfl) ⟨1285013, by rfl⟩ : syracuseStep 1713351 = 2570027) B2570027
theorem B3253459 : Blo 1713057 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B1713371 : Blo 1713057 1713371 := bstep (se 1 (by rfl) ⟨1285028, by rfl⟩ : syracuseStep 1713371 = 2570057) B2570057
theorem B1713447 : Blo 1713057 1713447 := bstep (se 1 (by rfl) ⟨1285085, by rfl⟩ : syracuseStep 1713447 = 2570171) B2570171
theorem B1713487 : Blo 1713057 1713487 := bstep (se 1 (by rfl) ⟨1285115, by rfl⟩ : syracuseStep 1713487 = 2570231) B2570231
theorem B1713503 : Blo 1713057 1713503 := bstep (se 1 (by rfl) ⟨1285127, by rfl⟩ : syracuseStep 1713503 = 2570255) B2570255
theorem B2893151 : Blo 1713057 2893151 := bstep (se 1 (by rfl) ⟨2169863, by rfl⟩ : syracuseStep 2893151 = 4339727) B4339727
theorem B1713531 : Blo 1713057 1713531 := bstep (se 1 (by rfl) ⟨1285148, by rfl⟩ : syracuseStep 1713531 = 2570297) B2570297
theorem B1713583 : Blo 1713057 1713583 := bstep (se 1 (by rfl) ⟨1285187, by rfl⟩ : syracuseStep 1713583 = 2570375) B2570375
theorem B3253679 : Blo 1713057 3253679 := bstep (se 1 (by rfl) ⟨2440259, by rfl⟩ : syracuseStep 3253679 = 4880519) B4880519
theorem B3089839 : Blo 1713057 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B1713607 : Blo 1713057 1713607 := bstep (se 1 (by rfl) ⟨1285205, by rfl⟩ : syracuseStep 1713607 = 2570411) B2570411
theorem B1713627 : Blo 1713057 1713627 := bstep (se 1 (by rfl) ⟨1285220, by rfl⟩ : syracuseStep 1713627 = 2570441) B2570441
theorem B5211611 : Blo 1713057 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B62555651 : Blo 1713057 62555651 := bstep (se 1 (by rfl) ⟨46916738, by rfl⟩ : syracuseStep 62555651 = 93833477) B93833477
theorem B1713703 : Blo 1713057 1713703 := bstep (se 1 (by rfl) ⟨1285277, by rfl⟩ : syracuseStep 1713703 = 2570555) B2570555
theorem B5785127 : Blo 1713057 5785127 := bstep (se 1 (by rfl) ⟨4338845, by rfl⟩ : syracuseStep 5785127 = 8677691) B8677691
theorem B2745895 : Blo 1713057 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B1713743 : Blo 1713057 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B1713759 : Blo 1713057 1713759 := bstep (se 1 (by rfl) ⟨1285319, by rfl⟩ : syracuseStep 1713759 = 2570639) B2570639
theorem B1713787 : Blo 1713057 1713787 := bstep (se 1 (by rfl) ⟨1285340, by rfl⟩ : syracuseStep 1713787 = 2570681) B2570681
theorem B5785235 : Blo 1713057 5785235 := bstep (se 1 (by rfl) ⟨4338926, by rfl⟩ : syracuseStep 5785235 = 8677853) B8677853
theorem B3090091 : Blo 1713057 3090091 := bstep (se 1 (by rfl) ⟨2317568, by rfl⟩ : syracuseStep 3090091 = 4635137) B4635137
theorem B1713839 : Blo 1713057 1713839 := bstep (se 1 (by rfl) ⟨1285379, by rfl⟩ : syracuseStep 1713839 = 2570759) B2570759
theorem B1713863 : Blo 1713057 1713863 := bstep (se 1 (by rfl) ⟨1285397, by rfl⟩ : syracuseStep 1713863 = 2570795) B2570795
theorem B7816919 : Blo 1713057 7816919 := bstep (se 1 (by rfl) ⟨5862689, by rfl⟩ : syracuseStep 7816919 = 11725379) B11725379
theorem B1713883 : Blo 1713057 1713883 := bstep (se 1 (by rfl) ⟨1285412, by rfl⟩ : syracuseStep 1713883 = 2570825) B2570825
theorem B1713959 : Blo 1713057 1713959 := bstep (se 1 (by rfl) ⟨1285469, by rfl⟩ : syracuseStep 1713959 = 2570939) B2570939
theorem B9266987 : Blo 1713057 9266987 := bstep (se 1 (by rfl) ⟨6950240, by rfl⟩ : syracuseStep 9266987 = 13900481) B13900481
theorem B166750001 : Blo 1713057 166750001 := bstep (se 2 (by rfl) ⟨62531250, by rfl⟩ : syracuseStep 166750001 = 125062501) B125062501
theorem B3254089 : Blo 1713057 3254089 := bstep (se 2 (by rfl) ⟨1220283, by rfl⟩ : syracuseStep 3254089 = 2440567) B2440567
theorem B1713999 : Blo 1713057 1713999 := bstep (se 1 (by rfl) ⟨1285499, by rfl⟩ : syracuseStep 1713999 = 2570999) B2570999
theorem B1714015 : Blo 1713057 1714015 := bstep (se 1 (by rfl) ⟨1285511, by rfl⟩ : syracuseStep 1714015 = 2571023) B2571023
theorem B5785451 : Blo 1713057 5785451 := bstep (se 1 (by rfl) ⟨4339088, by rfl⟩ : syracuseStep 5785451 = 8678177) B8678177
theorem B1714043 : Blo 1713057 1714043 := bstep (se 1 (by rfl) ⟨1285532, by rfl⟩ : syracuseStep 1714043 = 2571065) B2571065
theorem B2893711 : Blo 1713057 2893711 := bstep (se 1 (by rfl) ⟨2170283, by rfl⟩ : syracuseStep 2893711 = 4340567) B4340567
theorem B5785505 : Blo 1713057 5785505 := bstep (se 2 (by rfl) ⟨2169564, by rfl⟩ : syracuseStep 5785505 = 4339129) B4339129
theorem B1714095 : Blo 1713057 1714095 := bstep (se 1 (by rfl) ⟨1285571, by rfl⟩ : syracuseStep 1714095 = 2571143) B2571143
theorem B19515329 : Blo 1713057 19515329 := bstep (se 2 (by rfl) ⟨7318248, by rfl⟩ : syracuseStep 19515329 = 14636497) B14636497
theorem B1714119 : Blo 1713057 1714119 := bstep (se 1 (by rfl) ⟨1285589, by rfl⟩ : syracuseStep 1714119 = 2571179) B2571179
theorem B25061329 : Blo 1713057 25061329 := bstep (se 2 (by rfl) ⟨9397998, by rfl⟩ : syracuseStep 25061329 = 18795997) B18795997
theorem B1714139 : Blo 1713057 1714139 := bstep (se 1 (by rfl) ⟨1285604, by rfl⟩ : syracuseStep 1714139 = 2571209) B2571209
theorem B1714215 : Blo 1713057 1714215 := bstep (se 1 (by rfl) ⟨1285661, by rfl⟩ : syracuseStep 1714215 = 2571323) B2571323
theorem B1714255 : Blo 1713057 1714255 := bstep (se 1 (by rfl) ⟨1285691, by rfl⟩ : syracuseStep 1714255 = 2571383) B2571383
theorem B1714271 : Blo 1713057 1714271 := bstep (se 1 (by rfl) ⟨1285703, by rfl⟩ : syracuseStep 1714271 = 2571407) B2571407
theorem B1927291 : Blo 1713057 1927291 := bstep (se 1 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 1927291 = 2890937) B2890937
theorem B1714299 : Blo 1713057 1714299 := bstep (se 1 (by rfl) ⟨1285724, by rfl⟩ : syracuseStep 1714299 = 2571449) B2571449
theorem B1714351 : Blo 1713057 1714351 := bstep (se 1 (by rfl) ⟨1285763, by rfl⟩ : syracuseStep 1714351 = 2571527) B2571527
theorem B1714375 : Blo 1713057 1714375 := bstep (se 1 (by rfl) ⟨1285781, by rfl⟩ : syracuseStep 1714375 = 2571563) B2571563
theorem B1714395 : Blo 1713057 1714395 := bstep (se 1 (by rfl) ⟨1285796, by rfl⟩ : syracuseStep 1714395 = 2571593) B2571593
theorem B9758987 : Blo 1713057 9758987 := bstep (se 1 (by rfl) ⟨7319240, by rfl⟩ : syracuseStep 9758987 = 14638481) B14638481
theorem B1714471 : Blo 1713057 1714471 := bstep (se 1 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 1714471 = 2571707) B2571707
theorem B13019453 : Blo 1713057 13019453 := bstep (se 3 (by rfl) ⟨2441147, by rfl⟩ : syracuseStep 13019453 = 4882295) B4882295
theorem B1714511 : Blo 1713057 1714511 := bstep (se 1 (by rfl) ⟨1285883, by rfl⟩ : syracuseStep 1714511 = 2571767) B2571767
theorem B1714527 : Blo 1713057 1714527 := bstep (se 1 (by rfl) ⟨1285895, by rfl⟩ : syracuseStep 1714527 = 2571791) B2571791
theorem B1714555 : Blo 1713057 1714555 := bstep (se 1 (by rfl) ⟨1285916, by rfl⟩ : syracuseStep 1714555 = 2571833) B2571833
theorem B17148311 : Blo 1713057 17148311 := bstep (se 1 (by rfl) ⟨12861233, by rfl⟩ : syracuseStep 17148311 = 25722467) B25722467
theorem B1714607 : Blo 1713057 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B1714631 : Blo 1713057 1714631 := bstep (se 1 (by rfl) ⟨1285973, by rfl⟩ : syracuseStep 1714631 = 2571947) B2571947
theorem B1714651 : Blo 1713057 1714651 := bstep (se 1 (by rfl) ⟨1285988, by rfl⟩ : syracuseStep 1714651 = 2571977) B2571977
theorem B19524077 : Blo 1713057 19524077 := bstep (se 3 (by rfl) ⟨3660764, by rfl⟩ : syracuseStep 19524077 = 7321529) B7321529
theorem B5786099 : Blo 1713057 5786099 := bstep (se 1 (by rfl) ⟨4339574, by rfl⟩ : syracuseStep 5786099 = 8679149) B8679149
theorem B1714727 : Blo 1713057 1714727 := bstep (se 1 (by rfl) ⟨1286045, by rfl⟩ : syracuseStep 1714727 = 2572091) B2572091
theorem B1927759 : Blo 1713057 1927759 := bstep (se 1 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 1927759 = 2891639) B2891639
theorem B1714767 : Blo 1713057 1714767 := bstep (se 1 (by rfl) ⟨1286075, by rfl⟩ : syracuseStep 1714767 = 2572151) B2572151
theorem B1714783 : Blo 1713057 1714783 := bstep (se 1 (by rfl) ⟨1286087, by rfl⟩ : syracuseStep 1714783 = 2572175) B2572175
theorem B1714811 : Blo 1713057 1714811 := bstep (se 1 (by rfl) ⟨1286108, by rfl⟩ : syracuseStep 1714811 = 2572217) B2572217
theorem B1714863 : Blo 1713057 1714863 := bstep (se 1 (by rfl) ⟨1286147, by rfl⟩ : syracuseStep 1714863 = 2572295) B2572295
theorem B1714887 : Blo 1713057 1714887 := bstep (se 1 (by rfl) ⟨1286165, by rfl⟩ : syracuseStep 1714887 = 2572331) B2572331
theorem B1714907 : Blo 1713057 1714907 := bstep (se 1 (by rfl) ⟨1286180, by rfl⟩ : syracuseStep 1714907 = 2572361) B2572361
theorem B31705829 : Blo 1713057 31705829 := bstep (se 4 (by rfl) ⟨2972421, by rfl⟩ : syracuseStep 31705829 = 5944843) B5944843
theorem B1714983 : Blo 1713057 1714983 := bstep (se 1 (by rfl) ⟨1286237, by rfl⟩ : syracuseStep 1714983 = 2572475) B2572475
theorem B1715023 : Blo 1713057 1715023 := bstep (se 1 (by rfl) ⟨1286267, by rfl⟩ : syracuseStep 1715023 = 2572535) B2572535
theorem B16468829 : Blo 1713057 16468829 := bstep (se 3 (by rfl) ⟨3087905, by rfl⟩ : syracuseStep 16468829 = 6175811) B6175811
theorem B1715039 : Blo 1713057 1715039 := bstep (se 1 (by rfl) ⟨1286279, by rfl⟩ : syracuseStep 1715039 = 2572559) B2572559
theorem B36162449 : Blo 1713057 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B1928155 : Blo 1713057 1928155 := bstep (se 1 (by rfl) ⟨1446116, by rfl⟩ : syracuseStep 1928155 = 2892233) B2892233
theorem B17591269 : Blo 1713057 17591269 := bstep (se 4 (by rfl) ⟨1649181, by rfl⟩ : syracuseStep 17591269 = 3298363) B3298363
theorem B3435527 : Blo 1713057 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B5786639 : Blo 1713057 5786639 := bstep (se 1 (by rfl) ⟨4339979, by rfl⟩ : syracuseStep 5786639 = 8679959) B8679959
theorem B4336811 : Blo 1713057 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B13012163 : Blo 1713057 13012163 := bstep (se 1 (by rfl) ⟨9759122, by rfl⟩ : syracuseStep 13012163 = 19518245) B19518245
theorem B1928623 : Blo 1713057 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B7048667 : Blo 1713057 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B49401413 : Blo 1713057 49401413 := bstep (se 4 (by rfl) ⟨4631382, by rfl⟩ : syracuseStep 49401413 = 9262765) B9262765
theorem B5787233 : Blo 1713057 5787233 := bstep (se 2 (by rfl) ⟨2170212, by rfl⟩ : syracuseStep 5787233 = 4340425) B4340425
theorem B16477829 : Blo 1713057 16477829 := bstep (se 4 (by rfl) ⟨1544796, by rfl⟩ : syracuseStep 16477829 = 3089593) B3089593
theorem B9891517 : Blo 1713057 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B9760445 : Blo 1713057 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B9268951 : Blo 1713057 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B14839517 : Blo 1713057 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B5213945 : Blo 1713057 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B10571563 : Blo 1713057 10571563 := bstep (se 1 (by rfl) ⟨7928672, by rfl⟩ : syracuseStep 10571563 = 15857345) B15857345
theorem B1929055 : Blo 1713057 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B2576233 : Blo 1713057 2576233 := bstep (se 2 (by rfl) ⟨966087, by rfl⟩ : syracuseStep 2576233 = 1932175) B1932175
theorem B2199403 : Blo 1713057 2199403 := bstep (se 1 (by rfl) ⟨1649552, by rfl⟩ : syracuseStep 2199403 = 3299105) B3299105
theorem B11726801 : Blo 1713057 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B4337671 : Blo 1713057 4337671 := bstep (se 1 (by rfl) ⟨3253253, by rfl⟩ : syracuseStep 4337671 = 6506507) B6506507
theorem B3854393 : Blo 1713057 3854393 := bstep (se 2 (by rfl) ⟨1445397, by rfl⟩ : syracuseStep 3854393 = 2890795) B2890795
theorem B1929415 : Blo 1713057 1929415 := bstep (se 1 (by rfl) ⟨1447061, by rfl⟩ : syracuseStep 1929415 = 2894123) B2894123
theorem B3854735 : Blo 1713057 3854735 := bstep (se 1 (by rfl) ⟨2891051, by rfl⟩ : syracuseStep 3854735 = 5782103) B5782103
theorem B4338299 : Blo 1713057 4338299 := bstep (se 1 (by rfl) ⟨3253724, by rfl⟩ : syracuseStep 4338299 = 6507449) B6507449
theorem B8680121 : Blo 1713057 8680121 := bstep (se 2 (by rfl) ⟨3255045, by rfl⟩ : syracuseStep 8680121 = 6510091) B6510091
theorem B3855059 : Blo 1713057 3855059 := bstep (se 1 (by rfl) ⟨2891294, by rfl⟩ : syracuseStep 3855059 = 5782589) B5782589
theorem B5567305 : Blo 1713057 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B4338593 : Blo 1713057 4338593 := bstep (se 2 (by rfl) ⟨1626972, by rfl⟩ : syracuseStep 4338593 = 3253945) B3253945
theorem B4879379 : Blo 1713057 4879379 := bstep (se 1 (by rfl) ⟨3659534, by rfl⟩ : syracuseStep 4879379 = 7319069) B7319069
theorem B5494007 : Blo 1713057 5494007 := bstep (se 1 (by rfl) ⟨4120505, by rfl⟩ : syracuseStep 5494007 = 8241011) B8241011
theorem B5494121 : Blo 1713057 5494121 := bstep (se 2 (by rfl) ⟨2060295, by rfl⟩ : syracuseStep 5494121 = 4120591) B4120591
theorem B31257971 : Blo 1713057 31257971 := bstep (se 1 (by rfl) ⟨23443478, by rfl⟩ : syracuseStep 31257971 = 46886957) B46886957
theorem B9762221 : Blo 1713057 9762221 := bstep (se 3 (by rfl) ⟨1830416, by rfl⟩ : syracuseStep 9762221 = 3660833) B3660833
theorem B2569655 : Blo 1713057 2569655 := bstep (se 1 (by rfl) ⟨1927241, by rfl⟩ : syracuseStep 2569655 = 3854483) B3854483
theorem B2569691 : Blo 1713057 2569691 := bstep (se 1 (by rfl) ⟨1927268, by rfl⟩ : syracuseStep 2569691 = 3854537) B3854537
theorem B4879835 : Blo 1713057 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B3855995 : Blo 1713057 3855995 := bstep (se 1 (by rfl) ⟨2891996, by rfl⟩ : syracuseStep 3855995 = 5783993) B5783993
theorem B23443091 : Blo 1713057 23443091 := bstep (se 1 (by rfl) ⟨17582318, by rfl⟩ : syracuseStep 23443091 = 35164637) B35164637
theorem B3856121 : Blo 1713057 3856121 := bstep (se 2 (by rfl) ⟨1446045, by rfl⟩ : syracuseStep 3856121 = 2892091) B2892091
theorem B6510365 : Blo 1713057 6510365 := bstep (se 3 (by rfl) ⟨1220693, by rfl⟩ : syracuseStep 6510365 = 2441387) B2441387
theorem B2570159 : Blo 1713057 2570159 := bstep (se 1 (by rfl) ⟨1927619, by rfl⟩ : syracuseStep 2570159 = 3855239) B3855239
theorem B2168795 : Blo 1713057 2168795 := bstep (se 1 (by rfl) ⟨1626596, by rfl⟩ : syracuseStep 2168795 = 3253193) B3253193
theorem B3856391 : Blo 1713057 3856391 := bstep (se 1 (by rfl) ⟨2892293, by rfl⟩ : syracuseStep 3856391 = 5784587) B5784587
theorem B2570249 : Blo 1713057 2570249 := bstep (se 2 (by rfl) ⟨963843, by rfl⟩ : syracuseStep 2570249 = 1927687) B1927687
theorem B6952979 : Blo 1713057 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B2570279 : Blo 1713057 2570279 := bstep (se 1 (by rfl) ⟨1927709, by rfl⟩ : syracuseStep 2570279 = 3855419) B3855419
theorem B3856463 : Blo 1713057 3856463 := bstep (se 1 (by rfl) ⟨2892347, by rfl⟩ : syracuseStep 3856463 = 5784695) B5784695
theorem B37140569 : Blo 1713057 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B2570363 : Blo 1713057 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B2570489 : Blo 1713057 2570489 := bstep (se 2 (by rfl) ⟨963933, by rfl⟩ : syracuseStep 2570489 = 1927867) B1927867
theorem B16464215 : Blo 1713057 16464215 := bstep (se 1 (by rfl) ⟨12348161, by rfl⟩ : syracuseStep 16464215 = 24696323) B24696323
theorem B6953303 : Blo 1713057 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B2570591 : Blo 1713057 2570591 := bstep (se 1 (by rfl) ⟨1927943, by rfl⟩ : syracuseStep 2570591 = 3855887) B3855887
theorem B13891945 : Blo 1713057 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B8673641 : Blo 1713057 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B2570603 : Blo 1713057 2570603 := bstep (se 1 (by rfl) ⟨1927952, by rfl⟩ : syracuseStep 2570603 = 3855905) B3855905
theorem B10983833 : Blo 1713057 10983833 := bstep (se 2 (by rfl) ⟨4118937, by rfl⟩ : syracuseStep 10983833 = 8237875) B8237875
theorem B21969305 : Blo 1713057 21969305 := bstep (se 2 (by rfl) ⟨8238489, by rfl⟩ : syracuseStep 21969305 = 16476979) B16476979
theorem B2169271 : Blo 1713057 2169271 := bstep (se 1 (by rfl) ⟨1626953, by rfl⟩ : syracuseStep 2169271 = 3253907) B3253907
theorem B6511049 : Blo 1713057 6511049 := bstep (se 2 (by rfl) ⟨2441643, by rfl⟩ : syracuseStep 6511049 = 4883287) B4883287
theorem B3856859 : Blo 1713057 3856859 := bstep (se 1 (by rfl) ⟨2892644, by rfl⟩ : syracuseStep 3856859 = 5785289) B5785289
theorem B5782049 : Blo 1713057 5782049 := bstep (se 2 (by rfl) ⟨2168268, by rfl⟩ : syracuseStep 5782049 = 4336537) B4336537
theorem B9763361 : Blo 1713057 9763361 := bstep (se 2 (by rfl) ⟨3661260, by rfl⟩ : syracuseStep 9763361 = 7322521) B7322521
theorem B4340263 : Blo 1713057 4340263 := bstep (se 1 (by rfl) ⟨3255197, by rfl⟩ : syracuseStep 4340263 = 6510395) B6510395
theorem B2570831 : Blo 1713057 2570831 := bstep (se 1 (by rfl) ⟨1928123, by rfl⟩ : syracuseStep 2570831 = 3856247) B3856247
theorem B3300011 : Blo 1713057 3300011 := bstep (se 1 (by rfl) ⟨2475008, by rfl⟩ : syracuseStep 3300011 = 4950017) B4950017
theorem B29301425 : Blo 1713057 29301425 := bstep (se 2 (by rfl) ⟨10988034, by rfl⟩ : syracuseStep 29301425 = 21976069) B21976069
theorem B55589561 : Blo 1713057 55589561 := bstep (se 2 (by rfl) ⟨20846085, by rfl⟩ : syracuseStep 55589561 = 41692171) B41692171
theorem B2570951 : Blo 1713057 2570951 := bstep (se 1 (by rfl) ⟨1928213, by rfl⟩ : syracuseStep 2570951 = 3856427) B3856427
theorem B5782265 : Blo 1713057 5782265 := bstep (se 2 (by rfl) ⟨2168349, by rfl⟩ : syracuseStep 5782265 = 4336699) B4336699
theorem B2439929 : Blo 1713057 2439929 := bstep (se 2 (by rfl) ⟨914973, by rfl⟩ : syracuseStep 2439929 = 1829947) B1829947
theorem B2571113 : Blo 1713057 2571113 := bstep (se 2 (by rfl) ⟨964167, by rfl⟩ : syracuseStep 2571113 = 1928335) B1928335
theorem B4340587 : Blo 1713057 4340587 := bstep (se 1 (by rfl) ⟨3255440, by rfl⟩ : syracuseStep 4340587 = 6510881) B6510881
theorem B3857327 : Blo 1713057 3857327 := bstep (se 1 (by rfl) ⟨2892995, by rfl⟩ : syracuseStep 3857327 = 5785991) B5785991
theorem B6511535 : Blo 1713057 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B2571191 : Blo 1713057 2571191 := bstep (se 1 (by rfl) ⟨1928393, by rfl⟩ : syracuseStep 2571191 = 3856787) B3856787
theorem B3660731 : Blo 1713057 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B3087323 : Blo 1713057 3087323 := bstep (se 1 (by rfl) ⟨2315492, by rfl⟩ : syracuseStep 3087323 = 4630985) B4630985
theorem B2571227 : Blo 1713057 2571227 := bstep (se 1 (by rfl) ⟨1928420, by rfl⟩ : syracuseStep 2571227 = 3856841) B3856841
theorem B5782535 : Blo 1713057 5782535 := bstep (se 1 (by rfl) ⟨4336901, by rfl⟩ : syracuseStep 5782535 = 8673803) B8673803
theorem B12688427 : Blo 1713057 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B5782643 : Blo 1713057 5782643 := bstep (se 1 (by rfl) ⟨4336982, by rfl⟩ : syracuseStep 5782643 = 8673965) B8673965
theorem B7322795 : Blo 1713057 7322795 := bstep (se 1 (by rfl) ⟨5492096, by rfl⟩ : syracuseStep 7322795 = 10984193) B10984193
theorem B3857579 : Blo 1713057 3857579 := bstep (se 1 (by rfl) ⟨2893184, by rfl⟩ : syracuseStep 3857579 = 5786369) B5786369
theorem B5782913 : Blo 1713057 5782913 := bstep (se 2 (by rfl) ⟨2168592, by rfl⟩ : syracuseStep 5782913 = 4337185) B4337185
theorem B2571695 : Blo 1713057 2571695 := bstep (se 1 (by rfl) ⟨1928771, by rfl⟩ : syracuseStep 2571695 = 3857543) B3857543
theorem B2891227 : Blo 1713057 2891227 := bstep (se 1 (by rfl) ⟨2168420, by rfl⟩ : syracuseStep 2891227 = 4336841) B4336841
theorem B4341235 : Blo 1713057 4341235 := bstep (se 1 (by rfl) ⟨3255926, by rfl⟩ : syracuseStep 4341235 = 6511853) B6511853
theorem B2571785 : Blo 1713057 2571785 := bstep (se 2 (by rfl) ⟨964419, by rfl⟩ : syracuseStep 2571785 = 1928839) B1928839
theorem B5864993 : Blo 1713057 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B2571815 : Blo 1713057 2571815 := bstep (se 1 (by rfl) ⟨1928861, by rfl⟩ : syracuseStep 2571815 = 3857723) B3857723
theorem B2440783 : Blo 1713057 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B2571899 : Blo 1713057 2571899 := bstep (se 1 (by rfl) ⟨1928924, by rfl⟩ : syracuseStep 2571899 = 3857849) B3857849
theorem B3858119 : Blo 1713057 3858119 := bstep (se 1 (by rfl) ⟨2893589, by rfl⟩ : syracuseStep 3858119 = 5787179) B5787179
theorem B2170567 : Blo 1713057 2170567 := bstep (se 1 (by rfl) ⟨1627925, by rfl⟩ : syracuseStep 2170567 = 3255851) B3255851
theorem B2572025 : Blo 1713057 2572025 := bstep (se 2 (by rfl) ⟨964509, by rfl⟩ : syracuseStep 2572025 = 1929019) B1929019
theorem B2572127 : Blo 1713057 2572127 := bstep (se 1 (by rfl) ⟨1929095, by rfl⟩ : syracuseStep 2572127 = 3858191) B3858191
theorem B2572139 : Blo 1713057 2572139 := bstep (se 1 (by rfl) ⟨1929104, by rfl⟩ : syracuseStep 2572139 = 3858209) B3858209
theorem B12353467 : Blo 1713057 12353467 := bstep (se 1 (by rfl) ⟨9265100, by rfl⟩ : syracuseStep 12353467 = 18530201) B18530201
theorem B5783561 : Blo 1713057 5783561 := bstep (se 2 (by rfl) ⟨2168835, by rfl⟩ : syracuseStep 5783561 = 4337671) B4337671
theorem B2572553 : Blo 1713057 2572553 := bstep (se 2 (by rfl) ⟨964707, by rfl⟩ : syracuseStep 2572553 = 1929415) B1929415
theorem B13017509 : Blo 1713057 13017509 := bstep (se 4 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 13017509 = 2440783) B2440783
theorem B2892199 : Blo 1713057 2892199 := bstep (se 1 (by rfl) ⟨2169149, by rfl⟩ : syracuseStep 2892199 = 4338299) B4338299
theorem B18522593 : Blo 1713057 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B2892361 : Blo 1713057 2892361 := bstep (se 2 (by rfl) ⟨1084635, by rfl⟩ : syracuseStep 2892361 = 2169271) B2169271
theorem B2892395 : Blo 1713057 2892395 := bstep (se 1 (by rfl) ⟨2169296, by rfl⟩ : syracuseStep 2892395 = 4338593) B4338593
theorem B14647979 : Blo 1713057 14647979 := bstep (se 1 (by rfl) ⟨10985984, by rfl⟩ : syracuseStep 14647979 = 21971969) B21971969
theorem B10568407 : Blo 1713057 10568407 := bstep (se 1 (by rfl) ⟨7926305, by rfl⟩ : syracuseStep 10568407 = 15852611) B15852611
theorem B3662671 : Blo 1713057 3662671 := bstep (se 1 (by rfl) ⟨2747003, by rfl⟩ : syracuseStep 3662671 = 5494007) B5494007
theorem B3662747 : Blo 1713057 3662747 := bstep (se 1 (by rfl) ⟨2747060, by rfl⟩ : syracuseStep 3662747 = 5494121) B5494121
theorem B1713103 : Blo 1713057 1713103 := bstep (se 1 (by rfl) ⟨1284827, by rfl⟩ : syracuseStep 1713103 = 2569655) B2569655
theorem B1713127 : Blo 1713057 1713127 := bstep (se 1 (by rfl) ⟨1284845, by rfl⟩ : syracuseStep 1713127 = 2569691) B2569691
theorem B3253223 : Blo 1713057 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B3474407 : Blo 1713057 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B7423073 : Blo 1713057 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B6177991 : Blo 1713057 6177991 := bstep (se 1 (by rfl) ⟨4633493, by rfl⟩ : syracuseStep 6177991 = 9266987) B9266987
theorem B111166667 : Blo 1713057 111166667 := bstep (se 1 (by rfl) ⟨83375000, by rfl⟩ : syracuseStep 111166667 = 166750001) B166750001
theorem B1713439 : Blo 1713057 1713439 := bstep (se 1 (by rfl) ⟨1285079, by rfl⟩ : syracuseStep 1713439 = 2570159) B2570159
theorem B13010219 : Blo 1713057 13010219 := bstep (se 1 (by rfl) ⟨9757664, by rfl⟩ : syracuseStep 13010219 = 19515329) B19515329
theorem B23455025 : Blo 1713057 23455025 := bstep (se 2 (by rfl) ⟨8795634, by rfl⟩ : syracuseStep 23455025 = 17591269) B17591269
theorem B1713499 : Blo 1713057 1713499 := bstep (se 1 (by rfl) ⟨1285124, by rfl⟩ : syracuseStep 1713499 = 2570249) B2570249
theorem B1713519 : Blo 1713057 1713519 := bstep (se 1 (by rfl) ⟨1285139, by rfl⟩ : syracuseStep 1713519 = 2570279) B2570279
theorem B1713575 : Blo 1713057 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B1713659 : Blo 1713057 1713659 := bstep (se 1 (by rfl) ⟨1285244, by rfl⟩ : syracuseStep 1713659 = 2570489) B2570489
theorem B6505991 : Blo 1713057 6505991 := bstep (se 1 (by rfl) ⟨4879493, by rfl⟩ : syracuseStep 6505991 = 9758987) B9758987
theorem B1713727 : Blo 1713057 1713727 := bstep (se 1 (by rfl) ⟨1285295, by rfl⟩ : syracuseStep 1713727 = 2570591) B2570591
theorem B1713735 : Blo 1713057 1713735 := bstep (se 1 (by rfl) ⟨1285301, by rfl⟩ : syracuseStep 1713735 = 2570603) B2570603
theorem B1713887 : Blo 1713057 1713887 := bstep (se 1 (by rfl) ⟨1285415, by rfl⟩ : syracuseStep 1713887 = 2570831) B2570831
theorem B1713967 : Blo 1713057 1713967 := bstep (se 1 (by rfl) ⟨1285475, by rfl⟩ : syracuseStep 1713967 = 2570951) B2570951
theorem B21137219 : Blo 1713057 21137219 := bstep (se 1 (by rfl) ⟨15852914, by rfl⟩ : syracuseStep 21137219 = 31705829) B31705829
theorem B10979219 : Blo 1713057 10979219 := bstep (se 1 (by rfl) ⟨8234414, by rfl⟩ : syracuseStep 10979219 = 16468829) B16468829
theorem B1714075 : Blo 1713057 1714075 := bstep (se 1 (by rfl) ⟨1285556, by rfl⟩ : syracuseStep 1714075 = 2571113) B2571113
theorem B1714127 : Blo 1713057 1714127 := bstep (se 1 (by rfl) ⟨1285595, by rfl⟩ : syracuseStep 1714127 = 2571191) B2571191
theorem B2058215 : Blo 1713057 2058215 := bstep (se 1 (by rfl) ⟨1543661, by rfl⟩ : syracuseStep 2058215 = 3087323) B3087323
theorem B1714151 : Blo 1713057 1714151 := bstep (se 1 (by rfl) ⟨1285613, by rfl⟩ : syracuseStep 1714151 = 2571227) B2571227
theorem B6506477 : Blo 1713057 6506477 := bstep (se 3 (by rfl) ⟨1219964, by rfl⟩ : syracuseStep 6506477 = 2439929) B2439929
theorem B2894089 : Blo 1713057 2894089 := bstep (se 2 (by rfl) ⟨1085283, by rfl⟩ : syracuseStep 2894089 = 2170567) B2170567
theorem B1714463 : Blo 1713057 1714463 := bstep (se 1 (by rfl) ⟨1285847, by rfl⟩ : syracuseStep 1714463 = 2571695) B2571695
theorem B1714523 : Blo 1713057 1714523 := bstep (se 1 (by rfl) ⟨1285892, by rfl⟩ : syracuseStep 1714523 = 2571785) B2571785
theorem B3909995 : Blo 1713057 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B1714543 : Blo 1713057 1714543 := bstep (se 1 (by rfl) ⟨1285907, by rfl⟩ : syracuseStep 1714543 = 2571815) B2571815
theorem B32934275 : Blo 1713057 32934275 := bstep (se 1 (by rfl) ⟨24700706, by rfl⟩ : syracuseStep 32934275 = 49401413) B49401413
theorem B1714599 : Blo 1713057 1714599 := bstep (se 1 (by rfl) ⟨1285949, by rfl⟩ : syracuseStep 1714599 = 2571899) B2571899
theorem B6506963 : Blo 1713057 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B3434977 : Blo 1713057 3434977 := bstep (se 2 (by rfl) ⟨1288116, by rfl⟩ : syracuseStep 3434977 = 2576233) B2576233
theorem B3475963 : Blo 1713057 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B1714683 : Blo 1713057 1714683 := bstep (se 1 (by rfl) ⟨1286012, by rfl⟩ : syracuseStep 1714683 = 2572025) B2572025
theorem B1714751 : Blo 1713057 1714751 := bstep (se 1 (by rfl) ⟨1286063, by rfl⟩ : syracuseStep 1714751 = 2572127) B2572127
theorem B1714759 : Blo 1713057 1714759 := bstep (se 1 (by rfl) ⟨1286069, by rfl⟩ : syracuseStep 1714759 = 2572139) B2572139
theorem B7817867 : Blo 1713057 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B13011677 : Blo 1713057 13011677 := bstep (se 3 (by rfl) ⟨2439689, by rfl⟩ : syracuseStep 13011677 = 4879379) B4879379
theorem B1927903 : Blo 1713057 1927903 := bstep (se 1 (by rfl) ⟨1445927, by rfl⟩ : syracuseStep 1927903 = 2891855) B2891855
theorem B1714911 : Blo 1713057 1714911 := bstep (se 1 (by rfl) ⟨1286183, by rfl⟩ : syracuseStep 1714911 = 2572367) B2572367
theorem B4336375 : Blo 1713057 4336375 := bstep (se 1 (by rfl) ⟨3252281, by rfl⟩ : syracuseStep 4336375 = 6504563) B6504563
theorem B1714991 : Blo 1713057 1714991 := bstep (se 1 (by rfl) ⟨1286243, by rfl⟩ : syracuseStep 1714991 = 2572487) B2572487
theorem B4336679 : Blo 1713057 4336679 := bstep (se 1 (by rfl) ⟨3252509, by rfl⟩ : syracuseStep 4336679 = 6505019) B6505019
theorem B5786747 : Blo 1713057 5786747 := bstep (se 1 (by rfl) ⟨4340060, by rfl⟩ : syracuseStep 5786747 = 8680121) B8680121
theorem B16706699 : Blo 1713057 16706699 := bstep (se 1 (by rfl) ⟨12530024, by rfl⟩ : syracuseStep 16706699 = 25060049) B25060049
theorem B1928479 : Blo 1713057 1928479 := bstep (se 1 (by rfl) ⟨1446359, by rfl⟩ : syracuseStep 1928479 = 2892719) B2892719
theorem B5787017 : Blo 1713057 5787017 := bstep (se 2 (by rfl) ⟨2170131, by rfl⟩ : syracuseStep 5787017 = 4340263) B4340263
theorem B3911161 : Blo 1713057 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B1928767 : Blo 1713057 1928767 := bstep (se 1 (by rfl) ⟨1446575, by rfl⟩ : syracuseStep 1928767 = 2893151) B2893151
theorem B6508147 : Blo 1713057 6508147 := bstep (se 1 (by rfl) ⟨4881110, by rfl⟩ : syracuseStep 6508147 = 9762221) B9762221
theorem B18526009 : Blo 1713057 18526009 := bstep (se 2 (by rfl) ⟨6947253, by rfl⟩ : syracuseStep 18526009 = 13894507) B13894507
theorem B5787449 : Blo 1713057 5787449 := bstep (se 2 (by rfl) ⟨2170293, by rfl⟩ : syracuseStep 5787449 = 4340587) B4340587
theorem B18796445 : Blo 1713057 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B4698121 : Blo 1713057 4698121 := bstep (se 2 (by rfl) ⟨1761795, by rfl⟩ : syracuseStep 4698121 = 3523591) B3523591
theorem B24760379 : Blo 1713057 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B13906025 : Blo 1713057 13906025 := bstep (se 2 (by rfl) ⟨5214759, by rfl⟩ : syracuseStep 13906025 = 10429519) B10429519
theorem B8679635 : Blo 1713057 8679635 := bstep (se 1 (by rfl) ⟨6509726, by rfl⟩ : syracuseStep 8679635 = 13019453) B13019453
theorem B11432207 : Blo 1713057 11432207 := bstep (se 1 (by rfl) ⟨8574155, by rfl⟩ : syracuseStep 11432207 = 17148311) B17148311
theorem B4337945 : Blo 1713057 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B3854699 : Blo 1713057 3854699 := bstep (se 1 (by rfl) ⟨2891024, by rfl⟩ : syracuseStep 3854699 = 5782049) B5782049
theorem B6508907 : Blo 1713057 6508907 := bstep (se 1 (by rfl) ⟨4881680, by rfl⟩ : syracuseStep 6508907 = 9763361) B9763361
theorem B2200007 : Blo 1713057 2200007 := bstep (se 1 (by rfl) ⟨1650005, by rfl⟩ : syracuseStep 2200007 = 3300011) B3300011
theorem B19534283 : Blo 1713057 19534283 := bstep (se 1 (by rfl) ⟨14650712, by rfl⟩ : syracuseStep 19534283 = 29301425) B29301425
theorem B3854843 : Blo 1713057 3854843 := bstep (se 1 (by rfl) ⟨2891132, by rfl⟩ : syracuseStep 3854843 = 5782265) B5782265
theorem B20845117 : Blo 1713057 20845117 := bstep (se 3 (by rfl) ⟨3908459, by rfl⟩ : syracuseStep 20845117 = 7816919) B7816919
theorem B3854969 : Blo 1713057 3854969 := bstep (se 2 (by rfl) ⟨1445613, by rfl⟩ : syracuseStep 3854969 = 2891227) B2891227
theorem B5788313 : Blo 1713057 5788313 := bstep (se 2 (by rfl) ⟨2170617, by rfl⟩ : syracuseStep 5788313 = 4341235) B4341235
theorem B3855023 : Blo 1713057 3855023 := bstep (se 1 (by rfl) ⟨2891267, by rfl⟩ : syracuseStep 3855023 = 5782535) B5782535
theorem B2290351 : Blo 1713057 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B8458951 : Blo 1713057 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B3855095 : Blo 1713057 3855095 := bstep (se 1 (by rfl) ⟨2891321, by rfl⟩ : syracuseStep 3855095 = 5782643) B5782643
theorem B3855275 : Blo 1713057 3855275 := bstep (se 1 (by rfl) ⟨2891456, by rfl⟩ : syracuseStep 3855275 = 5782913) B5782913
theorem B12358601 : Blo 1713057 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B29275181 : Blo 1713057 29275181 := bstep (se 3 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 29275181 = 10978193) B10978193
theorem B14095417 : Blo 1713057 14095417 := bstep (se 2 (by rfl) ⟨5285781, by rfl⟩ : syracuseStep 14095417 = 10571563) B10571563
theorem B4338785 : Blo 1713057 4338785 := bstep (se 2 (by rfl) ⟨1627044, by rfl⟩ : syracuseStep 4338785 = 3254089) B3254089
theorem B9893011 : Blo 1713057 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B16471289 : Blo 1713057 16471289 := bstep (se 2 (by rfl) ⟨6176733, by rfl⟩ : syracuseStep 16471289 = 12353467) B12353467
theorem B2569595 : Blo 1713057 2569595 := bstep (se 1 (by rfl) ⟨1927196, by rfl⟩ : syracuseStep 2569595 = 3854393) B3854393
theorem B3855815 : Blo 1713057 3855815 := bstep (se 1 (by rfl) ⟨2891861, by rfl⟩ : syracuseStep 3855815 = 5783723) B5783723
theorem B2569721 : Blo 1713057 2569721 := bstep (se 2 (by rfl) ⟨963645, by rfl⟩ : syracuseStep 2569721 = 1927291) B1927291
theorem B3659347 : Blo 1713057 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B2569823 : Blo 1713057 2569823 := bstep (se 1 (by rfl) ⟨1927367, by rfl⟩ : syracuseStep 2569823 = 3854735) B3854735
theorem B2168623 : Blo 1713057 2168623 := bstep (se 1 (by rfl) ⟨1626467, by rfl⟩ : syracuseStep 2168623 = 3252935) B3252935
theorem B3856175 : Blo 1713057 3856175 := bstep (se 1 (by rfl) ⟨2892131, by rfl⟩ : syracuseStep 3856175 = 5784263) B5784263
theorem B2570039 : Blo 1713057 2570039 := bstep (se 1 (by rfl) ⟨1927529, by rfl⟩ : syracuseStep 2570039 = 3855059) B3855059
theorem B2570345 : Blo 1713057 2570345 := bstep (se 2 (by rfl) ⟨963879, by rfl⟩ : syracuseStep 2570345 = 1927759) B1927759
theorem B20838647 : Blo 1713057 20838647 := bstep (se 1 (by rfl) ⟨15628985, by rfl⟩ : syracuseStep 20838647 = 31257971) B31257971
theorem B2169119 : Blo 1713057 2169119 := bstep (se 1 (by rfl) ⟨1626839, by rfl⟩ : syracuseStep 2169119 = 3253679) B3253679
theorem B41703767 : Blo 1713057 41703767 := bstep (se 1 (by rfl) ⟨31277825, by rfl⟩ : syracuseStep 41703767 = 62555651) B62555651
theorem B3856751 : Blo 1713057 3856751 := bstep (se 1 (by rfl) ⟨2892563, by rfl⟩ : syracuseStep 3856751 = 5785127) B5785127
theorem B2570663 : Blo 1713057 2570663 := bstep (se 1 (by rfl) ⟨1927997, by rfl⟩ : syracuseStep 2570663 = 3855995) B3855995
theorem B15628727 : Blo 1713057 15628727 := bstep (se 1 (by rfl) ⟨11721545, by rfl⟩ : syracuseStep 15628727 = 23443091) B23443091
theorem B3856823 : Blo 1713057 3856823 := bstep (se 1 (by rfl) ⟨2892617, by rfl⟩ : syracuseStep 3856823 = 5785235) B5785235
theorem B2570747 : Blo 1713057 2570747 := bstep (se 1 (by rfl) ⟨1928060, by rfl⟩ : syracuseStep 2570747 = 3856121) B3856121
theorem B4340243 : Blo 1713057 4340243 := bstep (se 1 (by rfl) ⟨3255182, by rfl⟩ : syracuseStep 4340243 = 6510365) B6510365
theorem B3856967 : Blo 1713057 3856967 := bstep (se 1 (by rfl) ⟨2892725, by rfl⟩ : syracuseStep 3856967 = 5785451) B5785451
theorem B3857003 : Blo 1713057 3857003 := bstep (se 1 (by rfl) ⟨2892752, by rfl⟩ : syracuseStep 3857003 = 5785505) B5785505
theorem B2570873 : Blo 1713057 2570873 := bstep (se 2 (by rfl) ⟨964077, by rfl⟩ : syracuseStep 2570873 = 1928155) B1928155
theorem B2570927 : Blo 1713057 2570927 := bstep (se 1 (by rfl) ⟨1928195, by rfl⟩ : syracuseStep 2570927 = 3856391) B3856391
theorem B4635319 : Blo 1713057 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B2570975 : Blo 1713057 2570975 := bstep (se 1 (by rfl) ⟨1928231, by rfl⟩ : syracuseStep 2570975 = 3856463) B3856463
theorem B2317097 : Blo 1713057 2317097 := bstep (se 2 (by rfl) ⟨868911, by rfl⟩ : syracuseStep 2317097 = 1737823) B1737823
theorem B10976143 : Blo 1713057 10976143 := bstep (se 1 (by rfl) ⟨8232107, by rfl⟩ : syracuseStep 10976143 = 16464215) B16464215
theorem B4635535 : Blo 1713057 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B5782427 : Blo 1713057 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B7322555 : Blo 1713057 7322555 := bstep (se 1 (by rfl) ⟨5491916, by rfl⟩ : syracuseStep 7322555 = 10983833) B10983833
theorem B14646203 : Blo 1713057 14646203 := bstep (se 1 (by rfl) ⟨10984652, by rfl⟩ : syracuseStep 14646203 = 21969305) B21969305
theorem B4340699 : Blo 1713057 4340699 := bstep (se 1 (by rfl) ⟨3255524, by rfl⟩ : syracuseStep 4340699 = 6511049) B6511049
theorem B2571239 : Blo 1713057 2571239 := bstep (se 1 (by rfl) ⟨1928429, by rfl⟩ : syracuseStep 2571239 = 3856859) B3856859
theorem B13016051 : Blo 1713057 13016051 := bstep (se 1 (by rfl) ⟨9762038, by rfl⟩ : syracuseStep 13016051 = 19524077) B19524077
theorem B3857399 : Blo 1713057 3857399 := bstep (se 1 (by rfl) ⟨2893049, by rfl⟩ : syracuseStep 3857399 = 5786099) B5786099
theorem B37059707 : Blo 1713057 37059707 := bstep (se 1 (by rfl) ⟨27794780, by rfl⟩ : syracuseStep 37059707 = 55589561) B55589561
theorem B2571497 : Blo 1713057 2571497 := bstep (se 2 (by rfl) ⟨964311, by rfl⟩ : syracuseStep 2571497 = 1928623) B1928623
theorem B4119785 : Blo 1713057 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B24108299 : Blo 1713057 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B2571551 : Blo 1713057 2571551 := bstep (se 1 (by rfl) ⟨1928663, by rfl⟩ : syracuseStep 2571551 = 3857327) B3857327
theorem B4341023 : Blo 1713057 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B2440487 : Blo 1713057 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B3857759 : Blo 1713057 3857759 := bstep (se 1 (by rfl) ⟨2893319, by rfl⟩ : syracuseStep 3857759 = 5786639) B5786639
theorem B3661193 : Blo 1713057 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B2891207 : Blo 1713057 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B4881863 : Blo 1713057 4881863 := bstep (se 1 (by rfl) ⟨3661397, by rfl⟩ : syracuseStep 4881863 = 7322795) B7322795
theorem B2571719 : Blo 1713057 2571719 := bstep (se 1 (by rfl) ⟨1928789, by rfl⟩ : syracuseStep 2571719 = 3857579) B3857579
theorem B8674775 : Blo 1713057 8674775 := bstep (se 1 (by rfl) ⟨6506081, by rfl⟩ : syracuseStep 8674775 = 13012163) B13012163
theorem B4120121 : Blo 1713057 4120121 := bstep (se 2 (by rfl) ⟨1545045, by rfl⟩ : syracuseStep 4120121 = 3090091) B3090091
theorem B13188689 : Blo 1713057 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B3858155 : Blo 1713057 3858155 := bstep (se 1 (by rfl) ⟨2893616, by rfl⟩ : syracuseStep 3858155 = 5787233) B5787233
theorem B10985219 : Blo 1713057 10985219 := bstep (se 1 (by rfl) ⟨8238914, by rfl⟩ : syracuseStep 10985219 = 16477829) B16477829
theorem B2572073 : Blo 1713057 2572073 := bstep (se 2 (by rfl) ⟨964527, by rfl⟩ : syracuseStep 2572073 = 1929055) B1929055
theorem B2572079 : Blo 1713057 2572079 := bstep (se 1 (by rfl) ⟨1929059, by rfl⟩ : syracuseStep 2572079 = 3858119) B3858119
theorem B2932537 : Blo 1713057 2932537 := bstep (se 2 (by rfl) ⟨1099701, by rfl⟩ : syracuseStep 2932537 = 2199403) B2199403
theorem B3858281 : Blo 1713057 3858281 := bstep (se 2 (by rfl) ⟨1446855, by rfl⟩ : syracuseStep 3858281 = 2893711) B2893711
theorem B5783453 : Blo 1713057 5783453 := bstep (se 3 (by rfl) ⟨1084397, by rfl⟩ : syracuseStep 5783453 = 2168795) B2168795
theorem B33415105 : Blo 1713057 33415105 := bstep (se 2 (by rfl) ⟨12530664, by rfl⟩ : syracuseStep 33415105 = 25061329) B25061329
theorem B16506919 : Blo 1713057 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B2891963 : Blo 1713057 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B3858785 : Blo 1713057 3858785 := bstep (se 2 (by rfl) ⟨1447044, by rfl⟩ : syracuseStep 3858785 = 2894089) B2894089
theorem B3858875 : Blo 1713057 3858875 := bstep (se 1 (by rfl) ⟨2894156, by rfl⟩ : syracuseStep 3858875 = 5788313) B5788313
theorem B9765319 : Blo 1713057 9765319 := bstep (se 1 (by rfl) ⟨7323989, by rfl⟩ : syracuseStep 9765319 = 14647979) B14647979
theorem B2441831 : Blo 1713057 2441831 := bstep (se 1 (by rfl) ⟨1831373, by rfl⟩ : syracuseStep 2441831 = 3662747) B3662747
theorem B2892523 : Blo 1713057 2892523 := bstep (se 1 (by rfl) ⟨2169392, by rfl⟩ : syracuseStep 2892523 = 4338785) B4338785
theorem B4948715 : Blo 1713057 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B5784317 : Blo 1713057 5784317 := bstep (se 3 (by rfl) ⟨1084559, by rfl⟩ : syracuseStep 5784317 = 2169119) B2169119
theorem B1713063 : Blo 1713057 1713063 := bstep (se 1 (by rfl) ⟨1284797, by rfl⟩ : syracuseStep 1713063 = 2569595) B2569595
theorem B14091209 : Blo 1713057 14091209 := bstep (se 2 (by rfl) ⟨5284203, by rfl⟩ : syracuseStep 14091209 = 10568407) B10568407
theorem B1713147 : Blo 1713057 1713147 := bstep (se 1 (by rfl) ⟨1284860, by rfl⟩ : syracuseStep 1713147 = 2569721) B2569721
theorem B1713215 : Blo 1713057 1713215 := bstep (se 1 (by rfl) ⟨1284911, by rfl⟩ : syracuseStep 1713215 = 2569823) B2569823
theorem B4883561 : Blo 1713057 4883561 := bstep (se 2 (by rfl) ⟨1831335, by rfl⟩ : syracuseStep 4883561 = 3662671) B3662671
theorem B5866685 : Blo 1713057 5866685 := bstep (se 3 (by rfl) ⟨1100003, by rfl⟩ : syracuseStep 5866685 = 2200007) B2200007
theorem B1713359 : Blo 1713057 1713359 := bstep (se 1 (by rfl) ⟨1285019, by rfl⟩ : syracuseStep 1713359 = 2570039) B2570039
theorem B14091479 : Blo 1713057 14091479 := bstep (se 1 (by rfl) ⟨10568609, by rfl⟩ : syracuseStep 14091479 = 21137219) B21137219
theorem B1713563 : Blo 1713057 1713563 := bstep (se 1 (by rfl) ⟨1285172, by rfl⟩ : syracuseStep 1713563 = 2570345) B2570345
theorem B18793889 : Blo 1713057 18793889 := bstep (se 2 (by rfl) ⟨7047708, by rfl⟩ : syracuseStep 18793889 = 14095417) B14095417
theorem B13190681 : Blo 1713057 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B2606663 : Blo 1713057 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B21956183 : Blo 1713057 21956183 := bstep (se 1 (by rfl) ⟨16467137, by rfl⟩ : syracuseStep 21956183 = 32934275) B32934275
theorem B1713775 : Blo 1713057 1713775 := bstep (se 1 (by rfl) ⟨1285331, by rfl⟩ : syracuseStep 1713775 = 2570663) B2570663
theorem B1713831 : Blo 1713057 1713831 := bstep (se 1 (by rfl) ⟨1285373, by rfl⟩ : syracuseStep 1713831 = 2570747) B2570747
theorem B2893495 : Blo 1713057 2893495 := bstep (se 1 (by rfl) ⟨2170121, by rfl⟩ : syracuseStep 2893495 = 4340243) B4340243
theorem B1713915 : Blo 1713057 1713915 := bstep (se 1 (by rfl) ⟨1285436, by rfl⟩ : syracuseStep 1713915 = 2570873) B2570873
theorem B5211911 : Blo 1713057 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B1713951 : Blo 1713057 1713951 := bstep (se 1 (by rfl) ⟨1285463, by rfl⟩ : syracuseStep 1713951 = 2570927) B2570927
theorem B1713983 : Blo 1713057 1713983 := bstep (se 1 (by rfl) ⟨1285487, by rfl⟩ : syracuseStep 1713983 = 2570975) B2570975
theorem B2893799 : Blo 1713057 2893799 := bstep (se 1 (by rfl) ⟨2170349, by rfl⟩ : syracuseStep 2893799 = 4340699) B4340699
theorem B1714159 : Blo 1713057 1714159 := bstep (se 1 (by rfl) ⟨1285619, by rfl⟩ : syracuseStep 1714159 = 2571239) B2571239
theorem B8677367 : Blo 1713057 8677367 := bstep (se 1 (by rfl) ⟨6508025, by rfl⟩ : syracuseStep 8677367 = 13016051) B13016051
theorem B6178925 : Blo 1713057 6178925 := bstep (se 3 (by rfl) ⟨1158548, by rfl⟩ : syracuseStep 6178925 = 2317097) B2317097
theorem B8677529 : Blo 1713057 8677529 := bstep (se 2 (by rfl) ⟨3254073, by rfl⟩ : syracuseStep 8677529 = 6508147) B6508147
theorem B1714331 : Blo 1713057 1714331 := bstep (se 1 (by rfl) ⟨1285748, by rfl⟩ : syracuseStep 1714331 = 2571497) B2571497
theorem B2746523 : Blo 1713057 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B1714367 : Blo 1713057 1714367 := bstep (se 1 (by rfl) ⟨1285775, by rfl⟩ : syracuseStep 1714367 = 2571551) B2571551
theorem B2894015 : Blo 1713057 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B1927471 : Blo 1713057 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B3254575 : Blo 1713057 3254575 := bstep (se 1 (by rfl) ⟨2440931, by rfl⟩ : syracuseStep 3254575 = 4881863) B4881863
theorem B1714479 : Blo 1713057 1714479 := bstep (se 1 (by rfl) ⟨1285859, by rfl⟩ : syracuseStep 1714479 = 2571719) B2571719
theorem B2746747 : Blo 1713057 2746747 := bstep (se 1 (by rfl) ⟨2060060, by rfl⟩ : syracuseStep 2746747 = 4120121) B4120121
theorem B8792459 : Blo 1713057 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B24701345 : Blo 1713057 24701345 := bstep (se 2 (by rfl) ⟨9263004, by rfl⟩ : syracuseStep 24701345 = 18526009) B18526009
theorem B3910049 : Blo 1713057 3910049 := bstep (se 2 (by rfl) ⟨1466268, by rfl⟩ : syracuseStep 3910049 = 2932537) B2932537
theorem B18319877 : Blo 1713057 18319877 := bstep (se 4 (by rfl) ⟨1717488, by rfl⟩ : syracuseStep 18319877 = 3434977) B3434977
theorem B1714715 : Blo 1713057 1714715 := bstep (se 1 (by rfl) ⟨1286036, by rfl⟩ : syracuseStep 1714715 = 2572073) B2572073
theorem B1714719 : Blo 1713057 1714719 := bstep (se 1 (by rfl) ⟨1286039, by rfl⟩ : syracuseStep 1714719 = 2572079) B2572079
theorem B5786423 : Blo 1713057 5786423 := bstep (se 1 (by rfl) ⟨4339817, by rfl⟩ : syracuseStep 5786423 = 8679635) B8679635
theorem B1715035 : Blo 1713057 1715035 := bstep (se 1 (by rfl) ⟨1286276, by rfl⟩ : syracuseStep 1715035 = 2572553) B2572553
theorem B7621471 : Blo 1713057 7621471 := bstep (se 1 (by rfl) ⟨5716103, by rfl⟩ : syracuseStep 7621471 = 11432207) B11432207
theorem B8678339 : Blo 1713057 8678339 := bstep (se 1 (by rfl) ⟨6508754, by rfl⟩ : syracuseStep 8678339 = 13017509) B13017509
theorem B12348395 : Blo 1713057 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B1928263 : Blo 1713057 1928263 := bstep (se 1 (by rfl) ⟨1446197, by rfl⟩ : syracuseStep 1928263 = 2892395) B2892395
theorem B55569725 : Blo 1713057 55569725 := bstep (se 3 (by rfl) ⟨10419323, by rfl⟩ : syracuseStep 55569725 = 20838647) B20838647
theorem B19516787 : Blo 1713057 19516787 := bstep (se 1 (by rfl) ⟨14637590, by rfl⟩ : syracuseStep 19516787 = 29275181) B29275181
theorem B6507965 : Blo 1713057 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B10980859 : Blo 1713057 10980859 := bstep (se 1 (by rfl) ⟨8235644, by rfl⟩ : syracuseStep 10980859 = 16471289) B16471289
theorem B6180425 : Blo 1713057 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B4337327 : Blo 1713057 4337327 := bstep (se 1 (by rfl) ⟨3252995, by rfl⟩ : syracuseStep 4337327 = 6505991) B6505991
theorem B14634857 : Blo 1713057 14634857 := bstep (se 2 (by rfl) ⟨5488071, by rfl⟩ : syracuseStep 14634857 = 10976143) B10976143
theorem B6180713 : Blo 1713057 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B7319479 : Blo 1713057 7319479 := bstep (se 1 (by rfl) ⟨5489609, by rfl⟩ : syracuseStep 7319479 = 10979219) B10979219
theorem B4337651 : Blo 1713057 4337651 := bstep (se 1 (by rfl) ⟨3253238, by rfl⟩ : syracuseStep 4337651 = 6506477) B6506477
theorem B8237321 : Blo 1713057 8237321 := bstep (se 2 (by rfl) ⟨3088995, by rfl⟩ : syracuseStep 8237321 = 6177991) B6177991
theorem B4337975 : Blo 1713057 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B3854951 : Blo 1713057 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B5214881 : Blo 1713057 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B11137799 : Blo 1713057 11137799 := bstep (se 1 (by rfl) ⟨8353349, by rfl⟩ : syracuseStep 11137799 = 16706699) B16706699
theorem B4879129 : Blo 1713057 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B44553473 : Blo 1713057 44553473 := bstep (se 2 (by rfl) ⟨16707552, by rfl⟩ : syracuseStep 44553473 = 33415105) B33415105
theorem B3855635 : Blo 1713057 3855635 := bstep (se 1 (by rfl) ⟨2891726, by rfl⟩ : syracuseStep 3855635 = 5783453) B5783453
theorem B12530963 : Blo 1713057 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B3855707 : Blo 1713057 3855707 := bstep (se 1 (by rfl) ⟨2891780, by rfl⟩ : syracuseStep 3855707 = 5783561) B5783561
theorem B6264161 : Blo 1713057 6264161 := bstep (se 2 (by rfl) ⟨2349060, by rfl⟩ : syracuseStep 6264161 = 4698121) B4698121
theorem B9270683 : Blo 1713057 9270683 := bstep (se 1 (by rfl) ⟨6953012, by rfl⟩ : syracuseStep 9270683 = 13906025) B13906025
theorem B2569799 : Blo 1713057 2569799 := bstep (se 1 (by rfl) ⟨1927349, by rfl⟩ : syracuseStep 2569799 = 3854699) B3854699
theorem B4339271 : Blo 1713057 4339271 := bstep (se 1 (by rfl) ⟨3254453, by rfl⟩ : syracuseStep 4339271 = 6508907) B6508907
theorem B13022855 : Blo 1713057 13022855 := bstep (se 1 (by rfl) ⟨9767141, by rfl⟩ : syracuseStep 13022855 = 19534283) B19534283
theorem B2569895 : Blo 1713057 2569895 := bstep (se 1 (by rfl) ⟨1927421, by rfl⟩ : syracuseStep 2569895 = 3854843) B3854843
theorem B2569979 : Blo 1713057 2569979 := bstep (se 1 (by rfl) ⟨1927484, by rfl⟩ : syracuseStep 2569979 = 3854969) B3854969
theorem B2570015 : Blo 1713057 2570015 := bstep (se 1 (by rfl) ⟨1927511, by rfl⟩ : syracuseStep 2570015 = 3855023) B3855023
theorem B2570063 : Blo 1713057 2570063 := bstep (se 1 (by rfl) ⟨1927547, by rfl⟩ : syracuseStep 2570063 = 3855095) B3855095
theorem B3856265 : Blo 1713057 3856265 := bstep (se 2 (by rfl) ⟨1446099, by rfl⟩ : syracuseStep 3856265 = 2892199) B2892199
theorem B2570183 : Blo 1713057 2570183 := bstep (se 1 (by rfl) ⟨1927637, by rfl⟩ : syracuseStep 2570183 = 3855275) B3855275
theorem B8239067 : Blo 1713057 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B2316271 : Blo 1713057 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B27793489 : Blo 1713057 27793489 := bstep (se 2 (by rfl) ⟨10422558, by rfl⟩ : syracuseStep 27793489 = 20845117) B20845117
theorem B3856481 : Blo 1713057 3856481 := bstep (se 2 (by rfl) ⟨1446180, by rfl⟩ : syracuseStep 3856481 = 2892361) B2892361
theorem B74111111 : Blo 1713057 74111111 := bstep (se 1 (by rfl) ⟨55583333, by rfl⟩ : syracuseStep 74111111 = 111166667) B111166667
theorem B8673479 : Blo 1713057 8673479 := bstep (se 1 (by rfl) ⟨6505109, by rfl⟩ : syracuseStep 8673479 = 13010219) B13010219
theorem B15636683 : Blo 1713057 15636683 := bstep (se 1 (by rfl) ⟨11727512, by rfl⟩ : syracuseStep 15636683 = 23455025) B23455025
theorem B3053801 : Blo 1713057 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B11278601 : Blo 1713057 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B2570537 : Blo 1713057 2570537 := bstep (se 2 (by rfl) ⟨963951, by rfl⟩ : syracuseStep 2570537 = 1927903) B1927903
theorem B2570543 : Blo 1713057 2570543 := bstep (se 1 (by rfl) ⟨1927907, by rfl⟩ : syracuseStep 2570543 = 3855815) B3855815
theorem B5781833 : Blo 1713057 5781833 := bstep (se 2 (by rfl) ⟨2168187, by rfl⟩ : syracuseStep 5781833 = 4336375) B4336375
theorem B2570783 : Blo 1713057 2570783 := bstep (se 1 (by rfl) ⟨1928087, by rfl⟩ : syracuseStep 2570783 = 3856175) B3856175
theorem B27802511 : Blo 1713057 27802511 := bstep (se 1 (by rfl) ⟨20851883, by rfl⟩ : syracuseStep 27802511 = 41703767) B41703767
theorem B2571167 : Blo 1713057 2571167 := bstep (se 1 (by rfl) ⟨1928375, by rfl⟩ : syracuseStep 2571167 = 3856751) B3856751
theorem B10419151 : Blo 1713057 10419151 := bstep (se 1 (by rfl) ⟨7814363, by rfl⟩ : syracuseStep 10419151 = 15628727) B15628727
theorem B2571215 : Blo 1713057 2571215 := bstep (se 1 (by rfl) ⟨1928411, by rfl⟩ : syracuseStep 2571215 = 3856823) B3856823
theorem B2571305 : Blo 1713057 2571305 := bstep (se 2 (by rfl) ⟨964239, by rfl⟩ : syracuseStep 2571305 = 1928479) B1928479
theorem B2571311 : Blo 1713057 2571311 := bstep (se 1 (by rfl) ⟨1928483, by rfl⟩ : syracuseStep 2571311 = 3856967) B3856967
theorem B2571335 : Blo 1713057 2571335 := bstep (se 1 (by rfl) ⟨1928501, by rfl⟩ : syracuseStep 2571335 = 3857003) B3857003
theorem B8674451 : Blo 1713057 8674451 := bstep (se 1 (by rfl) ⟨6505838, by rfl⟩ : syracuseStep 8674451 = 13011677) B13011677
theorem B4881703 : Blo 1713057 4881703 := bstep (se 1 (by rfl) ⟨3661277, by rfl⟩ : syracuseStep 4881703 = 7322555) B7322555
theorem B9764135 : Blo 1713057 9764135 := bstep (se 1 (by rfl) ⟨7323101, by rfl⟩ : syracuseStep 9764135 = 14646203) B14646203
theorem B2571599 : Blo 1713057 2571599 := bstep (se 1 (by rfl) ⟨1928699, by rfl⟩ : syracuseStep 2571599 = 3857399) B3857399
theorem B2891119 : Blo 1713057 2891119 := bstep (se 1 (by rfl) ⟨2168339, by rfl⟩ : syracuseStep 2891119 = 4336679) B4336679
theorem B24706471 : Blo 1713057 24706471 := bstep (se 1 (by rfl) ⟨18529853, by rfl⟩ : syracuseStep 24706471 = 37059707) B37059707
theorem B2571689 : Blo 1713057 2571689 := bstep (se 2 (by rfl) ⟨964383, by rfl⟩ : syracuseStep 2571689 = 1928767) B1928767
theorem B3857831 : Blo 1713057 3857831 := bstep (se 1 (by rfl) ⟨2893373, by rfl⟩ : syracuseStep 3857831 = 5786747) B5786747
theorem B16072199 : Blo 1713057 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B2571839 : Blo 1713057 2571839 := bstep (se 1 (by rfl) ⟨1928879, by rfl⟩ : syracuseStep 2571839 = 3857759) B3857759
theorem B2440795 : Blo 1713057 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B3858011 : Blo 1713057 3858011 := bstep (se 1 (by rfl) ⟨2893508, by rfl⟩ : syracuseStep 3858011 = 5787017) B5787017
theorem B5783183 : Blo 1713057 5783183 := bstep (se 1 (by rfl) ⟨4337387, by rfl⟩ : syracuseStep 5783183 = 8674775) B8674775
theorem B2891497 : Blo 1713057 2891497 := bstep (se 2 (by rfl) ⟨1084311, by rfl⟩ : syracuseStep 2891497 = 2168623) B2168623
theorem B2572103 : Blo 1713057 2572103 := bstep (se 1 (by rfl) ⟨1929077, by rfl⟩ : syracuseStep 2572103 = 3858155) B3858155
theorem B7323479 : Blo 1713057 7323479 := bstep (se 1 (by rfl) ⟨5492609, by rfl⟩ : syracuseStep 7323479 = 10985219) B10985219
theorem B3858299 : Blo 1713057 3858299 := bstep (se 1 (by rfl) ⟨2893724, by rfl⟩ : syracuseStep 3858299 = 5787449) B5787449
theorem B2572187 : Blo 1713057 2572187 := bstep (se 1 (by rfl) ⟨1929140, by rfl⟩ : syracuseStep 2572187 = 3858281) B3858281
theorem B5488573 : Blo 1713057 5488573 := bstep (se 3 (by rfl) ⟨1029107, by rfl⟩ : syracuseStep 5488573 = 2058215) B2058215
theorem B8675261 : Blo 1713057 8675261 := bstep (se 3 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 8675261 = 3253223) B3253223
theorem B18538469 : Blo 1713057 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B2891983 : Blo 1713057 2891983 := bstep (se 1 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 2891983 = 4337975) B4337975
theorem B2572523 : Blo 1713057 2572523 := bstep (se 1 (by rfl) ⟨1929392, by rfl⟩ : syracuseStep 2572523 = 3858785) B3858785
theorem B2572583 : Blo 1713057 2572583 := bstep (se 1 (by rfl) ⟨1929437, by rfl⟩ : syracuseStep 2572583 = 3858875) B3858875
theorem B3662329 : Blo 1713057 3662329 := bstep (se 2 (by rfl) ⟨1373373, by rfl⟩ : syracuseStep 3662329 = 2746747) B2746747
theorem B41697821 : Blo 1713057 41697821 := bstep (se 3 (by rfl) ⟨7818341, by rfl⟩ : syracuseStep 41697821 = 15636683) B15636683
theorem B6505505 : Blo 1713057 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B1713199 : Blo 1713057 1713199 := bstep (se 1 (by rfl) ⟨1284899, by rfl⟩ : syracuseStep 1713199 = 2569799) B2569799
theorem B2892847 : Blo 1713057 2892847 := bstep (se 1 (by rfl) ⟨2169635, by rfl⟩ : syracuseStep 2892847 = 4339271) B4339271
theorem B1737775 : Blo 1713057 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B1713263 : Blo 1713057 1713263 := bstep (se 1 (by rfl) ⟨1284947, by rfl⟩ : syracuseStep 1713263 = 2569895) B2569895
theorem B1713319 : Blo 1713057 1713319 := bstep (se 1 (by rfl) ⟨1284989, by rfl⟩ : syracuseStep 1713319 = 2569979) B2569979
theorem B1713343 : Blo 1713057 1713343 := bstep (se 1 (by rfl) ⟨1285007, by rfl⟩ : syracuseStep 1713343 = 2570015) B2570015
theorem B1713375 : Blo 1713057 1713375 := bstep (se 1 (by rfl) ⟨1285031, by rfl⟩ : syracuseStep 1713375 = 2570063) B2570063
theorem B1713455 : Blo 1713057 1713455 := bstep (se 1 (by rfl) ⟨1285091, by rfl⟩ : syracuseStep 1713455 = 2570183) B2570183
theorem B5784911 : Blo 1713057 5784911 := bstep (se 1 (by rfl) ⟨4338683, by rfl⟩ : syracuseStep 5784911 = 8677367) B8677367
theorem B49407407 : Blo 1713057 49407407 := bstep (se 1 (by rfl) ⟨37055555, by rfl⟩ : syracuseStep 49407407 = 74111111) B74111111
theorem B5785019 : Blo 1713057 5785019 := bstep (se 1 (by rfl) ⟨4338764, by rfl⟩ : syracuseStep 5785019 = 8677529) B8677529
theorem B1713691 : Blo 1713057 1713691 := bstep (se 1 (by rfl) ⟨1285268, by rfl⟩ : syracuseStep 1713691 = 2570537) B2570537
theorem B1713695 : Blo 1713057 1713695 := bstep (se 1 (by rfl) ⟨1285271, by rfl⟩ : syracuseStep 1713695 = 2570543) B2570543
theorem B16467563 : Blo 1713057 16467563 := bstep (se 1 (by rfl) ⟨12350672, by rfl⟩ : syracuseStep 16467563 = 24701345) B24701345
theorem B2606699 : Blo 1713057 2606699 := bstep (se 1 (by rfl) ⟨1955024, by rfl⟩ : syracuseStep 2606699 = 3910049) B3910049
theorem B1713855 : Blo 1713057 1713855 := bstep (se 1 (by rfl) ⟨1285391, by rfl⟩ : syracuseStep 1713855 = 2570783) B2570783
theorem B32941961 : Blo 1713057 32941961 := bstep (se 2 (by rfl) ⟨12353235, by rfl⟩ : syracuseStep 32941961 = 24706471) B24706471
theorem B1714111 : Blo 1713057 1714111 := bstep (se 1 (by rfl) ⟨1285583, by rfl⟩ : syracuseStep 1714111 = 2571167) B2571167
theorem B5785559 : Blo 1713057 5785559 := bstep (se 1 (by rfl) ⟨4339169, by rfl⟩ : syracuseStep 5785559 = 8678339) B8678339
theorem B1714143 : Blo 1713057 1714143 := bstep (se 1 (by rfl) ⟨1285607, by rfl⟩ : syracuseStep 1714143 = 2571215) B2571215
theorem B14641145 : Blo 1713057 14641145 := bstep (se 2 (by rfl) ⟨5490429, by rfl⟩ : syracuseStep 14641145 = 10980859) B10980859
theorem B1714203 : Blo 1713057 1714203 := bstep (se 1 (by rfl) ⟨1285652, by rfl⟩ : syracuseStep 1714203 = 2571305) B2571305
theorem B1714207 : Blo 1713057 1714207 := bstep (se 1 (by rfl) ⟨1285655, by rfl⟩ : syracuseStep 1714207 = 2571311) B2571311
theorem B1714223 : Blo 1713057 1714223 := bstep (se 1 (by rfl) ⟨1285667, by rfl⟩ : syracuseStep 1714223 = 2571335) B2571335
theorem B3254393 : Blo 1713057 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B37046483 : Blo 1713057 37046483 := bstep (se 1 (by rfl) ⟨27784862, by rfl⟩ : syracuseStep 37046483 = 55569725) B55569725
theorem B1714399 : Blo 1713057 1714399 := bstep (se 1 (by rfl) ⟨1285799, by rfl⟩ : syracuseStep 1714399 = 2571599) B2571599
theorem B13011191 : Blo 1713057 13011191 := bstep (se 1 (by rfl) ⟨9758393, by rfl⟩ : syracuseStep 13011191 = 19516787) B19516787
theorem B1714459 : Blo 1713057 1714459 := bstep (se 1 (by rfl) ⟨1285844, by rfl⟩ : syracuseStep 1714459 = 2571689) B2571689
theorem B1714559 : Blo 1713057 1714559 := bstep (se 1 (by rfl) ⟨1285919, by rfl⟩ : syracuseStep 1714559 = 2571839) B2571839
theorem B1714735 : Blo 1713057 1714735 := bstep (se 1 (by rfl) ⟨1286051, by rfl⟩ : syracuseStep 1714735 = 2572103) B2572103
theorem B9759305 : Blo 1713057 9759305 := bstep (se 2 (by rfl) ⟨3659739, by rfl⟩ : syracuseStep 9759305 = 7319479) B7319479
theorem B7318097 : Blo 1713057 7318097 := bstep (se 2 (by rfl) ⟨2744286, by rfl⟩ : syracuseStep 7318097 = 5488573) B5488573
theorem B1714791 : Blo 1713057 1714791 := bstep (se 1 (by rfl) ⟨1286093, by rfl⟩ : syracuseStep 1714791 = 2572187) B2572187
theorem B1927975 : Blo 1713057 1927975 := bstep (se 1 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 1927975 = 2891963) B2891963
theorem B5491547 : Blo 1713057 5491547 := bstep (se 1 (by rfl) ⟨4118660, by rfl⟩ : syracuseStep 5491547 = 8237321) B8237321
theorem B7425199 : Blo 1713057 7425199 := bstep (se 1 (by rfl) ⟨5568899, by rfl⟩ : syracuseStep 7425199 = 11137799) B11137799
theorem B13020425 : Blo 1713057 13020425 := bstep (se 2 (by rfl) ⟨4882659, by rfl⟩ : syracuseStep 13020425 = 9765319) B9765319
theorem B3255707 : Blo 1713057 3255707 := bstep (se 1 (by rfl) ⟨2441780, by rfl⟩ : syracuseStep 3255707 = 4883561) B4883561
theorem B3911123 : Blo 1713057 3911123 := bstep (se 1 (by rfl) ⟨2933342, by rfl⟩ : syracuseStep 3911123 = 5866685) B5866685
theorem B6180455 : Blo 1713057 6180455 := bstep (se 1 (by rfl) ⟨4635341, by rfl⟩ : syracuseStep 6180455 = 9270683) B9270683
theorem B12529259 : Blo 1713057 12529259 := bstep (se 1 (by rfl) ⟨9396944, by rfl⟩ : syracuseStep 12529259 = 18793889) B18793889
theorem B8793787 : Blo 1713057 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B5492711 : Blo 1713057 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B1929199 : Blo 1713057 1929199 := bstep (se 1 (by rfl) ⟨1446899, by rfl⟩ : syracuseStep 1929199 = 2893799) B2893799
theorem B1831015 : Blo 1713057 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B1929343 : Blo 1713057 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B2035867 : Blo 1713057 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B3854555 : Blo 1713057 3854555 := bstep (se 1 (by rfl) ⟨2890916, by rfl⟩ : syracuseStep 3854555 = 5781833) B5781833
theorem B5861639 : Blo 1713057 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B6508937 : Blo 1713057 6508937 := bstep (se 2 (by rfl) ⟨2440851, by rfl⟩ : syracuseStep 6508937 = 4881703) B4881703
theorem B13906349 : Blo 1713057 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B3854825 : Blo 1713057 3854825 := bstep (se 2 (by rfl) ⟨1445559, by rfl⟩ : syracuseStep 3854825 = 2891119) B2891119
theorem B18535007 : Blo 1713057 18535007 := bstep (se 1 (by rfl) ⟨13901255, by rfl⟩ : syracuseStep 18535007 = 27802511) B27802511
theorem B13898429 : Blo 1713057 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B6509423 : Blo 1713057 6509423 := bstep (se 1 (by rfl) ⟨4882067, by rfl⟩ : syracuseStep 6509423 = 9764135) B9764135
theorem B4338643 : Blo 1713057 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B3855329 : Blo 1713057 3855329 := bstep (se 2 (by rfl) ⟨1445748, by rfl⟩ : syracuseStep 3855329 = 2891497) B2891497
theorem B3855455 : Blo 1713057 3855455 := bstep (se 1 (by rfl) ⟨2891591, by rfl⟩ : syracuseStep 3855455 = 5783183) B5783183
theorem B12358979 : Blo 1713057 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B37057985 : Blo 1713057 37057985 := bstep (se 2 (by rfl) ⟨13896744, by rfl⟩ : syracuseStep 37057985 = 27793489) B27793489
theorem B88036901 : Blo 1713057 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B2569961 : Blo 1713057 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B4339433 : Blo 1713057 4339433 := bstep (se 2 (by rfl) ⟨1627287, by rfl⟩ : syracuseStep 4339433 = 3254575) B3254575
theorem B2569967 : Blo 1713057 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B3299143 : Blo 1713057 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B3856211 : Blo 1713057 3856211 := bstep (se 1 (by rfl) ⟨2892158, by rfl⟩ : syracuseStep 3856211 = 5784317) B5784317
theorem B9394139 : Blo 1713057 9394139 := bstep (se 1 (by rfl) ⟨7045604, by rfl⟩ : syracuseStep 9394139 = 14091209) B14091209
theorem B9394319 : Blo 1713057 9394319 := bstep (se 1 (by rfl) ⟨7045739, by rfl⟩ : syracuseStep 9394319 = 14091479) B14091479
theorem B29702315 : Blo 1713057 29702315 := bstep (se 1 (by rfl) ⟨22276736, by rfl⟩ : syracuseStep 29702315 = 44553473) B44553473
theorem B2570423 : Blo 1713057 2570423 := bstep (se 1 (by rfl) ⟨1927817, by rfl⟩ : syracuseStep 2570423 = 3855635) B3855635
theorem B8353975 : Blo 1713057 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B2570471 : Blo 1713057 2570471 := bstep (se 1 (by rfl) ⟨1927853, by rfl⟩ : syracuseStep 2570471 = 3855707) B3855707
theorem B4176107 : Blo 1713057 4176107 := bstep (se 1 (by rfl) ⟨3132080, by rfl⟩ : syracuseStep 4176107 = 6264161) B6264161
theorem B3856697 : Blo 1713057 3856697 := bstep (se 2 (by rfl) ⟨1446261, by rfl⟩ : syracuseStep 3856697 = 2892523) B2892523
theorem B14637455 : Blo 1713057 14637455 := bstep (se 1 (by rfl) ⟨10978091, by rfl⟩ : syracuseStep 14637455 = 21956183) B21956183
theorem B8681903 : Blo 1713057 8681903 := bstep (se 1 (by rfl) ⟨6511427, by rfl⟩ : syracuseStep 8681903 = 13022855) B13022855
theorem B2570843 : Blo 1713057 2570843 := bstep (se 1 (by rfl) ⟨1928132, by rfl⟩ : syracuseStep 2570843 = 3856265) B3856265
theorem B13892201 : Blo 1713057 13892201 := bstep (se 2 (by rfl) ⟨5209575, by rfl⟩ : syracuseStep 13892201 = 10419151) B10419151
theorem B2570987 : Blo 1713057 2570987 := bstep (se 1 (by rfl) ⟨1928240, by rfl⟩ : syracuseStep 2570987 = 3856481) B3856481
theorem B4119283 : Blo 1713057 4119283 := bstep (se 1 (by rfl) ⟨3089462, by rfl⟩ : syracuseStep 4119283 = 6178925) B6178925
theorem B2571017 : Blo 1713057 2571017 := bstep (se 2 (by rfl) ⟨964131, by rfl⟩ : syracuseStep 2571017 = 1928263) B1928263
theorem B5782319 : Blo 1713057 5782319 := bstep (se 1 (by rfl) ⟨4336739, by rfl⟩ : syracuseStep 5782319 = 8673479) B8673479
theorem B7519067 : Blo 1713057 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B6511549 : Blo 1713057 6511549 := bstep (se 3 (by rfl) ⟨1220915, by rfl⟩ : syracuseStep 6511549 = 2441831) B2441831
theorem B12213251 : Blo 1713057 12213251 := bstep (se 1 (by rfl) ⟨9159938, by rfl⟩ : syracuseStep 12213251 = 18319877) B18319877
theorem B40647845 : Blo 1713057 40647845 := bstep (se 4 (by rfl) ⟨3810735, by rfl⟩ : syracuseStep 40647845 = 7621471) B7621471
theorem B3857615 : Blo 1713057 3857615 := bstep (se 1 (by rfl) ⟨2893211, by rfl⟩ : syracuseStep 3857615 = 5786423) B5786423
theorem B8232263 : Blo 1713057 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B5782967 : Blo 1713057 5782967 := bstep (se 1 (by rfl) ⟨4337225, by rfl⟩ : syracuseStep 5782967 = 8674451) B8674451
theorem B3857993 : Blo 1713057 3857993 := bstep (se 2 (by rfl) ⟨1446747, by rfl⟩ : syracuseStep 3857993 = 2893495) B2893495
theorem B2571887 : Blo 1713057 2571887 := bstep (se 1 (by rfl) ⟨1928915, by rfl⟩ : syracuseStep 2571887 = 3857831) B3857831
theorem B10714799 : Blo 1713057 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B4120283 : Blo 1713057 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B2572007 : Blo 1713057 2572007 := bstep (se 1 (by rfl) ⟨1929005, by rfl⟩ : syracuseStep 2572007 = 3858011) B3858011
theorem B2891551 : Blo 1713057 2891551 := bstep (se 1 (by rfl) ⟨2168663, by rfl⟩ : syracuseStep 2891551 = 4337327) B4337327
theorem B4882319 : Blo 1713057 4882319 := bstep (se 1 (by rfl) ⟨3661739, by rfl⟩ : syracuseStep 4882319 = 7323479) B7323479
theorem B9756571 : Blo 1713057 9756571 := bstep (se 1 (by rfl) ⟨7317428, by rfl⟩ : syracuseStep 9756571 = 14634857) B14634857
theorem B4120475 : Blo 1713057 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B2572199 : Blo 1713057 2572199 := bstep (se 1 (by rfl) ⟨1929149, by rfl⟩ : syracuseStep 2572199 = 3858299) B3858299
theorem B5783507 : Blo 1713057 5783507 := bstep (se 1 (by rfl) ⟨4337630, by rfl⟩ : syracuseStep 5783507 = 8675261) B8675261
theorem B3088361 : Blo 1713057 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B2891767 : Blo 1713057 2891767 := bstep (se 1 (by rfl) ⟨2168825, by rfl⟩ : syracuseStep 2891767 = 4337651) B4337651
theorem B2441353 : Blo 1713057 2441353 := bstep (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) B1831015
theorem B2572457 : Blo 1713057 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B3907759 : Blo 1713057 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B25051517 : Blo 1713057 25051517 := bstep (se 3 (by rfl) ⟨4697159, by rfl⟩ : syracuseStep 25051517 = 9394319) B9394319
theorem B9265619 : Blo 1713057 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B4883105 : Blo 1713057 4883105 := bstep (se 2 (by rfl) ⟨1831164, by rfl⟩ : syracuseStep 4883105 = 3662329) B3662329
theorem B10978375 : Blo 1713057 10978375 := bstep (se 1 (by rfl) ⟨8233781, by rfl⟩ : syracuseStep 10978375 = 16467563) B16467563
theorem B1713307 : Blo 1713057 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B2892955 : Blo 1713057 2892955 := bstep (se 1 (by rfl) ⟨2169716, by rfl⟩ : syracuseStep 2892955 = 4339433) B4339433
theorem B1713311 : Blo 1713057 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B10429661 : Blo 1713057 10429661 := bstep (se 3 (by rfl) ⟨1955561, by rfl⟩ : syracuseStep 10429661 = 3911123) B3911123
theorem B5784857 : Blo 1713057 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B19801543 : Blo 1713057 19801543 := bstep (se 1 (by rfl) ⟨14851157, by rfl⟩ : syracuseStep 19801543 = 29702315) B29702315
theorem B1713615 : Blo 1713057 1713615 := bstep (se 1 (by rfl) ⟨1285211, by rfl⟩ : syracuseStep 1713615 = 2570423) B2570423
theorem B1713647 : Blo 1713057 1713647 := bstep (se 1 (by rfl) ⟨1285235, by rfl⟩ : syracuseStep 1713647 = 2570471) B2570471
theorem B9758303 : Blo 1713057 9758303 := bstep (se 1 (by rfl) ⟨7318727, by rfl⟩ : syracuseStep 9758303 = 14637455) B14637455
theorem B6506203 : Blo 1713057 6506203 := bstep (se 1 (by rfl) ⟨4879652, by rfl⟩ : syracuseStep 6506203 = 9759305) B9759305
theorem B1713895 : Blo 1713057 1713895 := bstep (se 1 (by rfl) ⟨1285421, by rfl⟩ : syracuseStep 1713895 = 2570843) B2570843
theorem B1713991 : Blo 1713057 1713991 := bstep (se 1 (by rfl) ⟨1285493, by rfl⟩ : syracuseStep 1713991 = 2570987) B2570987
theorem B1714011 : Blo 1713057 1714011 := bstep (se 1 (by rfl) ⟨1285508, by rfl⟩ : syracuseStep 1714011 = 2571017) B2571017
theorem B11725049 : Blo 1713057 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B10987933 : Blo 1713057 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B1714591 : Blo 1713057 1714591 := bstep (se 1 (by rfl) ⟨1285943, by rfl⟩ : syracuseStep 1714591 = 2571887) B2571887
theorem B2746855 : Blo 1713057 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B1714671 : Blo 1713057 1714671 := bstep (se 1 (by rfl) ⟨1286003, by rfl⟩ : syracuseStep 1714671 = 2572007) B2572007
theorem B3254879 : Blo 1713057 3254879 := bstep (se 1 (by rfl) ⟨2441159, by rfl⟩ : syracuseStep 3254879 = 4882319) B4882319
theorem B1714799 : Blo 1713057 1714799 := bstep (se 1 (by rfl) ⟨1286099, by rfl⟩ : syracuseStep 1714799 = 2572199) B2572199
theorem B2058907 : Blo 1713057 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B1715015 : Blo 1713057 1715015 := bstep (se 1 (by rfl) ⟨1286261, by rfl⟩ : syracuseStep 1715015 = 2572523) B2572523
theorem B1715055 : Blo 1713057 1715055 := bstep (se 1 (by rfl) ⟨1286291, by rfl⟩ : syracuseStep 1715055 = 2572583) B2572583
theorem B2714489 : Blo 1713057 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B27798547 : Blo 1713057 27798547 := bstep (se 1 (by rfl) ⟨20848910, by rfl⟩ : syracuseStep 27798547 = 41697821) B41697821
theorem B12356671 : Blo 1713057 12356671 := bstep (se 1 (by rfl) ⟨9267503, by rfl⟩ : syracuseStep 12356671 = 18535007) B18535007
theorem B4337003 : Blo 1713057 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B5492377 : Blo 1713057 5492377 := bstep (se 2 (by rfl) ⟨2059641, by rfl⟩ : syracuseStep 5492377 = 4119283) B4119283
theorem B58691267 : Blo 1713057 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B6262759 : Blo 1713057 6262759 := bstep (se 1 (by rfl) ⟨4697069, by rfl⟩ : syracuseStep 6262759 = 9394139) B9394139
theorem B9760763 : Blo 1713057 9760763 := bstep (se 1 (by rfl) ⟨7320572, by rfl⟩ : syracuseStep 9760763 = 14641145) B14641145
theorem B9900265 : Blo 1713057 9900265 := bstep (se 2 (by rfl) ⟨3712599, by rfl⟩ : syracuseStep 9900265 = 7425199) B7425199
theorem B6951197 : Blo 1713057 6951197 := bstep (se 3 (by rfl) ⟨1303349, by rfl⟩ : syracuseStep 6951197 = 2606699) B2606699
theorem B5787935 : Blo 1713057 5787935 := bstep (se 1 (by rfl) ⟨4340951, by rfl⟩ : syracuseStep 5787935 = 8681903) B8681903
theorem B4878731 : Blo 1713057 4878731 := bstep (se 1 (by rfl) ⟨3659048, by rfl⟩ : syracuseStep 4878731 = 7318097) B7318097
theorem B9261467 : Blo 1713057 9261467 := bstep (se 1 (by rfl) ⟨6946100, by rfl⟩ : syracuseStep 9261467 = 13892201) B13892201
theorem B3854879 : Blo 1713057 3854879 := bstep (se 1 (by rfl) ⟨2891159, by rfl⟩ : syracuseStep 3854879 = 5782319) B5782319
theorem B8680283 : Blo 1713057 8680283 := bstep (se 1 (by rfl) ⟨6510212, by rfl⟩ : syracuseStep 8680283 = 13020425) B13020425
theorem B3855311 : Blo 1713057 3855311 := bstep (se 1 (by rfl) ⟨2891483, by rfl⟩ : syracuseStep 3855311 = 5782967) B5782967
theorem B3855401 : Blo 1713057 3855401 := bstep (se 2 (by rfl) ⟨1445775, by rfl⟩ : syracuseStep 3855401 = 2891551) B2891551
theorem B8352839 : Blo 1713057 8352839 := bstep (se 1 (by rfl) ⟨6264629, by rfl⟩ : syracuseStep 8352839 = 12529259) B12529259
theorem B44545141 : Blo 1713057 44545141 := bstep (se 5 (by rfl) ⟨2088053, by rfl⟩ : syracuseStep 44545141 = 4176107) B4176107
theorem B3855671 : Blo 1713057 3855671 := bstep (se 1 (by rfl) ⟨2891753, by rfl⟩ : syracuseStep 3855671 = 5783507) B5783507
theorem B3855689 : Blo 1713057 3855689 := bstep (se 2 (by rfl) ⟨1445883, by rfl⟩ : syracuseStep 3855689 = 2891767) B2891767
theorem B2569703 : Blo 1713057 2569703 := bstep (se 1 (by rfl) ⟨1927277, by rfl⟩ : syracuseStep 2569703 = 3854555) B3854555
theorem B11138633 : Blo 1713057 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B4339291 : Blo 1713057 4339291 := bstep (se 1 (by rfl) ⟨3254468, by rfl⟩ : syracuseStep 4339291 = 6508937) B6508937
theorem B3855977 : Blo 1713057 3855977 := bstep (se 2 (by rfl) ⟨1445991, by rfl⟩ : syracuseStep 3855977 = 2891983) B2891983
theorem B9270899 : Blo 1713057 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B2569883 : Blo 1713057 2569883 := bstep (se 1 (by rfl) ⟨1927412, by rfl⟩ : syracuseStep 2569883 = 3854825) B3854825
theorem B4339615 : Blo 1713057 4339615 := bstep (se 1 (by rfl) ⟨3254711, by rfl⟩ : syracuseStep 4339615 = 6509423) B6509423
theorem B2570219 : Blo 1713057 2570219 := bstep (se 1 (by rfl) ⟨1927664, by rfl⟩ : syracuseStep 2570219 = 3855329) B3855329
theorem B2570303 : Blo 1713057 2570303 := bstep (se 1 (by rfl) ⟨1927727, by rfl⟩ : syracuseStep 2570303 = 3855455) B3855455
theorem B8239319 : Blo 1713057 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B3856607 : Blo 1713057 3856607 := bstep (se 1 (by rfl) ⟨2892455, by rfl⟩ : syracuseStep 3856607 = 5784911) B5784911
theorem B32938271 : Blo 1713057 32938271 := bstep (se 1 (by rfl) ⟨24703703, by rfl⟩ : syracuseStep 32938271 = 49407407) B49407407
theorem B3856679 : Blo 1713057 3856679 := bstep (se 1 (by rfl) ⟨2892509, by rfl⟩ : syracuseStep 3856679 = 5785019) B5785019
theorem B24705323 : Blo 1713057 24705323 := bstep (se 1 (by rfl) ⟨18528992, by rfl⟩ : syracuseStep 24705323 = 37057985) B37057985
theorem B2570633 : Blo 1713057 2570633 := bstep (se 2 (by rfl) ⟨963987, by rfl⟩ : syracuseStep 2570633 = 1927975) B1927975
theorem B2570807 : Blo 1713057 2570807 := bstep (se 1 (by rfl) ⟨1928105, by rfl⟩ : syracuseStep 2570807 = 3856211) B3856211
theorem B8682065 : Blo 1713057 8682065 := bstep (se 2 (by rfl) ⟨3255774, by rfl⟩ : syracuseStep 8682065 = 6511549) B6511549
theorem B21961307 : Blo 1713057 21961307 := bstep (se 1 (by rfl) ⟨16470980, by rfl⟩ : syracuseStep 21961307 = 32941961) B32941961
theorem B3857039 : Blo 1713057 3857039 := bstep (se 1 (by rfl) ⟨2892779, by rfl⟩ : syracuseStep 3857039 = 5785559) B5785559
theorem B3857129 : Blo 1713057 3857129 := bstep (se 2 (by rfl) ⟨1446423, by rfl⟩ : syracuseStep 3857129 = 2892847) B2892847
theorem B2317033 : Blo 1713057 2317033 := bstep (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) B1737775
theorem B2169595 : Blo 1713057 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B24697655 : Blo 1713057 24697655 := bstep (se 1 (by rfl) ⟨18523241, by rfl⟩ : syracuseStep 24697655 = 37046483) B37046483
theorem B8674127 : Blo 1713057 8674127 := bstep (se 1 (by rfl) ⟨6505595, by rfl⟩ : syracuseStep 8674127 = 13011191) B13011191
theorem B2571131 : Blo 1713057 2571131 := bstep (se 1 (by rfl) ⟨1928348, by rfl⟩ : syracuseStep 2571131 = 3856697) B3856697
theorem B28572797 : Blo 1713057 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B5012711 : Blo 1713057 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B3661031 : Blo 1713057 3661031 := bstep (se 1 (by rfl) ⟨2745773, by rfl⟩ : syracuseStep 3661031 = 5491547) B5491547
theorem B8142167 : Blo 1713057 8142167 := bstep (se 1 (by rfl) ⟨6106625, by rfl⟩ : syracuseStep 8142167 = 12213251) B12213251
theorem B27098563 : Blo 1713057 27098563 := bstep (se 1 (by rfl) ⟨20323922, by rfl⟩ : syracuseStep 27098563 = 40647845) B40647845
theorem B2571743 : Blo 1713057 2571743 := bstep (se 1 (by rfl) ⟨1928807, by rfl⟩ : syracuseStep 2571743 = 3857615) B3857615
theorem B5488175 : Blo 1713057 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B2170471 : Blo 1713057 2170471 := bstep (se 1 (by rfl) ⟨1627853, by rfl⟩ : syracuseStep 2170471 = 3255707) B3255707
theorem B2571995 : Blo 1713057 2571995 := bstep (se 1 (by rfl) ⟨1928996, by rfl⟩ : syracuseStep 2571995 = 3857993) B3857993
theorem B4120303 : Blo 1713057 4120303 := bstep (se 1 (by rfl) ⟨3090227, by rfl⟩ : syracuseStep 4120303 = 6180455) B6180455
theorem B4398857 : Blo 1713057 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B13008761 : Blo 1713057 13008761 := bstep (se 2 (by rfl) ⟨4878285, by rfl⟩ : syracuseStep 13008761 = 9756571) B9756571
theorem B14647229 : Blo 1713057 14647229 := bstep (se 3 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 14647229 = 5492711) B5492711
theorem B2572265 : Blo 1713057 2572265 := bstep (se 2 (by rfl) ⟨964599, by rfl⟩ : syracuseStep 2572265 = 1929199) B1929199
theorem B22274237 : Blo 1713057 22274237 := bstep (se 3 (by rfl) ⟨4176419, by rfl⟩ : syracuseStep 22274237 = 8352839) B8352839
theorem B3858623 : Blo 1713057 3858623 := bstep (se 1 (by rfl) ⟨2893967, by rfl⟩ : syracuseStep 3858623 = 5787935) B5787935
theorem B5210345 : Blo 1713057 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B3252487 : Blo 1713057 3252487 := bstep (se 1 (by rfl) ⟨2439365, by rfl⟩ : syracuseStep 3252487 = 4878731) B4878731
theorem B6177079 : Blo 1713057 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B27812429 : Blo 1713057 27812429 := bstep (se 3 (by rfl) ⟨5214830, by rfl⟩ : syracuseStep 27812429 = 10429661) B10429661
theorem B2745209 : Blo 1713057 2745209 := bstep (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) B2058907
theorem B3089377 : Blo 1713057 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B1713135 : Blo 1713057 1713135 := bstep (se 1 (by rfl) ⟨1284851, by rfl⟩ : syracuseStep 1713135 = 2569703) B2569703
theorem B2892793 : Blo 1713057 2892793 := bstep (se 2 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 2892793 = 2169595) B2169595
theorem B6505535 : Blo 1713057 6505535 := bstep (se 1 (by rfl) ⟨4879151, by rfl⟩ : syracuseStep 6505535 = 9758303) B9758303
theorem B1713255 : Blo 1713057 1713255 := bstep (se 1 (by rfl) ⟨1284941, by rfl⟩ : syracuseStep 1713255 = 2569883) B2569883
theorem B1713479 : Blo 1713057 1713479 := bstep (se 1 (by rfl) ⟨1285109, by rfl⟩ : syracuseStep 1713479 = 2570219) B2570219
theorem B1713535 : Blo 1713057 1713535 := bstep (se 1 (by rfl) ⟨1285151, by rfl⟩ : syracuseStep 1713535 = 2570303) B2570303
theorem B16475561 : Blo 1713057 16475561 := bstep (se 2 (by rfl) ⟨6178335, by rfl⟩ : syracuseStep 16475561 = 12356671) B12356671
theorem B59393521 : Blo 1713057 59393521 := bstep (se 2 (by rfl) ⟨22272570, by rfl⟩ : syracuseStep 59393521 = 44545141) B44545141
theorem B7816699 : Blo 1713057 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B1713755 : Blo 1713057 1713755 := bstep (se 1 (by rfl) ⟨1285316, by rfl⟩ : syracuseStep 1713755 = 2570633) B2570633
theorem B1713871 : Blo 1713057 1713871 := bstep (se 1 (by rfl) ⟨1285403, by rfl⟩ : syracuseStep 1713871 = 2570807) B2570807
theorem B14640871 : Blo 1713057 14640871 := bstep (se 1 (by rfl) ⟨10980653, by rfl⟩ : syracuseStep 14640871 = 21961307) B21961307
theorem B1714087 : Blo 1713057 1714087 := bstep (se 1 (by rfl) ⟨1285565, by rfl⟩ : syracuseStep 1714087 = 2571131) B2571131
theorem B19048531 : Blo 1713057 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B5785721 : Blo 1713057 5785721 := bstep (se 2 (by rfl) ⟨2169645, by rfl⟩ : syracuseStep 5785721 = 4339291) B4339291
theorem B2893961 : Blo 1713057 2893961 := bstep (se 2 (by rfl) ⟨1085235, by rfl⟩ : syracuseStep 2893961 = 2170471) B2170471
theorem B1714495 : Blo 1713057 1714495 := bstep (se 1 (by rfl) ⟨1285871, by rfl⟩ : syracuseStep 1714495 = 2571743) B2571743
theorem B39127511 : Blo 1713057 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B1714663 : Blo 1713057 1714663 := bstep (se 1 (by rfl) ⟨1285997, by rfl⟩ : syracuseStep 1714663 = 2571995) B2571995
theorem B14649893 : Blo 1713057 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B5786153 : Blo 1713057 5786153 := bstep (se 2 (by rfl) ⟨2169807, by rfl⟩ : syracuseStep 5786153 = 4339615) B4339615
theorem B8350345 : Blo 1713057 8350345 := bstep (se 2 (by rfl) ⟨3131379, by rfl⟩ : syracuseStep 8350345 = 6262759) B6262759
theorem B1714843 : Blo 1713057 1714843 := bstep (se 1 (by rfl) ⟨1286132, by rfl⟩ : syracuseStep 1714843 = 2572265) B2572265
theorem B6507175 : Blo 1713057 6507175 := bstep (se 1 (by rfl) ⟨4880381, by rfl⟩ : syracuseStep 6507175 = 9760763) B9760763
theorem B1714971 : Blo 1713057 1714971 := bstep (se 1 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 1714971 = 2572457) B2572457
theorem B3255137 : Blo 1713057 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B13200353 : Blo 1713057 13200353 := bstep (se 2 (by rfl) ⟨4950132, by rfl⟩ : syracuseStep 13200353 = 9900265) B9900265
theorem B3255403 : Blo 1713057 3255403 := bstep (se 1 (by rfl) ⟨2441552, by rfl⟩ : syracuseStep 3255403 = 4883105) B4883105
theorem B14650577 : Blo 1713057 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B5786855 : Blo 1713057 5786855 := bstep (se 1 (by rfl) ⟨4340141, by rfl⟩ : syracuseStep 5786855 = 8680283) B8680283
theorem B21712445 : Blo 1713057 21712445 := bstep (se 3 (by rfl) ⟨4071083, by rfl⟩ : syracuseStep 21712445 = 8142167) B8142167
theorem B7425755 : Blo 1713057 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B6180599 : Blo 1713057 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B37064729 : Blo 1713057 37064729 := bstep (se 2 (by rfl) ⟨13899273, by rfl⟩ : syracuseStep 37064729 = 27798547) B27798547
theorem B5492879 : Blo 1713057 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B21958847 : Blo 1713057 21958847 := bstep (se 1 (by rfl) ⟨16469135, by rfl⟩ : syracuseStep 21958847 = 32938271) B32938271
theorem B16470215 : Blo 1713057 16470215 := bstep (se 1 (by rfl) ⟨12352661, by rfl⟩ : syracuseStep 16470215 = 24705323) B24705323
theorem B5788043 : Blo 1713057 5788043 := bstep (se 1 (by rfl) ⟨4341032, by rfl⟩ : syracuseStep 5788043 = 8682065) B8682065
theorem B36131417 : Blo 1713057 36131417 := bstep (se 2 (by rfl) ⟨13549281, by rfl⟩ : syracuseStep 36131417 = 27098563) B27098563
theorem B5493737 : Blo 1713057 5493737 := bstep (se 2 (by rfl) ⟨2060151, by rfl⟩ : syracuseStep 5493737 = 4120303) B4120303
theorem B3658783 : Blo 1713057 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B8672507 : Blo 1713057 8672507 := bstep (se 1 (by rfl) ⟨6504380, by rfl⟩ : syracuseStep 8672507 = 13008761) B13008761
theorem B4634131 : Blo 1713057 4634131 := bstep (se 1 (by rfl) ⟨3475598, by rfl⟩ : syracuseStep 4634131 = 6951197) B6951197
theorem B16701011 : Blo 1713057 16701011 := bstep (se 1 (by rfl) ⟨12525758, by rfl⟩ : syracuseStep 16701011 = 25051517) B25051517
theorem B6174311 : Blo 1713057 6174311 := bstep (se 1 (by rfl) ⟨4630733, by rfl⟩ : syracuseStep 6174311 = 9261467) B9261467
theorem B2569919 : Blo 1713057 2569919 := bstep (se 1 (by rfl) ⟨1927439, by rfl⟩ : syracuseStep 2569919 = 3854879) B3854879
theorem B2570207 : Blo 1713057 2570207 := bstep (se 1 (by rfl) ⟨1927655, by rfl⟩ : syracuseStep 2570207 = 3855311) B3855311
theorem B2570267 : Blo 1713057 2570267 := bstep (se 1 (by rfl) ⟨1927700, by rfl⟩ : syracuseStep 2570267 = 3855401) B3855401
theorem B29292677 : Blo 1713057 29292677 := bstep (se 4 (by rfl) ⟨2746188, by rfl⟩ : syracuseStep 29292677 = 5492377) B5492377
theorem B3856571 : Blo 1713057 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B2570447 : Blo 1713057 2570447 := bstep (se 1 (by rfl) ⟨1927835, by rfl⟩ : syracuseStep 2570447 = 3855671) B3855671
theorem B2570459 : Blo 1713057 2570459 := bstep (se 1 (by rfl) ⟨1927844, by rfl⟩ : syracuseStep 2570459 = 3855689) B3855689
theorem B2570651 : Blo 1713057 2570651 := bstep (se 1 (by rfl) ⟨1927988, by rfl⟩ : syracuseStep 2570651 = 3855977) B3855977
theorem B14637833 : Blo 1713057 14637833 := bstep (se 2 (by rfl) ⟨5489187, by rfl⟩ : syracuseStep 14637833 = 10978375) B10978375
theorem B2571071 : Blo 1713057 2571071 := bstep (se 1 (by rfl) ⟨1928303, by rfl⟩ : syracuseStep 2571071 = 3856607) B3856607
theorem B2571119 : Blo 1713057 2571119 := bstep (se 1 (by rfl) ⟨1928339, by rfl⟩ : syracuseStep 2571119 = 3856679) B3856679
theorem B3857273 : Blo 1713057 3857273 := bstep (se 2 (by rfl) ⟨1446477, by rfl⟩ : syracuseStep 3857273 = 2892955) B2892955
theorem B2169919 : Blo 1713057 2169919 := bstep (se 1 (by rfl) ⟨1627439, by rfl⟩ : syracuseStep 2169919 = 3254879) B3254879
theorem B2571359 : Blo 1713057 2571359 := bstep (se 1 (by rfl) ⟨1928519, by rfl⟩ : syracuseStep 2571359 = 3857039) B3857039
theorem B2571419 : Blo 1713057 2571419 := bstep (se 1 (by rfl) ⟨1928564, by rfl⟩ : syracuseStep 2571419 = 3857129) B3857129
theorem B16465103 : Blo 1713057 16465103 := bstep (se 1 (by rfl) ⟨12348827, by rfl⟩ : syracuseStep 16465103 = 24697655) B24697655
theorem B5782751 : Blo 1713057 5782751 := bstep (se 1 (by rfl) ⟨4337063, by rfl⟩ : syracuseStep 5782751 = 8674127) B8674127
theorem B1809659 : Blo 1713057 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B26402057 : Blo 1713057 26402057 := bstep (se 2 (by rfl) ⟨9900771, by rfl⟩ : syracuseStep 26402057 = 19801543) B19801543
theorem B3341807 : Blo 1713057 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B2440687 : Blo 1713057 2440687 := bstep (se 1 (by rfl) ⟨1830515, by rfl⟩ : syracuseStep 2440687 = 3661031) B3661031
theorem B2891335 : Blo 1713057 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B8674937 : Blo 1713057 8674937 := bstep (se 2 (by rfl) ⟨3253101, by rfl⟩ : syracuseStep 8674937 = 6506203) B6506203
theorem B2932571 : Blo 1713057 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B9764819 : Blo 1713057 9764819 := bstep (se 1 (by rfl) ⟨7323614, by rfl⟩ : syracuseStep 9764819 = 14647229) B14647229
theorem B3661919 : Blo 1713057 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B14639231 : Blo 1713057 14639231 := bstep (se 1 (by rfl) ⟨10979423, by rfl⟩ : syracuseStep 14639231 = 21958847) B21958847
theorem B2572415 : Blo 1713057 2572415 := bstep (se 1 (by rfl) ⟨1929311, by rfl⟩ : syracuseStep 2572415 = 3858623) B3858623
theorem B3858695 : Blo 1713057 3858695 := bstep (se 1 (by rfl) ⟨2894021, by rfl⟩ : syracuseStep 3858695 = 5788043) B5788043
theorem B13894253 : Blo 1713057 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B3662491 : Blo 1713057 3662491 := bstep (se 1 (by rfl) ⟨2746868, by rfl⟩ : syracuseStep 3662491 = 5493737) B5493737
theorem B4825757 : Blo 1713057 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B11133793 : Blo 1713057 11133793 := bstep (se 2 (by rfl) ⟨4175172, by rfl⟩ : syracuseStep 11133793 = 8350345) B8350345
theorem B8676233 : Blo 1713057 8676233 := bstep (se 2 (by rfl) ⟨3253587, by rfl⟩ : syracuseStep 8676233 = 6507175) B6507175
theorem B11134007 : Blo 1713057 11134007 := bstep (se 1 (by rfl) ⟨8350505, by rfl⟩ : syracuseStep 11134007 = 16701011) B16701011
theorem B1713279 : Blo 1713057 1713279 := bstep (se 1 (by rfl) ⟨1284959, by rfl⟩ : syracuseStep 1713279 = 2569919) B2569919
theorem B1713471 : Blo 1713057 1713471 := bstep (se 1 (by rfl) ⟨1285103, by rfl⟩ : syracuseStep 1713471 = 2570207) B2570207
theorem B1713511 : Blo 1713057 1713511 := bstep (se 1 (by rfl) ⟨1285133, by rfl⟩ : syracuseStep 1713511 = 2570267) B2570267
theorem B2893225 : Blo 1713057 2893225 := bstep (se 2 (by rfl) ⟨1084959, by rfl⟩ : syracuseStep 2893225 = 2169919) B2169919
theorem B1713631 : Blo 1713057 1713631 := bstep (se 1 (by rfl) ⟨1285223, by rfl⟩ : syracuseStep 1713631 = 2570447) B2570447
theorem B1713639 : Blo 1713057 1713639 := bstep (se 1 (by rfl) ⟨1285229, by rfl⟩ : syracuseStep 1713639 = 2570459) B2570459
theorem B1713767 : Blo 1713057 1713767 := bstep (se 1 (by rfl) ⟨1285325, by rfl⟩ : syracuseStep 1713767 = 2570651) B2570651
theorem B26085007 : Blo 1713057 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B9766595 : Blo 1713057 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B9758555 : Blo 1713057 9758555 := bstep (se 1 (by rfl) ⟨7318916, by rfl⟩ : syracuseStep 9758555 = 14637833) B14637833
theorem B1714047 : Blo 1713057 1714047 := bstep (se 1 (by rfl) ⟨1285535, by rfl⟩ : syracuseStep 1714047 = 2571071) B2571071
theorem B1714079 : Blo 1713057 1714079 := bstep (se 1 (by rfl) ⟨1285559, by rfl⟩ : syracuseStep 1714079 = 2571119) B2571119
theorem B3254249 : Blo 1713057 3254249 := bstep (se 2 (by rfl) ⟨1220343, by rfl⟩ : syracuseStep 3254249 = 2440687) B2440687
theorem B8800235 : Blo 1713057 8800235 := bstep (se 1 (by rfl) ⟨6600176, by rfl⟩ : syracuseStep 8800235 = 13200353) B13200353
theorem B10422265 : Blo 1713057 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B6178841 : Blo 1713057 6178841 := bstep (se 2 (by rfl) ⟨2317065, by rfl⟩ : syracuseStep 6178841 = 4634131) B4634131
theorem B1714239 : Blo 1713057 1714239 := bstep (se 1 (by rfl) ⟨1285679, by rfl⟩ : syracuseStep 1714239 = 2571359) B2571359
theorem B1714279 : Blo 1713057 1714279 := bstep (se 1 (by rfl) ⟨1285709, by rfl⟩ : syracuseStep 1714279 = 2571419) B2571419
theorem B9767051 : Blo 1713057 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B4950503 : Blo 1713057 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B24709819 : Blo 1713057 24709819 := bstep (se 1 (by rfl) ⟨18532364, by rfl⟩ : syracuseStep 24709819 = 37064729) B37064729
theorem B25398041 : Blo 1713057 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B10980143 : Blo 1713057 10980143 := bstep (se 1 (by rfl) ⟨8235107, by rfl⟩ : syracuseStep 10980143 = 16470215) B16470215
theorem B4336649 : Blo 1713057 4336649 := bstep (se 2 (by rfl) ⟨1626243, by rfl⟩ : syracuseStep 4336649 = 3252487) B3252487
theorem B18541619 : Blo 1713057 18541619 := bstep (se 1 (by rfl) ⟨13906214, by rfl⟩ : syracuseStep 18541619 = 27812429) B27812429
theorem B24087611 : Blo 1713057 24087611 := bstep (se 1 (by rfl) ⟨18065708, by rfl⟩ : syracuseStep 24087611 = 36131417) B36131417
theorem B4337023 : Blo 1713057 4337023 := bstep (se 1 (by rfl) ⟨3252767, by rfl⟩ : syracuseStep 4337023 = 6505535) B6505535
theorem B65859317 : Blo 1713057 65859317 := bstep (se 5 (by rfl) ⟨3087155, by rfl⟩ : syracuseStep 65859317 = 6174311) B6174311
theorem B4878377 : Blo 1713057 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B1929307 : Blo 1713057 1929307 := bstep (se 1 (by rfl) ⟨1446980, by rfl⟩ : syracuseStep 1929307 = 2893961) B2893961
theorem B32944421 : Blo 1713057 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B3855113 : Blo 1713057 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B3855167 : Blo 1713057 3855167 := bstep (se 1 (by rfl) ⟨2891375, by rfl⟩ : syracuseStep 3855167 = 5782751) B5782751
theorem B17601371 : Blo 1713057 17601371 := bstep (se 1 (by rfl) ⟨13201028, by rfl⟩ : syracuseStep 17601371 = 26402057) B26402057
theorem B7820189 : Blo 1713057 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B7320557 : Blo 1713057 7320557 := bstep (se 3 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 7320557 = 2745209) B2745209
theorem B6509879 : Blo 1713057 6509879 := bstep (se 1 (by rfl) ⟨4882409, by rfl⟩ : syracuseStep 6509879 = 9764819) B9764819
theorem B14849491 : Blo 1713057 14849491 := bstep (se 1 (by rfl) ⟨11137118, by rfl⟩ : syracuseStep 14849491 = 22274237) B22274237
theorem B5781671 : Blo 1713057 5781671 := bstep (se 1 (by rfl) ⟨4336253, by rfl⟩ : syracuseStep 5781671 = 8672507) B8672507
theorem B10983707 : Blo 1713057 10983707 := bstep (se 1 (by rfl) ⟨8237780, by rfl⟩ : syracuseStep 10983707 = 16475561) B16475561
theorem B4119169 : Blo 1713057 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B3857057 : Blo 1713057 3857057 := bstep (se 2 (by rfl) ⟨1446396, by rfl⟩ : syracuseStep 3857057 = 2892793) B2892793
theorem B3857147 : Blo 1713057 3857147 := bstep (se 1 (by rfl) ⟨2892860, by rfl⟩ : syracuseStep 3857147 = 5785721) B5785721
theorem B19528451 : Blo 1713057 19528451 := bstep (se 1 (by rfl) ⟨14646338, by rfl⟩ : syracuseStep 19528451 = 29292677) B29292677
theorem B2571047 : Blo 1713057 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B4340537 : Blo 1713057 4340537 := bstep (se 2 (by rfl) ⟨1627701, by rfl⟩ : syracuseStep 4340537 = 3255403) B3255403
theorem B3857435 : Blo 1713057 3857435 := bstep (se 1 (by rfl) ⟨2893076, by rfl⟩ : syracuseStep 3857435 = 5786153) B5786153
theorem B2170091 : Blo 1713057 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B2571515 : Blo 1713057 2571515 := bstep (se 1 (by rfl) ⟨1928636, by rfl⟩ : syracuseStep 2571515 = 3857273) B3857273
theorem B79191361 : Blo 1713057 79191361 := bstep (se 2 (by rfl) ⟨29696760, by rfl⟩ : syracuseStep 79191361 = 59393521) B59393521
theorem B10976735 : Blo 1713057 10976735 := bstep (se 1 (by rfl) ⟨8232551, by rfl⟩ : syracuseStep 10976735 = 16465103) B16465103
theorem B3857903 : Blo 1713057 3857903 := bstep (se 1 (by rfl) ⟨2893427, by rfl⟩ : syracuseStep 3857903 = 5786855) B5786855
theorem B19521161 : Blo 1713057 19521161 := bstep (se 2 (by rfl) ⟨7320435, by rfl⟩ : syracuseStep 19521161 = 14640871) B14640871
theorem B2227871 : Blo 1713057 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B14474963 : Blo 1713057 14474963 := bstep (se 1 (by rfl) ⟨10856222, by rfl⟩ : syracuseStep 14474963 = 21712445) B21712445
theorem B5783291 : Blo 1713057 5783291 := bstep (se 1 (by rfl) ⟨4337468, by rfl⟩ : syracuseStep 5783291 = 8674937) B8674937
theorem B4120399 : Blo 1713057 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B3252251 : Blo 1713057 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B2441279 : Blo 1713057 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B2572409 : Blo 1713057 2572409 := bstep (se 2 (by rfl) ⟨964653, by rfl⟩ : syracuseStep 2572409 = 1929307) B1929307
theorem B2572463 : Blo 1713057 2572463 := bstep (se 1 (by rfl) ⟨1929347, by rfl⟩ : syracuseStep 2572463 = 3858695) B3858695
theorem B21962947 : Blo 1713057 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B5784155 : Blo 1713057 5784155 := bstep (se 1 (by rfl) ⟨4338116, by rfl⟩ : syracuseStep 5784155 = 8676233) B8676233
theorem B7422671 : Blo 1713057 7422671 := bstep (se 1 (by rfl) ⟨5567003, by rfl⟩ : syracuseStep 7422671 = 11134007) B11134007
theorem B4883321 : Blo 1713057 4883321 := bstep (se 2 (by rfl) ⟨1831245, by rfl⟩ : syracuseStep 4883321 = 3662491) B3662491
theorem B6505703 : Blo 1713057 6505703 := bstep (se 1 (by rfl) ⟨4879277, by rfl⟩ : syracuseStep 6505703 = 9758555) B9758555
theorem B5866823 : Blo 1713057 5866823 := bstep (se 1 (by rfl) ⟨4400117, by rfl⟩ : syracuseStep 5866823 = 8800235) B8800235
theorem B5940989 : Blo 1713057 5940989 := bstep (se 3 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 5940989 = 2227871) B2227871
theorem B105588481 : Blo 1713057 105588481 := bstep (se 2 (by rfl) ⟨39595680, by rfl⟩ : syracuseStep 105588481 = 79191361) B79191361
theorem B13018967 : Blo 1713057 13018967 := bstep (se 1 (by rfl) ⟨9764225, by rfl⟩ : syracuseStep 13018967 = 19528451) B19528451
theorem B1714031 : Blo 1713057 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B2893691 : Blo 1713057 2893691 := bstep (se 1 (by rfl) ⟨2170268, by rfl⟩ : syracuseStep 2893691 = 4340537) B4340537
theorem B16058407 : Blo 1713057 16058407 := bstep (se 1 (by rfl) ⟨12043805, by rfl⟩ : syracuseStep 16058407 = 24087611) B24087611
theorem B1714343 : Blo 1713057 1714343 := bstep (se 1 (by rfl) ⟨1285757, by rfl⟩ : syracuseStep 1714343 = 2571515) B2571515
theorem B7317823 : Blo 1713057 7317823 := bstep (se 1 (by rfl) ⟨5488367, by rfl⟩ : syracuseStep 7317823 = 10976735) B10976735
theorem B13896353 : Blo 1713057 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B9759487 : Blo 1713057 9759487 := bstep (se 1 (by rfl) ⟨7319615, by rfl⟩ : syracuseStep 9759487 = 14639231) B14639231
theorem B1714943 : Blo 1713057 1714943 := bstep (se 1 (by rfl) ⟨1286207, by rfl⟩ : syracuseStep 1714943 = 2572415) B2572415
theorem B270912437 : Blo 1713057 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B11734247 : Blo 1713057 11734247 := bstep (se 1 (by rfl) ⟨8800685, by rfl⟩ : syracuseStep 11734247 = 17601371) B17601371
theorem B5213459 : Blo 1713057 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B5786909 : Blo 1713057 5786909 := bstep (se 3 (by rfl) ⟨1085045, by rfl⟩ : syracuseStep 5786909 = 2170091) B2170091
theorem B5492225 : Blo 1713057 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B3854447 : Blo 1713057 3854447 := bstep (se 1 (by rfl) ⟨2890835, by rfl⟩ : syracuseStep 3854447 = 5781671) B5781671
theorem B59380229 : Blo 1713057 59380229 := bstep (se 4 (by rfl) ⟨5566896, by rfl⟩ : syracuseStep 59380229 = 11133793) B11133793
theorem B7320095 : Blo 1713057 7320095 := bstep (se 1 (by rfl) ⟨5490071, by rfl⟩ : syracuseStep 7320095 = 10980143) B10980143
theorem B34780009 : Blo 1713057 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B13014107 : Blo 1713057 13014107 := bstep (se 1 (by rfl) ⟨9760580, by rfl⟩ : syracuseStep 13014107 = 19521161) B19521161
theorem B5493865 : Blo 1713057 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B43906211 : Blo 1713057 43906211 := bstep (se 1 (by rfl) ⟨32929658, by rfl⟩ : syracuseStep 43906211 = 65859317) B65859317
theorem B3855527 : Blo 1713057 3855527 := bstep (se 1 (by rfl) ⟨2891645, by rfl⟩ : syracuseStep 3855527 = 5783291) B5783291
theorem B9262835 : Blo 1713057 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B3217171 : Blo 1713057 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B2570075 : Blo 1713057 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B2570111 : Blo 1713057 2570111 := bstep (se 1 (by rfl) ⟨1927583, by rfl⟩ : syracuseStep 2570111 = 3855167) B3855167
theorem B4880371 : Blo 1713057 4880371 := bstep (se 1 (by rfl) ⟨3660278, by rfl⟩ : syracuseStep 4880371 = 7320557) B7320557
theorem B4339919 : Blo 1713057 4339919 := bstep (se 1 (by rfl) ⟨3254939, by rfl⟩ : syracuseStep 4339919 = 6509879) B6509879
theorem B32946425 : Blo 1713057 32946425 := bstep (se 2 (by rfl) ⟨12354909, by rfl⟩ : syracuseStep 32946425 = 24709819) B24709819
theorem B6511063 : Blo 1713057 6511063 := bstep (se 1 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 6511063 = 9766595) B9766595
theorem B2169499 : Blo 1713057 2169499 := bstep (se 1 (by rfl) ⟨1627124, by rfl⟩ : syracuseStep 2169499 = 3254249) B3254249
theorem B4119227 : Blo 1713057 4119227 := bstep (se 1 (by rfl) ⟨3089420, by rfl⟩ : syracuseStep 4119227 = 6178841) B6178841
theorem B6511367 : Blo 1713057 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B7322471 : Blo 1713057 7322471 := bstep (se 1 (by rfl) ⟨5491853, by rfl⟩ : syracuseStep 7322471 = 10983707) B10983707
theorem B3300335 : Blo 1713057 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2571371 : Blo 1713057 2571371 := bstep (se 1 (by rfl) ⟨1928528, by rfl⟩ : syracuseStep 2571371 = 3857057) B3857057
theorem B2571431 : Blo 1713057 2571431 := bstep (se 1 (by rfl) ⟨1928573, by rfl⟩ : syracuseStep 2571431 = 3857147) B3857147
theorem B5782697 : Blo 1713057 5782697 := bstep (se 2 (by rfl) ⟨2168511, by rfl⟩ : syracuseStep 5782697 = 4337023) B4337023
theorem B3857633 : Blo 1713057 3857633 := bstep (se 2 (by rfl) ⟨1446612, by rfl⟩ : syracuseStep 3857633 = 2893225) B2893225
theorem B19799321 : Blo 1713057 19799321 := bstep (se 2 (by rfl) ⟨7424745, by rfl⟩ : syracuseStep 19799321 = 14849491) B14849491
theorem B2891099 : Blo 1713057 2891099 := bstep (se 1 (by rfl) ⟨2168324, by rfl⟩ : syracuseStep 2891099 = 4336649) B4336649
theorem B2571623 : Blo 1713057 2571623 := bstep (se 1 (by rfl) ⟨1928717, by rfl⟩ : syracuseStep 2571623 = 3857435) B3857435
theorem B12361079 : Blo 1713057 12361079 := bstep (se 1 (by rfl) ⟨9270809, by rfl⟩ : syracuseStep 12361079 = 18541619) B18541619
theorem B2571935 : Blo 1713057 2571935 := bstep (se 1 (by rfl) ⟨1928951, by rfl⟩ : syracuseStep 2571935 = 3857903) B3857903
theorem B9649975 : Blo 1713057 9649975 := bstep (se 1 (by rfl) ⟨7237481, by rfl⟩ : syracuseStep 9649975 = 14474963) B14474963
theorem B9757097 : Blo 1713057 9757097 := bstep (se 2 (by rfl) ⟨3658911, by rfl⟩ : syracuseStep 9757097 = 7317823) B7317823
theorem B4948447 : Blo 1713057 4948447 := bstep (se 1 (by rfl) ⟨3711335, by rfl⟩ : syracuseStep 4948447 = 7422671) B7422671
theorem B8676071 : Blo 1713057 8676071 := bstep (se 1 (by rfl) ⟨6507053, by rfl⟩ : syracuseStep 8676071 = 13014107) B13014107
theorem B52798189 : Blo 1713057 52798189 := bstep (se 3 (by rfl) ⟨9899660, by rfl⟩ : syracuseStep 52798189 = 19799321) B19799321
theorem B29270807 : Blo 1713057 29270807 := bstep (se 1 (by rfl) ⟨21953105, by rfl⟩ : syracuseStep 29270807 = 43906211) B43906211
theorem B2892665 : Blo 1713057 2892665 := bstep (se 2 (by rfl) ⟨1084749, by rfl⟩ : syracuseStep 2892665 = 2169499) B2169499
theorem B1713383 : Blo 1713057 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B1713407 : Blo 1713057 1713407 := bstep (se 1 (by rfl) ⟨1285055, by rfl⟩ : syracuseStep 1713407 = 2570111) B2570111
theorem B2893279 : Blo 1713057 2893279 := bstep (se 1 (by rfl) ⟨2169959, by rfl⟩ : syracuseStep 2893279 = 4339919) B4339919
theorem B7325153 : Blo 1713057 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B21964283 : Blo 1713057 21964283 := bstep (se 1 (by rfl) ⟨16473212, by rfl⟩ : syracuseStep 21964283 = 32946425) B32946425
theorem B2746151 : Blo 1713057 2746151 := bstep (se 1 (by rfl) ⟨2059613, by rfl⟩ : syracuseStep 2746151 = 4119227) B4119227
theorem B1714247 : Blo 1713057 1714247 := bstep (se 1 (by rfl) ⟨1285685, by rfl⟩ : syracuseStep 1714247 = 2571371) B2571371
theorem B1714287 : Blo 1713057 1714287 := bstep (se 1 (by rfl) ⟨1285715, by rfl⟩ : syracuseStep 1714287 = 2571431) B2571431
theorem B3475639 : Blo 1713057 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B1927399 : Blo 1713057 1927399 := bstep (se 1 (by rfl) ⟨1445549, by rfl⟩ : syracuseStep 1927399 = 2891099) B2891099
theorem B1714415 : Blo 1713057 1714415 := bstep (se 1 (by rfl) ⟨1285811, by rfl⟩ : syracuseStep 1714415 = 2571623) B2571623
theorem B1714623 : Blo 1713057 1714623 := bstep (se 1 (by rfl) ⟨1285967, by rfl⟩ : syracuseStep 1714623 = 2571935) B2571935
theorem B6507161 : Blo 1713057 6507161 := bstep (se 2 (by rfl) ⟨2440185, by rfl⟩ : syracuseStep 6507161 = 4880371) B4880371
theorem B1714939 : Blo 1713057 1714939 := bstep (se 1 (by rfl) ⟨1286204, by rfl⟩ : syracuseStep 1714939 = 2572409) B2572409
theorem B1714975 : Blo 1713057 1714975 := bstep (se 1 (by rfl) ⟨1286231, by rfl⟩ : syracuseStep 1714975 = 2572463) B2572463
theorem B39586819 : Blo 1713057 39586819 := bstep (se 1 (by rfl) ⟨29690114, by rfl⟩ : syracuseStep 39586819 = 59380229) B59380229
theorem B3255547 : Blo 1713057 3255547 := bstep (se 1 (by rfl) ⟨2441660, by rfl⟩ : syracuseStep 3255547 = 4883321) B4883321
theorem B4337135 : Blo 1713057 4337135 := bstep (se 1 (by rfl) ⟨3252851, by rfl⟩ : syracuseStep 4337135 = 6505703) B6505703
theorem B3911215 : Blo 1713057 3911215 := bstep (se 1 (by rfl) ⟨2933411, by rfl⟩ : syracuseStep 3911215 = 5866823) B5866823
theorem B13012649 : Blo 1713057 13012649 := bstep (se 2 (by rfl) ⟨4879743, by rfl⟩ : syracuseStep 13012649 = 9759487) B9759487
theorem B3960659 : Blo 1713057 3960659 := bstep (se 1 (by rfl) ⟨2970494, by rfl⟩ : syracuseStep 3960659 = 5940989) B5940989
theorem B8679311 : Blo 1713057 8679311 := bstep (se 1 (by rfl) ⟨6509483, by rfl⟩ : syracuseStep 8679311 = 13018967) B13018967
theorem B1929127 : Blo 1713057 1929127 := bstep (se 1 (by rfl) ⟨1446845, by rfl⟩ : syracuseStep 1929127 = 2893691) B2893691
theorem B2200223 : Blo 1713057 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B3855131 : Blo 1713057 3855131 := bstep (se 1 (by rfl) ⟨2891348, by rfl⟩ : syracuseStep 3855131 = 5782697) B5782697
theorem B140784641 : Blo 1713057 140784641 := bstep (se 2 (by rfl) ⟨52794240, by rfl⟩ : syracuseStep 140784641 = 105588481) B105588481
theorem B4289561 : Blo 1713057 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B12866633 : Blo 1713057 12866633 := bstep (se 2 (by rfl) ⟨4824987, by rfl⟩ : syracuseStep 12866633 = 9649975) B9649975
theorem B21411209 : Blo 1713057 21411209 := bstep (se 2 (by rfl) ⟨8029203, by rfl⟩ : syracuseStep 21411209 = 16058407) B16058407
theorem B8672669 : Blo 1713057 8672669 := bstep (se 3 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 8672669 = 3252251) B3252251
theorem B2569631 : Blo 1713057 2569631 := bstep (se 1 (by rfl) ⟨1927223, by rfl⟩ : syracuseStep 2569631 = 3854447) B3854447
theorem B6510077 : Blo 1713057 6510077 := bstep (se 3 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 6510077 = 2441279) B2441279
theorem B29283929 : Blo 1713057 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B4880063 : Blo 1713057 4880063 := bstep (se 1 (by rfl) ⟨3660047, by rfl⟩ : syracuseStep 4880063 = 7320095) B7320095
theorem B3856103 : Blo 1713057 3856103 := bstep (se 1 (by rfl) ⟨2892077, by rfl⟩ : syracuseStep 3856103 = 5784155) B5784155
theorem B8681417 : Blo 1713057 8681417 := bstep (se 2 (by rfl) ⟨3255531, by rfl⟩ : syracuseStep 8681417 = 6511063) B6511063
theorem B2570351 : Blo 1713057 2570351 := bstep (se 1 (by rfl) ⟨1927763, by rfl⟩ : syracuseStep 2570351 = 3855527) B3855527
theorem B46373345 : Blo 1713057 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B6175223 : Blo 1713057 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B9264235 : Blo 1713057 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B4340911 : Blo 1713057 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B4881647 : Blo 1713057 4881647 := bstep (se 1 (by rfl) ⟨3661235, by rfl⟩ : syracuseStep 4881647 = 7322471) B7322471
theorem B180608291 : Blo 1713057 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B2571755 : Blo 1713057 2571755 := bstep (se 1 (by rfl) ⟨1928816, by rfl⟩ : syracuseStep 2571755 = 3857633) B3857633
theorem B7822831 : Blo 1713057 7822831 := bstep (se 1 (by rfl) ⟨5867123, by rfl⟩ : syracuseStep 7822831 = 11734247) B11734247
theorem B3857939 : Blo 1713057 3857939 := bstep (se 1 (by rfl) ⟨2893454, by rfl⟩ : syracuseStep 3857939 = 5786909) B5786909
theorem B8240719 : Blo 1713057 8240719 := bstep (se 1 (by rfl) ⟨6180539, by rfl⟩ : syracuseStep 8240719 = 12361079) B12361079
theorem B3661483 : Blo 1713057 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B6504731 : Blo 1713057 6504731 := bstep (se 1 (by rfl) ⟨4878548, by rfl⟩ : syracuseStep 6504731 = 9757097) B9757097
theorem B5784047 : Blo 1713057 5784047 := bstep (se 1 (by rfl) ⟨4338035, by rfl⟩ : syracuseStep 5784047 = 8676071) B8676071
theorem B19513871 : Blo 1713057 19513871 := bstep (se 1 (by rfl) ⟨14635403, by rfl⟩ : syracuseStep 19513871 = 29270807) B29270807
theorem B93856427 : Blo 1713057 93856427 := bstep (se 1 (by rfl) ⟨70392320, by rfl⟩ : syracuseStep 93856427 = 140784641) B140784641
theorem B2859707 : Blo 1713057 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B8577755 : Blo 1713057 8577755 := bstep (se 1 (by rfl) ⟨6433316, by rfl⟩ : syracuseStep 8577755 = 12866633) B12866633
theorem B1713087 : Blo 1713057 1713087 := bstep (se 1 (by rfl) ⟨1284815, by rfl⟩ : syracuseStep 1713087 = 2569631) B2569631
theorem B4883435 : Blo 1713057 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B19522619 : Blo 1713057 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B3253375 : Blo 1713057 3253375 := bstep (se 1 (by rfl) ⟨2440031, by rfl⟩ : syracuseStep 3253375 = 4880063) B4880063
theorem B52782425 : Blo 1713057 52782425 := bstep (se 2 (by rfl) ⟨19793409, by rfl⟩ : syracuseStep 52782425 = 39586819) B39586819
theorem B1713567 : Blo 1713057 1713567 := bstep (se 1 (by rfl) ⟨1285175, by rfl⟩ : syracuseStep 1713567 = 2570351) B2570351
theorem B5867261 : Blo 1713057 5867261 := bstep (se 3 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 5867261 = 2200223) B2200223
theorem B10430441 : Blo 1713057 10430441 := bstep (se 2 (by rfl) ⟨3911415, by rfl⟩ : syracuseStep 10430441 = 7822831) B7822831
theorem B10987625 : Blo 1713057 10987625 := bstep (se 2 (by rfl) ⟨4120359, by rfl⟩ : syracuseStep 10987625 = 8240719) B8240719
theorem B3254431 : Blo 1713057 3254431 := bstep (se 1 (by rfl) ⟨2440823, by rfl⟩ : syracuseStep 3254431 = 4881647) B4881647
theorem B1714503 : Blo 1713057 1714503 := bstep (se 1 (by rfl) ⟨1285877, by rfl⟩ : syracuseStep 1714503 = 2571755) B2571755
theorem B2640439 : Blo 1713057 2640439 := bstep (se 1 (by rfl) ⟨1980329, by rfl⟩ : syracuseStep 2640439 = 3960659) B3960659
theorem B5786207 : Blo 1713057 5786207 := bstep (se 1 (by rfl) ⟨4339655, by rfl⟩ : syracuseStep 5786207 = 8679311) B8679311
theorem B1928443 : Blo 1713057 1928443 := bstep (se 1 (by rfl) ⟨1446332, by rfl⟩ : syracuseStep 1928443 = 2892665) B2892665
theorem B6597929 : Blo 1713057 6597929 := bstep (se 2 (by rfl) ⟨2474223, by rfl⟩ : syracuseStep 6597929 = 4948447) B4948447
theorem B14274139 : Blo 1713057 14274139 := bstep (se 1 (by rfl) ⟨10705604, by rfl⟩ : syracuseStep 14274139 = 21411209) B21411209
theorem B70397585 : Blo 1713057 70397585 := bstep (se 2 (by rfl) ⟨26399094, by rfl⟩ : syracuseStep 70397585 = 52798189) B52798189
theorem B14642855 : Blo 1713057 14642855 := bstep (se 1 (by rfl) ⟨10982141, by rfl⟩ : syracuseStep 14642855 = 21964283) B21964283
theorem B1830767 : Blo 1713057 1830767 := bstep (se 1 (by rfl) ⟨1373075, by rfl⟩ : syracuseStep 1830767 = 2746151) B2746151
theorem B5787611 : Blo 1713057 5787611 := bstep (se 1 (by rfl) ⟨4340708, by rfl⟩ : syracuseStep 5787611 = 8681417) B8681417
theorem B5787881 : Blo 1713057 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B4116815 : Blo 1713057 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B4338107 : Blo 1713057 4338107 := bstep (se 1 (by rfl) ⟨3253580, by rfl⟩ : syracuseStep 4338107 = 6507161) B6507161
theorem B5214953 : Blo 1713057 5214953 := bstep (se 2 (by rfl) ⟨1955607, by rfl⟩ : syracuseStep 5214953 = 3911215) B3911215
theorem B4634185 : Blo 1713057 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B2569865 : Blo 1713057 2569865 := bstep (se 2 (by rfl) ⟨963699, by rfl⟩ : syracuseStep 2569865 = 1927399) B1927399
theorem B2570087 : Blo 1713057 2570087 := bstep (se 1 (by rfl) ⟨1927565, by rfl⟩ : syracuseStep 2570087 = 3855131) B3855131
theorem B5781779 : Blo 1713057 5781779 := bstep (se 1 (by rfl) ⟨4336334, by rfl⟩ : syracuseStep 5781779 = 8672669) B8672669
theorem B4340051 : Blo 1713057 4340051 := bstep (se 1 (by rfl) ⟨3255038, by rfl⟩ : syracuseStep 4340051 = 6510077) B6510077
theorem B2570735 : Blo 1713057 2570735 := bstep (se 1 (by rfl) ⟨1928051, by rfl⟩ : syracuseStep 2570735 = 3856103) B3856103
theorem B12352313 : Blo 1713057 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B30915563 : Blo 1713057 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B4340729 : Blo 1713057 4340729 := bstep (se 2 (by rfl) ⟨1627773, by rfl⟩ : syracuseStep 4340729 = 3255547) B3255547
theorem B3857705 : Blo 1713057 3857705 := bstep (se 2 (by rfl) ⟨1446639, by rfl⟩ : syracuseStep 3857705 = 2893279) B2893279
theorem B120405527 : Blo 1713057 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B4881977 : Blo 1713057 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B2891423 : Blo 1713057 2891423 := bstep (se 1 (by rfl) ⟨2168567, by rfl⟩ : syracuseStep 2891423 = 4337135) B4337135
theorem B2571959 : Blo 1713057 2571959 := bstep (se 1 (by rfl) ⟨1928969, by rfl⟩ : syracuseStep 2571959 = 3857939) B3857939
theorem B8675099 : Blo 1713057 8675099 := bstep (se 1 (by rfl) ⟨6506324, by rfl⟩ : syracuseStep 8675099 = 13012649) B13012649
theorem B2572169 : Blo 1713057 2572169 := bstep (se 2 (by rfl) ⟨964563, by rfl⟩ : syracuseStep 2572169 = 1929127) B1929127
theorem B3858587 : Blo 1713057 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B2744543 : Blo 1713057 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B14082341 : Blo 1713057 14082341 := bstep (se 4 (by rfl) ⟨1320219, by rfl⟩ : syracuseStep 14082341 = 2640439) B2640439
theorem B2892071 : Blo 1713057 2892071 := bstep (se 1 (by rfl) ⟨2169053, by rfl⟩ : syracuseStep 2892071 = 4338107) B4338107
theorem B13009247 : Blo 1713057 13009247 := bstep (se 1 (by rfl) ⟨9756935, by rfl⟩ : syracuseStep 13009247 = 19513871) B19513871
theorem B62570951 : Blo 1713057 62570951 := bstep (se 1 (by rfl) ⟨46928213, by rfl⟩ : syracuseStep 62570951 = 93856427) B93856427
theorem B5718503 : Blo 1713057 5718503 := bstep (se 1 (by rfl) ⟨4288877, by rfl⟩ : syracuseStep 5718503 = 8577755) B8577755
theorem B1713243 : Blo 1713057 1713243 := bstep (se 1 (by rfl) ⟨1284932, by rfl⟩ : syracuseStep 1713243 = 2569865) B2569865
theorem B1713391 : Blo 1713057 1713391 := bstep (se 1 (by rfl) ⟨1285043, by rfl⟩ : syracuseStep 1713391 = 2570087) B2570087
theorem B7325083 : Blo 1713057 7325083 := bstep (se 1 (by rfl) ⟨5493812, by rfl⟩ : syracuseStep 7325083 = 10987625) B10987625
theorem B2893367 : Blo 1713057 2893367 := bstep (se 1 (by rfl) ⟨2170025, by rfl⟩ : syracuseStep 2893367 = 4340051) B4340051
theorem B1713823 : Blo 1713057 1713823 := bstep (se 1 (by rfl) ⟨1285367, by rfl⟩ : syracuseStep 1713823 = 2570735) B2570735
theorem B8234875 : Blo 1713057 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B2893819 : Blo 1713057 2893819 := bstep (se 1 (by rfl) ⟨2170364, by rfl⟩ : syracuseStep 2893819 = 4340729) B4340729
theorem B6178913 : Blo 1713057 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B19032185 : Blo 1713057 19032185 := bstep (se 2 (by rfl) ⟨7137069, by rfl⟩ : syracuseStep 19032185 = 14274139) B14274139
theorem B3254651 : Blo 1713057 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B1927615 : Blo 1713057 1927615 := bstep (se 1 (by rfl) ⟨1445711, by rfl⟩ : syracuseStep 1927615 = 2891423) B2891423
theorem B1714639 : Blo 1713057 1714639 := bstep (se 1 (by rfl) ⟨1285979, by rfl⟩ : syracuseStep 1714639 = 2571959) B2571959
theorem B1714779 : Blo 1713057 1714779 := bstep (se 1 (by rfl) ⟨1286084, by rfl⟩ : syracuseStep 1714779 = 2572169) B2572169
theorem B4336487 : Blo 1713057 4336487 := bstep (se 1 (by rfl) ⟨3252365, by rfl⟩ : syracuseStep 4336487 = 6504731) B6504731
theorem B3255623 : Blo 1713057 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B35188283 : Blo 1713057 35188283 := bstep (se 1 (by rfl) ⟨26391212, by rfl⟩ : syracuseStep 35188283 = 52782425) B52782425
theorem B3911507 : Blo 1713057 3911507 := bstep (se 1 (by rfl) ⟨2933630, by rfl⟩ : syracuseStep 3911507 = 5867261) B5867261
theorem B4337833 : Blo 1713057 4337833 := bstep (se 2 (by rfl) ⟨1626687, by rfl⟩ : syracuseStep 4337833 = 3253375) B3253375
theorem B3854519 : Blo 1713057 3854519 := bstep (se 1 (by rfl) ⟨2890889, by rfl⟩ : syracuseStep 3854519 = 5781779) B5781779
theorem B13906541 : Blo 1713057 13906541 := bstep (se 3 (by rfl) ⟨2607476, by rfl⟩ : syracuseStep 13906541 = 5214953) B5214953
theorem B80270351 : Blo 1713057 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B9761903 : Blo 1713057 9761903 := bstep (se 1 (by rfl) ⟨7321427, by rfl⟩ : syracuseStep 9761903 = 14642855) B14642855
theorem B329766005 : Blo 1713057 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B4339241 : Blo 1713057 4339241 := bstep (se 2 (by rfl) ⟨1627215, by rfl⟩ : syracuseStep 4339241 = 3254431) B3254431
theorem B3856031 : Blo 1713057 3856031 := bstep (se 1 (by rfl) ⟨2892023, by rfl⟩ : syracuseStep 3856031 = 5784047) B5784047
theorem B1906471 : Blo 1713057 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B13015079 : Blo 1713057 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B6953627 : Blo 1713057 6953627 := bstep (se 1 (by rfl) ⟨5215220, by rfl⟩ : syracuseStep 6953627 = 10430441) B10430441
theorem B2571257 : Blo 1713057 2571257 := bstep (se 2 (by rfl) ⟨964221, by rfl⟩ : syracuseStep 2571257 = 1928443) B1928443
theorem B3857471 : Blo 1713057 3857471 := bstep (se 1 (by rfl) ⟨2893103, by rfl⟩ : syracuseStep 3857471 = 5786207) B5786207
theorem B4398619 : Blo 1713057 4398619 := bstep (se 1 (by rfl) ⟨3298964, by rfl⟩ : syracuseStep 4398619 = 6597929) B6597929
theorem B2571803 : Blo 1713057 2571803 := bstep (se 1 (by rfl) ⟨1928852, by rfl⟩ : syracuseStep 2571803 = 3857705) B3857705
theorem B4882045 : Blo 1713057 4882045 := bstep (se 3 (by rfl) ⟨915383, by rfl⟩ : syracuseStep 4882045 = 1830767) B1830767
theorem B46931723 : Blo 1713057 46931723 := bstep (se 1 (by rfl) ⟨35198792, by rfl⟩ : syracuseStep 46931723 = 70397585) B70397585
theorem B5783399 : Blo 1713057 5783399 := bstep (se 1 (by rfl) ⟨4337549, by rfl⟩ : syracuseStep 5783399 = 8675099) B8675099
theorem B3858407 : Blo 1713057 3858407 := bstep (se 1 (by rfl) ⟨2893805, by rfl⟩ : syracuseStep 3858407 = 5787611) B5787611
theorem B2572391 : Blo 1713057 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B5783777 : Blo 1713057 5783777 := bstep (se 2 (by rfl) ⟨2168916, by rfl⟩ : syracuseStep 5783777 = 4337833) B4337833
theorem B41713967 : Blo 1713057 41713967 := bstep (se 1 (by rfl) ⟨31285475, by rfl⟩ : syracuseStep 41713967 = 62570951) B62570951
theorem B37552909 : Blo 1713057 37552909 := bstep (se 3 (by rfl) ⟨7041170, by rfl⟩ : syracuseStep 37552909 = 14082341) B14082341
theorem B2892827 : Blo 1713057 2892827 := bstep (se 1 (by rfl) ⟨2169620, by rfl⟩ : syracuseStep 2892827 = 4339241) B4339241
theorem B8676719 : Blo 1713057 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B9766777 : Blo 1713057 9766777 := bstep (se 2 (by rfl) ⟨3662541, by rfl⟩ : syracuseStep 9766777 = 7325083) B7325083
theorem B43919333 : Blo 1713057 43919333 := bstep (se 4 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 43919333 = 8234875) B8234875
theorem B1714171 : Blo 1713057 1714171 := bstep (se 1 (by rfl) ⟨1285628, by rfl⟩ : syracuseStep 1714171 = 2571257) B2571257
theorem B1714535 : Blo 1713057 1714535 := bstep (se 1 (by rfl) ⟨1285901, by rfl⟩ : syracuseStep 1714535 = 2571803) B2571803
theorem B2541961 : Blo 1713057 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B31287815 : Blo 1713057 31287815 := bstep (se 1 (by rfl) ⟨23465861, by rfl⟩ : syracuseStep 31287815 = 46931723) B46931723
theorem B2607671 : Blo 1713057 2607671 := bstep (se 1 (by rfl) ⟨1955753, by rfl⟩ : syracuseStep 2607671 = 3911507) B3911507
theorem B1928047 : Blo 1713057 1928047 := bstep (se 1 (by rfl) ⟨1446035, by rfl⟩ : syracuseStep 1928047 = 2892071) B2892071
theorem B50752493 : Blo 1713057 50752493 := bstep (se 3 (by rfl) ⟨9516092, by rfl⟩ : syracuseStep 50752493 = 19032185) B19032185
theorem B3812335 : Blo 1713057 3812335 := bstep (se 1 (by rfl) ⟨2859251, by rfl⟩ : syracuseStep 3812335 = 5718503) B5718503
theorem B7318781 : Blo 1713057 7318781 := bstep (se 3 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 7318781 = 2744543) B2744543
theorem B53513567 : Blo 1713057 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B6507935 : Blo 1713057 6507935 := bstep (se 1 (by rfl) ⟨4880951, by rfl⟩ : syracuseStep 6507935 = 9761903) B9761903
theorem B219844003 : Blo 1713057 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B1928911 : Blo 1713057 1928911 := bstep (se 1 (by rfl) ⟨1446683, by rfl⟩ : syracuseStep 1928911 = 2893367) B2893367
theorem B93835421 : Blo 1713057 93835421 := bstep (se 3 (by rfl) ⟨17594141, by rfl⟩ : syracuseStep 93835421 = 35188283) B35188283
theorem B18543005 : Blo 1713057 18543005 := bstep (se 3 (by rfl) ⟨3476813, by rfl⟩ : syracuseStep 18543005 = 6953627) B6953627
theorem B6509393 : Blo 1713057 6509393 := bstep (se 2 (by rfl) ⟨2441022, by rfl⟩ : syracuseStep 6509393 = 4882045) B4882045
theorem B3855599 : Blo 1713057 3855599 := bstep (se 1 (by rfl) ⟨2891699, by rfl⟩ : syracuseStep 3855599 = 5783399) B5783399
theorem B2569679 : Blo 1713057 2569679 := bstep (se 1 (by rfl) ⟨1927259, by rfl⟩ : syracuseStep 2569679 = 3854519) B3854519
theorem B8672831 : Blo 1713057 8672831 := bstep (se 1 (by rfl) ⟨6504623, by rfl⟩ : syracuseStep 8672831 = 13009247) B13009247
theorem B9271027 : Blo 1713057 9271027 := bstep (se 1 (by rfl) ⟨6953270, by rfl⟩ : syracuseStep 9271027 = 13906541) B13906541
theorem B2570153 : Blo 1713057 2570153 := bstep (se 2 (by rfl) ⟨963807, by rfl⟩ : syracuseStep 2570153 = 1927615) B1927615
theorem B2570687 : Blo 1713057 2570687 := bstep (se 1 (by rfl) ⟨1928015, by rfl⟩ : syracuseStep 2570687 = 3856031) B3856031
theorem B4119275 : Blo 1713057 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B2169767 : Blo 1713057 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B2890991 : Blo 1713057 2890991 := bstep (se 1 (by rfl) ⟨2168243, by rfl⟩ : syracuseStep 2890991 = 4336487) B4336487
theorem B5864825 : Blo 1713057 5864825 := bstep (se 2 (by rfl) ⟨2199309, by rfl⟩ : syracuseStep 5864825 = 4398619) B4398619
theorem B2571647 : Blo 1713057 2571647 := bstep (se 1 (by rfl) ⟨1928735, by rfl⟩ : syracuseStep 2571647 = 3857471) B3857471
theorem B2170415 : Blo 1713057 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B2572271 : Blo 1713057 2572271 := bstep (se 1 (by rfl) ⟨1929203, by rfl⟩ : syracuseStep 2572271 = 3858407) B3858407
theorem B3858425 : Blo 1713057 3858425 := bstep (se 2 (by rfl) ⟨1446909, by rfl⟩ : syracuseStep 3858425 = 2893819) B2893819
theorem B12362003 : Blo 1713057 12362003 := bstep (se 1 (by rfl) ⟨9271502, by rfl⟩ : syracuseStep 12362003 = 18543005) B18543005
theorem B5784479 : Blo 1713057 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B1713119 : Blo 1713057 1713119 := bstep (se 1 (by rfl) ⟨1284839, by rfl⟩ : syracuseStep 1713119 = 2569679) B2569679
theorem B50070545 : Blo 1713057 50070545 := bstep (se 2 (by rfl) ⟨18776454, by rfl⟩ : syracuseStep 50070545 = 37552909) B37552909
theorem B1713435 : Blo 1713057 1713435 := bstep (se 1 (by rfl) ⟨1285076, by rfl⟩ : syracuseStep 1713435 = 2570153) B2570153
theorem B29279555 : Blo 1713057 29279555 := bstep (se 1 (by rfl) ⟨21959666, by rfl⟩ : syracuseStep 29279555 = 43919333) B43919333
theorem B1713791 : Blo 1713057 1713791 := bstep (se 1 (by rfl) ⟨1285343, by rfl⟩ : syracuseStep 1713791 = 2570687) B2570687
theorem B20858543 : Blo 1713057 20858543 := bstep (se 1 (by rfl) ⟨15643907, by rfl⟩ : syracuseStep 20858543 = 31287815) B31287815
theorem B33834995 : Blo 1713057 33834995 := bstep (se 1 (by rfl) ⟨25376246, by rfl⟩ : syracuseStep 33834995 = 50752493) B50752493
theorem B1927327 : Blo 1713057 1927327 := bstep (se 1 (by rfl) ⟨1445495, by rfl⟩ : syracuseStep 1927327 = 2890991) B2890991
theorem B3909883 : Blo 1713057 3909883 := bstep (se 1 (by rfl) ⟨2932412, by rfl⟩ : syracuseStep 3909883 = 5864825) B5864825
theorem B1714431 : Blo 1713057 1714431 := bstep (se 1 (by rfl) ⟨1285823, by rfl⟩ : syracuseStep 1714431 = 2571647) B2571647
theorem B5786045 : Blo 1713057 5786045 := bstep (se 3 (by rfl) ⟨1084883, by rfl⟩ : syracuseStep 5786045 = 2169767) B2169767
theorem B1714847 : Blo 1713057 1714847 := bstep (se 1 (by rfl) ⟨1286135, by rfl⟩ : syracuseStep 1714847 = 2572271) B2572271
theorem B1714927 : Blo 1713057 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B62556947 : Blo 1713057 62556947 := bstep (se 1 (by rfl) ⟨46917710, by rfl⟩ : syracuseStep 62556947 = 93835421) B93835421
theorem B1928551 : Blo 1713057 1928551 := bstep (se 1 (by rfl) ⟨1446413, by rfl⟩ : syracuseStep 1928551 = 2892827) B2892827
theorem B5787773 : Blo 1713057 5787773 := bstep (se 3 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 5787773 = 2170415) B2170415
theorem B4879187 : Blo 1713057 4879187 := bstep (se 1 (by rfl) ⟨3659390, by rfl⟩ : syracuseStep 4879187 = 7318781) B7318781
theorem B4338623 : Blo 1713057 4338623 := bstep (se 1 (by rfl) ⟨3253967, by rfl⟩ : syracuseStep 4338623 = 6507935) B6507935
theorem B13022369 : Blo 1713057 13022369 := bstep (se 2 (by rfl) ⟨4883388, by rfl⟩ : syracuseStep 13022369 = 9766777) B9766777
theorem B3855851 : Blo 1713057 3855851 := bstep (se 1 (by rfl) ⟨2891888, by rfl⟩ : syracuseStep 3855851 = 5783777) B5783777
theorem B4339595 : Blo 1713057 4339595 := bstep (se 1 (by rfl) ⟨3254696, by rfl⟩ : syracuseStep 4339595 = 6509393) B6509393
theorem B111237245 : Blo 1713057 111237245 := bstep (se 3 (by rfl) ⟨20856983, by rfl⟩ : syracuseStep 111237245 = 41713967) B41713967
theorem B2570399 : Blo 1713057 2570399 := bstep (se 1 (by rfl) ⟨1927799, by rfl⟩ : syracuseStep 2570399 = 3855599) B3855599
theorem B5781887 : Blo 1713057 5781887 := bstep (se 1 (by rfl) ⟨4336415, by rfl⟩ : syracuseStep 5781887 = 8672831) B8672831
theorem B2570729 : Blo 1713057 2570729 := bstep (se 2 (by rfl) ⟨964023, by rfl⟩ : syracuseStep 2570729 = 1928047) B1928047
theorem B6953789 : Blo 1713057 6953789 := bstep (se 3 (by rfl) ⟨1303835, by rfl⟩ : syracuseStep 6953789 = 2607671) B2607671
theorem B293125337 : Blo 1713057 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B10984733 : Blo 1713057 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B13557125 : Blo 1713057 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B35675711 : Blo 1713057 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B2571881 : Blo 1713057 2571881 := bstep (se 2 (by rfl) ⟨964455, by rfl⟩ : syracuseStep 2571881 = 1928911) B1928911
theorem B12361369 : Blo 1713057 12361369 := bstep (se 2 (by rfl) ⟨4635513, by rfl⟩ : syracuseStep 12361369 = 9271027) B9271027
theorem B20332453 : Blo 1713057 20332453 := bstep (se 4 (by rfl) ⟨1906167, by rfl⟩ : syracuseStep 20332453 = 3812335) B3812335
theorem B2572283 : Blo 1713057 2572283 := bstep (se 1 (by rfl) ⟨1929212, by rfl⟩ : syracuseStep 2572283 = 3858425) B3858425
theorem B3858515 : Blo 1713057 3858515 := bstep (se 1 (by rfl) ⟨2893886, by rfl⟩ : syracuseStep 3858515 = 5787773) B5787773
theorem B8241335 : Blo 1713057 8241335 := bstep (se 1 (by rfl) ⟨6181001, by rfl⟩ : syracuseStep 8241335 = 12362003) B12362003
theorem B3252791 : Blo 1713057 3252791 := bstep (se 1 (by rfl) ⟨2439593, by rfl⟩ : syracuseStep 3252791 = 4879187) B4879187
theorem B2892415 : Blo 1713057 2892415 := bstep (se 1 (by rfl) ⟨2169311, by rfl⟩ : syracuseStep 2892415 = 4338623) B4338623
theorem B2893063 : Blo 1713057 2893063 := bstep (se 1 (by rfl) ⟨2169797, by rfl⟩ : syracuseStep 2893063 = 4339595) B4339595
theorem B1713599 : Blo 1713057 1713599 := bstep (se 1 (by rfl) ⟨1285199, by rfl⟩ : syracuseStep 1713599 = 2570399) B2570399
theorem B1713819 : Blo 1713057 1713819 := bstep (se 1 (by rfl) ⟨1285364, by rfl⟩ : syracuseStep 1713819 = 2570729) B2570729
theorem B9038083 : Blo 1713057 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B23783807 : Blo 1713057 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B1714587 : Blo 1713057 1714587 := bstep (se 1 (by rfl) ⟨1285940, by rfl⟩ : syracuseStep 1714587 = 2571881) B2571881
theorem B27109937 : Blo 1713057 27109937 := bstep (se 2 (by rfl) ⟨10166226, by rfl⟩ : syracuseStep 27109937 = 20332453) B20332453
theorem B1714855 : Blo 1713057 1714855 := bstep (se 1 (by rfl) ⟨1286141, by rfl⟩ : syracuseStep 1714855 = 2572283) B2572283
theorem B5213177 : Blo 1713057 5213177 := bstep (se 2 (by rfl) ⟨1954941, by rfl⟩ : syracuseStep 5213177 = 3909883) B3909883
theorem B13905695 : Blo 1713057 13905695 := bstep (se 1 (by rfl) ⟨10429271, by rfl⟩ : syracuseStep 13905695 = 20858543) B20858543
theorem B22556663 : Blo 1713057 22556663 := bstep (se 1 (by rfl) ⟨16917497, by rfl⟩ : syracuseStep 22556663 = 33834995) B33834995
theorem B74158163 : Blo 1713057 74158163 := bstep (se 1 (by rfl) ⟨55618622, by rfl⟩ : syracuseStep 74158163 = 111237245) B111237245
theorem B3854591 : Blo 1713057 3854591 := bstep (se 1 (by rfl) ⟨2890943, by rfl⟩ : syracuseStep 3854591 = 5781887) B5781887
theorem B195416891 : Blo 1713057 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B18543437 : Blo 1713057 18543437 := bstep (se 3 (by rfl) ⟨3476894, by rfl⟩ : syracuseStep 18543437 = 6953789) B6953789
theorem B2569769 : Blo 1713057 2569769 := bstep (se 2 (by rfl) ⟨963663, by rfl⟩ : syracuseStep 2569769 = 1927327) B1927327
theorem B3856319 : Blo 1713057 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B33380363 : Blo 1713057 33380363 := bstep (se 1 (by rfl) ⟨25035272, by rfl⟩ : syracuseStep 33380363 = 50070545) B50070545
theorem B8681579 : Blo 1713057 8681579 := bstep (se 1 (by rfl) ⟨6511184, by rfl⟩ : syracuseStep 8681579 = 13022369) B13022369
theorem B19519703 : Blo 1713057 19519703 := bstep (se 1 (by rfl) ⟨14639777, by rfl⟩ : syracuseStep 19519703 = 29279555) B29279555
theorem B2570567 : Blo 1713057 2570567 := bstep (se 1 (by rfl) ⟨1927925, by rfl⟩ : syracuseStep 2570567 = 3855851) B3855851
theorem B3857363 : Blo 1713057 3857363 := bstep (se 1 (by rfl) ⟨2893022, by rfl⟩ : syracuseStep 3857363 = 5786045) B5786045
theorem B2571401 : Blo 1713057 2571401 := bstep (se 2 (by rfl) ⟨964275, by rfl⟩ : syracuseStep 2571401 = 1928551) B1928551
theorem B41704631 : Blo 1713057 41704631 := bstep (se 1 (by rfl) ⟨31278473, by rfl⟩ : syracuseStep 41704631 = 62556947) B62556947
theorem B7323155 : Blo 1713057 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B16481825 : Blo 1713057 16481825 := bstep (se 2 (by rfl) ⟨6180684, by rfl⟩ : syracuseStep 16481825 = 12361369) B12361369
theorem B49438775 : Blo 1713057 49438775 := bstep (se 1 (by rfl) ⟨37079081, by rfl⟩ : syracuseStep 49438775 = 74158163) B74158163
theorem B2572343 : Blo 1713057 2572343 := bstep (se 1 (by rfl) ⟨1929257, by rfl⟩ : syracuseStep 2572343 = 3858515) B3858515
theorem B12050777 : Blo 1713057 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B130277927 : Blo 1713057 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B12362291 : Blo 1713057 12362291 := bstep (se 1 (by rfl) ⟨9271718, by rfl⟩ : syracuseStep 12362291 = 18543437) B18543437
theorem B1713179 : Blo 1713057 1713179 := bstep (se 1 (by rfl) ⟨1284884, by rfl⟩ : syracuseStep 1713179 = 2569769) B2569769
theorem B1713711 : Blo 1713057 1713711 := bstep (se 1 (by rfl) ⟨1285283, by rfl⟩ : syracuseStep 1713711 = 2570567) B2570567
theorem B3475451 : Blo 1713057 3475451 := bstep (se 1 (by rfl) ⟨2606588, by rfl⟩ : syracuseStep 3475451 = 5213177) B5213177
theorem B1714267 : Blo 1713057 1714267 := bstep (se 1 (by rfl) ⟨1285700, by rfl⟩ : syracuseStep 1714267 = 2571401) B2571401
theorem B10987883 : Blo 1713057 10987883 := bstep (se 1 (by rfl) ⟨8240912, by rfl⟩ : syracuseStep 10987883 = 16481825) B16481825
theorem B22253575 : Blo 1713057 22253575 := bstep (se 1 (by rfl) ⟨16690181, by rfl⟩ : syracuseStep 22253575 = 33380363) B33380363
theorem B5787719 : Blo 1713057 5787719 := bstep (se 1 (by rfl) ⟨4340789, by rfl⟩ : syracuseStep 5787719 = 8681579) B8681579
theorem B13013135 : Blo 1713057 13013135 := bstep (se 1 (by rfl) ⟨9759851, by rfl⟩ : syracuseStep 13013135 = 19519703) B19519703
theorem B15855871 : Blo 1713057 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B9270463 : Blo 1713057 9270463 := bstep (se 1 (by rfl) ⟨6952847, by rfl⟩ : syracuseStep 9270463 = 13905695) B13905695
theorem B15037775 : Blo 1713057 15037775 := bstep (se 1 (by rfl) ⟨11278331, by rfl⟩ : syracuseStep 15037775 = 22556663) B22556663
theorem B5494223 : Blo 1713057 5494223 := bstep (se 1 (by rfl) ⟨4120667, by rfl⟩ : syracuseStep 5494223 = 8241335) B8241335
theorem B2569727 : Blo 1713057 2569727 := bstep (se 1 (by rfl) ⟨1927295, by rfl⟩ : syracuseStep 2569727 = 3854591) B3854591
theorem B2168527 : Blo 1713057 2168527 := bstep (se 1 (by rfl) ⟨1626395, by rfl⟩ : syracuseStep 2168527 = 3252791) B3252791
theorem B3856553 : Blo 1713057 3856553 := bstep (se 2 (by rfl) ⟨1446207, by rfl⟩ : syracuseStep 3856553 = 2892415) B2892415
theorem B2570879 : Blo 1713057 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B72293165 : Blo 1713057 72293165 := bstep (se 3 (by rfl) ⟨13554968, by rfl⟩ : syracuseStep 72293165 = 27109937) B27109937
theorem B3857417 : Blo 1713057 3857417 := bstep (se 2 (by rfl) ⟨1446531, by rfl⟩ : syracuseStep 3857417 = 2893063) B2893063
theorem B2571575 : Blo 1713057 2571575 := bstep (se 1 (by rfl) ⟨1928681, by rfl⟩ : syracuseStep 2571575 = 3857363) B3857363
theorem B27803087 : Blo 1713057 27803087 := bstep (se 1 (by rfl) ⟨20852315, by rfl⟩ : syracuseStep 27803087 = 41704631) B41704631
theorem B4882103 : Blo 1713057 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B29671433 : Blo 1713057 29671433 := bstep (se 2 (by rfl) ⟨11126787, by rfl⟩ : syracuseStep 29671433 = 22253575) B22253575
theorem B3858479 : Blo 1713057 3858479 := bstep (se 1 (by rfl) ⟨2893859, by rfl⟩ : syracuseStep 3858479 = 5787719) B5787719
theorem B8675423 : Blo 1713057 8675423 := bstep (se 1 (by rfl) ⟨6506567, by rfl⟩ : syracuseStep 8675423 = 13013135) B13013135
theorem B8241527 : Blo 1713057 8241527 := bstep (se 1 (by rfl) ⟨6181145, by rfl⟩ : syracuseStep 8241527 = 12362291) B12362291
theorem B3662815 : Blo 1713057 3662815 := bstep (se 1 (by rfl) ⟨2747111, by rfl⟩ : syracuseStep 3662815 = 5494223) B5494223
theorem B1713151 : Blo 1713057 1713151 := bstep (se 1 (by rfl) ⟨1284863, by rfl⟩ : syracuseStep 1713151 = 2569727) B2569727
theorem B347407805 : Blo 1713057 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B7325255 : Blo 1713057 7325255 := bstep (se 1 (by rfl) ⟨5493941, by rfl⟩ : syracuseStep 7325255 = 10987883) B10987883
theorem B1713919 : Blo 1713057 1713919 := bstep (se 1 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 1713919 = 2570879) B2570879
theorem B48195443 : Blo 1713057 48195443 := bstep (se 1 (by rfl) ⟨36146582, by rfl⟩ : syracuseStep 48195443 = 72293165) B72293165
theorem B1714383 : Blo 1713057 1714383 := bstep (se 1 (by rfl) ⟨1285787, by rfl⟩ : syracuseStep 1714383 = 2571575) B2571575
theorem B3254735 : Blo 1713057 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B32959183 : Blo 1713057 32959183 := bstep (se 1 (by rfl) ⟨24719387, by rfl⟩ : syracuseStep 32959183 = 49438775) B49438775
theorem B1714895 : Blo 1713057 1714895 := bstep (se 1 (by rfl) ⟨1286171, by rfl⟩ : syracuseStep 1714895 = 2572343) B2572343
theorem B18535391 : Blo 1713057 18535391 := bstep (se 1 (by rfl) ⟨13901543, by rfl⟩ : syracuseStep 18535391 = 27803087) B27803087
theorem B8033851 : Blo 1713057 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B21141161 : Blo 1713057 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B10025183 : Blo 1713057 10025183 := bstep (se 1 (by rfl) ⟨7518887, by rfl⟩ : syracuseStep 10025183 = 15037775) B15037775
theorem B2316967 : Blo 1713057 2316967 := bstep (se 1 (by rfl) ⟨1737725, by rfl⟩ : syracuseStep 2316967 = 3475451) B3475451
theorem B2571035 : Blo 1713057 2571035 := bstep (se 1 (by rfl) ⟨1928276, by rfl⟩ : syracuseStep 2571035 = 3856553) B3856553
theorem B12360617 : Blo 1713057 12360617 := bstep (se 2 (by rfl) ⟨4635231, by rfl⟩ : syracuseStep 12360617 = 9270463) B9270463
theorem B2571611 : Blo 1713057 2571611 := bstep (se 1 (by rfl) ⟨1928708, by rfl⟩ : syracuseStep 2571611 = 3857417) B3857417
theorem B2891369 : Blo 1713057 2891369 := bstep (se 2 (by rfl) ⟨1084263, by rfl⟩ : syracuseStep 2891369 = 2168527) B2168527
theorem B2572319 : Blo 1713057 2572319 := bstep (se 1 (by rfl) ⟨1929239, by rfl⟩ : syracuseStep 2572319 = 3858479) B3858479
theorem B5783615 : Blo 1713057 5783615 := bstep (se 1 (by rfl) ⟨4337711, by rfl⟩ : syracuseStep 5783615 = 8675423) B8675423
theorem B231605203 : Blo 1713057 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B4883503 : Blo 1713057 4883503 := bstep (se 1 (by rfl) ⟨3662627, by rfl⟩ : syracuseStep 4883503 = 7325255) B7325255
theorem B4883753 : Blo 1713057 4883753 := bstep (se 2 (by rfl) ⟨1831407, by rfl⟩ : syracuseStep 4883753 = 3662815) B3662815
theorem B1714023 : Blo 1713057 1714023 := bstep (se 1 (by rfl) ⟨1285517, by rfl⟩ : syracuseStep 1714023 = 2571035) B2571035
theorem B1714407 : Blo 1713057 1714407 := bstep (se 1 (by rfl) ⟨1285805, by rfl⟩ : syracuseStep 1714407 = 2571611) B2571611
theorem B1927579 : Blo 1713057 1927579 := bstep (se 1 (by rfl) ⟨1445684, by rfl⟩ : syracuseStep 1927579 = 2891369) B2891369
theorem B12356927 : Blo 1713057 12356927 := bstep (se 1 (by rfl) ⟨9267695, by rfl⟩ : syracuseStep 12356927 = 18535391) B18535391
theorem B43945577 : Blo 1713057 43945577 := bstep (se 2 (by rfl) ⟨16479591, by rfl⟩ : syracuseStep 43945577 = 32959183) B32959183
theorem B14094107 : Blo 1713057 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B10711801 : Blo 1713057 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B128521181 : Blo 1713057 128521181 := bstep (se 3 (by rfl) ⟨24097721, by rfl⟩ : syracuseStep 128521181 = 48195443) B48195443
theorem B19780955 : Blo 1713057 19780955 := bstep (se 1 (by rfl) ⟨14835716, by rfl⟩ : syracuseStep 19780955 = 29671433) B29671433
theorem B49428629 : Blo 1713057 49428629 := bstep (se 6 (by rfl) ⟨1158483, by rfl⟩ : syracuseStep 49428629 = 2316967) B2316967
theorem B21977405 : Blo 1713057 21977405 := bstep (se 3 (by rfl) ⟨4120763, by rfl⟩ : syracuseStep 21977405 = 8241527) B8241527
theorem B6683455 : Blo 1713057 6683455 := bstep (se 1 (by rfl) ⟨5012591, by rfl⟩ : syracuseStep 6683455 = 10025183) B10025183
theorem B2169823 : Blo 1713057 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B8240411 : Blo 1713057 8240411 := bstep (se 1 (by rfl) ⟨6180308, by rfl⟩ : syracuseStep 8240411 = 12360617) B12360617
theorem B85680787 : Blo 1713057 85680787 := bstep (se 1 (by rfl) ⟨64260590, by rfl⟩ : syracuseStep 85680787 = 128521181) B128521181
theorem B308806937 : Blo 1713057 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B2893097 : Blo 1713057 2893097 := bstep (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) B2169823
theorem B35645093 : Blo 1713057 35645093 := bstep (se 4 (by rfl) ⟨3341727, by rfl⟩ : syracuseStep 35645093 = 6683455) B6683455
theorem B29297051 : Blo 1713057 29297051 := bstep (se 1 (by rfl) ⟨21972788, by rfl⟩ : syracuseStep 29297051 = 43945577) B43945577
theorem B1714879 : Blo 1713057 1714879 := bstep (se 1 (by rfl) ⟨1286159, by rfl⟩ : syracuseStep 1714879 = 2572319) B2572319
theorem B21974429 : Blo 1713057 21974429 := bstep (se 3 (by rfl) ⟨4120205, by rfl⟩ : syracuseStep 21974429 = 8240411) B8240411
theorem B14282401 : Blo 1713057 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B32952419 : Blo 1713057 32952419 := bstep (se 1 (by rfl) ⟨24714314, by rfl⟩ : syracuseStep 32952419 = 49428629) B49428629
theorem B14651603 : Blo 1713057 14651603 := bstep (se 1 (by rfl) ⟨10988702, by rfl⟩ : syracuseStep 14651603 = 21977405) B21977405
theorem B8237951 : Blo 1713057 8237951 := bstep (se 1 (by rfl) ⟨6178463, by rfl⟩ : syracuseStep 8237951 = 12356927) B12356927
theorem B3855743 : Blo 1713057 3855743 := bstep (se 1 (by rfl) ⟨2891807, by rfl⟩ : syracuseStep 3855743 = 5783615) B5783615
theorem B2570105 : Blo 1713057 2570105 := bstep (se 2 (by rfl) ⟨963789, by rfl⟩ : syracuseStep 2570105 = 1927579) B1927579
theorem B13023341 : Blo 1713057 13023341 := bstep (se 3 (by rfl) ⟨2441876, by rfl⟩ : syracuseStep 13023341 = 4883753) B4883753
theorem B13187303 : Blo 1713057 13187303 := bstep (se 1 (by rfl) ⟨9890477, by rfl⟩ : syracuseStep 13187303 = 19780955) B19780955
theorem B6511337 : Blo 1713057 6511337 := bstep (se 2 (by rfl) ⟨2441751, by rfl⟩ : syracuseStep 6511337 = 4883503) B4883503
theorem B9396071 : Blo 1713057 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B1713403 : Blo 1713057 1713403 := bstep (se 1 (by rfl) ⟨1285052, by rfl⟩ : syracuseStep 1713403 = 2570105) B2570105
theorem B8791535 : Blo 1713057 8791535 := bstep (se 1 (by rfl) ⟨6593651, by rfl⟩ : syracuseStep 8791535 = 13187303) B13187303
theorem B19531367 : Blo 1713057 19531367 := bstep (se 1 (by rfl) ⟨14648525, by rfl⟩ : syracuseStep 19531367 = 29297051) B29297051
theorem B14649619 : Blo 1713057 14649619 := bstep (se 1 (by rfl) ⟨10987214, by rfl⟩ : syracuseStep 14649619 = 21974429) B21974429
theorem B9767735 : Blo 1713057 9767735 := bstep (se 1 (by rfl) ⟨7325801, by rfl⟩ : syracuseStep 9767735 = 14651603) B14651603
theorem B5491967 : Blo 1713057 5491967 := bstep (se 1 (by rfl) ⟨4118975, by rfl⟩ : syracuseStep 5491967 = 8237951) B8237951
theorem B114241049 : Blo 1713057 114241049 := bstep (se 2 (by rfl) ⟨42840393, by rfl⟩ : syracuseStep 114241049 = 85680787) B85680787
theorem B1928731 : Blo 1713057 1928731 := bstep (se 1 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 1928731 = 2893097) B2893097
theorem B19043201 : Blo 1713057 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B6264047 : Blo 1713057 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B21968279 : Blo 1713057 21968279 := bstep (se 1 (by rfl) ⟨16476209, by rfl⟩ : syracuseStep 21968279 = 32952419) B32952419
theorem B205871291 : Blo 1713057 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B2570495 : Blo 1713057 2570495 := bstep (se 1 (by rfl) ⟨1927871, by rfl⟩ : syracuseStep 2570495 = 3855743) B3855743
theorem B23763395 : Blo 1713057 23763395 := bstep (se 1 (by rfl) ⟨17822546, by rfl⟩ : syracuseStep 23763395 = 35645093) B35645093
theorem B8682227 : Blo 1713057 8682227 := bstep (se 1 (by rfl) ⟨6511670, by rfl⟩ : syracuseStep 8682227 = 13023341) B13023341
theorem B4340891 : Blo 1713057 4340891 := bstep (se 1 (by rfl) ⟨3255668, by rfl⟩ : syracuseStep 4340891 = 6511337) B6511337
theorem B1713663 : Blo 1713057 1713663 := bstep (se 1 (by rfl) ⟨1285247, by rfl⟩ : syracuseStep 1713663 = 2570495) B2570495
theorem B2893927 : Blo 1713057 2893927 := bstep (se 1 (by rfl) ⟨2170445, by rfl⟩ : syracuseStep 2893927 = 4340891) B4340891
theorem B19532825 : Blo 1713057 19532825 := bstep (se 2 (by rfl) ⟨7324809, by rfl⟩ : syracuseStep 19532825 = 14649619) B14649619
theorem B13020911 : Blo 1713057 13020911 := bstep (se 1 (by rfl) ⟨9765683, by rfl⟩ : syracuseStep 13020911 = 19531367) B19531367
theorem B5788151 : Blo 1713057 5788151 := bstep (se 1 (by rfl) ⟨4341113, by rfl⟩ : syracuseStep 5788151 = 8682227) B8682227
theorem B12695467 : Blo 1713057 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B14645245 : Blo 1713057 14645245 := bstep (se 3 (by rfl) ⟨2745983, by rfl⟩ : syracuseStep 14645245 = 5491967) B5491967
theorem B4176031 : Blo 1713057 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B14645519 : Blo 1713057 14645519 := bstep (se 1 (by rfl) ⟨10984139, by rfl⟩ : syracuseStep 14645519 = 21968279) B21968279
theorem B23444093 : Blo 1713057 23444093 := bstep (se 3 (by rfl) ⟨4395767, by rfl⟩ : syracuseStep 23444093 = 8791535) B8791535
theorem B137247527 : Blo 1713057 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B15842263 : Blo 1713057 15842263 := bstep (se 1 (by rfl) ⟨11881697, by rfl⟩ : syracuseStep 15842263 = 23763395) B23763395
theorem B6511823 : Blo 1713057 6511823 := bstep (se 1 (by rfl) ⟨4883867, by rfl⟩ : syracuseStep 6511823 = 9767735) B9767735
theorem B2571641 : Blo 1713057 2571641 := bstep (se 2 (by rfl) ⟨964365, by rfl⟩ : syracuseStep 2571641 = 1928731) B1928731
theorem B76160699 : Blo 1713057 76160699 := bstep (se 1 (by rfl) ⟨57120524, by rfl⟩ : syracuseStep 76160699 = 114241049) B114241049
theorem B3858569 : Blo 1713057 3858569 := bstep (se 2 (by rfl) ⟨1446963, by rfl⟩ : syracuseStep 3858569 = 2893927) B2893927
theorem B3858767 : Blo 1713057 3858767 := bstep (se 1 (by rfl) ⟨2894075, by rfl⟩ : syracuseStep 3858767 = 5788151) B5788151
theorem B91498351 : Blo 1713057 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B1714427 : Blo 1713057 1714427 := bstep (se 1 (by rfl) ⟨1285820, by rfl⟩ : syracuseStep 1714427 = 2571641) B2571641
theorem B16927289 : Blo 1713057 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B21123017 : Blo 1713057 21123017 := bstep (se 2 (by rfl) ⟨7921131, by rfl⟩ : syracuseStep 21123017 = 15842263) B15842263
theorem B13021883 : Blo 1713057 13021883 := bstep (se 1 (by rfl) ⟨9766412, by rfl⟩ : syracuseStep 13021883 = 19532825) B19532825
theorem B8680607 : Blo 1713057 8680607 := bstep (se 1 (by rfl) ⟨6510455, by rfl⟩ : syracuseStep 8680607 = 13020911) B13020911
theorem B19526993 : Blo 1713057 19526993 := bstep (se 2 (by rfl) ⟨7322622, by rfl⟩ : syracuseStep 19526993 = 14645245) B14645245
theorem B5568041 : Blo 1713057 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B9763679 : Blo 1713057 9763679 := bstep (se 1 (by rfl) ⟨7322759, by rfl⟩ : syracuseStep 9763679 = 14645519) B14645519
theorem B15629395 : Blo 1713057 15629395 := bstep (se 1 (by rfl) ⟨11722046, by rfl⟩ : syracuseStep 15629395 = 23444093) B23444093
theorem B4341215 : Blo 1713057 4341215 := bstep (se 1 (by rfl) ⟨3255911, by rfl⟩ : syracuseStep 4341215 = 6511823) B6511823
theorem B50773799 : Blo 1713057 50773799 := bstep (se 1 (by rfl) ⟨38080349, by rfl⟩ : syracuseStep 50773799 = 76160699) B76160699
theorem B2572379 : Blo 1713057 2572379 := bstep (se 1 (by rfl) ⟨1929284, by rfl⟩ : syracuseStep 2572379 = 3858569) B3858569
theorem B2572511 : Blo 1713057 2572511 := bstep (se 1 (by rfl) ⟨1929383, by rfl⟩ : syracuseStep 2572511 = 3858767) B3858767
theorem B13017995 : Blo 1713057 13017995 := bstep (se 1 (by rfl) ⟨9763496, by rfl⟩ : syracuseStep 13017995 = 19526993) B19526993
theorem B2894143 : Blo 1713057 2894143 := bstep (se 1 (by rfl) ⟨2170607, by rfl⟩ : syracuseStep 2894143 = 4341215) B4341215
theorem B121997801 : Blo 1713057 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B5787071 : Blo 1713057 5787071 := bstep (se 1 (by rfl) ⟨4340303, by rfl⟩ : syracuseStep 5787071 = 8680607) B8680607
theorem B14848109 : Blo 1713057 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B11284859 : Blo 1713057 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B6509119 : Blo 1713057 6509119 := bstep (se 1 (by rfl) ⟨4881839, by rfl⟩ : syracuseStep 6509119 = 9763679) B9763679
theorem B8681255 : Blo 1713057 8681255 := bstep (se 1 (by rfl) ⟨6510941, by rfl⟩ : syracuseStep 8681255 = 13021883) B13021883
theorem B20839193 : Blo 1713057 20839193 := bstep (se 2 (by rfl) ⟨7814697, by rfl⟩ : syracuseStep 20839193 = 15629395) B15629395
theorem B33849199 : Blo 1713057 33849199 := bstep (se 1 (by rfl) ⟨25386899, by rfl⟩ : syracuseStep 33849199 = 50773799) B50773799
theorem B14082011 : Blo 1713057 14082011 := bstep (se 1 (by rfl) ⟨10561508, by rfl⟩ : syracuseStep 14082011 = 21123017) B21123017
theorem B3858857 : Blo 1713057 3858857 := bstep (se 2 (by rfl) ⟨1447071, by rfl⟩ : syracuseStep 3858857 = 2894143) B2894143
theorem B81331867 : Blo 1713057 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B45132265 : Blo 1713057 45132265 := bstep (se 2 (by rfl) ⟨16924599, by rfl⟩ : syracuseStep 45132265 = 33849199) B33849199
theorem B1714919 : Blo 1713057 1714919 := bstep (se 1 (by rfl) ⟨1286189, by rfl⟩ : syracuseStep 1714919 = 2572379) B2572379
theorem B9898739 : Blo 1713057 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B1715007 : Blo 1713057 1715007 := bstep (se 1 (by rfl) ⟨1286255, by rfl⟩ : syracuseStep 1715007 = 2572511) B2572511
theorem B7523239 : Blo 1713057 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B8678663 : Blo 1713057 8678663 := bstep (se 1 (by rfl) ⟨6508997, by rfl⟩ : syracuseStep 8678663 = 13017995) B13017995
theorem B8678825 : Blo 1713057 8678825 := bstep (se 2 (by rfl) ⟨3254559, by rfl⟩ : syracuseStep 8678825 = 6509119) B6509119
theorem B5787503 : Blo 1713057 5787503 := bstep (se 1 (by rfl) ⟨4340627, by rfl⟩ : syracuseStep 5787503 = 8681255) B8681255
theorem B13892795 : Blo 1713057 13892795 := bstep (se 1 (by rfl) ⟨10419596, by rfl⟩ : syracuseStep 13892795 = 20839193) B20839193
theorem B3858047 : Blo 1713057 3858047 := bstep (se 1 (by rfl) ⟨2893535, by rfl⟩ : syracuseStep 3858047 = 5787071) B5787071
theorem B9388007 : Blo 1713057 9388007 := bstep (se 1 (by rfl) ⟨7041005, by rfl⟩ : syracuseStep 9388007 = 14082011) B14082011
theorem B2572571 : Blo 1713057 2572571 := bstep (se 1 (by rfl) ⟨1929428, by rfl⟩ : syracuseStep 2572571 = 3858857) B3858857
theorem B5785775 : Blo 1713057 5785775 := bstep (se 1 (by rfl) ⟨4339331, by rfl⟩ : syracuseStep 5785775 = 8678663) B8678663
theorem B5785883 : Blo 1713057 5785883 := bstep (se 1 (by rfl) ⟨4339412, by rfl⟩ : syracuseStep 5785883 = 8678825) B8678825
theorem B10030985 : Blo 1713057 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B6599159 : Blo 1713057 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B9261863 : Blo 1713057 9261863 := bstep (se 1 (by rfl) ⟨6946397, by rfl⟩ : syracuseStep 9261863 = 13892795) B13892795
theorem B108442489 : Blo 1713057 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B60176353 : Blo 1713057 60176353 := bstep (se 2 (by rfl) ⟨22566132, by rfl⟩ : syracuseStep 60176353 = 45132265) B45132265
theorem B2572031 : Blo 1713057 2572031 := bstep (se 1 (by rfl) ⟨1929023, by rfl⟩ : syracuseStep 2572031 = 3858047) B3858047
theorem B3858335 : Blo 1713057 3858335 := bstep (se 1 (by rfl) ⟨2893751, by rfl⟩ : syracuseStep 3858335 = 5787503) B5787503
theorem B6258671 : Blo 1713057 6258671 := bstep (se 1 (by rfl) ⟨4694003, by rfl⟩ : syracuseStep 6258671 = 9388007) B9388007
theorem B4399439 : Blo 1713057 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B144589985 : Blo 1713057 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B1714687 : Blo 1713057 1714687 := bstep (se 1 (by rfl) ⟨1286015, by rfl⟩ : syracuseStep 1714687 = 2572031) B2572031
theorem B6687323 : Blo 1713057 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B80235137 : Blo 1713057 80235137 := bstep (se 2 (by rfl) ⟨30088176, by rfl⟩ : syracuseStep 80235137 = 60176353) B60176353
theorem B4172447 : Blo 1713057 4172447 := bstep (se 1 (by rfl) ⟨3129335, by rfl⟩ : syracuseStep 4172447 = 6258671) B6258671
theorem B1715047 : Blo 1713057 1715047 := bstep (se 1 (by rfl) ⟨1286285, by rfl⟩ : syracuseStep 1715047 = 2572571) B2572571
theorem B6174575 : Blo 1713057 6174575 := bstep (se 1 (by rfl) ⟨4630931, by rfl⟩ : syracuseStep 6174575 = 9261863) B9261863
theorem B3857183 : Blo 1713057 3857183 := bstep (se 1 (by rfl) ⟨2892887, by rfl⟩ : syracuseStep 3857183 = 5785775) B5785775
theorem B3857255 : Blo 1713057 3857255 := bstep (se 1 (by rfl) ⟨2892941, by rfl⟩ : syracuseStep 3857255 = 5785883) B5785883
theorem B2572223 : Blo 1713057 2572223 := bstep (se 1 (by rfl) ⟨1929167, by rfl⟩ : syracuseStep 2572223 = 3858335) B3858335
theorem B4458215 : Blo 1713057 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B1714815 : Blo 1713057 1714815 := bstep (se 1 (by rfl) ⟨1286111, by rfl⟩ : syracuseStep 1714815 = 2572223) B2572223
theorem B46927349 : Blo 1713057 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B4116383 : Blo 1713057 4116383 := bstep (se 1 (by rfl) ⟨3087287, by rfl⟩ : syracuseStep 4116383 = 6174575) B6174575
theorem B53490091 : Blo 1713057 53490091 := bstep (se 1 (by rfl) ⟨40117568, by rfl⟩ : syracuseStep 53490091 = 80235137) B80235137
theorem B2781631 : Blo 1713057 2781631 := bstep (se 1 (by rfl) ⟨2086223, by rfl⟩ : syracuseStep 2781631 = 4172447) B4172447
theorem B96393323 : Blo 1713057 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B2571455 : Blo 1713057 2571455 := bstep (se 1 (by rfl) ⟨1928591, by rfl⟩ : syracuseStep 2571455 = 3857183) B3857183
theorem B2571503 : Blo 1713057 2571503 := bstep (se 1 (by rfl) ⟨1928627, by rfl⟩ : syracuseStep 2571503 = 3857255) B3857255
theorem B71320121 : Blo 1713057 71320121 := bstep (se 2 (by rfl) ⟨26745045, by rfl⟩ : syracuseStep 71320121 = 53490091) B53490091
theorem B1714303 : Blo 1713057 1714303 := bstep (se 1 (by rfl) ⟨1285727, by rfl⟩ : syracuseStep 1714303 = 2571455) B2571455
theorem B1714335 : Blo 1713057 1714335 := bstep (se 1 (by rfl) ⟨1285751, by rfl⟩ : syracuseStep 1714335 = 2571503) B2571503
theorem B64262215 : Blo 1713057 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B3708841 : Blo 1713057 3708841 := bstep (se 2 (by rfl) ⟨1390815, by rfl⟩ : syracuseStep 3708841 = 2781631) B2781631
theorem B2972143 : Blo 1713057 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B31284899 : Blo 1713057 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B2744255 : Blo 1713057 2744255 := bstep (se 1 (by rfl) ⟨2058191, by rfl⟩ : syracuseStep 2744255 = 4116383) B4116383
theorem B47546747 : Blo 1713057 47546747 := bstep (se 1 (by rfl) ⟨35660060, by rfl⟩ : syracuseStep 47546747 = 71320121) B71320121
theorem B1829503 : Blo 1713057 1829503 := bstep (se 1 (by rfl) ⟨1372127, by rfl⟩ : syracuseStep 1829503 = 2744255) B2744255
theorem B85682953 : Blo 1713057 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B4945121 : Blo 1713057 4945121 := bstep (se 2 (by rfl) ⟨1854420, by rfl⟩ : syracuseStep 4945121 = 3708841) B3708841
theorem B3962857 : Blo 1713057 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B20856599 : Blo 1713057 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B456975749 : Blo 1713057 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B13904399 : Blo 1713057 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B31697831 : Blo 1713057 31697831 := bstep (se 1 (by rfl) ⟨23773373, by rfl⟩ : syracuseStep 31697831 = 47546747) B47546747
theorem B3296747 : Blo 1713057 3296747 := bstep (se 1 (by rfl) ⟨2472560, by rfl⟩ : syracuseStep 3296747 = 4945121) B4945121
theorem B2439337 : Blo 1713057 2439337 := bstep (se 2 (by rfl) ⟨914751, by rfl⟩ : syracuseStep 2439337 = 1829503) B1829503
theorem B5283809 : Blo 1713057 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B3252449 : Blo 1713057 3252449 := bstep (se 2 (by rfl) ⟨1219668, by rfl⟩ : syracuseStep 3252449 = 2439337) B2439337
theorem B8791325 : Blo 1713057 8791325 := bstep (se 3 (by rfl) ⟨1648373, by rfl⟩ : syracuseStep 8791325 = 3296747) B3296747
theorem B37078397 : Blo 1713057 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B84527549 : Blo 1713057 84527549 := bstep (se 3 (by rfl) ⟨15848915, by rfl⟩ : syracuseStep 84527549 = 31697831) B31697831
theorem B304650499 : Blo 1713057 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B3522539 : Blo 1713057 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B406200665 : Blo 1713057 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B5860883 : Blo 1713057 5860883 := bstep (se 1 (by rfl) ⟨4395662, by rfl⟩ : syracuseStep 5860883 = 8791325) B8791325
theorem B24718931 : Blo 1713057 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B2348359 : Blo 1713057 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B2168299 : Blo 1713057 2168299 := bstep (se 1 (by rfl) ⟨1626224, by rfl⟩ : syracuseStep 2168299 = 3252449) B3252449
theorem B56351699 : Blo 1713057 56351699 := bstep (se 1 (by rfl) ⟨42263774, by rfl⟩ : syracuseStep 56351699 = 84527549) B84527549
theorem B16479287 : Blo 1713057 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B270800443 : Blo 1713057 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B15629021 : Blo 1713057 15629021 := bstep (se 3 (by rfl) ⟨2930441, by rfl⟩ : syracuseStep 15629021 = 5860883) B5860883
theorem B12524581 : Blo 1713057 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B37567799 : Blo 1713057 37567799 := bstep (se 1 (by rfl) ⟨28175849, by rfl⟩ : syracuseStep 37567799 = 56351699) B56351699
theorem B2891065 : Blo 1713057 2891065 := bstep (se 2 (by rfl) ⟨1084149, by rfl⟩ : syracuseStep 2891065 = 2168299) B2168299
theorem B10986191 : Blo 1713057 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B25045199 : Blo 1713057 25045199 := bstep (se 1 (by rfl) ⟨18783899, by rfl⟩ : syracuseStep 25045199 = 37567799) B37567799
theorem B16699441 : Blo 1713057 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B3854753 : Blo 1713057 3854753 := bstep (se 2 (by rfl) ⟨1445532, by rfl⟩ : syracuseStep 3854753 = 2891065) B2891065
theorem B361067257 : Blo 1713057 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B10419347 : Blo 1713057 10419347 := bstep (se 1 (by rfl) ⟨7814510, by rfl⟩ : syracuseStep 10419347 = 15629021) B15629021
theorem B22265921 : Blo 1713057 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B7324127 : Blo 1713057 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B16696799 : Blo 1713057 16696799 := bstep (se 1 (by rfl) ⟨12522599, by rfl⟩ : syracuseStep 16696799 = 25045199) B25045199
theorem B481423009 : Blo 1713057 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B2569835 : Blo 1713057 2569835 := bstep (se 1 (by rfl) ⟨1927376, by rfl⟩ : syracuseStep 2569835 = 3854753) B3854753
theorem B6946231 : Blo 1713057 6946231 := bstep (se 1 (by rfl) ⟨5209673, by rfl⟩ : syracuseStep 6946231 = 10419347) B10419347
theorem B14843947 : Blo 1713057 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B4882751 : Blo 1713057 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B1713223 : Blo 1713057 1713223 := bstep (se 1 (by rfl) ⟨1284917, by rfl⟩ : syracuseStep 1713223 = 2569835) B2569835
theorem B9261641 : Blo 1713057 9261641 := bstep (se 2 (by rfl) ⟨3473115, by rfl⟩ : syracuseStep 9261641 = 6946231) B6946231
theorem B641897345 : Blo 1713057 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B11131199 : Blo 1713057 11131199 := bstep (se 1 (by rfl) ⟨8348399, by rfl⟩ : syracuseStep 11131199 = 16696799) B16696799
theorem B19791929 : Blo 1713057 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B3255167 : Blo 1713057 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B24697709 : Blo 1713057 24697709 := bstep (se 3 (by rfl) ⟨4630820, by rfl⟩ : syracuseStep 24697709 = 9261641) B9261641
theorem B7420799 : Blo 1713057 7420799 := bstep (se 1 (by rfl) ⟨5565599, by rfl⟩ : syracuseStep 7420799 = 11131199) B11131199
theorem B1711726253 : Blo 1713057 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B8680445 : Blo 1713057 8680445 := bstep (se 3 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 8680445 = 3255167) B3255167
theorem B1141150835 : Blo 1713057 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B13194619 : Blo 1713057 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B16465139 : Blo 1713057 16465139 := bstep (se 1 (by rfl) ⟨12348854, by rfl⟩ : syracuseStep 16465139 = 24697709) B24697709
theorem B4947199 : Blo 1713057 4947199 := bstep (se 1 (by rfl) ⟨3710399, by rfl⟩ : syracuseStep 4947199 = 7420799) B7420799
theorem B760767223 : Blo 1713057 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B70371301 : Blo 1713057 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B105540245 : Blo 1713057 105540245 := bstep (se 6 (by rfl) ⟨2473599, by rfl⟩ : syracuseStep 105540245 = 4947199) B4947199
theorem B5786963 : Blo 1713057 5786963 := bstep (se 1 (by rfl) ⟨4340222, by rfl⟩ : syracuseStep 5786963 = 8680445) B8680445
theorem B10976759 : Blo 1713057 10976759 := bstep (se 1 (by rfl) ⟨8232569, by rfl⟩ : syracuseStep 10976759 = 16465139) B16465139
theorem B7317839 : Blo 1713057 7317839 := bstep (se 1 (by rfl) ⟨5488379, by rfl⟩ : syracuseStep 7317839 = 10976759) B10976759
theorem B93828401 : Blo 1713057 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B1014356297 : Blo 1713057 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B70360163 : Blo 1713057 70360163 := bstep (se 1 (by rfl) ⟨52770122, by rfl⟩ : syracuseStep 70360163 = 105540245) B105540245
theorem B3857975 : Blo 1713057 3857975 := bstep (se 1 (by rfl) ⟨2893481, by rfl⟩ : syracuseStep 3857975 = 5786963) B5786963
theorem B676237531 : Blo 1713057 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B4878559 : Blo 1713057 4878559 := bstep (se 1 (by rfl) ⟨3658919, by rfl⟩ : syracuseStep 4878559 = 7317839) B7317839
theorem B62552267 : Blo 1713057 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B46906775 : Blo 1713057 46906775 := bstep (se 1 (by rfl) ⟨35180081, by rfl⟩ : syracuseStep 46906775 = 70360163) B70360163
theorem B2571983 : Blo 1713057 2571983 := bstep (se 1 (by rfl) ⟨1928987, by rfl⟩ : syracuseStep 2571983 = 3857975) B3857975
theorem B6504745 : Blo 1713057 6504745 := bstep (se 2 (by rfl) ⟨2439279, by rfl⟩ : syracuseStep 6504745 = 4878559) B4878559
theorem B31271183 : Blo 1713057 31271183 := bstep (se 1 (by rfl) ⟨23453387, by rfl⟩ : syracuseStep 31271183 = 46906775) B46906775
theorem B1714655 : Blo 1713057 1714655 := bstep (se 1 (by rfl) ⟨1285991, by rfl⟩ : syracuseStep 1714655 = 2571983) B2571983
theorem B41701511 : Blo 1713057 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B901650041 : Blo 1713057 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B601100027 : Blo 1713057 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B111204029 : Blo 1713057 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B8672993 : Blo 1713057 8672993 := bstep (se 2 (by rfl) ⟨3252372, by rfl⟩ : syracuseStep 8672993 = 6504745) B6504745
theorem B20847455 : Blo 1713057 20847455 := bstep (se 1 (by rfl) ⟨15635591, by rfl⟩ : syracuseStep 20847455 = 31271183) B31271183
theorem B13898303 : Blo 1713057 13898303 := bstep (se 1 (by rfl) ⟨10423727, by rfl⟩ : syracuseStep 13898303 = 20847455) B20847455
theorem B400733351 : Blo 1713057 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B74136019 : Blo 1713057 74136019 := bstep (se 1 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 74136019 = 111204029) B111204029
theorem B5781995 : Blo 1713057 5781995 := bstep (se 1 (by rfl) ⟨4336496, by rfl⟩ : syracuseStep 5781995 = 8672993) B8672993
theorem B9265535 : Blo 1713057 9265535 := bstep (se 1 (by rfl) ⟨6949151, by rfl⟩ : syracuseStep 9265535 = 13898303) B13898303
theorem B98848025 : Blo 1713057 98848025 := bstep (se 2 (by rfl) ⟨37068009, by rfl⟩ : syracuseStep 98848025 = 74136019) B74136019
theorem B3854663 : Blo 1713057 3854663 := bstep (se 1 (by rfl) ⟨2890997, by rfl⟩ : syracuseStep 3854663 = 5781995) B5781995
theorem B267155567 : Blo 1713057 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B6177023 : Blo 1713057 6177023 := bstep (se 1 (by rfl) ⟨4632767, by rfl⟩ : syracuseStep 6177023 = 9265535) B9265535
theorem B178103711 : Blo 1713057 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B65898683 : Blo 1713057 65898683 := bstep (se 1 (by rfl) ⟨49424012, by rfl⟩ : syracuseStep 65898683 = 98848025) B98848025
theorem B2569775 : Blo 1713057 2569775 := bstep (se 1 (by rfl) ⟨1927331, by rfl⟩ : syracuseStep 2569775 = 3854663) B3854663
theorem B118735807 : Blo 1713057 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B1713183 : Blo 1713057 1713183 := bstep (se 1 (by rfl) ⟨1284887, by rfl⟩ : syracuseStep 1713183 = 2569775) B2569775
theorem B4118015 : Blo 1713057 4118015 := bstep (se 1 (by rfl) ⟨3088511, by rfl⟩ : syracuseStep 4118015 = 6177023) B6177023
theorem B43932455 : Blo 1713057 43932455 := bstep (se 1 (by rfl) ⟨32949341, by rfl⟩ : syracuseStep 43932455 = 65898683) B65898683
theorem B2745343 : Blo 1713057 2745343 := bstep (se 1 (by rfl) ⟨2059007, by rfl⟩ : syracuseStep 2745343 = 4118015) B4118015
theorem B29288303 : Blo 1713057 29288303 := bstep (se 1 (by rfl) ⟨21966227, by rfl⟩ : syracuseStep 29288303 = 43932455) B43932455
theorem B158314409 : Blo 1713057 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B14641829 : Blo 1713057 14641829 := bstep (se 4 (by rfl) ⟨1372671, by rfl⟩ : syracuseStep 14641829 = 2745343) B2745343
theorem B19525535 : Blo 1713057 19525535 := bstep (se 1 (by rfl) ⟨14644151, by rfl⟩ : syracuseStep 19525535 = 29288303) B29288303
theorem B105542939 : Blo 1713057 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B70361959 : Blo 1713057 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B9761219 : Blo 1713057 9761219 := bstep (se 1 (by rfl) ⟨7320914, by rfl⟩ : syracuseStep 9761219 = 14641829) B14641829
theorem B13017023 : Blo 1713057 13017023 := bstep (se 1 (by rfl) ⟨9762767, by rfl⟩ : syracuseStep 13017023 = 19525535) B19525535
theorem B93815945 : Blo 1713057 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B8678015 : Blo 1713057 8678015 := bstep (se 1 (by rfl) ⟨6508511, by rfl⟩ : syracuseStep 8678015 = 13017023) B13017023
theorem B6507479 : Blo 1713057 6507479 := bstep (se 1 (by rfl) ⟨4880609, by rfl⟩ : syracuseStep 6507479 = 9761219) B9761219
theorem B5785343 : Blo 1713057 5785343 := bstep (se 1 (by rfl) ⟨4339007, by rfl⟩ : syracuseStep 5785343 = 8678015) B8678015
theorem B4338319 : Blo 1713057 4338319 := bstep (se 1 (by rfl) ⟨3253739, by rfl⟩ : syracuseStep 4338319 = 6507479) B6507479
theorem B62543963 : Blo 1713057 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B5784425 : Blo 1713057 5784425 := bstep (se 2 (by rfl) ⟨2169159, by rfl⟩ : syracuseStep 5784425 = 4338319) B4338319
theorem B3856895 : Blo 1713057 3856895 := bstep (se 1 (by rfl) ⟨2892671, by rfl⟩ : syracuseStep 3856895 = 5785343) B5785343
theorem B41695975 : Blo 1713057 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B55594633 : Blo 1713057 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B3856283 : Blo 1713057 3856283 := bstep (se 1 (by rfl) ⟨2892212, by rfl⟩ : syracuseStep 3856283 = 5784425) B5784425
theorem B2571263 : Blo 1713057 2571263 := bstep (se 1 (by rfl) ⟨1928447, by rfl⟩ : syracuseStep 2571263 = 3856895) B3856895
theorem B1714175 : Blo 1713057 1714175 := bstep (se 1 (by rfl) ⟨1285631, by rfl⟩ : syracuseStep 1714175 = 2571263) B2571263
theorem B74126177 : Blo 1713057 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B2570855 : Blo 1713057 2570855 := bstep (se 1 (by rfl) ⟨1928141, by rfl⟩ : syracuseStep 2570855 = 3856283) B3856283
theorem B1713903 : Blo 1713057 1713903 := bstep (se 1 (by rfl) ⟨1285427, by rfl⟩ : syracuseStep 1713903 = 2570855) B2570855
theorem B49417451 : Blo 1713057 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B32944967 : Blo 1713057 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B21963311 : Blo 1713057 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B14642207 : Blo 1713057 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B9761471 : Blo 1713057 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B6507647 : Blo 1713057 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B4338431 : Blo 1713057 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B2892287 : Blo 1713057 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B1928191 : Blo 1713057 1928191 := bstep (se 1 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 1928191 = 2892287) B2892287
theorem B2570921 : Blo 1713057 2570921 := bstep (se 2 (by rfl) ⟨964095, by rfl⟩ : syracuseStep 2570921 = 1928191) B1928191
theorem B1713947 : Blo 1713057 1713947 := bstep (se 1 (by rfl) ⟨1285460, by rfl⟩ : syracuseStep 1713947 = 2570921) B2570921

theorem C0 (j : ℕ) (h1 : 428264 ≤ j) (h2 : j ≤ 428763) : Blo 1713057 (4 * j + 3) := by
  interval_cases j
  · exact B1713059
  · exact B1713063
  · exact B1713067
  · exact B1713071
  · exact B1713075
  · exact B1713079
  · exact B1713083
  · exact B1713087
  · exact B1713091
  · exact B1713095
  · exact B1713099
  · exact B1713103
  · exact B1713107
  · exact B1713111
  · exact B1713115
  · exact B1713119
  · exact B1713123
  · exact B1713127
  · exact B1713131
  · exact B1713135
  · exact B1713139
  · exact B1713143
  · exact B1713147
  · exact B1713151
  · exact B1713155
  · exact B1713159
  · exact B1713163
  · exact B1713167
  · exact B1713171
  · exact B1713175
  · exact B1713179
  · exact B1713183
  · exact B1713187
  · exact B1713191
  · exact B1713195
  · exact B1713199
  · exact B1713203
  · exact B1713207
  · exact B1713211
  · exact B1713215
  · exact B1713219
  · exact B1713223
  · exact B1713227
  · exact B1713231
  · exact B1713235
  · exact B1713239
  · exact B1713243
  · exact B1713247
  · exact B1713251
  · exact B1713255
  · exact B1713259
  · exact B1713263
  · exact B1713267
  · exact B1713271
  · exact B1713275
  · exact B1713279
  · exact B1713283
  · exact B1713287
  · exact B1713291
  · exact B1713295
  · exact B1713299
  · exact B1713303
  · exact B1713307
  · exact B1713311
  · exact B1713315
  · exact B1713319
  · exact B1713323
  · exact B1713327
  · exact B1713331
  · exact B1713335
  · exact B1713339
  · exact B1713343
  · exact B1713347
  · exact B1713351
  · exact B1713355
  · exact B1713359
  · exact B1713363
  · exact B1713367
  · exact B1713371
  · exact B1713375
  · exact B1713379
  · exact B1713383
  · exact B1713387
  · exact B1713391
  · exact B1713395
  · exact B1713399
  · exact B1713403
  · exact B1713407
  · exact B1713411
  · exact B1713415
  · exact B1713419
  · exact B1713423
  · exact B1713427
  · exact B1713431
  · exact B1713435
  · exact B1713439
  · exact B1713443
  · exact B1713447
  · exact B1713451
  · exact B1713455
  · exact B1713459
  · exact B1713463
  · exact B1713467
  · exact B1713471
  · exact B1713475
  · exact B1713479
  · exact B1713483
  · exact B1713487
  · exact B1713491
  · exact B1713495
  · exact B1713499
  · exact B1713503
  · exact B1713507
  · exact B1713511
  · exact B1713515
  · exact B1713519
  · exact B1713523
  · exact B1713527
  · exact B1713531
  · exact B1713535
  · exact B1713539
  · exact B1713543
  · exact B1713547
  · exact B1713551
  · exact B1713555
  · exact B1713559
  · exact B1713563
  · exact B1713567
  · exact B1713571
  · exact B1713575
  · exact B1713579
  · exact B1713583
  · exact B1713587
  · exact B1713591
  · exact B1713595
  · exact B1713599
  · exact B1713603
  · exact B1713607
  · exact B1713611
  · exact B1713615
  · exact B1713619
  · exact B1713623
  · exact B1713627
  · exact B1713631
  · exact B1713635
  · exact B1713639
  · exact B1713643
  · exact B1713647
  · exact B1713651
  · exact B1713655
  · exact B1713659
  · exact B1713663
  · exact B1713667
  · exact B1713671
  · exact B1713675
  · exact B1713679
  · exact B1713683
  · exact B1713687
  · exact B1713691
  · exact B1713695
  · exact B1713699
  · exact B1713703
  · exact B1713707
  · exact B1713711
  · exact B1713715
  · exact B1713719
  · exact B1713723
  · exact B1713727
  · exact B1713731
  · exact B1713735
  · exact B1713739
  · exact B1713743
  · exact B1713747
  · exact B1713751
  · exact B1713755
  · exact B1713759
  · exact B1713763
  · exact B1713767
  · exact B1713771
  · exact B1713775
  · exact B1713779
  · exact B1713783
  · exact B1713787
  · exact B1713791
  · exact B1713795
  · exact B1713799
  · exact B1713803
  · exact B1713807
  · exact B1713811
  · exact B1713815
  · exact B1713819
  · exact B1713823
  · exact B1713827
  · exact B1713831
  · exact B1713835
  · exact B1713839
  · exact B1713843
  · exact B1713847
  · exact B1713851
  · exact B1713855
  · exact B1713859
  · exact B1713863
  · exact B1713867
  · exact B1713871
  · exact B1713875
  · exact B1713879
  · exact B1713883
  · exact B1713887
  · exact B1713891
  · exact B1713895
  · exact B1713899
  · exact B1713903
  · exact B1713907
  · exact B1713911
  · exact B1713915
  · exact B1713919
  · exact B1713923
  · exact B1713927
  · exact B1713931
  · exact B1713935
  · exact B1713939
  · exact B1713943
  · exact B1713947
  · exact B1713951
  · exact B1713955
  · exact B1713959
  · exact B1713963
  · exact B1713967
  · exact B1713971
  · exact B1713975
  · exact B1713979
  · exact B1713983
  · exact B1713987
  · exact B1713991
  · exact B1713995
  · exact B1713999
  · exact B1714003
  · exact B1714007
  · exact B1714011
  · exact B1714015
  · exact B1714019
  · exact B1714023
  · exact B1714027
  · exact B1714031
  · exact B1714035
  · exact B1714039
  · exact B1714043
  · exact B1714047
  · exact B1714051
  · exact B1714055
  · exact B1714059
  · exact B1714063
  · exact B1714067
  · exact B1714071
  · exact B1714075
  · exact B1714079
  · exact B1714083
  · exact B1714087
  · exact B1714091
  · exact B1714095
  · exact B1714099
  · exact B1714103
  · exact B1714107
  · exact B1714111
  · exact B1714115
  · exact B1714119
  · exact B1714123
  · exact B1714127
  · exact B1714131
  · exact B1714135
  · exact B1714139
  · exact B1714143
  · exact B1714147
  · exact B1714151
  · exact B1714155
  · exact B1714159
  · exact B1714163
  · exact B1714167
  · exact B1714171
  · exact B1714175
  · exact B1714179
  · exact B1714183
  · exact B1714187
  · exact B1714191
  · exact B1714195
  · exact B1714199
  · exact B1714203
  · exact B1714207
  · exact B1714211
  · exact B1714215
  · exact B1714219
  · exact B1714223
  · exact B1714227
  · exact B1714231
  · exact B1714235
  · exact B1714239
  · exact B1714243
  · exact B1714247
  · exact B1714251
  · exact B1714255
  · exact B1714259
  · exact B1714263
  · exact B1714267
  · exact B1714271
  · exact B1714275
  · exact B1714279
  · exact B1714283
  · exact B1714287
  · exact B1714291
  · exact B1714295
  · exact B1714299
  · exact B1714303
  · exact B1714307
  · exact B1714311
  · exact B1714315
  · exact B1714319
  · exact B1714323
  · exact B1714327
  · exact B1714331
  · exact B1714335
  · exact B1714339
  · exact B1714343
  · exact B1714347
  · exact B1714351
  · exact B1714355
  · exact B1714359
  · exact B1714363
  · exact B1714367
  · exact B1714371
  · exact B1714375
  · exact B1714379
  · exact B1714383
  · exact B1714387
  · exact B1714391
  · exact B1714395
  · exact B1714399
  · exact B1714403
  · exact B1714407
  · exact B1714411
  · exact B1714415
  · exact B1714419
  · exact B1714423
  · exact B1714427
  · exact B1714431
  · exact B1714435
  · exact B1714439
  · exact B1714443
  · exact B1714447
  · exact B1714451
  · exact B1714455
  · exact B1714459
  · exact B1714463
  · exact B1714467
  · exact B1714471
  · exact B1714475
  · exact B1714479
  · exact B1714483
  · exact B1714487
  · exact B1714491
  · exact B1714495
  · exact B1714499
  · exact B1714503
  · exact B1714507
  · exact B1714511
  · exact B1714515
  · exact B1714519
  · exact B1714523
  · exact B1714527
  · exact B1714531
  · exact B1714535
  · exact B1714539
  · exact B1714543
  · exact B1714547
  · exact B1714551
  · exact B1714555
  · exact B1714559
  · exact B1714563
  · exact B1714567
  · exact B1714571
  · exact B1714575
  · exact B1714579
  · exact B1714583
  · exact B1714587
  · exact B1714591
  · exact B1714595
  · exact B1714599
  · exact B1714603
  · exact B1714607
  · exact B1714611
  · exact B1714615
  · exact B1714619
  · exact B1714623
  · exact B1714627
  · exact B1714631
  · exact B1714635
  · exact B1714639
  · exact B1714643
  · exact B1714647
  · exact B1714651
  · exact B1714655
  · exact B1714659
  · exact B1714663
  · exact B1714667
  · exact B1714671
  · exact B1714675
  · exact B1714679
  · exact B1714683
  · exact B1714687
  · exact B1714691
  · exact B1714695
  · exact B1714699
  · exact B1714703
  · exact B1714707
  · exact B1714711
  · exact B1714715
  · exact B1714719
  · exact B1714723
  · exact B1714727
  · exact B1714731
  · exact B1714735
  · exact B1714739
  · exact B1714743
  · exact B1714747
  · exact B1714751
  · exact B1714755
  · exact B1714759
  · exact B1714763
  · exact B1714767
  · exact B1714771
  · exact B1714775
  · exact B1714779
  · exact B1714783
  · exact B1714787
  · exact B1714791
  · exact B1714795
  · exact B1714799
  · exact B1714803
  · exact B1714807
  · exact B1714811
  · exact B1714815
  · exact B1714819
  · exact B1714823
  · exact B1714827
  · exact B1714831
  · exact B1714835
  · exact B1714839
  · exact B1714843
  · exact B1714847
  · exact B1714851
  · exact B1714855
  · exact B1714859
  · exact B1714863
  · exact B1714867
  · exact B1714871
  · exact B1714875
  · exact B1714879
  · exact B1714883
  · exact B1714887
  · exact B1714891
  · exact B1714895
  · exact B1714899
  · exact B1714903
  · exact B1714907
  · exact B1714911
  · exact B1714915
  · exact B1714919
  · exact B1714923
  · exact B1714927
  · exact B1714931
  · exact B1714935
  · exact B1714939
  · exact B1714943
  · exact B1714947
  · exact B1714951
  · exact B1714955
  · exact B1714959
  · exact B1714963
  · exact B1714967
  · exact B1714971
  · exact B1714975
  · exact B1714979
  · exact B1714983
  · exact B1714987
  · exact B1714991
  · exact B1714995
  · exact B1714999
  · exact B1715003
  · exact B1715007
  · exact B1715011
  · exact B1715015
  · exact B1715019
  · exact B1715023
  · exact B1715027
  · exact B1715031
  · exact B1715035
  · exact B1715039
  · exact B1715043
  · exact B1715047
  · exact B1715051
  · exact B1715055

theorem solution (m : ℕ) (hlo : 1713057 ≤ m) (hhi : m ≤ 1715057) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 428264 ≤ j := by omega
    have hj2 : j ≤ 428763 := by omega
    have hb : Blo 1713057 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
