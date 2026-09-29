-- Prove2me | solution 1 for syracuse_descends_range_1140634_1144634
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:45.887771+00:00
-- url     : https://prove2.me/submissions/bbf63df0-12a9-4831-ae1f-81268c239371

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


theorem B5865509 : Blo 1140634 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B1736957 : Blo 1140634 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B35225941 : Blo 1140634 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B21955157 : Blo 1140634 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B1409857 : Blo 1140634 1409857 := bbase (se 2 (by rfl) ⟨528696, by rfl⟩ : syracuseStep 1409857 = 1057393) (by norm_num)
theorem B2786125 : Blo 1140634 2786125 := bbase (se 3 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 2786125 = 1044797) (by norm_num)
theorem B9765845 : Blo 1140634 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B1443673 : Blo 1140634 1443673 := bbase (se 2 (by rfl) ⟨541377, by rfl⟩ : syracuseStep 1443673 = 1082755) (by norm_num)
theorem B3475349 : Blo 1140634 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B16484309 : Blo 1140634 16484309 := bbase (se 7 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 16484309 = 386351) (by norm_num)
theorem B1443845 : Blo 1140634 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B1443901 : Blo 1140634 1443901 := bbase (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) (by norm_num)
theorem B1443997 : Blo 1140634 1443997 := bbase (se 3 (by rfl) ⟨270749, by rfl⟩ : syracuseStep 1443997 = 541499) (by norm_num)
theorem B1444169 : Blo 1140634 1444169 := bbase (se 2 (by rfl) ⟨541563, by rfl⟩ : syracuseStep 1444169 = 1083127) (by norm_num)
theorem B1444225 : Blo 1140634 1444225 := bbase (se 2 (by rfl) ⟨541584, by rfl⟩ : syracuseStep 1444225 = 1083169) (by norm_num)
theorem B1444321 : Blo 1140634 1444321 := bbase (se 2 (by rfl) ⟨541620, by rfl⟩ : syracuseStep 1444321 = 1083241) (by norm_num)
theorem B1444493 : Blo 1140634 1444493 := bbase (se 3 (by rfl) ⟨270842, by rfl⟩ : syracuseStep 1444493 = 541685) (by norm_num)
theorem B1444549 : Blo 1140634 1444549 := bbase (se 4 (by rfl) ⟨135426, by rfl⟩ : syracuseStep 1444549 = 270853) (by norm_num)
theorem B2165525 : Blo 1140634 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B1444645 : Blo 1140634 1444645 := bbase (se 4 (by rfl) ⟨135435, by rfl⟩ : syracuseStep 1444645 = 270871) (by norm_num)
theorem B5868389 : Blo 1140634 5868389 := bbase (se 4 (by rfl) ⟨550161, by rfl⟩ : syracuseStep 5868389 = 1100323) (by norm_num)
theorem B1444817 : Blo 1140634 1444817 := bbase (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) (by norm_num)
theorem B1444873 : Blo 1140634 1444873 := bbase (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) (by norm_num)
theorem B1444969 : Blo 1140634 1444969 := bbase (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) (by norm_num)
theorem B1445141 : Blo 1140634 1445141 := bbase (se 6 (by rfl) ⟨33870, by rfl⟩ : syracuseStep 1445141 = 67741) (by norm_num)
theorem B1445197 : Blo 1140634 1445197 := bbase (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) (by norm_num)
theorem B1543501 : Blo 1140634 1543501 := bbase (se 3 (by rfl) ⟨289406, by rfl⟩ : syracuseStep 1543501 = 578813) (by norm_num)
theorem B1445293 : Blo 1140634 1445293 := bbase (se 3 (by rfl) ⟨270992, by rfl⟩ : syracuseStep 1445293 = 541985) (by norm_num)
theorem B2166277 : Blo 1140634 2166277 := bbase (se 4 (by rfl) ⟨203088, by rfl⟩ : syracuseStep 2166277 = 406177) (by norm_num)
theorem B5213717 : Blo 1140634 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1445465 : Blo 1140634 1445465 := bbase (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) (by norm_num)
theorem B2887285 : Blo 1140634 2887285 := bbase (se 5 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 2887285 = 270683) (by norm_num)
theorem B1445521 : Blo 1140634 1445521 := bbase (se 2 (by rfl) ⟨542070, by rfl⟩ : syracuseStep 1445521 = 1084141) (by norm_num)
theorem B2166421 : Blo 1140634 2166421 := bbase (se 6 (by rfl) ⟨50775, by rfl⟩ : syracuseStep 2166421 = 101551) (by norm_num)
theorem B6950549 : Blo 1140634 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B2887397 : Blo 1140634 2887397 := bbase (se 4 (by rfl) ⟨270693, by rfl⟩ : syracuseStep 2887397 = 541387) (by norm_num)
theorem B1445617 : Blo 1140634 1445617 := bbase (se 2 (by rfl) ⟨542106, by rfl⟩ : syracuseStep 1445617 = 1084213) (by norm_num)
theorem B2166581 : Blo 1140634 2166581 := bbase (se 5 (by rfl) ⟨101558, by rfl⟩ : syracuseStep 2166581 = 203117) (by norm_num)
theorem B35163989 : Blo 1140634 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B18550613 : Blo 1140634 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B3084149 : Blo 1140634 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B2199413 : Blo 1140634 2199413 := bbase (se 5 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 2199413 = 206195) (by norm_num)
theorem B1445789 : Blo 1140634 1445789 := bbase (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) (by norm_num)
theorem B2887589 : Blo 1140634 2887589 := bbase (se 4 (by rfl) ⟨270711, by rfl⟩ : syracuseStep 2887589 = 541423) (by norm_num)
theorem B2166725 : Blo 1140634 2166725 := bbase (se 4 (by rfl) ⟨203130, by rfl⟩ : syracuseStep 2166725 = 406261) (by norm_num)
theorem B1445845 : Blo 1140634 1445845 := bbase (se 7 (by rfl) ⟨16943, by rfl⟩ : syracuseStep 1445845 = 33887) (by norm_num)
theorem B11145205 : Blo 1140634 11145205 := bbase (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) (by norm_num)
theorem B1445941 : Blo 1140634 1445941 := bbase (se 5 (by rfl) ⟨67778, by rfl⟩ : syracuseStep 1445941 = 135557) (by norm_num)
theorem B2199653 : Blo 1140634 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B1446113 : Blo 1140634 1446113 := bbase (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) (by norm_num)
theorem B2167013 : Blo 1140634 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B2887933 : Blo 1140634 2887933 := bbase (se 3 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 2887933 = 1082975) (by norm_num)
theorem B1446169 : Blo 1140634 1446169 := bbase (se 2 (by rfl) ⟨542313, by rfl⟩ : syracuseStep 1446169 = 1084627) (by norm_num)
theorem B3084581 : Blo 1140634 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B4886837 : Blo 1140634 4886837 := bbase (se 5 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 4886837 = 458141) (by norm_num)
theorem B19796309 : Blo 1140634 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B2888045 : Blo 1140634 2888045 := bbase (se 3 (by rfl) ⟨541508, by rfl⟩ : syracuseStep 2888045 = 1083017) (by norm_num)
theorem B1446265 : Blo 1140634 1446265 := bbase (se 2 (by rfl) ⟨542349, by rfl⟩ : syracuseStep 1446265 = 1084699) (by norm_num)
theorem B2167165 : Blo 1140634 2167165 := bbase (se 3 (by rfl) ⟨406343, by rfl⟩ : syracuseStep 2167165 = 812687) (by norm_num)
theorem B5870069 : Blo 1140634 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B9277973 : Blo 1140634 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B1446437 : Blo 1140634 1446437 := bbase (se 4 (by rfl) ⟨135603, by rfl⟩ : syracuseStep 1446437 = 271207) (by norm_num)
theorem B2888237 : Blo 1140634 2888237 := bbase (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) (by norm_num)
theorem B4887125 : Blo 1140634 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B1446493 : Blo 1140634 1446493 := bbase (se 3 (by rfl) ⟨271217, by rfl⟩ : syracuseStep 1446493 = 542435) (by norm_num)
theorem B2167469 : Blo 1140634 2167469 := bbase (se 3 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 2167469 = 812801) (by norm_num)
theorem B1446589 : Blo 1140634 1446589 := bbase (se 3 (by rfl) ⟨271235, by rfl⟩ : syracuseStep 1446589 = 542471) (by norm_num)
theorem B3248869 : Blo 1140634 3248869 := bbase (se 4 (by rfl) ⟨304581, by rfl⟩ : syracuseStep 3248869 = 609163) (by norm_num)
theorem B1446761 : Blo 1140634 1446761 := bbase (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) (by norm_num)
theorem B2888581 : Blo 1140634 2888581 := bbase (se 4 (by rfl) ⟨270804, by rfl⟩ : syracuseStep 2888581 = 541609) (by norm_num)
theorem B1446817 : Blo 1140634 1446817 := bbase (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) (by norm_num)
theorem B2888693 : Blo 1140634 2888693 := bbase (se 5 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 2888693 = 270815) (by norm_num)
theorem B1446913 : Blo 1140634 1446913 := bbase (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) (by norm_num)
theorem B1283233 : Blo 1140634 1283233 := bbase (se 2 (by rfl) ⟨481212, by rfl⟩ : syracuseStep 1283233 = 962425) (by norm_num)
theorem B1447085 : Blo 1140634 1447085 := bbase (se 3 (by rfl) ⟨271328, by rfl⟩ : syracuseStep 1447085 = 542657) (by norm_num)
theorem B2888885 : Blo 1140634 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B1283269 : Blo 1140634 1283269 := bbase (se 4 (by rfl) ⟨120306, by rfl⟩ : syracuseStep 1283269 = 240613) (by norm_num)
theorem B1742029 : Blo 1140634 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B1545421 : Blo 1140634 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B1447141 : Blo 1140634 1447141 := bbase (se 4 (by rfl) ⟨135669, by rfl⟩ : syracuseStep 1447141 = 271339) (by norm_num)
theorem B1283305 : Blo 1140634 1283305 := bbase (se 2 (by rfl) ⟨481239, by rfl⟩ : syracuseStep 1283305 = 962479) (by norm_num)
theorem B1283341 : Blo 1140634 1283341 := bbase (se 3 (by rfl) ⟨240626, by rfl⟩ : syracuseStep 1283341 = 481253) (by norm_num)
theorem B1283377 : Blo 1140634 1283377 := bbase (se 2 (by rfl) ⟨481266, by rfl⟩ : syracuseStep 1283377 = 962533) (by norm_num)
theorem B1447237 : Blo 1140634 1447237 := bbase (se 4 (by rfl) ⟨135678, by rfl⟩ : syracuseStep 1447237 = 271357) (by norm_num)
theorem B4887877 : Blo 1140634 4887877 := bbase (se 4 (by rfl) ⟨458238, by rfl⟩ : syracuseStep 4887877 = 916477) (by norm_num)
theorem B1283413 : Blo 1140634 1283413 := bbase (se 14 (by rfl) ⟨117, by rfl⟩ : syracuseStep 1283413 = 235) (by norm_num)
theorem B4330853 : Blo 1140634 4330853 := bbase (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) (by norm_num)
theorem B1283449 : Blo 1140634 1283449 := bbase (se 2 (by rfl) ⟨481293, by rfl⟩ : syracuseStep 1283449 = 962587) (by norm_num)
theorem B1283485 : Blo 1140634 1283485 := bbase (se 3 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 1283485 = 481307) (by norm_num)
theorem B2168221 : Blo 1140634 2168221 := bbase (se 3 (by rfl) ⟨406541, by rfl⟩ : syracuseStep 2168221 = 813083) (by norm_num)
theorem B1545637 : Blo 1140634 1545637 := bbase (se 4 (by rfl) ⟨144903, by rfl⟩ : syracuseStep 1545637 = 289807) (by norm_num)
theorem B1283521 : Blo 1140634 1283521 := bbase (se 2 (by rfl) ⟨481320, by rfl⟩ : syracuseStep 1283521 = 962641) (by norm_num)
theorem B1283557 : Blo 1140634 1283557 := bbase (se 4 (by rfl) ⟨120333, by rfl⟩ : syracuseStep 1283557 = 240667) (by norm_num)
theorem B1447409 : Blo 1140634 1447409 := bbase (se 2 (by rfl) ⟨542778, by rfl⟩ : syracuseStep 1447409 = 1085557) (by norm_num)
theorem B1283593 : Blo 1140634 1283593 := bbase (se 2 (by rfl) ⟨481347, by rfl⟩ : syracuseStep 1283593 = 962695) (by norm_num)
theorem B2889229 : Blo 1140634 2889229 := bbase (se 3 (by rfl) ⟨541730, by rfl⟩ : syracuseStep 2889229 = 1083461) (by norm_num)
theorem B1447465 : Blo 1140634 1447465 := bbase (se 2 (by rfl) ⟨542799, by rfl⟩ : syracuseStep 1447465 = 1085599) (by norm_num)
theorem B1283629 : Blo 1140634 1283629 := bbase (se 3 (by rfl) ⟨240680, by rfl⟩ : syracuseStep 1283629 = 481361) (by norm_num)
theorem B2168365 : Blo 1140634 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B1218125 : Blo 1140634 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1283665 : Blo 1140634 1283665 := bbase (se 2 (by rfl) ⟨481374, by rfl⟩ : syracuseStep 1283665 = 962749) (by norm_num)
theorem B1283701 : Blo 1140634 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B2889341 : Blo 1140634 2889341 := bbase (se 3 (by rfl) ⟨541751, by rfl⟩ : syracuseStep 2889341 = 1083503) (by norm_num)
theorem B4331141 : Blo 1140634 4331141 := bbase (se 4 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 4331141 = 812089) (by norm_num)
theorem B1447561 : Blo 1140634 1447561 := bbase (se 2 (by rfl) ⟨542835, by rfl⟩ : syracuseStep 1447561 = 1085671) (by norm_num)
theorem B1283737 : Blo 1140634 1283737 := bbase (se 2 (by rfl) ⟨481401, by rfl⟩ : syracuseStep 1283737 = 962803) (by norm_num)
theorem B1283773 : Blo 1140634 1283773 := bbase (se 3 (by rfl) ⟨240707, by rfl⟩ : syracuseStep 1283773 = 481415) (by norm_num)
theorem B2168525 : Blo 1140634 2168525 := bbase (se 3 (by rfl) ⟨406598, by rfl⟩ : syracuseStep 2168525 = 813197) (by norm_num)
theorem B1283809 : Blo 1140634 1283809 := bbase (se 2 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 1283809 = 962857) (by norm_num)
theorem B1283845 : Blo 1140634 1283845 := bbase (se 4 (by rfl) ⟨120360, by rfl⟩ : syracuseStep 1283845 = 240721) (by norm_num)
theorem B1283881 : Blo 1140634 1283881 := bbase (se 2 (by rfl) ⟨481455, by rfl⟩ : syracuseStep 1283881 = 962911) (by norm_num)
theorem B3249973 : Blo 1140634 3249973 := bbase (se 5 (by rfl) ⟨152342, by rfl⟩ : syracuseStep 3249973 = 304685) (by norm_num)
theorem B1447733 : Blo 1140634 1447733 := bbase (se 5 (by rfl) ⟨67862, by rfl⟩ : syracuseStep 1447733 = 135725) (by norm_num)
theorem B2889533 : Blo 1140634 2889533 := bbase (se 3 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 2889533 = 1083575) (by norm_num)
theorem B1283917 : Blo 1140634 1283917 := bbase (se 3 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 1283917 = 481469) (by norm_num)
theorem B7313237 : Blo 1140634 7313237 := bbase (se 9 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 7313237 = 42851) (by norm_num)
theorem B2168669 : Blo 1140634 2168669 := bbase (se 3 (by rfl) ⟨406625, by rfl⟩ : syracuseStep 2168669 = 813251) (by norm_num)
theorem B1447789 : Blo 1140634 1447789 := bbase (se 3 (by rfl) ⟨271460, by rfl⟩ : syracuseStep 1447789 = 542921) (by norm_num)
theorem B1283953 : Blo 1140634 1283953 := bbase (se 2 (by rfl) ⟨481482, by rfl⟩ : syracuseStep 1283953 = 962965) (by norm_num)
theorem B1283989 : Blo 1140634 1283989 := bbase (se 6 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 1283989 = 60187) (by norm_num)
theorem B1284025 : Blo 1140634 1284025 := bbase (se 2 (by rfl) ⟨481509, by rfl⟩ : syracuseStep 1284025 = 963019) (by norm_num)
theorem B1447885 : Blo 1140634 1447885 := bbase (se 3 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 1447885 = 542957) (by norm_num)
theorem B1284061 : Blo 1140634 1284061 := bbase (se 3 (by rfl) ⟨240761, by rfl⟩ : syracuseStep 1284061 = 481523) (by norm_num)
theorem B1284097 : Blo 1140634 1284097 := bbase (se 2 (by rfl) ⟨481536, by rfl⟩ : syracuseStep 1284097 = 963073) (by norm_num)
theorem B1218569 : Blo 1140634 1218569 := bbase (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) (by norm_num)
theorem B1284133 : Blo 1140634 1284133 := bbase (se 4 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 1284133 = 240775) (by norm_num)
theorem B4888613 : Blo 1140634 4888613 := bbase (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) (by norm_num)
theorem B1284169 : Blo 1140634 1284169 := bbase (se 2 (by rfl) ⟨481563, by rfl⟩ : syracuseStep 1284169 = 963127) (by norm_num)
theorem B1284205 : Blo 1140634 1284205 := bbase (se 3 (by rfl) ⟨240788, by rfl⟩ : syracuseStep 1284205 = 481577) (by norm_num)
theorem B1448057 : Blo 1140634 1448057 := bbase (se 2 (by rfl) ⟨543021, by rfl⟩ : syracuseStep 1448057 = 1086043) (by norm_num)
theorem B2168957 : Blo 1140634 2168957 := bbase (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) (by norm_num)
theorem B1284241 : Blo 1140634 1284241 := bbase (se 2 (by rfl) ⟨481590, by rfl⟩ : syracuseStep 1284241 = 963181) (by norm_num)
theorem B2889877 : Blo 1140634 2889877 := bbase (se 6 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 2889877 = 135463) (by norm_num)
theorem B1448113 : Blo 1140634 1448113 := bbase (se 2 (by rfl) ⟨543042, by rfl⟩ : syracuseStep 1448113 = 1086085) (by norm_num)
theorem B1284277 : Blo 1140634 1284277 := bbase (se 5 (by rfl) ⟨60200, by rfl⟩ : syracuseStep 1284277 = 120401) (by norm_num)
theorem B1284313 : Blo 1140634 1284313 := bbase (se 2 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 1284313 = 963235) (by norm_num)
theorem B1284349 : Blo 1140634 1284349 := bbase (se 3 (by rfl) ⟨240815, by rfl⟩ : syracuseStep 1284349 = 481631) (by norm_num)
theorem B1218817 : Blo 1140634 1218817 := bbase (se 2 (by rfl) ⟨457056, by rfl⟩ : syracuseStep 1218817 = 914113) (by norm_num)
theorem B2889989 : Blo 1140634 2889989 := bbase (se 4 (by rfl) ⟨270936, by rfl⟩ : syracuseStep 2889989 = 541873) (by norm_num)
theorem B1448209 : Blo 1140634 1448209 := bbase (se 2 (by rfl) ⟨543078, by rfl⟩ : syracuseStep 1448209 = 1086157) (by norm_num)
theorem B2169109 : Blo 1140634 2169109 := bbase (se 6 (by rfl) ⟨50838, by rfl⟩ : syracuseStep 2169109 = 101677) (by norm_num)
theorem B1284385 : Blo 1140634 1284385 := bbase (se 2 (by rfl) ⟨481644, by rfl⟩ : syracuseStep 1284385 = 963289) (by norm_num)
theorem B1284421 : Blo 1140634 1284421 := bbase (se 4 (by rfl) ⟨120414, by rfl⟩ : syracuseStep 1284421 = 240829) (by norm_num)
theorem B1284457 : Blo 1140634 1284457 := bbase (se 2 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 1284457 = 963343) (by norm_num)
theorem B1284493 : Blo 1140634 1284493 := bbase (se 3 (by rfl) ⟨240842, by rfl⟩ : syracuseStep 1284493 = 481685) (by norm_num)
theorem B1284529 : Blo 1140634 1284529 := bbase (se 2 (by rfl) ⟨481698, by rfl⟩ : syracuseStep 1284529 = 963397) (by norm_num)
theorem B1448381 : Blo 1140634 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B2890181 : Blo 1140634 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B1284565 : Blo 1140634 1284565 := bbase (se 7 (by rfl) ⟨15053, by rfl⟩ : syracuseStep 1284565 = 30107) (by norm_num)
theorem B8690165 : Blo 1140634 8690165 := bbase (se 5 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 8690165 = 814703) (by norm_num)
theorem B1448437 : Blo 1140634 1448437 := bbase (se 5 (by rfl) ⟨67895, by rfl⟩ : syracuseStep 1448437 = 135791) (by norm_num)
theorem B1284601 : Blo 1140634 1284601 := bbase (se 2 (by rfl) ⟨481725, by rfl⟩ : syracuseStep 1284601 = 963451) (by norm_num)
theorem B1284637 : Blo 1140634 1284637 := bbase (se 3 (by rfl) ⟨240869, by rfl⟩ : syracuseStep 1284637 = 481739) (by norm_num)
theorem B1284673 : Blo 1140634 1284673 := bbase (se 2 (by rfl) ⟨481752, by rfl⟩ : syracuseStep 1284673 = 963505) (by norm_num)
theorem B2169413 : Blo 1140634 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B1448533 : Blo 1140634 1448533 := bbase (se 8 (by rfl) ⟨8487, by rfl⟩ : syracuseStep 1448533 = 16975) (by norm_num)
theorem B1284709 : Blo 1140634 1284709 := bbase (se 4 (by rfl) ⟨120441, by rfl⟩ : syracuseStep 1284709 = 240883) (by norm_num)
theorem B1284745 : Blo 1140634 1284745 := bbase (se 2 (by rfl) ⟨481779, by rfl⟩ : syracuseStep 1284745 = 963559) (by norm_num)
theorem B1284781 : Blo 1140634 1284781 := bbase (se 3 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 1284781 = 481793) (by norm_num)
theorem B1219249 : Blo 1140634 1219249 := bbase (se 2 (by rfl) ⟨457218, by rfl⟩ : syracuseStep 1219249 = 914437) (by norm_num)
theorem B1284817 : Blo 1140634 1284817 := bbase (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) (by norm_num)
theorem B1284853 : Blo 1140634 1284853 := bbase (se 5 (by rfl) ⟨60227, by rfl⟩ : syracuseStep 1284853 = 120455) (by norm_num)
theorem B1219321 : Blo 1140634 1219321 := bbase (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) (by norm_num)
theorem B1284889 : Blo 1140634 1284889 := bbase (se 2 (by rfl) ⟨481833, by rfl⟩ : syracuseStep 1284889 = 963667) (by norm_num)
theorem B2890525 : Blo 1140634 2890525 := bbase (se 3 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 2890525 = 1083947) (by norm_num)
theorem B4332325 : Blo 1140634 4332325 := bbase (se 4 (by rfl) ⟨406155, by rfl⟩ : syracuseStep 4332325 = 812311) (by norm_num)
theorem B1284925 : Blo 1140634 1284925 := bbase (se 3 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 1284925 = 481847) (by norm_num)
theorem B1284961 : Blo 1140634 1284961 := bbase (se 2 (by rfl) ⟨481860, by rfl⟩ : syracuseStep 1284961 = 963721) (by norm_num)
theorem B1710965 : Blo 1140634 1710965 := bbase (se 5 (by rfl) ⟨80201, by rfl⟩ : syracuseStep 1710965 = 160403) (by norm_num)
theorem B1284997 : Blo 1140634 1284997 := bbase (se 4 (by rfl) ⟨120468, by rfl⟩ : syracuseStep 1284997 = 240937) (by norm_num)
theorem B1710989 : Blo 1140634 1710989 := bbase (se 3 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 1710989 = 641621) (by norm_num)
theorem B2890637 : Blo 1140634 2890637 := bbase (se 3 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 2890637 = 1083989) (by norm_num)
theorem B14654357 : Blo 1140634 14654357 := bbase (se 6 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 14654357 = 686923) (by norm_num)
theorem B1711013 : Blo 1140634 1711013 := bbase (se 4 (by rfl) ⟨160407, by rfl⟩ : syracuseStep 1711013 = 320815) (by norm_num)
theorem B1285033 : Blo 1140634 1285033 := bbase (se 2 (by rfl) ⟨481887, by rfl⟩ : syracuseStep 1285033 = 963775) (by norm_num)
theorem B1711037 : Blo 1140634 1711037 := bbase (se 3 (by rfl) ⟨320819, by rfl⟩ : syracuseStep 1711037 = 641639) (by norm_num)
theorem B1285069 : Blo 1140634 1285069 := bbase (se 3 (by rfl) ⟨240950, by rfl⟩ : syracuseStep 1285069 = 481901) (by norm_num)
theorem B1711061 : Blo 1140634 1711061 := bbase (se 7 (by rfl) ⟨20051, by rfl⟩ : syracuseStep 1711061 = 40103) (by norm_num)
theorem B1711085 : Blo 1140634 1711085 := bbase (se 3 (by rfl) ⟨320828, by rfl⟩ : syracuseStep 1711085 = 641657) (by norm_num)
theorem B1285105 : Blo 1140634 1285105 := bbase (se 2 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 1285105 = 963829) (by norm_num)
theorem B1711109 : Blo 1140634 1711109 := bbase (se 4 (by rfl) ⟨160416, by rfl⟩ : syracuseStep 1711109 = 320833) (by norm_num)
theorem B1285141 : Blo 1140634 1285141 := bbase (se 6 (by rfl) ⟨30120, by rfl⟩ : syracuseStep 1285141 = 60241) (by norm_num)
theorem B1711133 : Blo 1140634 1711133 := bbase (se 3 (by rfl) ⟨320837, by rfl⟩ : syracuseStep 1711133 = 641675) (by norm_num)
theorem B1711157 : Blo 1140634 1711157 := bbase (se 5 (by rfl) ⟨80210, by rfl⟩ : syracuseStep 1711157 = 160421) (by norm_num)
theorem B1285177 : Blo 1140634 1285177 := bbase (se 2 (by rfl) ⟨481941, by rfl⟩ : syracuseStep 1285177 = 963883) (by norm_num)
theorem B1711181 : Blo 1140634 1711181 := bbase (se 3 (by rfl) ⟨320846, by rfl⟩ : syracuseStep 1711181 = 641693) (by norm_num)
theorem B2890829 : Blo 1140634 2890829 := bbase (se 3 (by rfl) ⟨542030, by rfl⟩ : syracuseStep 2890829 = 1084061) (by norm_num)
theorem B4332629 : Blo 1140634 4332629 := bbase (se 8 (by rfl) ⟨25386, by rfl⟩ : syracuseStep 4332629 = 50773) (by norm_num)
theorem B17603669 : Blo 1140634 17603669 := bbase (se 8 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 17603669 = 206293) (by norm_num)
theorem B1285213 : Blo 1140634 1285213 := bbase (se 3 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 1285213 = 481955) (by norm_num)
theorem B1711205 : Blo 1140634 1711205 := bbase (se 4 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 1711205 = 320851) (by norm_num)
theorem B1219693 : Blo 1140634 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B1711229 : Blo 1140634 1711229 := bbase (se 3 (by rfl) ⟨320855, by rfl⟩ : syracuseStep 1711229 = 641711) (by norm_num)
theorem B1285249 : Blo 1140634 1285249 := bbase (se 2 (by rfl) ⟨481968, by rfl⟩ : syracuseStep 1285249 = 963937) (by norm_num)
theorem B1711253 : Blo 1140634 1711253 := bbase (se 6 (by rfl) ⟨40107, by rfl⟩ : syracuseStep 1711253 = 80215) (by norm_num)
theorem B1285285 : Blo 1140634 1285285 := bbase (se 4 (by rfl) ⟨120495, by rfl⟩ : syracuseStep 1285285 = 240991) (by norm_num)
theorem B1711277 : Blo 1140634 1711277 := bbase (se 3 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 1711277 = 641729) (by norm_num)
theorem B1711301 : Blo 1140634 1711301 := bbase (se 4 (by rfl) ⟨160434, by rfl⟩ : syracuseStep 1711301 = 320869) (by norm_num)
theorem B1285321 : Blo 1140634 1285321 := bbase (se 2 (by rfl) ⟨481995, by rfl⟩ : syracuseStep 1285321 = 963991) (by norm_num)
theorem B1711325 : Blo 1140634 1711325 := bbase (se 3 (by rfl) ⟨320873, by rfl⟩ : syracuseStep 1711325 = 641747) (by norm_num)
theorem B1285357 : Blo 1140634 1285357 := bbase (se 3 (by rfl) ⟨241004, by rfl⟩ : syracuseStep 1285357 = 482009) (by norm_num)
theorem B1711349 : Blo 1140634 1711349 := bbase (se 5 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 1711349 = 160439) (by norm_num)
theorem B9280757 : Blo 1140634 9280757 := bbase (se 5 (by rfl) ⟨435035, by rfl⟩ : syracuseStep 9280757 = 870071) (by norm_num)
theorem B1711373 : Blo 1140634 1711373 := bbase (se 3 (by rfl) ⟨320882, by rfl⟩ : syracuseStep 1711373 = 641765) (by norm_num)
theorem B1285393 : Blo 1140634 1285393 := bbase (se 2 (by rfl) ⟨482022, by rfl⟩ : syracuseStep 1285393 = 964045) (by norm_num)
theorem B3251477 : Blo 1140634 3251477 := bbase (se 6 (by rfl) ⟨76206, by rfl⟩ : syracuseStep 3251477 = 152413) (by norm_num)
theorem B1711397 : Blo 1140634 1711397 := bbase (se 4 (by rfl) ⟨160443, by rfl⟩ : syracuseStep 1711397 = 320887) (by norm_num)
theorem B1285429 : Blo 1140634 1285429 := bbase (se 5 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 1285429 = 120509) (by norm_num)
theorem B2170165 : Blo 1140634 2170165 := bbase (se 5 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 2170165 = 203453) (by norm_num)
theorem B1711421 : Blo 1140634 1711421 := bbase (se 3 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 1711421 = 641783) (by norm_num)
theorem B1711445 : Blo 1140634 1711445 := bbase (se 11 (by rfl) ⟨1253, by rfl⟩ : syracuseStep 1711445 = 2507) (by norm_num)
theorem B1285465 : Blo 1140634 1285465 := bbase (se 2 (by rfl) ⟨482049, by rfl⟩ : syracuseStep 1285465 = 964099) (by norm_num)
theorem B1711469 : Blo 1140634 1711469 := bbase (se 3 (by rfl) ⟨320900, by rfl⟩ : syracuseStep 1711469 = 641801) (by norm_num)
theorem B1285501 : Blo 1140634 1285501 := bbase (se 3 (by rfl) ⟨241031, by rfl⟩ : syracuseStep 1285501 = 482063) (by norm_num)
theorem B1711493 : Blo 1140634 1711493 := bbase (se 4 (by rfl) ⟨160452, by rfl⟩ : syracuseStep 1711493 = 320905) (by norm_num)
theorem B1711517 : Blo 1140634 1711517 := bbase (se 3 (by rfl) ⟨320909, by rfl⟩ : syracuseStep 1711517 = 641819) (by norm_num)
theorem B1285537 : Blo 1140634 1285537 := bbase (se 2 (by rfl) ⟨482076, by rfl⟩ : syracuseStep 1285537 = 964153) (by norm_num)
theorem B2891173 : Blo 1140634 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B1711541 : Blo 1140634 1711541 := bbase (se 5 (by rfl) ⟨80228, by rfl⟩ : syracuseStep 1711541 = 160457) (by norm_num)
theorem B1285573 : Blo 1140634 1285573 := bbase (se 4 (by rfl) ⟨120522, by rfl⟩ : syracuseStep 1285573 = 241045) (by norm_num)
theorem B2170309 : Blo 1140634 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B1711565 : Blo 1140634 1711565 := bbase (se 3 (by rfl) ⟨320918, by rfl⟩ : syracuseStep 1711565 = 641837) (by norm_num)
theorem B4627925 : Blo 1140634 4627925 := bbase (se 7 (by rfl) ⟨54233, by rfl⟩ : syracuseStep 4627925 = 108467) (by norm_num)
theorem B1711589 : Blo 1140634 1711589 := bbase (se 4 (by rfl) ⟨160461, by rfl⟩ : syracuseStep 1711589 = 320923) (by norm_num)
theorem B1220069 : Blo 1140634 1220069 := bbase (se 4 (by rfl) ⟨114381, by rfl⟩ : syracuseStep 1220069 = 228763) (by norm_num)
theorem B1285609 : Blo 1140634 1285609 := bbase (se 2 (by rfl) ⟨482103, by rfl⟩ : syracuseStep 1285609 = 964207) (by norm_num)
theorem B1711613 : Blo 1140634 1711613 := bbase (se 3 (by rfl) ⟨320927, by rfl⟩ : syracuseStep 1711613 = 641855) (by norm_num)
theorem B1285645 : Blo 1140634 1285645 := bbase (se 3 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 1285645 = 482117) (by norm_num)
theorem B1711637 : Blo 1140634 1711637 := bbase (se 6 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 1711637 = 80233) (by norm_num)
theorem B2891285 : Blo 1140634 2891285 := bbase (se 6 (by rfl) ⟨67764, by rfl⟩ : syracuseStep 2891285 = 135529) (by norm_num)
theorem B1711661 : Blo 1140634 1711661 := bbase (se 3 (by rfl) ⟨320936, by rfl⟩ : syracuseStep 1711661 = 641873) (by norm_num)
theorem B1220141 : Blo 1140634 1220141 := bbase (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) (by norm_num)
theorem B1285681 : Blo 1140634 1285681 := bbase (se 2 (by rfl) ⟨482130, by rfl⟩ : syracuseStep 1285681 = 964261) (by norm_num)
theorem B1711685 : Blo 1140634 1711685 := bbase (se 4 (by rfl) ⟨160470, by rfl⟩ : syracuseStep 1711685 = 320941) (by norm_num)
theorem B4628053 : Blo 1140634 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B1285717 : Blo 1140634 1285717 := bbase (se 8 (by rfl) ⟨7533, by rfl⟩ : syracuseStep 1285717 = 15067) (by norm_num)
theorem B1711709 : Blo 1140634 1711709 := bbase (se 3 (by rfl) ⟨320945, by rfl⟩ : syracuseStep 1711709 = 641891) (by norm_num)
theorem B2170469 : Blo 1140634 2170469 := bbase (se 4 (by rfl) ⟨203481, by rfl⟩ : syracuseStep 2170469 = 406963) (by norm_num)
theorem B1711733 : Blo 1140634 1711733 := bbase (se 5 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 1711733 = 160475) (by norm_num)
theorem B1285753 : Blo 1140634 1285753 := bbase (se 2 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 1285753 = 964315) (by norm_num)
theorem B1711757 : Blo 1140634 1711757 := bbase (se 3 (by rfl) ⟨320954, by rfl⟩ : syracuseStep 1711757 = 641909) (by norm_num)
theorem B1285789 : Blo 1140634 1285789 := bbase (se 3 (by rfl) ⟨241085, by rfl⟩ : syracuseStep 1285789 = 482171) (by norm_num)
theorem B1711781 : Blo 1140634 1711781 := bbase (se 4 (by rfl) ⟨160479, by rfl⟩ : syracuseStep 1711781 = 320959) (by norm_num)
theorem B1711805 : Blo 1140634 1711805 := bbase (se 3 (by rfl) ⟨320963, by rfl⟩ : syracuseStep 1711805 = 641927) (by norm_num)
theorem B1285825 : Blo 1140634 1285825 := bbase (se 2 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 1285825 = 964369) (by norm_num)
theorem B1711829 : Blo 1140634 1711829 := bbase (se 7 (by rfl) ⟨20060, by rfl⟩ : syracuseStep 1711829 = 40121) (by norm_num)
theorem B2891477 : Blo 1140634 2891477 := bbase (se 7 (by rfl) ⟨33884, by rfl⟩ : syracuseStep 2891477 = 67769) (by norm_num)
theorem B1285861 : Blo 1140634 1285861 := bbase (se 4 (by rfl) ⟨120549, by rfl⟩ : syracuseStep 1285861 = 241099) (by norm_num)
theorem B1220329 : Blo 1140634 1220329 := bbase (se 2 (by rfl) ⟨457623, by rfl⟩ : syracuseStep 1220329 = 915247) (by norm_num)
theorem B1711853 : Blo 1140634 1711853 := bbase (se 3 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 1711853 = 641945) (by norm_num)
theorem B2170613 : Blo 1140634 2170613 := bbase (se 5 (by rfl) ⟨101747, by rfl⟩ : syracuseStep 2170613 = 203495) (by norm_num)
theorem B1711877 : Blo 1140634 1711877 := bbase (se 4 (by rfl) ⟨160488, by rfl⟩ : syracuseStep 1711877 = 320977) (by norm_num)
theorem B1285897 : Blo 1140634 1285897 := bbase (se 2 (by rfl) ⟨482211, by rfl⟩ : syracuseStep 1285897 = 964423) (by norm_num)
theorem B1711901 : Blo 1140634 1711901 := bbase (se 3 (by rfl) ⟨320981, by rfl⟩ : syracuseStep 1711901 = 641963) (by norm_num)
theorem B1285933 : Blo 1140634 1285933 := bbase (se 3 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 1285933 = 482225) (by norm_num)
theorem B1711925 : Blo 1140634 1711925 := bbase (se 5 (by rfl) ⟨80246, by rfl⟩ : syracuseStep 1711925 = 160493) (by norm_num)
theorem B3088181 : Blo 1140634 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B1711949 : Blo 1140634 1711949 := bbase (se 3 (by rfl) ⟨320990, by rfl⟩ : syracuseStep 1711949 = 641981) (by norm_num)
theorem B1285969 : Blo 1140634 1285969 := bbase (se 2 (by rfl) ⟨482238, by rfl⟩ : syracuseStep 1285969 = 964477) (by norm_num)
theorem B1711973 : Blo 1140634 1711973 := bbase (se 4 (by rfl) ⟨160497, by rfl⟩ : syracuseStep 1711973 = 320995) (by norm_num)
theorem B1286005 : Blo 1140634 1286005 := bbase (se 5 (by rfl) ⟨60281, by rfl⟩ : syracuseStep 1286005 = 120563) (by norm_num)
theorem B1711997 : Blo 1140634 1711997 := bbase (se 3 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 1711997 = 641999) (by norm_num)
theorem B1712021 : Blo 1140634 1712021 := bbase (se 6 (by rfl) ⟨40125, by rfl⟩ : syracuseStep 1712021 = 80251) (by norm_num)
theorem B1286041 : Blo 1140634 1286041 := bbase (se 2 (by rfl) ⟨482265, by rfl⟩ : syracuseStep 1286041 = 964531) (by norm_num)
theorem B1220513 : Blo 1140634 1220513 := bbase (se 2 (by rfl) ⟨457692, by rfl⟩ : syracuseStep 1220513 = 915385) (by norm_num)
theorem B1712045 : Blo 1140634 1712045 := bbase (se 3 (by rfl) ⟨321008, by rfl⟩ : syracuseStep 1712045 = 642017) (by norm_num)
theorem B1286077 : Blo 1140634 1286077 := bbase (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) (by norm_num)
theorem B1712069 : Blo 1140634 1712069 := bbase (se 4 (by rfl) ⟨160506, by rfl⟩ : syracuseStep 1712069 = 321013) (by norm_num)
theorem B1646557 : Blo 1140634 1646557 := bbase (se 3 (by rfl) ⟨308729, by rfl⟩ : syracuseStep 1646557 = 617459) (by norm_num)
theorem B1712093 : Blo 1140634 1712093 := bbase (se 3 (by rfl) ⟨321017, by rfl⟩ : syracuseStep 1712093 = 642035) (by norm_num)
theorem B1286113 : Blo 1140634 1286113 := bbase (se 2 (by rfl) ⟨482292, by rfl⟩ : syracuseStep 1286113 = 964585) (by norm_num)
theorem B1712117 : Blo 1140634 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B1286149 : Blo 1140634 1286149 := bbase (se 4 (by rfl) ⟨120576, by rfl⟩ : syracuseStep 1286149 = 241153) (by norm_num)
theorem B1712141 : Blo 1140634 1712141 := bbase (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) (by norm_num)
theorem B2170901 : Blo 1140634 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B1712165 : Blo 1140634 1712165 := bbase (se 4 (by rfl) ⟨160515, by rfl⟩ : syracuseStep 1712165 = 321031) (by norm_num)
theorem B1286185 : Blo 1140634 1286185 := bbase (se 2 (by rfl) ⟨482319, by rfl⟩ : syracuseStep 1286185 = 964639) (by norm_num)
theorem B2891821 : Blo 1140634 2891821 := bbase (se 3 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 2891821 = 1084433) (by norm_num)
theorem B1712189 : Blo 1140634 1712189 := bbase (se 3 (by rfl) ⟨321035, by rfl⟩ : syracuseStep 1712189 = 642071) (by norm_num)
theorem B1286221 : Blo 1140634 1286221 := bbase (se 3 (by rfl) ⟨241166, by rfl⟩ : syracuseStep 1286221 = 482333) (by norm_num)
theorem B1712213 : Blo 1140634 1712213 := bbase (se 8 (by rfl) ⟨10032, by rfl⟩ : syracuseStep 1712213 = 20065) (by norm_num)
theorem B5775461 : Blo 1140634 5775461 := bbase (se 4 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 5775461 = 1082899) (by norm_num)
theorem B1712237 : Blo 1140634 1712237 := bbase (se 3 (by rfl) ⟨321044, by rfl⟩ : syracuseStep 1712237 = 642089) (by norm_num)
theorem B1286257 : Blo 1140634 1286257 := bbase (se 2 (by rfl) ⟨482346, by rfl⟩ : syracuseStep 1286257 = 964693) (by norm_num)
theorem B1712261 : Blo 1140634 1712261 := bbase (se 4 (by rfl) ⟨160524, by rfl⟩ : syracuseStep 1712261 = 321049) (by norm_num)
theorem B1286293 : Blo 1140634 1286293 := bbase (se 6 (by rfl) ⟨30147, by rfl⟩ : syracuseStep 1286293 = 60295) (by norm_num)
theorem B1712285 : Blo 1140634 1712285 := bbase (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) (by norm_num)
theorem B2891933 : Blo 1140634 2891933 := bbase (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) (by norm_num)
theorem B2171053 : Blo 1140634 2171053 := bbase (se 3 (by rfl) ⟨407072, by rfl⟩ : syracuseStep 2171053 = 814145) (by norm_num)
theorem B1712309 : Blo 1140634 1712309 := bbase (se 5 (by rfl) ⟨80264, by rfl⟩ : syracuseStep 1712309 = 160529) (by norm_num)
theorem B1286329 : Blo 1140634 1286329 := bbase (se 2 (by rfl) ⟨482373, by rfl⟩ : syracuseStep 1286329 = 964747) (by norm_num)
theorem B1712333 : Blo 1140634 1712333 := bbase (se 3 (by rfl) ⟨321062, by rfl⟩ : syracuseStep 1712333 = 642125) (by norm_num)
theorem B1286365 : Blo 1140634 1286365 := bbase (se 3 (by rfl) ⟨241193, by rfl⟩ : syracuseStep 1286365 = 482387) (by norm_num)
theorem B1712357 : Blo 1140634 1712357 := bbase (se 4 (by rfl) ⟨160533, by rfl⟩ : syracuseStep 1712357 = 321067) (by norm_num)
theorem B1712381 : Blo 1140634 1712381 := bbase (se 3 (by rfl) ⟨321071, by rfl⟩ : syracuseStep 1712381 = 642143) (by norm_num)
theorem B1286401 : Blo 1140634 1286401 := bbase (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) (by norm_num)
theorem B1712405 : Blo 1140634 1712405 := bbase (se 6 (by rfl) ⟨40134, by rfl⟩ : syracuseStep 1712405 = 80269) (by norm_num)
theorem B1286437 : Blo 1140634 1286437 := bbase (se 4 (by rfl) ⟨120603, by rfl⟩ : syracuseStep 1286437 = 241207) (by norm_num)
theorem B1712429 : Blo 1140634 1712429 := bbase (se 3 (by rfl) ⟨321080, by rfl⟩ : syracuseStep 1712429 = 642161) (by norm_num)
theorem B1712453 : Blo 1140634 1712453 := bbase (se 4 (by rfl) ⟨160542, by rfl⟩ : syracuseStep 1712453 = 321085) (by norm_num)
theorem B1286473 : Blo 1140634 1286473 := bbase (se 2 (by rfl) ⟨482427, by rfl⟩ : syracuseStep 1286473 = 964855) (by norm_num)
theorem B1712477 : Blo 1140634 1712477 := bbase (se 3 (by rfl) ⟨321089, by rfl⟩ : syracuseStep 1712477 = 642179) (by norm_num)
theorem B2892125 : Blo 1140634 2892125 := bbase (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) (by norm_num)
theorem B1286509 : Blo 1140634 1286509 := bbase (se 3 (by rfl) ⟨241220, by rfl⟩ : syracuseStep 1286509 = 482441) (by norm_num)
theorem B1712501 : Blo 1140634 1712501 := bbase (se 5 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 1712501 = 160547) (by norm_num)
theorem B1712525 : Blo 1140634 1712525 := bbase (se 3 (by rfl) ⟨321098, by rfl⟩ : syracuseStep 1712525 = 642197) (by norm_num)
theorem B1286545 : Blo 1140634 1286545 := bbase (se 2 (by rfl) ⟨482454, by rfl⟩ : syracuseStep 1286545 = 964909) (by norm_num)
theorem B1712549 : Blo 1140634 1712549 := bbase (se 4 (by rfl) ⟨160551, by rfl⟩ : syracuseStep 1712549 = 321103) (by norm_num)
theorem B1286581 : Blo 1140634 1286581 := bbase (se 5 (by rfl) ⟨60308, by rfl⟩ : syracuseStep 1286581 = 120617) (by norm_num)
theorem B1712573 : Blo 1140634 1712573 := bbase (se 3 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 1712573 = 642215) (by norm_num)
theorem B1712597 : Blo 1140634 1712597 := bbase (se 7 (by rfl) ⟨20069, by rfl⟩ : syracuseStep 1712597 = 40139) (by norm_num)
theorem B1286617 : Blo 1140634 1286617 := bbase (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) (by norm_num)
theorem B2171357 : Blo 1140634 2171357 := bbase (se 3 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 2171357 = 814259) (by norm_num)
theorem B1712621 : Blo 1140634 1712621 := bbase (se 3 (by rfl) ⟨321116, by rfl⟩ : syracuseStep 1712621 = 642233) (by norm_num)
theorem B6496757 : Blo 1140634 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B1286653 : Blo 1140634 1286653 := bbase (se 3 (by rfl) ⟨241247, by rfl⟩ : syracuseStep 1286653 = 482495) (by norm_num)
theorem B1712645 : Blo 1140634 1712645 := bbase (se 4 (by rfl) ⟨160560, by rfl⟩ : syracuseStep 1712645 = 321121) (by norm_num)
theorem B6595093 : Blo 1140634 6595093 := bbase (se 6 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 6595093 = 309145) (by norm_num)
theorem B1712669 : Blo 1140634 1712669 := bbase (se 3 (by rfl) ⟨321125, by rfl⟩ : syracuseStep 1712669 = 642251) (by norm_num)
theorem B1286689 : Blo 1140634 1286689 := bbase (se 2 (by rfl) ⟨482508, by rfl⟩ : syracuseStep 1286689 = 965017) (by norm_num)
theorem B1712693 : Blo 1140634 1712693 := bbase (se 5 (by rfl) ⟨80282, by rfl⟩ : syracuseStep 1712693 = 160565) (by norm_num)
theorem B1286725 : Blo 1140634 1286725 := bbase (se 4 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 1286725 = 241261) (by norm_num)
theorem B1712717 : Blo 1140634 1712717 := bbase (se 3 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 1712717 = 642269) (by norm_num)
theorem B1712741 : Blo 1140634 1712741 := bbase (se 4 (by rfl) ⟨160569, by rfl⟩ : syracuseStep 1712741 = 321139) (by norm_num)
theorem B1286761 : Blo 1140634 1286761 := bbase (se 2 (by rfl) ⟨482535, by rfl⟩ : syracuseStep 1286761 = 965071) (by norm_num)
theorem B1712765 : Blo 1140634 1712765 := bbase (se 3 (by rfl) ⟨321143, by rfl⟩ : syracuseStep 1712765 = 642287) (by norm_num)
theorem B1286797 : Blo 1140634 1286797 := bbase (se 3 (by rfl) ⟨241274, by rfl⟩ : syracuseStep 1286797 = 482549) (by norm_num)
theorem B1221265 : Blo 1140634 1221265 := bbase (se 2 (by rfl) ⟨457974, by rfl⟩ : syracuseStep 1221265 = 915949) (by norm_num)
theorem B1712789 : Blo 1140634 1712789 := bbase (se 6 (by rfl) ⟨40143, by rfl⟩ : syracuseStep 1712789 = 80287) (by norm_num)
theorem B1712813 : Blo 1140634 1712813 := bbase (se 3 (by rfl) ⟨321152, by rfl⟩ : syracuseStep 1712813 = 642305) (by norm_num)
theorem B1286833 : Blo 1140634 1286833 := bbase (se 2 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 1286833 = 965125) (by norm_num)
theorem B2892469 : Blo 1140634 2892469 := bbase (se 5 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 2892469 = 271169) (by norm_num)
theorem B1712837 : Blo 1140634 1712837 := bbase (se 4 (by rfl) ⟨160578, by rfl⟩ : syracuseStep 1712837 = 321157) (by norm_num)
theorem B1286869 : Blo 1140634 1286869 := bbase (se 7 (by rfl) ⟨15080, by rfl⟩ : syracuseStep 1286869 = 30161) (by norm_num)
theorem B1221337 : Blo 1140634 1221337 := bbase (se 2 (by rfl) ⟨458001, by rfl⟩ : syracuseStep 1221337 = 916003) (by norm_num)
theorem B1712861 : Blo 1140634 1712861 := bbase (se 3 (by rfl) ⟨321161, by rfl⟩ : syracuseStep 1712861 = 642323) (by norm_num)
theorem B1712885 : Blo 1140634 1712885 := bbase (se 5 (by rfl) ⟨80291, by rfl⟩ : syracuseStep 1712885 = 160583) (by norm_num)
theorem B1286905 : Blo 1140634 1286905 := bbase (se 2 (by rfl) ⟨482589, by rfl⟩ : syracuseStep 1286905 = 965179) (by norm_num)
theorem B1712909 : Blo 1140634 1712909 := bbase (se 3 (by rfl) ⟨321170, by rfl⟩ : syracuseStep 1712909 = 642341) (by norm_num)
theorem B1286941 : Blo 1140634 1286941 := bbase (se 3 (by rfl) ⟨241301, by rfl⟩ : syracuseStep 1286941 = 482603) (by norm_num)
theorem B1712933 : Blo 1140634 1712933 := bbase (se 4 (by rfl) ⟨160587, by rfl⟩ : syracuseStep 1712933 = 321175) (by norm_num)
theorem B2892581 : Blo 1140634 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B1712957 : Blo 1140634 1712957 := bbase (se 3 (by rfl) ⟨321179, by rfl⟩ : syracuseStep 1712957 = 642359) (by norm_num)
theorem B1286977 : Blo 1140634 1286977 := bbase (se 2 (by rfl) ⟨482616, by rfl⟩ : syracuseStep 1286977 = 965233) (by norm_num)
theorem B3253061 : Blo 1140634 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B1712981 : Blo 1140634 1712981 := bbase (se 9 (by rfl) ⟨5018, by rfl⟩ : syracuseStep 1712981 = 10037) (by norm_num)
theorem B1287013 : Blo 1140634 1287013 := bbase (se 4 (by rfl) ⟨120657, by rfl⟩ : syracuseStep 1287013 = 241315) (by norm_num)
theorem B1713005 : Blo 1140634 1713005 := bbase (se 3 (by rfl) ⟨321188, by rfl⟩ : syracuseStep 1713005 = 642377) (by norm_num)
theorem B1713029 : Blo 1140634 1713029 := bbase (se 4 (by rfl) ⟨160596, by rfl⟩ : syracuseStep 1713029 = 321193) (by norm_num)
theorem B1287049 : Blo 1140634 1287049 := bbase (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) (by norm_num)
theorem B1221517 : Blo 1140634 1221517 := bbase (se 3 (by rfl) ⟨229034, by rfl⟩ : syracuseStep 1221517 = 458069) (by norm_num)
theorem B1713053 : Blo 1140634 1713053 := bbase (se 3 (by rfl) ⟨321197, by rfl⟩ : syracuseStep 1713053 = 642395) (by norm_num)
theorem B1287085 : Blo 1140634 1287085 := bbase (se 3 (by rfl) ⟨241328, by rfl⟩ : syracuseStep 1287085 = 482657) (by norm_num)
theorem B1713077 : Blo 1140634 1713077 := bbase (se 5 (by rfl) ⟨80300, by rfl⟩ : syracuseStep 1713077 = 160601) (by norm_num)
theorem B1713101 : Blo 1140634 1713101 := bbase (se 3 (by rfl) ⟨321206, by rfl⟩ : syracuseStep 1713101 = 642413) (by norm_num)
theorem B1287121 : Blo 1140634 1287121 := bbase (se 2 (by rfl) ⟨482670, by rfl⟩ : syracuseStep 1287121 = 965341) (by norm_num)
theorem B1713125 : Blo 1140634 1713125 := bbase (se 4 (by rfl) ⟨160605, by rfl⟩ : syracuseStep 1713125 = 321211) (by norm_num)
theorem B2892773 : Blo 1140634 2892773 := bbase (se 4 (by rfl) ⟨271197, by rfl⟩ : syracuseStep 2892773 = 542395) (by norm_num)
theorem B1287157 : Blo 1140634 1287157 := bbase (se 5 (by rfl) ⟨60335, by rfl⟩ : syracuseStep 1287157 = 120671) (by norm_num)
theorem B1713149 : Blo 1140634 1713149 := bbase (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) (by norm_num)
theorem B1713173 : Blo 1140634 1713173 := bbase (se 6 (by rfl) ⟨40152, by rfl⟩ : syracuseStep 1713173 = 80305) (by norm_num)
theorem B1287193 : Blo 1140634 1287193 := bbase (se 2 (by rfl) ⟨482697, by rfl⟩ : syracuseStep 1287193 = 965395) (by norm_num)
theorem B1713197 : Blo 1140634 1713197 := bbase (se 3 (by rfl) ⟨321224, by rfl⟩ : syracuseStep 1713197 = 642449) (by norm_num)
theorem B1287229 : Blo 1140634 1287229 := bbase (se 3 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 1287229 = 482711) (by norm_num)
theorem B1713221 : Blo 1140634 1713221 := bbase (se 4 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 1713221 = 321229) (by norm_num)
theorem B1713245 : Blo 1140634 1713245 := bbase (se 3 (by rfl) ⟨321233, by rfl⟩ : syracuseStep 1713245 = 642467) (by norm_num)
theorem B1287265 : Blo 1140634 1287265 := bbase (se 2 (by rfl) ⟨482724, by rfl⟩ : syracuseStep 1287265 = 965449) (by norm_num)
theorem B1713269 : Blo 1140634 1713269 := bbase (se 5 (by rfl) ⟨80309, by rfl⟩ : syracuseStep 1713269 = 160619) (by norm_num)
theorem B1287301 : Blo 1140634 1287301 := bbase (se 4 (by rfl) ⟨120684, by rfl⟩ : syracuseStep 1287301 = 241369) (by norm_num)
theorem B1713293 : Blo 1140634 1713293 := bbase (se 3 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 1713293 = 642485) (by norm_num)
theorem B4334741 : Blo 1140634 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B1713317 : Blo 1140634 1713317 := bbase (se 4 (by rfl) ⟨160623, by rfl⟩ : syracuseStep 1713317 = 321247) (by norm_num)
theorem B1287337 : Blo 1140634 1287337 := bbase (se 2 (by rfl) ⟨482751, by rfl⟩ : syracuseStep 1287337 = 965503) (by norm_num)
theorem B1713341 : Blo 1140634 1713341 := bbase (se 3 (by rfl) ⟨321251, by rfl⟩ : syracuseStep 1713341 = 642503) (by norm_num)
theorem B2172109 : Blo 1140634 2172109 := bbase (se 3 (by rfl) ⟨407270, by rfl⟩ : syracuseStep 2172109 = 814541) (by norm_num)
theorem B1287373 : Blo 1140634 1287373 := bbase (se 3 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 1287373 = 482765) (by norm_num)
theorem B1713365 : Blo 1140634 1713365 := bbase (se 7 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 1713365 = 40157) (by norm_num)
theorem B5481701 : Blo 1140634 5481701 := bbase (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) (by norm_num)
theorem B1713389 : Blo 1140634 1713389 := bbase (se 3 (by rfl) ⟨321260, by rfl⟩ : syracuseStep 1713389 = 642521) (by norm_num)
theorem B1287409 : Blo 1140634 1287409 := bbase (se 2 (by rfl) ⟨482778, by rfl⟩ : syracuseStep 1287409 = 965557) (by norm_num)
theorem B1713413 : Blo 1140634 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B1287445 : Blo 1140634 1287445 := bbase (se 6 (by rfl) ⟨30174, by rfl⟩ : syracuseStep 1287445 = 60349) (by norm_num)
theorem B1713437 : Blo 1140634 1713437 := bbase (se 3 (by rfl) ⟨321269, by rfl⟩ : syracuseStep 1713437 = 642539) (by norm_num)
theorem B1713461 : Blo 1140634 1713461 := bbase (se 5 (by rfl) ⟨80318, by rfl⟩ : syracuseStep 1713461 = 160637) (by norm_num)
theorem B1287481 : Blo 1140634 1287481 := bbase (se 2 (by rfl) ⟨482805, by rfl⟩ : syracuseStep 1287481 = 965611) (by norm_num)
theorem B2893117 : Blo 1140634 2893117 := bbase (se 3 (by rfl) ⟨542459, by rfl⟩ : syracuseStep 2893117 = 1084919) (by norm_num)
theorem B1221961 : Blo 1140634 1221961 := bbase (se 2 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 1221961 = 916471) (by norm_num)
theorem B1713485 : Blo 1140634 1713485 := bbase (se 3 (by rfl) ⟨321278, by rfl⟩ : syracuseStep 1713485 = 642557) (by norm_num)
theorem B2172253 : Blo 1140634 2172253 := bbase (se 3 (by rfl) ⟨407297, by rfl⟩ : syracuseStep 2172253 = 814595) (by norm_num)
theorem B1287517 : Blo 1140634 1287517 := bbase (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) (by norm_num)
theorem B1713509 : Blo 1140634 1713509 := bbase (se 4 (by rfl) ⟨160641, by rfl⟩ : syracuseStep 1713509 = 321283) (by norm_num)
theorem B5776757 : Blo 1140634 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B1713533 : Blo 1140634 1713533 := bbase (se 3 (by rfl) ⟨321287, by rfl⟩ : syracuseStep 1713533 = 642575) (by norm_num)
theorem B1287553 : Blo 1140634 1287553 := bbase (se 2 (by rfl) ⟨482832, by rfl⟩ : syracuseStep 1287553 = 965665) (by norm_num)
theorem B1713557 : Blo 1140634 1713557 := bbase (se 6 (by rfl) ⟨40161, by rfl⟩ : syracuseStep 1713557 = 80323) (by norm_num)
theorem B1287589 : Blo 1140634 1287589 := bbase (se 4 (by rfl) ⟨120711, by rfl⟩ : syracuseStep 1287589 = 241423) (by norm_num)
theorem B1713581 : Blo 1140634 1713581 := bbase (se 3 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 1713581 = 642593) (by norm_num)
theorem B2893229 : Blo 1140634 2893229 := bbase (se 3 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 2893229 = 1084961) (by norm_num)
theorem B4335029 : Blo 1140634 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1713605 : Blo 1140634 1713605 := bbase (se 4 (by rfl) ⟨160650, by rfl⟩ : syracuseStep 1713605 = 321301) (by norm_num)
theorem B1222085 : Blo 1140634 1222085 := bbase (se 4 (by rfl) ⟨114570, by rfl⟩ : syracuseStep 1222085 = 229141) (by norm_num)
theorem B1287625 : Blo 1140634 1287625 := bbase (se 2 (by rfl) ⟨482859, by rfl⟩ : syracuseStep 1287625 = 965719) (by norm_num)
theorem B1713629 : Blo 1140634 1713629 := bbase (se 3 (by rfl) ⟨321305, by rfl⟩ : syracuseStep 1713629 = 642611) (by norm_num)
theorem B3253733 : Blo 1140634 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B1287661 : Blo 1140634 1287661 := bbase (se 3 (by rfl) ⟨241436, by rfl⟩ : syracuseStep 1287661 = 482873) (by norm_num)
theorem B1713653 : Blo 1140634 1713653 := bbase (se 5 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 1713653 = 160655) (by norm_num)
theorem B2172413 : Blo 1140634 2172413 := bbase (se 3 (by rfl) ⟨407327, by rfl⟩ : syracuseStep 2172413 = 814655) (by norm_num)
theorem B1713677 : Blo 1140634 1713677 := bbase (se 3 (by rfl) ⟨321314, by rfl⟩ : syracuseStep 1713677 = 642629) (by norm_num)
theorem B1287697 : Blo 1140634 1287697 := bbase (se 2 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 1287697 = 965773) (by norm_num)
theorem B1713701 : Blo 1140634 1713701 := bbase (se 4 (by rfl) ⟨160659, by rfl⟩ : syracuseStep 1713701 = 321319) (by norm_num)
theorem B3712549 : Blo 1140634 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B1713725 : Blo 1140634 1713725 := bbase (se 3 (by rfl) ⟨321323, by rfl⟩ : syracuseStep 1713725 = 642647) (by norm_num)
theorem B1713749 : Blo 1140634 1713749 := bbase (se 8 (by rfl) ⟨10041, by rfl⟩ : syracuseStep 1713749 = 20083) (by norm_num)
theorem B1713773 : Blo 1140634 1713773 := bbase (se 3 (by rfl) ⟨321332, by rfl⟩ : syracuseStep 1713773 = 642665) (by norm_num)
theorem B2893421 : Blo 1140634 2893421 := bbase (se 3 (by rfl) ⟨542516, by rfl⟩ : syracuseStep 2893421 = 1085033) (by norm_num)
theorem B1713797 : Blo 1140634 1713797 := bbase (se 4 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 1713797 = 321337) (by norm_num)
theorem B2172557 : Blo 1140634 2172557 := bbase (se 3 (by rfl) ⟨407354, by rfl⟩ : syracuseStep 2172557 = 814709) (by norm_num)
theorem B6497941 : Blo 1140634 6497941 := bbase (se 6 (by rfl) ⟨152295, by rfl⟩ : syracuseStep 6497941 = 304591) (by norm_num)
theorem B1713821 : Blo 1140634 1713821 := bbase (se 3 (by rfl) ⟨321341, by rfl⟩ : syracuseStep 1713821 = 642683) (by norm_num)
theorem B1713845 : Blo 1140634 1713845 := bbase (se 5 (by rfl) ⟨80336, by rfl⟩ : syracuseStep 1713845 = 160673) (by norm_num)
theorem B1713869 : Blo 1140634 1713869 := bbase (se 3 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 1713869 = 642701) (by norm_num)
theorem B1713893 : Blo 1140634 1713893 := bbase (se 4 (by rfl) ⟨160677, by rfl⟩ : syracuseStep 1713893 = 321355) (by norm_num)
theorem B1713917 : Blo 1140634 1713917 := bbase (se 3 (by rfl) ⟨321359, by rfl⟩ : syracuseStep 1713917 = 642719) (by norm_num)
theorem B1713941 : Blo 1140634 1713941 := bbase (se 6 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 1713941 = 80341) (by norm_num)
theorem B1713965 : Blo 1140634 1713965 := bbase (se 3 (by rfl) ⟨321368, by rfl⟩ : syracuseStep 1713965 = 642737) (by norm_num)
theorem B1156933 : Blo 1140634 1156933 := bbase (se 4 (by rfl) ⟨108462, by rfl⟩ : syracuseStep 1156933 = 216925) (by norm_num)
theorem B1713989 : Blo 1140634 1713989 := bbase (se 4 (by rfl) ⟨160686, by rfl⟩ : syracuseStep 1713989 = 321373) (by norm_num)
theorem B1714013 : Blo 1140634 1714013 := bbase (se 3 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 1714013 = 642755) (by norm_num)
theorem B1714037 : Blo 1140634 1714037 := bbase (se 5 (by rfl) ⟨80345, by rfl⟩ : syracuseStep 1714037 = 160691) (by norm_num)
theorem B1714061 : Blo 1140634 1714061 := bbase (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) (by norm_num)
theorem B3254165 : Blo 1140634 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B1714085 : Blo 1140634 1714085 := bbase (se 4 (by rfl) ⟨160695, by rfl⟩ : syracuseStep 1714085 = 321391) (by norm_num)
theorem B2172845 : Blo 1140634 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B1714109 : Blo 1140634 1714109 := bbase (se 3 (by rfl) ⟨321395, by rfl⟩ : syracuseStep 1714109 = 642791) (by norm_num)
theorem B2893765 : Blo 1140634 2893765 := bbase (se 4 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 2893765 = 542581) (by norm_num)
theorem B1714133 : Blo 1140634 1714133 := bbase (se 7 (by rfl) ⟨20087, by rfl⟩ : syracuseStep 1714133 = 40175) (by norm_num)
theorem B1714157 : Blo 1140634 1714157 := bbase (se 3 (by rfl) ⟨321404, by rfl⟩ : syracuseStep 1714157 = 642809) (by norm_num)
theorem B1714181 : Blo 1140634 1714181 := bbase (se 4 (by rfl) ⟨160704, by rfl⟩ : syracuseStep 1714181 = 321409) (by norm_num)
theorem B1714205 : Blo 1140634 1714205 := bbase (se 3 (by rfl) ⟨321413, by rfl⟩ : syracuseStep 1714205 = 642827) (by norm_num)
theorem B1714229 : Blo 1140634 1714229 := bbase (se 5 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 1714229 = 160709) (by norm_num)
theorem B2893877 : Blo 1140634 2893877 := bbase (se 5 (by rfl) ⟨135650, by rfl⟩ : syracuseStep 2893877 = 271301) (by norm_num)
theorem B2172997 : Blo 1140634 2172997 := bbase (se 4 (by rfl) ⟨203718, by rfl⟩ : syracuseStep 2172997 = 407437) (by norm_num)
theorem B1714253 : Blo 1140634 1714253 := bbase (se 3 (by rfl) ⟨321422, by rfl⟩ : syracuseStep 1714253 = 642845) (by norm_num)
theorem B1714277 : Blo 1140634 1714277 := bbase (se 4 (by rfl) ⟨160713, by rfl⟩ : syracuseStep 1714277 = 321427) (by norm_num)
theorem B1714301 : Blo 1140634 1714301 := bbase (se 3 (by rfl) ⟨321431, by rfl⟩ : syracuseStep 1714301 = 642863) (by norm_num)
theorem B1714325 : Blo 1140634 1714325 := bbase (se 6 (by rfl) ⟨40179, by rfl⟩ : syracuseStep 1714325 = 80359) (by norm_num)
theorem B1714349 : Blo 1140634 1714349 := bbase (se 3 (by rfl) ⟨321440, by rfl⟩ : syracuseStep 1714349 = 642881) (by norm_num)
theorem B1714373 : Blo 1140634 1714373 := bbase (se 4 (by rfl) ⟨160722, by rfl⟩ : syracuseStep 1714373 = 321445) (by norm_num)
theorem B1714397 : Blo 1140634 1714397 := bbase (se 3 (by rfl) ⟨321449, by rfl⟩ : syracuseStep 1714397 = 642899) (by norm_num)
theorem B1714421 : Blo 1140634 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B2894069 : Blo 1140634 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1714445 : Blo 1140634 1714445 := bbase (se 3 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 1714445 = 642917) (by norm_num)
theorem B1714469 : Blo 1140634 1714469 := bbase (se 4 (by rfl) ⟨160731, by rfl⟩ : syracuseStep 1714469 = 321463) (by norm_num)
theorem B1714493 : Blo 1140634 1714493 := bbase (se 3 (by rfl) ⟨321467, by rfl⟩ : syracuseStep 1714493 = 642935) (by norm_num)
theorem B1714517 : Blo 1140634 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B2566493 : Blo 1140634 2566493 := bbase (se 3 (by rfl) ⟨481217, by rfl⟩ : syracuseStep 2566493 = 962435) (by norm_num)
theorem B1714541 : Blo 1140634 1714541 := bbase (se 3 (by rfl) ⟨321476, by rfl⟩ : syracuseStep 1714541 = 642953) (by norm_num)
theorem B1714565 : Blo 1140634 1714565 := bbase (se 4 (by rfl) ⟨160740, by rfl⟩ : syracuseStep 1714565 = 321481) (by norm_num)
theorem B1714589 : Blo 1140634 1714589 := bbase (se 3 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 1714589 = 642971) (by norm_num)
theorem B2566565 : Blo 1140634 2566565 := bbase (se 4 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 2566565 = 481231) (by norm_num)
theorem B1714613 : Blo 1140634 1714613 := bbase (se 5 (by rfl) ⟨80372, by rfl⟩ : syracuseStep 1714613 = 160745) (by norm_num)
theorem B1714637 : Blo 1140634 1714637 := bbase (se 3 (by rfl) ⟨321494, by rfl⟩ : syracuseStep 1714637 = 642989) (by norm_num)
theorem B1714661 : Blo 1140634 1714661 := bbase (se 4 (by rfl) ⟨160749, by rfl⟩ : syracuseStep 1714661 = 321499) (by norm_num)
theorem B2566637 : Blo 1140634 2566637 := bbase (se 3 (by rfl) ⟨481244, by rfl⟩ : syracuseStep 2566637 = 962489) (by norm_num)
theorem B1714685 : Blo 1140634 1714685 := bbase (se 3 (by rfl) ⟨321503, by rfl⟩ : syracuseStep 1714685 = 643007) (by norm_num)
theorem B1714709 : Blo 1140634 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B1714733 : Blo 1140634 1714733 := bbase (se 3 (by rfl) ⟨321512, by rfl⟩ : syracuseStep 1714733 = 643025) (by norm_num)
theorem B2566709 : Blo 1140634 2566709 := bbase (se 5 (by rfl) ⟨120314, by rfl⟩ : syracuseStep 2566709 = 240629) (by norm_num)
theorem B1714757 : Blo 1140634 1714757 := bbase (se 4 (by rfl) ⟨160758, by rfl⟩ : syracuseStep 1714757 = 321517) (by norm_num)
theorem B2894413 : Blo 1140634 2894413 := bbase (se 3 (by rfl) ⟨542702, by rfl⟩ : syracuseStep 2894413 = 1085405) (by norm_num)
theorem B10693205 : Blo 1140634 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B4336213 : Blo 1140634 4336213 := bbase (se 8 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 4336213 = 50815) (by norm_num)
theorem B1714781 : Blo 1140634 1714781 := bbase (se 3 (by rfl) ⟨321521, by rfl⟩ : syracuseStep 1714781 = 643043) (by norm_num)
theorem B1714805 : Blo 1140634 1714805 := bbase (se 5 (by rfl) ⟨80381, by rfl⟩ : syracuseStep 1714805 = 160763) (by norm_num)
theorem B2566781 : Blo 1140634 2566781 := bbase (se 3 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 2566781 = 962543) (by norm_num)
theorem B5778053 : Blo 1140634 5778053 := bbase (se 4 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 5778053 = 1083385) (by norm_num)
theorem B3254917 : Blo 1140634 3254917 := bbase (se 4 (by rfl) ⟨305148, by rfl⟩ : syracuseStep 3254917 = 610297) (by norm_num)
theorem B1714829 : Blo 1140634 1714829 := bbase (se 3 (by rfl) ⟨321530, by rfl⟩ : syracuseStep 1714829 = 643061) (by norm_num)
theorem B1714853 : Blo 1140634 1714853 := bbase (se 4 (by rfl) ⟨160767, by rfl⟩ : syracuseStep 1714853 = 321535) (by norm_num)
theorem B1157809 : Blo 1140634 1157809 := bbase (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) (by norm_num)
theorem B1714877 : Blo 1140634 1714877 := bbase (se 3 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 1714877 = 643079) (by norm_num)
theorem B2894525 : Blo 1140634 2894525 := bbase (se 3 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 2894525 = 1085447) (by norm_num)
theorem B2566853 : Blo 1140634 2566853 := bbase (se 4 (by rfl) ⟨240642, by rfl⟩ : syracuseStep 2566853 = 481285) (by norm_num)
theorem B1714901 : Blo 1140634 1714901 := bbase (se 7 (by rfl) ⟨20096, by rfl⟩ : syracuseStep 1714901 = 40193) (by norm_num)
theorem B1714925 : Blo 1140634 1714925 := bbase (se 3 (by rfl) ⟨321548, by rfl⟩ : syracuseStep 1714925 = 643097) (by norm_num)
theorem B1714949 : Blo 1140634 1714949 := bbase (se 4 (by rfl) ⟨160776, by rfl⟩ : syracuseStep 1714949 = 321553) (by norm_num)
theorem B2566925 : Blo 1140634 2566925 := bbase (se 3 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 2566925 = 962597) (by norm_num)
theorem B1714973 : Blo 1140634 1714973 := bbase (se 3 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 1714973 = 643115) (by norm_num)
theorem B1714997 : Blo 1140634 1714997 := bbase (se 5 (by rfl) ⟨80390, by rfl⟩ : syracuseStep 1714997 = 160781) (by norm_num)
theorem B1715021 : Blo 1140634 1715021 := bbase (se 3 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 1715021 = 643133) (by norm_num)
theorem B2566997 : Blo 1140634 2566997 := bbase (se 9 (by rfl) ⟨7520, by rfl⟩ : syracuseStep 2566997 = 15041) (by norm_num)
theorem B1715045 : Blo 1140634 1715045 := bbase (se 4 (by rfl) ⟨160785, by rfl⟩ : syracuseStep 1715045 = 321571) (by norm_num)
theorem B1715069 : Blo 1140634 1715069 := bbase (se 3 (by rfl) ⟨321575, by rfl⟩ : syracuseStep 1715069 = 643151) (by norm_num)
theorem B2894717 : Blo 1140634 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B4336517 : Blo 1140634 4336517 := bbase (se 4 (by rfl) ⟨406548, by rfl⟩ : syracuseStep 4336517 = 813097) (by norm_num)
theorem B1715093 : Blo 1140634 1715093 := bbase (se 6 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 1715093 = 80395) (by norm_num)
theorem B2567069 : Blo 1140634 2567069 := bbase (se 3 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 2567069 = 962651) (by norm_num)
theorem B1715117 : Blo 1140634 1715117 := bbase (se 3 (by rfl) ⟨321584, by rfl⟩ : syracuseStep 1715117 = 643169) (by norm_num)
theorem B1715141 : Blo 1140634 1715141 := bbase (se 4 (by rfl) ⟨160794, by rfl⟩ : syracuseStep 1715141 = 321589) (by norm_num)
theorem B1715165 : Blo 1140634 1715165 := bbase (se 3 (by rfl) ⟨321593, by rfl⟩ : syracuseStep 1715165 = 643187) (by norm_num)
theorem B2567141 : Blo 1140634 2567141 := bbase (se 4 (by rfl) ⟨240669, by rfl⟩ : syracuseStep 2567141 = 481339) (by norm_num)
theorem B1715189 : Blo 1140634 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B1715213 : Blo 1140634 1715213 := bbase (se 3 (by rfl) ⟨321602, by rfl⟩ : syracuseStep 1715213 = 643205) (by norm_num)
theorem B1715237 : Blo 1140634 1715237 := bbase (se 4 (by rfl) ⟨160803, by rfl⟩ : syracuseStep 1715237 = 321607) (by norm_num)
theorem B2567213 : Blo 1140634 2567213 := bbase (se 3 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 2567213 = 962705) (by norm_num)
theorem B1715261 : Blo 1140634 1715261 := bbase (se 3 (by rfl) ⟨321611, by rfl⟩ : syracuseStep 1715261 = 643223) (by norm_num)
theorem B1715285 : Blo 1140634 1715285 := bbase (se 8 (by rfl) ⟨10050, by rfl⟩ : syracuseStep 1715285 = 20101) (by norm_num)
theorem B2174045 : Blo 1140634 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B1715309 : Blo 1140634 1715309 := bbase (se 3 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 1715309 = 643241) (by norm_num)
theorem B2567285 : Blo 1140634 2567285 := bbase (se 5 (by rfl) ⟨120341, by rfl⟩ : syracuseStep 2567285 = 240683) (by norm_num)
theorem B1715333 : Blo 1140634 1715333 := bbase (se 4 (by rfl) ⟨160812, by rfl⟩ : syracuseStep 1715333 = 321625) (by norm_num)
theorem B1715357 : Blo 1140634 1715357 := bbase (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) (by norm_num)
theorem B1715381 : Blo 1140634 1715381 := bbase (se 5 (by rfl) ⟨80408, by rfl⟩ : syracuseStep 1715381 = 160817) (by norm_num)
theorem B2567357 : Blo 1140634 2567357 := bbase (se 3 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 2567357 = 962759) (by norm_num)
theorem B1715405 : Blo 1140634 1715405 := bbase (se 3 (by rfl) ⟨321638, by rfl⟩ : syracuseStep 1715405 = 643277) (by norm_num)
theorem B2895061 : Blo 1140634 2895061 := bbase (se 7 (by rfl) ⟨33926, by rfl⟩ : syracuseStep 2895061 = 67853) (by norm_num)
theorem B1715429 : Blo 1140634 1715429 := bbase (se 4 (by rfl) ⟨160821, by rfl⟩ : syracuseStep 1715429 = 321643) (by norm_num)
theorem B1715453 : Blo 1140634 1715453 := bbase (se 3 (by rfl) ⟨321647, by rfl⟩ : syracuseStep 1715453 = 643295) (by norm_num)
theorem B2567429 : Blo 1140634 2567429 := bbase (se 4 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 2567429 = 481393) (by norm_num)
theorem B1715477 : Blo 1140634 1715477 := bbase (se 6 (by rfl) ⟨40206, by rfl⟩ : syracuseStep 1715477 = 80413) (by norm_num)
theorem B1715501 : Blo 1140634 1715501 := bbase (se 3 (by rfl) ⟨321656, by rfl⟩ : syracuseStep 1715501 = 643313) (by norm_num)
theorem B2436421 : Blo 1140634 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B1715525 : Blo 1140634 1715525 := bbase (se 4 (by rfl) ⟨160830, by rfl⟩ : syracuseStep 1715525 = 321661) (by norm_num)
theorem B2895173 : Blo 1140634 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B2567501 : Blo 1140634 2567501 := bbase (se 3 (by rfl) ⟨481406, by rfl⟩ : syracuseStep 2567501 = 962813) (by norm_num)
theorem B1715549 : Blo 1140634 1715549 := bbase (se 3 (by rfl) ⟨321665, by rfl⟩ : syracuseStep 1715549 = 643331) (by norm_num)
theorem B1715573 : Blo 1140634 1715573 := bbase (se 5 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 1715573 = 160835) (by norm_num)
theorem B1715597 : Blo 1140634 1715597 := bbase (se 3 (by rfl) ⟨321674, by rfl⟩ : syracuseStep 1715597 = 643349) (by norm_num)
theorem B2567573 : Blo 1140634 2567573 := bbase (se 6 (by rfl) ⟨60177, by rfl⟩ : syracuseStep 2567573 = 120355) (by norm_num)
theorem B1715621 : Blo 1140634 1715621 := bbase (se 4 (by rfl) ⟨160839, by rfl⟩ : syracuseStep 1715621 = 321679) (by norm_num)
theorem B1715645 : Blo 1140634 1715645 := bbase (se 3 (by rfl) ⟨321683, by rfl⟩ : syracuseStep 1715645 = 643367) (by norm_num)
theorem B1715669 : Blo 1140634 1715669 := bbase (se 7 (by rfl) ⟨20105, by rfl⟩ : syracuseStep 1715669 = 40211) (by norm_num)
theorem B2567645 : Blo 1140634 2567645 := bbase (se 3 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 2567645 = 962867) (by norm_num)
theorem B1715693 : Blo 1140634 1715693 := bbase (se 3 (by rfl) ⟨321692, by rfl⟩ : syracuseStep 1715693 = 643385) (by norm_num)
theorem B1715717 : Blo 1140634 1715717 := bbase (se 4 (by rfl) ⟨160848, by rfl⟩ : syracuseStep 1715717 = 321697) (by norm_num)
theorem B2895365 : Blo 1140634 2895365 := bbase (se 4 (by rfl) ⟨271440, by rfl⟩ : syracuseStep 2895365 = 542881) (by norm_num)
theorem B1715741 : Blo 1140634 1715741 := bbase (se 3 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 1715741 = 643403) (by norm_num)
theorem B2567717 : Blo 1140634 2567717 := bbase (se 4 (by rfl) ⟨240723, by rfl⟩ : syracuseStep 2567717 = 481447) (by norm_num)
theorem B1715765 : Blo 1140634 1715765 := bbase (se 5 (by rfl) ⟨80426, by rfl⟩ : syracuseStep 1715765 = 160853) (by norm_num)
theorem B2010685 : Blo 1140634 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B2928197 : Blo 1140634 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B1715789 : Blo 1140634 1715789 := bbase (se 3 (by rfl) ⟨321710, by rfl⟩ : syracuseStep 1715789 = 643421) (by norm_num)
theorem B6499925 : Blo 1140634 6499925 := bbase (se 8 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 6499925 = 76171) (by norm_num)
theorem B1715813 : Blo 1140634 1715813 := bbase (se 4 (by rfl) ⟨160857, by rfl⟩ : syracuseStep 1715813 = 321715) (by norm_num)
theorem B2567789 : Blo 1140634 2567789 := bbase (se 3 (by rfl) ⟨481460, by rfl⟩ : syracuseStep 2567789 = 962921) (by norm_num)
theorem B1715837 : Blo 1140634 1715837 := bbase (se 3 (by rfl) ⟨321719, by rfl⟩ : syracuseStep 1715837 = 643439) (by norm_num)
theorem B1715861 : Blo 1140634 1715861 := bbase (se 6 (by rfl) ⟨40215, by rfl⟩ : syracuseStep 1715861 = 80431) (by norm_num)
theorem B1715885 : Blo 1140634 1715885 := bbase (se 3 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 1715885 = 643457) (by norm_num)
theorem B2567861 : Blo 1140634 2567861 := bbase (se 5 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 2567861 = 240737) (by norm_num)
theorem B2436797 : Blo 1140634 2436797 := bbase (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) (by norm_num)
theorem B1715909 : Blo 1140634 1715909 := bbase (se 4 (by rfl) ⟨160866, by rfl⟩ : syracuseStep 1715909 = 321733) (by norm_num)
theorem B1715933 : Blo 1140634 1715933 := bbase (se 3 (by rfl) ⟨321737, by rfl⟩ : syracuseStep 1715933 = 643475) (by norm_num)
theorem B1715957 : Blo 1140634 1715957 := bbase (se 5 (by rfl) ⟨80435, by rfl⟩ : syracuseStep 1715957 = 160871) (by norm_num)
theorem B2567933 : Blo 1140634 2567933 := bbase (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) (by norm_num)
theorem B1289981 : Blo 1140634 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1715981 : Blo 1140634 1715981 := bbase (se 3 (by rfl) ⟨321746, by rfl⟩ : syracuseStep 1715981 = 643493) (by norm_num)
theorem B1716005 : Blo 1140634 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B2928437 : Blo 1140634 2928437 := bbase (se 5 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 2928437 = 274541) (by norm_num)
theorem B1716029 : Blo 1140634 1716029 := bbase (se 3 (by rfl) ⟨321755, by rfl⟩ : syracuseStep 1716029 = 643511) (by norm_num)
theorem B2568005 : Blo 1140634 2568005 := bbase (se 4 (by rfl) ⟨240750, by rfl⟩ : syracuseStep 2568005 = 481501) (by norm_num)
theorem B1716053 : Blo 1140634 1716053 := bbase (se 9 (by rfl) ⟨5027, by rfl⟩ : syracuseStep 1716053 = 10055) (by norm_num)
theorem B2895709 : Blo 1140634 2895709 := bbase (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) (by norm_num)
theorem B1716077 : Blo 1140634 1716077 := bbase (se 3 (by rfl) ⟨321764, by rfl⟩ : syracuseStep 1716077 = 643529) (by norm_num)
theorem B1486717 : Blo 1140634 1486717 := bbase (se 3 (by rfl) ⟨278759, by rfl⟩ : syracuseStep 1486717 = 557519) (by norm_num)
theorem B1716101 : Blo 1140634 1716101 := bbase (se 4 (by rfl) ⟨160884, by rfl⟩ : syracuseStep 1716101 = 321769) (by norm_num)
theorem B2568077 : Blo 1140634 2568077 := bbase (se 3 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 2568077 = 963029) (by norm_num)
theorem B1159057 : Blo 1140634 1159057 := bbase (se 2 (by rfl) ⟨434646, by rfl⟩ : syracuseStep 1159057 = 869293) (by norm_num)
theorem B5779349 : Blo 1140634 5779349 := bbase (se 6 (by rfl) ⟨135453, by rfl⟩ : syracuseStep 5779349 = 270907) (by norm_num)
theorem B1716125 : Blo 1140634 1716125 := bbase (se 3 (by rfl) ⟨321773, by rfl⟩ : syracuseStep 1716125 = 643547) (by norm_num)
theorem B1716149 : Blo 1140634 1716149 := bbase (se 5 (by rfl) ⟨80444, by rfl⟩ : syracuseStep 1716149 = 160889) (by norm_num)
theorem B2895821 : Blo 1140634 2895821 := bbase (se 3 (by rfl) ⟨542966, by rfl⟩ : syracuseStep 2895821 = 1085933) (by norm_num)
theorem B1716173 : Blo 1140634 1716173 := bbase (se 3 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 1716173 = 643565) (by norm_num)
theorem B2568149 : Blo 1140634 2568149 := bbase (se 7 (by rfl) ⟨30095, by rfl⟩ : syracuseStep 2568149 = 60191) (by norm_num)
theorem B1716197 : Blo 1140634 1716197 := bbase (se 4 (by rfl) ⟨160893, by rfl⟩ : syracuseStep 1716197 = 321787) (by norm_num)
theorem B1716221 : Blo 1140634 1716221 := bbase (se 3 (by rfl) ⟨321791, by rfl⟩ : syracuseStep 1716221 = 643583) (by norm_num)
theorem B1716245 : Blo 1140634 1716245 := bbase (se 6 (by rfl) ⟨40224, by rfl⟩ : syracuseStep 1716245 = 80449) (by norm_num)
theorem B2568221 : Blo 1140634 2568221 := bbase (se 3 (by rfl) ⟨481541, by rfl⟩ : syracuseStep 2568221 = 963083) (by norm_num)
theorem B1716269 : Blo 1140634 1716269 := bbase (se 3 (by rfl) ⟨321800, by rfl⟩ : syracuseStep 1716269 = 643601) (by norm_num)
theorem B1716293 : Blo 1140634 1716293 := bbase (se 4 (by rfl) ⟨160902, by rfl⟩ : syracuseStep 1716293 = 321805) (by norm_num)
theorem B3518549 : Blo 1140634 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1716317 : Blo 1140634 1716317 := bbase (se 3 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 1716317 = 643619) (by norm_num)
theorem B2568293 : Blo 1140634 2568293 := bbase (se 4 (by rfl) ⟨240777, by rfl⟩ : syracuseStep 2568293 = 481555) (by norm_num)
theorem B1716341 : Blo 1140634 1716341 := bbase (se 5 (by rfl) ⟨80453, by rfl⟩ : syracuseStep 1716341 = 160907) (by norm_num)
theorem B2896013 : Blo 1140634 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B1716365 : Blo 1140634 1716365 := bbase (se 3 (by rfl) ⟨321818, by rfl⟩ : syracuseStep 1716365 = 643637) (by norm_num)
theorem B1716389 : Blo 1140634 1716389 := bbase (se 4 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 1716389 = 321823) (by norm_num)
theorem B2568365 : Blo 1140634 2568365 := bbase (se 3 (by rfl) ⟨481568, by rfl⟩ : syracuseStep 2568365 = 963137) (by norm_num)
theorem B1716413 : Blo 1140634 1716413 := bbase (se 3 (by rfl) ⟨321827, by rfl⟩ : syracuseStep 1716413 = 643655) (by norm_num)
theorem B13021397 : Blo 1140634 13021397 := bbase (se 7 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 13021397 = 305189) (by norm_num)
theorem B1716437 : Blo 1140634 1716437 := bbase (se 7 (by rfl) ⟨20114, by rfl⟩ : syracuseStep 1716437 = 40229) (by norm_num)
theorem B1716461 : Blo 1140634 1716461 := bbase (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) (by norm_num)
theorem B2568437 : Blo 1140634 2568437 := bbase (se 5 (by rfl) ⟨120395, by rfl⟩ : syracuseStep 2568437 = 240791) (by norm_num)
theorem B1716485 : Blo 1140634 1716485 := bbase (se 4 (by rfl) ⟨160920, by rfl⟩ : syracuseStep 1716485 = 321841) (by norm_num)
theorem B1716509 : Blo 1140634 1716509 := bbase (se 3 (by rfl) ⟨321845, by rfl⟩ : syracuseStep 1716509 = 643691) (by norm_num)
theorem B1716533 : Blo 1140634 1716533 := bbase (se 5 (by rfl) ⟨80462, by rfl⟩ : syracuseStep 1716533 = 160925) (by norm_num)
theorem B2568509 : Blo 1140634 2568509 := bbase (se 3 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 2568509 = 963191) (by norm_num)
theorem B1716557 : Blo 1140634 1716557 := bbase (se 3 (by rfl) ⟨321854, by rfl⟩ : syracuseStep 1716557 = 643709) (by norm_num)
theorem B9744725 : Blo 1140634 9744725 := bbase (se 10 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 9744725 = 28549) (by norm_num)
theorem B1716581 : Blo 1140634 1716581 := bbase (se 4 (by rfl) ⟨160929, by rfl⟩ : syracuseStep 1716581 = 321859) (by norm_num)
theorem B1716605 : Blo 1140634 1716605 := bbase (se 3 (by rfl) ⟨321863, by rfl⟩ : syracuseStep 1716605 = 643727) (by norm_num)
theorem B2568581 : Blo 1140634 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B1716629 : Blo 1140634 1716629 := bbase (se 6 (by rfl) ⟨40233, by rfl⟩ : syracuseStep 1716629 = 80467) (by norm_num)
theorem B1716653 : Blo 1140634 1716653 := bbase (se 3 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 1716653 = 643745) (by norm_num)
theorem B1716677 : Blo 1140634 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B2568653 : Blo 1140634 2568653 := bbase (se 3 (by rfl) ⟨481622, by rfl⟩ : syracuseStep 2568653 = 963245) (by norm_num)
theorem B1716701 : Blo 1140634 1716701 := bbase (se 3 (by rfl) ⟨321881, by rfl⟩ : syracuseStep 1716701 = 643763) (by norm_num)
theorem B2896357 : Blo 1140634 2896357 := bbase (se 4 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 2896357 = 543067) (by norm_num)
theorem B1716725 : Blo 1140634 1716725 := bbase (se 5 (by rfl) ⟨80471, by rfl⟩ : syracuseStep 1716725 = 160943) (by norm_num)
theorem B1716749 : Blo 1140634 1716749 := bbase (se 3 (by rfl) ⟨321890, by rfl⟩ : syracuseStep 1716749 = 643781) (by norm_num)
theorem B2568725 : Blo 1140634 2568725 := bbase (se 6 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 2568725 = 120409) (by norm_num)
theorem B1716773 : Blo 1140634 1716773 := bbase (se 4 (by rfl) ⟨160947, by rfl⟩ : syracuseStep 1716773 = 321895) (by norm_num)
theorem B1716797 : Blo 1140634 1716797 := bbase (se 3 (by rfl) ⟨321899, by rfl⟩ : syracuseStep 1716797 = 643799) (by norm_num)
theorem B2896469 : Blo 1140634 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B1716821 : Blo 1140634 1716821 := bbase (se 8 (by rfl) ⟨10059, by rfl⟩ : syracuseStep 1716821 = 20119) (by norm_num)
theorem B2568797 : Blo 1140634 2568797 := bbase (se 3 (by rfl) ⟨481649, by rfl⟩ : syracuseStep 2568797 = 963299) (by norm_num)
theorem B1716845 : Blo 1140634 1716845 := bbase (se 3 (by rfl) ⟨321908, by rfl⟩ : syracuseStep 1716845 = 643817) (by norm_num)
theorem B1716869 : Blo 1140634 1716869 := bbase (se 4 (by rfl) ⟨160956, by rfl⟩ : syracuseStep 1716869 = 321913) (by norm_num)
theorem B1716893 : Blo 1140634 1716893 := bbase (se 3 (by rfl) ⟨321917, by rfl⟩ : syracuseStep 1716893 = 643835) (by norm_num)
theorem B2568869 : Blo 1140634 2568869 := bbase (se 4 (by rfl) ⟨240831, by rfl⟩ : syracuseStep 2568869 = 481663) (by norm_num)
theorem B1716917 : Blo 1140634 1716917 := bbase (se 5 (by rfl) ⟨80480, by rfl⟩ : syracuseStep 1716917 = 160961) (by norm_num)
theorem B1716941 : Blo 1140634 1716941 := bbase (se 3 (by rfl) ⟨321926, by rfl⟩ : syracuseStep 1716941 = 643853) (by norm_num)
theorem B2568941 : Blo 1140634 2568941 := bbase (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) (by norm_num)
theorem B2896661 : Blo 1140634 2896661 := bbase (se 6 (by rfl) ⟨67890, by rfl⟩ : syracuseStep 2896661 = 135781) (by norm_num)
theorem B9777941 : Blo 1140634 9777941 := bbase (se 6 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 9777941 = 458341) (by norm_num)
theorem B2569013 : Blo 1140634 2569013 := bbase (se 5 (by rfl) ⟨120422, by rfl⟩ : syracuseStep 2569013 = 240845) (by norm_num)
theorem B2569085 : Blo 1140634 2569085 := bbase (se 3 (by rfl) ⟨481703, by rfl⟩ : syracuseStep 2569085 = 963407) (by norm_num)
theorem B2569157 : Blo 1140634 2569157 := bbase (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) (by norm_num)
theorem B4338629 : Blo 1140634 4338629 := bbase (se 4 (by rfl) ⟨406746, by rfl⟩ : syracuseStep 4338629 = 813493) (by norm_num)
theorem B2569229 : Blo 1140634 2569229 := bbase (se 3 (by rfl) ⟨481730, by rfl⟩ : syracuseStep 2569229 = 963461) (by norm_num)
theorem B2864189 : Blo 1140634 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B2569301 : Blo 1140634 2569301 := bbase (se 8 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 2569301 = 30109) (by norm_num)
theorem B2897005 : Blo 1140634 2897005 := bbase (se 3 (by rfl) ⟨543188, by rfl⟩ : syracuseStep 2897005 = 1086377) (by norm_num)
theorem B2569373 : Blo 1140634 2569373 := bbase (se 3 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 2569373 = 963515) (by norm_num)
theorem B5780645 : Blo 1140634 5780645 := bbase (se 4 (by rfl) ⟨541935, by rfl⟩ : syracuseStep 5780645 = 1083871) (by norm_num)
theorem B2897117 : Blo 1140634 2897117 := bbase (se 3 (by rfl) ⟨543209, by rfl⟩ : syracuseStep 2897117 = 1086419) (by norm_num)
theorem B2569445 : Blo 1140634 2569445 := bbase (se 4 (by rfl) ⟨240885, by rfl⟩ : syracuseStep 2569445 = 481771) (by norm_num)
theorem B4338917 : Blo 1140634 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B2438437 : Blo 1140634 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B2569517 : Blo 1140634 2569517 := bbase (se 3 (by rfl) ⟨481784, by rfl⟩ : syracuseStep 2569517 = 963569) (by norm_num)
theorem B4633957 : Blo 1140634 4633957 := bbase (se 4 (by rfl) ⟨434433, by rfl⟩ : syracuseStep 4633957 = 868867) (by norm_num)
theorem B2569589 : Blo 1140634 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B4404613 : Blo 1140634 4404613 := bbase (se 4 (by rfl) ⟨412932, by rfl⟩ : syracuseStep 4404613 = 825865) (by norm_num)
theorem B2897309 : Blo 1140634 2897309 := bbase (se 3 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 2897309 = 1086491) (by norm_num)
theorem B2602405 : Blo 1140634 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B3257765 : Blo 1140634 3257765 := bbase (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) (by norm_num)
theorem B2569661 : Blo 1140634 2569661 := bbase (se 3 (by rfl) ⟨481811, by rfl⟩ : syracuseStep 2569661 = 963623) (by norm_num)
theorem B2471381 : Blo 1140634 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B2569733 : Blo 1140634 2569733 := bbase (se 4 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 2569733 = 481825) (by norm_num)
theorem B2569805 : Blo 1140634 2569805 := bbase (se 3 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 2569805 = 963677) (by norm_num)
theorem B1390189 : Blo 1140634 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B2569877 : Blo 1140634 2569877 := bbase (se 6 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 2569877 = 120463) (by norm_num)
theorem B2569949 : Blo 1140634 2569949 := bbase (se 3 (by rfl) ⟨481865, by rfl⟩ : syracuseStep 2569949 = 963731) (by norm_num)
theorem B6502133 : Blo 1140634 6502133 := bbase (se 5 (by rfl) ⟨304787, by rfl⟩ : syracuseStep 6502133 = 609575) (by norm_num)
theorem B2570021 : Blo 1140634 2570021 := bbase (se 4 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 2570021 = 481879) (by norm_num)
theorem B2570093 : Blo 1140634 2570093 := bbase (se 3 (by rfl) ⟨481892, by rfl⟩ : syracuseStep 2570093 = 963785) (by norm_num)
theorem B2570165 : Blo 1140634 2570165 := bbase (se 5 (by rfl) ⟨120476, by rfl⟩ : syracuseStep 2570165 = 240953) (by norm_num)
theorem B2570237 : Blo 1140634 2570237 := bbase (se 3 (by rfl) ⟨481919, by rfl⟩ : syracuseStep 2570237 = 963839) (by norm_num)
theorem B2570309 : Blo 1140634 2570309 := bbase (se 4 (by rfl) ⟨240966, by rfl⟩ : syracuseStep 2570309 = 481933) (by norm_num)
theorem B2570381 : Blo 1140634 2570381 := bbase (se 3 (by rfl) ⟨481946, by rfl⟩ : syracuseStep 2570381 = 963893) (by norm_num)
theorem B2439325 : Blo 1140634 2439325 := bbase (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) (by norm_num)
theorem B5486773 : Blo 1140634 5486773 := bbase (se 5 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 5486773 = 514385) (by norm_num)
theorem B2570453 : Blo 1140634 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B2570525 : Blo 1140634 2570525 := bbase (se 3 (by rfl) ⟨481973, by rfl⟩ : syracuseStep 2570525 = 963947) (by norm_num)
theorem B2570597 : Blo 1140634 2570597 := bbase (se 4 (by rfl) ⟨240993, by rfl⟩ : syracuseStep 2570597 = 481987) (by norm_num)
theorem B4340101 : Blo 1140634 4340101 := bbase (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) (by norm_num)
theorem B2570669 : Blo 1140634 2570669 := bbase (se 3 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 2570669 = 964001) (by norm_num)
theorem B5781941 : Blo 1140634 5781941 := bbase (se 5 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 5781941 = 542057) (by norm_num)
theorem B1391033 : Blo 1140634 1391033 := bbase (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) (by norm_num)
theorem B2570741 : Blo 1140634 2570741 := bbase (se 5 (by rfl) ⟨120503, by rfl⟩ : syracuseStep 2570741 = 241007) (by norm_num)
theorem B2603573 : Blo 1140634 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B2570813 : Blo 1140634 2570813 := bbase (se 3 (by rfl) ⟨482027, by rfl⟩ : syracuseStep 2570813 = 964055) (by norm_num)
theorem B3258949 : Blo 1140634 3258949 := bbase (se 4 (by rfl) ⟨305526, by rfl⟩ : syracuseStep 3258949 = 611053) (by norm_num)
theorem B2570885 : Blo 1140634 2570885 := bbase (se 4 (by rfl) ⟨241020, by rfl⟩ : syracuseStep 2570885 = 482041) (by norm_num)
theorem B2439821 : Blo 1140634 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B4340405 : Blo 1140634 4340405 := bbase (se 5 (by rfl) ⟨203456, by rfl⟩ : syracuseStep 4340405 = 406913) (by norm_num)
theorem B2570957 : Blo 1140634 2570957 := bbase (se 3 (by rfl) ⟨482054, by rfl⟩ : syracuseStep 2570957 = 964109) (by norm_num)
theorem B10992341 : Blo 1140634 10992341 := bbase (se 7 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 10992341 = 257633) (by norm_num)
theorem B3259109 : Blo 1140634 3259109 := bbase (se 4 (by rfl) ⟨305541, by rfl⟩ : syracuseStep 3259109 = 611083) (by norm_num)
theorem B2571029 : Blo 1140634 2571029 := bbase (se 6 (by rfl) ⟨60258, by rfl⟩ : syracuseStep 2571029 = 120517) (by norm_num)
theorem B2571101 : Blo 1140634 2571101 := bbase (se 3 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 2571101 = 964163) (by norm_num)
theorem B2571173 : Blo 1140634 2571173 := bbase (se 4 (by rfl) ⟨241047, by rfl⟩ : syracuseStep 2571173 = 482095) (by norm_num)
theorem B3259349 : Blo 1140634 3259349 := bbase (se 7 (by rfl) ⟨38195, by rfl⟩ : syracuseStep 3259349 = 76391) (by norm_num)
theorem B2571245 : Blo 1140634 2571245 := bbase (se 3 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 2571245 = 964217) (by norm_num)
theorem B3128341 : Blo 1140634 3128341 := bbase (se 6 (by rfl) ⟨73320, by rfl⟩ : syracuseStep 3128341 = 146641) (by norm_num)
theorem B2571317 : Blo 1140634 2571317 := bbase (se 5 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 2571317 = 241061) (by norm_num)
theorem B2571389 : Blo 1140634 2571389 := bbase (se 3 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 2571389 = 964271) (by norm_num)
theorem B3914885 : Blo 1140634 3914885 := bbase (se 4 (by rfl) ⟨367020, by rfl⟩ : syracuseStep 3914885 = 734041) (by norm_num)
theorem B2571461 : Blo 1140634 2571461 := bbase (se 4 (by rfl) ⟨241074, by rfl⟩ : syracuseStep 2571461 = 482149) (by norm_num)
theorem B9747701 : Blo 1140634 9747701 := bbase (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) (by norm_num)
theorem B2571533 : Blo 1140634 2571533 := bbase (se 3 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 2571533 = 964325) (by norm_num)
theorem B2571605 : Blo 1140634 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B2571677 : Blo 1140634 2571677 := bbase (se 3 (by rfl) ⟨482189, by rfl⟩ : syracuseStep 2571677 = 964379) (by norm_num)
theorem B2571749 : Blo 1140634 2571749 := bbase (se 4 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 2571749 = 482203) (by norm_num)
theorem B2440685 : Blo 1140634 2440685 := bbase (se 3 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 2440685 = 915257) (by norm_num)
theorem B2932213 : Blo 1140634 2932213 := bbase (se 5 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 2932213 = 274895) (by norm_num)
theorem B2604557 : Blo 1140634 2604557 := bbase (se 3 (by rfl) ⟨488354, by rfl⟩ : syracuseStep 2604557 = 976709) (by norm_num)
theorem B2571821 : Blo 1140634 2571821 := bbase (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) (by norm_num)
theorem B2637413 : Blo 1140634 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B2571893 : Blo 1140634 2571893 := bbase (se 5 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 2571893 = 241115) (by norm_num)
theorem B2440829 : Blo 1140634 2440829 := bbase (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) (by norm_num)
theorem B2571965 : Blo 1140634 2571965 := bbase (se 3 (by rfl) ⟨482243, by rfl⟩ : syracuseStep 2571965 = 964487) (by norm_num)
theorem B5783237 : Blo 1140634 5783237 := bbase (se 4 (by rfl) ⟨542178, by rfl⟩ : syracuseStep 5783237 = 1084357) (by norm_num)
theorem B8666837 : Blo 1140634 8666837 := bbase (se 7 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 8666837 = 203129) (by norm_num)
theorem B6602485 : Blo 1140634 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B2572037 : Blo 1140634 2572037 := bbase (se 4 (by rfl) ⟨241128, by rfl⟩ : syracuseStep 2572037 = 482257) (by norm_num)
theorem B6176533 : Blo 1140634 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B3850037 : Blo 1140634 3850037 := bbase (se 5 (by rfl) ⟨180470, by rfl⟩ : syracuseStep 3850037 = 360941) (by norm_num)
theorem B2473805 : Blo 1140634 2473805 := bbase (se 3 (by rfl) ⟨463838, by rfl⟩ : syracuseStep 2473805 = 927677) (by norm_num)
theorem B2572109 : Blo 1140634 2572109 := bbase (se 3 (by rfl) ⟨482270, by rfl⟩ : syracuseStep 2572109 = 964541) (by norm_num)
theorem B2572181 : Blo 1140634 2572181 := bbase (se 6 (by rfl) ⟨60285, by rfl⟩ : syracuseStep 2572181 = 120571) (by norm_num)
theorem B2572253 : Blo 1140634 2572253 := bbase (se 3 (by rfl) ⟨482297, by rfl⟩ : syracuseStep 2572253 = 964595) (by norm_num)
theorem B2572325 : Blo 1140634 2572325 := bbase (se 4 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 2572325 = 482311) (by norm_num)
theorem B2572397 : Blo 1140634 2572397 := bbase (se 3 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 2572397 = 964649) (by norm_num)
theorem B2572469 : Blo 1140634 2572469 := bbase (se 5 (by rfl) ⟨120584, by rfl⟩ : syracuseStep 2572469 = 241169) (by norm_num)
theorem B3850469 : Blo 1140634 3850469 := bbase (se 4 (by rfl) ⟨360981, by rfl⟩ : syracuseStep 3850469 = 721963) (by norm_num)
theorem B2572541 : Blo 1140634 2572541 := bbase (se 3 (by rfl) ⟨482351, by rfl⟩ : syracuseStep 2572541 = 964703) (by norm_num)
theorem B2572613 : Blo 1140634 2572613 := bbase (se 4 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 2572613 = 482365) (by norm_num)
theorem B2441573 : Blo 1140634 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B2572685 : Blo 1140634 2572685 := bbase (se 3 (by rfl) ⟨482378, by rfl⟩ : syracuseStep 2572685 = 964757) (by norm_num)
theorem B2572757 : Blo 1140634 2572757 := bbase (se 7 (by rfl) ⟨30149, by rfl⟩ : syracuseStep 2572757 = 60299) (by norm_num)
theorem B3523061 : Blo 1140634 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B7324181 : Blo 1140634 7324181 := bbase (se 6 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 7324181 = 343321) (by norm_num)
theorem B2572829 : Blo 1140634 2572829 := bbase (se 3 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 2572829 = 964811) (by norm_num)
theorem B3654197 : Blo 1140634 3654197 := bbase (se 5 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 3654197 = 342581) (by norm_num)
theorem B2572901 : Blo 1140634 2572901 := bbase (se 4 (by rfl) ⟨241209, by rfl⟩ : syracuseStep 2572901 = 482419) (by norm_num)
theorem B2605709 : Blo 1140634 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B3850901 : Blo 1140634 3850901 := bbase (se 6 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 3850901 = 180511) (by norm_num)
theorem B2572973 : Blo 1140634 2572973 := bbase (se 3 (by rfl) ⟨482432, by rfl⟩ : syracuseStep 2572973 = 964865) (by norm_num)
theorem B2573045 : Blo 1140634 2573045 := bbase (se 5 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 2573045 = 241223) (by norm_num)
theorem B4342517 : Blo 1140634 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B2573117 : Blo 1140634 2573117 := bbase (se 3 (by rfl) ⟨482459, by rfl⟩ : syracuseStep 2573117 = 964919) (by norm_num)
theorem B2573189 : Blo 1140634 2573189 := bbase (se 4 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 2573189 = 482473) (by norm_num)
theorem B2573261 : Blo 1140634 2573261 := bbase (se 3 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 2573261 = 964973) (by norm_num)
theorem B5784533 : Blo 1140634 5784533 := bbase (se 7 (by rfl) ⟨67787, by rfl⟩ : syracuseStep 5784533 = 135575) (by norm_num)
theorem B2573333 : Blo 1140634 2573333 := bbase (se 6 (by rfl) ⟨60312, by rfl⟩ : syracuseStep 2573333 = 120625) (by norm_num)
theorem B4342805 : Blo 1140634 4342805 := bbase (se 6 (by rfl) ⟨101784, by rfl⟩ : syracuseStep 4342805 = 203569) (by norm_num)
theorem B3851333 : Blo 1140634 3851333 := bbase (se 4 (by rfl) ⟨361062, by rfl⟩ : syracuseStep 3851333 = 722125) (by norm_num)
theorem B2442325 : Blo 1140634 2442325 := bbase (se 8 (by rfl) ⟨14310, by rfl⟩ : syracuseStep 2442325 = 28621) (by norm_num)
theorem B2573405 : Blo 1140634 2573405 := bbase (se 3 (by rfl) ⟨482513, by rfl⟩ : syracuseStep 2573405 = 965027) (by norm_num)
theorem B2573477 : Blo 1140634 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B2442469 : Blo 1140634 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B2573549 : Blo 1140634 2573549 := bbase (se 3 (by rfl) ⟨482540, by rfl⟩ : syracuseStep 2573549 = 965081) (by norm_num)
theorem B2475301 : Blo 1140634 2475301 := bbase (se 4 (by rfl) ⟨232059, by rfl⟩ : syracuseStep 2475301 = 464119) (by norm_num)
theorem B2573621 : Blo 1140634 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B3523925 : Blo 1140634 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B2573693 : Blo 1140634 2573693 := bbase (se 3 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 2573693 = 965135) (by norm_num)
theorem B2573765 : Blo 1140634 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B3851765 : Blo 1140634 3851765 := bbase (se 5 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 3851765 = 361103) (by norm_num)
theorem B2573837 : Blo 1140634 2573837 := bbase (se 3 (by rfl) ⟨482594, by rfl⟩ : syracuseStep 2573837 = 965189) (by norm_num)
theorem B2475605 : Blo 1140634 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2573909 : Blo 1140634 2573909 := bbase (se 8 (by rfl) ⟨15081, by rfl⟩ : syracuseStep 2573909 = 30163) (by norm_num)
theorem B2442845 : Blo 1140634 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B1951381 : Blo 1140634 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B2573981 : Blo 1140634 2573981 := bbase (se 3 (by rfl) ⟨482621, by rfl⟩ : syracuseStep 2573981 = 965243) (by norm_num)
theorem B2574053 : Blo 1140634 2574053 := bbase (se 4 (by rfl) ⟨241317, by rfl⟩ : syracuseStep 2574053 = 482635) (by norm_num)
theorem B2574125 : Blo 1140634 2574125 := bbase (se 3 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 2574125 = 965297) (by norm_num)
theorem B2574197 : Blo 1140634 2574197 := bbase (se 5 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 2574197 = 241331) (by norm_num)
theorem B10438517 : Blo 1140634 10438517 := bbase (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) (by norm_num)
theorem B3852197 : Blo 1140634 3852197 := bbase (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) (by norm_num)
theorem B2574269 : Blo 1140634 2574269 := bbase (se 3 (by rfl) ⟨482675, by rfl⟩ : syracuseStep 2574269 = 965351) (by norm_num)
theorem B2443213 : Blo 1140634 2443213 := bbase (se 3 (by rfl) ⟨458102, by rfl⟩ : syracuseStep 2443213 = 916205) (by norm_num)
theorem B2574341 : Blo 1140634 2574341 := bbase (se 4 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 2574341 = 482689) (by norm_num)
theorem B2574413 : Blo 1140634 2574413 := bbase (se 3 (by rfl) ⟨482702, by rfl⟩ : syracuseStep 2574413 = 965405) (by norm_num)
theorem B5490773 : Blo 1140634 5490773 := bbase (se 8 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 5490773 = 64345) (by norm_num)
theorem B2574485 : Blo 1140634 2574485 := bbase (se 6 (by rfl) ⟨60339, by rfl⟩ : syracuseStep 2574485 = 120679) (by norm_num)
theorem B4343989 : Blo 1140634 4343989 := bbase (se 5 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 4343989 = 407249) (by norm_num)
theorem B2574557 : Blo 1140634 2574557 := bbase (se 3 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 2574557 = 965459) (by norm_num)
theorem B5785829 : Blo 1140634 5785829 := bbase (se 4 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 5785829 = 1084843) (by norm_num)
theorem B2574629 : Blo 1140634 2574629 := bbase (se 4 (by rfl) ⟨241371, by rfl⟩ : syracuseStep 2574629 = 482743) (by norm_num)
theorem B3852629 : Blo 1140634 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B2607461 : Blo 1140634 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B2574701 : Blo 1140634 2574701 := bbase (se 3 (by rfl) ⟨482756, by rfl⟩ : syracuseStep 2574701 = 965513) (by norm_num)
theorem B2574773 : Blo 1140634 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B4344293 : Blo 1140634 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B2574845 : Blo 1140634 2574845 := bbase (se 3 (by rfl) ⟨482783, by rfl⟩ : syracuseStep 2574845 = 965567) (by norm_num)
theorem B1624645 : Blo 1140634 1624645 := bbase (se 4 (by rfl) ⟨152310, by rfl⟩ : syracuseStep 1624645 = 304621) (by norm_num)
theorem B2574917 : Blo 1140634 2574917 := bbase (se 4 (by rfl) ⟨241398, by rfl⟩ : syracuseStep 2574917 = 482797) (by norm_num)
theorem B2574989 : Blo 1140634 2574989 := bbase (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) (by norm_num)
theorem B2607805 : Blo 1140634 2607805 := bbase (se 3 (by rfl) ⟨488963, by rfl⟩ : syracuseStep 2607805 = 977927) (by norm_num)
theorem B2575061 : Blo 1140634 2575061 := bbase (se 7 (by rfl) ⟨30176, by rfl⟩ : syracuseStep 2575061 = 60353) (by norm_num)
theorem B2312941 : Blo 1140634 2312941 := bbase (se 3 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 2312941 = 867353) (by norm_num)
theorem B3853061 : Blo 1140634 3853061 := bbase (se 4 (by rfl) ⟨361224, by rfl⟩ : syracuseStep 3853061 = 722449) (by norm_num)
theorem B2575133 : Blo 1140634 2575133 := bbase (se 3 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 2575133 = 965675) (by norm_num)
theorem B2575205 : Blo 1140634 2575205 := bbase (se 4 (by rfl) ⟨241425, by rfl⟩ : syracuseStep 2575205 = 482851) (by norm_num)
theorem B2575277 : Blo 1140634 2575277 := bbase (se 3 (by rfl) ⟨482864, by rfl⟩ : syracuseStep 2575277 = 965729) (by norm_num)
theorem B5721013 : Blo 1140634 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B2575349 : Blo 1140634 2575349 := bbase (se 5 (by rfl) ⟨120719, by rfl⟩ : syracuseStep 2575349 = 241439) (by norm_num)
theorem B5557285 : Blo 1140634 5557285 := bbase (se 4 (by rfl) ⟨520995, by rfl⟩ : syracuseStep 5557285 = 1041991) (by norm_num)
theorem B2575421 : Blo 1140634 2575421 := bbase (se 3 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 2575421 = 965783) (by norm_num)
theorem B3853493 : Blo 1140634 3853493 := bbase (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) (by norm_num)
theorem B15650005 : Blo 1140634 15650005 := bbase (se 7 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 15650005 = 366797) (by norm_num)
theorem B1625437 : Blo 1140634 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B5787125 : Blo 1140634 5787125 := bbase (se 5 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 5787125 = 542543) (by norm_num)
theorem B3853925 : Blo 1140634 3853925 := bbase (se 4 (by rfl) ⟨361305, by rfl⟩ : syracuseStep 3853925 = 722611) (by norm_num)
theorem B10407541 : Blo 1140634 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B1625773 : Blo 1140634 1625773 := bbase (se 3 (by rfl) ⟨304832, by rfl⟩ : syracuseStep 1625773 = 609665) (by norm_num)
theorem B8244949 : Blo 1140634 8244949 := bbase (se 7 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 8244949 = 193241) (by norm_num)
theorem B1625989 : Blo 1140634 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B2084861 : Blo 1140634 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B3854357 : Blo 1140634 3854357 := bbase (se 6 (by rfl) ⟨90336, by rfl⟩ : syracuseStep 3854357 = 180673) (by norm_num)
theorem B8802325 : Blo 1140634 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B11751509 : Blo 1140634 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B1626365 : Blo 1140634 1626365 := bbase (se 3 (by rfl) ⟨304943, by rfl⟩ : syracuseStep 1626365 = 609887) (by norm_num)
theorem B3658117 : Blo 1140634 3658117 := bbase (se 4 (by rfl) ⟨342948, by rfl⟩ : syracuseStep 3658117 = 685897) (by norm_num)
theorem B3854789 : Blo 1140634 3854789 := bbase (se 4 (by rfl) ⟨361386, by rfl⟩ : syracuseStep 3854789 = 722773) (by norm_num)
theorem B4116997 : Blo 1140634 4116997 := bbase (se 4 (by rfl) ⟨385968, by rfl⟩ : syracuseStep 4116997 = 771937) (by norm_num)
theorem B2609741 : Blo 1140634 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B3658373 : Blo 1140634 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B12341909 : Blo 1140634 12341909 := bbase (se 6 (by rfl) ⟨289263, by rfl⟩ : syracuseStep 12341909 = 578527) (by norm_num)
theorem B5788421 : Blo 1140634 5788421 := bbase (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) (by norm_num)
theorem B5493557 : Blo 1140634 5493557 := bbase (se 5 (by rfl) ⟨257510, by rfl⟩ : syracuseStep 5493557 = 515021) (by norm_num)
theorem B3855221 : Blo 1140634 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B18502613 : Blo 1140634 18502613 := bbase (se 7 (by rfl) ⟨216827, by rfl⟩ : syracuseStep 18502613 = 433655) (by norm_num)
theorem B40096853 : Blo 1140634 40096853 := bbase (se 8 (by rfl) ⟨234942, by rfl⟩ : syracuseStep 40096853 = 469885) (by norm_num)
theorem B12375125 : Blo 1140634 12375125 := bbase (se 8 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 12375125 = 145021) (by norm_num)
theorem B1758485 : Blo 1140634 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B3855653 : Blo 1140634 3855653 := bbase (se 4 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 3855653 = 722935) (by norm_num)
theorem B1627789 : Blo 1140634 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B3856085 : Blo 1140634 3856085 := bbase (se 7 (by rfl) ⟨45188, by rfl⟩ : syracuseStep 3856085 = 90377) (by norm_num)
theorem B5789717 : Blo 1140634 5789717 := bbase (se 6 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 5789717 = 271393) (by norm_num)
theorem B1235057 : Blo 1140634 1235057 := bbase (se 2 (by rfl) ⟨463146, by rfl⟩ : syracuseStep 1235057 = 926293) (by norm_num)
theorem B3856517 : Blo 1140634 3856517 := bbase (se 4 (by rfl) ⟨361548, by rfl⟩ : syracuseStep 3856517 = 723097) (by norm_num)
theorem B2742493 : Blo 1140634 2742493 := bbase (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) (by norm_num)
theorem B1628381 : Blo 1140634 1628381 := bbase (se 3 (by rfl) ⟨305321, by rfl⟩ : syracuseStep 1628381 = 610643) (by norm_num)
theorem B2316557 : Blo 1140634 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B1628461 : Blo 1140634 1628461 := bbase (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) (by norm_num)
theorem B2742589 : Blo 1140634 2742589 := bbase (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) (by norm_num)
theorem B2087317 : Blo 1140634 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B1628581 : Blo 1140634 1628581 := bbase (se 4 (by rfl) ⟨152679, by rfl⟩ : syracuseStep 1628581 = 305359) (by norm_num)
theorem B1464797 : Blo 1140634 1464797 := bbase (se 3 (by rfl) ⟨274649, by rfl⟩ : syracuseStep 1464797 = 549299) (by norm_num)
theorem B2742781 : Blo 1140634 2742781 := bbase (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) (by norm_num)
theorem B1628677 : Blo 1140634 1628677 := bbase (se 4 (by rfl) ⟨152688, by rfl⟩ : syracuseStep 1628677 = 305377) (by norm_num)
theorem B4872757 : Blo 1140634 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B3856949 : Blo 1140634 3856949 := bbase (se 5 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 3856949 = 361589) (by norm_num)
theorem B4872773 : Blo 1140634 4872773 := bbase (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) (by norm_num)
theorem B2579165 : Blo 1140634 2579165 := bbase (se 3 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 2579165 = 967187) (by norm_num)
theorem B2743109 : Blo 1140634 2743109 := bbase (se 4 (by rfl) ⟨257166, by rfl⟩ : syracuseStep 2743109 = 514333) (by norm_num)
theorem B3857381 : Blo 1140634 3857381 := bbase (se 4 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 3857381 = 723259) (by norm_num)
theorem B1629173 : Blo 1140634 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1465393 : Blo 1140634 1465393 := bbase (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) (by norm_num)
theorem B1236061 : Blo 1140634 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B1301713 : Blo 1140634 1301713 := bbase (se 2 (by rfl) ⟨488142, by rfl⟩ : syracuseStep 1301713 = 976285) (by norm_num)
theorem B2743541 : Blo 1140634 2743541 := bbase (se 5 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 2743541 = 257207) (by norm_num)
theorem B5791013 : Blo 1140634 5791013 := bbase (se 4 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 5791013 = 1085815) (by norm_num)
theorem B8674613 : Blo 1140634 8674613 := bbase (se 5 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 8674613 = 813245) (by norm_num)
theorem B3661141 : Blo 1140634 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B3857813 : Blo 1140634 3857813 := bbase (se 6 (by rfl) ⟨90417, by rfl⟩ : syracuseStep 3857813 = 180835) (by norm_num)
theorem B6512021 : Blo 1140634 6512021 := bbase (se 6 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 6512021 = 305251) (by norm_num)
theorem B1465777 : Blo 1140634 1465777 := bbase (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) (by norm_num)
theorem B2317789 : Blo 1140634 2317789 := bbase (se 3 (by rfl) ⟨434585, by rfl⟩ : syracuseStep 2317789 = 869171) (by norm_num)
theorem B1629725 : Blo 1140634 1629725 := bbase (se 3 (by rfl) ⟨305573, by rfl⟩ : syracuseStep 1629725 = 611147) (by norm_num)
theorem B2743877 : Blo 1140634 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B1924877 : Blo 1140634 1924877 := bbase (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) (by norm_num)
theorem B3858245 : Blo 1140634 3858245 := bbase (se 4 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 3858245 = 723421) (by norm_num)
theorem B2318213 : Blo 1140634 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B1925005 : Blo 1140634 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B1925093 : Blo 1140634 1925093 := bbase (se 4 (by rfl) ⟨180477, by rfl⟩ : syracuseStep 1925093 = 360955) (by norm_num)
theorem B1302589 : Blo 1140634 1302589 := bbase (se 3 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 1302589 = 488471) (by norm_num)
theorem B1466461 : Blo 1140634 1466461 := bbase (se 3 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 1466461 = 549923) (by norm_num)
theorem B1925221 : Blo 1140634 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B2384005 : Blo 1140634 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1925309 : Blo 1140634 1925309 := bbase (se 3 (by rfl) ⟨360995, by rfl⟩ : syracuseStep 1925309 = 721991) (by norm_num)
theorem B4940021 : Blo 1140634 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B3858677 : Blo 1140634 3858677 := bbase (se 5 (by rfl) ⟨180875, by rfl⟩ : syracuseStep 3858677 = 361751) (by norm_num)
theorem B5497093 : Blo 1140634 5497093 := bbase (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) (by norm_num)
theorem B1827085 : Blo 1140634 1827085 := bbase (se 3 (by rfl) ⟨342578, by rfl⟩ : syracuseStep 1827085 = 685157) (by norm_num)
theorem B1925437 : Blo 1140634 1925437 := bbase (se 3 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 1925437 = 722039) (by norm_num)
theorem B3760453 : Blo 1140634 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B1925525 : Blo 1140634 1925525 := bbase (se 6 (by rfl) ⟨45129, by rfl⟩ : syracuseStep 1925525 = 90259) (by norm_num)
theorem B1925653 : Blo 1140634 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B2318885 : Blo 1140634 2318885 := bbase (se 4 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 2318885 = 434791) (by norm_num)
theorem B5792309 : Blo 1140634 5792309 := bbase (se 5 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 5792309 = 543029) (by norm_num)
theorem B2744933 : Blo 1140634 2744933 := bbase (se 4 (by rfl) ⟨257337, by rfl⟩ : syracuseStep 2744933 = 514675) (by norm_num)
theorem B1925741 : Blo 1140634 1925741 := bbase (se 3 (by rfl) ⟨361076, by rfl⟩ : syracuseStep 1925741 = 722153) (by norm_num)
theorem B17588885 : Blo 1140634 17588885 := bbase (se 6 (by rfl) ⟨412239, by rfl⟩ : syracuseStep 17588885 = 824479) (by norm_num)
theorem B3859109 : Blo 1140634 3859109 := bbase (se 4 (by rfl) ⟨361791, by rfl⟩ : syracuseStep 3859109 = 723583) (by norm_num)
theorem B1925869 : Blo 1140634 1925869 := bbase (se 3 (by rfl) ⟨361100, by rfl⟩ : syracuseStep 1925869 = 722201) (by norm_num)
theorem B4875029 : Blo 1140634 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B7824181 : Blo 1140634 7824181 := bbase (se 5 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 7824181 = 733517) (by norm_num)
theorem B1925957 : Blo 1140634 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B1303393 : Blo 1140634 1303393 := bbase (se 2 (by rfl) ⟨488772, by rfl⟩ : syracuseStep 1303393 = 977545) (by norm_num)
theorem B1926085 : Blo 1140634 1926085 := bbase (se 4 (by rfl) ⟨180570, by rfl⟩ : syracuseStep 1926085 = 361141) (by norm_num)
theorem B1926173 : Blo 1140634 1926173 := bbase (se 3 (by rfl) ⟨361157, by rfl⟩ : syracuseStep 1926173 = 722315) (by norm_num)
theorem B3859541 : Blo 1140634 3859541 := bbase (se 8 (by rfl) ⟨22614, by rfl⟩ : syracuseStep 3859541 = 45229) (by norm_num)
theorem B2319445 : Blo 1140634 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B1172569 : Blo 1140634 1172569 := bbase (se 2 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 1172569 = 879427) (by norm_num)
theorem B1926301 : Blo 1140634 1926301 := bbase (se 3 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 1926301 = 722363) (by norm_num)
theorem B1828021 : Blo 1140634 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B1926389 : Blo 1140634 1926389 := bbase (se 5 (by rfl) ⟨90299, by rfl⟩ : syracuseStep 1926389 = 180599) (by norm_num)
theorem B1303885 : Blo 1140634 1303885 := bbase (se 3 (by rfl) ⟨244478, by rfl⟩ : syracuseStep 1303885 = 488957) (by norm_num)
theorem B6939989 : Blo 1140634 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B1926517 : Blo 1140634 1926517 := bbase (se 5 (by rfl) ⟨90305, by rfl⟩ : syracuseStep 1926517 = 180611) (by norm_num)
theorem B1926605 : Blo 1140634 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B3859973 : Blo 1140634 3859973 := bbase (se 4 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 3859973 = 723745) (by norm_num)
theorem B1926733 : Blo 1140634 1926733 := bbase (se 3 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 1926733 = 722525) (by norm_num)
theorem B4122245 : Blo 1140634 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B1926821 : Blo 1140634 1926821 := bbase (se 4 (by rfl) ⟨180639, by rfl⟩ : syracuseStep 1926821 = 361279) (by norm_num)
theorem B1926949 : Blo 1140634 1926949 := bbase (se 4 (by rfl) ⟨180651, by rfl⟩ : syracuseStep 1926949 = 361303) (by norm_num)
theorem B5793605 : Blo 1140634 5793605 := bbase (se 4 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 5793605 = 1086301) (by norm_num)
theorem B1927037 : Blo 1140634 1927037 := bbase (se 3 (by rfl) ⟨361319, by rfl⟩ : syracuseStep 1927037 = 722639) (by norm_num)
theorem B3860405 : Blo 1140634 3860405 := bbase (se 5 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 3860405 = 361913) (by norm_num)
theorem B1468405 : Blo 1140634 1468405 := bbase (se 5 (by rfl) ⟨68831, by rfl⟩ : syracuseStep 1468405 = 137663) (by norm_num)
theorem B1927165 : Blo 1140634 1927165 := bbase (se 3 (by rfl) ⟨361343, by rfl⟩ : syracuseStep 1927165 = 722687) (by norm_num)
theorem B1304597 : Blo 1140634 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1304633 : Blo 1140634 1304633 := bbase (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) (by norm_num)
theorem B1927253 : Blo 1140634 1927253 := bbase (se 8 (by rfl) ⟨11292, by rfl⟩ : syracuseStep 1927253 = 22585) (by norm_num)
theorem B1927381 : Blo 1140634 1927381 := bbase (se 7 (by rfl) ⟨22586, by rfl⟩ : syracuseStep 1927381 = 45173) (by norm_num)
theorem B1927469 : Blo 1140634 1927469 := bbase (se 3 (by rfl) ⟨361400, by rfl⟩ : syracuseStep 1927469 = 722801) (by norm_num)
theorem B1829213 : Blo 1140634 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B3860837 : Blo 1140634 3860837 := bbase (se 4 (by rfl) ⟨361953, by rfl⟩ : syracuseStep 3860837 = 723907) (by norm_num)
theorem B1927597 : Blo 1140634 1927597 := bbase (se 3 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 1927597 = 722849) (by norm_num)
theorem B1927685 : Blo 1140634 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B1829405 : Blo 1140634 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B1927813 : Blo 1140634 1927813 := bbase (se 4 (by rfl) ⟨180732, by rfl⟩ : syracuseStep 1927813 = 361465) (by norm_num)
theorem B1927901 : Blo 1140634 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B2747125 : Blo 1140634 2747125 := bbase (se 5 (by rfl) ⟨128771, by rfl⟩ : syracuseStep 2747125 = 257543) (by norm_num)
theorem B3861269 : Blo 1140634 3861269 := bbase (se 6 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 3861269 = 180997) (by norm_num)
theorem B1370929 : Blo 1140634 1370929 := bbase (se 2 (by rfl) ⟨514098, by rfl⟩ : syracuseStep 1370929 = 1028197) (by norm_num)
theorem B1928029 : Blo 1140634 1928029 := bbase (se 3 (by rfl) ⟨361505, by rfl⟩ : syracuseStep 1928029 = 723011) (by norm_num)
theorem B1371025 : Blo 1140634 1371025 := bbase (se 2 (by rfl) ⟨514134, by rfl⟩ : syracuseStep 1371025 = 1028269) (by norm_num)
theorem B1928117 : Blo 1140634 1928117 := bbase (se 5 (by rfl) ⟨90380, by rfl⟩ : syracuseStep 1928117 = 180761) (by norm_num)
theorem B1928245 : Blo 1140634 1928245 := bbase (se 5 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 1928245 = 180773) (by norm_num)
theorem B1928333 : Blo 1140634 1928333 := bbase (se 3 (by rfl) ⟨361562, by rfl⟩ : syracuseStep 1928333 = 723125) (by norm_num)
theorem B4942997 : Blo 1140634 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B3861701 : Blo 1140634 3861701 := bbase (se 4 (by rfl) ⟨362034, by rfl⟩ : syracuseStep 3861701 = 724069) (by norm_num)
theorem B2059501 : Blo 1140634 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B1928461 : Blo 1140634 1928461 := bbase (se 3 (by rfl) ⟨361586, by rfl⟩ : syracuseStep 1928461 = 723173) (by norm_num)
theorem B1928549 : Blo 1140634 1928549 := bbase (se 4 (by rfl) ⟨180801, by rfl⟩ : syracuseStep 1928549 = 361603) (by norm_num)
theorem B1928677 : Blo 1140634 1928677 := bbase (se 4 (by rfl) ⟨180813, by rfl⟩ : syracuseStep 1928677 = 361627) (by norm_num)
theorem B1928765 : Blo 1140634 1928765 := bbase (se 3 (by rfl) ⟨361643, by rfl⟩ : syracuseStep 1928765 = 723287) (by norm_num)
theorem B3862133 : Blo 1140634 3862133 := bbase (se 5 (by rfl) ⟨181037, by rfl⟩ : syracuseStep 3862133 = 362075) (by norm_num)
theorem B1928893 : Blo 1140634 1928893 := bbase (se 3 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 1928893 = 723335) (by norm_num)
theorem B1928981 : Blo 1140634 1928981 := bbase (se 6 (by rfl) ⟨45210, by rfl⟩ : syracuseStep 1928981 = 90421) (by norm_num)
theorem B1372025 : Blo 1140634 1372025 := bbase (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) (by norm_num)
theorem B1929109 : Blo 1140634 1929109 := bbase (se 6 (by rfl) ⟨45213, by rfl⟩ : syracuseStep 1929109 = 90427) (by norm_num)
theorem B1830853 : Blo 1140634 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B1929197 : Blo 1140634 1929197 := bbase (se 3 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 1929197 = 723449) (by norm_num)
theorem B2060309 : Blo 1140634 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B3862565 : Blo 1140634 3862565 := bbase (se 4 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 3862565 = 724231) (by norm_num)
theorem B2748509 : Blo 1140634 2748509 := bbase (se 3 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 2748509 = 1030691) (by norm_num)
theorem B1929325 : Blo 1140634 1929325 := bbase (se 3 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 1929325 = 723497) (by norm_num)
theorem B1372313 : Blo 1140634 1372313 := bbase (se 2 (by rfl) ⟨514617, by rfl⟩ : syracuseStep 1372313 = 1029235) (by norm_num)
theorem B1929413 : Blo 1140634 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B2748701 : Blo 1140634 2748701 := bbase (se 3 (by rfl) ⟨515381, by rfl⟩ : syracuseStep 2748701 = 1030763) (by norm_num)
theorem B1372477 : Blo 1140634 1372477 := bbase (se 3 (by rfl) ⟨257339, by rfl⟩ : syracuseStep 1372477 = 514679) (by norm_num)
theorem B1929541 : Blo 1140634 1929541 := bbase (se 4 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 1929541 = 361789) (by norm_num)
theorem B1372505 : Blo 1140634 1372505 := bbase (se 2 (by rfl) ⟨514689, by rfl⟩ : syracuseStep 1372505 = 1029379) (by norm_num)
theorem B3666293 : Blo 1140634 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B1929629 : Blo 1140634 1929629 := bbase (se 3 (by rfl) ⟨361805, by rfl⟩ : syracuseStep 1929629 = 723611) (by norm_num)
theorem B6943157 : Blo 1140634 6943157 := bbase (se 5 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 6943157 = 650921) (by norm_num)
theorem B1372621 : Blo 1140634 1372621 := bbase (se 3 (by rfl) ⟨257366, by rfl⟩ : syracuseStep 1372621 = 514733) (by norm_num)
theorem B3862997 : Blo 1140634 3862997 := bbase (se 7 (by rfl) ⟨45269, by rfl⟩ : syracuseStep 3862997 = 90539) (by norm_num)
theorem B1929757 : Blo 1140634 1929757 := bbase (se 3 (by rfl) ⟨361829, by rfl⟩ : syracuseStep 1929757 = 723659) (by norm_num)
theorem B1372717 : Blo 1140634 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1929845 : Blo 1140634 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B4879061 : Blo 1140634 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B1929973 : Blo 1140634 1929973 := bbase (se 5 (by rfl) ⟨90467, by rfl⟩ : syracuseStep 1929973 = 180935) (by norm_num)
theorem B5206837 : Blo 1140634 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1930061 : Blo 1140634 1930061 := bbase (se 3 (by rfl) ⟨361886, by rfl⟩ : syracuseStep 1930061 = 723773) (by norm_num)
theorem B6943637 : Blo 1140634 6943637 := bbase (se 6 (by rfl) ⟨162741, by rfl⟩ : syracuseStep 6943637 = 325483) (by norm_num)
theorem B3470261 : Blo 1140634 3470261 := bbase (se 5 (by rfl) ⟨162668, by rfl⟩ : syracuseStep 3470261 = 325337) (by norm_num)
theorem B1930189 : Blo 1140634 1930189 := bbase (se 3 (by rfl) ⟨361910, by rfl⟩ : syracuseStep 1930189 = 723821) (by norm_num)
theorem B1373197 : Blo 1140634 1373197 := bbase (se 3 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 1373197 = 514949) (by norm_num)
theorem B2749469 : Blo 1140634 2749469 := bbase (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) (by norm_num)
theorem B1930277 : Blo 1140634 1930277 := bbase (se 4 (by rfl) ⟨180963, by rfl⟩ : syracuseStep 1930277 = 361927) (by norm_num)
theorem B10417205 : Blo 1140634 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B1930405 : Blo 1140634 1930405 := bbase (se 4 (by rfl) ⟨180975, by rfl⟩ : syracuseStep 1930405 = 361951) (by norm_num)
theorem B4945109 : Blo 1140634 4945109 := bbase (se 7 (by rfl) ⟨57950, by rfl⟩ : syracuseStep 4945109 = 115901) (by norm_num)
theorem B1930493 : Blo 1140634 1930493 := bbase (se 3 (by rfl) ⟨361967, by rfl⟩ : syracuseStep 1930493 = 723935) (by norm_num)
theorem B1832237 : Blo 1140634 1832237 := bbase (se 3 (by rfl) ⟨343544, by rfl⟩ : syracuseStep 1832237 = 687089) (by norm_num)
theorem B1930621 : Blo 1140634 1930621 := bbase (se 3 (by rfl) ⟨361991, by rfl⟩ : syracuseStep 1930621 = 723983) (by norm_num)
theorem B1930709 : Blo 1140634 1930709 := bbase (se 7 (by rfl) ⟨22625, by rfl⟩ : syracuseStep 1930709 = 45251) (by norm_num)
theorem B1832429 : Blo 1140634 1832429 := bbase (se 3 (by rfl) ⟨343580, by rfl⟩ : syracuseStep 1832429 = 687161) (by norm_num)
theorem B1930837 : Blo 1140634 1930837 := bbase (se 8 (by rfl) ⟨11313, by rfl⟩ : syracuseStep 1930837 = 22627) (by norm_num)
theorem B1930925 : Blo 1140634 1930925 := bbase (se 3 (by rfl) ⟨362048, by rfl⟩ : syracuseStep 1930925 = 724097) (by norm_num)
theorem B2062045 : Blo 1140634 2062045 := bbase (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) (by norm_num)
theorem B1931053 : Blo 1140634 1931053 := bbase (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) (by norm_num)
theorem B2062189 : Blo 1140634 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B1931141 : Blo 1140634 1931141 := bbase (se 4 (by rfl) ⟨181044, by rfl⟩ : syracuseStep 1931141 = 362089) (by norm_num)
theorem B3766181 : Blo 1140634 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B6256597 : Blo 1140634 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B1931269 : Blo 1140634 1931269 := bbase (se 4 (by rfl) ⟨181056, by rfl⟩ : syracuseStep 1931269 = 362113) (by norm_num)
theorem B1931357 : Blo 1140634 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B1931485 : Blo 1140634 1931485 := bbase (se 3 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 1931485 = 724307) (by norm_num)
theorem B1734949 : Blo 1140634 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B1374581 : Blo 1140634 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B4880837 : Blo 1140634 4880837 := bbase (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) (by norm_num)
theorem B4454885 : Blo 1140634 4454885 := bbase (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) (by norm_num)
theorem B1735157 : Blo 1140634 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B10975733 : Blo 1140634 10975733 := bbase (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) (by norm_num)
theorem B1374769 : Blo 1140634 1374769 := bbase (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) (by norm_num)
theorem B5274341 : Blo 1140634 5274341 := bbase (se 4 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 5274341 = 988939) (by norm_num)
theorem B1374985 : Blo 1140634 1374985 := bbase (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) (by norm_num)
theorem B8682389 : Blo 1140634 8682389 := bbase (se 6 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 8682389 = 406987) (by norm_num)
theorem B1735661 : Blo 1140634 1735661 := bbase (se 3 (by rfl) ⟨325436, by rfl⟩ : syracuseStep 1735661 = 650873) (by norm_num)
theorem B9763861 : Blo 1140634 9763861 := bbase (se 6 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 9763861 = 457681) (by norm_num)
theorem B1408369 : Blo 1140634 1408369 := bbase (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) (by norm_num)
theorem B4881829 : Blo 1140634 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B1736165 : Blo 1140634 1736165 := bbase (se 4 (by rfl) ⟨162765, by rfl⟩ : syracuseStep 1736165 = 325531) (by norm_num)
theorem B1736245 : Blo 1140634 1736245 := bbase (se 5 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 1736245 = 162773) (by norm_num)
theorem B1736785 : Blo 1140634 1736785 := bstep (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) B1302589
theorem B3178673 : Blo 1140634 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B29327669 : Blo 1140634 29327669 := bstep (se 5 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 29327669 = 2749469) B2749469
theorem B4882787 : Blo 1140634 4882787 := bstep (se 1 (by rfl) ⟨3662090, by rfl⟩ : syracuseStep 4882787 = 7324181) B7324181
theorem B5013937 : Blo 1140634 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B1737139 : Blo 1140634 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B8225549 : Blo 1140634 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B13009733 : Blo 1140634 13009733 := bstep (se 4 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 13009733 = 2439325) B2439325
theorem B1737857 : Blo 1140634 1737857 := bstep (se 2 (by rfl) ⟨651696, by rfl⟩ : syracuseStep 1737857 = 1303393) B1303393
theorem B13173941 : Blo 1140634 13173941 := bstep (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) B1235057
theorem B1738307 : Blo 1140634 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B1738513 : Blo 1140634 1738513 := bstep (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) B1303885
theorem B1443683 : Blo 1140634 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B4950065 : Blo 1140634 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B3475811 : Blo 1140634 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B1542577 : Blo 1140634 1542577 := bstep (se 2 (by rfl) ⟨578466, by rfl⟩ : syracuseStep 1542577 = 1156933) B1156933
theorem B1444387 : Blo 1140634 1444387 := bstep (se 1 (by rfl) ⟨1083290, by rfl⟩ : syracuseStep 1444387 = 2166581) B2166581
theorem B1444483 : Blo 1140634 1444483 := bstep (se 1 (by rfl) ⟨1083362, by rfl⟩ : syracuseStep 1444483 = 2166725) B2166725
theorem B8686277 : Blo 1140634 8686277 := bstep (se 4 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 8686277 = 1628677) B1628677
theorem B7834339 : Blo 1140634 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B1739827 : Blo 1140634 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B8227939 : Blo 1140634 8227939 := bstep (se 1 (by rfl) ⟨6170954, by rfl⟩ : syracuseStep 8227939 = 12341909) B12341909
theorem B1444979 : Blo 1140634 1444979 := bstep (se 1 (by rfl) ⟨1083734, by rfl⟩ : syracuseStep 1444979 = 2167469) B2167469
theorem B2166193 : Blo 1140634 2166193 := bstep (se 2 (by rfl) ⟨812322, by rfl⟩ : syracuseStep 2166193 = 1624645) B1624645
theorem B1543745 : Blo 1140634 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B2887235 : Blo 1140634 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B3477073 : Blo 1140634 3477073 := bstep (se 2 (by rfl) ⟨1303902, by rfl⟩ : syracuseStep 3477073 = 2607805) B2607805
theorem B3083921 : Blo 1140634 3083921 := bstep (se 2 (by rfl) ⟨1156470, by rfl⟩ : syracuseStep 3083921 = 2312941) B2312941
theorem B2887427 : Blo 1140634 2887427 := bstep (se 1 (by rfl) ⟨2165570, by rfl⟩ : syracuseStep 2887427 = 4331141) B4331141
theorem B1445683 : Blo 1140634 1445683 := bstep (se 1 (by rfl) ⟨1084262, by rfl⟩ : syracuseStep 1445683 = 2168525) B2168525
theorem B1445779 : Blo 1140634 1445779 := bstep (se 1 (by rfl) ⟨1084334, by rfl⟩ : syracuseStep 1445779 = 2168669) B2168669
theorem B4886477 : Blo 1140634 4886477 := bstep (se 3 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 4886477 = 1832429) B1832429
theorem B7409713 : Blo 1140634 7409713 := bstep (se 2 (by rfl) ⟨2778642, by rfl⟩ : syracuseStep 7409713 = 5557285) B5557285
theorem B3248333 : Blo 1140634 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B3248515 : Blo 1140634 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B1446275 : Blo 1140634 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B3248561 : Blo 1140634 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B2167249 : Blo 1140634 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B9769571 : Blo 1140634 9769571 := bstep (se 1 (by rfl) ⟨7327178, by rfl⟩ : syracuseStep 9769571 = 14654357) B14654357
theorem B2888369 : Blo 1140634 2888369 := bstep (se 2 (by rfl) ⟨1083138, by rfl⟩ : syracuseStep 2888369 = 2166277) B2166277
theorem B2888419 : Blo 1140634 2888419 := bstep (se 1 (by rfl) ⟨2166314, by rfl⟩ : syracuseStep 2888419 = 4332629) B4332629
theorem B11735779 : Blo 1140634 11735779 := bstep (se 1 (by rfl) ⟨8801834, by rfl⟩ : syracuseStep 11735779 = 17603669) B17603669
theorem B7312133 : Blo 1140634 7312133 := bstep (se 4 (by rfl) ⟨685512, by rfl⟩ : syracuseStep 7312133 = 1371025) B1371025
theorem B2167651 : Blo 1140634 2167651 := bstep (se 1 (by rfl) ⟨1625738, by rfl⟩ : syracuseStep 2167651 = 3251477) B3251477
theorem B2888561 : Blo 1140634 2888561 := bstep (se 2 (by rfl) ⟨1083210, by rfl⟩ : syracuseStep 2888561 = 2166421) B2166421
theorem B2167697 : Blo 1140634 2167697 := bstep (se 2 (by rfl) ⟨812886, by rfl⟩ : syracuseStep 2167697 = 1625773) B1625773
theorem B3085283 : Blo 1140634 3085283 := bstep (se 1 (by rfl) ⟨2313962, by rfl⟩ : syracuseStep 3085283 = 4627925) B4627925
theorem B1446979 : Blo 1140634 1446979 := bstep (se 1 (by rfl) ⟨1085234, by rfl⟩ : syracuseStep 1446979 = 2170469) B2170469
theorem B1447075 : Blo 1140634 1447075 := bstep (se 1 (by rfl) ⟨1085306, by rfl⟩ : syracuseStep 1447075 = 2170613) B2170613
theorem B2167985 : Blo 1140634 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B1283251 : Blo 1140634 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B1545409 : Blo 1140634 1545409 := bstep (se 2 (by rfl) ⟨579528, by rfl⟩ : syracuseStep 1545409 = 1159057) B1159057
theorem B1545475 : Blo 1140634 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1283395 : Blo 1140634 1283395 := bstep (se 1 (by rfl) ⟨962546, by rfl⟩ : syracuseStep 1283395 = 1925093) B1925093
theorem B11736433 : Blo 1140634 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B3478925 : Blo 1140634 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B1283539 : Blo 1140634 1283539 := bstep (se 1 (by rfl) ⟨962654, by rfl⟩ : syracuseStep 1283539 = 1925309) B1925309
theorem B3479021 : Blo 1140634 3479021 := bstep (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) B1304633
theorem B1283683 : Blo 1140634 1283683 := bstep (se 1 (by rfl) ⟨962762, by rfl⟩ : syracuseStep 1283683 = 1925525) B1925525
theorem B1447571 : Blo 1140634 1447571 := bstep (se 1 (by rfl) ⟨1085678, by rfl⟩ : syracuseStep 1447571 = 2171357) B2171357
theorem B4331171 : Blo 1140634 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B1545923 : Blo 1140634 1545923 := bstep (se 1 (by rfl) ⟨1159442, by rfl⟩ : syracuseStep 1545923 = 2318885) B2318885
theorem B1283827 : Blo 1140634 1283827 := bstep (se 1 (by rfl) ⟨962870, by rfl⟩ : syracuseStep 1283827 = 1925741) B1925741
theorem B2889553 : Blo 1140634 2889553 := bstep (se 2 (by rfl) ⟨1083582, by rfl⟩ : syracuseStep 2889553 = 2167165) B2167165
theorem B3250019 : Blo 1140634 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B1283971 : Blo 1140634 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B2168707 : Blo 1140634 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B1284115 : Blo 1140634 1284115 := bstep (se 1 (by rfl) ⟨963086, by rfl⟩ : syracuseStep 1284115 = 1926173) B1926173
theorem B2889827 : Blo 1140634 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B1284259 : Blo 1140634 1284259 := bstep (se 1 (by rfl) ⟨963194, by rfl⟩ : syracuseStep 1284259 = 1926389) B1926389
theorem B4626659 : Blo 1140634 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B2890019 : Blo 1140634 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B4331825 : Blo 1140634 4331825 := bstep (se 2 (by rfl) ⟨1624434, by rfl⟩ : syracuseStep 4331825 = 3248869) B3248869
theorem B1284403 : Blo 1140634 1284403 := bstep (se 1 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 1284403 = 1926605) B1926605
theorem B2169155 : Blo 1140634 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B1448275 : Blo 1140634 1448275 := bstep (se 1 (by rfl) ⟨1086206, by rfl⟩ : syracuseStep 1448275 = 2172413) B2172413
theorem B1448371 : Blo 1140634 1448371 := bstep (se 1 (by rfl) ⟨1086278, by rfl⟩ : syracuseStep 1448371 = 2172557) B2172557
theorem B1284547 : Blo 1140634 1284547 := bstep (se 1 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 1284547 = 1926821) B1926821
theorem B3709421 : Blo 1140634 3709421 := bstep (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) B1391033
theorem B13015565 : Blo 1140634 13015565 := bstep (se 3 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 13015565 = 4880837) B4880837
theorem B3906125 : Blo 1140634 3906125 := bstep (se 3 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 3906125 = 1464797) B1464797
theorem B1284691 : Blo 1140634 1284691 := bstep (se 1 (by rfl) ⟨963518, by rfl⟩ : syracuseStep 1284691 = 1927037) B1927037
theorem B2169443 : Blo 1140634 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B1284835 : Blo 1140634 1284835 := bstep (se 1 (by rfl) ⟨963626, by rfl⟩ : syracuseStep 1284835 = 1927253) B1927253
theorem B1284979 : Blo 1140634 1284979 := bstep (se 1 (by rfl) ⟨963734, by rfl⟩ : syracuseStep 1284979 = 1927469) B1927469
theorem B1710977 : Blo 1140634 1710977 := bstep (se 2 (by rfl) ⟨641616, by rfl⟩ : syracuseStep 1710977 = 1283233) B1283233
theorem B1710995 : Blo 1140634 1710995 := bstep (se 1 (by rfl) ⟨1283246, by rfl⟩ : syracuseStep 1710995 = 2566493) B2566493
theorem B1219475 : Blo 1140634 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1711025 : Blo 1140634 1711025 := bstep (se 2 (by rfl) ⟨641634, by rfl⟩ : syracuseStep 1711025 = 1283269) B1283269
theorem B1711043 : Blo 1140634 1711043 := bstep (se 1 (by rfl) ⟨1283282, by rfl⟩ : syracuseStep 1711043 = 2566565) B2566565
theorem B1711073 : Blo 1140634 1711073 := bstep (se 2 (by rfl) ⟨641652, by rfl⟩ : syracuseStep 1711073 = 1283305) B1283305
theorem B1711091 : Blo 1140634 1711091 := bstep (se 1 (by rfl) ⟨1283318, by rfl⟩ : syracuseStep 1711091 = 2566637) B2566637
theorem B1285123 : Blo 1140634 1285123 := bstep (se 1 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 1285123 = 1927685) B1927685
theorem B1711121 : Blo 1140634 1711121 := bstep (se 2 (by rfl) ⟨641670, by rfl⟩ : syracuseStep 1711121 = 1283341) B1283341
theorem B1711139 : Blo 1140634 1711139 := bstep (se 1 (by rfl) ⟨1283354, by rfl⟩ : syracuseStep 1711139 = 2566709) B2566709
theorem B3251249 : Blo 1140634 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B1711169 : Blo 1140634 1711169 := bstep (se 2 (by rfl) ⟨641688, by rfl⟩ : syracuseStep 1711169 = 1283377) B1283377
theorem B8232005 : Blo 1140634 8232005 := bstep (se 4 (by rfl) ⟨771750, by rfl⟩ : syracuseStep 8232005 = 1543501) B1543501
theorem B1711187 : Blo 1140634 1711187 := bstep (se 1 (by rfl) ⟨1283390, by rfl⟩ : syracuseStep 1711187 = 2566781) B2566781
theorem B1711217 : Blo 1140634 1711217 := bstep (se 2 (by rfl) ⟨641706, by rfl⟩ : syracuseStep 1711217 = 1283413) B1283413
theorem B1711235 : Blo 1140634 1711235 := bstep (se 1 (by rfl) ⟨1283426, by rfl⟩ : syracuseStep 1711235 = 2566853) B2566853
theorem B1285267 : Blo 1140634 1285267 := bstep (se 1 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 1285267 = 1927901) B1927901
theorem B1711265 : Blo 1140634 1711265 := bstep (se 2 (by rfl) ⟨641724, by rfl⟩ : syracuseStep 1711265 = 1283449) B1283449
theorem B5872817 : Blo 1140634 5872817 := bstep (se 2 (by rfl) ⟨2202306, by rfl⟩ : syracuseStep 5872817 = 4404613) B4404613
theorem B1711283 : Blo 1140634 1711283 := bstep (se 1 (by rfl) ⟨1283462, by rfl⟩ : syracuseStep 1711283 = 2566925) B2566925
theorem B1711313 : Blo 1140634 1711313 := bstep (se 2 (by rfl) ⟨641742, by rfl⟩ : syracuseStep 1711313 = 1283485) B1283485
theorem B2890961 : Blo 1140634 2890961 := bstep (se 2 (by rfl) ⟨1084110, by rfl⟩ : syracuseStep 2890961 = 2168221) B2168221
theorem B1711331 : Blo 1140634 1711331 := bstep (se 1 (by rfl) ⟨1283498, by rfl⟩ : syracuseStep 1711331 = 2566997) B2566997
theorem B1711361 : Blo 1140634 1711361 := bstep (se 2 (by rfl) ⟨641760, by rfl⟩ : syracuseStep 1711361 = 1283521) B1283521
theorem B2891011 : Blo 1140634 2891011 := bstep (se 1 (by rfl) ⟨2168258, by rfl⟩ : syracuseStep 2891011 = 4336517) B4336517
theorem B1711379 : Blo 1140634 1711379 := bstep (se 1 (by rfl) ⟨1283534, by rfl⟩ : syracuseStep 1711379 = 2567069) B2567069
theorem B1285411 : Blo 1140634 1285411 := bstep (se 1 (by rfl) ⟨964058, by rfl⟩ : syracuseStep 1285411 = 1928117) B1928117
theorem B1711409 : Blo 1140634 1711409 := bstep (se 2 (by rfl) ⟨641778, by rfl⟩ : syracuseStep 1711409 = 1283557) B1283557
theorem B1711427 : Blo 1140634 1711427 := bstep (se 1 (by rfl) ⟨1283570, by rfl⟩ : syracuseStep 1711427 = 2567141) B2567141
theorem B1711457 : Blo 1140634 1711457 := bstep (se 2 (by rfl) ⟨641796, by rfl⟩ : syracuseStep 1711457 = 1283593) B1283593
theorem B1711475 : Blo 1140634 1711475 := bstep (se 1 (by rfl) ⟨1283606, by rfl⟩ : syracuseStep 1711475 = 2567213) B2567213
theorem B1711505 : Blo 1140634 1711505 := bstep (se 2 (by rfl) ⟨641814, by rfl⟩ : syracuseStep 1711505 = 1283629) B1283629
theorem B2891153 : Blo 1140634 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B1711523 : Blo 1140634 1711523 := bstep (se 1 (by rfl) ⟨1283642, by rfl⟩ : syracuseStep 1711523 = 2567285) B2567285
theorem B1285555 : Blo 1140634 1285555 := bstep (se 1 (by rfl) ⟨964166, by rfl⟩ : syracuseStep 1285555 = 1928333) B1928333
theorem B1711553 : Blo 1140634 1711553 := bstep (se 2 (by rfl) ⟨641832, by rfl⟩ : syracuseStep 1711553 = 1283665) B1283665
theorem B1711571 : Blo 1140634 1711571 := bstep (se 1 (by rfl) ⟨1283678, by rfl⟩ : syracuseStep 1711571 = 2567357) B2567357
theorem B1711601 : Blo 1140634 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B1711619 : Blo 1140634 1711619 := bstep (se 1 (by rfl) ⟨1283714, by rfl⟩ : syracuseStep 1711619 = 2567429) B2567429
theorem B2170385 : Blo 1140634 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B1711649 : Blo 1140634 1711649 := bstep (se 2 (by rfl) ⟨641868, by rfl⟩ : syracuseStep 1711649 = 1283737) B1283737
theorem B1711667 : Blo 1140634 1711667 := bstep (se 1 (by rfl) ⟨1283750, by rfl⟩ : syracuseStep 1711667 = 2567501) B2567501
theorem B1285699 : Blo 1140634 1285699 := bstep (se 1 (by rfl) ⟨964274, by rfl⟩ : syracuseStep 1285699 = 1928549) B1928549
theorem B1711697 : Blo 1140634 1711697 := bstep (se 2 (by rfl) ⟨641886, by rfl⟩ : syracuseStep 1711697 = 1283773) B1283773
theorem B1711715 : Blo 1140634 1711715 := bstep (se 1 (by rfl) ⟨1283786, by rfl⟩ : syracuseStep 1711715 = 2567573) B2567573
theorem B1711745 : Blo 1140634 1711745 := bstep (se 2 (by rfl) ⟨641904, by rfl⟩ : syracuseStep 1711745 = 1283809) B1283809
theorem B1711763 : Blo 1140634 1711763 := bstep (se 1 (by rfl) ⟨1283822, by rfl⟩ : syracuseStep 1711763 = 2567645) B2567645
theorem B1711793 : Blo 1140634 1711793 := bstep (se 2 (by rfl) ⟨641922, by rfl⟩ : syracuseStep 1711793 = 1283845) B1283845
theorem B1711811 : Blo 1140634 1711811 := bstep (se 1 (by rfl) ⟨1283858, by rfl⟩ : syracuseStep 1711811 = 2567717) B2567717
theorem B1285843 : Blo 1140634 1285843 := bstep (se 1 (by rfl) ⟨964382, by rfl⟩ : syracuseStep 1285843 = 1928765) B1928765
theorem B1711841 : Blo 1140634 1711841 := bstep (se 2 (by rfl) ⟨641940, by rfl⟩ : syracuseStep 1711841 = 1283881) B1283881
theorem B4333283 : Blo 1140634 4333283 := bstep (se 1 (by rfl) ⟨3249962, by rfl⟩ : syracuseStep 4333283 = 6499925) B6499925
theorem B4333297 : Blo 1140634 4333297 := bstep (se 2 (by rfl) ⟨1624986, by rfl⟩ : syracuseStep 4333297 = 3249973) B3249973
theorem B1711859 : Blo 1140634 1711859 := bstep (se 1 (by rfl) ⟨1283894, by rfl⟩ : syracuseStep 1711859 = 2567789) B2567789
theorem B1711889 : Blo 1140634 1711889 := bstep (se 2 (by rfl) ⟨641958, by rfl⟩ : syracuseStep 1711889 = 1283917) B1283917
theorem B1711907 : Blo 1140634 1711907 := bstep (se 1 (by rfl) ⟨1283930, by rfl⟩ : syracuseStep 1711907 = 2567861) B2567861
theorem B1711937 : Blo 1140634 1711937 := bstep (se 2 (by rfl) ⟨641976, by rfl⟩ : syracuseStep 1711937 = 1283953) B1283953
theorem B1711955 : Blo 1140634 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B1285987 : Blo 1140634 1285987 := bstep (se 1 (by rfl) ⟨964490, by rfl⟩ : syracuseStep 1285987 = 1928981) B1928981
theorem B1711985 : Blo 1140634 1711985 := bstep (se 2 (by rfl) ⟨641994, by rfl⟩ : syracuseStep 1711985 = 1283989) B1283989
theorem B1712003 : Blo 1140634 1712003 := bstep (se 1 (by rfl) ⟨1284002, by rfl⟩ : syracuseStep 1712003 = 2568005) B2568005
theorem B1712033 : Blo 1140634 1712033 := bstep (se 2 (by rfl) ⟨642012, by rfl⟩ : syracuseStep 1712033 = 1284025) B1284025
theorem B1712051 : Blo 1140634 1712051 := bstep (se 1 (by rfl) ⟨1284038, by rfl⟩ : syracuseStep 1712051 = 2568077) B2568077
theorem B1712081 : Blo 1140634 1712081 := bstep (se 2 (by rfl) ⟨642030, by rfl⟩ : syracuseStep 1712081 = 1284061) B1284061
theorem B1712099 : Blo 1140634 1712099 := bstep (se 1 (by rfl) ⟨1284074, by rfl⟩ : syracuseStep 1712099 = 2568149) B2568149
theorem B1286131 : Blo 1140634 1286131 := bstep (se 1 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 1286131 = 1929197) B1929197
theorem B1712129 : Blo 1140634 1712129 := bstep (se 2 (by rfl) ⟨642048, by rfl⟩ : syracuseStep 1712129 = 1284097) B1284097
theorem B1712147 : Blo 1140634 1712147 := bstep (se 1 (by rfl) ⟨1284110, by rfl⟩ : syracuseStep 1712147 = 2568221) B2568221
theorem B1712177 : Blo 1140634 1712177 := bstep (se 2 (by rfl) ⟨642066, by rfl⟩ : syracuseStep 1712177 = 1284133) B1284133
theorem B1712195 : Blo 1140634 1712195 := bstep (se 1 (by rfl) ⟨1284146, by rfl⟩ : syracuseStep 1712195 = 2568293) B2568293
theorem B1712225 : Blo 1140634 1712225 := bstep (se 2 (by rfl) ⟨642084, by rfl⟩ : syracuseStep 1712225 = 1284169) B1284169
theorem B1712243 : Blo 1140634 1712243 := bstep (se 1 (by rfl) ⟨1284182, by rfl⟩ : syracuseStep 1712243 = 2568365) B2568365
theorem B1286275 : Blo 1140634 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B1712273 : Blo 1140634 1712273 := bstep (se 2 (by rfl) ⟨642102, by rfl⟩ : syracuseStep 1712273 = 1284205) B1284205
theorem B1712291 : Blo 1140634 1712291 := bstep (se 1 (by rfl) ⟨1284218, by rfl⟩ : syracuseStep 1712291 = 2568437) B2568437
theorem B1712321 : Blo 1140634 1712321 := bstep (se 2 (by rfl) ⟨642120, by rfl⟩ : syracuseStep 1712321 = 1284241) B1284241
theorem B1712339 : Blo 1140634 1712339 := bstep (se 1 (by rfl) ⟨1284254, by rfl⟩ : syracuseStep 1712339 = 2568509) B2568509
theorem B6496483 : Blo 1140634 6496483 := bstep (se 1 (by rfl) ⟨4872362, by rfl⟩ : syracuseStep 6496483 = 9744725) B9744725
theorem B1712369 : Blo 1140634 1712369 := bstep (se 2 (by rfl) ⟨642138, by rfl⟩ : syracuseStep 1712369 = 1284277) B1284277
theorem B7315697 : Blo 1140634 7315697 := bstep (se 2 (by rfl) ⟨2743386, by rfl⟩ : syracuseStep 7315697 = 5486773) B5486773
theorem B1712387 : Blo 1140634 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B1286419 : Blo 1140634 1286419 := bstep (se 1 (by rfl) ⟨964814, by rfl⟩ : syracuseStep 1286419 = 1929629) B1929629
theorem B1712417 : Blo 1140634 1712417 := bstep (se 2 (by rfl) ⟨642156, by rfl⟩ : syracuseStep 1712417 = 1284313) B1284313
theorem B4628771 : Blo 1140634 4628771 := bstep (se 1 (by rfl) ⟨3471578, by rfl⟩ : syracuseStep 4628771 = 6943157) B6943157
theorem B1712435 : Blo 1140634 1712435 := bstep (se 1 (by rfl) ⟨1284326, by rfl⟩ : syracuseStep 1712435 = 2568653) B2568653
theorem B1712465 : Blo 1140634 1712465 := bstep (se 2 (by rfl) ⟨642174, by rfl⟩ : syracuseStep 1712465 = 1284349) B1284349
theorem B1712483 : Blo 1140634 1712483 := bstep (se 1 (by rfl) ⟨1284362, by rfl⟩ : syracuseStep 1712483 = 2568725) B2568725
theorem B2892145 : Blo 1140634 2892145 := bstep (se 2 (by rfl) ⟨1084554, by rfl⟩ : syracuseStep 2892145 = 2169109) B2169109
theorem B1712513 : Blo 1140634 1712513 := bstep (se 2 (by rfl) ⟨642192, by rfl⟩ : syracuseStep 1712513 = 1284385) B1284385
theorem B2171281 : Blo 1140634 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B1712531 : Blo 1140634 1712531 := bstep (se 1 (by rfl) ⟨1284398, by rfl⟩ : syracuseStep 1712531 = 2568797) B2568797
theorem B1286563 : Blo 1140634 1286563 := bstep (se 1 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 1286563 = 1929845) B1929845
theorem B1712561 : Blo 1140634 1712561 := bstep (se 2 (by rfl) ⟨642210, by rfl⟩ : syracuseStep 1712561 = 1284421) B1284421
theorem B1712579 : Blo 1140634 1712579 := bstep (se 1 (by rfl) ⟨1284434, by rfl⟩ : syracuseStep 1712579 = 2568869) B2568869
theorem B1712609 : Blo 1140634 1712609 := bstep (se 2 (by rfl) ⟨642228, by rfl⟩ : syracuseStep 1712609 = 1284457) B1284457
theorem B3252707 : Blo 1140634 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B1712627 : Blo 1140634 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B1712657 : Blo 1140634 1712657 := bstep (se 2 (by rfl) ⟨642246, by rfl⟩ : syracuseStep 1712657 = 1284493) B1284493
theorem B1712675 : Blo 1140634 1712675 := bstep (se 1 (by rfl) ⟨1284506, by rfl⟩ : syracuseStep 1712675 = 2569013) B2569013
theorem B2171441 : Blo 1140634 2171441 := bstep (se 2 (by rfl) ⟨814290, by rfl⟩ : syracuseStep 2171441 = 1628581) B1628581
theorem B1286707 : Blo 1140634 1286707 := bstep (se 1 (by rfl) ⟨965030, by rfl⟩ : syracuseStep 1286707 = 1930061) B1930061
theorem B1712705 : Blo 1140634 1712705 := bstep (se 2 (by rfl) ⟨642264, by rfl⟩ : syracuseStep 1712705 = 1284529) B1284529
theorem B1712723 : Blo 1140634 1712723 := bstep (se 1 (by rfl) ⟨1284542, by rfl⟩ : syracuseStep 1712723 = 2569085) B2569085
theorem B4629091 : Blo 1140634 4629091 := bstep (se 1 (by rfl) ⟨3471818, by rfl⟩ : syracuseStep 4629091 = 6943637) B6943637
theorem B1712753 : Blo 1140634 1712753 := bstep (se 2 (by rfl) ⟨642282, by rfl⟩ : syracuseStep 1712753 = 1284565) B1284565
theorem B1712771 : Blo 1140634 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B2892419 : Blo 1140634 2892419 := bstep (se 1 (by rfl) ⟨2169314, by rfl⟩ : syracuseStep 2892419 = 4338629) B4338629
theorem B24748685 : Blo 1140634 24748685 := bstep (se 3 (by rfl) ⟨4640378, by rfl⟩ : syracuseStep 24748685 = 9280757) B9280757
theorem B1712801 : Blo 1140634 1712801 := bstep (se 2 (by rfl) ⟨642300, by rfl⟩ : syracuseStep 1712801 = 1284601) B1284601
theorem B1712819 : Blo 1140634 1712819 := bstep (se 1 (by rfl) ⟨1284614, by rfl⟩ : syracuseStep 1712819 = 2569229) B2569229
theorem B1286851 : Blo 1140634 1286851 := bstep (se 1 (by rfl) ⟨965138, by rfl⟩ : syracuseStep 1286851 = 1930277) B1930277
theorem B1712849 : Blo 1140634 1712849 := bstep (se 2 (by rfl) ⟨642318, by rfl⟩ : syracuseStep 1712849 = 1284637) B1284637
theorem B1909459 : Blo 1140634 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B1712867 : Blo 1140634 1712867 := bstep (se 1 (by rfl) ⟨1284650, by rfl⟩ : syracuseStep 1712867 = 2569301) B2569301
theorem B6497009 : Blo 1140634 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1712897 : Blo 1140634 1712897 := bstep (se 2 (by rfl) ⟨642336, by rfl⟩ : syracuseStep 1712897 = 1284673) B1284673
theorem B1712915 : Blo 1140634 1712915 := bstep (se 1 (by rfl) ⟨1284686, by rfl⟩ : syracuseStep 1712915 = 2569373) B2569373
theorem B1712945 : Blo 1140634 1712945 := bstep (se 2 (by rfl) ⟨642354, by rfl⟩ : syracuseStep 1712945 = 1284709) B1284709
theorem B1712963 : Blo 1140634 1712963 := bstep (se 1 (by rfl) ⟨1284722, by rfl⟩ : syracuseStep 1712963 = 2569445) B2569445
theorem B2892611 : Blo 1140634 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B1286995 : Blo 1140634 1286995 := bstep (se 1 (by rfl) ⟨965246, by rfl⟩ : syracuseStep 1286995 = 1930493) B1930493
theorem B1712993 : Blo 1140634 1712993 := bstep (se 2 (by rfl) ⟨642372, by rfl⟩ : syracuseStep 1712993 = 1284745) B1284745
theorem B1713011 : Blo 1140634 1713011 := bstep (se 1 (by rfl) ⟨1284758, by rfl⟩ : syracuseStep 1713011 = 2569517) B2569517
theorem B1221491 : Blo 1140634 1221491 := bstep (se 1 (by rfl) ⟨916118, by rfl⟩ : syracuseStep 1221491 = 1832237) B1832237
theorem B1713041 : Blo 1140634 1713041 := bstep (se 2 (by rfl) ⟨642390, by rfl⟩ : syracuseStep 1713041 = 1284781) B1284781
theorem B1713059 : Blo 1140634 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1713089 : Blo 1140634 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B2171843 : Blo 1140634 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B1713107 : Blo 1140634 1713107 := bstep (se 1 (by rfl) ⟨1284830, by rfl⟩ : syracuseStep 1713107 = 2569661) B2569661
theorem B1647587 : Blo 1140634 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B1287139 : Blo 1140634 1287139 := bstep (se 1 (by rfl) ⟨965354, by rfl⟩ : syracuseStep 1287139 = 1930709) B1930709
theorem B1713137 : Blo 1140634 1713137 := bstep (se 2 (by rfl) ⟨642426, by rfl⟩ : syracuseStep 1713137 = 1284853) B1284853
theorem B1713155 : Blo 1140634 1713155 := bstep (se 1 (by rfl) ⟨1284866, by rfl⟩ : syracuseStep 1713155 = 2569733) B2569733
theorem B1713185 : Blo 1140634 1713185 := bstep (se 2 (by rfl) ⟨642444, by rfl⟩ : syracuseStep 1713185 = 1284889) B1284889
theorem B5776433 : Blo 1140634 5776433 := bstep (se 2 (by rfl) ⟨2166162, by rfl⟩ : syracuseStep 5776433 = 4332325) B4332325
theorem B1713203 : Blo 1140634 1713203 := bstep (se 1 (by rfl) ⟨1284902, by rfl⟩ : syracuseStep 1713203 = 2569805) B2569805
theorem B1713233 : Blo 1140634 1713233 := bstep (se 2 (by rfl) ⟨642462, by rfl⟩ : syracuseStep 1713233 = 1284925) B1284925
theorem B1713251 : Blo 1140634 1713251 := bstep (se 1 (by rfl) ⟨1284938, by rfl⟩ : syracuseStep 1713251 = 2569877) B2569877
theorem B1287283 : Blo 1140634 1287283 := bstep (se 1 (by rfl) ⟨965462, by rfl⟩ : syracuseStep 1287283 = 1930925) B1930925
theorem B1713281 : Blo 1140634 1713281 := bstep (se 2 (by rfl) ⟨642480, by rfl⟩ : syracuseStep 1713281 = 1284961) B1284961
theorem B1713299 : Blo 1140634 1713299 := bstep (se 1 (by rfl) ⟨1284974, by rfl⟩ : syracuseStep 1713299 = 2569949) B2569949
theorem B4334755 : Blo 1140634 4334755 := bstep (se 1 (by rfl) ⟨3251066, by rfl⟩ : syracuseStep 4334755 = 6502133) B6502133
theorem B1713329 : Blo 1140634 1713329 := bstep (se 2 (by rfl) ⟨642498, by rfl⟩ : syracuseStep 1713329 = 1284997) B1284997
theorem B1713347 : Blo 1140634 1713347 := bstep (se 1 (by rfl) ⟨1285010, by rfl⟩ : syracuseStep 1713347 = 2570021) B2570021
theorem B1713377 : Blo 1140634 1713377 := bstep (se 2 (by rfl) ⟨642516, by rfl⟩ : syracuseStep 1713377 = 1285033) B1285033
theorem B1713395 : Blo 1140634 1713395 := bstep (se 1 (by rfl) ⟨1285046, by rfl⟩ : syracuseStep 1713395 = 2570093) B2570093
theorem B1287427 : Blo 1140634 1287427 := bstep (se 1 (by rfl) ⟨965570, by rfl⟩ : syracuseStep 1287427 = 1931141) B1931141
theorem B4629773 : Blo 1140634 4629773 := bstep (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) B1736165
theorem B3253517 : Blo 1140634 3253517 := bstep (se 3 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 3253517 = 1220069) B1220069
theorem B1713425 : Blo 1140634 1713425 := bstep (se 2 (by rfl) ⟨642534, by rfl⟩ : syracuseStep 1713425 = 1285069) B1285069
theorem B1713443 : Blo 1140634 1713443 := bstep (se 1 (by rfl) ⟨1285082, by rfl⟩ : syracuseStep 1713443 = 2570165) B2570165
theorem B1713473 : Blo 1140634 1713473 := bstep (se 2 (by rfl) ⟨642552, by rfl⟩ : syracuseStep 1713473 = 1285105) B1285105
theorem B1713491 : Blo 1140634 1713491 := bstep (se 1 (by rfl) ⟨1285118, by rfl⟩ : syracuseStep 1713491 = 2570237) B2570237
theorem B4171121 : Blo 1140634 4171121 := bstep (se 2 (by rfl) ⟨1564170, by rfl⟩ : syracuseStep 4171121 = 3128341) B3128341
theorem B1713521 : Blo 1140634 1713521 := bstep (se 2 (by rfl) ⟨642570, by rfl⟩ : syracuseStep 1713521 = 1285141) B1285141
theorem B13018481 : Blo 1140634 13018481 := bstep (se 2 (by rfl) ⟨4881930, by rfl⟩ : syracuseStep 13018481 = 9763861) B9763861
theorem B1713539 : Blo 1140634 1713539 := bstep (se 1 (by rfl) ⟨1285154, by rfl⟩ : syracuseStep 1713539 = 2570309) B2570309
theorem B1287571 : Blo 1140634 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B1713569 : Blo 1140634 1713569 := bstep (se 2 (by rfl) ⟨642588, by rfl⟩ : syracuseStep 1713569 = 1285177) B1285177
theorem B1713587 : Blo 1140634 1713587 := bstep (se 1 (by rfl) ⟨1285190, by rfl⟩ : syracuseStep 1713587 = 2570381) B2570381
theorem B3253709 : Blo 1140634 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B1648081 : Blo 1140634 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B1713617 : Blo 1140634 1713617 := bstep (se 2 (by rfl) ⟨642606, by rfl⟩ : syracuseStep 1713617 = 1285213) B1285213
theorem B1713635 : Blo 1140634 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B1713665 : Blo 1140634 1713665 := bstep (se 2 (by rfl) ⟨642624, by rfl⟩ : syracuseStep 1713665 = 1285249) B1285249
theorem B1713683 : Blo 1140634 1713683 := bstep (se 1 (by rfl) ⟨1285262, by rfl⟩ : syracuseStep 1713683 = 2570525) B2570525
theorem B1713713 : Blo 1140634 1713713 := bstep (se 2 (by rfl) ⟨642642, by rfl⟩ : syracuseStep 1713713 = 1285285) B1285285
theorem B1713731 : Blo 1140634 1713731 := bstep (se 1 (by rfl) ⟨1285298, by rfl⟩ : syracuseStep 1713731 = 2570597) B2570597
theorem B1713761 : Blo 1140634 1713761 := bstep (se 2 (by rfl) ⟨642660, by rfl⟩ : syracuseStep 1713761 = 1285321) B1285321
theorem B1713779 : Blo 1140634 1713779 := bstep (se 1 (by rfl) ⟨1285334, by rfl⟩ : syracuseStep 1713779 = 2570669) B2570669
theorem B1713809 : Blo 1140634 1713809 := bstep (se 2 (by rfl) ⟨642678, by rfl⟩ : syracuseStep 1713809 = 1285357) B1285357
theorem B1156771 : Blo 1140634 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B7317155 : Blo 1140634 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B1713827 : Blo 1140634 1713827 := bstep (se 1 (by rfl) ⟨1285370, by rfl⟩ : syracuseStep 1713827 = 2570741) B2570741
theorem B1713857 : Blo 1140634 1713857 := bstep (se 2 (by rfl) ⟨642696, by rfl⟩ : syracuseStep 1713857 = 1285393) B1285393
theorem B1713875 : Blo 1140634 1713875 := bstep (se 1 (by rfl) ⟨1285406, by rfl⟩ : syracuseStep 1713875 = 2570813) B2570813
theorem B1713905 : Blo 1140634 1713905 := bstep (se 2 (by rfl) ⟨642714, by rfl⟩ : syracuseStep 1713905 = 1285429) B1285429
theorem B2893553 : Blo 1140634 2893553 := bstep (se 2 (by rfl) ⟨1085082, by rfl⟩ : syracuseStep 2893553 = 2170165) B2170165
theorem B1713923 : Blo 1140634 1713923 := bstep (se 1 (by rfl) ⟨1285442, by rfl⟩ : syracuseStep 1713923 = 2570885) B2570885
theorem B1713953 : Blo 1140634 1713953 := bstep (se 2 (by rfl) ⟨642732, by rfl⟩ : syracuseStep 1713953 = 1285465) B1285465
theorem B2893603 : Blo 1140634 2893603 := bstep (se 1 (by rfl) ⟨2170202, by rfl⟩ : syracuseStep 2893603 = 4340405) B4340405
theorem B1713971 : Blo 1140634 1713971 := bstep (se 1 (by rfl) ⟨1285478, by rfl⟩ : syracuseStep 1713971 = 2570957) B2570957
theorem B1877825 : Blo 1140634 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B3516227 : Blo 1140634 3516227 := bstep (se 1 (by rfl) ⟨2637170, by rfl⟩ : syracuseStep 3516227 = 5274341) B5274341
theorem B2172739 : Blo 1140634 2172739 := bstep (se 1 (by rfl) ⟨1629554, by rfl⟩ : syracuseStep 2172739 = 3259109) B3259109
theorem B1714001 : Blo 1140634 1714001 := bstep (se 2 (by rfl) ⟨642750, by rfl⟩ : syracuseStep 1714001 = 1285501) B1285501
theorem B1714019 : Blo 1140634 1714019 := bstep (se 1 (by rfl) ⟨1285514, by rfl⟩ : syracuseStep 1714019 = 2571029) B2571029
theorem B1714049 : Blo 1140634 1714049 := bstep (se 2 (by rfl) ⟨642768, by rfl⟩ : syracuseStep 1714049 = 1285537) B1285537
theorem B1714067 : Blo 1140634 1714067 := bstep (se 1 (by rfl) ⟨1285550, by rfl⟩ : syracuseStep 1714067 = 2571101) B2571101
theorem B1714097 : Blo 1140634 1714097 := bstep (se 2 (by rfl) ⟨642786, by rfl⟩ : syracuseStep 1714097 = 1285573) B1285573
theorem B2893745 : Blo 1140634 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B1714115 : Blo 1140634 1714115 := bstep (se 1 (by rfl) ⟨1285586, by rfl⟩ : syracuseStep 1714115 = 2571173) B2571173
theorem B3090385 : Blo 1140634 3090385 := bstep (se 2 (by rfl) ⟨1158894, by rfl⟩ : syracuseStep 3090385 = 2317789) B2317789
theorem B1714145 : Blo 1140634 1714145 := bstep (se 2 (by rfl) ⟨642804, by rfl⟩ : syracuseStep 1714145 = 1285609) B1285609
theorem B2172899 : Blo 1140634 2172899 := bstep (se 1 (by rfl) ⟨1629674, by rfl⟩ : syracuseStep 2172899 = 3259349) B3259349
theorem B3909617 : Blo 1140634 3909617 := bstep (se 2 (by rfl) ⟨1466106, by rfl⟩ : syracuseStep 3909617 = 2932213) B2932213
theorem B1157107 : Blo 1140634 1157107 := bstep (se 1 (by rfl) ⟨867830, by rfl⟩ : syracuseStep 1157107 = 1735661) B1735661
theorem B1714163 : Blo 1140634 1714163 := bstep (se 1 (by rfl) ⟨1285622, by rfl⟩ : syracuseStep 1714163 = 2571245) B2571245
theorem B1714193 : Blo 1140634 1714193 := bstep (se 2 (by rfl) ⟨642822, by rfl⟩ : syracuseStep 1714193 = 1285645) B1285645
theorem B1714211 : Blo 1140634 1714211 := bstep (se 1 (by rfl) ⟨1285658, by rfl⟩ : syracuseStep 1714211 = 2571317) B2571317
theorem B1714241 : Blo 1140634 1714241 := bstep (se 2 (by rfl) ⟨642840, by rfl⟩ : syracuseStep 1714241 = 1285681) B1285681
theorem B1714259 : Blo 1140634 1714259 := bstep (se 1 (by rfl) ⟨1285694, by rfl⟩ : syracuseStep 1714259 = 2571389) B2571389
theorem B6170737 : Blo 1140634 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B1714289 : Blo 1140634 1714289 := bstep (se 2 (by rfl) ⟨642858, by rfl⟩ : syracuseStep 1714289 = 1285717) B1285717
theorem B1714307 : Blo 1140634 1714307 := bstep (se 1 (by rfl) ⟨1285730, by rfl⟩ : syracuseStep 1714307 = 2571461) B2571461
theorem B1714337 : Blo 1140634 1714337 := bstep (se 2 (by rfl) ⟨642876, by rfl⟩ : syracuseStep 1714337 = 1285753) B1285753
theorem B6498467 : Blo 1140634 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B1714355 : Blo 1140634 1714355 := bstep (se 1 (by rfl) ⟨1285766, by rfl⟩ : syracuseStep 1714355 = 2571533) B2571533
theorem B1714385 : Blo 1140634 1714385 := bstep (se 2 (by rfl) ⟨642894, by rfl⟩ : syracuseStep 1714385 = 1285789) B1285789
theorem B1714403 : Blo 1140634 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1714433 : Blo 1140634 1714433 := bstep (se 2 (by rfl) ⟨642912, by rfl⟩ : syracuseStep 1714433 = 1285825) B1285825
theorem B1714451 : Blo 1140634 1714451 := bstep (se 1 (by rfl) ⟨1285838, by rfl⟩ : syracuseStep 1714451 = 2571677) B2571677
theorem B1714481 : Blo 1140634 1714481 := bstep (se 2 (by rfl) ⟨642930, by rfl⟩ : syracuseStep 1714481 = 1285861) B1285861
theorem B1714499 : Blo 1140634 1714499 := bstep (se 1 (by rfl) ⟨1285874, by rfl⟩ : syracuseStep 1714499 = 2571749) B2571749
theorem B1714529 : Blo 1140634 1714529 := bstep (se 2 (by rfl) ⟨642948, by rfl⟩ : syracuseStep 1714529 = 1285897) B1285897
theorem B8235377 : Blo 1140634 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B1714547 : Blo 1140634 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B1714577 : Blo 1140634 1714577 := bstep (se 2 (by rfl) ⟨642966, by rfl⟩ : syracuseStep 1714577 = 1285933) B1285933
theorem B1714595 : Blo 1140634 1714595 := bstep (se 1 (by rfl) ⟨1285946, by rfl⟩ : syracuseStep 1714595 = 2571893) B2571893
theorem B3254701 : Blo 1140634 3254701 := bstep (se 3 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 3254701 = 1220513) B1220513
theorem B1714625 : Blo 1140634 1714625 := bstep (se 2 (by rfl) ⟨642984, by rfl⟩ : syracuseStep 1714625 = 1285969) B1285969
theorem B1714643 : Blo 1140634 1714643 := bstep (se 1 (by rfl) ⟨1285982, by rfl⟩ : syracuseStep 1714643 = 2571965) B2571965
theorem B5777891 : Blo 1140634 5777891 := bstep (se 1 (by rfl) ⟨4333418, by rfl⟩ : syracuseStep 5777891 = 8666837) B8666837
theorem B1714673 : Blo 1140634 1714673 := bstep (se 2 (by rfl) ⟨643002, by rfl⟩ : syracuseStep 1714673 = 1286005) B1286005
theorem B1714691 : Blo 1140634 1714691 := bstep (se 1 (by rfl) ⟨1286018, by rfl⟩ : syracuseStep 1714691 = 2572037) B2572037
theorem B2566673 : Blo 1140634 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B1714721 : Blo 1140634 1714721 := bstep (se 2 (by rfl) ⟨643020, by rfl⟩ : syracuseStep 1714721 = 1286041) B1286041
theorem B2566691 : Blo 1140634 2566691 := bstep (se 1 (by rfl) ⟨1925018, by rfl⟩ : syracuseStep 2566691 = 3850037) B3850037
theorem B1649203 : Blo 1140634 1649203 := bstep (se 1 (by rfl) ⟨1236902, by rfl⟩ : syracuseStep 1649203 = 2473805) B2473805
theorem B1714739 : Blo 1140634 1714739 := bstep (se 1 (by rfl) ⟨1286054, by rfl⟩ : syracuseStep 1714739 = 2572109) B2572109
theorem B1714769 : Blo 1140634 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B1714787 : Blo 1140634 1714787 := bstep (se 1 (by rfl) ⟨1286090, by rfl⟩ : syracuseStep 1714787 = 2572181) B2572181
theorem B1714817 : Blo 1140634 1714817 := bstep (se 2 (by rfl) ⟨643056, by rfl⟩ : syracuseStep 1714817 = 1286113) B1286113
theorem B1714835 : Blo 1140634 1714835 := bstep (se 1 (by rfl) ⟨1286126, by rfl⟩ : syracuseStep 1714835 = 2572253) B2572253
theorem B1714865 : Blo 1140634 1714865 := bstep (se 2 (by rfl) ⟨643074, by rfl⟩ : syracuseStep 1714865 = 1286149) B1286149
theorem B3910339 : Blo 1140634 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B1714883 : Blo 1140634 1714883 := bstep (se 1 (by rfl) ⟨1286162, by rfl⟩ : syracuseStep 1714883 = 2572325) B2572325
theorem B1714913 : Blo 1140634 1714913 := bstep (se 2 (by rfl) ⟨643092, by rfl⟩ : syracuseStep 1714913 = 1286185) B1286185
theorem B1714931 : Blo 1140634 1714931 := bstep (se 1 (by rfl) ⟨1286198, by rfl⟩ : syracuseStep 1714931 = 2572397) B2572397
theorem B1714961 : Blo 1140634 1714961 := bstep (se 2 (by rfl) ⟨643110, by rfl⟩ : syracuseStep 1714961 = 1286221) B1286221
theorem B1714979 : Blo 1140634 1714979 := bstep (se 1 (by rfl) ⟨1286234, by rfl⟩ : syracuseStep 1714979 = 2572469) B2572469
theorem B2566961 : Blo 1140634 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B1715009 : Blo 1140634 1715009 := bstep (se 2 (by rfl) ⟨643128, by rfl⟩ : syracuseStep 1715009 = 1286257) B1286257
theorem B2566979 : Blo 1140634 2566979 := bstep (se 1 (by rfl) ⟨1925234, by rfl⟩ : syracuseStep 2566979 = 3850469) B3850469
theorem B1157971 : Blo 1140634 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1715027 : Blo 1140634 1715027 := bstep (se 1 (by rfl) ⟨1286270, by rfl⟩ : syracuseStep 1715027 = 2572541) B2572541
theorem B1715057 : Blo 1140634 1715057 := bstep (se 2 (by rfl) ⟨643146, by rfl⟩ : syracuseStep 1715057 = 1286293) B1286293
theorem B1715075 : Blo 1140634 1715075 := bstep (se 1 (by rfl) ⟨1286306, by rfl⟩ : syracuseStep 1715075 = 2572613) B2572613
theorem B2894737 : Blo 1140634 2894737 := bstep (se 2 (by rfl) ⟨1085526, by rfl⟩ : syracuseStep 2894737 = 2171053) B2171053
theorem B1715105 : Blo 1140634 1715105 := bstep (se 2 (by rfl) ⟨643164, by rfl⟩ : syracuseStep 1715105 = 1286329) B1286329
theorem B1715123 : Blo 1140634 1715123 := bstep (se 1 (by rfl) ⟨1286342, by rfl⟩ : syracuseStep 1715123 = 2572685) B2572685
theorem B1715153 : Blo 1140634 1715153 := bstep (se 2 (by rfl) ⟨643182, by rfl⟩ : syracuseStep 1715153 = 1286365) B1286365
theorem B1715171 : Blo 1140634 1715171 := bstep (se 1 (by rfl) ⟨1286378, by rfl⟩ : syracuseStep 1715171 = 2572757) B2572757
theorem B1715201 : Blo 1140634 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B2436113 : Blo 1140634 2436113 := bstep (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) B1827085
theorem B1715219 : Blo 1140634 1715219 := bstep (se 1 (by rfl) ⟨1286414, by rfl⟩ : syracuseStep 1715219 = 2572829) B2572829
theorem B2436131 : Blo 1140634 2436131 := bstep (se 1 (by rfl) ⟨1827098, by rfl⟩ : syracuseStep 2436131 = 3654197) B3654197
theorem B1715249 : Blo 1140634 1715249 := bstep (se 2 (by rfl) ⟨643218, by rfl⟩ : syracuseStep 1715249 = 1286437) B1286437
theorem B1715267 : Blo 1140634 1715267 := bstep (se 1 (by rfl) ⟨1286450, by rfl⟩ : syracuseStep 1715267 = 2572901) B2572901
theorem B2567249 : Blo 1140634 2567249 := bstep (se 2 (by rfl) ⟨962718, by rfl⟩ : syracuseStep 2567249 = 1925437) B1925437
theorem B1715297 : Blo 1140634 1715297 := bstep (se 2 (by rfl) ⟨643236, by rfl⟩ : syracuseStep 1715297 = 1286473) B1286473
theorem B2567267 : Blo 1140634 2567267 := bstep (se 1 (by rfl) ⟨1925450, by rfl⟩ : syracuseStep 2567267 = 3850901) B3850901
theorem B46967921 : Blo 1140634 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B1715315 : Blo 1140634 1715315 := bstep (se 1 (by rfl) ⟨1286486, by rfl⟩ : syracuseStep 1715315 = 2572973) B2572973
theorem B1715345 : Blo 1140634 1715345 := bstep (se 2 (by rfl) ⟨643254, by rfl⟩ : syracuseStep 1715345 = 1286509) B1286509
theorem B1715363 : Blo 1140634 1715363 := bstep (se 1 (by rfl) ⟨1286522, by rfl⟩ : syracuseStep 1715363 = 2573045) B2573045
theorem B2895011 : Blo 1140634 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B1715393 : Blo 1140634 1715393 := bstep (se 2 (by rfl) ⟨643272, by rfl⟩ : syracuseStep 1715393 = 1286545) B1286545
theorem B1715411 : Blo 1140634 1715411 := bstep (se 1 (by rfl) ⟨1286558, by rfl⟩ : syracuseStep 1715411 = 2573117) B2573117
theorem B1715441 : Blo 1140634 1715441 := bstep (se 2 (by rfl) ⟨643290, by rfl⟩ : syracuseStep 1715441 = 1286581) B1286581
theorem B1715459 : Blo 1140634 1715459 := bstep (se 1 (by rfl) ⟨1286594, by rfl⟩ : syracuseStep 1715459 = 2573189) B2573189
theorem B5778701 : Blo 1140634 5778701 := bstep (se 3 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 5778701 = 2167013) B2167013
theorem B1715489 : Blo 1140634 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B1715507 : Blo 1140634 1715507 := bstep (se 1 (by rfl) ⟨1286630, by rfl⟩ : syracuseStep 1715507 = 2573261) B2573261
theorem B4336973 : Blo 1140634 4336973 := bstep (se 3 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 4336973 = 1626365) B1626365
theorem B1715537 : Blo 1140634 1715537 := bstep (se 2 (by rfl) ⟨643326, by rfl⟩ : syracuseStep 1715537 = 1286653) B1286653
theorem B2895203 : Blo 1140634 2895203 := bstep (se 1 (by rfl) ⟨2171402, by rfl⟩ : syracuseStep 2895203 = 4342805) B4342805
theorem B1715555 : Blo 1140634 1715555 := bstep (se 1 (by rfl) ⟨1286666, by rfl⟩ : syracuseStep 1715555 = 2573333) B2573333
theorem B2567537 : Blo 1140634 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B1715585 : Blo 1140634 1715585 := bstep (se 2 (by rfl) ⟨643344, by rfl⟩ : syracuseStep 1715585 = 1286689) B1286689
theorem B2567555 : Blo 1140634 2567555 := bstep (se 1 (by rfl) ⟨1925666, by rfl⟩ : syracuseStep 2567555 = 3851333) B3851333
theorem B1715603 : Blo 1140634 1715603 := bstep (se 1 (by rfl) ⟨1286702, by rfl⟩ : syracuseStep 1715603 = 2573405) B2573405
theorem B1715633 : Blo 1140634 1715633 := bstep (se 2 (by rfl) ⟨643362, by rfl⟩ : syracuseStep 1715633 = 1286725) B1286725
theorem B1715651 : Blo 1140634 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1715681 : Blo 1140634 1715681 := bstep (se 2 (by rfl) ⟨643380, by rfl⟩ : syracuseStep 1715681 = 1286761) B1286761
theorem B1715699 : Blo 1140634 1715699 := bstep (se 1 (by rfl) ⟨1286774, by rfl⟩ : syracuseStep 1715699 = 2573549) B2573549
theorem B1715729 : Blo 1140634 1715729 := bstep (se 2 (by rfl) ⟨643398, by rfl⟩ : syracuseStep 1715729 = 1286797) B1286797
theorem B1715747 : Blo 1140634 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B1715777 : Blo 1140634 1715777 := bstep (se 2 (by rfl) ⟨643416, by rfl⟩ : syracuseStep 1715777 = 1286833) B1286833
theorem B1715795 : Blo 1140634 1715795 := bstep (se 1 (by rfl) ⟨1286846, by rfl⟩ : syracuseStep 1715795 = 2573693) B2573693
theorem B1715825 : Blo 1140634 1715825 := bstep (se 2 (by rfl) ⟨643434, by rfl⟩ : syracuseStep 1715825 = 1286869) B1286869
theorem B1715843 : Blo 1140634 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B2567825 : Blo 1140634 2567825 := bstep (se 2 (by rfl) ⟨962934, by rfl⟩ : syracuseStep 2567825 = 1925869) B1925869
theorem B1715873 : Blo 1140634 1715873 := bstep (se 2 (by rfl) ⟨643452, by rfl⟩ : syracuseStep 1715873 = 1286905) B1286905
theorem B2567843 : Blo 1140634 2567843 := bstep (se 1 (by rfl) ⟨1925882, by rfl⟩ : syracuseStep 2567843 = 3851765) B3851765
theorem B1715891 : Blo 1140634 1715891 := bstep (se 1 (by rfl) ⟨1286918, by rfl⟩ : syracuseStep 1715891 = 2573837) B2573837
theorem B1715921 : Blo 1140634 1715921 := bstep (se 2 (by rfl) ⟨643470, by rfl⟩ : syracuseStep 1715921 = 1286941) B1286941
theorem B1650403 : Blo 1140634 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B1715939 : Blo 1140634 1715939 := bstep (se 1 (by rfl) ⟨1286954, by rfl⟩ : syracuseStep 1715939 = 2573909) B2573909
theorem B10432241 : Blo 1140634 10432241 := bstep (se 2 (by rfl) ⟨3912090, by rfl⟩ : syracuseStep 10432241 = 7824181) B7824181
theorem B1715969 : Blo 1140634 1715969 := bstep (se 2 (by rfl) ⟨643488, by rfl⟩ : syracuseStep 1715969 = 1286977) B1286977
theorem B3714833 : Blo 1140634 3714833 := bstep (se 2 (by rfl) ⟨1393062, by rfl⟩ : syracuseStep 3714833 = 2786125) B2786125
theorem B1715987 : Blo 1140634 1715987 := bstep (se 1 (by rfl) ⟨1286990, by rfl⟩ : syracuseStep 1715987 = 2573981) B2573981
theorem B1716017 : Blo 1140634 1716017 := bstep (se 2 (by rfl) ⟨643506, by rfl⟩ : syracuseStep 1716017 = 1287013) B1287013
theorem B1716035 : Blo 1140634 1716035 := bstep (se 1 (by rfl) ⟨1287026, by rfl⟩ : syracuseStep 1716035 = 2574053) B2574053
theorem B1716065 : Blo 1140634 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B1716083 : Blo 1140634 1716083 := bstep (se 1 (by rfl) ⟨1287062, by rfl⟩ : syracuseStep 1716083 = 2574125) B2574125
theorem B1716113 : Blo 1140634 1716113 := bstep (se 2 (by rfl) ⟨643542, by rfl⟩ : syracuseStep 1716113 = 1287085) B1287085
theorem B1716131 : Blo 1140634 1716131 := bstep (se 1 (by rfl) ⟨1287098, by rfl⟩ : syracuseStep 1716131 = 2574197) B2574197
theorem B2568113 : Blo 1140634 2568113 := bstep (se 2 (by rfl) ⟨963042, by rfl⟩ : syracuseStep 2568113 = 1926085) B1926085
theorem B1716161 : Blo 1140634 1716161 := bstep (se 2 (by rfl) ⟨643560, by rfl⟩ : syracuseStep 1716161 = 1287121) B1287121
theorem B2568131 : Blo 1140634 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B1716179 : Blo 1140634 1716179 := bstep (se 1 (by rfl) ⟨1287134, by rfl⟩ : syracuseStep 1716179 = 2574269) B2574269
theorem B10989539 : Blo 1140634 10989539 := bstep (se 1 (by rfl) ⟨8242154, by rfl⟩ : syracuseStep 10989539 = 16484309) B16484309
theorem B1716209 : Blo 1140634 1716209 := bstep (se 2 (by rfl) ⟨643578, by rfl⟩ : syracuseStep 1716209 = 1287157) B1287157
theorem B1716227 : Blo 1140634 1716227 := bstep (se 1 (by rfl) ⟨1287170, by rfl⟩ : syracuseStep 1716227 = 2574341) B2574341
theorem B6500357 : Blo 1140634 6500357 := bstep (se 4 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 6500357 = 1218817) B1218817
theorem B1716257 : Blo 1140634 1716257 := bstep (se 2 (by rfl) ⟨643596, by rfl⟩ : syracuseStep 1716257 = 1287193) B1287193
theorem B1716275 : Blo 1140634 1716275 := bstep (se 1 (by rfl) ⟨1287206, by rfl⟩ : syracuseStep 1716275 = 2574413) B2574413
theorem B1716305 : Blo 1140634 1716305 := bstep (se 2 (by rfl) ⟨643614, by rfl⟩ : syracuseStep 1716305 = 1287229) B1287229
theorem B1716323 : Blo 1140634 1716323 := bstep (se 1 (by rfl) ⟨1287242, by rfl⟩ : syracuseStep 1716323 = 2574485) B2574485
theorem B3256433 : Blo 1140634 3256433 := bstep (se 2 (by rfl) ⟨1221162, by rfl⟩ : syracuseStep 3256433 = 2442325) B2442325
theorem B3092593 : Blo 1140634 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B1716353 : Blo 1140634 1716353 := bstep (se 2 (by rfl) ⟨643632, by rfl⟩ : syracuseStep 1716353 = 1287265) B1287265
theorem B1716371 : Blo 1140634 1716371 := bstep (se 1 (by rfl) ⟨1287278, by rfl⟩ : syracuseStep 1716371 = 2574557) B2574557
theorem B1716401 : Blo 1140634 1716401 := bstep (se 2 (by rfl) ⟨643650, by rfl⟩ : syracuseStep 1716401 = 1287301) B1287301
theorem B1716419 : Blo 1140634 1716419 := bstep (se 1 (by rfl) ⟨1287314, by rfl⟩ : syracuseStep 1716419 = 2574629) B2574629
theorem B9253061 : Blo 1140634 9253061 := bstep (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) B1734949
theorem B2568401 : Blo 1140634 2568401 := bstep (se 2 (by rfl) ⟨963150, by rfl⟩ : syracuseStep 2568401 = 1926301) B1926301
theorem B1716449 : Blo 1140634 1716449 := bstep (se 2 (by rfl) ⟨643668, by rfl⟩ : syracuseStep 1716449 = 1287337) B1287337
theorem B2568419 : Blo 1140634 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B2437361 : Blo 1140634 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B1716467 : Blo 1140634 1716467 := bstep (se 1 (by rfl) ⟨1287350, by rfl⟩ : syracuseStep 1716467 = 2574701) B2574701
theorem B7319821 : Blo 1140634 7319821 := bstep (se 3 (by rfl) ⟨1372466, by rfl⟩ : syracuseStep 7319821 = 2744933) B2744933
theorem B2896145 : Blo 1140634 2896145 := bstep (se 2 (by rfl) ⟨1086054, by rfl⟩ : syracuseStep 2896145 = 2172109) B2172109
theorem B1716497 : Blo 1140634 1716497 := bstep (se 2 (by rfl) ⟨643686, by rfl⟩ : syracuseStep 1716497 = 1287373) B1287373
theorem B1716515 : Blo 1140634 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B3256625 : Blo 1140634 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B1716545 : Blo 1140634 1716545 := bstep (se 2 (by rfl) ⟨643704, by rfl⟩ : syracuseStep 1716545 = 1287409) B1287409
theorem B2896195 : Blo 1140634 2896195 := bstep (se 1 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 2896195 = 4344293) B4344293
theorem B1716563 : Blo 1140634 1716563 := bstep (se 1 (by rfl) ⟨1287422, by rfl⟩ : syracuseStep 1716563 = 2574845) B2574845
theorem B1716593 : Blo 1140634 1716593 := bstep (se 2 (by rfl) ⟨643722, by rfl⟩ : syracuseStep 1716593 = 1287445) B1287445
theorem B1716611 : Blo 1140634 1716611 := bstep (se 1 (by rfl) ⟨1287458, by rfl⟩ : syracuseStep 1716611 = 2574917) B2574917
theorem B46903693 : Blo 1140634 46903693 := bstep (se 3 (by rfl) ⟨8794442, by rfl⟩ : syracuseStep 46903693 = 17588885) B17588885
theorem B1716641 : Blo 1140634 1716641 := bstep (se 2 (by rfl) ⟨643740, by rfl⟩ : syracuseStep 1716641 = 1287481) B1287481
theorem B1716659 : Blo 1140634 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B2896337 : Blo 1140634 2896337 := bstep (se 2 (by rfl) ⟨1086126, by rfl⟩ : syracuseStep 2896337 = 2172253) B2172253
theorem B1716689 : Blo 1140634 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B1716707 : Blo 1140634 1716707 := bstep (se 1 (by rfl) ⟨1287530, by rfl⟩ : syracuseStep 1716707 = 2575061) B2575061
theorem B2568689 : Blo 1140634 2568689 := bstep (se 2 (by rfl) ⟨963258, by rfl⟩ : syracuseStep 2568689 = 1926517) B1926517
theorem B1716737 : Blo 1140634 1716737 := bstep (se 2 (by rfl) ⟨643776, by rfl⟩ : syracuseStep 1716737 = 1287553) B1287553
theorem B2568707 : Blo 1140634 2568707 := bstep (se 1 (by rfl) ⟨1926530, by rfl⟩ : syracuseStep 2568707 = 3853061) B3853061
theorem B1716755 : Blo 1140634 1716755 := bstep (se 1 (by rfl) ⟨1287566, by rfl⟩ : syracuseStep 1716755 = 2575133) B2575133
theorem B1716785 : Blo 1140634 1716785 := bstep (se 2 (by rfl) ⟨643794, by rfl⟩ : syracuseStep 1716785 = 1287589) B1287589
theorem B3912259 : Blo 1140634 3912259 := bstep (se 1 (by rfl) ⟨2934194, by rfl⟩ : syracuseStep 3912259 = 5868389) B5868389
theorem B1716803 : Blo 1140634 1716803 := bstep (se 1 (by rfl) ⟨1287602, by rfl⟩ : syracuseStep 1716803 = 2575205) B2575205
theorem B1716833 : Blo 1140634 1716833 := bstep (se 2 (by rfl) ⟨643812, by rfl⟩ : syracuseStep 1716833 = 1287625) B1287625
theorem B1716851 : Blo 1140634 1716851 := bstep (se 1 (by rfl) ⟨1287638, by rfl⟩ : syracuseStep 1716851 = 2575277) B2575277
theorem B1716881 : Blo 1140634 1716881 := bstep (se 2 (by rfl) ⟨643830, by rfl⟩ : syracuseStep 1716881 = 1287661) B1287661
theorem B1716899 : Blo 1140634 1716899 := bstep (se 1 (by rfl) ⟨1287674, by rfl⟩ : syracuseStep 1716899 = 2575349) B2575349
theorem B1716929 : Blo 1140634 1716929 := bstep (se 2 (by rfl) ⟨643848, by rfl⟩ : syracuseStep 1716929 = 1287697) B1287697
theorem B1716947 : Blo 1140634 1716947 := bstep (se 1 (by rfl) ⟨1287710, by rfl⟩ : syracuseStep 1716947 = 2575421) B2575421
theorem B2568977 : Blo 1140634 2568977 := bstep (se 2 (by rfl) ⟨963366, by rfl⟩ : syracuseStep 2568977 = 1926733) B1926733
theorem B2568995 : Blo 1140634 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B8663921 : Blo 1140634 8663921 := bstep (se 2 (by rfl) ⟨3248970, by rfl⟩ : syracuseStep 8663921 = 6497941) B6497941
theorem B2569265 : Blo 1140634 2569265 := bstep (se 2 (by rfl) ⟨963474, by rfl⟩ : syracuseStep 2569265 = 1926949) B1926949
theorem B2569283 : Blo 1140634 2569283 := bstep (se 1 (by rfl) ⟨1926962, by rfl⟩ : syracuseStep 2569283 = 3853925) B3853925
theorem B4633699 : Blo 1140634 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B9254029 : Blo 1140634 9254029 := bstep (se 3 (by rfl) ⟨1735130, by rfl⟩ : syracuseStep 9254029 = 3470261) B3470261
theorem B23442659 : Blo 1140634 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B12367075 : Blo 1140634 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B3257617 : Blo 1140634 3257617 := bstep (se 2 (by rfl) ⟨1221606, by rfl⟩ : syracuseStep 3257617 = 2443213) B2443213
theorem B2569553 : Blo 1140634 2569553 := bstep (se 2 (by rfl) ⟨963582, by rfl⟩ : syracuseStep 2569553 = 1927165) B1927165
theorem B1389907 : Blo 1140634 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B2569571 : Blo 1140634 2569571 := bstep (se 1 (by rfl) ⟨1927178, by rfl⟩ : syracuseStep 2569571 = 3854357) B3854357
theorem B2897329 : Blo 1140634 2897329 := bstep (se 2 (by rfl) ⟨1086498, by rfl⟩ : syracuseStep 2897329 = 2172997) B2172997
theorem B35173829 : Blo 1140634 35173829 := bstep (se 4 (by rfl) ⟨3297546, by rfl⟩ : syracuseStep 35173829 = 6595093) B6595093
theorem B3257891 : Blo 1140634 3257891 := bstep (se 1 (by rfl) ⟨2443418, by rfl⟩ : syracuseStep 3257891 = 4886837) B4886837
theorem B2569841 : Blo 1140634 2569841 := bstep (se 2 (by rfl) ⟨963690, by rfl⟩ : syracuseStep 2569841 = 1927381) B1927381
theorem B2569859 : Blo 1140634 2569859 := bstep (se 1 (by rfl) ⟨1927394, by rfl⟩ : syracuseStep 2569859 = 3854789) B3854789
theorem B3913379 : Blo 1140634 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B3258083 : Blo 1140634 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B2438915 : Blo 1140634 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B13186957 : Blo 1140634 13186957 := bstep (se 3 (by rfl) ⟨2472554, by rfl⟩ : syracuseStep 13186957 = 4945109) B4945109
theorem B2570129 : Blo 1140634 2570129 := bstep (se 2 (by rfl) ⟨963798, by rfl⟩ : syracuseStep 2570129 = 1927597) B1927597
theorem B2570147 : Blo 1140634 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B12335075 : Blo 1140634 12335075 := bstep (se 1 (by rfl) ⟨9251306, by rfl⟩ : syracuseStep 12335075 = 18502613) B18502613
theorem B5781617 : Blo 1140634 5781617 := bstep (se 2 (by rfl) ⟨2168106, by rfl⟩ : syracuseStep 5781617 = 4336213) B4336213
theorem B2570417 : Blo 1140634 2570417 := bstep (se 2 (by rfl) ⟨963906, by rfl⟩ : syracuseStep 2570417 = 1927813) B1927813
theorem B4339889 : Blo 1140634 4339889 := bstep (se 2 (by rfl) ⟨1627458, by rfl⟩ : syracuseStep 4339889 = 3254917) B3254917
theorem B2570435 : Blo 1140634 2570435 := bstep (se 1 (by rfl) ⟨1927826, by rfl⟩ : syracuseStep 2570435 = 3855653) B3855653
theorem B2570705 : Blo 1140634 2570705 := bstep (se 2 (by rfl) ⟨964014, by rfl⟩ : syracuseStep 2570705 = 1928029) B1928029
theorem B2570723 : Blo 1140634 2570723 := bstep (se 1 (by rfl) ⟨1928042, by rfl⟩ : syracuseStep 2570723 = 3856085) B3856085
theorem B3258893 : Blo 1140634 3258893 := bstep (se 3 (by rfl) ⟨611042, by rfl⟩ : syracuseStep 3258893 = 1222085) B1222085
theorem B3259075 : Blo 1140634 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B2570993 : Blo 1140634 2570993 := bstep (se 2 (by rfl) ⟨964122, by rfl⟩ : syracuseStep 2570993 = 1928245) B1928245
theorem B2571011 : Blo 1140634 2571011 := bstep (se 1 (by rfl) ⟨1928258, by rfl⟩ : syracuseStep 2571011 = 3856517) B3856517
theorem B7519237 : Blo 1140634 7519237 := bstep (se 4 (by rfl) ⟨704928, by rfl⟩ : syracuseStep 7519237 = 1409857) B1409857
theorem B2571281 : Blo 1140634 2571281 := bstep (se 2 (by rfl) ⟨964230, by rfl⟩ : syracuseStep 2571281 = 1928461) B1928461
theorem B2571299 : Blo 1140634 2571299 := bstep (se 1 (by rfl) ⟨1928474, by rfl⟩ : syracuseStep 2571299 = 3856949) B3856949
theorem B1719443 : Blo 1140634 1719443 := bstep (se 1 (by rfl) ⟨1289582, by rfl⟩ : syracuseStep 1719443 = 2579165) B2579165
theorem B2571569 : Blo 1140634 2571569 := bstep (se 2 (by rfl) ⟨964338, by rfl⟩ : syracuseStep 2571569 = 1928677) B1928677
theorem B2571587 : Blo 1140634 2571587 := bstep (se 1 (by rfl) ⟨1928690, by rfl⟩ : syracuseStep 2571587 = 3857381) B3857381
theorem B3849713 : Blo 1140634 3849713 := bstep (se 2 (by rfl) ⟨1443642, by rfl⟩ : syracuseStep 3849713 = 2887285) B2887285
theorem B13876721 : Blo 1140634 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B5783075 : Blo 1140634 5783075 := bstep (se 1 (by rfl) ⟨4337306, by rfl⟩ : syracuseStep 5783075 = 8674613) B8674613
theorem B2571857 : Blo 1140634 2571857 := bstep (se 2 (by rfl) ⟨964446, by rfl⟩ : syracuseStep 2571857 = 1928893) B1928893
theorem B2571875 : Blo 1140634 2571875 := bstep (se 1 (by rfl) ⟨1928906, by rfl⟩ : syracuseStep 2571875 = 3857813) B3857813
theorem B4341347 : Blo 1140634 4341347 := bstep (se 1 (by rfl) ⟨3256010, by rfl⟩ : syracuseStep 4341347 = 6512021) B6512021
theorem B10993265 : Blo 1140634 10993265 := bstep (se 2 (by rfl) ⟨4122474, by rfl⟩ : syracuseStep 10993265 = 8244949) B8244949
theorem B27836045 : Blo 1140634 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B10043149 : Blo 1140634 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B2572145 : Blo 1140634 2572145 := bstep (se 2 (by rfl) ⟨964554, by rfl⟩ : syracuseStep 2572145 = 1929109) B1929109
theorem B2572163 : Blo 1140634 2572163 := bstep (se 1 (by rfl) ⟨1929122, by rfl⟩ : syracuseStep 2572163 = 3858245) B3858245
theorem B2441137 : Blo 1140634 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B14860273 : Blo 1140634 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B3850253 : Blo 1140634 3850253 := bstep (se 3 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 3850253 = 1443845) B1443845
theorem B3850307 : Blo 1140634 3850307 := bstep (se 1 (by rfl) ⟨2887730, by rfl⟩ : syracuseStep 3850307 = 5775461) B5775461
theorem B2572433 : Blo 1140634 2572433 := bstep (se 2 (by rfl) ⟨964662, by rfl⟩ : syracuseStep 2572433 = 1929325) B1929325
theorem B3293347 : Blo 1140634 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B2572451 : Blo 1140634 2572451 := bstep (se 1 (by rfl) ⟨1929338, by rfl⟩ : syracuseStep 2572451 = 3858677) B3858677
theorem B5783885 : Blo 1140634 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B3850577 : Blo 1140634 3850577 := bstep (se 2 (by rfl) ⟨1443966, by rfl⟩ : syracuseStep 3850577 = 2887933) B2887933
theorem B2572721 : Blo 1140634 2572721 := bstep (se 2 (by rfl) ⟨964770, by rfl⟩ : syracuseStep 2572721 = 1929541) B1929541
theorem B2572739 : Blo 1140634 2572739 := bstep (se 1 (by rfl) ⟨1929554, by rfl⟩ : syracuseStep 2572739 = 3859109) B3859109
theorem B4342349 : Blo 1140634 4342349 := bstep (se 3 (by rfl) ⟨814190, by rfl⟩ : syracuseStep 4342349 = 1628381) B1628381
theorem B5489329 : Blo 1140634 5489329 := bstep (se 2 (by rfl) ⟨2058498, by rfl⟩ : syracuseStep 5489329 = 4116997) B4116997
theorem B6177485 : Blo 1140634 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B2573009 : Blo 1140634 2573009 := bstep (se 2 (by rfl) ⟨964878, by rfl⟩ : syracuseStep 2573009 = 1929757) B1929757
theorem B2573027 : Blo 1140634 2573027 := bstep (se 1 (by rfl) ⟨1929770, by rfl⟩ : syracuseStep 2573027 = 3859541) B3859541
theorem B3654467 : Blo 1140634 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B3851117 : Blo 1140634 3851117 := bstep (se 3 (by rfl) ⟨722084, by rfl⟩ : syracuseStep 3851117 = 1444169) B1444169
theorem B3851171 : Blo 1140634 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B2573297 : Blo 1140634 2573297 := bstep (se 2 (by rfl) ⟨964986, by rfl⟩ : syracuseStep 2573297 = 1929973) B1929973
theorem B2573315 : Blo 1140634 2573315 := bstep (se 1 (by rfl) ⟨1929986, by rfl⟩ : syracuseStep 2573315 = 3859973) B3859973
theorem B9290821 : Blo 1140634 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B3851441 : Blo 1140634 3851441 := bstep (se 2 (by rfl) ⟨1444290, by rfl⟩ : syracuseStep 3851441 = 2888581) B2888581
theorem B11879693 : Blo 1140634 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B2573585 : Blo 1140634 2573585 := bstep (se 2 (by rfl) ⟨965094, by rfl⟩ : syracuseStep 2573585 = 1930189) B1930189
theorem B2573603 : Blo 1140634 2573603 := bstep (se 1 (by rfl) ⟨1930202, by rfl⟩ : syracuseStep 2573603 = 3860405) B3860405
theorem B2573873 : Blo 1140634 2573873 := bstep (se 2 (by rfl) ⟨965202, by rfl⟩ : syracuseStep 2573873 = 1930405) B1930405
theorem B2573891 : Blo 1140634 2573891 := bstep (se 1 (by rfl) ⟨1930418, by rfl⟩ : syracuseStep 2573891 = 3860837) B3860837
theorem B3851981 : Blo 1140634 3851981 := bstep (se 3 (by rfl) ⟨722246, by rfl⟩ : syracuseStep 3851981 = 1444493) B1444493
theorem B6506189 : Blo 1140634 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B7128803 : Blo 1140634 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B3852035 : Blo 1140634 3852035 := bstep (se 1 (by rfl) ⟨2889026, by rfl⟩ : syracuseStep 3852035 = 5778053) B5778053
theorem B6178609 : Blo 1140634 6178609 := bstep (se 2 (by rfl) ⟨2316978, by rfl⟩ : syracuseStep 6178609 = 4633957) B4633957
theorem B2574161 : Blo 1140634 2574161 := bstep (se 2 (by rfl) ⟨965310, by rfl⟩ : syracuseStep 2574161 = 1930621) B1930621
theorem B2574179 : Blo 1140634 2574179 := bstep (se 1 (by rfl) ⟨1930634, by rfl⟩ : syracuseStep 2574179 = 3861269) B3861269
theorem B3852305 : Blo 1140634 3852305 := bstep (se 2 (by rfl) ⟨1444614, by rfl⟩ : syracuseStep 3852305 = 2889229) B2889229
theorem B3295331 : Blo 1140634 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2574449 : Blo 1140634 2574449 := bstep (se 2 (by rfl) ⟨965418, by rfl⟩ : syracuseStep 2574449 = 1930837) B1930837
theorem B2574467 : Blo 1140634 2574467 := bstep (se 1 (by rfl) ⟨1930850, by rfl⟩ : syracuseStep 2574467 = 3861701) B3861701
theorem B1853585 : Blo 1140634 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B7817477 : Blo 1140634 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B1952131 : Blo 1140634 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B2574737 : Blo 1140634 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B2574755 : Blo 1140634 2574755 := bstep (se 1 (by rfl) ⟨1931066, by rfl⟩ : syracuseStep 2574755 = 3862133) B3862133
theorem B1624531 : Blo 1140634 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B1952291 : Blo 1140634 1952291 := bstep (se 1 (by rfl) ⟨1464218, by rfl⟩ : syracuseStep 1952291 = 2928437) B2928437
theorem B3852845 : Blo 1140634 3852845 := bstep (se 3 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 3852845 = 1444817) B1444817
theorem B3852899 : Blo 1140634 3852899 := bstep (se 1 (by rfl) ⟨2889674, by rfl⟩ : syracuseStep 3852899 = 5779349) B5779349
theorem B8342129 : Blo 1140634 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B4344461 : Blo 1140634 4344461 := bstep (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) B1629173
theorem B2575025 : Blo 1140634 2575025 := bstep (se 2 (by rfl) ⟨965634, by rfl⟩ : syracuseStep 2575025 = 1931269) B1931269
theorem B2575043 : Blo 1140634 2575043 := bstep (se 1 (by rfl) ⟨1931282, by rfl⟩ : syracuseStep 2575043 = 3862565) B3862565
theorem B2345699 : Blo 1140634 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B3853169 : Blo 1140634 3853169 := bstep (se 2 (by rfl) ⟨1444938, by rfl⟩ : syracuseStep 3853169 = 2889877) B2889877
theorem B2444195 : Blo 1140634 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B3656657 : Blo 1140634 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B2575313 : Blo 1140634 2575313 := bstep (se 2 (by rfl) ⟨965742, by rfl⟩ : syracuseStep 2575313 = 1931485) B1931485
theorem B2575331 : Blo 1140634 2575331 := bstep (se 1 (by rfl) ⟨1931498, by rfl⟩ : syracuseStep 2575331 = 3862997) B3862997
theorem B3656785 : Blo 1140634 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B5786801 : Blo 1140634 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B3657041 : Blo 1140634 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B3853709 : Blo 1140634 3853709 := bstep (se 3 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 3853709 = 1445141) B1445141
theorem B4345265 : Blo 1140634 4345265 := bstep (se 2 (by rfl) ⟨1629474, by rfl⟩ : syracuseStep 4345265 = 3258949) B3258949
theorem B3853763 : Blo 1140634 3853763 := bstep (se 1 (by rfl) ⟨2890322, by rfl⟩ : syracuseStep 3853763 = 5780645) B5780645
theorem B10407365 : Blo 1140634 10407365 := bstep (se 4 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 10407365 = 1951381) B1951381
theorem B1625665 : Blo 1140634 1625665 := bstep (se 2 (by rfl) ⟨609624, by rfl⟩ : syracuseStep 1625665 = 1219249) B1219249
theorem B1625761 : Blo 1140634 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B3854033 : Blo 1140634 3854033 := bstep (se 2 (by rfl) ⟨1445262, by rfl⟩ : syracuseStep 3854033 = 2890525) B2890525
theorem B6508421 : Blo 1140634 6508421 := bstep (se 4 (by rfl) ⟨610164, by rfl⟩ : syracuseStep 6508421 = 1220329) B1220329
theorem B1953857 : Blo 1140634 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B4345933 : Blo 1140634 4345933 := bstep (se 3 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 4345933 = 1629725) B1629725
theorem B1626257 : Blo 1140634 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B3854573 : Blo 1140634 3854573 := bstep (se 3 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 3854573 = 1445465) B1445465
theorem B3854627 : Blo 1140634 3854627 := bstep (se 1 (by rfl) ⟨2890970, by rfl⟩ : syracuseStep 3854627 = 5781941) B5781941
theorem B7328227 : Blo 1140634 7328227 := bstep (se 1 (by rfl) ⟨5496170, by rfl⟩ : syracuseStep 7328227 = 10992341) B10992341
theorem B3854897 : Blo 1140634 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B6509105 : Blo 1140634 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B10998341 : Blo 1140634 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B5788259 : Blo 1140634 5788259 := bstep (se 1 (by rfl) ⟨4341194, by rfl⟩ : syracuseStep 5788259 = 8682389) B8682389
theorem B2314993 : Blo 1140634 2314993 := bstep (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) B1736245
theorem B2609923 : Blo 1140634 2609923 := bstep (se 1 (by rfl) ⟨1957442, by rfl⟩ : syracuseStep 2609923 = 3914885) B3914885
theorem B3658733 : Blo 1140634 3658733 := bstep (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) B1372025
theorem B8803313 : Blo 1140634 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B1627123 : Blo 1140634 1627123 := bstep (se 1 (by rfl) ⟨1220342, by rfl⟩ : syracuseStep 1627123 = 2440685) B2440685
theorem B1758275 : Blo 1140634 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B3855437 : Blo 1140634 3855437 := bstep (se 3 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 3855437 = 1445789) B1445789
theorem B1627219 : Blo 1140634 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B3855491 : Blo 1140634 3855491 := bstep (se 1 (by rfl) ⟨2891618, by rfl⟩ : syracuseStep 3855491 = 5783237) B5783237
theorem B5789069 : Blo 1140634 5789069 := bstep (se 3 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 5789069 = 2170901) B2170901
theorem B3855761 : Blo 1140634 3855761 := bstep (se 2 (by rfl) ⟨1445910, by rfl⟩ : syracuseStep 3855761 = 2891821) B2891821
theorem B12998069 : Blo 1140634 12998069 := bstep (se 5 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 12998069 = 1218569) B1218569
theorem B1955281 : Blo 1140634 1955281 := bstep (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) B1466461
theorem B1627715 : Blo 1140634 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B7329457 : Blo 1140634 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B14636771 : Blo 1140634 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B3659501 : Blo 1140634 3659501 := bstep (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) B1372313
theorem B3856301 : Blo 1140634 3856301 := bstep (se 3 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 3856301 = 1446113) B1446113
theorem B3856355 : Blo 1140634 3856355 := bstep (se 1 (by rfl) ⟨2892266, by rfl⟩ : syracuseStep 3856355 = 5784533) B5784533
theorem B6510563 : Blo 1140634 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B1628353 : Blo 1140634 1628353 := bstep (se 2 (by rfl) ⟨610632, by rfl⟩ : syracuseStep 1628353 = 1221265) B1221265
theorem B2349283 : Blo 1140634 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B3660013 : Blo 1140634 3660013 := bstep (se 3 (by rfl) ⟨686252, by rfl⟩ : syracuseStep 3660013 = 1372505) B1372505
theorem B3856625 : Blo 1140634 3856625 := bstep (se 2 (by rfl) ⟨1446234, by rfl⟩ : syracuseStep 3856625 = 2892469) B2892469
theorem B1628689 : Blo 1140634 1628689 := bstep (se 2 (by rfl) ⟨610758, by rfl⟩ : syracuseStep 1628689 = 1221517) B1221517
theorem B2316899 : Blo 1140634 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B9394829 : Blo 1140634 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B3660515 : Blo 1140634 3660515 := bstep (se 1 (by rfl) ⟨2745386, by rfl⟩ : syracuseStep 3660515 = 5490773) B5490773
theorem B3857165 : Blo 1140634 3857165 := bstep (se 3 (by rfl) ⟨723218, by rfl⟩ : syracuseStep 3857165 = 1446437) B1446437
theorem B1563425 : Blo 1140634 1563425 := bstep (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) B1172569
theorem B3857219 : Blo 1140634 3857219 := bstep (se 1 (by rfl) ⟨2892914, by rfl⟩ : syracuseStep 3857219 = 5785829) B5785829
theorem B3300401 : Blo 1140634 3300401 := bstep (se 2 (by rfl) ⟨1237650, by rfl⟩ : syracuseStep 3300401 = 2475301) B2475301
theorem B3857489 : Blo 1140634 3857489 := bstep (se 2 (by rfl) ⟨1446558, by rfl⟩ : syracuseStep 3857489 = 2893117) B2893117
theorem B1629281 : Blo 1140634 1629281 := bstep (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) B1221961
theorem B3858029 : Blo 1140634 3858029 := bstep (se 3 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 3858029 = 1446761) B1446761
theorem B3858083 : Blo 1140634 3858083 := bstep (se 1 (by rfl) ⟨2893562, by rfl⟩ : syracuseStep 3858083 = 5787125) B5787125
theorem B1924897 : Blo 1140634 1924897 := bstep (se 2 (by rfl) ⟨721836, by rfl⟩ : syracuseStep 1924897 = 1443673) B1443673
theorem B1924931 : Blo 1140634 1924931 := bstep (se 1 (by rfl) ⟨1443698, by rfl⟩ : syracuseStep 1924931 = 2887397) B2887397
theorem B2056099 : Blo 1140634 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B1466275 : Blo 1140634 1466275 := bstep (se 1 (by rfl) ⟨1099706, by rfl⟩ : syracuseStep 1466275 = 2199413) B2199413
theorem B3858353 : Blo 1140634 3858353 := bstep (se 2 (by rfl) ⟨1446882, by rfl⟩ : syracuseStep 3858353 = 2893765) B2893765
theorem B1925059 : Blo 1140634 1925059 := bstep (se 1 (by rfl) ⟨1443794, by rfl⟩ : syracuseStep 1925059 = 2887589) B2887589
theorem B1957873 : Blo 1140634 1957873 := bstep (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) B1468405
theorem B1466435 : Blo 1140634 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1925201 : Blo 1140634 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B27779213 : Blo 1140634 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B1925329 : Blo 1140634 1925329 := bstep (se 2 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 1925329 = 1443997) B1443997
theorem B13197539 : Blo 1140634 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B5791985 : Blo 1140634 5791985 := bstep (se 2 (by rfl) ⟨2171994, by rfl⟩ : syracuseStep 5791985 = 4343989) B4343989
theorem B1925363 : Blo 1140634 1925363 := bstep (se 1 (by rfl) ⟨1444022, by rfl⟩ : syracuseStep 1925363 = 2888045) B2888045
theorem B6185315 : Blo 1140634 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B1925491 : Blo 1140634 1925491 := bstep (se 1 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 1925491 = 2888237) B2888237
theorem B3858893 : Blo 1140634 3858893 := bstep (se 3 (by rfl) ⟨723542, by rfl⟩ : syracuseStep 3858893 = 1447085) B1447085
theorem B1925633 : Blo 1140634 1925633 := bstep (se 2 (by rfl) ⟨722112, by rfl⟩ : syracuseStep 1925633 = 1444225) B1444225
theorem B3858947 : Blo 1140634 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B3662371 : Blo 1140634 3662371 := bstep (se 1 (by rfl) ⟨2746778, by rfl⟩ : syracuseStep 3662371 = 5493557) B5493557
theorem B1925761 : Blo 1140634 1925761 := bstep (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) B1444321
theorem B1925795 : Blo 1140634 1925795 := bstep (se 1 (by rfl) ⟨1444346, by rfl⟩ : syracuseStep 1925795 = 2888693) B2888693
theorem B26731235 : Blo 1140634 26731235 := bstep (se 1 (by rfl) ⟨20048426, by rfl⟩ : syracuseStep 26731235 = 40096853) B40096853
theorem B8250083 : Blo 1140634 8250083 := bstep (se 1 (by rfl) ⟨6187562, by rfl⟩ : syracuseStep 8250083 = 12375125) B12375125
theorem B3859217 : Blo 1140634 3859217 := bstep (se 2 (by rfl) ⟨1447206, by rfl⟩ : syracuseStep 3859217 = 2894413) B2894413
theorem B1925923 : Blo 1140634 1925923 := bstep (se 1 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 1925923 = 2888885) B2888885
theorem B1172323 : Blo 1140634 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B1926065 : Blo 1140634 1926065 := bstep (se 2 (by rfl) ⟨722274, by rfl⟩ : syracuseStep 1926065 = 1444549) B1444549
theorem B3662833 : Blo 1140634 3662833 := bstep (se 2 (by rfl) ⟨1373562, by rfl⟩ : syracuseStep 3662833 = 2747125) B2747125
theorem B1926193 : Blo 1140634 1926193 := bstep (se 2 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 1926193 = 1444645) B1444645
theorem B1827905 : Blo 1140634 1827905 := bstep (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) B1370929
theorem B1926227 : Blo 1140634 1926227 := bstep (se 1 (by rfl) ⟨1444670, by rfl⟩ : syracuseStep 1926227 = 2889341) B2889341
theorem B6513797 : Blo 1140634 6513797 := bstep (se 4 (by rfl) ⟨610668, by rfl⟩ : syracuseStep 6513797 = 1221337) B1221337
theorem B1926355 : Blo 1140634 1926355 := bstep (se 1 (by rfl) ⟨1444766, by rfl⟩ : syracuseStep 1926355 = 2889533) B2889533
theorem B4875491 : Blo 1140634 4875491 := bstep (se 1 (by rfl) ⟨3656618, by rfl⟩ : syracuseStep 4875491 = 7313237) B7313237
theorem B7628017 : Blo 1140634 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3859757 : Blo 1140634 3859757 := bstep (se 3 (by rfl) ⟨723704, by rfl⟩ : syracuseStep 3859757 = 1447409) B1447409
theorem B1926497 : Blo 1140634 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B3859811 : Blo 1140634 3859811 := bstep (se 1 (by rfl) ⟨2894858, by rfl⟩ : syracuseStep 3859811 = 5789717) B5789717
theorem B7333253 : Blo 1140634 7333253 := bstep (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) B1374985
theorem B1926625 : Blo 1140634 1926625 := bstep (se 2 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 1926625 = 1444969) B1444969
theorem B1926659 : Blo 1140634 1926659 := bstep (se 1 (by rfl) ⟨1444994, by rfl⟩ : syracuseStep 1926659 = 2889989) B2889989
theorem B6514253 : Blo 1140634 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B20866673 : Blo 1140634 20866673 := bstep (se 2 (by rfl) ⟨7825002, by rfl⟩ : syracuseStep 20866673 = 15650005) B15650005
theorem B3860081 : Blo 1140634 3860081 := bstep (se 2 (by rfl) ⟨1447530, by rfl⟩ : syracuseStep 3860081 = 2895061) B2895061
theorem B1926787 : Blo 1140634 1926787 := bstep (se 1 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 1926787 = 2890181) B2890181
theorem B2746001 : Blo 1140634 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B5793443 : Blo 1140634 5793443 := bstep (se 1 (by rfl) ⟨4345082, by rfl⟩ : syracuseStep 5793443 = 8690165) B8690165
theorem B1926929 : Blo 1140634 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B1828739 : Blo 1140634 1828739 := bstep (se 1 (by rfl) ⟨1371554, by rfl⟩ : syracuseStep 1828739 = 2743109) B2743109
theorem B1927057 : Blo 1140634 1927057 := bstep (se 2 (by rfl) ⟨722646, by rfl⟩ : syracuseStep 1927057 = 1445293) B1445293
theorem B1140643 : Blo 1140634 1140643 := bstep (se 1 (by rfl) ⟨855482, by rfl⟩ : syracuseStep 1140643 = 1710965) B1710965
theorem B1140659 : Blo 1140634 1140659 := bstep (se 1 (by rfl) ⟨855494, by rfl⟩ : syracuseStep 1140659 = 1710989) B1710989
theorem B1927091 : Blo 1140634 1927091 := bstep (se 1 (by rfl) ⟨1445318, by rfl⟩ : syracuseStep 1927091 = 2890637) B2890637
theorem B1140675 : Blo 1140634 1140675 := bstep (se 1 (by rfl) ⟨855506, by rfl⟩ : syracuseStep 1140675 = 1711013) B1711013
theorem B1140691 : Blo 1140634 1140691 := bstep (se 1 (by rfl) ⟨855518, by rfl⟩ : syracuseStep 1140691 = 1711037) B1711037
theorem B1140707 : Blo 1140634 1140707 := bstep (se 1 (by rfl) ⟨855530, by rfl⟩ : syracuseStep 1140707 = 1711061) B1711061
theorem B1140723 : Blo 1140634 1140723 := bstep (se 1 (by rfl) ⟨855542, by rfl⟩ : syracuseStep 1140723 = 1711085) B1711085
theorem B1140739 : Blo 1140634 1140739 := bstep (se 1 (by rfl) ⟨855554, by rfl⟩ : syracuseStep 1140739 = 1711109) B1711109
theorem B1140755 : Blo 1140634 1140755 := bstep (se 1 (by rfl) ⟨855566, by rfl⟩ : syracuseStep 1140755 = 1711133) B1711133
theorem B1140771 : Blo 1140634 1140771 := bstep (se 1 (by rfl) ⟨855578, by rfl⟩ : syracuseStep 1140771 = 1711157) B1711157
theorem B1140787 : Blo 1140634 1140787 := bstep (se 1 (by rfl) ⟨855590, by rfl⟩ : syracuseStep 1140787 = 1711181) B1711181
theorem B1927219 : Blo 1140634 1927219 := bstep (se 1 (by rfl) ⟨1445414, by rfl⟩ : syracuseStep 1927219 = 2890829) B2890829
theorem B1140803 : Blo 1140634 1140803 := bstep (se 1 (by rfl) ⟨855602, by rfl⟩ : syracuseStep 1140803 = 1711205) B1711205
theorem B2680913 : Blo 1140634 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B1140819 : Blo 1140634 1140819 := bstep (se 1 (by rfl) ⟨855614, by rfl⟩ : syracuseStep 1140819 = 1711229) B1711229
theorem B1140835 : Blo 1140634 1140835 := bstep (se 1 (by rfl) ⟨855626, by rfl⟩ : syracuseStep 1140835 = 1711253) B1711253
theorem B1140851 : Blo 1140634 1140851 := bstep (se 1 (by rfl) ⟨855638, by rfl⟩ : syracuseStep 1140851 = 1711277) B1711277
theorem B1140867 : Blo 1140634 1140867 := bstep (se 1 (by rfl) ⟨855650, by rfl⟩ : syracuseStep 1140867 = 1711301) B1711301
theorem B3860621 : Blo 1140634 3860621 := bstep (se 3 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 3860621 = 1447733) B1447733
theorem B1140883 : Blo 1140634 1140883 := bstep (se 1 (by rfl) ⟨855662, by rfl⟩ : syracuseStep 1140883 = 1711325) B1711325
theorem B1140899 : Blo 1140634 1140899 := bstep (se 1 (by rfl) ⟨855674, by rfl⟩ : syracuseStep 1140899 = 1711349) B1711349
theorem B1829027 : Blo 1140634 1829027 := bstep (se 1 (by rfl) ⟨1371770, by rfl⟩ : syracuseStep 1829027 = 2743541) B2743541
theorem B1140915 : Blo 1140634 1140915 := bstep (se 1 (by rfl) ⟨855686, by rfl⟩ : syracuseStep 1140915 = 1711373) B1711373
theorem B1927361 : Blo 1140634 1927361 := bstep (se 2 (by rfl) ⟨722760, by rfl⟩ : syracuseStep 1927361 = 1445521) B1445521
theorem B1140931 : Blo 1140634 1140931 := bstep (se 1 (by rfl) ⟨855698, by rfl⟩ : syracuseStep 1140931 = 1711397) B1711397
theorem B3860675 : Blo 1140634 3860675 := bstep (se 1 (by rfl) ⟨2895506, by rfl⟩ : syracuseStep 3860675 = 5791013) B5791013
theorem B1140947 : Blo 1140634 1140947 := bstep (se 1 (by rfl) ⟨855710, by rfl⟩ : syracuseStep 1140947 = 1711421) B1711421
theorem B1140963 : Blo 1140634 1140963 := bstep (se 1 (by rfl) ⟨855722, by rfl⟩ : syracuseStep 1140963 = 1711445) B1711445
theorem B1140979 : Blo 1140634 1140979 := bstep (se 1 (by rfl) ⟨855734, by rfl⟩ : syracuseStep 1140979 = 1711469) B1711469
theorem B1140995 : Blo 1140634 1140995 := bstep (se 1 (by rfl) ⟨855746, by rfl⟩ : syracuseStep 1140995 = 1711493) B1711493
theorem B1141011 : Blo 1140634 1141011 := bstep (se 1 (by rfl) ⟨855758, by rfl⟩ : syracuseStep 1141011 = 1711517) B1711517
theorem B1141027 : Blo 1140634 1141027 := bstep (se 1 (by rfl) ⟨855770, by rfl⟩ : syracuseStep 1141027 = 1711541) B1711541
theorem B1141043 : Blo 1140634 1141043 := bstep (se 1 (by rfl) ⟨855782, by rfl⟩ : syracuseStep 1141043 = 1711565) B1711565
theorem B1927489 : Blo 1140634 1927489 := bstep (se 2 (by rfl) ⟨722808, by rfl⟩ : syracuseStep 1927489 = 1445617) B1445617
theorem B1141059 : Blo 1140634 1141059 := bstep (se 1 (by rfl) ⟨855794, by rfl⟩ : syracuseStep 1141059 = 1711589) B1711589
theorem B1141075 : Blo 1140634 1141075 := bstep (se 1 (by rfl) ⟨855806, by rfl⟩ : syracuseStep 1141075 = 1711613) B1711613
theorem B1141091 : Blo 1140634 1141091 := bstep (se 1 (by rfl) ⟨855818, by rfl⟩ : syracuseStep 1141091 = 1711637) B1711637
theorem B1927523 : Blo 1140634 1927523 := bstep (se 1 (by rfl) ⟨1445642, by rfl⟩ : syracuseStep 1927523 = 2891285) B2891285
theorem B1141107 : Blo 1140634 1141107 := bstep (se 1 (by rfl) ⟨855830, by rfl⟩ : syracuseStep 1141107 = 1711661) B1711661
theorem B1141123 : Blo 1140634 1141123 := bstep (se 1 (by rfl) ⟨855842, by rfl⟩ : syracuseStep 1141123 = 1711685) B1711685
theorem B1829251 : Blo 1140634 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1141139 : Blo 1140634 1141139 := bstep (se 1 (by rfl) ⟨855854, by rfl⟩ : syracuseStep 1141139 = 1711709) B1711709
theorem B1141155 : Blo 1140634 1141155 := bstep (se 1 (by rfl) ⟨855866, by rfl⟩ : syracuseStep 1141155 = 1711733) B1711733
theorem B1141171 : Blo 1140634 1141171 := bstep (se 1 (by rfl) ⟨855878, by rfl⟩ : syracuseStep 1141171 = 1711757) B1711757
theorem B1141187 : Blo 1140634 1141187 := bstep (se 1 (by rfl) ⟨855890, by rfl⟩ : syracuseStep 1141187 = 1711781) B1711781
theorem B5794253 : Blo 1140634 5794253 := bstep (se 3 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 5794253 = 2172845) B2172845
theorem B3860945 : Blo 1140634 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B1141203 : Blo 1140634 1141203 := bstep (se 1 (by rfl) ⟨855902, by rfl⟩ : syracuseStep 1141203 = 1711805) B1711805
theorem B1141219 : Blo 1140634 1141219 := bstep (se 1 (by rfl) ⟨855914, by rfl⟩ : syracuseStep 1141219 = 1711829) B1711829
theorem B1927651 : Blo 1140634 1927651 := bstep (se 1 (by rfl) ⟨1445738, by rfl⟩ : syracuseStep 1927651 = 2891477) B2891477
theorem B1141235 : Blo 1140634 1141235 := bstep (se 1 (by rfl) ⟨855926, by rfl⟩ : syracuseStep 1141235 = 1711853) B1711853
theorem B1141251 : Blo 1140634 1141251 := bstep (se 1 (by rfl) ⟨855938, by rfl⟩ : syracuseStep 1141251 = 1711877) B1711877
theorem B1141267 : Blo 1140634 1141267 := bstep (se 1 (by rfl) ⟨855950, by rfl⟩ : syracuseStep 1141267 = 1711901) B1711901
theorem B1141283 : Blo 1140634 1141283 := bstep (se 1 (by rfl) ⟨855962, by rfl⟩ : syracuseStep 1141283 = 1711925) B1711925
theorem B2058787 : Blo 1140634 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1141299 : Blo 1140634 1141299 := bstep (se 1 (by rfl) ⟨855974, by rfl⟩ : syracuseStep 1141299 = 1711949) B1711949
theorem B1141315 : Blo 1140634 1141315 := bstep (se 1 (by rfl) ⟨855986, by rfl⟩ : syracuseStep 1141315 = 1711973) B1711973
theorem B1141331 : Blo 1140634 1141331 := bstep (se 1 (by rfl) ⟨855998, by rfl⟩ : syracuseStep 1141331 = 1711997) B1711997
theorem B1141347 : Blo 1140634 1141347 := bstep (se 1 (by rfl) ⟨856010, by rfl⟩ : syracuseStep 1141347 = 1712021) B1712021
theorem B1927793 : Blo 1140634 1927793 := bstep (se 2 (by rfl) ⟨722922, by rfl⟩ : syracuseStep 1927793 = 1445845) B1445845
theorem B1141363 : Blo 1140634 1141363 := bstep (se 1 (by rfl) ⟨856022, by rfl⟩ : syracuseStep 1141363 = 1712045) B1712045
theorem B1141379 : Blo 1140634 1141379 := bstep (se 1 (by rfl) ⟨856034, by rfl⟩ : syracuseStep 1141379 = 1712069) B1712069
theorem B1141395 : Blo 1140634 1141395 := bstep (se 1 (by rfl) ⟨856046, by rfl⟩ : syracuseStep 1141395 = 1712093) B1712093
theorem B1141411 : Blo 1140634 1141411 := bstep (se 1 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 1141411 = 1712117) B1712117
theorem B1141427 : Blo 1140634 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B1141443 : Blo 1140634 1141443 := bstep (se 1 (by rfl) ⟨856082, by rfl⟩ : syracuseStep 1141443 = 1712165) B1712165
theorem B1141459 : Blo 1140634 1141459 := bstep (se 1 (by rfl) ⟨856094, by rfl⟩ : syracuseStep 1141459 = 1712189) B1712189
theorem B1141475 : Blo 1140634 1141475 := bstep (se 1 (by rfl) ⟨856106, by rfl⟩ : syracuseStep 1141475 = 1712213) B1712213
theorem B1927921 : Blo 1140634 1927921 := bstep (se 2 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 1927921 = 1445941) B1445941
theorem B1141491 : Blo 1140634 1141491 := bstep (se 1 (by rfl) ⟨856118, by rfl⟩ : syracuseStep 1141491 = 1712237) B1712237
theorem B1141507 : Blo 1140634 1141507 := bstep (se 1 (by rfl) ⟨856130, by rfl⟩ : syracuseStep 1141507 = 1712261) B1712261
theorem B1141523 : Blo 1140634 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B1927955 : Blo 1140634 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1141539 : Blo 1140634 1141539 := bstep (se 1 (by rfl) ⟨856154, by rfl⟩ : syracuseStep 1141539 = 1712309) B1712309
theorem B1141555 : Blo 1140634 1141555 := bstep (se 1 (by rfl) ⟨856166, by rfl⟩ : syracuseStep 1141555 = 1712333) B1712333
theorem B1141571 : Blo 1140634 1141571 := bstep (se 1 (by rfl) ⟨856178, by rfl⟩ : syracuseStep 1141571 = 1712357) B1712357
theorem B1141587 : Blo 1140634 1141587 := bstep (se 1 (by rfl) ⟨856190, by rfl⟩ : syracuseStep 1141587 = 1712381) B1712381
theorem B1141603 : Blo 1140634 1141603 := bstep (se 1 (by rfl) ⟨856202, by rfl⟩ : syracuseStep 1141603 = 1712405) B1712405
theorem B1141619 : Blo 1140634 1141619 := bstep (se 1 (by rfl) ⟨856214, by rfl⟩ : syracuseStep 1141619 = 1712429) B1712429
theorem B1141635 : Blo 1140634 1141635 := bstep (se 1 (by rfl) ⟨856226, by rfl⟩ : syracuseStep 1141635 = 1712453) B1712453
theorem B1141651 : Blo 1140634 1141651 := bstep (se 1 (by rfl) ⟨856238, by rfl⟩ : syracuseStep 1141651 = 1712477) B1712477
theorem B1928083 : Blo 1140634 1928083 := bstep (se 1 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 1928083 = 2892125) B2892125
theorem B1141667 : Blo 1140634 1141667 := bstep (se 1 (by rfl) ⟨856250, by rfl⟩ : syracuseStep 1141667 = 1712501) B1712501
theorem B1141683 : Blo 1140634 1141683 := bstep (se 1 (by rfl) ⟨856262, by rfl⟩ : syracuseStep 1141683 = 1712525) B1712525
theorem B1141699 : Blo 1140634 1141699 := bstep (se 1 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 1141699 = 1712549) B1712549
theorem B1141715 : Blo 1140634 1141715 := bstep (se 1 (by rfl) ⟨856286, by rfl⟩ : syracuseStep 1141715 = 1712573) B1712573
theorem B1141731 : Blo 1140634 1141731 := bstep (se 1 (by rfl) ⟨856298, by rfl⟩ : syracuseStep 1141731 = 1712597) B1712597
theorem B3861485 : Blo 1140634 3861485 := bstep (se 3 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 3861485 = 1448057) B1448057
theorem B1141747 : Blo 1140634 1141747 := bstep (se 1 (by rfl) ⟨856310, by rfl⟩ : syracuseStep 1141747 = 1712621) B1712621
theorem B1141763 : Blo 1140634 1141763 := bstep (se 1 (by rfl) ⟨856322, by rfl⟩ : syracuseStep 1141763 = 1712645) B1712645
theorem B1141779 : Blo 1140634 1141779 := bstep (se 1 (by rfl) ⟨856334, by rfl⟩ : syracuseStep 1141779 = 1712669) B1712669
theorem B1928225 : Blo 1140634 1928225 := bstep (se 2 (by rfl) ⟨723084, by rfl⟩ : syracuseStep 1928225 = 1446169) B1446169
theorem B1141795 : Blo 1140634 1141795 := bstep (se 1 (by rfl) ⟨856346, by rfl⟩ : syracuseStep 1141795 = 1712693) B1712693
theorem B3861539 : Blo 1140634 3861539 := bstep (se 1 (by rfl) ⟨2896154, by rfl⟩ : syracuseStep 3861539 = 5792309) B5792309
theorem B1141811 : Blo 1140634 1141811 := bstep (se 1 (by rfl) ⟨856358, by rfl⟩ : syracuseStep 1141811 = 1712717) B1712717
theorem B1141827 : Blo 1140634 1141827 := bstep (se 1 (by rfl) ⟨856370, by rfl⟩ : syracuseStep 1141827 = 1712741) B1712741
theorem B1829969 : Blo 1140634 1829969 := bstep (se 2 (by rfl) ⟨686238, by rfl⟩ : syracuseStep 1829969 = 1372477) B1372477
theorem B1141843 : Blo 1140634 1141843 := bstep (se 1 (by rfl) ⟨856382, by rfl⟩ : syracuseStep 1141843 = 1712765) B1712765
theorem B1141859 : Blo 1140634 1141859 := bstep (se 1 (by rfl) ⟨856394, by rfl⟩ : syracuseStep 1141859 = 1712789) B1712789
theorem B1141875 : Blo 1140634 1141875 := bstep (se 1 (by rfl) ⟨856406, by rfl⟩ : syracuseStep 1141875 = 1712813) B1712813
theorem B1141891 : Blo 1140634 1141891 := bstep (se 1 (by rfl) ⟨856418, by rfl⟩ : syracuseStep 1141891 = 1712837) B1712837
theorem B1141907 : Blo 1140634 1141907 := bstep (se 1 (by rfl) ⟨856430, by rfl⟩ : syracuseStep 1141907 = 1712861) B1712861
theorem B1928353 : Blo 1140634 1928353 := bstep (se 2 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 1928353 = 1446265) B1446265
theorem B1141923 : Blo 1140634 1141923 := bstep (se 1 (by rfl) ⟨856442, by rfl⟩ : syracuseStep 1141923 = 1712885) B1712885
theorem B4877489 : Blo 1140634 4877489 := bstep (se 2 (by rfl) ⟨1829058, by rfl⟩ : syracuseStep 4877489 = 3658117) B3658117
theorem B1141939 : Blo 1140634 1141939 := bstep (se 1 (by rfl) ⟨856454, by rfl⟩ : syracuseStep 1141939 = 1712909) B1712909
theorem B1141955 : Blo 1140634 1141955 := bstep (se 1 (by rfl) ⟨856466, by rfl⟩ : syracuseStep 1141955 = 1712933) B1712933
theorem B1928387 : Blo 1140634 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B1141971 : Blo 1140634 1141971 := bstep (se 1 (by rfl) ⟨856478, by rfl⟩ : syracuseStep 1141971 = 1712957) B1712957
theorem B1141987 : Blo 1140634 1141987 := bstep (se 1 (by rfl) ⟨856490, by rfl⟩ : syracuseStep 1141987 = 1712981) B1712981
theorem B1142003 : Blo 1140634 1142003 := bstep (se 1 (by rfl) ⟨856502, by rfl⟩ : syracuseStep 1142003 = 1713005) B1713005
theorem B1142019 : Blo 1140634 1142019 := bstep (se 1 (by rfl) ⟨856514, by rfl⟩ : syracuseStep 1142019 = 1713029) B1713029
theorem B1830161 : Blo 1140634 1830161 := bstep (se 2 (by rfl) ⟨686310, by rfl⟩ : syracuseStep 1830161 = 1372621) B1372621
theorem B1142035 : Blo 1140634 1142035 := bstep (se 1 (by rfl) ⟨856526, by rfl⟩ : syracuseStep 1142035 = 1713053) B1713053
theorem B1142051 : Blo 1140634 1142051 := bstep (se 1 (by rfl) ⟨856538, by rfl⟩ : syracuseStep 1142051 = 1713077) B1713077
theorem B3861809 : Blo 1140634 3861809 := bstep (se 2 (by rfl) ⟨1448178, by rfl⟩ : syracuseStep 3861809 = 2896357) B2896357
theorem B1142067 : Blo 1140634 1142067 := bstep (se 1 (by rfl) ⟨856550, by rfl⟩ : syracuseStep 1142067 = 1713101) B1713101
theorem B1142083 : Blo 1140634 1142083 := bstep (se 1 (by rfl) ⟨856562, by rfl⟩ : syracuseStep 1142083 = 1713125) B1713125
theorem B1928515 : Blo 1140634 1928515 := bstep (se 1 (by rfl) ⟨1446386, by rfl⟩ : syracuseStep 1928515 = 2892773) B2892773
theorem B1142099 : Blo 1140634 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B1142115 : Blo 1140634 1142115 := bstep (se 1 (by rfl) ⟨856586, by rfl⟩ : syracuseStep 1142115 = 1713173) B1713173
theorem B1142131 : Blo 1140634 1142131 := bstep (se 1 (by rfl) ⟨856598, by rfl⟩ : syracuseStep 1142131 = 1713197) B1713197
theorem B1142147 : Blo 1140634 1142147 := bstep (se 1 (by rfl) ⟨856610, by rfl⟩ : syracuseStep 1142147 = 1713221) B1713221
theorem B1830289 : Blo 1140634 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1142163 : Blo 1140634 1142163 := bstep (se 1 (by rfl) ⟨856622, by rfl⟩ : syracuseStep 1142163 = 1713245) B1713245
theorem B1142179 : Blo 1140634 1142179 := bstep (se 1 (by rfl) ⟨856634, by rfl⟩ : syracuseStep 1142179 = 1713269) B1713269
theorem B1142195 : Blo 1140634 1142195 := bstep (se 1 (by rfl) ⟨856646, by rfl⟩ : syracuseStep 1142195 = 1713293) B1713293
theorem B1142211 : Blo 1140634 1142211 := bstep (se 1 (by rfl) ⟨856658, by rfl⟩ : syracuseStep 1142211 = 1713317) B1713317
theorem B1928657 : Blo 1140634 1928657 := bstep (se 2 (by rfl) ⟨723246, by rfl⟩ : syracuseStep 1928657 = 1446493) B1446493
theorem B1142227 : Blo 1140634 1142227 := bstep (se 1 (by rfl) ⟨856670, by rfl⟩ : syracuseStep 1142227 = 1713341) B1713341
theorem B1142243 : Blo 1140634 1142243 := bstep (se 1 (by rfl) ⟨856682, by rfl⟩ : syracuseStep 1142243 = 1713365) B1713365
theorem B1142259 : Blo 1140634 1142259 := bstep (se 1 (by rfl) ⟨856694, by rfl⟩ : syracuseStep 1142259 = 1713389) B1713389
theorem B1142275 : Blo 1140634 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B1142291 : Blo 1140634 1142291 := bstep (se 1 (by rfl) ⟨856718, by rfl⟩ : syracuseStep 1142291 = 1713437) B1713437
theorem B1142307 : Blo 1140634 1142307 := bstep (se 1 (by rfl) ⟨856730, by rfl⟩ : syracuseStep 1142307 = 1713461) B1713461
theorem B1142323 : Blo 1140634 1142323 := bstep (se 1 (by rfl) ⟨856742, by rfl⟩ : syracuseStep 1142323 = 1713485) B1713485
theorem B1142339 : Blo 1140634 1142339 := bstep (se 1 (by rfl) ⟨856754, by rfl⟩ : syracuseStep 1142339 = 1713509) B1713509
theorem B1928785 : Blo 1140634 1928785 := bstep (se 2 (by rfl) ⟨723294, by rfl⟩ : syracuseStep 1928785 = 1446589) B1446589
theorem B1142355 : Blo 1140634 1142355 := bstep (se 1 (by rfl) ⟨856766, by rfl⟩ : syracuseStep 1142355 = 1713533) B1713533
theorem B1142371 : Blo 1140634 1142371 := bstep (se 1 (by rfl) ⟨856778, by rfl⟩ : syracuseStep 1142371 = 1713557) B1713557
theorem B1142387 : Blo 1140634 1142387 := bstep (se 1 (by rfl) ⟨856790, by rfl⟩ : syracuseStep 1142387 = 1713581) B1713581
theorem B1928819 : Blo 1140634 1928819 := bstep (se 1 (by rfl) ⟨1446614, by rfl⟩ : syracuseStep 1928819 = 2893229) B2893229
theorem B1142403 : Blo 1140634 1142403 := bstep (se 1 (by rfl) ⟨856802, by rfl⟩ : syracuseStep 1142403 = 1713605) B1713605
theorem B3665549 : Blo 1140634 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B1142419 : Blo 1140634 1142419 := bstep (se 1 (by rfl) ⟨856814, by rfl⟩ : syracuseStep 1142419 = 1713629) B1713629
theorem B1142435 : Blo 1140634 1142435 := bstep (se 1 (by rfl) ⟨856826, by rfl⟩ : syracuseStep 1142435 = 1713653) B1713653
theorem B1142451 : Blo 1140634 1142451 := bstep (se 1 (by rfl) ⟨856838, by rfl⟩ : syracuseStep 1142451 = 1713677) B1713677
theorem B1142467 : Blo 1140634 1142467 := bstep (se 1 (by rfl) ⟨856850, by rfl⟩ : syracuseStep 1142467 = 1713701) B1713701
theorem B1142483 : Blo 1140634 1142483 := bstep (se 1 (by rfl) ⟨856862, by rfl⟩ : syracuseStep 1142483 = 1713725) B1713725
theorem B1142499 : Blo 1140634 1142499 := bstep (se 1 (by rfl) ⟨856874, by rfl⟩ : syracuseStep 1142499 = 1713749) B1713749
theorem B6942449 : Blo 1140634 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1142515 : Blo 1140634 1142515 := bstep (se 1 (by rfl) ⟨856886, by rfl⟩ : syracuseStep 1142515 = 1713773) B1713773
theorem B1928947 : Blo 1140634 1928947 := bstep (se 1 (by rfl) ⟨1446710, by rfl⟩ : syracuseStep 1928947 = 2893421) B2893421
theorem B1142531 : Blo 1140634 1142531 := bstep (se 1 (by rfl) ⟨856898, by rfl⟩ : syracuseStep 1142531 = 1713797) B1713797
theorem B2748163 : Blo 1140634 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B6942469 : Blo 1140634 6942469 := bstep (se 4 (by rfl) ⟨650856, by rfl⟩ : syracuseStep 6942469 = 1301713) B1301713
theorem B1142547 : Blo 1140634 1142547 := bstep (se 1 (by rfl) ⟨856910, by rfl⟩ : syracuseStep 1142547 = 1713821) B1713821
theorem B1142563 : Blo 1140634 1142563 := bstep (se 1 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 1142563 = 1713845) B1713845
theorem B1142579 : Blo 1140634 1142579 := bstep (se 1 (by rfl) ⟨856934, by rfl⟩ : syracuseStep 1142579 = 1713869) B1713869
theorem B1142595 : Blo 1140634 1142595 := bstep (se 1 (by rfl) ⟨856946, by rfl⟩ : syracuseStep 1142595 = 1713893) B1713893
theorem B3862349 : Blo 1140634 3862349 := bstep (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) B1448381
theorem B1142611 : Blo 1140634 1142611 := bstep (se 1 (by rfl) ⟨856958, by rfl⟩ : syracuseStep 1142611 = 1713917) B1713917
theorem B1142627 : Blo 1140634 1142627 := bstep (se 1 (by rfl) ⟨856970, by rfl⟩ : syracuseStep 1142627 = 1713941) B1713941
theorem B1142643 : Blo 1140634 1142643 := bstep (se 1 (by rfl) ⟨856982, by rfl⟩ : syracuseStep 1142643 = 1713965) B1713965
theorem B1929089 : Blo 1140634 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B1142659 : Blo 1140634 1142659 := bstep (se 1 (by rfl) ⟨856994, by rfl⟩ : syracuseStep 1142659 = 1713989) B1713989
theorem B3862403 : Blo 1140634 3862403 := bstep (se 1 (by rfl) ⟨2896802, by rfl⟩ : syracuseStep 3862403 = 5793605) B5793605
theorem B1142675 : Blo 1140634 1142675 := bstep (se 1 (by rfl) ⟨857006, by rfl⟩ : syracuseStep 1142675 = 1714013) B1714013
theorem B1142691 : Blo 1140634 1142691 := bstep (se 1 (by rfl) ⟨857018, by rfl⟩ : syracuseStep 1142691 = 1714037) B1714037
theorem B1142707 : Blo 1140634 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B1142723 : Blo 1140634 1142723 := bstep (se 1 (by rfl) ⟨857042, by rfl⟩ : syracuseStep 1142723 = 1714085) B1714085
theorem B1142739 : Blo 1140634 1142739 := bstep (se 1 (by rfl) ⟨857054, by rfl⟩ : syracuseStep 1142739 = 1714109) B1714109
theorem B1142755 : Blo 1140634 1142755 := bstep (se 1 (by rfl) ⟨857066, by rfl⟩ : syracuseStep 1142755 = 1714133) B1714133
theorem B1142771 : Blo 1140634 1142771 := bstep (se 1 (by rfl) ⟨857078, by rfl⟩ : syracuseStep 1142771 = 1714157) B1714157
theorem B1929217 : Blo 1140634 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B1142787 : Blo 1140634 1142787 := bstep (se 1 (by rfl) ⟨857090, by rfl⟩ : syracuseStep 1142787 = 1714181) B1714181
theorem B1830929 : Blo 1140634 1830929 := bstep (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) B1373197
theorem B1142803 : Blo 1140634 1142803 := bstep (se 1 (by rfl) ⟨857102, by rfl⟩ : syracuseStep 1142803 = 1714205) B1714205
theorem B1142819 : Blo 1140634 1142819 := bstep (se 1 (by rfl) ⟨857114, by rfl⟩ : syracuseStep 1142819 = 1714229) B1714229
theorem B1929251 : Blo 1140634 1929251 := bstep (se 1 (by rfl) ⟨1446938, by rfl⟩ : syracuseStep 1929251 = 2893877) B2893877
theorem B1142835 : Blo 1140634 1142835 := bstep (se 1 (by rfl) ⟨857126, by rfl⟩ : syracuseStep 1142835 = 1714253) B1714253
theorem B1142851 : Blo 1140634 1142851 := bstep (se 1 (by rfl) ⟨857138, by rfl⟩ : syracuseStep 1142851 = 1714277) B1714277
theorem B4878413 : Blo 1140634 4878413 := bstep (se 3 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 4878413 = 1829405) B1829405
theorem B1142867 : Blo 1140634 1142867 := bstep (se 1 (by rfl) ⟨857150, by rfl⟩ : syracuseStep 1142867 = 1714301) B1714301
theorem B1142883 : Blo 1140634 1142883 := bstep (se 1 (by rfl) ⟨857162, by rfl⟩ : syracuseStep 1142883 = 1714325) B1714325
theorem B1142899 : Blo 1140634 1142899 := bstep (se 1 (by rfl) ⟨857174, by rfl⟩ : syracuseStep 1142899 = 1714349) B1714349
theorem B1142915 : Blo 1140634 1142915 := bstep (se 1 (by rfl) ⟨857186, by rfl⟩ : syracuseStep 1142915 = 1714373) B1714373
theorem B3862673 : Blo 1140634 3862673 := bstep (se 2 (by rfl) ⟨1448502, by rfl⟩ : syracuseStep 3862673 = 2897005) B2897005
theorem B1142931 : Blo 1140634 1142931 := bstep (se 1 (by rfl) ⟨857198, by rfl⟩ : syracuseStep 1142931 = 1714397) B1714397
theorem B1142947 : Blo 1140634 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B1929379 : Blo 1140634 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1142963 : Blo 1140634 1142963 := bstep (se 1 (by rfl) ⟨857222, by rfl⟩ : syracuseStep 1142963 = 1714445) B1714445
theorem B1142979 : Blo 1140634 1142979 := bstep (se 1 (by rfl) ⟨857234, by rfl⟩ : syracuseStep 1142979 = 1714469) B1714469
theorem B1142995 : Blo 1140634 1142995 := bstep (se 1 (by rfl) ⟨857246, by rfl⟩ : syracuseStep 1142995 = 1714493) B1714493
theorem B1143011 : Blo 1140634 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B1143027 : Blo 1140634 1143027 := bstep (se 1 (by rfl) ⟨857270, by rfl⟩ : syracuseStep 1143027 = 1714541) B1714541
theorem B1143043 : Blo 1140634 1143043 := bstep (se 1 (by rfl) ⟨857282, by rfl⟩ : syracuseStep 1143043 = 1714565) B1714565
theorem B2060561 : Blo 1140634 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1143059 : Blo 1140634 1143059 := bstep (se 1 (by rfl) ⟨857294, by rfl⟩ : syracuseStep 1143059 = 1714589) B1714589
theorem B1143075 : Blo 1140634 1143075 := bstep (se 1 (by rfl) ⟨857306, by rfl⟩ : syracuseStep 1143075 = 1714613) B1714613
theorem B1929521 : Blo 1140634 1929521 := bstep (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) B1447141
theorem B1143091 : Blo 1140634 1143091 := bstep (se 1 (by rfl) ⟨857318, by rfl⟩ : syracuseStep 1143091 = 1714637) B1714637
theorem B1143107 : Blo 1140634 1143107 := bstep (se 1 (by rfl) ⟨857330, by rfl⟩ : syracuseStep 1143107 = 1714661) B1714661
theorem B1143123 : Blo 1140634 1143123 := bstep (se 1 (by rfl) ⟨857342, by rfl⟩ : syracuseStep 1143123 = 1714685) B1714685
theorem B1143139 : Blo 1140634 1143139 := bstep (se 1 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 1143139 = 1714709) B1714709
theorem B1143155 : Blo 1140634 1143155 := bstep (se 1 (by rfl) ⟨857366, by rfl⟩ : syracuseStep 1143155 = 1714733) B1714733
theorem B1143171 : Blo 1140634 1143171 := bstep (se 1 (by rfl) ⟨857378, by rfl⟩ : syracuseStep 1143171 = 1714757) B1714757
theorem B1143187 : Blo 1140634 1143187 := bstep (se 1 (by rfl) ⟨857390, by rfl⟩ : syracuseStep 1143187 = 1714781) B1714781
theorem B1143203 : Blo 1140634 1143203 := bstep (se 1 (by rfl) ⟨857402, by rfl⟩ : syracuseStep 1143203 = 1714805) B1714805
theorem B1929649 : Blo 1140634 1929649 := bstep (se 2 (by rfl) ⟨723618, by rfl⟩ : syracuseStep 1929649 = 1447237) B1447237
theorem B6517169 : Blo 1140634 6517169 := bstep (se 2 (by rfl) ⟨2443938, by rfl⟩ : syracuseStep 6517169 = 4887877) B4887877
theorem B1143219 : Blo 1140634 1143219 := bstep (se 1 (by rfl) ⟨857414, by rfl⟩ : syracuseStep 1143219 = 1714829) B1714829
theorem B1143235 : Blo 1140634 1143235 := bstep (se 1 (by rfl) ⟨857426, by rfl⟩ : syracuseStep 1143235 = 1714853) B1714853
theorem B1143251 : Blo 1140634 1143251 := bstep (se 1 (by rfl) ⟨857438, by rfl⟩ : syracuseStep 1143251 = 1714877) B1714877
theorem B1929683 : Blo 1140634 1929683 := bstep (se 1 (by rfl) ⟨1447262, by rfl⟩ : syracuseStep 1929683 = 2894525) B2894525
theorem B1143267 : Blo 1140634 1143267 := bstep (se 1 (by rfl) ⟨857450, by rfl⟩ : syracuseStep 1143267 = 1714901) B1714901
theorem B1143283 : Blo 1140634 1143283 := bstep (se 1 (by rfl) ⟨857462, by rfl⟩ : syracuseStep 1143283 = 1714925) B1714925
theorem B1143299 : Blo 1140634 1143299 := bstep (se 1 (by rfl) ⟨857474, by rfl⟩ : syracuseStep 1143299 = 1714949) B1714949
theorem B1143315 : Blo 1140634 1143315 := bstep (se 1 (by rfl) ⟨857486, by rfl⟩ : syracuseStep 1143315 = 1714973) B1714973
theorem B1143331 : Blo 1140634 1143331 := bstep (se 1 (by rfl) ⟨857498, by rfl⟩ : syracuseStep 1143331 = 1714997) B1714997
theorem B3469873 : Blo 1140634 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B2060849 : Blo 1140634 2060849 := bstep (se 2 (by rfl) ⟨772818, by rfl⟩ : syracuseStep 2060849 = 1545637) B1545637
theorem B1143347 : Blo 1140634 1143347 := bstep (se 1 (by rfl) ⟨857510, by rfl⟩ : syracuseStep 1143347 = 1715021) B1715021
theorem B1143363 : Blo 1140634 1143363 := bstep (se 1 (by rfl) ⟨857522, by rfl⟩ : syracuseStep 1143363 = 1715045) B1715045
theorem B1143379 : Blo 1140634 1143379 := bstep (se 1 (by rfl) ⟨857534, by rfl⟩ : syracuseStep 1143379 = 1715069) B1715069
theorem B1929811 : Blo 1140634 1929811 := bstep (se 1 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 1929811 = 2894717) B2894717
theorem B1143395 : Blo 1140634 1143395 := bstep (se 1 (by rfl) ⟨857546, by rfl⟩ : syracuseStep 1143395 = 1715093) B1715093
theorem B1143411 : Blo 1140634 1143411 := bstep (se 1 (by rfl) ⟨857558, by rfl⟩ : syracuseStep 1143411 = 1715117) B1715117
theorem B1143427 : Blo 1140634 1143427 := bstep (se 1 (by rfl) ⟨857570, by rfl⟩ : syracuseStep 1143427 = 1715141) B1715141
theorem B1143443 : Blo 1140634 1143443 := bstep (se 1 (by rfl) ⟨857582, by rfl⟩ : syracuseStep 1143443 = 1715165) B1715165
theorem B1143459 : Blo 1140634 1143459 := bstep (se 1 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 1143459 = 1715189) B1715189
theorem B1143475 : Blo 1140634 1143475 := bstep (se 1 (by rfl) ⟨857606, by rfl⟩ : syracuseStep 1143475 = 1715213) B1715213
theorem B1143491 : Blo 1140634 1143491 := bstep (se 1 (by rfl) ⟨857618, by rfl⟩ : syracuseStep 1143491 = 1715237) B1715237
theorem B1143507 : Blo 1140634 1143507 := bstep (se 1 (by rfl) ⟨857630, by rfl⟩ : syracuseStep 1143507 = 1715261) B1715261
theorem B1929953 : Blo 1140634 1929953 := bstep (se 2 (by rfl) ⟨723732, by rfl⟩ : syracuseStep 1929953 = 1447465) B1447465
theorem B1143523 : Blo 1140634 1143523 := bstep (se 1 (by rfl) ⟨857642, by rfl⟩ : syracuseStep 1143523 = 1715285) B1715285
theorem B1143539 : Blo 1140634 1143539 := bstep (se 1 (by rfl) ⟨857654, by rfl⟩ : syracuseStep 1143539 = 1715309) B1715309
theorem B1143555 : Blo 1140634 1143555 := bstep (se 1 (by rfl) ⟨857666, by rfl⟩ : syracuseStep 1143555 = 1715333) B1715333
theorem B1143571 : Blo 1140634 1143571 := bstep (se 1 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 1143571 = 1715357) B1715357
theorem B1143587 : Blo 1140634 1143587 := bstep (se 1 (by rfl) ⟨857690, by rfl⟩ : syracuseStep 1143587 = 1715381) B1715381
theorem B1143603 : Blo 1140634 1143603 := bstep (se 1 (by rfl) ⟨857702, by rfl⟩ : syracuseStep 1143603 = 1715405) B1715405
theorem B1143619 : Blo 1140634 1143619 := bstep (se 1 (by rfl) ⟨857714, by rfl⟩ : syracuseStep 1143619 = 1715429) B1715429
theorem B1143635 : Blo 1140634 1143635 := bstep (se 1 (by rfl) ⟨857726, by rfl⟩ : syracuseStep 1143635 = 1715453) B1715453
theorem B1930081 : Blo 1140634 1930081 := bstep (se 2 (by rfl) ⟨723780, by rfl⟩ : syracuseStep 1930081 = 1447561) B1447561
theorem B1143651 : Blo 1140634 1143651 := bstep (se 1 (by rfl) ⟨857738, by rfl⟩ : syracuseStep 1143651 = 1715477) B1715477
theorem B1143667 : Blo 1140634 1143667 := bstep (se 1 (by rfl) ⟨857750, by rfl⟩ : syracuseStep 1143667 = 1715501) B1715501
theorem B1143683 : Blo 1140634 1143683 := bstep (se 1 (by rfl) ⟨857762, by rfl⟩ : syracuseStep 1143683 = 1715525) B1715525
theorem B1930115 : Blo 1140634 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B1143699 : Blo 1140634 1143699 := bstep (se 1 (by rfl) ⟨857774, by rfl⟩ : syracuseStep 1143699 = 1715549) B1715549
theorem B1143715 : Blo 1140634 1143715 := bstep (se 1 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 1143715 = 1715573) B1715573
theorem B1143731 : Blo 1140634 1143731 := bstep (se 1 (by rfl) ⟨857798, by rfl⟩ : syracuseStep 1143731 = 1715597) B1715597
theorem B1143747 : Blo 1140634 1143747 := bstep (se 1 (by rfl) ⟨857810, by rfl⟩ : syracuseStep 1143747 = 1715621) B1715621
theorem B2749393 : Blo 1140634 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B1143763 : Blo 1140634 1143763 := bstep (se 1 (by rfl) ⟨857822, by rfl⟩ : syracuseStep 1143763 = 1715645) B1715645
theorem B1143779 : Blo 1140634 1143779 := bstep (se 1 (by rfl) ⟨857834, by rfl⟩ : syracuseStep 1143779 = 1715669) B1715669
theorem B1143795 : Blo 1140634 1143795 := bstep (se 1 (by rfl) ⟨857846, by rfl⟩ : syracuseStep 1143795 = 1715693) B1715693
theorem B1143811 : Blo 1140634 1143811 := bstep (se 1 (by rfl) ⟨857858, by rfl⟩ : syracuseStep 1143811 = 1715717) B1715717
theorem B1930243 : Blo 1140634 1930243 := bstep (se 1 (by rfl) ⟨1447682, by rfl⟩ : syracuseStep 1930243 = 2895365) B2895365
theorem B1143827 : Blo 1140634 1143827 := bstep (se 1 (by rfl) ⟨857870, by rfl⟩ : syracuseStep 1143827 = 1715741) B1715741
theorem B1143843 : Blo 1140634 1143843 := bstep (se 1 (by rfl) ⟨857882, by rfl⟩ : syracuseStep 1143843 = 1715765) B1715765
theorem B1143859 : Blo 1140634 1143859 := bstep (se 1 (by rfl) ⟨857894, by rfl⟩ : syracuseStep 1143859 = 1715789) B1715789
theorem B1143875 : Blo 1140634 1143875 := bstep (se 1 (by rfl) ⟨857906, by rfl⟩ : syracuseStep 1143875 = 1715813) B1715813
theorem B1143891 : Blo 1140634 1143891 := bstep (se 1 (by rfl) ⟨857918, by rfl⟩ : syracuseStep 1143891 = 1715837) B1715837
theorem B1143907 : Blo 1140634 1143907 := bstep (se 1 (by rfl) ⟨857930, by rfl⟩ : syracuseStep 1143907 = 1715861) B1715861
theorem B1143923 : Blo 1140634 1143923 := bstep (se 1 (by rfl) ⟨857942, by rfl⟩ : syracuseStep 1143923 = 1715885) B1715885
theorem B1143939 : Blo 1140634 1143939 := bstep (se 1 (by rfl) ⟨857954, by rfl⟩ : syracuseStep 1143939 = 1715909) B1715909
theorem B1930385 : Blo 1140634 1930385 := bstep (se 2 (by rfl) ⟨723894, by rfl⟩ : syracuseStep 1930385 = 1447789) B1447789
theorem B1143955 : Blo 1140634 1143955 := bstep (se 1 (by rfl) ⟨857966, by rfl⟩ : syracuseStep 1143955 = 1715933) B1715933
theorem B1143971 : Blo 1140634 1143971 := bstep (se 1 (by rfl) ⟨857978, by rfl⟩ : syracuseStep 1143971 = 1715957) B1715957
theorem B1143987 : Blo 1140634 1143987 := bstep (se 1 (by rfl) ⟨857990, by rfl⟩ : syracuseStep 1143987 = 1715981) B1715981
theorem B1144003 : Blo 1140634 1144003 := bstep (se 1 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 1144003 = 1716005) B1716005
theorem B1144019 : Blo 1140634 1144019 := bstep (se 1 (by rfl) ⟨858014, by rfl⟩ : syracuseStep 1144019 = 1716029) B1716029
theorem B1144035 : Blo 1140634 1144035 := bstep (se 1 (by rfl) ⟨858026, by rfl⟩ : syracuseStep 1144035 = 1716053) B1716053
theorem B1144051 : Blo 1140634 1144051 := bstep (se 1 (by rfl) ⟨858038, by rfl⟩ : syracuseStep 1144051 = 1716077) B1716077
theorem B1144067 : Blo 1140634 1144067 := bstep (se 1 (by rfl) ⟨858050, by rfl⟩ : syracuseStep 1144067 = 1716101) B1716101
theorem B1930513 : Blo 1140634 1930513 := bstep (se 2 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 1930513 = 1447885) B1447885
theorem B1144083 : Blo 1140634 1144083 := bstep (se 1 (by rfl) ⟨858062, by rfl⟩ : syracuseStep 1144083 = 1716125) B1716125
theorem B1144099 : Blo 1140634 1144099 := bstep (se 1 (by rfl) ⟨858074, by rfl⟩ : syracuseStep 1144099 = 1716149) B1716149
theorem B1930547 : Blo 1140634 1930547 := bstep (se 1 (by rfl) ⟨1447910, by rfl⟩ : syracuseStep 1930547 = 2895821) B2895821
theorem B1144115 : Blo 1140634 1144115 := bstep (se 1 (by rfl) ⟨858086, by rfl⟩ : syracuseStep 1144115 = 1716173) B1716173
theorem B1144131 : Blo 1140634 1144131 := bstep (se 1 (by rfl) ⟨858098, by rfl⟩ : syracuseStep 1144131 = 1716197) B1716197
theorem B1144147 : Blo 1140634 1144147 := bstep (se 1 (by rfl) ⟨858110, by rfl⟩ : syracuseStep 1144147 = 1716221) B1716221
theorem B1373539 : Blo 1140634 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B1144163 : Blo 1140634 1144163 := bstep (se 1 (by rfl) ⟨858122, by rfl⟩ : syracuseStep 1144163 = 1716245) B1716245
theorem B1144179 : Blo 1140634 1144179 := bstep (se 1 (by rfl) ⟨858134, by rfl⟩ : syracuseStep 1144179 = 1716269) B1716269
theorem B1144195 : Blo 1140634 1144195 := bstep (se 1 (by rfl) ⟨858146, by rfl⟩ : syracuseStep 1144195 = 1716293) B1716293
theorem B1832339 : Blo 1140634 1832339 := bstep (se 1 (by rfl) ⟨1374254, by rfl⟩ : syracuseStep 1832339 = 2748509) B2748509
theorem B1144211 : Blo 1140634 1144211 := bstep (se 1 (by rfl) ⟨858158, by rfl⟩ : syracuseStep 1144211 = 1716317) B1716317
theorem B1144227 : Blo 1140634 1144227 := bstep (se 1 (by rfl) ⟨858170, by rfl⟩ : syracuseStep 1144227 = 1716341) B1716341
theorem B1930675 : Blo 1140634 1930675 := bstep (se 1 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 1930675 = 2896013) B2896013
theorem B1144243 : Blo 1140634 1144243 := bstep (se 1 (by rfl) ⟨858182, by rfl⟩ : syracuseStep 1144243 = 1716365) B1716365
theorem B1144259 : Blo 1140634 1144259 := bstep (se 1 (by rfl) ⟨858194, by rfl⟩ : syracuseStep 1144259 = 1716389) B1716389
theorem B1144275 : Blo 1140634 1144275 := bstep (se 1 (by rfl) ⟨858206, by rfl⟩ : syracuseStep 1144275 = 1716413) B1716413
theorem B8680931 : Blo 1140634 8680931 := bstep (se 1 (by rfl) ⟨6510698, by rfl⟩ : syracuseStep 8680931 = 13021397) B13021397
theorem B1144291 : Blo 1140634 1144291 := bstep (se 1 (by rfl) ⟨858218, by rfl⟩ : syracuseStep 1144291 = 1716437) B1716437
theorem B1144307 : Blo 1140634 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B1144323 : Blo 1140634 1144323 := bstep (se 1 (by rfl) ⟨858242, by rfl⟩ : syracuseStep 1144323 = 1716485) B1716485
theorem B1832467 : Blo 1140634 1832467 := bstep (se 1 (by rfl) ⟨1374350, by rfl⟩ : syracuseStep 1832467 = 2748701) B2748701
theorem B1144339 : Blo 1140634 1144339 := bstep (se 1 (by rfl) ⟨858254, by rfl⟩ : syracuseStep 1144339 = 1716509) B1716509
theorem B1144355 : Blo 1140634 1144355 := bstep (se 1 (by rfl) ⟨858266, by rfl⟩ : syracuseStep 1144355 = 1716533) B1716533
theorem B1144371 : Blo 1140634 1144371 := bstep (se 1 (by rfl) ⟨858278, by rfl⟩ : syracuseStep 1144371 = 1716557) B1716557
theorem B1930817 : Blo 1140634 1930817 := bstep (se 2 (by rfl) ⟨724056, by rfl⟩ : syracuseStep 1930817 = 1448113) B1448113
theorem B1144387 : Blo 1140634 1144387 := bstep (se 1 (by rfl) ⟨858290, by rfl⟩ : syracuseStep 1144387 = 1716581) B1716581
theorem B5797453 : Blo 1140634 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B1144403 : Blo 1140634 1144403 := bstep (se 1 (by rfl) ⟨858302, by rfl⟩ : syracuseStep 1144403 = 1716605) B1716605
theorem B1144419 : Blo 1140634 1144419 := bstep (se 1 (by rfl) ⟨858314, by rfl⟩ : syracuseStep 1144419 = 1716629) B1716629
theorem B1144435 : Blo 1140634 1144435 := bstep (se 1 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 1144435 = 1716653) B1716653
theorem B1144451 : Blo 1140634 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B1144467 : Blo 1140634 1144467 := bstep (se 1 (by rfl) ⟨858350, by rfl⟩ : syracuseStep 1144467 = 1716701) B1716701
theorem B1144483 : Blo 1140634 1144483 := bstep (se 1 (by rfl) ⟨858362, by rfl⟩ : syracuseStep 1144483 = 1716725) B1716725
theorem B1144499 : Blo 1140634 1144499 := bstep (se 1 (by rfl) ⟨858374, by rfl⟩ : syracuseStep 1144499 = 1716749) B1716749
theorem B1930945 : Blo 1140634 1930945 := bstep (se 2 (by rfl) ⟨724104, by rfl⟩ : syracuseStep 1930945 = 1448209) B1448209
theorem B1144515 : Blo 1140634 1144515 := bstep (se 1 (by rfl) ⟨858386, by rfl⟩ : syracuseStep 1144515 = 1716773) B1716773
theorem B1144531 : Blo 1140634 1144531 := bstep (se 1 (by rfl) ⟨858398, by rfl⟩ : syracuseStep 1144531 = 1716797) B1716797
theorem B1930979 : Blo 1140634 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B1144547 : Blo 1140634 1144547 := bstep (se 1 (by rfl) ⟨858410, by rfl⟩ : syracuseStep 1144547 = 1716821) B1716821
theorem B1144563 : Blo 1140634 1144563 := bstep (se 1 (by rfl) ⟨858422, by rfl⟩ : syracuseStep 1144563 = 1716845) B1716845
theorem B1144579 : Blo 1140634 1144579 := bstep (se 1 (by rfl) ⟨858434, by rfl⟩ : syracuseStep 1144579 = 1716869) B1716869
theorem B1144595 : Blo 1140634 1144595 := bstep (se 1 (by rfl) ⟨858446, by rfl⟩ : syracuseStep 1144595 = 1716893) B1716893
theorem B1144611 : Blo 1140634 1144611 := bstep (se 1 (by rfl) ⟨858458, by rfl⟩ : syracuseStep 1144611 = 1716917) B1716917
theorem B1144627 : Blo 1140634 1144627 := bstep (se 1 (by rfl) ⟨858470, by rfl⟩ : syracuseStep 1144627 = 1716941) B1716941
theorem B1931107 : Blo 1140634 1931107 := bstep (se 1 (by rfl) ⟨1448330, by rfl⟩ : syracuseStep 1931107 = 2896661) B2896661
theorem B6518627 : Blo 1140634 6518627 := bstep (se 1 (by rfl) ⟨4888970, by rfl⟩ : syracuseStep 6518627 = 9777941) B9777941
theorem B2783089 : Blo 1140634 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B1931249 : Blo 1140634 1931249 := bstep (se 2 (by rfl) ⟨724218, by rfl⟩ : syracuseStep 1931249 = 1448437) B1448437
theorem B1833025 : Blo 1140634 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B1931377 : Blo 1140634 1931377 := bstep (se 2 (by rfl) ⟨724266, by rfl⟩ : syracuseStep 1931377 = 1448533) B1448533
theorem B1931411 : Blo 1140634 1931411 := bstep (se 1 (by rfl) ⟨1448558, by rfl⟩ : syracuseStep 1931411 = 2897117) B2897117
theorem B1931539 : Blo 1140634 1931539 := bstep (se 1 (by rfl) ⟨1448654, by rfl⟩ : syracuseStep 1931539 = 2897309) B2897309
theorem B6945485 : Blo 1140634 6945485 := bstep (se 3 (by rfl) ⟨1302278, by rfl⟩ : syracuseStep 6945485 = 2604557) B2604557
theorem B1735715 : Blo 1140634 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B4881521 : Blo 1140634 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B7929157 : Blo 1140634 7929157 := bstep (se 4 (by rfl) ⟨743358, by rfl⟩ : syracuseStep 7929157 = 1486717) B1486717
theorem B3439949 : Blo 1140634 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B8781637 : Blo 1140634 8781637 := bstep (se 4 (by rfl) ⟨823278, by rfl⟩ : syracuseStep 8781637 = 1646557) B1646557
theorem B19529909 : Blo 1140634 19529909 := bstep (se 5 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 19529909 = 1830929) B1830929
theorem B4391129 : Blo 1140634 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B6685249 : Blo 1140634 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B35193437 : Blo 1140634 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B4883161 : Blo 1140634 4883161 := bstep (se 2 (by rfl) ⟨1831185, by rfl⟩ : syracuseStep 4883161 = 3662371) B3662371
theorem B8782627 : Blo 1140634 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B8684333 : Blo 1140634 8684333 := bstep (se 3 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 8684333 = 3256625) B3256625
theorem B4752535 : Blo 1140634 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B4883777 : Blo 1140634 4883777 := bstep (se 2 (by rfl) ⟨1831416, by rfl⟩ : syracuseStep 4883777 = 3662833) B3662833
theorem B2196887 : Blo 1140634 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B12387761 : Blo 1140634 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B2197441 : Blo 1140634 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B4393565 : Blo 1140634 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B1542809 : Blo 1140634 1542809 := bstep (se 2 (by rfl) ⟨578553, by rfl⟩ : syracuseStep 1542809 = 1157107) B1157107
theorem B2165555 : Blo 1140634 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B8227649 : Blo 1140634 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B10980197 : Blo 1140634 10980197 := bstep (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) B2058787
theorem B2165707 : Blo 1140634 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B1445131 : Blo 1140634 1445131 := bstep (se 1 (by rfl) ⟨1083848, by rfl⟩ : syracuseStep 1445131 = 2167697) B2167697
theorem B2166041 : Blo 1140634 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B5868875 : Blo 1140634 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B4886237 : Blo 1140634 4886237 := bstep (se 3 (by rfl) ⟨916169, by rfl⟩ : syracuseStep 4886237 = 1832339) B1832339
theorem B2887447 : Blo 1140634 2887447 := bstep (se 1 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 2887447 = 4331171) B4331171
theorem B1543961 : Blo 1140634 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B41783141 : Blo 1140634 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B2166679 : Blo 1140634 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B2887883 : Blo 1140634 2887883 := bstep (se 1 (by rfl) ⟨2165912, by rfl⟩ : syracuseStep 2887883 = 4331825) B4331825
theorem B1446103 : Blo 1140634 1446103 := bstep (se 1 (by rfl) ⟨1084577, by rfl⟩ : syracuseStep 1446103 = 2169155) B2169155
theorem B1544599 : Blo 1140634 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B6263219 : Blo 1140634 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B2888257 : Blo 1140634 2888257 := bstep (se 2 (by rfl) ⟨1083096, by rfl⟩ : syracuseStep 2888257 = 2166193) B2166193
theorem B8688221 : Blo 1140634 8688221 := bstep (se 3 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 8688221 = 3258083) B3258083
theorem B2167499 : Blo 1140634 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B2167553 : Blo 1140634 2167553 := bstep (se 2 (by rfl) ⟨812832, by rfl⟩ : syracuseStep 2167553 = 1625665) B1625665
theorem B2200537 : Blo 1140634 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B1446923 : Blo 1140634 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B2888855 : Blo 1140634 2888855 := bstep (se 1 (by rfl) ⟨2166641, by rfl⟩ : syracuseStep 2888855 = 4333283) B4333283
theorem B1283287 : Blo 1140634 1283287 := bstep (se 1 (by rfl) ⟨962465, by rfl⟩ : syracuseStep 1283287 = 1924931) B1924931
theorem B1283467 : Blo 1140634 1283467 := bstep (se 1 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 1283467 = 1925201) B1925201
theorem B18519475 : Blo 1140634 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B1283575 : Blo 1140634 1283575 := bstep (se 1 (by rfl) ⟨962681, by rfl⟩ : syracuseStep 1283575 = 1925363) B1925363
theorem B3085847 : Blo 1140634 3085847 := bstep (se 1 (by rfl) ⟨2314385, by rfl⟩ : syracuseStep 3085847 = 4628771) B4628771
theorem B2168471 : Blo 1140634 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B1283755 : Blo 1140634 1283755 := bstep (se 1 (by rfl) ⟨962816, by rfl⟩ : syracuseStep 1283755 = 1925633) B1925633
theorem B1447627 : Blo 1140634 1447627 := bstep (se 1 (by rfl) ⟨1085720, by rfl⟩ : syracuseStep 1447627 = 2171441) B2171441
theorem B1283863 : Blo 1140634 1283863 := bstep (se 1 (by rfl) ⟨962897, by rfl⟩ : syracuseStep 1283863 = 1925795) B1925795
theorem B4331339 : Blo 1140634 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B4331353 : Blo 1140634 4331353 := bstep (se 2 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 4331353 = 3248515) B3248515
theorem B2889665 : Blo 1140634 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B1284043 : Blo 1140634 1284043 := bstep (se 1 (by rfl) ⟨963032, by rfl⟩ : syracuseStep 1284043 = 1926065) B1926065
theorem B1447895 : Blo 1140634 1447895 := bstep (se 1 (by rfl) ⟨1085921, by rfl⟩ : syracuseStep 1447895 = 2171843) B2171843
theorem B9770969 : Blo 1140634 9770969 := bstep (se 2 (by rfl) ⟨3664113, by rfl⟩ : syracuseStep 9770969 = 7328227) B7328227
theorem B20846605 : Blo 1140634 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B1284151 : Blo 1140634 1284151 := bstep (se 1 (by rfl) ⟨963113, by rfl⟩ : syracuseStep 1284151 = 1926227) B1926227
theorem B4626497 : Blo 1140634 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B5216345 : Blo 1140634 5216345 := bstep (se 2 (by rfl) ⟨1956129, by rfl⟩ : syracuseStep 5216345 = 3912259) B3912259
theorem B3250327 : Blo 1140634 3250327 := bstep (se 1 (by rfl) ⟨2437745, by rfl⟩ : syracuseStep 3250327 = 4875491) B4875491
theorem B3086515 : Blo 1140634 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B2169011 : Blo 1140634 2169011 := bstep (se 1 (by rfl) ⟨1626758, by rfl⟩ : syracuseStep 2169011 = 3253517) B3253517
theorem B1284331 : Blo 1140634 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B4888835 : Blo 1140634 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B3086657 : Blo 1140634 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B1284439 : Blo 1140634 1284439 := bstep (se 1 (by rfl) ⟨963329, by rfl⟩ : syracuseStep 1284439 = 1926659) B1926659
theorem B3479897 : Blo 1140634 3479897 := bstep (se 2 (by rfl) ⟨1304961, by rfl⟩ : syracuseStep 3479897 = 2609923) B2609923
theorem B2890201 : Blo 1140634 2890201 := bstep (se 2 (by rfl) ⟨1083825, by rfl⟩ : syracuseStep 2890201 = 2167651) B2167651
theorem B1284619 : Blo 1140634 1284619 := bstep (se 1 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 1284619 = 1926929) B1926929
theorem B1251883 : Blo 1140634 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1219159 : Blo 1140634 1219159 := bstep (se 1 (by rfl) ⟨914369, by rfl⟩ : syracuseStep 1219159 = 1828739) B1828739
theorem B1284727 : Blo 1140634 1284727 := bstep (se 1 (by rfl) ⟨963545, by rfl⟩ : syracuseStep 1284727 = 1927091) B1927091
theorem B1448599 : Blo 1140634 1448599 := bstep (se 1 (by rfl) ⟨1086449, by rfl⟩ : syracuseStep 1448599 = 2172899) B2172899
theorem B2169497 : Blo 1140634 2169497 := bstep (se 2 (by rfl) ⟨813561, by rfl⟩ : syracuseStep 2169497 = 1627123) B1627123
theorem B4332311 : Blo 1140634 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B1284907 : Blo 1140634 1284907 := bstep (se 1 (by rfl) ⟨963680, by rfl⟩ : syracuseStep 1284907 = 1927361) B1927361
theorem B1285015 : Blo 1140634 1285015 := bstep (se 1 (by rfl) ⟨963761, by rfl⟩ : syracuseStep 1285015 = 1927523) B1927523
theorem B1711001 : Blo 1140634 1711001 := bstep (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) B1283251
theorem B16489433 : Blo 1140634 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B1711115 : Blo 1140634 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B1711127 : Blo 1140634 1711127 := bstep (se 1 (by rfl) ⟨1283345, by rfl⟩ : syracuseStep 1711127 = 2566691) B2566691
theorem B1285195 : Blo 1140634 1285195 := bstep (se 1 (by rfl) ⟨963896, by rfl⟩ : syracuseStep 1285195 = 1927793) B1927793
theorem B1711193 : Blo 1140634 1711193 := bstep (se 2 (by rfl) ⟨641697, by rfl⟩ : syracuseStep 1711193 = 1283395) B1283395
theorem B1285303 : Blo 1140634 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B1711307 : Blo 1140634 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B18521293 : Blo 1140634 18521293 := bstep (se 3 (by rfl) ⟨3472742, by rfl⟩ : syracuseStep 18521293 = 6945485) B6945485
theorem B1711319 : Blo 1140634 1711319 := bstep (se 1 (by rfl) ⟨1283489, by rfl⟩ : syracuseStep 1711319 = 2566979) B2566979
theorem B62594309 : Blo 1140634 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B1711385 : Blo 1140634 1711385 := bstep (se 2 (by rfl) ⟨641769, by rfl⟩ : syracuseStep 1711385 = 1283539) B1283539
theorem B1285483 : Blo 1140634 1285483 := bstep (se 1 (by rfl) ⟨964112, by rfl⟩ : syracuseStep 1285483 = 1928225) B1928225
theorem B1711499 : Blo 1140634 1711499 := bstep (se 1 (by rfl) ⟨1283624, by rfl⟩ : syracuseStep 1711499 = 2567249) B2567249
theorem B1219979 : Blo 1140634 1219979 := bstep (se 1 (by rfl) ⟨914984, by rfl⟩ : syracuseStep 1219979 = 1829969) B1829969
theorem B1711511 : Blo 1140634 1711511 := bstep (se 1 (by rfl) ⟨1283633, by rfl⟩ : syracuseStep 1711511 = 2567267) B2567267
theorem B3251659 : Blo 1140634 3251659 := bstep (se 1 (by rfl) ⟨2438744, by rfl⟩ : syracuseStep 3251659 = 4877489) B4877489
theorem B1285591 : Blo 1140634 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B1711577 : Blo 1140634 1711577 := bstep (se 2 (by rfl) ⟨641841, by rfl⟩ : syracuseStep 1711577 = 1283683) B1283683
theorem B1220107 : Blo 1140634 1220107 := bstep (se 1 (by rfl) ⟨915080, by rfl⟩ : syracuseStep 1220107 = 1830161) B1830161
theorem B2891315 : Blo 1140634 2891315 := bstep (se 1 (by rfl) ⟨2168486, by rfl⟩ : syracuseStep 2891315 = 4336973) B4336973
theorem B9772609 : Blo 1140634 9772609 := bstep (se 2 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 9772609 = 7329457) B7329457
theorem B1711691 : Blo 1140634 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B1711703 : Blo 1140634 1711703 := bstep (se 1 (by rfl) ⟨1283777, by rfl⟩ : syracuseStep 1711703 = 2567555) B2567555
theorem B1285771 : Blo 1140634 1285771 := bstep (se 1 (by rfl) ⟨964328, by rfl⟩ : syracuseStep 1285771 = 1928657) B1928657
theorem B1711769 : Blo 1140634 1711769 := bstep (se 2 (by rfl) ⟨641913, by rfl⟩ : syracuseStep 1711769 = 1283827) B1283827
theorem B3251933 : Blo 1140634 3251933 := bstep (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) B1219475
theorem B1285879 : Blo 1140634 1285879 := bstep (se 1 (by rfl) ⟨964409, by rfl⟩ : syracuseStep 1285879 = 1928819) B1928819
theorem B1711883 : Blo 1140634 1711883 := bstep (se 1 (by rfl) ⟨1283912, by rfl⟩ : syracuseStep 1711883 = 2567825) B2567825
theorem B1711895 : Blo 1140634 1711895 := bstep (se 1 (by rfl) ⟨1283921, by rfl⟩ : syracuseStep 1711895 = 2567843) B2567843
theorem B3710785 : Blo 1140634 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B6954827 : Blo 1140634 6954827 := bstep (se 1 (by rfl) ⟨5216120, by rfl⟩ : syracuseStep 6954827 = 10432241) B10432241
theorem B1711961 : Blo 1140634 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B2891609 : Blo 1140634 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B1286059 : Blo 1140634 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B1712075 : Blo 1140634 1712075 := bstep (se 1 (by rfl) ⟨1284056, by rfl⟩ : syracuseStep 1712075 = 2568113) B2568113
theorem B1712087 : Blo 1140634 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B4333571 : Blo 1140634 4333571 := bstep (se 1 (by rfl) ⟨3250178, by rfl⟩ : syracuseStep 4333571 = 6500357) B6500357
theorem B1286167 : Blo 1140634 1286167 := bstep (se 1 (by rfl) ⟨964625, by rfl⟩ : syracuseStep 1286167 = 1929251) B1929251
theorem B1712153 : Blo 1140634 1712153 := bstep (se 2 (by rfl) ⟨642057, by rfl⟩ : syracuseStep 1712153 = 1284115) B1284115
theorem B6496301 : Blo 1140634 6496301 := bstep (se 3 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 6496301 = 2436113) B2436113
theorem B3252275 : Blo 1140634 3252275 := bstep (se 1 (by rfl) ⟨2439206, by rfl⟩ : syracuseStep 3252275 = 4878413) B4878413
theorem B2170955 : Blo 1140634 2170955 := bstep (se 1 (by rfl) ⟨1628216, by rfl⟩ : syracuseStep 2170955 = 3256433) B3256433
theorem B4628573 : Blo 1140634 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B6168707 : Blo 1140634 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B1712267 : Blo 1140634 1712267 := bstep (se 1 (by rfl) ⟨1284200, by rfl⟩ : syracuseStep 1712267 = 2568401) B2568401
theorem B1712279 : Blo 1140634 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B1286347 : Blo 1140634 1286347 := bstep (se 1 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 1286347 = 1929521) B1929521
theorem B1712345 : Blo 1140634 1712345 := bstep (se 2 (by rfl) ⟨642129, by rfl⟩ : syracuseStep 1712345 = 1284259) B1284259
theorem B2171137 : Blo 1140634 2171137 := bstep (se 2 (by rfl) ⟨814176, by rfl⟩ : syracuseStep 2171137 = 1628353) B1628353
theorem B1286455 : Blo 1140634 1286455 := bstep (se 1 (by rfl) ⟨964841, by rfl⟩ : syracuseStep 1286455 = 1929683) B1929683
theorem B1712459 : Blo 1140634 1712459 := bstep (se 1 (by rfl) ⟨1284344, by rfl⟩ : syracuseStep 1712459 = 2568689) B2568689
theorem B1712471 : Blo 1140634 1712471 := bstep (se 1 (by rfl) ⟨1284353, by rfl⟩ : syracuseStep 1712471 = 2568707) B2568707
theorem B1712537 : Blo 1140634 1712537 := bstep (se 2 (by rfl) ⟨642201, by rfl⟩ : syracuseStep 1712537 = 1284403) B1284403
theorem B1286635 : Blo 1140634 1286635 := bstep (se 1 (by rfl) ⟨964976, by rfl⟩ : syracuseStep 1286635 = 1929953) B1929953
theorem B1712651 : Blo 1140634 1712651 := bstep (se 1 (by rfl) ⟨1284488, by rfl⟩ : syracuseStep 1712651 = 2568977) B2568977
theorem B1712663 : Blo 1140634 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B5775947 : Blo 1140634 5775947 := bstep (se 1 (by rfl) ⟨4331960, by rfl⟩ : syracuseStep 5775947 = 8663921) B8663921
theorem B1286743 : Blo 1140634 1286743 := bstep (se 1 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 1286743 = 1930115) B1930115
theorem B1712729 : Blo 1140634 1712729 := bstep (se 2 (by rfl) ⟨642273, by rfl⟩ : syracuseStep 1712729 = 1284547) B1284547
theorem B2171585 : Blo 1140634 2171585 := bstep (se 2 (by rfl) ⟨814344, by rfl⟩ : syracuseStep 2171585 = 1628689) B1628689
theorem B1712843 : Blo 1140634 1712843 := bstep (se 1 (by rfl) ⟨1284632, by rfl⟩ : syracuseStep 1712843 = 2569265) B2569265
theorem B1712855 : Blo 1140634 1712855 := bstep (se 1 (by rfl) ⟨1284641, by rfl⟩ : syracuseStep 1712855 = 2569283) B2569283
theorem B1286923 : Blo 1140634 1286923 := bstep (se 1 (by rfl) ⟨965192, by rfl⟩ : syracuseStep 1286923 = 1930385) B1930385
theorem B1712921 : Blo 1140634 1712921 := bstep (se 2 (by rfl) ⟨642345, by rfl⟩ : syracuseStep 1712921 = 1284691) B1284691
theorem B6169445 : Blo 1140634 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B1287031 : Blo 1140634 1287031 := bstep (se 1 (by rfl) ⟨965273, by rfl⟩ : syracuseStep 1287031 = 1930547) B1930547
theorem B1713035 : Blo 1140634 1713035 := bstep (se 1 (by rfl) ⟨1284776, by rfl⟩ : syracuseStep 1713035 = 2569553) B2569553
theorem B1713047 : Blo 1140634 1713047 := bstep (se 1 (by rfl) ⟨1284785, by rfl⟩ : syracuseStep 1713047 = 2569571) B2569571
theorem B1713113 : Blo 1140634 1713113 := bstep (se 2 (by rfl) ⟨642417, by rfl⟩ : syracuseStep 1713113 = 1284835) B1284835
theorem B2171927 : Blo 1140634 2171927 := bstep (se 1 (by rfl) ⟨1628945, by rfl⟩ : syracuseStep 2171927 = 3257891) B3257891
theorem B1287211 : Blo 1140634 1287211 := bstep (se 1 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 1287211 = 1930817) B1930817
theorem B1713227 : Blo 1140634 1713227 := bstep (se 1 (by rfl) ⟨1284920, by rfl⟩ : syracuseStep 1713227 = 2569841) B2569841
theorem B1713239 : Blo 1140634 1713239 := bstep (se 1 (by rfl) ⟨1284929, by rfl⟩ : syracuseStep 1713239 = 2569859) B2569859
theorem B1287319 : Blo 1140634 1287319 := bstep (se 1 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 1287319 = 1930979) B1930979
theorem B1713305 : Blo 1140634 1713305 := bstep (se 2 (by rfl) ⟨642489, by rfl⟩ : syracuseStep 1713305 = 1284979) B1284979
theorem B1713419 : Blo 1140634 1713419 := bstep (se 1 (by rfl) ⟨1285064, by rfl⟩ : syracuseStep 1713419 = 2570129) B2570129
theorem B1713431 : Blo 1140634 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B1287499 : Blo 1140634 1287499 := bstep (se 1 (by rfl) ⟨965624, by rfl⟩ : syracuseStep 1287499 = 1931249) B1931249
theorem B1713497 : Blo 1140634 1713497 := bstep (se 2 (by rfl) ⟨642561, by rfl⟩ : syracuseStep 1713497 = 1285123) B1285123
theorem B1287607 : Blo 1140634 1287607 := bstep (se 1 (by rfl) ⟨965705, by rfl⟩ : syracuseStep 1287607 = 1931411) B1931411
theorem B1713611 : Blo 1140634 1713611 := bstep (se 1 (by rfl) ⟨1285208, by rfl⟩ : syracuseStep 1713611 = 2570417) B2570417
theorem B2893259 : Blo 1140634 2893259 := bstep (se 1 (by rfl) ⟨2169944, by rfl⟩ : syracuseStep 2893259 = 4339889) B4339889
theorem B1713623 : Blo 1140634 1713623 := bstep (se 1 (by rfl) ⟨1285217, by rfl⟩ : syracuseStep 1713623 = 2570435) B2570435
theorem B1713689 : Blo 1140634 1713689 := bstep (se 2 (by rfl) ⟨642633, by rfl⟩ : syracuseStep 1713689 = 1285267) B1285267
theorem B1713803 : Blo 1140634 1713803 := bstep (se 1 (by rfl) ⟨1285352, by rfl⟩ : syracuseStep 1713803 = 2570705) B2570705
theorem B1713815 : Blo 1140634 1713815 := bstep (se 1 (by rfl) ⟨1285361, by rfl⟩ : syracuseStep 1713815 = 2570723) B2570723
theorem B2172595 : Blo 1140634 2172595 := bstep (se 1 (by rfl) ⟨1629446, by rfl⟩ : syracuseStep 2172595 = 3258893) B3258893
theorem B1713881 : Blo 1140634 1713881 := bstep (se 2 (by rfl) ⟨642705, by rfl⟩ : syracuseStep 1713881 = 1285411) B1285411
theorem B1713995 : Blo 1140634 1713995 := bstep (se 1 (by rfl) ⟨1285496, by rfl⟩ : syracuseStep 1713995 = 2570993) B2570993
theorem B1714007 : Blo 1140634 1714007 := bstep (se 1 (by rfl) ⟨1285505, by rfl⟩ : syracuseStep 1714007 = 2571011) B2571011
theorem B1714073 : Blo 1140634 1714073 := bstep (se 2 (by rfl) ⟨642777, by rfl⟩ : syracuseStep 1714073 = 1285555) B1285555
theorem B1714187 : Blo 1140634 1714187 := bstep (se 1 (by rfl) ⟨1285640, by rfl⟩ : syracuseStep 1714187 = 2571281) B2571281
theorem B1714199 : Blo 1140634 1714199 := bstep (se 1 (by rfl) ⟨1285649, by rfl⟩ : syracuseStep 1714199 = 2571299) B2571299
theorem B3254347 : Blo 1140634 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B1714265 : Blo 1140634 1714265 := bstep (se 2 (by rfl) ⟨642849, by rfl⟩ : syracuseStep 1714265 = 1285699) B1285699
theorem B1714379 : Blo 1140634 1714379 := bstep (se 1 (by rfl) ⟨1285784, by rfl⟩ : syracuseStep 1714379 = 2571569) B2571569
theorem B1714391 : Blo 1140634 1714391 := bstep (se 1 (by rfl) ⟨1285793, by rfl⟩ : syracuseStep 1714391 = 2571587) B2571587
theorem B1714457 : Blo 1140634 1714457 := bstep (se 2 (by rfl) ⟨642921, by rfl⟩ : syracuseStep 1714457 = 1285843) B1285843
theorem B5777729 : Blo 1140634 5777729 := bstep (se 2 (by rfl) ⟨2166648, by rfl⟩ : syracuseStep 5777729 = 4333297) B4333297
theorem B2566475 : Blo 1140634 2566475 := bstep (se 1 (by rfl) ⟨1924856, by rfl⟩ : syracuseStep 2566475 = 3849713) B3849713
theorem B9251147 : Blo 1140634 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B2566529 : Blo 1140634 2566529 := bstep (se 2 (by rfl) ⟨962448, by rfl⟩ : syracuseStep 2566529 = 1924897) B1924897
theorem B1714571 : Blo 1140634 1714571 := bstep (se 1 (by rfl) ⟨1285928, by rfl⟩ : syracuseStep 1714571 = 2571857) B2571857
theorem B1714583 : Blo 1140634 1714583 := bstep (se 1 (by rfl) ⟨1285937, by rfl⟩ : syracuseStep 1714583 = 2571875) B2571875
theorem B2894231 : Blo 1140634 2894231 := bstep (se 1 (by rfl) ⟨2170673, by rfl⟩ : syracuseStep 2894231 = 4341347) B4341347
theorem B11708849 : Blo 1140634 11708849 := bstep (se 2 (by rfl) ⟨4390818, by rfl⟩ : syracuseStep 11708849 = 8781637) B8781637
theorem B18557363 : Blo 1140634 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B1714649 : Blo 1140634 1714649 := bstep (se 2 (by rfl) ⟨642993, by rfl⟩ : syracuseStep 1714649 = 1285987) B1285987
theorem B3254849 : Blo 1140634 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B1714763 : Blo 1140634 1714763 := bstep (se 1 (by rfl) ⟨1286072, by rfl⟩ : syracuseStep 1714763 = 2572145) B2572145
theorem B1714775 : Blo 1140634 1714775 := bstep (se 1 (by rfl) ⟨1286081, by rfl⟩ : syracuseStep 1714775 = 2572163) B2572163
theorem B2566745 : Blo 1140634 2566745 := bstep (se 2 (by rfl) ⟨962529, by rfl⟩ : syracuseStep 2566745 = 1925059) B1925059
theorem B1714841 : Blo 1140634 1714841 := bstep (se 2 (by rfl) ⟨643065, by rfl⟩ : syracuseStep 1714841 = 1286131) B1286131
theorem B2566835 : Blo 1140634 2566835 := bstep (se 1 (by rfl) ⟨1925126, by rfl⟩ : syracuseStep 2566835 = 3850253) B3850253
theorem B2566871 : Blo 1140634 2566871 := bstep (se 1 (by rfl) ⟨1925153, by rfl⟩ : syracuseStep 2566871 = 3850307) B3850307
theorem B1714955 : Blo 1140634 1714955 := bstep (se 1 (by rfl) ⟨1286216, by rfl⟩ : syracuseStep 1714955 = 2572433) B2572433
theorem B1714967 : Blo 1140634 1714967 := bstep (se 1 (by rfl) ⟨1286225, by rfl⟩ : syracuseStep 1714967 = 2572451) B2572451
theorem B1715033 : Blo 1140634 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B3910493 : Blo 1140634 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B2567051 : Blo 1140634 2567051 := bstep (se 1 (by rfl) ⟨1925288, by rfl⟩ : syracuseStep 2567051 = 3850577) B3850577
theorem B3255191 : Blo 1140634 3255191 := bstep (se 1 (by rfl) ⟨2441393, by rfl⟩ : syracuseStep 3255191 = 4882787) B4882787
theorem B2567105 : Blo 1140634 2567105 := bstep (se 2 (by rfl) ⟨962664, by rfl⟩ : syracuseStep 2567105 = 1925329) B1925329
theorem B1715147 : Blo 1140634 1715147 := bstep (se 1 (by rfl) ⟨1286360, by rfl⟩ : syracuseStep 1715147 = 2572721) B2572721
theorem B1715159 : Blo 1140634 1715159 := bstep (se 1 (by rfl) ⟨1286369, by rfl⟩ : syracuseStep 1715159 = 2572739) B2572739
theorem B8661977 : Blo 1140634 8661977 := bstep (se 2 (by rfl) ⟨3248241, by rfl⟩ : syracuseStep 8661977 = 6496483) B6496483
theorem B1715225 : Blo 1140634 1715225 := bstep (se 2 (by rfl) ⟨643209, by rfl⟩ : syracuseStep 1715225 = 1286419) B1286419
theorem B4336685 : Blo 1140634 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B2894899 : Blo 1140634 2894899 := bstep (se 1 (by rfl) ⟨2171174, by rfl⟩ : syracuseStep 2894899 = 4342349) B4342349
theorem B1715339 : Blo 1140634 1715339 := bstep (se 1 (by rfl) ⟨1286504, by rfl⟩ : syracuseStep 1715339 = 2573009) B2573009
theorem B1715351 : Blo 1140634 1715351 := bstep (se 1 (by rfl) ⟨1286513, by rfl⟩ : syracuseStep 1715351 = 2573027) B2573027
theorem B2567321 : Blo 1140634 2567321 := bstep (se 2 (by rfl) ⟨962745, by rfl⟩ : syracuseStep 2567321 = 1925491) B1925491
theorem B5483699 : Blo 1140634 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B2895041 : Blo 1140634 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B2436311 : Blo 1140634 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B1715417 : Blo 1140634 1715417 := bstep (se 2 (by rfl) ⟨643281, by rfl⟩ : syracuseStep 1715417 = 1286563) B1286563
theorem B2567411 : Blo 1140634 2567411 := bstep (se 1 (by rfl) ⟨1925558, by rfl⟩ : syracuseStep 2567411 = 3851117) B3851117
theorem B2567447 : Blo 1140634 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B1715531 : Blo 1140634 1715531 := bstep (se 1 (by rfl) ⟨1286648, by rfl⟩ : syracuseStep 1715531 = 2573297) B2573297
theorem B1715543 : Blo 1140634 1715543 := bstep (se 1 (by rfl) ⟨1286657, by rfl⟩ : syracuseStep 1715543 = 2573315) B2573315
theorem B1715609 : Blo 1140634 1715609 := bstep (se 2 (by rfl) ⟨643353, by rfl⟩ : syracuseStep 1715609 = 1286707) B1286707
theorem B1158571 : Blo 1140634 1158571 := bstep (se 1 (by rfl) ⟨868928, by rfl⟩ : syracuseStep 1158571 = 1737857) B1737857
theorem B2567627 : Blo 1140634 2567627 := bstep (se 1 (by rfl) ⟨1925720, by rfl⟩ : syracuseStep 2567627 = 3851441) B3851441
theorem B6172121 : Blo 1140634 6172121 := bstep (se 2 (by rfl) ⟨2314545, by rfl⟩ : syracuseStep 6172121 = 4629091) B4629091
theorem B2567681 : Blo 1140634 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B1715723 : Blo 1140634 1715723 := bstep (se 1 (by rfl) ⟨1286792, by rfl⟩ : syracuseStep 1715723 = 2573585) B2573585
theorem B1715735 : Blo 1140634 1715735 := bstep (se 1 (by rfl) ⟨1286801, by rfl⟩ : syracuseStep 1715735 = 2573603) B2573603
theorem B7319105 : Blo 1140634 7319105 := bstep (se 2 (by rfl) ⟨2744664, by rfl⟩ : syracuseStep 7319105 = 5489329) B5489329
theorem B1715801 : Blo 1140634 1715801 := bstep (se 2 (by rfl) ⟨643425, by rfl⟩ : syracuseStep 1715801 = 1286851) B1286851
theorem B1715915 : Blo 1140634 1715915 := bstep (se 1 (by rfl) ⟨1286936, by rfl⟩ : syracuseStep 1715915 = 2573873) B2573873
theorem B1158871 : Blo 1140634 1158871 := bstep (se 1 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 1158871 = 1738307) B1738307
theorem B1715927 : Blo 1140634 1715927 := bstep (se 1 (by rfl) ⟨1286945, by rfl⟩ : syracuseStep 1715927 = 2573891) B2573891
theorem B2567897 : Blo 1140634 2567897 := bstep (se 2 (by rfl) ⟨962961, by rfl⟩ : syracuseStep 2567897 = 1925923) B1925923
theorem B1715993 : Blo 1140634 1715993 := bstep (se 2 (by rfl) ⟨643497, by rfl⟩ : syracuseStep 1715993 = 1286995) B1286995
theorem B2567987 : Blo 1140634 2567987 := bstep (se 1 (by rfl) ⟨1925990, by rfl⟩ : syracuseStep 2567987 = 3851981) B3851981
theorem B4337459 : Blo 1140634 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B2568023 : Blo 1140634 2568023 := bstep (se 1 (by rfl) ⟨1926017, by rfl⟩ : syracuseStep 2568023 = 3852035) B3852035
theorem B1716107 : Blo 1140634 1716107 := bstep (se 1 (by rfl) ⟨1287080, by rfl⟩ : syracuseStep 1716107 = 2574161) B2574161
theorem B1716119 : Blo 1140634 1716119 := bstep (se 1 (by rfl) ⟨1287089, by rfl⟩ : syracuseStep 1716119 = 2574179) B2574179
theorem B1716185 : Blo 1140634 1716185 := bstep (se 2 (by rfl) ⟨643569, by rfl⟩ : syracuseStep 1716185 = 1287139) B1287139
theorem B2568203 : Blo 1140634 2568203 := bstep (se 1 (by rfl) ⟨1926152, by rfl⟩ : syracuseStep 2568203 = 3852305) B3852305
theorem B2568257 : Blo 1140634 2568257 := bstep (se 2 (by rfl) ⟨963096, by rfl⟩ : syracuseStep 2568257 = 1926193) B1926193
theorem B1716299 : Blo 1140634 1716299 := bstep (se 1 (by rfl) ⟨1287224, by rfl⟩ : syracuseStep 1716299 = 2574449) B2574449
theorem B1716311 : Blo 1140634 1716311 := bstep (se 1 (by rfl) ⟨1287233, by rfl⟩ : syracuseStep 1716311 = 2574467) B2574467
theorem B1716377 : Blo 1140634 1716377 := bstep (se 2 (by rfl) ⟨643641, by rfl⟩ : syracuseStep 1716377 = 1287283) B1287283
theorem B5779673 : Blo 1140634 5779673 := bstep (se 2 (by rfl) ⟨2167377, by rfl⟩ : syracuseStep 5779673 = 4334755) B4334755
theorem B1716491 : Blo 1140634 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B1716503 : Blo 1140634 1716503 := bstep (se 1 (by rfl) ⟨1287377, by rfl⟩ : syracuseStep 1716503 = 2574755) B2574755
theorem B2568473 : Blo 1140634 2568473 := bstep (se 2 (by rfl) ⟨963177, by rfl⟩ : syracuseStep 2568473 = 1926355) B1926355
theorem B10170689 : Blo 1140634 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B1716569 : Blo 1140634 1716569 := bstep (se 2 (by rfl) ⟨643713, by rfl⟩ : syracuseStep 1716569 = 1287427) B1287427
theorem B2568563 : Blo 1140634 2568563 := bstep (se 1 (by rfl) ⟨1926422, by rfl⟩ : syracuseStep 2568563 = 3852845) B3852845
theorem B2568599 : Blo 1140634 2568599 := bstep (se 1 (by rfl) ⟨1926449, by rfl⟩ : syracuseStep 2568599 = 3852899) B3852899
theorem B2896307 : Blo 1140634 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B1716683 : Blo 1140634 1716683 := bstep (se 1 (by rfl) ⟨1287512, by rfl⟩ : syracuseStep 1716683 = 2575025) B2575025
theorem B1716695 : Blo 1140634 1716695 := bstep (se 1 (by rfl) ⟨1287521, by rfl⟩ : syracuseStep 1716695 = 2575043) B2575043
theorem B1716761 : Blo 1140634 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B2568779 : Blo 1140634 2568779 := bstep (se 1 (by rfl) ⟨1926584, by rfl⟩ : syracuseStep 2568779 = 3853169) B3853169
theorem B2568833 : Blo 1140634 2568833 := bstep (se 2 (by rfl) ⟨963312, by rfl⟩ : syracuseStep 2568833 = 1926625) B1926625
theorem B2437771 : Blo 1140634 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B1716875 : Blo 1140634 1716875 := bstep (se 1 (by rfl) ⟨1287656, by rfl⟩ : syracuseStep 1716875 = 2575313) B2575313
theorem B1716887 : Blo 1140634 1716887 := bstep (se 1 (by rfl) ⟨1287665, by rfl⟩ : syracuseStep 1716887 = 2575331) B2575331
theorem B2569049 : Blo 1140634 2569049 := bstep (se 2 (by rfl) ⟨963393, by rfl⟩ : syracuseStep 2569049 = 1926787) B1926787
theorem B2438027 : Blo 1140634 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B2569139 : Blo 1140634 2569139 := bstep (se 1 (by rfl) ⟨1926854, by rfl⟩ : syracuseStep 2569139 = 3853709) B3853709
theorem B2896843 : Blo 1140634 2896843 := bstep (se 1 (by rfl) ⟨2172632, by rfl⟩ : syracuseStep 2896843 = 4345265) B4345265
theorem B2569175 : Blo 1140634 2569175 := bstep (se 1 (by rfl) ⟨1926881, by rfl⟩ : syracuseStep 2569175 = 3853763) B3853763
theorem B3257309 : Blo 1140634 3257309 := bstep (se 3 (by rfl) ⟨610745, by rfl⟩ : syracuseStep 3257309 = 1221491) B1221491
theorem B8238145 : Blo 1140634 8238145 := bstep (se 2 (by rfl) ⟨3089304, by rfl⟩ : syracuseStep 8238145 = 6178609) B6178609
theorem B2896985 : Blo 1140634 2896985 := bstep (se 2 (by rfl) ⟨1086369, by rfl⟩ : syracuseStep 2896985 = 2172739) B2172739
theorem B2569355 : Blo 1140634 2569355 := bstep (se 1 (by rfl) ⟨1927016, by rfl⟩ : syracuseStep 2569355 = 3854033) B3854033
theorem B2569409 : Blo 1140634 2569409 := bstep (se 2 (by rfl) ⟨963528, by rfl⟩ : syracuseStep 2569409 = 1927057) B1927057
theorem B4338947 : Blo 1140634 4338947 := bstep (se 1 (by rfl) ⟨3254210, by rfl⟩ : syracuseStep 4338947 = 6508421) B6508421
theorem B3257651 : Blo 1140634 3257651 := bstep (se 1 (by rfl) ⟨2443238, by rfl⟩ : syracuseStep 3257651 = 4886477) B4886477
theorem B2569625 : Blo 1140634 2569625 := bstep (se 2 (by rfl) ⟨963609, by rfl⟩ : syracuseStep 2569625 = 1927219) B1927219
theorem B2569715 : Blo 1140634 2569715 := bstep (se 1 (by rfl) ⟨1927286, by rfl⟩ : syracuseStep 2569715 = 3854573) B3854573
theorem B2569751 : Blo 1140634 2569751 := bstep (se 1 (by rfl) ⟨1927313, by rfl⟩ : syracuseStep 2569751 = 3854627) B3854627
theorem B8795749 : Blo 1140634 8795749 := bstep (se 4 (by rfl) ⟨824601, by rfl⟩ : syracuseStep 8795749 = 1649203) B1649203
theorem B2569931 : Blo 1140634 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B4339403 : Blo 1140634 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B2569985 : Blo 1140634 2569985 := bstep (se 2 (by rfl) ⟨963744, by rfl⟩ : syracuseStep 2569985 = 1927489) B1927489
theorem B5781293 : Blo 1140634 5781293 := bstep (se 3 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 5781293 = 2167985) B2167985
theorem B2439001 : Blo 1140634 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B4339601 : Blo 1140634 4339601 := bstep (se 2 (by rfl) ⟨1627350, by rfl⟩ : syracuseStep 4339601 = 3254701) B3254701
theorem B2570201 : Blo 1140634 2570201 := bstep (se 2 (by rfl) ⟨963825, by rfl⟩ : syracuseStep 2570201 = 1927651) B1927651
theorem B2439155 : Blo 1140634 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B2570291 : Blo 1140634 2570291 := bstep (se 1 (by rfl) ⟨1927718, by rfl⟩ : syracuseStep 2570291 = 3855437) B3855437
theorem B2570327 : Blo 1140634 2570327 := bstep (se 1 (by rfl) ⟨1927745, by rfl⟩ : syracuseStep 2570327 = 3855491) B3855491
theorem B2570507 : Blo 1140634 2570507 := bstep (se 1 (by rfl) ⟨1927880, by rfl⟩ : syracuseStep 2570507 = 3855761) B3855761
theorem B8665379 : Blo 1140634 8665379 := bstep (se 1 (by rfl) ⟨6499034, by rfl⟩ : syracuseStep 8665379 = 12998069) B12998069
theorem B2570561 : Blo 1140634 2570561 := bstep (se 2 (by rfl) ⟨963960, by rfl⟩ : syracuseStep 2570561 = 1927921) B1927921
theorem B20855141 : Blo 1140634 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B2439667 : Blo 1140634 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B2570777 : Blo 1140634 2570777 := bstep (se 2 (by rfl) ⟨964041, by rfl⟩ : syracuseStep 2570777 = 1928083) B1928083
theorem B2570867 : Blo 1140634 2570867 := bstep (se 1 (by rfl) ⟨1928150, by rfl⟩ : syracuseStep 2570867 = 3856301) B3856301
theorem B2570903 : Blo 1140634 2570903 := bstep (se 1 (by rfl) ⟨1928177, by rfl⟩ : syracuseStep 2570903 = 3856355) B3856355
theorem B4340375 : Blo 1140634 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B2571083 : Blo 1140634 2571083 := bstep (se 1 (by rfl) ⟨1928312, by rfl⟩ : syracuseStep 2571083 = 3856625) B3856625
theorem B4340573 : Blo 1140634 4340573 := bstep (se 3 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 4340573 = 1627715) B1627715
theorem B2571137 : Blo 1140634 2571137 := bstep (se 2 (by rfl) ⟨964176, by rfl⟩ : syracuseStep 2571137 = 1928353) B1928353
theorem B2472947 : Blo 1140634 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B7322669 : Blo 1140634 7322669 := bstep (se 3 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 7322669 = 2746001) B2746001
theorem B2604083 : Blo 1140634 2604083 := bstep (se 1 (by rfl) ⟨1953062, by rfl⟩ : syracuseStep 2604083 = 3906125) B3906125
theorem B2571353 : Blo 1140634 2571353 := bstep (se 2 (by rfl) ⟨964257, by rfl⟩ : syracuseStep 2571353 = 1928515) B1928515
theorem B19512413 : Blo 1140634 19512413 := bstep (se 3 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 19512413 = 7317155) B7317155
theorem B2440343 : Blo 1140634 2440343 := bstep (se 1 (by rfl) ⟨1830257, by rfl⟩ : syracuseStep 2440343 = 3660515) B3660515
theorem B2571443 : Blo 1140634 2571443 := bstep (se 1 (by rfl) ⟨1928582, by rfl⟩ : syracuseStep 2571443 = 3857165) B3857165
theorem B2440385 : Blo 1140634 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B2571479 : Blo 1140634 2571479 := bstep (se 1 (by rfl) ⟨1928609, by rfl⟩ : syracuseStep 2571479 = 3857219) B3857219
theorem B6503773 : Blo 1140634 6503773 := bstep (se 3 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 6503773 = 2438915) B2438915
theorem B5488003 : Blo 1140634 5488003 := bstep (se 1 (by rfl) ⟨4116002, by rfl⟩ : syracuseStep 5488003 = 8232005) B8232005
theorem B2571659 : Blo 1140634 2571659 := bstep (se 1 (by rfl) ⟨1928744, by rfl⟩ : syracuseStep 2571659 = 3857489) B3857489
theorem B2571713 : Blo 1140634 2571713 := bstep (se 2 (by rfl) ⟨964392, by rfl⟩ : syracuseStep 2571713 = 1928785) B1928785
theorem B4636097 : Blo 1140634 4636097 := bstep (se 2 (by rfl) ⟨1738536, by rfl⟩ : syracuseStep 4636097 = 3477073) B3477073
theorem B3915211 : Blo 1140634 3915211 := bstep (se 1 (by rfl) ⟨2936408, by rfl⟩ : syracuseStep 3915211 = 5872817) B5872817
theorem B3849821 : Blo 1140634 3849821 := bstep (se 3 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 3849821 = 1443683) B1443683
theorem B2571929 : Blo 1140634 2571929 := bstep (se 2 (by rfl) ⟨964473, by rfl⟩ : syracuseStep 2571929 = 1928947) B1928947
theorem B9256625 : Blo 1140634 9256625 := bstep (se 2 (by rfl) ⟨3471234, by rfl⟩ : syracuseStep 9256625 = 6942469) B6942469
theorem B2572019 : Blo 1140634 2572019 := bstep (se 1 (by rfl) ⟨1929014, by rfl⟩ : syracuseStep 2572019 = 3858029) B3858029
theorem B2572055 : Blo 1140634 2572055 := bstep (se 1 (by rfl) ⟨1929041, by rfl⟩ : syracuseStep 2572055 = 3858083) B3858083
theorem B2572235 : Blo 1140634 2572235 := bstep (se 1 (by rfl) ⟨1929176, by rfl⟩ : syracuseStep 2572235 = 3858353) B3858353
theorem B2572289 : Blo 1140634 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B9879617 : Blo 1140634 9879617 := bstep (se 2 (by rfl) ⟨3704856, by rfl⟩ : syracuseStep 9879617 = 7409713) B7409713
theorem B2572505 : Blo 1140634 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B2572595 : Blo 1140634 2572595 := bstep (se 1 (by rfl) ⟨1929446, by rfl⟩ : syracuseStep 2572595 = 3858893) B3858893
theorem B2572631 : Blo 1140634 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B16499123 : Blo 1140634 16499123 := bstep (se 1 (by rfl) ⟨12374342, by rfl⟩ : syracuseStep 16499123 = 24748685) B24748685
theorem B2572811 : Blo 1140634 2572811 := bstep (se 1 (by rfl) ⟨1929608, by rfl⟩ : syracuseStep 2572811 = 3859217) B3859217
theorem B62538257 : Blo 1140634 62538257 := bstep (se 2 (by rfl) ⟨23451846, by rfl⟩ : syracuseStep 62538257 = 46903693) B46903693
theorem B2572865 : Blo 1140634 2572865 := bstep (se 2 (by rfl) ⟨964824, by rfl⟩ : syracuseStep 2572865 = 1929649) B1929649
theorem B12337757 : Blo 1140634 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B3850955 : Blo 1140634 3850955 := bstep (se 1 (by rfl) ⟨2888216, by rfl⟩ : syracuseStep 3850955 = 5776433) B5776433
theorem B79086293 : Blo 1140634 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B4342531 : Blo 1140634 4342531 := bstep (se 1 (by rfl) ⟨3256898, by rfl⟩ : syracuseStep 4342531 = 6513797) B6513797
theorem B2573081 : Blo 1140634 2573081 := bstep (se 2 (by rfl) ⟨964905, by rfl⟩ : syracuseStep 2573081 = 1929811) B1929811
theorem B2573171 : Blo 1140634 2573171 := bstep (se 1 (by rfl) ⟨1929878, by rfl⟩ : syracuseStep 2573171 = 3859757) B3859757
theorem B2573207 : Blo 1140634 2573207 := bstep (se 1 (by rfl) ⟨1929905, by rfl⟩ : syracuseStep 2573207 = 3859811) B3859811
theorem B3851225 : Blo 1140634 3851225 := bstep (se 2 (by rfl) ⟨1444209, by rfl⟩ : syracuseStep 3851225 = 2888419) B2888419
theorem B15647705 : Blo 1140634 15647705 := bstep (se 2 (by rfl) ⟨5867889, by rfl⟩ : syracuseStep 15647705 = 11735779) B11735779
theorem B8242181 : Blo 1140634 8242181 := bstep (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) B1545409
theorem B4342835 : Blo 1140634 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B13911115 : Blo 1140634 13911115 := bstep (se 1 (by rfl) ⟨10433336, by rfl⟩ : syracuseStep 13911115 = 20866673) B20866673
theorem B2573387 : Blo 1140634 2573387 := bstep (se 1 (by rfl) ⟨1930040, by rfl⟩ : syracuseStep 2573387 = 3860081) B3860081
theorem B2573441 : Blo 1140634 2573441 := bstep (se 2 (by rfl) ⟨965040, by rfl⟩ : syracuseStep 2573441 = 1930081) B1930081
theorem B2344151 : Blo 1140634 2344151 := bstep (se 1 (by rfl) ⟨1758113, by rfl⟩ : syracuseStep 2344151 = 3516227) B3516227
theorem B2606411 : Blo 1140634 2606411 := bstep (se 1 (by rfl) ⟨1954808, by rfl⟩ : syracuseStep 2606411 = 3909617) B3909617
theorem B2573657 : Blo 1140634 2573657 := bstep (se 2 (by rfl) ⟨965121, by rfl⟩ : syracuseStep 2573657 = 1930243) B1930243
theorem B1787275 : Blo 1140634 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B2573747 : Blo 1140634 2573747 := bstep (se 1 (by rfl) ⟨1930310, by rfl⟩ : syracuseStep 2573747 = 3860621) B3860621
theorem B2573783 : Blo 1140634 2573783 := bstep (se 1 (by rfl) ⟨1930337, by rfl⟩ : syracuseStep 2573783 = 3860675) B3860675
theorem B6178265 : Blo 1140634 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B12338705 : Blo 1140634 12338705 := bstep (se 2 (by rfl) ⟨4627014, by rfl⟩ : syracuseStep 12338705 = 9254029) B9254029
theorem B5490251 : Blo 1140634 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B5785181 : Blo 1140634 5785181 := bstep (se 3 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 5785181 = 2169443) B2169443
theorem B2573963 : Blo 1140634 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B3851927 : Blo 1140634 3851927 := bstep (se 1 (by rfl) ⟨2888945, by rfl⟩ : syracuseStep 3851927 = 5777891) B5777891
theorem B4343489 : Blo 1140634 4343489 := bstep (se 2 (by rfl) ⟨1628808, by rfl⟩ : syracuseStep 4343489 = 3257617) B3257617
theorem B2574017 : Blo 1140634 2574017 := bstep (se 2 (by rfl) ⟨965256, by rfl⟩ : syracuseStep 2574017 = 1930513) B1930513
theorem B1853209 : Blo 1140634 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B2574233 : Blo 1140634 2574233 := bstep (se 2 (by rfl) ⟨965337, by rfl⟩ : syracuseStep 2574233 = 1930675) B1930675
theorem B2607041 : Blo 1140634 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B2574323 : Blo 1140634 2574323 := bstep (se 1 (by rfl) ⟨1930742, by rfl⟩ : syracuseStep 2574323 = 3861485) B3861485
theorem B1624087 : Blo 1140634 1624087 := bstep (se 1 (by rfl) ⟨1218065, by rfl⟩ : syracuseStep 1624087 = 2436131) B2436131
theorem B2574359 : Blo 1140634 2574359 := bstep (se 1 (by rfl) ⟨1930769, by rfl⟩ : syracuseStep 2574359 = 3861539) B3861539
theorem B2443289 : Blo 1140634 2443289 := bstep (se 2 (by rfl) ⟨916233, by rfl⟩ : syracuseStep 2443289 = 1832467) B1832467
theorem B31311947 : Blo 1140634 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B3852467 : Blo 1140634 3852467 := bstep (se 1 (by rfl) ⟨2889350, by rfl⟩ : syracuseStep 3852467 = 5778701) B5778701
theorem B2574539 : Blo 1140634 2574539 := bstep (se 1 (by rfl) ⟨1930904, by rfl⟩ : syracuseStep 2574539 = 3861809) B3861809
theorem B2574593 : Blo 1140634 2574593 := bstep (se 2 (by rfl) ⟨965472, by rfl⟩ : syracuseStep 2574593 = 1930945) B1930945
theorem B2443699 : Blo 1140634 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B3852737 : Blo 1140634 3852737 := bstep (se 2 (by rfl) ⟨1444776, by rfl⟩ : syracuseStep 3852737 = 2889553) B2889553
theorem B2574809 : Blo 1140634 2574809 := bstep (se 2 (by rfl) ⟨965553, by rfl⟩ : syracuseStep 2574809 = 1931107) B1931107
theorem B2476555 : Blo 1140634 2476555 := bstep (se 1 (by rfl) ⟨1857416, by rfl⟩ : syracuseStep 2476555 = 3714833) B3714833
theorem B17582609 : Blo 1140634 17582609 := bstep (se 2 (by rfl) ⟨6593478, by rfl⟩ : syracuseStep 17582609 = 13186957) B13186957
theorem B2574899 : Blo 1140634 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B2574935 : Blo 1140634 2574935 := bstep (se 1 (by rfl) ⟨1931201, by rfl⟩ : syracuseStep 2574935 = 3862403) B3862403
theorem B7326359 : Blo 1140634 7326359 := bstep (se 1 (by rfl) ⟨5494769, by rfl⟩ : syracuseStep 7326359 = 10989539) B10989539
theorem B2444033 : Blo 1140634 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2575115 : Blo 1140634 2575115 := bstep (se 1 (by rfl) ⟨1931336, by rfl⟩ : syracuseStep 2575115 = 3862673) B3862673
theorem B8801069 : Blo 1140634 8801069 := bstep (se 3 (by rfl) ⟨1650200, by rfl⟩ : syracuseStep 8801069 = 3300401) B3300401
theorem B2575169 : Blo 1140634 2575169 := bstep (se 2 (by rfl) ⟨965688, by rfl⟩ : syracuseStep 2575169 = 1931377) B1931377
theorem B1624907 : Blo 1140634 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B4344749 : Blo 1140634 4344749 := bstep (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) B1629281
theorem B4344779 : Blo 1140634 4344779 := bstep (se 1 (by rfl) ⟨3258584, by rfl⟩ : syracuseStep 4344779 = 6517169) B6517169
theorem B3132377 : Blo 1140634 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B3853277 : Blo 1140634 3853277 := bstep (se 3 (by rfl) ⟨722489, by rfl⟩ : syracuseStep 3853277 = 1444979) B1444979
theorem B2575385 : Blo 1140634 2575385 := bstep (se 2 (by rfl) ⟨965769, by rfl⟩ : syracuseStep 2575385 = 1931539) B1931539
theorem B8670725 : Blo 1140634 8670725 := bstep (se 4 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 8670725 = 1625761) B1625761
theorem B4345433 : Blo 1140634 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B23449219 : Blo 1140634 23449219 := bstep (se 1 (by rfl) ⟨17586914, by rfl⟩ : syracuseStep 23449219 = 35173829) B35173829
theorem B5787287 : Blo 1140634 5787287 := bstep (se 1 (by rfl) ⟨4340465, by rfl⟩ : syracuseStep 5787287 = 8680931) B8680931
theorem B2608919 : Blo 1140634 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B4345751 : Blo 1140634 4345751 := bstep (se 1 (by rfl) ⟨3259313, by rfl⟩ : syracuseStep 4345751 = 6518627) B6518627
theorem B3854411 : Blo 1140634 3854411 := bstep (se 1 (by rfl) ⟨2890808, by rfl⟩ : syracuseStep 3854411 = 5781617) B5781617
theorem B4116653 : Blo 1140634 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B3854681 : Blo 1140634 3854681 := bstep (se 2 (by rfl) ⟨1445505, by rfl⟩ : syracuseStep 3854681 = 2891011) B2891011
theorem B10572209 : Blo 1140634 10572209 := bstep (se 2 (by rfl) ⟨3964578, by rfl⟩ : syracuseStep 10572209 = 7929157) B7929157
theorem B13390865 : Blo 1140634 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B3855383 : Blo 1140634 3855383 := bstep (se 1 (by rfl) ⟨2891537, by rfl⟩ : syracuseStep 3855383 = 5783075) B5783075
theorem B7328843 : Blo 1140634 7328843 := bstep (se 1 (by rfl) ⟨5496632, by rfl⟩ : syracuseStep 7328843 = 10993265) B10993265
theorem B2741465 : Blo 1140634 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B1955033 : Blo 1140634 1955033 := bstep (se 2 (by rfl) ⟨733137, by rfl⟩ : syracuseStep 1955033 = 1466275) B1466275
theorem B19813697 : Blo 1140634 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B2610497 : Blo 1140634 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B2315713 : Blo 1140634 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B2119115 : Blo 1140634 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B19551779 : Blo 1140634 19551779 := bstep (se 1 (by rfl) ⟨14663834, by rfl⟩ : syracuseStep 19551779 = 29327669) B29327669
theorem B3855923 : Blo 1140634 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B166581845 : Blo 1140634 166581845 := bstep (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) B1952131
theorem B4118323 : Blo 1140634 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B3856193 : Blo 1140634 3856193 := bstep (se 2 (by rfl) ⟨1446072, by rfl⟩ : syracuseStep 3856193 = 2892145) B2892145
theorem B8673155 : Blo 1140634 8673155 := bstep (se 1 (by rfl) ⟨6504866, by rfl⟩ : syracuseStep 8673155 = 13009733) B13009733
theorem B2316185 : Blo 1140634 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B7919795 : Blo 1140634 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B3856733 : Blo 1140634 3856733 := bstep (se 3 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 3856733 = 1446275) B1446275
theorem B3300043 : Blo 1140634 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B5495597 : Blo 1140634 5495597 := bstep (se 3 (by rfl) ⟨1030424, by rfl⟩ : syracuseStep 5495597 = 2060849) B2060849
theorem B2317207 : Blo 1140634 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B1301527 : Blo 1140634 1301527 := bstep (se 1 (by rfl) ⟨976145, by rfl⟩ : syracuseStep 1301527 = 1952291) B1952291
theorem B5790851 : Blo 1140634 5790851 := bstep (se 1 (by rfl) ⟨4343138, by rfl⟩ : syracuseStep 5790851 = 8686277) B8686277
theorem B3857867 : Blo 1140634 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B6938243 : Blo 1140634 6938243 := bstep (se 1 (by rfl) ⟨5203682, by rfl⟩ : syracuseStep 6938243 = 10407365) B10407365
theorem B1924823 : Blo 1140634 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B3858137 : Blo 1140634 3858137 := bstep (se 2 (by rfl) ⟨1446801, by rfl⟩ : syracuseStep 3858137 = 2893603) B2893603
theorem B2055947 : Blo 1140634 2055947 := bstep (se 1 (by rfl) ⟨1541960, by rfl⟩ : syracuseStep 2055947 = 3083921) B3083921
theorem B1924951 : Blo 1140634 1924951 := bstep (se 1 (by rfl) ⟨1443713, by rfl⟩ : syracuseStep 1924951 = 2887427) B2887427
theorem B4120513 : Blo 1140634 4120513 := bstep (se 2 (by rfl) ⟨1545192, by rfl⟩ : syracuseStep 4120513 = 3090385) B3090385
theorem B1302571 : Blo 1140634 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B4874413 : Blo 1140634 4874413 := bstep (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) B1827905
theorem B7332227 : Blo 1140634 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B3858839 : Blo 1140634 3858839 := bstep (se 1 (by rfl) ⟨2894129, by rfl⟩ : syracuseStep 3858839 = 5788259) B5788259
theorem B6513047 : Blo 1140634 6513047 := bstep (se 1 (by rfl) ⟨4884785, by rfl⟩ : syracuseStep 6513047 = 9769571) B9769571
theorem B1925579 : Blo 1140634 1925579 := bstep (se 1 (by rfl) ⟨1444184, by rfl⟩ : syracuseStep 1925579 = 2888369) B2888369
theorem B4874755 : Blo 1140634 4874755 := bstep (se 1 (by rfl) ⟨3656066, by rfl⟩ : syracuseStep 4874755 = 7312133) B7312133
theorem B2056769 : Blo 1140634 2056769 := bstep (se 2 (by rfl) ⟨771288, by rfl⟩ : syracuseStep 2056769 = 1542577) B1542577
theorem B1925707 : Blo 1140634 1925707 := bstep (se 1 (by rfl) ⟨1444280, by rfl⟩ : syracuseStep 1925707 = 2888561) B2888561
theorem B2056855 : Blo 1140634 2056855 := bstep (se 1 (by rfl) ⟨1542641, by rfl⟩ : syracuseStep 2056855 = 3085283) B3085283
theorem B1172183 : Blo 1140634 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1925849 : Blo 1140634 1925849 := bstep (se 2 (by rfl) ⟨722193, by rfl⟩ : syracuseStep 1925849 = 1444387) B1444387
theorem B1925977 : Blo 1140634 1925977 := bstep (se 2 (by rfl) ⟨722241, by rfl⟩ : syracuseStep 1925977 = 1444483) B1444483
theorem B3859379 : Blo 1140634 3859379 := bstep (se 1 (by rfl) ⟨2894534, by rfl⟩ : syracuseStep 3859379 = 5789069) B5789069
theorem B2319283 : Blo 1140634 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B2319347 : Blo 1140634 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B10183781 : Blo 1140634 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B9757847 : Blo 1140634 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B3859649 : Blo 1140634 3859649 := bstep (se 2 (by rfl) ⟨1447368, by rfl⟩ : syracuseStep 3859649 = 2894737) B2894737
theorem B8676557 : Blo 1140634 8676557 := bstep (se 3 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 8676557 = 3253709) B3253709
theorem B1926551 : Blo 1140634 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B2319769 : Blo 1140634 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B4875713 : Blo 1140634 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B10970585 : Blo 1140634 10970585 := bstep (se 2 (by rfl) ⟨4113969, by rfl⟩ : syracuseStep 10970585 = 8227939) B8227939
theorem B1926679 : Blo 1140634 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B8677043 : Blo 1140634 8677043 := bstep (se 1 (by rfl) ⟨6507782, by rfl⟩ : syracuseStep 8677043 = 13015565) B13015565
theorem B3860189 : Blo 1140634 3860189 := bstep (se 3 (by rfl) ⟨723785, by rfl⟩ : syracuseStep 3860189 = 1447571) B1447571
theorem B4122461 : Blo 1140634 4122461 := bstep (se 3 (by rfl) ⟨772961, by rfl⟩ : syracuseStep 4122461 = 1545923) B1545923
theorem B6252389 : Blo 1140634 6252389 := bstep (se 4 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 6252389 = 1172323) B1172323
theorem B1140651 : Blo 1140634 1140651 := bstep (se 1 (by rfl) ⟨855488, by rfl⟩ : syracuseStep 1140651 = 1710977) B1710977
theorem B1140663 : Blo 1140634 1140663 := bstep (se 1 (by rfl) ⟨855497, by rfl⟩ : syracuseStep 1140663 = 1710995) B1710995
theorem B1140683 : Blo 1140634 1140683 := bstep (se 1 (by rfl) ⟨855512, by rfl⟩ : syracuseStep 1140683 = 1711025) B1711025
theorem B1140695 : Blo 1140634 1140695 := bstep (se 1 (by rfl) ⟨855521, by rfl⟩ : syracuseStep 1140695 = 1711043) B1711043
theorem B1140715 : Blo 1140634 1140715 := bstep (se 1 (by rfl) ⟨855536, by rfl⟩ : syracuseStep 1140715 = 1711073) B1711073
theorem B1140727 : Blo 1140634 1140727 := bstep (se 1 (by rfl) ⟨855545, by rfl⟩ : syracuseStep 1140727 = 1711091) B1711091
theorem B1140747 : Blo 1140634 1140747 := bstep (se 1 (by rfl) ⟨855560, by rfl⟩ : syracuseStep 1140747 = 1711121) B1711121
theorem B1140759 : Blo 1140634 1140759 := bstep (se 1 (by rfl) ⟨855569, by rfl⟩ : syracuseStep 1140759 = 1711139) B1711139
theorem B1140779 : Blo 1140634 1140779 := bstep (se 1 (by rfl) ⟨855584, by rfl⟩ : syracuseStep 1140779 = 1711169) B1711169
theorem B1140791 : Blo 1140634 1140791 := bstep (se 1 (by rfl) ⟨855593, by rfl⟩ : syracuseStep 1140791 = 1711187) B1711187
theorem B1140811 : Blo 1140634 1140811 := bstep (se 1 (by rfl) ⟨855608, by rfl⟩ : syracuseStep 1140811 = 1711217) B1711217
theorem B1140823 : Blo 1140634 1140823 := bstep (se 1 (by rfl) ⟨855617, by rfl⟩ : syracuseStep 1140823 = 1711235) B1711235
theorem B1140843 : Blo 1140634 1140843 := bstep (se 1 (by rfl) ⟨855632, by rfl⟩ : syracuseStep 1140843 = 1711265) B1711265
theorem B1140855 : Blo 1140634 1140855 := bstep (se 1 (by rfl) ⟨855641, by rfl⟩ : syracuseStep 1140855 = 1711283) B1711283
theorem B1140875 : Blo 1140634 1140875 := bstep (se 1 (by rfl) ⟨855656, by rfl⟩ : syracuseStep 1140875 = 1711313) B1711313
theorem B1927307 : Blo 1140634 1927307 := bstep (se 1 (by rfl) ⟨1445480, by rfl⟩ : syracuseStep 1927307 = 2890961) B2890961
theorem B1140887 : Blo 1140634 1140887 := bstep (se 1 (by rfl) ⟨855665, by rfl⟩ : syracuseStep 1140887 = 1711331) B1711331
theorem B1140907 : Blo 1140634 1140907 := bstep (se 1 (by rfl) ⟨855680, by rfl⟩ : syracuseStep 1140907 = 1711361) B1711361
theorem B1140919 : Blo 1140634 1140919 := bstep (se 1 (by rfl) ⟨855689, by rfl⟩ : syracuseStep 1140919 = 1711379) B1711379
theorem B1140939 : Blo 1140634 1140939 := bstep (se 1 (by rfl) ⟨855704, by rfl⟩ : syracuseStep 1140939 = 1711409) B1711409
theorem B1140951 : Blo 1140634 1140951 := bstep (se 1 (by rfl) ⟨855713, by rfl⟩ : syracuseStep 1140951 = 1711427) B1711427
theorem B1140971 : Blo 1140634 1140971 := bstep (se 1 (by rfl) ⟨855728, by rfl⟩ : syracuseStep 1140971 = 1711457) B1711457
theorem B1140983 : Blo 1140634 1140983 := bstep (se 1 (by rfl) ⟨855737, by rfl⟩ : syracuseStep 1140983 = 1711475) B1711475
theorem B1141003 : Blo 1140634 1141003 := bstep (se 1 (by rfl) ⟨855752, by rfl⟩ : syracuseStep 1141003 = 1711505) B1711505
theorem B1927435 : Blo 1140634 1927435 := bstep (se 1 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 1927435 = 2891153) B2891153
theorem B1141015 : Blo 1140634 1141015 := bstep (se 1 (by rfl) ⟨855761, by rfl⟩ : syracuseStep 1141015 = 1711523) B1711523
theorem B1141035 : Blo 1140634 1141035 := bstep (se 1 (by rfl) ⟨855776, by rfl⟩ : syracuseStep 1141035 = 1711553) B1711553
theorem B1141047 : Blo 1140634 1141047 := bstep (se 1 (by rfl) ⟨855785, by rfl⟩ : syracuseStep 1141047 = 1711571) B1711571
theorem B1141067 : Blo 1140634 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B1141079 : Blo 1140634 1141079 := bstep (se 1 (by rfl) ⟨855809, by rfl⟩ : syracuseStep 1141079 = 1711619) B1711619
theorem B3664217 : Blo 1140634 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B1141099 : Blo 1140634 1141099 := bstep (se 1 (by rfl) ⟨855824, by rfl⟩ : syracuseStep 1141099 = 1711649) B1711649
theorem B1141111 : Blo 1140634 1141111 := bstep (se 1 (by rfl) ⟨855833, by rfl⟩ : syracuseStep 1141111 = 1711667) B1711667
theorem B1141131 : Blo 1140634 1141131 := bstep (se 1 (by rfl) ⟨855848, by rfl⟩ : syracuseStep 1141131 = 1711697) B1711697
theorem B1141143 : Blo 1140634 1141143 := bstep (se 1 (by rfl) ⟨855857, by rfl⟩ : syracuseStep 1141143 = 1711715) B1711715
theorem B1927577 : Blo 1140634 1927577 := bstep (se 2 (by rfl) ⟨722841, by rfl⟩ : syracuseStep 1927577 = 1445683) B1445683
theorem B1141163 : Blo 1140634 1141163 := bstep (se 1 (by rfl) ⟨855872, by rfl⟩ : syracuseStep 1141163 = 1711745) B1711745
theorem B1141175 : Blo 1140634 1141175 := bstep (se 1 (by rfl) ⟨855881, by rfl⟩ : syracuseStep 1141175 = 1711763) B1711763
theorem B1141195 : Blo 1140634 1141195 := bstep (se 1 (by rfl) ⟨855896, by rfl⟩ : syracuseStep 1141195 = 1711793) B1711793
theorem B1141207 : Blo 1140634 1141207 := bstep (se 1 (by rfl) ⟨855905, by rfl⟩ : syracuseStep 1141207 = 1711811) B1711811
theorem B1141227 : Blo 1140634 1141227 := bstep (se 1 (by rfl) ⟨855920, by rfl⟩ : syracuseStep 1141227 = 1711841) B1711841
theorem B1141239 : Blo 1140634 1141239 := bstep (se 1 (by rfl) ⟨855929, by rfl⟩ : syracuseStep 1141239 = 1711859) B1711859
theorem B1141259 : Blo 1140634 1141259 := bstep (se 1 (by rfl) ⟨855944, by rfl⟩ : syracuseStep 1141259 = 1711889) B1711889
theorem B1141271 : Blo 1140634 1141271 := bstep (se 1 (by rfl) ⟨855953, by rfl⟩ : syracuseStep 1141271 = 1711907) B1711907
theorem B1927705 : Blo 1140634 1927705 := bstep (se 2 (by rfl) ⟨722889, by rfl⟩ : syracuseStep 1927705 = 1445779) B1445779
theorem B1141291 : Blo 1140634 1141291 := bstep (se 1 (by rfl) ⟨855968, by rfl⟩ : syracuseStep 1141291 = 1711937) B1711937
theorem B1141303 : Blo 1140634 1141303 := bstep (se 1 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 1141303 = 1711955) B1711955
theorem B1141323 : Blo 1140634 1141323 := bstep (se 1 (by rfl) ⟨855992, by rfl⟩ : syracuseStep 1141323 = 1711985) B1711985
theorem B1141335 : Blo 1140634 1141335 := bstep (se 1 (by rfl) ⟨856001, by rfl⟩ : syracuseStep 1141335 = 1712003) B1712003
theorem B1141355 : Blo 1140634 1141355 := bstep (se 1 (by rfl) ⟨856016, by rfl⟩ : syracuseStep 1141355 = 1712033) B1712033
theorem B1141367 : Blo 1140634 1141367 := bstep (se 1 (by rfl) ⟨856025, by rfl⟩ : syracuseStep 1141367 = 1712051) B1712051
theorem B1141387 : Blo 1140634 1141387 := bstep (se 1 (by rfl) ⟨856040, by rfl⟩ : syracuseStep 1141387 = 1712081) B1712081
theorem B1141399 : Blo 1140634 1141399 := bstep (se 1 (by rfl) ⟨856049, by rfl⟩ : syracuseStep 1141399 = 1712099) B1712099
theorem B1141419 : Blo 1140634 1141419 := bstep (se 1 (by rfl) ⟨856064, by rfl⟩ : syracuseStep 1141419 = 1712129) B1712129
theorem B1141431 : Blo 1140634 1141431 := bstep (se 1 (by rfl) ⟨856073, by rfl⟩ : syracuseStep 1141431 = 1712147) B1712147
theorem B40102597 : Blo 1140634 40102597 := bstep (se 4 (by rfl) ⟨3759618, by rfl⟩ : syracuseStep 40102597 = 7519237) B7519237
theorem B1141451 : Blo 1140634 1141451 := bstep (se 1 (by rfl) ⟨856088, by rfl⟩ : syracuseStep 1141451 = 1712177) B1712177
theorem B1141463 : Blo 1140634 1141463 := bstep (se 1 (by rfl) ⟨856097, by rfl⟩ : syracuseStep 1141463 = 1712195) B1712195
theorem B1141483 : Blo 1140634 1141483 := bstep (se 1 (by rfl) ⟨856112, by rfl⟩ : syracuseStep 1141483 = 1712225) B1712225
theorem B1141495 : Blo 1140634 1141495 := bstep (se 1 (by rfl) ⟨856121, by rfl⟩ : syracuseStep 1141495 = 1712243) B1712243
theorem B1141515 : Blo 1140634 1141515 := bstep (se 1 (by rfl) ⟨856136, by rfl⟩ : syracuseStep 1141515 = 1712273) B1712273
theorem B5794577 : Blo 1140634 5794577 := bstep (se 2 (by rfl) ⟨2172966, by rfl⟩ : syracuseStep 5794577 = 4345933) B4345933
theorem B1141527 : Blo 1140634 1141527 := bstep (se 1 (by rfl) ⟨856145, by rfl⟩ : syracuseStep 1141527 = 1712291) B1712291
theorem B1141547 : Blo 1140634 1141547 := bstep (se 1 (by rfl) ⟨856160, by rfl⟩ : syracuseStep 1141547 = 1712321) B1712321
theorem B1141559 : Blo 1140634 1141559 := bstep (se 1 (by rfl) ⟨856169, by rfl⟩ : syracuseStep 1141559 = 1712339) B1712339
theorem B4123457 : Blo 1140634 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B1141579 : Blo 1140634 1141579 := bstep (se 1 (by rfl) ⟨856184, by rfl⟩ : syracuseStep 1141579 = 1712369) B1712369
theorem B4877131 : Blo 1140634 4877131 := bstep (se 1 (by rfl) ⟨3657848, by rfl⟩ : syracuseStep 4877131 = 7315697) B7315697
theorem B3861323 : Blo 1140634 3861323 := bstep (se 1 (by rfl) ⟨2895992, by rfl⟩ : syracuseStep 3861323 = 5791985) B5791985
theorem B1141591 : Blo 1140634 1141591 := bstep (se 1 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 1141591 = 1712387) B1712387
theorem B1141611 : Blo 1140634 1141611 := bstep (se 1 (by rfl) ⟨856208, by rfl⟩ : syracuseStep 1141611 = 1712417) B1712417
theorem B1141623 : Blo 1140634 1141623 := bstep (se 1 (by rfl) ⟨856217, by rfl⟩ : syracuseStep 1141623 = 1712435) B1712435
theorem B1141643 : Blo 1140634 1141643 := bstep (se 1 (by rfl) ⟨856232, by rfl⟩ : syracuseStep 1141643 = 1712465) B1712465
theorem B1141655 : Blo 1140634 1141655 := bstep (se 1 (by rfl) ⟨856241, by rfl⟩ : syracuseStep 1141655 = 1712483) B1712483
theorem B4123543 : Blo 1140634 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B1141675 : Blo 1140634 1141675 := bstep (se 1 (by rfl) ⟨856256, by rfl⟩ : syracuseStep 1141675 = 1712513) B1712513
theorem B1141687 : Blo 1140634 1141687 := bstep (se 1 (by rfl) ⟨856265, by rfl⟩ : syracuseStep 1141687 = 1712531) B1712531
theorem B1141707 : Blo 1140634 1141707 := bstep (se 1 (by rfl) ⟨856280, by rfl⟩ : syracuseStep 1141707 = 1712561) B1712561
theorem B1141719 : Blo 1140634 1141719 := bstep (se 1 (by rfl) ⟨856289, by rfl⟩ : syracuseStep 1141719 = 1712579) B1712579
theorem B1141739 : Blo 1140634 1141739 := bstep (se 1 (by rfl) ⟨856304, by rfl⟩ : syracuseStep 1141739 = 1712609) B1712609
theorem B1141751 : Blo 1140634 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B1141771 : Blo 1140634 1141771 := bstep (se 1 (by rfl) ⟨856328, by rfl⟩ : syracuseStep 1141771 = 1712657) B1712657
theorem B9759761 : Blo 1140634 9759761 := bstep (se 2 (by rfl) ⟨3659910, by rfl⟩ : syracuseStep 9759761 = 7319821) B7319821
theorem B1141783 : Blo 1140634 1141783 := bstep (se 1 (by rfl) ⟨856337, by rfl⟩ : syracuseStep 1141783 = 1712675) B1712675
theorem B1141803 : Blo 1140634 1141803 := bstep (se 1 (by rfl) ⟨856352, by rfl⟩ : syracuseStep 1141803 = 1712705) B1712705
theorem B1141815 : Blo 1140634 1141815 := bstep (se 1 (by rfl) ⟨856361, by rfl⟩ : syracuseStep 1141815 = 1712723) B1712723
theorem B1141835 : Blo 1140634 1141835 := bstep (se 1 (by rfl) ⟨856376, by rfl⟩ : syracuseStep 1141835 = 1712753) B1712753
theorem B1141847 : Blo 1140634 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B1928279 : Blo 1140634 1928279 := bstep (se 1 (by rfl) ⟨1446209, by rfl⟩ : syracuseStep 1928279 = 2892419) B2892419
theorem B3861593 : Blo 1140634 3861593 := bstep (se 2 (by rfl) ⟨1448097, by rfl⟩ : syracuseStep 3861593 = 2896195) B2896195
theorem B4877405 : Blo 1140634 4877405 := bstep (se 3 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 4877405 = 1829027) B1829027
theorem B8678501 : Blo 1140634 8678501 := bstep (se 4 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 8678501 = 1627219) B1627219
theorem B1141867 : Blo 1140634 1141867 := bstep (se 1 (by rfl) ⟨856400, by rfl⟩ : syracuseStep 1141867 = 1712801) B1712801
theorem B1141879 : Blo 1140634 1141879 := bstep (se 1 (by rfl) ⟨856409, by rfl⟩ : syracuseStep 1141879 = 1712819) B1712819
theorem B1141899 : Blo 1140634 1141899 := bstep (se 1 (by rfl) ⟨856424, by rfl⟩ : syracuseStep 1141899 = 1712849) B1712849
theorem B1141911 : Blo 1140634 1141911 := bstep (se 1 (by rfl) ⟨856433, by rfl⟩ : syracuseStep 1141911 = 1712867) B1712867
theorem B17820823 : Blo 1140634 17820823 := bstep (se 1 (by rfl) ⟨13365617, by rfl⟩ : syracuseStep 17820823 = 26731235) B26731235
theorem B5500055 : Blo 1140634 5500055 := bstep (se 1 (by rfl) ⟨4125041, by rfl⟩ : syracuseStep 5500055 = 8250083) B8250083
theorem B1141931 : Blo 1140634 1141931 := bstep (se 1 (by rfl) ⟨856448, by rfl⟩ : syracuseStep 1141931 = 1712897) B1712897
theorem B1141943 : Blo 1140634 1141943 := bstep (se 1 (by rfl) ⟨856457, by rfl⟩ : syracuseStep 1141943 = 1712915) B1712915
theorem B1141963 : Blo 1140634 1141963 := bstep (se 1 (by rfl) ⟨856472, by rfl⟩ : syracuseStep 1141963 = 1712945) B1712945
theorem B1141975 : Blo 1140634 1141975 := bstep (se 1 (by rfl) ⟨856481, by rfl⟩ : syracuseStep 1141975 = 1712963) B1712963
theorem B1928407 : Blo 1140634 1928407 := bstep (se 1 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 1928407 = 2892611) B2892611
theorem B1141995 : Blo 1140634 1141995 := bstep (se 1 (by rfl) ⟨856496, by rfl⟩ : syracuseStep 1141995 = 1712993) B1712993
theorem B1142007 : Blo 1140634 1142007 := bstep (se 1 (by rfl) ⟨856505, by rfl⟩ : syracuseStep 1142007 = 1713011) B1713011
theorem B1142027 : Blo 1140634 1142027 := bstep (se 1 (by rfl) ⟨856520, by rfl⟩ : syracuseStep 1142027 = 1713041) B1713041
theorem B1142039 : Blo 1140634 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B1142059 : Blo 1140634 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B1142071 : Blo 1140634 1142071 := bstep (se 1 (by rfl) ⟨856553, by rfl⟩ : syracuseStep 1142071 = 1713107) B1713107
theorem B1142091 : Blo 1140634 1142091 := bstep (se 1 (by rfl) ⟨856568, by rfl⟩ : syracuseStep 1142091 = 1713137) B1713137
theorem B1142103 : Blo 1140634 1142103 := bstep (se 1 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 1142103 = 1713155) B1713155
theorem B1142123 : Blo 1140634 1142123 := bstep (se 1 (by rfl) ⟨856592, by rfl⟩ : syracuseStep 1142123 = 1713185) B1713185
theorem B1142135 : Blo 1140634 1142135 := bstep (se 1 (by rfl) ⟨856601, by rfl⟩ : syracuseStep 1142135 = 1713203) B1713203
theorem B1142155 : Blo 1140634 1142155 := bstep (se 1 (by rfl) ⟨856616, by rfl⟩ : syracuseStep 1142155 = 1713233) B1713233
theorem B1142167 : Blo 1140634 1142167 := bstep (se 1 (by rfl) ⟨856625, by rfl⟩ : syracuseStep 1142167 = 1713251) B1713251
theorem B1142187 : Blo 1140634 1142187 := bstep (se 1 (by rfl) ⟨856640, by rfl⟩ : syracuseStep 1142187 = 1713281) B1713281
theorem B1142199 : Blo 1140634 1142199 := bstep (se 1 (by rfl) ⟨856649, by rfl⟩ : syracuseStep 1142199 = 1713299) B1713299
theorem B1142219 : Blo 1140634 1142219 := bstep (se 1 (by rfl) ⟨856664, by rfl⟩ : syracuseStep 1142219 = 1713329) B1713329
theorem B1142231 : Blo 1140634 1142231 := bstep (se 1 (by rfl) ⟨856673, by rfl⟩ : syracuseStep 1142231 = 1713347) B1713347
theorem B1142251 : Blo 1140634 1142251 := bstep (se 1 (by rfl) ⟨856688, by rfl⟩ : syracuseStep 1142251 = 1713377) B1713377
theorem B1142263 : Blo 1140634 1142263 := bstep (se 1 (by rfl) ⟨856697, by rfl⟩ : syracuseStep 1142263 = 1713395) B1713395
theorem B1142283 : Blo 1140634 1142283 := bstep (se 1 (by rfl) ⟨856712, by rfl⟩ : syracuseStep 1142283 = 1713425) B1713425
theorem B1142295 : Blo 1140634 1142295 := bstep (se 1 (by rfl) ⟨856721, by rfl⟩ : syracuseStep 1142295 = 1713443) B1713443
theorem B1142315 : Blo 1140634 1142315 := bstep (se 1 (by rfl) ⟨856736, by rfl⟩ : syracuseStep 1142315 = 1713473) B1713473
theorem B1142327 : Blo 1140634 1142327 := bstep (se 1 (by rfl) ⟨856745, by rfl⟩ : syracuseStep 1142327 = 1713491) B1713491
theorem B2780747 : Blo 1140634 2780747 := bstep (se 1 (by rfl) ⟨2085560, by rfl⟩ : syracuseStep 2780747 = 4171121) B4171121
theorem B1142347 : Blo 1140634 1142347 := bstep (se 1 (by rfl) ⟨856760, by rfl⟩ : syracuseStep 1142347 = 1713521) B1713521
theorem B8678987 : Blo 1140634 8678987 := bstep (se 1 (by rfl) ⟨6509240, by rfl⟩ : syracuseStep 8678987 = 13018481) B13018481
theorem B1142359 : Blo 1140634 1142359 := bstep (se 1 (by rfl) ⟨856769, by rfl⟩ : syracuseStep 1142359 = 1713539) B1713539
theorem B1142379 : Blo 1140634 1142379 := bstep (se 1 (by rfl) ⟨856784, by rfl⟩ : syracuseStep 1142379 = 1713569) B1713569
theorem B1142391 : Blo 1140634 1142391 := bstep (se 1 (by rfl) ⟨856793, by rfl⟩ : syracuseStep 1142391 = 1713587) B1713587
theorem B1142411 : Blo 1140634 1142411 := bstep (se 1 (by rfl) ⟨856808, by rfl⟩ : syracuseStep 1142411 = 1713617) B1713617
theorem B1142423 : Blo 1140634 1142423 := bstep (se 1 (by rfl) ⟨856817, by rfl⟩ : syracuseStep 1142423 = 1713635) B1713635
theorem B1142443 : Blo 1140634 1142443 := bstep (se 1 (by rfl) ⟨856832, by rfl⟩ : syracuseStep 1142443 = 1713665) B1713665
theorem B1142455 : Blo 1140634 1142455 := bstep (se 1 (by rfl) ⟨856841, by rfl⟩ : syracuseStep 1142455 = 1713683) B1713683
theorem B1142475 : Blo 1140634 1142475 := bstep (se 1 (by rfl) ⟨856856, by rfl⟩ : syracuseStep 1142475 = 1713713) B1713713
theorem B1142487 : Blo 1140634 1142487 := bstep (se 1 (by rfl) ⟨856865, by rfl⟩ : syracuseStep 1142487 = 1713731) B1713731
theorem B1142507 : Blo 1140634 1142507 := bstep (se 1 (by rfl) ⟨856880, by rfl⟩ : syracuseStep 1142507 = 1713761) B1713761
theorem B1142519 : Blo 1140634 1142519 := bstep (se 1 (by rfl) ⟨856889, by rfl⟩ : syracuseStep 1142519 = 1713779) B1713779
theorem B1142539 : Blo 1140634 1142539 := bstep (se 1 (by rfl) ⟨856904, by rfl⟩ : syracuseStep 1142539 = 1713809) B1713809
theorem B1142551 : Blo 1140634 1142551 := bstep (se 1 (by rfl) ⟨856913, by rfl⟩ : syracuseStep 1142551 = 1713827) B1713827
theorem B3862295 : Blo 1140634 3862295 := bstep (se 1 (by rfl) ⟨2896721, by rfl⟩ : syracuseStep 3862295 = 5793443) B5793443
theorem B1142571 : Blo 1140634 1142571 := bstep (se 1 (by rfl) ⟨856928, by rfl⟩ : syracuseStep 1142571 = 1713857) B1713857
theorem B1142583 : Blo 1140634 1142583 := bstep (se 1 (by rfl) ⟨856937, by rfl⟩ : syracuseStep 1142583 = 1713875) B1713875
theorem B1142603 : Blo 1140634 1142603 := bstep (se 1 (by rfl) ⟨856952, by rfl⟩ : syracuseStep 1142603 = 1713905) B1713905
theorem B1929035 : Blo 1140634 1929035 := bstep (se 1 (by rfl) ⟨1446776, by rfl⟩ : syracuseStep 1929035 = 2893553) B2893553
theorem B1142615 : Blo 1140634 1142615 := bstep (se 1 (by rfl) ⟨856961, by rfl⟩ : syracuseStep 1142615 = 1713923) B1713923
theorem B1142635 : Blo 1140634 1142635 := bstep (se 1 (by rfl) ⟨856976, by rfl⟩ : syracuseStep 1142635 = 1713953) B1713953
theorem B1142647 : Blo 1140634 1142647 := bstep (se 1 (by rfl) ⟨856985, by rfl⟩ : syracuseStep 1142647 = 1713971) B1713971
theorem B1142667 : Blo 1140634 1142667 := bstep (se 1 (by rfl) ⟨857000, by rfl⟩ : syracuseStep 1142667 = 1714001) B1714001
theorem B1142679 : Blo 1140634 1142679 := bstep (se 1 (by rfl) ⟨857009, by rfl⟩ : syracuseStep 1142679 = 1714019) B1714019
theorem B1142699 : Blo 1140634 1142699 := bstep (se 1 (by rfl) ⟨857024, by rfl⟩ : syracuseStep 1142699 = 1714049) B1714049
theorem B1142711 : Blo 1140634 1142711 := bstep (se 1 (by rfl) ⟨857033, by rfl⟩ : syracuseStep 1142711 = 1714067) B1714067
theorem B3665857 : Blo 1140634 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1142731 : Blo 1140634 1142731 := bstep (se 1 (by rfl) ⟨857048, by rfl⟩ : syracuseStep 1142731 = 1714097) B1714097
theorem B1929163 : Blo 1140634 1929163 := bstep (se 1 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 1929163 = 2893745) B2893745
theorem B1142743 : Blo 1140634 1142743 := bstep (se 1 (by rfl) ⟨857057, by rfl⟩ : syracuseStep 1142743 = 1714115) B1714115
theorem B1142763 : Blo 1140634 1142763 := bstep (se 1 (by rfl) ⟨857072, by rfl⟩ : syracuseStep 1142763 = 1714145) B1714145
theorem B1142775 : Blo 1140634 1142775 := bstep (se 1 (by rfl) ⟨857081, by rfl⟩ : syracuseStep 1142775 = 1714163) B1714163
theorem B1142795 : Blo 1140634 1142795 := bstep (se 1 (by rfl) ⟨857096, by rfl⟩ : syracuseStep 1142795 = 1714193) B1714193
theorem B1142807 : Blo 1140634 1142807 := bstep (se 1 (by rfl) ⟨857105, by rfl⟩ : syracuseStep 1142807 = 1714211) B1714211
theorem B1142827 : Blo 1140634 1142827 := bstep (se 1 (by rfl) ⟨857120, by rfl⟩ : syracuseStep 1142827 = 1714241) B1714241
theorem B1142839 : Blo 1140634 1142839 := bstep (se 1 (by rfl) ⟨857129, by rfl⟩ : syracuseStep 1142839 = 1714259) B1714259
theorem B1142859 : Blo 1140634 1142859 := bstep (se 1 (by rfl) ⟨857144, by rfl⟩ : syracuseStep 1142859 = 1714289) B1714289
theorem B1142871 : Blo 1140634 1142871 := bstep (se 1 (by rfl) ⟨857153, by rfl⟩ : syracuseStep 1142871 = 1714307) B1714307
theorem B1929305 : Blo 1140634 1929305 := bstep (se 2 (by rfl) ⟨723489, by rfl⟩ : syracuseStep 1929305 = 1446979) B1446979
theorem B1142891 : Blo 1140634 1142891 := bstep (se 1 (by rfl) ⟨857168, by rfl⟩ : syracuseStep 1142891 = 1714337) B1714337
theorem B1142903 : Blo 1140634 1142903 := bstep (se 1 (by rfl) ⟨857177, by rfl⟩ : syracuseStep 1142903 = 1714355) B1714355
theorem B1142923 : Blo 1140634 1142923 := bstep (se 1 (by rfl) ⟨857192, by rfl⟩ : syracuseStep 1142923 = 1714385) B1714385
theorem B1142935 : Blo 1140634 1142935 := bstep (se 1 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 1142935 = 1714403) B1714403
theorem B1142955 : Blo 1140634 1142955 := bstep (se 1 (by rfl) ⟨857216, by rfl⟩ : syracuseStep 1142955 = 1714433) B1714433
theorem B1142967 : Blo 1140634 1142967 := bstep (se 1 (by rfl) ⟨857225, by rfl⟩ : syracuseStep 1142967 = 1714451) B1714451
theorem B1142987 : Blo 1140634 1142987 := bstep (se 1 (by rfl) ⟨857240, by rfl⟩ : syracuseStep 1142987 = 1714481) B1714481
theorem B1142999 : Blo 1140634 1142999 := bstep (se 1 (by rfl) ⟨857249, by rfl⟩ : syracuseStep 1142999 = 1714499) B1714499
theorem B1929433 : Blo 1140634 1929433 := bstep (se 2 (by rfl) ⟨723537, by rfl⟩ : syracuseStep 1929433 = 1447075) B1447075
theorem B1143019 : Blo 1140634 1143019 := bstep (se 1 (by rfl) ⟨857264, by rfl⟩ : syracuseStep 1143019 = 1714529) B1714529
theorem B1143031 : Blo 1140634 1143031 := bstep (se 1 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 1143031 = 1714547) B1714547
theorem B1143051 : Blo 1140634 1143051 := bstep (se 1 (by rfl) ⟨857288, by rfl⟩ : syracuseStep 1143051 = 1714577) B1714577
theorem B1143063 : Blo 1140634 1143063 := bstep (se 1 (by rfl) ⟨857297, by rfl⟩ : syracuseStep 1143063 = 1714595) B1714595
theorem B1143083 : Blo 1140634 1143083 := bstep (se 1 (by rfl) ⟨857312, by rfl⟩ : syracuseStep 1143083 = 1714625) B1714625
theorem B22245677 : Blo 1140634 22245677 := bstep (se 3 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 22245677 = 8342129) B8342129
theorem B3862835 : Blo 1140634 3862835 := bstep (se 1 (by rfl) ⟨2897126, by rfl⟩ : syracuseStep 3862835 = 5794253) B5794253
theorem B1143095 : Blo 1140634 1143095 := bstep (se 1 (by rfl) ⟨857321, by rfl⟩ : syracuseStep 1143095 = 1714643) B1714643
theorem B1143115 : Blo 1140634 1143115 := bstep (se 1 (by rfl) ⟨857336, by rfl⟩ : syracuseStep 1143115 = 1714673) B1714673
theorem B1143127 : Blo 1140634 1143127 := bstep (se 1 (by rfl) ⟨857345, by rfl⟩ : syracuseStep 1143127 = 1714691) B1714691
theorem B2060633 : Blo 1140634 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1143147 : Blo 1140634 1143147 := bstep (se 1 (by rfl) ⟨857360, by rfl⟩ : syracuseStep 1143147 = 1714721) B1714721
theorem B1143159 : Blo 1140634 1143159 := bstep (se 1 (by rfl) ⟨857369, by rfl⟩ : syracuseStep 1143159 = 1714739) B1714739
theorem B1143179 : Blo 1140634 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B1143191 : Blo 1140634 1143191 := bstep (se 1 (by rfl) ⟨857393, by rfl⟩ : syracuseStep 1143191 = 1714787) B1714787
theorem B1143211 : Blo 1140634 1143211 := bstep (se 1 (by rfl) ⟨857408, by rfl⟩ : syracuseStep 1143211 = 1714817) B1714817
theorem B1143223 : Blo 1140634 1143223 := bstep (se 1 (by rfl) ⟨857417, by rfl⟩ : syracuseStep 1143223 = 1714835) B1714835
theorem B1143243 : Blo 1140634 1143243 := bstep (se 1 (by rfl) ⟨857432, by rfl⟩ : syracuseStep 1143243 = 1714865) B1714865
theorem B1143255 : Blo 1140634 1143255 := bstep (se 1 (by rfl) ⟨857441, by rfl⟩ : syracuseStep 1143255 = 1714883) B1714883
theorem B1831385 : Blo 1140634 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B1143275 : Blo 1140634 1143275 := bstep (se 1 (by rfl) ⟨857456, by rfl⟩ : syracuseStep 1143275 = 1714913) B1714913
theorem B1143287 : Blo 1140634 1143287 := bstep (se 1 (by rfl) ⟨857465, by rfl⟩ : syracuseStep 1143287 = 1714931) B1714931
theorem B1143307 : Blo 1140634 1143307 := bstep (se 1 (by rfl) ⟨857480, by rfl⟩ : syracuseStep 1143307 = 1714961) B1714961
theorem B1143319 : Blo 1140634 1143319 := bstep (se 1 (by rfl) ⟨857489, by rfl⟩ : syracuseStep 1143319 = 1714979) B1714979
theorem B1143339 : Blo 1140634 1143339 := bstep (se 1 (by rfl) ⟨857504, by rfl⟩ : syracuseStep 1143339 = 1715009) B1715009
theorem B1143351 : Blo 1140634 1143351 := bstep (se 1 (by rfl) ⟨857513, by rfl⟩ : syracuseStep 1143351 = 1715027) B1715027
theorem B3863105 : Blo 1140634 3863105 := bstep (se 2 (by rfl) ⟨1448664, by rfl⟩ : syracuseStep 3863105 = 2897329) B2897329
theorem B1143371 : Blo 1140634 1143371 := bstep (se 1 (by rfl) ⟨857528, by rfl⟩ : syracuseStep 1143371 = 1715057) B1715057
theorem B1143383 : Blo 1140634 1143383 := bstep (se 1 (by rfl) ⟨857537, by rfl⟩ : syracuseStep 1143383 = 1715075) B1715075
theorem B6255197 : Blo 1140634 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B1143403 : Blo 1140634 1143403 := bstep (se 1 (by rfl) ⟨857552, by rfl⟩ : syracuseStep 1143403 = 1715105) B1715105
theorem B1143415 : Blo 1140634 1143415 := bstep (se 1 (by rfl) ⟨857561, by rfl⟩ : syracuseStep 1143415 = 1715123) B1715123
theorem B1143435 : Blo 1140634 1143435 := bstep (se 1 (by rfl) ⟨857576, by rfl⟩ : syracuseStep 1143435 = 1715153) B1715153
theorem B1143447 : Blo 1140634 1143447 := bstep (se 1 (by rfl) ⟨857585, by rfl⟩ : syracuseStep 1143447 = 1715171) B1715171
theorem B1143467 : Blo 1140634 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B1143479 : Blo 1140634 1143479 := bstep (se 1 (by rfl) ⟨857609, by rfl⟩ : syracuseStep 1143479 = 1715219) B1715219
theorem B1143499 : Blo 1140634 1143499 := bstep (se 1 (by rfl) ⟨857624, by rfl⟩ : syracuseStep 1143499 = 1715249) B1715249
theorem B1143511 : Blo 1140634 1143511 := bstep (se 1 (by rfl) ⟨857633, by rfl⟩ : syracuseStep 1143511 = 1715267) B1715267
theorem B1143531 : Blo 1140634 1143531 := bstep (se 1 (by rfl) ⟨857648, by rfl⟩ : syracuseStep 1143531 = 1715297) B1715297
theorem B1143543 : Blo 1140634 1143543 := bstep (se 1 (by rfl) ⟨857657, by rfl⟩ : syracuseStep 1143543 = 1715315) B1715315
theorem B1143563 : Blo 1140634 1143563 := bstep (se 1 (by rfl) ⟨857672, by rfl⟩ : syracuseStep 1143563 = 1715345) B1715345
theorem B7729937 : Blo 1140634 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B1143575 : Blo 1140634 1143575 := bstep (se 1 (by rfl) ⟨857681, by rfl⟩ : syracuseStep 1143575 = 1715363) B1715363
theorem B1930007 : Blo 1140634 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B1143595 : Blo 1140634 1143595 := bstep (se 1 (by rfl) ⟨857696, by rfl⟩ : syracuseStep 1143595 = 1715393) B1715393
theorem B1143607 : Blo 1140634 1143607 := bstep (se 1 (by rfl) ⟨857705, by rfl⟩ : syracuseStep 1143607 = 1715411) B1715411
theorem B1143627 : Blo 1140634 1143627 := bstep (se 1 (by rfl) ⟨857720, by rfl⟩ : syracuseStep 1143627 = 1715441) B1715441
theorem B1143639 : Blo 1140634 1143639 := bstep (se 1 (by rfl) ⟨857729, by rfl⟩ : syracuseStep 1143639 = 1715459) B1715459
theorem B1143659 : Blo 1140634 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B1143671 : Blo 1140634 1143671 := bstep (se 1 (by rfl) ⟨857753, by rfl⟩ : syracuseStep 1143671 = 1715507) B1715507
theorem B1143691 : Blo 1140634 1143691 := bstep (se 1 (by rfl) ⟨857768, by rfl⟩ : syracuseStep 1143691 = 1715537) B1715537
theorem B1143703 : Blo 1140634 1143703 := bstep (se 1 (by rfl) ⟨857777, by rfl⟩ : syracuseStep 1143703 = 1715555) B1715555
theorem B1930135 : Blo 1140634 1930135 := bstep (se 1 (by rfl) ⟨1447601, by rfl⟩ : syracuseStep 1930135 = 2895203) B2895203
theorem B1143723 : Blo 1140634 1143723 := bstep (se 1 (by rfl) ⟨857792, by rfl⟩ : syracuseStep 1143723 = 1715585) B1715585
theorem B1143735 : Blo 1140634 1143735 := bstep (se 1 (by rfl) ⟨857801, by rfl⟩ : syracuseStep 1143735 = 1715603) B1715603
theorem B1143755 : Blo 1140634 1143755 := bstep (se 1 (by rfl) ⟨857816, by rfl⟩ : syracuseStep 1143755 = 1715633) B1715633
theorem B1143767 : Blo 1140634 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1143787 : Blo 1140634 1143787 := bstep (se 1 (by rfl) ⟨857840, by rfl⟩ : syracuseStep 1143787 = 1715681) B1715681
theorem B1143799 : Blo 1140634 1143799 := bstep (se 1 (by rfl) ⟨857849, by rfl⟩ : syracuseStep 1143799 = 1715699) B1715699
theorem B1143819 : Blo 1140634 1143819 := bstep (se 1 (by rfl) ⟨857864, by rfl⟩ : syracuseStep 1143819 = 1715729) B1715729
theorem B1143831 : Blo 1140634 1143831 := bstep (se 1 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 1143831 = 1715747) B1715747
theorem B1143851 : Blo 1140634 1143851 := bstep (se 1 (by rfl) ⟨857888, by rfl⟩ : syracuseStep 1143851 = 1715777) B1715777
theorem B1143863 : Blo 1140634 1143863 := bstep (se 1 (by rfl) ⟨857897, by rfl⟩ : syracuseStep 1143863 = 1715795) B1715795
theorem B1143883 : Blo 1140634 1143883 := bstep (se 1 (by rfl) ⟨857912, by rfl⟩ : syracuseStep 1143883 = 1715825) B1715825
theorem B1143895 : Blo 1140634 1143895 := bstep (se 1 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 1143895 = 1715843) B1715843
theorem B6517853 : Blo 1140634 6517853 := bstep (se 3 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 6517853 = 2444195) B2444195
theorem B1143915 : Blo 1140634 1143915 := bstep (se 1 (by rfl) ⟨857936, by rfl⟩ : syracuseStep 1143915 = 1715873) B1715873
theorem B1143927 : Blo 1140634 1143927 := bstep (se 1 (by rfl) ⟨857945, by rfl⟩ : syracuseStep 1143927 = 1715891) B1715891
theorem B1143947 : Blo 1140634 1143947 := bstep (se 1 (by rfl) ⟨857960, by rfl⟩ : syracuseStep 1143947 = 1715921) B1715921
theorem B1143959 : Blo 1140634 1143959 := bstep (se 1 (by rfl) ⟨857969, by rfl⟩ : syracuseStep 1143959 = 1715939) B1715939
theorem B1143979 : Blo 1140634 1143979 := bstep (se 1 (by rfl) ⟨857984, by rfl⟩ : syracuseStep 1143979 = 1715969) B1715969
theorem B1143991 : Blo 1140634 1143991 := bstep (se 1 (by rfl) ⟨857993, by rfl⟩ : syracuseStep 1143991 = 1715987) B1715987
theorem B1144011 : Blo 1140634 1144011 := bstep (se 1 (by rfl) ⟨858008, by rfl⟩ : syracuseStep 1144011 = 1716017) B1716017
theorem B1144023 : Blo 1140634 1144023 := bstep (se 1 (by rfl) ⟨858017, by rfl⟩ : syracuseStep 1144023 = 1716035) B1716035
theorem B1144043 : Blo 1140634 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B1144055 : Blo 1140634 1144055 := bstep (se 1 (by rfl) ⟨858041, by rfl⟩ : syracuseStep 1144055 = 1716083) B1716083
theorem B1144075 : Blo 1140634 1144075 := bstep (se 1 (by rfl) ⟨858056, by rfl⟩ : syracuseStep 1144075 = 1716113) B1716113
theorem B1144087 : Blo 1140634 1144087 := bstep (se 1 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 1144087 = 1716131) B1716131
theorem B1144107 : Blo 1140634 1144107 := bstep (se 1 (by rfl) ⟨858080, by rfl⟩ : syracuseStep 1144107 = 1716161) B1716161
theorem B1144119 : Blo 1140634 1144119 := bstep (se 1 (by rfl) ⟨858089, by rfl⟩ : syracuseStep 1144119 = 1716179) B1716179
theorem B1144139 : Blo 1140634 1144139 := bstep (se 1 (by rfl) ⟨858104, by rfl⟩ : syracuseStep 1144139 = 1716209) B1716209
theorem B1144151 : Blo 1140634 1144151 := bstep (se 1 (by rfl) ⟨858113, by rfl⟩ : syracuseStep 1144151 = 1716227) B1716227
theorem B1144171 : Blo 1140634 1144171 := bstep (se 1 (by rfl) ⟨858128, by rfl⟩ : syracuseStep 1144171 = 1716257) B1716257
theorem B1144183 : Blo 1140634 1144183 := bstep (se 1 (by rfl) ⟨858137, by rfl⟩ : syracuseStep 1144183 = 1716275) B1716275
theorem B1144203 : Blo 1140634 1144203 := bstep (se 1 (by rfl) ⟨858152, by rfl⟩ : syracuseStep 1144203 = 1716305) B1716305
theorem B1144215 : Blo 1140634 1144215 := bstep (se 1 (by rfl) ⟨858161, by rfl⟩ : syracuseStep 1144215 = 1716323) B1716323
theorem B1144235 : Blo 1140634 1144235 := bstep (se 1 (by rfl) ⟨858176, by rfl⟩ : syracuseStep 1144235 = 1716353) B1716353
theorem B1144247 : Blo 1140634 1144247 := bstep (se 1 (by rfl) ⟨858185, by rfl⟩ : syracuseStep 1144247 = 1716371) B1716371
theorem B1144267 : Blo 1140634 1144267 := bstep (se 1 (by rfl) ⟨858200, by rfl⟩ : syracuseStep 1144267 = 1716401) B1716401
theorem B1144279 : Blo 1140634 1144279 := bstep (se 1 (by rfl) ⟨858209, by rfl⟩ : syracuseStep 1144279 = 1716419) B1716419
theorem B1144299 : Blo 1140634 1144299 := bstep (se 1 (by rfl) ⟨858224, by rfl⟩ : syracuseStep 1144299 = 1716449) B1716449
theorem B1144311 : Blo 1140634 1144311 := bstep (se 1 (by rfl) ⟨858233, by rfl⟩ : syracuseStep 1144311 = 1716467) B1716467
theorem B1373707 : Blo 1140634 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B1930763 : Blo 1140634 1930763 := bstep (se 1 (by rfl) ⟨1448072, by rfl⟩ : syracuseStep 1930763 = 2896145) B2896145
theorem B1144331 : Blo 1140634 1144331 := bstep (se 1 (by rfl) ⟨858248, by rfl⟩ : syracuseStep 1144331 = 1716497) B1716497
theorem B1144343 : Blo 1140634 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B1144363 : Blo 1140634 1144363 := bstep (se 1 (by rfl) ⟨858272, by rfl⟩ : syracuseStep 1144363 = 1716545) B1716545
theorem B1144375 : Blo 1140634 1144375 := bstep (se 1 (by rfl) ⟨858281, by rfl⟩ : syracuseStep 1144375 = 1716563) B1716563
theorem B1144395 : Blo 1140634 1144395 := bstep (se 1 (by rfl) ⟨858296, by rfl⟩ : syracuseStep 1144395 = 1716593) B1716593
theorem B1144407 : Blo 1140634 1144407 := bstep (se 1 (by rfl) ⟨858305, by rfl⟩ : syracuseStep 1144407 = 1716611) B1716611
theorem B1144427 : Blo 1140634 1144427 := bstep (se 1 (by rfl) ⟨858320, by rfl⟩ : syracuseStep 1144427 = 1716641) B1716641
theorem B1144439 : Blo 1140634 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B1930891 : Blo 1140634 1930891 := bstep (se 1 (by rfl) ⟨1448168, by rfl⟩ : syracuseStep 1930891 = 2896337) B2896337
theorem B1144459 : Blo 1140634 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B4880017 : Blo 1140634 4880017 := bstep (se 2 (by rfl) ⟨1830006, by rfl⟩ : syracuseStep 4880017 = 3660013) B3660013
theorem B1144471 : Blo 1140634 1144471 := bstep (se 1 (by rfl) ⟨858353, by rfl⟩ : syracuseStep 1144471 = 1716707) B1716707
theorem B1144491 : Blo 1140634 1144491 := bstep (se 1 (by rfl) ⟨858368, by rfl⟩ : syracuseStep 1144491 = 1716737) B1716737
theorem B16676533 : Blo 1140634 16676533 := bstep (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) B1563425
theorem B1144503 : Blo 1140634 1144503 := bstep (se 1 (by rfl) ⟨858377, by rfl⟩ : syracuseStep 1144503 = 1716755) B1716755
theorem B1144523 : Blo 1140634 1144523 := bstep (se 1 (by rfl) ⟨858392, by rfl⟩ : syracuseStep 1144523 = 1716785) B1716785
theorem B1144535 : Blo 1140634 1144535 := bstep (se 1 (by rfl) ⟨858401, by rfl⟩ : syracuseStep 1144535 = 1716803) B1716803
theorem B1144555 : Blo 1140634 1144555 := bstep (se 1 (by rfl) ⟨858416, by rfl⟩ : syracuseStep 1144555 = 1716833) B1716833
theorem B1144567 : Blo 1140634 1144567 := bstep (se 1 (by rfl) ⟨858425, by rfl⟩ : syracuseStep 1144567 = 1716851) B1716851
theorem B1144587 : Blo 1140634 1144587 := bstep (se 1 (by rfl) ⟨858440, by rfl⟩ : syracuseStep 1144587 = 1716881) B1716881
theorem B1144599 : Blo 1140634 1144599 := bstep (se 1 (by rfl) ⟨858449, by rfl⟩ : syracuseStep 1144599 = 1716899) B1716899
theorem B1931033 : Blo 1140634 1931033 := bstep (se 2 (by rfl) ⟨724137, by rfl⟩ : syracuseStep 1931033 = 1448275) B1448275
theorem B1144619 : Blo 1140634 1144619 := bstep (se 1 (by rfl) ⟨858464, by rfl⟩ : syracuseStep 1144619 = 1716929) B1716929
theorem B1144631 : Blo 1140634 1144631 := bstep (se 1 (by rfl) ⟨858473, by rfl⟩ : syracuseStep 1144631 = 1716947) B1716947
theorem B1931161 : Blo 1140634 1931161 := bstep (se 2 (by rfl) ⟨724185, by rfl⟩ : syracuseStep 1931161 = 1448371) B1448371
theorem B15628439 : Blo 1140634 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B9173197 : Blo 1140634 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B8223383 : Blo 1140634 8223383 := bstep (se 1 (by rfl) ⟨6167537, by rfl⟩ : syracuseStep 8223383 = 12335075) B12335075
theorem B9272069 : Blo 1140634 9272069 := bstep (se 4 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 9272069 = 1738513) B1738513
theorem B18513197 : Blo 1140634 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B1146295 : Blo 1140634 1146295 := bstep (se 1 (by rfl) ⟨859721, by rfl⟩ : syracuseStep 1146295 = 1719443) B1719443
theorem B26345645 : Blo 1140634 26345645 := bstep (se 3 (by rfl) ⟨4939808, by rfl⟩ : syracuseStep 26345645 = 9879617) B9879617
theorem B6947045 : Blo 1140634 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B8225171 : Blo 1140634 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B23462291 : Blo 1140634 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B52724195 : Blo 1140634 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B8913665 : Blo 1140634 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B1737607 : Blo 1140634 1737607 := bstep (se 1 (by rfl) ⟨1303205, by rfl⟩ : syracuseStep 1737607 = 2606411) B2606411
theorem B8258507 : Blo 1140634 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B8225803 : Blo 1140634 8225803 := bstep (se 1 (by rfl) ⟨6169352, by rfl⟩ : syracuseStep 8225803 = 12338705) B12338705
theorem B1738027 : Blo 1140634 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B20874631 : Blo 1140634 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B18548153 : Blo 1140634 18548153 := bstep (se 2 (by rfl) ⟨6955557, by rfl⟩ : syracuseStep 18548153 = 13911115) B13911115
theorem B4884239 : Blo 1140634 4884239 := bstep (se 1 (by rfl) ⟨3663179, by rfl⟩ : syracuseStep 4884239 = 7326359) B7326359
theorem B1739279 : Blo 1140634 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B27855427 : Blo 1140634 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B2165449 : Blo 1140634 2165449 := bstep (se 2 (by rfl) ⟨812043, by rfl⟩ : syracuseStep 2165449 = 1624087) B1624087
theorem B13208293 : Blo 1140634 13208293 := bstep (se 4 (by rfl) ⟨1238277, by rfl⟩ : syracuseStep 13208293 = 2476555) B2476555
theorem B7048139 : Blo 1140634 7048139 := bstep (se 1 (by rfl) ⟨5286104, by rfl⟩ : syracuseStep 7048139 = 10572209) B10572209
theorem B1445035 : Blo 1140634 1445035 := bstep (se 1 (by rfl) ⟨1083776, by rfl⟩ : syracuseStep 1445035 = 2167553) B2167553
theorem B7310573 : Blo 1140634 7310573 := bstep (se 3 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 7310573 = 2741465) B2741465
theorem B4885895 : Blo 1140634 4885895 := bstep (se 1 (by rfl) ⟨3664421, by rfl⟩ : syracuseStep 4885895 = 7328843) B7328843
theorem B13209131 : Blo 1140634 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B1740331 : Blo 1140634 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B1412743 : Blo 1140634 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B111054563 : Blo 1140634 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B2887559 : Blo 1140634 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B2887609 : Blo 1140634 2887609 := bstep (se 2 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 2887609 = 2165707) B2165707
theorem B1544123 : Blo 1140634 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B3084331 : Blo 1140634 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B3477563 : Blo 1140634 3477563 := bstep (se 1 (by rfl) ⟨2608172, by rfl⟩ : syracuseStep 3477563 = 5216345) B5216345
theorem B5279863 : Blo 1140634 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B1446007 : Blo 1140634 1446007 := bstep (se 1 (by rfl) ⟨1084505, by rfl⟩ : syracuseStep 1446007 = 2169011) B2169011
theorem B23761097 : Blo 1140634 23761097 := bstep (se 2 (by rfl) ⟨8910411, by rfl⟩ : syracuseStep 23761097 = 17820823) B17820823
theorem B23433461 : Blo 1140634 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1446331 : Blo 1140634 1446331 := bstep (se 1 (by rfl) ⟨1084748, by rfl⟩ : syracuseStep 1446331 = 2169497) B2169497
theorem B2888207 : Blo 1140634 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B1544761 : Blo 1140634 1544761 := bstep (se 2 (by rfl) ⟨579285, by rfl⟩ : syracuseStep 1544761 = 1158571) B1158571
theorem B1545161 : Blo 1140634 1545161 := bstep (se 2 (by rfl) ⟨579435, by rfl⟩ : syracuseStep 1545161 = 1158871) B1158871
theorem B4625495 : Blo 1140634 4625495 := bstep (se 1 (by rfl) ⟨3469121, by rfl⟩ : syracuseStep 4625495 = 6938243) B6938243
theorem B1283215 : Blo 1140634 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B2167955 : Blo 1140634 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B2888905 : Blo 1140634 2888905 := bstep (se 2 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 2888905 = 2166679) B2166679
theorem B4887809 : Blo 1140634 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B2889047 : Blo 1140634 2889047 := bstep (se 1 (by rfl) ⟨2166785, by rfl⟩ : syracuseStep 2889047 = 4333571) B4333571
theorem B4330867 : Blo 1140634 4330867 := bstep (se 1 (by rfl) ⟨3248150, by rfl⟩ : syracuseStep 4330867 = 6496301) B6496301
theorem B2168183 : Blo 1140634 2168183 := bstep (se 1 (by rfl) ⟨1626137, by rfl⟩ : syracuseStep 2168183 = 3252275) B3252275
theorem B1447303 : Blo 1140634 1447303 := bstep (se 1 (by rfl) ⟨1085477, by rfl⟩ : syracuseStep 1447303 = 2170955) B2170955
theorem B3085715 : Blo 1140634 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B4888151 : Blo 1140634 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B1283719 : Blo 1140634 1283719 := bstep (se 1 (by rfl) ⟨962789, by rfl⟩ : syracuseStep 1283719 = 1925579) B1925579
theorem B1447723 : Blo 1140634 1447723 := bstep (se 1 (by rfl) ⟨1085792, by rfl⟩ : syracuseStep 1447723 = 2171585) B2171585
theorem B1283899 : Blo 1140634 1283899 := bstep (se 1 (by rfl) ⟨962924, by rfl⟩ : syracuseStep 1283899 = 1925849) B1925849
theorem B1546231 : Blo 1140634 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B1447951 : Blo 1140634 1447951 := bstep (se 1 (by rfl) ⟨1085963, by rfl⟩ : syracuseStep 1447951 = 2171927) B2171927
theorem B6789187 : Blo 1140634 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B3250361 : Blo 1140634 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B1284367 : Blo 1140634 1284367 := bstep (se 1 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 1284367 = 1926551) B1926551
theorem B3250475 : Blo 1140634 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B7313723 : Blo 1140634 7313723 := bstep (se 1 (by rfl) ⟨5485292, by rfl⟩ : syracuseStep 7313723 = 10970585) B10970585
theorem B4168259 : Blo 1140634 4168259 := bstep (se 1 (by rfl) ⟨3126194, by rfl⟩ : syracuseStep 4168259 = 6252389) B6252389
theorem B10984193 : Blo 1140634 10984193 := bstep (se 2 (by rfl) ⟨4119072, by rfl⟩ : syracuseStep 10984193 = 8238145) B8238145
theorem B1284871 : Blo 1140634 1284871 := bstep (se 1 (by rfl) ⟨963653, by rfl⟩ : syracuseStep 1284871 = 1927307) B1927307
theorem B1710983 : Blo 1140634 1710983 := bstep (se 1 (by rfl) ⟨1283237, by rfl⟩ : syracuseStep 1710983 = 2566475) B2566475
theorem B6167431 : Blo 1140634 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B1711019 : Blo 1140634 1711019 := bstep (se 1 (by rfl) ⟨1283264, by rfl⟩ : syracuseStep 1711019 = 2566529) B2566529
theorem B1285051 : Blo 1140634 1285051 := bstep (se 1 (by rfl) ⟨963788, by rfl⟩ : syracuseStep 1285051 = 1927577) B1927577
theorem B1711049 : Blo 1140634 1711049 := bstep (se 2 (by rfl) ⟨641643, by rfl⟩ : syracuseStep 1711049 = 1283287) B1283287
theorem B7805899 : Blo 1140634 7805899 := bstep (se 1 (by rfl) ⟨5854424, by rfl⟩ : syracuseStep 7805899 = 11708849) B11708849
theorem B2169899 : Blo 1140634 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B1711163 : Blo 1140634 1711163 := bstep (se 1 (by rfl) ⟨1283372, by rfl⟩ : syracuseStep 1711163 = 2566745) B2566745
theorem B1711223 : Blo 1140634 1711223 := bstep (se 1 (by rfl) ⟨1283417, by rfl⟩ : syracuseStep 1711223 = 2566835) B2566835
theorem B1711247 : Blo 1140634 1711247 := bstep (se 1 (by rfl) ⟨1283435, by rfl⟩ : syracuseStep 1711247 = 2566871) B2566871
theorem B1711289 : Blo 1140634 1711289 := bstep (se 2 (by rfl) ⟨641733, by rfl⟩ : syracuseStep 1711289 = 1283467) B1283467
theorem B3087617 : Blo 1140634 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B1711367 : Blo 1140634 1711367 := bstep (se 1 (by rfl) ⟨1283525, by rfl⟩ : syracuseStep 1711367 = 2567051) B2567051
theorem B2170127 : Blo 1140634 2170127 := bstep (se 1 (by rfl) ⟨1627595, by rfl⟩ : syracuseStep 2170127 = 3255191) B3255191
theorem B1711403 : Blo 1140634 1711403 := bstep (se 1 (by rfl) ⟨1283552, by rfl⟩ : syracuseStep 1711403 = 2567105) B2567105
theorem B5774651 : Blo 1140634 5774651 := bstep (se 1 (by rfl) ⟨4330988, by rfl⟩ : syracuseStep 5774651 = 8661977) B8661977
theorem B1711433 : Blo 1140634 1711433 := bstep (se 2 (by rfl) ⟨641787, by rfl⟩ : syracuseStep 1711433 = 1283575) B1283575
theorem B2891123 : Blo 1140634 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B1285519 : Blo 1140634 1285519 := bstep (se 1 (by rfl) ⟨964139, by rfl⟩ : syracuseStep 1285519 = 1928279) B1928279
theorem B3251603 : Blo 1140634 3251603 := bstep (se 1 (by rfl) ⟨2438702, by rfl⟩ : syracuseStep 3251603 = 4877405) B4877405
theorem B1711547 : Blo 1140634 1711547 := bstep (se 1 (by rfl) ⟨1283660, by rfl⟩ : syracuseStep 1711547 = 2567321) B2567321
theorem B23469517 : Blo 1140634 23469517 := bstep (se 3 (by rfl) ⟨4400534, by rfl⟩ : syracuseStep 23469517 = 8801069) B8801069
theorem B5774813 : Blo 1140634 5774813 := bstep (se 3 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 5774813 = 2165555) B2165555
theorem B1711607 : Blo 1140634 1711607 := bstep (se 1 (by rfl) ⟨1283705, by rfl⟩ : syracuseStep 1711607 = 2567411) B2567411
theorem B1711631 : Blo 1140634 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B4333085 : Blo 1140634 4333085 := bstep (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) B1624907
theorem B1711673 : Blo 1140634 1711673 := bstep (se 2 (by rfl) ⟨641877, by rfl⟩ : syracuseStep 1711673 = 1283755) B1283755
theorem B1711751 : Blo 1140634 1711751 := bstep (se 1 (by rfl) ⟨1283813, by rfl⟩ : syracuseStep 1711751 = 2567627) B2567627
theorem B1711787 : Blo 1140634 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B1711817 : Blo 1140634 1711817 := bstep (se 2 (by rfl) ⟨641931, by rfl⟩ : syracuseStep 1711817 = 1283863) B1283863
theorem B5775137 : Blo 1140634 5775137 := bstep (se 2 (by rfl) ⟨2165676, by rfl⟩ : syracuseStep 5775137 = 4331353) B4331353
theorem B3252001 : Blo 1140634 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B1711931 : Blo 1140634 1711931 := bstep (se 1 (by rfl) ⟨1283948, by rfl⟩ : syracuseStep 1711931 = 2567897) B2567897
theorem B1711991 : Blo 1140634 1711991 := bstep (se 1 (by rfl) ⟨1283993, by rfl⟩ : syracuseStep 1711991 = 2567987) B2567987
theorem B2891639 : Blo 1140634 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B1286023 : Blo 1140634 1286023 := bstep (se 1 (by rfl) ⟨964517, by rfl⟩ : syracuseStep 1286023 = 1929035) B1929035
theorem B1712015 : Blo 1140634 1712015 := bstep (se 1 (by rfl) ⟨1284011, by rfl⟩ : syracuseStep 1712015 = 2568023) B2568023
theorem B1712057 : Blo 1140634 1712057 := bstep (se 2 (by rfl) ⟨642021, by rfl⟩ : syracuseStep 1712057 = 1284043) B1284043
theorem B1712135 : Blo 1140634 1712135 := bstep (se 1 (by rfl) ⟨1284101, by rfl⟩ : syracuseStep 1712135 = 2568203) B2568203
theorem B27795473 : Blo 1140634 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B1712171 : Blo 1140634 1712171 := bstep (se 1 (by rfl) ⟨1284128, by rfl⟩ : syracuseStep 1712171 = 2568257) B2568257
theorem B1286203 : Blo 1140634 1286203 := bstep (se 1 (by rfl) ⟨964652, by rfl⟩ : syracuseStep 1286203 = 1929305) B1929305
theorem B1712201 : Blo 1140634 1712201 := bstep (se 2 (by rfl) ⟨642075, by rfl⟩ : syracuseStep 1712201 = 1284151) B1284151
theorem B1712315 : Blo 1140634 1712315 := bstep (se 1 (by rfl) ⟨1284236, by rfl⟩ : syracuseStep 1712315 = 2568473) B2568473
theorem B4333769 : Blo 1140634 4333769 := bstep (se 2 (by rfl) ⟨1625163, by rfl⟩ : syracuseStep 4333769 = 3250327) B3250327
theorem B1712375 : Blo 1140634 1712375 := bstep (se 1 (by rfl) ⟨1284281, by rfl⟩ : syracuseStep 1712375 = 2568563) B2568563
theorem B1712399 : Blo 1140634 1712399 := bstep (se 1 (by rfl) ⟨1284299, by rfl⟩ : syracuseStep 1712399 = 2568599) B2568599
theorem B12230929 : Blo 1140634 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1712441 : Blo 1140634 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B1220923 : Blo 1140634 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B1712519 : Blo 1140634 1712519 := bstep (se 1 (by rfl) ⟨1284389, by rfl⟩ : syracuseStep 1712519 = 2568779) B2568779
theorem B4170131 : Blo 1140634 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B1712555 : Blo 1140634 1712555 := bstep (se 1 (by rfl) ⟨1284416, by rfl⟩ : syracuseStep 1712555 = 2568833) B2568833
theorem B1712585 : Blo 1140634 1712585 := bstep (se 2 (by rfl) ⟨642219, by rfl⟩ : syracuseStep 1712585 = 1284439) B1284439
theorem B5153291 : Blo 1140634 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B1286671 : Blo 1140634 1286671 := bstep (se 1 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 1286671 = 1930007) B1930007
theorem B1712699 : Blo 1140634 1712699 := bstep (se 1 (by rfl) ⟨1284524, by rfl⟩ : syracuseStep 1712699 = 2569049) B2569049
theorem B1712759 : Blo 1140634 1712759 := bstep (se 1 (by rfl) ⟨1284569, by rfl⟩ : syracuseStep 1712759 = 2569139) B2569139
theorem B1712783 : Blo 1140634 1712783 := bstep (se 1 (by rfl) ⟨1284587, by rfl⟩ : syracuseStep 1712783 = 2569175) B2569175
theorem B2171539 : Blo 1140634 2171539 := bstep (se 1 (by rfl) ⟨1628654, by rfl⟩ : syracuseStep 2171539 = 3257309) B3257309
theorem B3252889 : Blo 1140634 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B1712825 : Blo 1140634 1712825 := bstep (se 2 (by rfl) ⟨642309, by rfl⟩ : syracuseStep 1712825 = 1284619) B1284619
theorem B5776109 : Blo 1140634 5776109 := bstep (se 3 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 5776109 = 2166041) B2166041
theorem B1712903 : Blo 1140634 1712903 := bstep (se 1 (by rfl) ⟨1284677, by rfl⟩ : syracuseStep 1712903 = 2569355) B2569355
theorem B1712939 : Blo 1140634 1712939 := bstep (se 1 (by rfl) ⟨1284704, by rfl⟩ : syracuseStep 1712939 = 2569409) B2569409
theorem B1712969 : Blo 1140634 1712969 := bstep (se 2 (by rfl) ⟨642363, by rfl⟩ : syracuseStep 1712969 = 1284727) B1284727
theorem B2892631 : Blo 1140634 2892631 := bstep (se 1 (by rfl) ⟨2169473, by rfl⟩ : syracuseStep 2892631 = 4338947) B4338947
theorem B2171767 : Blo 1140634 2171767 := bstep (se 1 (by rfl) ⟨1628825, by rfl⟩ : syracuseStep 2171767 = 3257651) B3257651
theorem B4400057 : Blo 1140634 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B1713083 : Blo 1140634 1713083 := bstep (se 1 (by rfl) ⟨1284812, by rfl⟩ : syracuseStep 1713083 = 2569625) B2569625
theorem B88941509 : Blo 1140634 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B1713143 : Blo 1140634 1713143 := bstep (se 1 (by rfl) ⟨1284857, by rfl⟩ : syracuseStep 1713143 = 2569715) B2569715
theorem B1287175 : Blo 1140634 1287175 := bstep (se 1 (by rfl) ⟨965381, by rfl⟩ : syracuseStep 1287175 = 1930763) B1930763
theorem B1713167 : Blo 1140634 1713167 := bstep (se 1 (by rfl) ⟨1284875, by rfl⟩ : syracuseStep 1713167 = 2569751) B2569751
theorem B3253277 : Blo 1140634 3253277 := bstep (se 3 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 3253277 = 1219979) B1219979
theorem B1713209 : Blo 1140634 1713209 := bstep (se 2 (by rfl) ⟨642453, by rfl⟩ : syracuseStep 1713209 = 1284907) B1284907
theorem B1713287 : Blo 1140634 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B2892935 : Blo 1140634 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B1713323 : Blo 1140634 1713323 := bstep (se 1 (by rfl) ⟨1284992, by rfl⟩ : syracuseStep 1713323 = 2569985) B2569985
theorem B1287355 : Blo 1140634 1287355 := bstep (se 1 (by rfl) ⟨965516, by rfl⟩ : syracuseStep 1287355 = 1931033) B1931033
theorem B1713353 : Blo 1140634 1713353 := bstep (se 2 (by rfl) ⟨642507, by rfl⟩ : syracuseStep 1713353 = 1285015) B1285015
theorem B3089609 : Blo 1140634 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B2893067 : Blo 1140634 2893067 := bstep (se 1 (by rfl) ⟨2169800, by rfl⟩ : syracuseStep 2893067 = 4339601) B4339601
theorem B1713467 : Blo 1140634 1713467 := bstep (se 1 (by rfl) ⟨1285100, by rfl⟩ : syracuseStep 1713467 = 2570201) B2570201
theorem B1713527 : Blo 1140634 1713527 := bstep (se 1 (by rfl) ⟨1285145, by rfl⟩ : syracuseStep 1713527 = 2570291) B2570291
theorem B1713551 : Blo 1140634 1713551 := bstep (se 1 (by rfl) ⟨1285163, by rfl⟩ : syracuseStep 1713551 = 2570327) B2570327
theorem B1713593 : Blo 1140634 1713593 := bstep (se 2 (by rfl) ⟨642597, by rfl⟩ : syracuseStep 1713593 = 1285195) B1285195
theorem B1713671 : Blo 1140634 1713671 := bstep (se 1 (by rfl) ⟨1285253, by rfl⟩ : syracuseStep 1713671 = 2570507) B2570507
theorem B5776919 : Blo 1140634 5776919 := bstep (se 1 (by rfl) ⟨4332689, by rfl⟩ : syracuseStep 5776919 = 8665379) B8665379
theorem B1713707 : Blo 1140634 1713707 := bstep (se 1 (by rfl) ⟨1285280, by rfl⟩ : syracuseStep 1713707 = 2570561) B2570561
theorem B13903427 : Blo 1140634 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B1713737 : Blo 1140634 1713737 := bstep (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) B1285303
theorem B1713851 : Blo 1140634 1713851 := bstep (se 1 (by rfl) ⟨1285388, by rfl⟩ : syracuseStep 1713851 = 2570777) B2570777
theorem B1713911 : Blo 1140634 1713911 := bstep (se 1 (by rfl) ⟨1285433, by rfl⟩ : syracuseStep 1713911 = 2570867) B2570867
theorem B5482255 : Blo 1140634 5482255 := bstep (se 1 (by rfl) ⟨4111691, by rfl⟩ : syracuseStep 5482255 = 8223383) B8223383
theorem B1713935 : Blo 1140634 1713935 := bstep (se 1 (by rfl) ⟨1285451, by rfl⟩ : syracuseStep 1713935 = 2570903) B2570903
theorem B2893583 : Blo 1140634 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B1713977 : Blo 1140634 1713977 := bstep (se 2 (by rfl) ⟨642741, by rfl⟩ : syracuseStep 1713977 = 1285483) B1285483
theorem B7317337 : Blo 1140634 7317337 := bstep (se 2 (by rfl) ⟨2744001, by rfl⟩ : syracuseStep 7317337 = 5488003) B5488003
theorem B1714055 : Blo 1140634 1714055 := bstep (se 1 (by rfl) ⟨1285541, by rfl⟩ : syracuseStep 1714055 = 2571083) B2571083
theorem B2893715 : Blo 1140634 2893715 := bstep (se 1 (by rfl) ⟨2170286, by rfl⟩ : syracuseStep 2893715 = 4340573) B4340573
theorem B1714091 : Blo 1140634 1714091 := bstep (se 1 (by rfl) ⟨1285568, by rfl⟩ : syracuseStep 1714091 = 2571137) B2571137
theorem B4335545 : Blo 1140634 4335545 := bstep (se 2 (by rfl) ⟨1625829, by rfl⟩ : syracuseStep 4335545 = 3251659) B3251659
theorem B5220281 : Blo 1140634 5220281 := bstep (se 2 (by rfl) ⟨1957605, by rfl⟩ : syracuseStep 5220281 = 3915211) B3915211
theorem B1714121 : Blo 1140634 1714121 := bstep (se 2 (by rfl) ⟨642795, by rfl⟩ : syracuseStep 1714121 = 1285591) B1285591
theorem B1648631 : Blo 1140634 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B5482525 : Blo 1140634 5482525 := bstep (se 3 (by rfl) ⟨1027973, by rfl⟩ : syracuseStep 5482525 = 2055947) B2055947
theorem B1714235 : Blo 1140634 1714235 := bstep (se 1 (by rfl) ⟨1285676, by rfl⟩ : syracuseStep 1714235 = 2571353) B2571353
theorem B1714295 : Blo 1140634 1714295 := bstep (se 1 (by rfl) ⟨1285721, by rfl⟩ : syracuseStep 1714295 = 2571443) B2571443
theorem B1714319 : Blo 1140634 1714319 := bstep (se 1 (by rfl) ⟨1285739, by rfl⟩ : syracuseStep 1714319 = 2571479) B2571479
theorem B1714361 : Blo 1140634 1714361 := bstep (se 2 (by rfl) ⟨642885, by rfl⟩ : syracuseStep 1714361 = 1285771) B1285771
theorem B1714439 : Blo 1140634 1714439 := bstep (se 1 (by rfl) ⟨1285829, by rfl⟩ : syracuseStep 1714439 = 2571659) B2571659
theorem B1714475 : Blo 1140634 1714475 := bstep (se 1 (by rfl) ⟨1285856, by rfl⟩ : syracuseStep 1714475 = 2571713) B2571713
theorem B3090731 : Blo 1140634 3090731 := bstep (se 1 (by rfl) ⟨2318048, by rfl⟩ : syracuseStep 3090731 = 4636097) B4636097
theorem B1714505 : Blo 1140634 1714505 := bstep (se 2 (by rfl) ⟨642939, by rfl⟩ : syracuseStep 1714505 = 1285879) B1285879
theorem B2566547 : Blo 1140634 2566547 := bstep (se 1 (by rfl) ⟨1924910, by rfl⟩ : syracuseStep 2566547 = 3849821) B3849821
theorem B1714619 : Blo 1140634 1714619 := bstep (se 1 (by rfl) ⟨1285964, by rfl⟩ : syracuseStep 1714619 = 2571929) B2571929
theorem B2566601 : Blo 1140634 2566601 := bstep (se 2 (by rfl) ⟨962475, by rfl⟩ : syracuseStep 2566601 = 1924951) B1924951
theorem B6171083 : Blo 1140634 6171083 := bstep (se 1 (by rfl) ⟨4628312, by rfl⟩ : syracuseStep 6171083 = 9256625) B9256625
theorem B1714679 : Blo 1140634 1714679 := bstep (se 1 (by rfl) ⟨1286009, by rfl⟩ : syracuseStep 1714679 = 2572019) B2572019
theorem B1714703 : Blo 1140634 1714703 := bstep (se 1 (by rfl) ⟨1286027, by rfl⟩ : syracuseStep 1714703 = 2572055) B2572055
theorem B1714745 : Blo 1140634 1714745 := bstep (se 2 (by rfl) ⟨643029, by rfl⟩ : syracuseStep 1714745 = 1286059) B1286059
theorem B1714823 : Blo 1140634 1714823 := bstep (se 1 (by rfl) ⟨1286117, by rfl⟩ : syracuseStep 1714823 = 2572235) B2572235
theorem B1714859 : Blo 1140634 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B1714889 : Blo 1140634 1714889 := bstep (se 2 (by rfl) ⟨643083, by rfl⟩ : syracuseStep 1714889 = 1286167) B1286167
theorem B13019939 : Blo 1140634 13019939 := bstep (se 1 (by rfl) ⟨9764954, by rfl⟩ : syracuseStep 13019939 = 19529909) B19529909
theorem B1715003 : Blo 1140634 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B1715063 : Blo 1140634 1715063 := bstep (se 1 (by rfl) ⟨1286297, by rfl⟩ : syracuseStep 1715063 = 2572595) B2572595
theorem B1715087 : Blo 1140634 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B6499217 : Blo 1140634 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B1715129 : Blo 1140634 1715129 := bstep (se 2 (by rfl) ⟨643173, by rfl⟩ : syracuseStep 1715129 = 1286347) B1286347
theorem B2894849 : Blo 1140634 2894849 := bstep (se 2 (by rfl) ⟨1085568, by rfl⟩ : syracuseStep 2894849 = 2171137) B2171137
theorem B1715207 : Blo 1140634 1715207 := bstep (se 1 (by rfl) ⟨1286405, by rfl⟩ : syracuseStep 1715207 = 2572811) B2572811
theorem B41692171 : Blo 1140634 41692171 := bstep (se 1 (by rfl) ⟨31269128, by rfl⟩ : syracuseStep 41692171 = 62538257) B62538257
theorem B1715243 : Blo 1140634 1715243 := bstep (se 1 (by rfl) ⟨1286432, by rfl⟩ : syracuseStep 1715243 = 2572865) B2572865
theorem B1715273 : Blo 1140634 1715273 := bstep (se 2 (by rfl) ⟨643227, by rfl⟩ : syracuseStep 1715273 = 1286455) B1286455
theorem B2567303 : Blo 1140634 2567303 := bstep (se 1 (by rfl) ⟨1925477, by rfl⟩ : syracuseStep 2567303 = 3850955) B3850955
theorem B1715387 : Blo 1140634 1715387 := bstep (se 1 (by rfl) ⟨1286540, by rfl⟩ : syracuseStep 1715387 = 2573081) B2573081
theorem B11709677 : Blo 1140634 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B1715447 : Blo 1140634 1715447 := bstep (se 1 (by rfl) ⟨1286585, by rfl⟩ : syracuseStep 1715447 = 2573171) B2573171
theorem B1715471 : Blo 1140634 1715471 := bstep (se 1 (by rfl) ⟨1286603, by rfl⟩ : syracuseStep 1715471 = 2573207) B2573207
theorem B1715513 : Blo 1140634 1715513 := bstep (se 2 (by rfl) ⟨643317, by rfl⟩ : syracuseStep 1715513 = 1286635) B1286635
theorem B2567483 : Blo 1140634 2567483 := bstep (se 1 (by rfl) ⟨1925612, by rfl⟩ : syracuseStep 2567483 = 3851225) B3851225
theorem B10431803 : Blo 1140634 10431803 := bstep (se 1 (by rfl) ⟨7823852, by rfl⟩ : syracuseStep 10431803 = 15647705) B15647705
theorem B6499673 : Blo 1140634 6499673 := bstep (se 2 (by rfl) ⟨2437377, by rfl⟩ : syracuseStep 6499673 = 4874755) B4874755
theorem B2895223 : Blo 1140634 2895223 := bstep (se 1 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 2895223 = 4342835) B4342835
theorem B1715591 : Blo 1140634 1715591 := bstep (se 1 (by rfl) ⟨1286693, by rfl⟩ : syracuseStep 1715591 = 2573387) B2573387
theorem B1715627 : Blo 1140634 1715627 := bstep (se 1 (by rfl) ⟨1286720, by rfl⟩ : syracuseStep 1715627 = 2573441) B2573441
theorem B2567609 : Blo 1140634 2567609 := bstep (se 2 (by rfl) ⟨962853, by rfl⟩ : syracuseStep 2567609 = 1925707) B1925707
theorem B1715657 : Blo 1140634 1715657 := bstep (se 2 (by rfl) ⟨643371, by rfl⟩ : syracuseStep 1715657 = 1286743) B1286743
theorem B3255851 : Blo 1140634 3255851 := bstep (se 1 (by rfl) ⟨2441888, by rfl⟩ : syracuseStep 3255851 = 4883777) B4883777
theorem B1715771 : Blo 1140634 1715771 := bstep (se 1 (by rfl) ⟨1286828, by rfl⟩ : syracuseStep 1715771 = 2573657) B2573657
theorem B16461413 : Blo 1140634 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B1715831 : Blo 1140634 1715831 := bstep (se 1 (by rfl) ⟨1286873, by rfl⟩ : syracuseStep 1715831 = 2573747) B2573747
theorem B1715855 : Blo 1140634 1715855 := bstep (se 1 (by rfl) ⟨1286891, by rfl⟩ : syracuseStep 1715855 = 2573783) B2573783
theorem B1715897 : Blo 1140634 1715897 := bstep (se 2 (by rfl) ⟨643461, by rfl⟩ : syracuseStep 1715897 = 1286923) B1286923
theorem B11710169 : Blo 1140634 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B1715975 : Blo 1140634 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B2567951 : Blo 1140634 2567951 := bstep (se 1 (by rfl) ⟨1925963, by rfl⟩ : syracuseStep 2567951 = 3851927) B3851927
theorem B2567969 : Blo 1140634 2567969 := bstep (se 2 (by rfl) ⟨962988, by rfl⟩ : syracuseStep 2567969 = 1925977) B1925977
theorem B2895659 : Blo 1140634 2895659 := bstep (se 1 (by rfl) ⟨2171744, by rfl⟩ : syracuseStep 2895659 = 4343489) B4343489
theorem B1716011 : Blo 1140634 1716011 := bstep (se 1 (by rfl) ⟨1287008, by rfl⟩ : syracuseStep 1716011 = 2574017) B2574017
theorem B1716041 : Blo 1140634 1716041 := bstep (se 2 (by rfl) ⟨643515, by rfl⟩ : syracuseStep 1716041 = 1287031) B1287031
theorem B3092377 : Blo 1140634 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B1716155 : Blo 1140634 1716155 := bstep (se 1 (by rfl) ⟨1287116, by rfl⟩ : syracuseStep 1716155 = 2574233) B2574233
theorem B1716215 : Blo 1140634 1716215 := bstep (se 1 (by rfl) ⟨1287161, by rfl⟩ : syracuseStep 1716215 = 2574323) B2574323
theorem B1716239 : Blo 1140634 1716239 := bstep (se 1 (by rfl) ⟨1287179, by rfl⟩ : syracuseStep 1716239 = 2574359) B2574359
theorem B1716281 : Blo 1140634 1716281 := bstep (se 2 (by rfl) ⟨643605, by rfl⟩ : syracuseStep 1716281 = 1287211) B1287211
theorem B2568311 : Blo 1140634 2568311 := bstep (se 1 (by rfl) ⟨1926233, by rfl⟩ : syracuseStep 2568311 = 3852467) B3852467
theorem B1716359 : Blo 1140634 1716359 := bstep (se 1 (by rfl) ⟨1287269, by rfl⟩ : syracuseStep 1716359 = 2574539) B2574539
theorem B1716395 : Blo 1140634 1716395 := bstep (se 1 (by rfl) ⟨1287296, by rfl⟩ : syracuseStep 1716395 = 2574593) B2574593
theorem B6336713 : Blo 1140634 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B1716425 : Blo 1140634 1716425 := bstep (se 2 (by rfl) ⟨643659, by rfl⟩ : syracuseStep 1716425 = 1287319) B1287319
theorem B2568491 : Blo 1140634 2568491 := bstep (se 1 (by rfl) ⟨1926368, by rfl⟩ : syracuseStep 2568491 = 3852737) B3852737
theorem B1716539 : Blo 1140634 1716539 := bstep (se 1 (by rfl) ⟨1287404, by rfl⟩ : syracuseStep 1716539 = 2574809) B2574809
theorem B1716599 : Blo 1140634 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B1716623 : Blo 1140634 1716623 := bstep (se 1 (by rfl) ⟨1287467, by rfl⟩ : syracuseStep 1716623 = 2574935) B2574935
theorem B2929043 : Blo 1140634 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B1716665 : Blo 1140634 1716665 := bstep (se 2 (by rfl) ⟨643749, by rfl⟩ : syracuseStep 1716665 = 1287499) B1287499
theorem B1716743 : Blo 1140634 1716743 := bstep (se 1 (by rfl) ⟨1287557, by rfl⟩ : syracuseStep 1716743 = 2575115) B2575115
theorem B5779997 : Blo 1140634 5779997 := bstep (se 3 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 5779997 = 2167499) B2167499
theorem B5485099 : Blo 1140634 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B1716779 : Blo 1140634 1716779 := bstep (se 1 (by rfl) ⟨1287584, by rfl⟩ : syracuseStep 1716779 = 2575169) B2575169
theorem B7320131 : Blo 1140634 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B1716809 : Blo 1140634 1716809 := bstep (se 2 (by rfl) ⟨643803, by rfl⟩ : syracuseStep 1716809 = 1287607) B1287607
theorem B2896499 : Blo 1140634 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B2896519 : Blo 1140634 2896519 := bstep (se 1 (by rfl) ⟨2172389, by rfl⟩ : syracuseStep 2896519 = 4344779) B4344779
theorem B2568851 : Blo 1140634 2568851 := bstep (se 1 (by rfl) ⟨1926638, by rfl⟩ : syracuseStep 2568851 = 3853277) B3853277
theorem B1716923 : Blo 1140634 1716923 := bstep (se 1 (by rfl) ⟨1287692, by rfl⟩ : syracuseStep 1716923 = 2575385) B2575385
theorem B2568905 : Blo 1140634 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B8237861 : Blo 1140634 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B2896793 : Blo 1140634 2896793 := bstep (se 2 (by rfl) ⟨1086297, by rfl⟩ : syracuseStep 2896793 = 2172595) B2172595
theorem B5780483 : Blo 1140634 5780483 := bstep (se 1 (by rfl) ⟨4335362, by rfl⟩ : syracuseStep 5780483 = 8670725) B8670725
theorem B2896955 : Blo 1140634 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B3257491 : Blo 1140634 3257491 := bstep (se 1 (by rfl) ⟨2443118, by rfl⟩ : syracuseStep 3257491 = 4886237) B4886237
theorem B2897167 : Blo 1140634 2897167 := bstep (se 1 (by rfl) ⟨2172875, by rfl⟩ : syracuseStep 2897167 = 4345751) B4345751
theorem B2569607 : Blo 1140634 2569607 := bstep (se 1 (by rfl) ⟨1927205, by rfl⟩ : syracuseStep 2569607 = 3854411) B3854411
theorem B4339129 : Blo 1140634 4339129 := bstep (se 2 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 4339129 = 3254347) B3254347
theorem B2569787 : Blo 1140634 2569787 := bstep (se 1 (by rfl) ⟨1927340, by rfl⟩ : syracuseStep 2569787 = 3854681) B3854681
theorem B4175479 : Blo 1140634 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B2569913 : Blo 1140634 2569913 := bstep (se 2 (by rfl) ⟨963717, by rfl⟩ : syracuseStep 2569913 = 1927435) B1927435
theorem B8927243 : Blo 1140634 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B2570255 : Blo 1140634 2570255 := bstep (se 1 (by rfl) ⟨1927691, by rfl⟩ : syracuseStep 2570255 = 3855383) B3855383
theorem B2570273 : Blo 1140634 2570273 := bstep (se 2 (by rfl) ⟨963852, by rfl⟩ : syracuseStep 2570273 = 1927705) B1927705
theorem B2570615 : Blo 1140634 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B6502841 : Blo 1140634 6502841 := bstep (se 2 (by rfl) ⟨2438565, by rfl⟩ : syracuseStep 6502841 = 4877131) B4877131
theorem B2570795 : Blo 1140634 2570795 := bstep (se 1 (by rfl) ⟨1928096, by rfl⟩ : syracuseStep 2570795 = 3856193) B3856193
theorem B5782103 : Blo 1140634 5782103 := bstep (se 1 (by rfl) ⟨4336577, by rfl⟩ : syracuseStep 5782103 = 8673155) B8673155
theorem B3259223 : Blo 1140634 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B2571155 : Blo 1140634 2571155 := bstep (se 1 (by rfl) ⟨1928366, by rfl⟩ : syracuseStep 2571155 = 3856733) B3856733
theorem B2571209 : Blo 1140634 2571209 := bstep (se 2 (by rfl) ⟨964203, by rfl⟩ : syracuseStep 2571209 = 1928407) B1928407
theorem B5782589 : Blo 1140634 5782589 := bstep (se 3 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 5782589 = 2168471) B2168471
theorem B41729539 : Blo 1140634 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B10993229 : Blo 1140634 10993229 := bstep (se 3 (by rfl) ⟨2061230, by rfl⟩ : syracuseStep 10993229 = 4122461) B4122461
theorem B2571911 : Blo 1140634 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B3849929 : Blo 1140634 3849929 := bstep (se 2 (by rfl) ⟨1443723, by rfl⟩ : syracuseStep 3849929 = 2887447) B2887447
theorem B2572091 : Blo 1140634 2572091 := bstep (se 1 (by rfl) ⟨1929068, by rfl⟩ : syracuseStep 2572091 = 3858137) B3858137
theorem B2572217 : Blo 1140634 2572217 := bstep (se 2 (by rfl) ⟨964581, by rfl⟩ : syracuseStep 2572217 = 1929163) B1929163
theorem B4112471 : Blo 1140634 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B2572559 : Blo 1140634 2572559 := bstep (se 1 (by rfl) ⟨1929419, by rfl⟩ : syracuseStep 2572559 = 3858839) B3858839
theorem B4342031 : Blo 1140634 4342031 := bstep (se 1 (by rfl) ⟨3256523, by rfl⟩ : syracuseStep 4342031 = 6513047) B6513047
theorem B2572577 : Blo 1140634 2572577 := bstep (se 2 (by rfl) ⟨964716, by rfl⟩ : syracuseStep 2572577 = 1929433) B1929433
theorem B3850631 : Blo 1140634 3850631 := bstep (se 1 (by rfl) ⟨2887973, by rfl⟩ : syracuseStep 3850631 = 5775947) B5775947
theorem B4112963 : Blo 1140634 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B2572919 : Blo 1140634 2572919 := bstep (se 1 (by rfl) ⟨1929689, by rfl⟩ : syracuseStep 2572919 = 3859379) B3859379
theorem B3851009 : Blo 1140634 3851009 := bstep (se 2 (by rfl) ⟨1444128, by rfl⟩ : syracuseStep 3851009 = 2888257) B2888257
theorem B6505231 : Blo 1140634 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B2573099 : Blo 1140634 2573099 := bstep (se 1 (by rfl) ⟨1929824, by rfl⟩ : syracuseStep 2573099 = 3859649) B3859649
theorem B5784371 : Blo 1140634 5784371 := bstep (se 1 (by rfl) ⟨4338278, by rfl⟩ : syracuseStep 5784371 = 8676557) B8676557
theorem B5784695 : Blo 1140634 5784695 := bstep (se 1 (by rfl) ⟨4338521, by rfl⟩ : syracuseStep 5784695 = 8677043) B8677043
theorem B2573459 : Blo 1140634 2573459 := bstep (se 1 (by rfl) ⟨1930094, by rfl⟩ : syracuseStep 2573459 = 3860189) B3860189
theorem B2573513 : Blo 1140634 2573513 := bstep (se 2 (by rfl) ⟨965067, by rfl⟩ : syracuseStep 2573513 = 1930135) B1930135
theorem B2934049 : Blo 1140634 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B3851819 : Blo 1140634 3851819 := bstep (se 1 (by rfl) ⟨2888864, by rfl⟩ : syracuseStep 3851819 = 5777729) B5777729
theorem B2442811 : Blo 1140634 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B12371575 : Blo 1140634 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B4114157 : Blo 1140634 4114157 := bstep (se 3 (by rfl) ⟨771404, by rfl⟩ : syracuseStep 4114157 = 1542809) B1542809
theorem B2574215 : Blo 1140634 2574215 := bstep (se 1 (by rfl) ⟨1930661, by rfl⟩ : syracuseStep 2574215 = 3861323) B3861323
theorem B2606995 : Blo 1140634 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B24692633 : Blo 1140634 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B6506507 : Blo 1140634 6506507 := bstep (se 1 (by rfl) ⟨4879880, by rfl⟩ : syracuseStep 6506507 = 9759761) B9759761
theorem B2574395 : Blo 1140634 2574395 := bstep (se 1 (by rfl) ⟨1930796, by rfl⟩ : syracuseStep 2574395 = 3861593) B3861593
theorem B5785667 : Blo 1140634 5785667 := bstep (se 1 (by rfl) ⟨4339250, by rfl⟩ : syracuseStep 5785667 = 8678501) B8678501
theorem B3655799 : Blo 1140634 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B12372101 : Blo 1140634 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B1624207 : Blo 1140634 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B2574521 : Blo 1140634 2574521 := bstep (se 2 (by rfl) ⟨965445, by rfl⟩ : syracuseStep 2574521 = 1930891) B1930891
theorem B6506689 : Blo 1140634 6506689 := bstep (se 2 (by rfl) ⟨2440008, by rfl⟩ : syracuseStep 6506689 = 4880017) B4880017
theorem B12503285 : Blo 1140634 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B4114747 : Blo 1140634 4114747 := bstep (se 1 (by rfl) ⟨3086060, by rfl⟩ : syracuseStep 4114747 = 6172121) B6172121
theorem B1853831 : Blo 1140634 1853831 := bstep (se 1 (by rfl) ⟨1390373, by rfl⟩ : syracuseStep 1853831 = 2780747) B2780747
theorem B5785991 : Blo 1140634 5785991 := bstep (se 1 (by rfl) ⟨4339493, by rfl⟩ : syracuseStep 5785991 = 8678987) B8678987
theorem B5491097 : Blo 1140634 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B2574863 : Blo 1140634 2574863 := bstep (se 1 (by rfl) ⟨1931147, by rfl⟩ : syracuseStep 2574863 = 3862295) B3862295
theorem B2574881 : Blo 1140634 2574881 := bstep (se 2 (by rfl) ⟨965580, by rfl⟩ : syracuseStep 2574881 = 1931161) B1931161
theorem B3853115 : Blo 1140634 3853115 := bstep (se 1 (by rfl) ⟨2889836, by rfl⟩ : syracuseStep 3853115 = 5779673) B5779673
theorem B14830451 : Blo 1140634 14830451 := bstep (se 1 (by rfl) ⟨11122838, by rfl⟩ : syracuseStep 14830451 = 22245677) B22245677
theorem B2575223 : Blo 1140634 2575223 := bstep (se 1 (by rfl) ⟨1931417, by rfl⟩ : syracuseStep 2575223 = 3862835) B3862835
theorem B2575403 : Blo 1140634 2575403 := bstep (se 1 (by rfl) ⟨1931552, by rfl⟩ : syracuseStep 2575403 = 3863105) B3863105
theorem B1625351 : Blo 1140634 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B3853601 : Blo 1140634 3853601 := bstep (se 2 (by rfl) ⟨1445100, by rfl⟩ : syracuseStep 3853601 = 2890201) B2890201
theorem B125062501 : Blo 1140634 125062501 := bstep (se 4 (by rfl) ⟨11724609, by rfl⟩ : syracuseStep 125062501 = 23449219) B23449219
theorem B4345235 : Blo 1140634 4345235 := bstep (se 1 (by rfl) ⟨3258926, by rfl⟩ : syracuseStep 4345235 = 6517853) B6517853
theorem B1625545 : Blo 1140634 1625545 := bstep (se 2 (by rfl) ⟨609579, by rfl⟩ : syracuseStep 1625545 = 1219159) B1219159
theorem B15650333 : Blo 1140634 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B3854195 : Blo 1140634 3854195 := bstep (se 1 (by rfl) ⟨2890646, by rfl⟩ : syracuseStep 3854195 = 5781293) B5781293
theorem B1626103 : Blo 1140634 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B9883781 : Blo 1140634 9883781 := bstep (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) B1853209
theorem B24695057 : Blo 1140634 24695057 := bstep (se 2 (by rfl) ⟨9260646, by rfl⟩ : syracuseStep 24695057 = 18521293) B18521293
theorem B8671697 : Blo 1140634 8671697 := bstep (se 2 (by rfl) ⟨3251886, by rfl⟩ : syracuseStep 8671697 = 6503773) B6503773
theorem B6181379 : Blo 1140634 6181379 := bstep (se 1 (by rfl) ⟨4636034, by rfl⟩ : syracuseStep 6181379 = 9272069) B9272069
theorem B1528393 : Blo 1140634 1528393 := bstep (se 2 (by rfl) ⟨573147, by rfl⟩ : syracuseStep 1528393 = 1146295) B1146295
theorem B1626809 : Blo 1140634 1626809 := bstep (se 2 (by rfl) ⟨610053, by rfl⟩ : syracuseStep 1626809 = 1220107) B1220107
theorem B4117229 : Blo 1140634 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B13030145 : Blo 1140634 13030145 := bstep (se 2 (by rfl) ⟨4886304, by rfl⟩ : syracuseStep 13030145 = 9772609) B9772609
theorem B1626895 : Blo 1140634 1626895 := bstep (se 1 (by rfl) ⟨1220171, by rfl⟩ : syracuseStep 1626895 = 2440343) B2440343
theorem B1626923 : Blo 1140634 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B12342131 : Blo 1140634 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B11719685 : Blo 1140634 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B21976069 : Blo 1140634 21976069 := bstep (se 4 (by rfl) ⟨2060256, by rfl⟩ : syracuseStep 21976069 = 4120513) B4120513
theorem B10999415 : Blo 1140634 10999415 := bstep (se 1 (by rfl) ⟨8249561, by rfl⟩ : syracuseStep 10999415 = 16499123) B16499123
theorem B5789555 : Blo 1140634 5789555 := bstep (se 1 (by rfl) ⟨4342166, by rfl⟩ : syracuseStep 5789555 = 8684333) B8684333
theorem B5494787 : Blo 1140634 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B27121837 : Blo 1140634 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B2742473 : Blo 1140634 2742473 := bstep (se 2 (by rfl) ⟨1028427, by rfl⟩ : syracuseStep 2742473 = 2056855) B2056855
theorem B6510881 : Blo 1140634 6510881 := bstep (se 2 (by rfl) ⟨2441580, by rfl⟩ : syracuseStep 6510881 = 4883161) B4883161
theorem B4118843 : Blo 1140634 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B5790041 : Blo 1140634 5790041 := bstep (se 2 (by rfl) ⟨2171265, by rfl⟩ : syracuseStep 5790041 = 4342531) B4342531
theorem B3660167 : Blo 1140634 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B3856787 : Blo 1140634 3856787 := bstep (se 1 (by rfl) ⟨2892590, by rfl⟩ : syracuseStep 3856787 = 5785181) B5785181
theorem B2383033 : Blo 1140634 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B2088251 : Blo 1140634 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B13033061 : Blo 1140634 13033061 := bstep (se 4 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 13033061 = 2443699) B2443699
theorem B3858191 : Blo 1140634 3858191 := bstep (se 1 (by rfl) ⟨2893643, by rfl⟩ : syracuseStep 3858191 = 5787287) B5787287
theorem B3858461 : Blo 1140634 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B2744435 : Blo 1140634 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B1925255 : Blo 1140634 1925255 := bstep (se 1 (by rfl) ⟨1443941, by rfl⟩ : syracuseStep 1925255 = 2887883) B2887883
theorem B5792147 : Blo 1140634 5792147 := bstep (se 1 (by rfl) ⟨4344110, by rfl⟩ : syracuseStep 5792147 = 8688221) B8688221
theorem B6251069 : Blo 1140634 6251069 := bstep (se 3 (by rfl) ⟨1172075, by rfl⟩ : syracuseStep 6251069 = 2344151) B2344151
theorem B1925903 : Blo 1140634 1925903 := bstep (se 1 (by rfl) ⟨1444427, by rfl⟩ : syracuseStep 1925903 = 2888855) B2888855
theorem B1303355 : Blo 1140634 1303355 := bstep (se 1 (by rfl) ⟨977516, by rfl⟩ : syracuseStep 1303355 = 1955033) B1955033
theorem B53470129 : Blo 1140634 53470129 := bstep (se 2 (by rfl) ⟨20051298, by rfl⟩ : syracuseStep 53470129 = 40102597) B40102597
theorem B2057231 : Blo 1140634 2057231 := bstep (se 1 (by rfl) ⟨1542923, by rfl⟩ : syracuseStep 2057231 = 3085847) B3085847
theorem B13034519 : Blo 1140634 13034519 := bstep (se 1 (by rfl) ⟨9775889, by rfl⟩ : syracuseStep 13034519 = 19551779) B19551779
theorem B5498057 : Blo 1140634 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B1926443 : Blo 1140634 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B6513979 : Blo 1140634 6513979 := bstep (se 1 (by rfl) ⟨4885484, by rfl⟩ : syracuseStep 6513979 = 9770969) B9770969
theorem B3859865 : Blo 1140634 3859865 := bstep (se 2 (by rfl) ⟨1447449, by rfl⟩ : syracuseStep 3859865 = 2894899) B2894899
theorem B2057771 : Blo 1140634 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B2319931 : Blo 1140634 2319931 := bstep (se 1 (by rfl) ⟨1739948, by rfl⟩ : syracuseStep 2319931 = 3479897) B3479897
theorem B1926841 : Blo 1140634 1926841 := bstep (se 2 (by rfl) ⟨722565, by rfl⟩ : syracuseStep 1926841 = 1445131) B1445131
theorem B3663731 : Blo 1140634 3663731 := bstep (se 1 (by rfl) ⟨2747798, by rfl⟩ : syracuseStep 3663731 = 5495597) B5495597
theorem B1140667 : Blo 1140634 1140667 := bstep (se 1 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 1140667 = 1711001) B1711001
theorem B1140743 : Blo 1140634 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B1140751 : Blo 1140634 1140751 := bstep (se 1 (by rfl) ⟨855563, by rfl⟩ : syracuseStep 1140751 = 1711127) B1711127
theorem B1140795 : Blo 1140634 1140795 := bstep (se 1 (by rfl) ⟨855596, by rfl⟩ : syracuseStep 1140795 = 1711193) B1711193
theorem B3860567 : Blo 1140634 3860567 := bstep (se 1 (by rfl) ⟨2895425, by rfl⟩ : syracuseStep 3860567 = 5790851) B5790851
theorem B1140871 : Blo 1140634 1140871 := bstep (se 1 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 1140871 = 1711307) B1711307
theorem B1140879 : Blo 1140634 1140879 := bstep (se 1 (by rfl) ⟨855659, by rfl⟩ : syracuseStep 1140879 = 1711319) B1711319
theorem B1140923 : Blo 1140634 1140923 := bstep (se 1 (by rfl) ⟨855692, by rfl⟩ : syracuseStep 1140923 = 1711385) B1711385
theorem B1140999 : Blo 1140634 1140999 := bstep (se 1 (by rfl) ⟨855749, by rfl⟩ : syracuseStep 1140999 = 1711499) B1711499
theorem B1141007 : Blo 1140634 1141007 := bstep (se 1 (by rfl) ⟨855755, by rfl⟩ : syracuseStep 1141007 = 1711511) B1711511
theorem B1141051 : Blo 1140634 1141051 := bstep (se 1 (by rfl) ⟨855788, by rfl⟩ : syracuseStep 1141051 = 1711577) B1711577
theorem B1927543 : Blo 1140634 1927543 := bstep (se 1 (by rfl) ⟨1445657, by rfl⟩ : syracuseStep 1927543 = 2891315) B2891315
theorem B1141127 : Blo 1140634 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B1141135 : Blo 1140634 1141135 := bstep (se 1 (by rfl) ⟨855851, by rfl⟩ : syracuseStep 1141135 = 1711703) B1711703
theorem B1141179 : Blo 1140634 1141179 := bstep (se 1 (by rfl) ⟨855884, by rfl⟩ : syracuseStep 1141179 = 1711769) B1711769
theorem B1141255 : Blo 1140634 1141255 := bstep (se 1 (by rfl) ⟨855941, by rfl⟩ : syracuseStep 1141255 = 1711883) B1711883
theorem B1141263 : Blo 1140634 1141263 := bstep (se 1 (by rfl) ⟨855947, by rfl⟩ : syracuseStep 1141263 = 1711895) B1711895
theorem B1141307 : Blo 1140634 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B1927739 : Blo 1140634 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B3861053 : Blo 1140634 3861053 := bstep (se 3 (by rfl) ⟨723947, by rfl⟩ : syracuseStep 3861053 = 1447895) B1447895
theorem B1141383 : Blo 1140634 1141383 := bstep (se 1 (by rfl) ⟨856037, by rfl⟩ : syracuseStep 1141383 = 1712075) B1712075
theorem B1141391 : Blo 1140634 1141391 := bstep (se 1 (by rfl) ⟨856043, by rfl⟩ : syracuseStep 1141391 = 1712087) B1712087
theorem B1141435 : Blo 1140634 1141435 := bstep (se 1 (by rfl) ⟨856076, by rfl⟩ : syracuseStep 1141435 = 1712153) B1712153
theorem B6515437 : Blo 1140634 6515437 := bstep (se 3 (by rfl) ⟨1221644, by rfl⟩ : syracuseStep 6515437 = 2443289) B2443289
theorem B1141511 : Blo 1140634 1141511 := bstep (se 1 (by rfl) ⟨856133, by rfl⟩ : syracuseStep 1141511 = 1712267) B1712267
theorem B1141519 : Blo 1140634 1141519 := bstep (se 1 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 1141519 = 1712279) B1712279
theorem B6941477 : Blo 1140634 6941477 := bstep (se 4 (by rfl) ⟨650763, by rfl⟩ : syracuseStep 6941477 = 1301527) B1301527
theorem B1141563 : Blo 1140634 1141563 := bstep (se 1 (by rfl) ⟨856172, by rfl⟩ : syracuseStep 1141563 = 1712345) B1712345
theorem B1141639 : Blo 1140634 1141639 := bstep (se 1 (by rfl) ⟨856229, by rfl⟩ : syracuseStep 1141639 = 1712459) B1712459
theorem B1141647 : Blo 1140634 1141647 := bstep (se 1 (by rfl) ⟨856235, by rfl⟩ : syracuseStep 1141647 = 1712471) B1712471
theorem B1141691 : Blo 1140634 1141691 := bstep (se 1 (by rfl) ⟨856268, by rfl⟩ : syracuseStep 1141691 = 1712537) B1712537
theorem B1928137 : Blo 1140634 1928137 := bstep (se 2 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 1928137 = 1446103) B1446103
theorem B1141767 : Blo 1140634 1141767 := bstep (se 1 (by rfl) ⟨856325, by rfl⟩ : syracuseStep 1141767 = 1712651) B1712651
theorem B1141775 : Blo 1140634 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B1371179 : Blo 1140634 1371179 := bstep (se 1 (by rfl) ⟨1028384, by rfl⟩ : syracuseStep 1371179 = 2056769) B2056769
theorem B1141819 : Blo 1140634 1141819 := bstep (se 1 (by rfl) ⟨856364, by rfl⟩ : syracuseStep 1141819 = 1712729) B1712729
theorem B1141895 : Blo 1140634 1141895 := bstep (se 1 (by rfl) ⟨856421, by rfl⟩ : syracuseStep 1141895 = 1712843) B1712843
theorem B1141903 : Blo 1140634 1141903 := bstep (se 1 (by rfl) ⟨856427, by rfl⟩ : syracuseStep 1141903 = 1712855) B1712855
theorem B1141947 : Blo 1140634 1141947 := bstep (se 1 (by rfl) ⟨856460, by rfl⟩ : syracuseStep 1141947 = 1712921) B1712921
theorem B1142023 : Blo 1140634 1142023 := bstep (se 1 (by rfl) ⟨856517, by rfl⟩ : syracuseStep 1142023 = 1713035) B1713035
theorem B1142031 : Blo 1140634 1142031 := bstep (se 1 (by rfl) ⟨856523, by rfl⟩ : syracuseStep 1142031 = 1713047) B1713047
theorem B1142075 : Blo 1140634 1142075 := bstep (se 1 (by rfl) ⟨856556, by rfl⟩ : syracuseStep 1142075 = 1713113) B1713113
theorem B1142151 : Blo 1140634 1142151 := bstep (se 1 (by rfl) ⟨856613, by rfl⟩ : syracuseStep 1142151 = 1713227) B1713227
theorem B1142159 : Blo 1140634 1142159 := bstep (se 1 (by rfl) ⟨856619, by rfl⟩ : syracuseStep 1142159 = 1713239) B1713239
theorem B1142203 : Blo 1140634 1142203 := bstep (se 1 (by rfl) ⟨856652, by rfl⟩ : syracuseStep 1142203 = 1713305) B1713305
theorem B1142279 : Blo 1140634 1142279 := bstep (se 1 (by rfl) ⟨856709, by rfl⟩ : syracuseStep 1142279 = 1713419) B1713419
theorem B1142287 : Blo 1140634 1142287 := bstep (se 1 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 1142287 = 1713431) B1713431
theorem B1142331 : Blo 1140634 1142331 := bstep (se 1 (by rfl) ⟨856748, by rfl⟩ : syracuseStep 1142331 = 1713497) B1713497
theorem B1142407 : Blo 1140634 1142407 := bstep (se 1 (by rfl) ⟨856805, by rfl⟩ : syracuseStep 1142407 = 1713611) B1713611
theorem B1928839 : Blo 1140634 1928839 := bstep (se 1 (by rfl) ⟨1446629, by rfl⟩ : syracuseStep 1928839 = 2893259) B2893259
theorem B1142415 : Blo 1140634 1142415 := bstep (se 1 (by rfl) ⟨856811, by rfl⟩ : syracuseStep 1142415 = 1713623) B1713623
theorem B1142459 : Blo 1140634 1142459 := bstep (se 1 (by rfl) ⟨856844, by rfl⟩ : syracuseStep 1142459 = 1713689) B1713689
theorem B1142535 : Blo 1140634 1142535 := bstep (se 1 (by rfl) ⟨856901, by rfl⟩ : syracuseStep 1142535 = 1713803) B1713803
theorem B1142543 : Blo 1140634 1142543 := bstep (se 1 (by rfl) ⟨856907, by rfl⟩ : syracuseStep 1142543 = 1713815) B1713815
theorem B1142587 : Blo 1140634 1142587 := bstep (se 1 (by rfl) ⟨856940, by rfl⟩ : syracuseStep 1142587 = 1713881) B1713881
theorem B1142663 : Blo 1140634 1142663 := bstep (se 1 (by rfl) ⟨856997, by rfl⟩ : syracuseStep 1142663 = 1713995) B1713995
theorem B1142671 : Blo 1140634 1142671 := bstep (se 1 (by rfl) ⟨857003, by rfl⟩ : syracuseStep 1142671 = 1714007) B1714007
theorem B3862457 : Blo 1140634 3862457 := bstep (se 2 (by rfl) ⟨1448421, by rfl⟩ : syracuseStep 3862457 = 2896843) B2896843
theorem B1142715 : Blo 1140634 1142715 := bstep (se 1 (by rfl) ⟨857036, by rfl⟩ : syracuseStep 1142715 = 1714073) B1714073
theorem B1142791 : Blo 1140634 1142791 := bstep (se 1 (by rfl) ⟨857093, by rfl⟩ : syracuseStep 1142791 = 1714187) B1714187
theorem B1142799 : Blo 1140634 1142799 := bstep (se 1 (by rfl) ⟨857099, by rfl⟩ : syracuseStep 1142799 = 1714199) B1714199
theorem B46886957 : Blo 1140634 46886957 := bstep (se 3 (by rfl) ⟨8791304, by rfl⟩ : syracuseStep 46886957 = 17582609) B17582609
theorem B1142843 : Blo 1140634 1142843 := bstep (se 1 (by rfl) ⟨857132, by rfl⟩ : syracuseStep 1142843 = 1714265) B1714265
theorem B1142919 : Blo 1140634 1142919 := bstep (se 1 (by rfl) ⟨857189, by rfl⟩ : syracuseStep 1142919 = 1714379) B1714379
theorem B1142927 : Blo 1140634 1142927 := bstep (se 1 (by rfl) ⟨857195, by rfl⟩ : syracuseStep 1142927 = 1714391) B1714391
theorem B1142971 : Blo 1140634 1142971 := bstep (se 1 (by rfl) ⟨857228, by rfl⟩ : syracuseStep 1142971 = 1714457) B1714457
theorem B1143047 : Blo 1140634 1143047 := bstep (se 1 (by rfl) ⟨857285, by rfl⟩ : syracuseStep 1143047 = 1714571) B1714571
theorem B1143055 : Blo 1140634 1143055 := bstep (se 1 (by rfl) ⟨857291, by rfl⟩ : syracuseStep 1143055 = 1714583) B1714583
theorem B1929487 : Blo 1140634 1929487 := bstep (se 1 (by rfl) ⟨1447115, by rfl⟩ : syracuseStep 1929487 = 2894231) B2894231
theorem B1143099 : Blo 1140634 1143099 := bstep (se 1 (by rfl) ⟨857324, by rfl⟩ : syracuseStep 1143099 = 1714649) B1714649
theorem B1143175 : Blo 1140634 1143175 := bstep (se 1 (by rfl) ⟨857381, by rfl⟩ : syracuseStep 1143175 = 1714763) B1714763
theorem B1143183 : Blo 1140634 1143183 := bstep (se 1 (by rfl) ⟨857387, by rfl⟩ : syracuseStep 1143183 = 1714775) B1714775
theorem B1143227 : Blo 1140634 1143227 := bstep (se 1 (by rfl) ⟨857420, by rfl⟩ : syracuseStep 1143227 = 1714841) B1714841
theorem B1143303 : Blo 1140634 1143303 := bstep (se 1 (by rfl) ⟨857477, by rfl⟩ : syracuseStep 1143303 = 1714955) B1714955
theorem B3863051 : Blo 1140634 3863051 := bstep (se 1 (by rfl) ⟨2897288, by rfl⟩ : syracuseStep 3863051 = 5794577) B5794577
theorem B1143311 : Blo 1140634 1143311 := bstep (se 1 (by rfl) ⟨857483, by rfl⟩ : syracuseStep 1143311 = 1714967) B1714967
theorem B2748971 : Blo 1140634 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B1143355 : Blo 1140634 1143355 := bstep (se 1 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 1143355 = 1715033) B1715033
theorem B1143431 : Blo 1140634 1143431 := bstep (se 1 (by rfl) ⟨857573, by rfl⟩ : syracuseStep 1143431 = 1715147) B1715147
theorem B1143439 : Blo 1140634 1143439 := bstep (se 1 (by rfl) ⟨857579, by rfl⟩ : syracuseStep 1143439 = 1715159) B1715159
theorem B6517421 : Blo 1140634 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B1831609 : Blo 1140634 1831609 := bstep (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) B1373707
theorem B1143483 : Blo 1140634 1143483 := bstep (se 1 (by rfl) ⟨857612, by rfl⟩ : syracuseStep 1143483 = 1715225) B1715225
theorem B1143559 : Blo 1140634 1143559 := bstep (se 1 (by rfl) ⟨857669, by rfl⟩ : syracuseStep 1143559 = 1715339) B1715339
theorem B1143567 : Blo 1140634 1143567 := bstep (se 1 (by rfl) ⟨857675, by rfl⟩ : syracuseStep 1143567 = 1715351) B1715351
theorem B3666703 : Blo 1140634 3666703 := bstep (se 1 (by rfl) ⟨2750027, by rfl⟩ : syracuseStep 3666703 = 5500055) B5500055
theorem B1930027 : Blo 1140634 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B11727665 : Blo 1140634 11727665 := bstep (se 2 (by rfl) ⟨4397874, by rfl⟩ : syracuseStep 11727665 = 8795749) B8795749
theorem B1143611 : Blo 1140634 1143611 := bstep (se 1 (by rfl) ⟨857708, by rfl⟩ : syracuseStep 1143611 = 1715417) B1715417
theorem B1143687 : Blo 1140634 1143687 := bstep (se 1 (by rfl) ⟨857765, by rfl⟩ : syracuseStep 1143687 = 1715531) B1715531
theorem B1143695 : Blo 1140634 1143695 := bstep (se 1 (by rfl) ⟨857771, by rfl⟩ : syracuseStep 1143695 = 1715543) B1715543
theorem B1930169 : Blo 1140634 1930169 := bstep (se 2 (by rfl) ⟨723813, by rfl⟩ : syracuseStep 1930169 = 1447627) B1447627
theorem B1143739 : Blo 1140634 1143739 := bstep (se 1 (by rfl) ⟨857804, by rfl⟩ : syracuseStep 1143739 = 1715609) B1715609
theorem B1143815 : Blo 1140634 1143815 := bstep (se 1 (by rfl) ⟨857861, by rfl⟩ : syracuseStep 1143815 = 1715723) B1715723
theorem B1143823 : Blo 1140634 1143823 := bstep (se 1 (by rfl) ⟨857867, by rfl⟩ : syracuseStep 1143823 = 1715735) B1715735
theorem B4879403 : Blo 1140634 4879403 := bstep (se 1 (by rfl) ⟨3659552, by rfl⟩ : syracuseStep 4879403 = 7319105) B7319105
theorem B1143867 : Blo 1140634 1143867 := bstep (se 1 (by rfl) ⟨857900, by rfl⟩ : syracuseStep 1143867 = 1715801) B1715801
theorem B1143943 : Blo 1140634 1143943 := bstep (se 1 (by rfl) ⟨857957, by rfl⟩ : syracuseStep 1143943 = 1715915) B1715915
theorem B1143951 : Blo 1140634 1143951 := bstep (se 1 (by rfl) ⟨857963, by rfl⟩ : syracuseStep 1143951 = 1715927) B1715927
theorem B1143995 : Blo 1140634 1143995 := bstep (se 1 (by rfl) ⟨857996, by rfl⟩ : syracuseStep 1143995 = 1715993) B1715993
theorem B43971821 : Blo 1140634 43971821 := bstep (se 3 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 43971821 = 16489433) B16489433
theorem B1144071 : Blo 1140634 1144071 := bstep (se 1 (by rfl) ⟨858053, by rfl⟩ : syracuseStep 1144071 = 1716107) B1716107
theorem B1144079 : Blo 1140634 1144079 := bstep (se 1 (by rfl) ⟨858059, by rfl⟩ : syracuseStep 1144079 = 1716119) B1716119
theorem B1144123 : Blo 1140634 1144123 := bstep (se 1 (by rfl) ⟨858092, by rfl⟩ : syracuseStep 1144123 = 1716185) B1716185
theorem B1144199 : Blo 1140634 1144199 := bstep (se 1 (by rfl) ⟨858149, by rfl⟩ : syracuseStep 1144199 = 1716299) B1716299
theorem B1144207 : Blo 1140634 1144207 := bstep (se 1 (by rfl) ⟨858155, by rfl⟩ : syracuseStep 1144207 = 1716311) B1716311
theorem B1144251 : Blo 1140634 1144251 := bstep (se 1 (by rfl) ⟨858188, by rfl⟩ : syracuseStep 1144251 = 1716377) B1716377
theorem B6944221 : Blo 1140634 6944221 := bstep (se 3 (by rfl) ⟨1302041, by rfl⟩ : syracuseStep 6944221 = 2604083) B2604083
theorem B1144327 : Blo 1140634 1144327 := bstep (se 1 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 1144327 = 1716491) B1716491
theorem B1144335 : Blo 1140634 1144335 := bstep (se 1 (by rfl) ⟨858251, by rfl⟩ : syracuseStep 1144335 = 1716503) B1716503
theorem B1373755 : Blo 1140634 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B1144379 : Blo 1140634 1144379 := bstep (se 1 (by rfl) ⟨858284, by rfl⟩ : syracuseStep 1144379 = 1716569) B1716569
theorem B1930871 : Blo 1140634 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B1144455 : Blo 1140634 1144455 := bstep (se 1 (by rfl) ⟨858341, by rfl⟩ : syracuseStep 1144455 = 1716683) B1716683
theorem B1144463 : Blo 1140634 1144463 := bstep (se 1 (by rfl) ⟨858347, by rfl⟩ : syracuseStep 1144463 = 1716695) B1716695
theorem B1144507 : Blo 1140634 1144507 := bstep (se 1 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 1144507 = 1716761) B1716761
theorem B1144583 : Blo 1140634 1144583 := bstep (se 1 (by rfl) ⟨858437, by rfl⟩ : syracuseStep 1144583 = 1716875) B1716875
theorem B1144591 : Blo 1140634 1144591 := bstep (se 1 (by rfl) ⟨858443, by rfl⟩ : syracuseStep 1144591 = 1716887) B1716887
theorem B1669177 : Blo 1140634 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B1931323 : Blo 1140634 1931323 := bstep (se 1 (by rfl) ⟨1448492, by rfl⟩ : syracuseStep 1931323 = 2896985) B2896985
theorem B1931465 : Blo 1140634 1931465 := bstep (se 2 (by rfl) ⟨724299, by rfl⟩ : syracuseStep 1931465 = 1448599) B1448599
theorem B10418959 : Blo 1140634 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B4881779 : Blo 1140634 4881779 := bstep (se 1 (by rfl) ⟨3661334, by rfl⟩ : syracuseStep 4881779 = 7322669) B7322669
theorem B13008275 : Blo 1140634 13008275 := bstep (se 1 (by rfl) ⟨9756206, by rfl⟩ : syracuseStep 13008275 = 19512413) B19512413
theorem B18546205 : Blo 1140634 18546205 := bstep (se 3 (by rfl) ⟨3477413, by rfl⟩ : syracuseStep 18546205 = 6954827) B6954827
theorem B4947713 : Blo 1140634 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B17563763 : Blo 1140634 17563763 := bstep (se 1 (by rfl) ⟨13172822, by rfl⟩ : syracuseStep 17563763 = 26345645) B26345645
theorem B5505671 : Blo 1140634 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B8685305 : Blo 1140634 8685305 := bstep (se 2 (by rfl) ⟨3256989, by rfl⟩ : syracuseStep 8685305 = 6513979) B6513979
theorem B3475613 : Blo 1140634 3475613 := bstep (se 3 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 3475613 = 1303355) B1303355
theorem B7309673 : Blo 1140634 7309673 := bstep (se 2 (by rfl) ⟨2741127, by rfl⟩ : syracuseStep 7309673 = 5482255) B5482255
theorem B3475993 : Blo 1140634 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B7310033 : Blo 1140634 7310033 := bstep (se 2 (by rfl) ⟨2741262, by rfl⟩ : syracuseStep 7310033 = 5482525) B5482525
theorem B6589187 : Blo 1140634 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B2165609 : Blo 1140634 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B8686763 : Blo 1140634 8686763 := bstep (se 1 (by rfl) ⟨6515072, by rfl⟩ : syracuseStep 8686763 = 13030145) B13030145
theorem B8228087 : Blo 1140634 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B3083663 : Blo 1140634 3083663 := bstep (se 1 (by rfl) ⟨2312747, by rfl⟩ : syracuseStep 3083663 = 4625495) B4625495
theorem B1445303 : Blo 1140634 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B1445455 : Blo 1140634 1445455 := bstep (se 1 (by rfl) ⟨1084091, by rfl⟩ : syracuseStep 1445455 = 2168183) B2168183
theorem B2887265 : Blo 1140634 2887265 := bstep (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) B2165449
theorem B8687249 : Blo 1140634 8687249 := bstep (se 2 (by rfl) ⟨3257718, by rfl⟩ : syracuseStep 8687249 = 6515437) B6515437
theorem B8228573 : Blo 1140634 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B2166907 : Blo 1140634 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B2166983 : Blo 1140634 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B2167393 : Blo 1140634 2167393 := bstep (se 2 (by rfl) ⟨812772, by rfl⟩ : syracuseStep 2167393 = 1625545) B1625545
theorem B1446599 : Blo 1140634 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B1446751 : Blo 1140634 1446751 := bstep (se 1 (by rfl) ⟨1085063, by rfl⟩ : syracuseStep 1446751 = 2170127) B2170127
theorem B2167735 : Blo 1140634 2167735 := bstep (se 1 (by rfl) ⟨1625801, by rfl⟩ : syracuseStep 2167735 = 3251603) B3251603
theorem B2888723 : Blo 1140634 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B8688707 : Blo 1140634 8688707 := bstep (se 1 (by rfl) ⟨6516530, by rfl⟩ : syracuseStep 8688707 = 13033061) B13033061
theorem B4396349 : Blo 1140634 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B2168137 : Blo 1140634 2168137 := bstep (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) B1626103
theorem B1283503 : Blo 1140634 1283503 := bstep (se 1 (by rfl) ⟨962627, by rfl⟩ : syracuseStep 1283503 = 1925255) B1925255
theorem B2889179 : Blo 1140634 2889179 := bstep (se 1 (by rfl) ⟨2166884, by rfl⟩ : syracuseStep 2889179 = 4333769) B4333769
theorem B4167379 : Blo 1140634 4167379 := bstep (se 1 (by rfl) ⟨3125534, by rfl⟩ : syracuseStep 4167379 = 6251069) B6251069
theorem B1283935 : Blo 1140634 1283935 := bstep (se 1 (by rfl) ⟨962951, by rfl⟩ : syracuseStep 1283935 = 1925903) B1925903
theorem B8689679 : Blo 1140634 8689679 := bstep (se 1 (by rfl) ⟨6517259, by rfl⟩ : syracuseStep 8689679 = 13034519) B13034519
theorem B2168851 : Blo 1140634 2168851 := bstep (se 1 (by rfl) ⟨1626638, by rfl⟩ : syracuseStep 2168851 = 3253277) B3253277
theorem B7313465 : Blo 1140634 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B2037857 : Blo 1140634 2037857 := bstep (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) B1528393
theorem B1284295 : Blo 1140634 1284295 := bstep (se 1 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 1284295 = 1926443) B1926443
theorem B2169193 : Blo 1140634 2169193 := bstep (se 2 (by rfl) ⟨813447, by rfl⟩ : syracuseStep 2169193 = 1626895) B1626895
theorem B4888937 : Blo 1140634 4888937 := bstep (se 2 (by rfl) ⟨1833351, by rfl⟩ : syracuseStep 4888937 = 3666703) B3666703
theorem B2890363 : Blo 1140634 2890363 := bstep (se 1 (by rfl) ⟨2167772, by rfl⟩ : syracuseStep 2890363 = 4335545) B4335545
theorem B3480187 : Blo 1140634 3480187 := bstep (se 1 (by rfl) ⟨2610140, by rfl⟩ : syracuseStep 3480187 = 5220281) B5220281
theorem B29301425 : Blo 1140634 29301425 := bstep (se 2 (by rfl) ⟨10988034, by rfl⟩ : syracuseStep 29301425 = 21976069) B21976069
theorem B1710953 : Blo 1140634 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B1711031 : Blo 1140634 1711031 := bstep (se 1 (by rfl) ⟨1283273, by rfl⟩ : syracuseStep 1711031 = 2566547) B2566547
theorem B1711067 : Blo 1140634 1711067 := bstep (se 1 (by rfl) ⟨1283300, by rfl⟩ : syracuseStep 1711067 = 2566601) B2566601
theorem B1285159 : Blo 1140634 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B5774489 : Blo 1140634 5774489 := bstep (se 2 (by rfl) ⟨2165433, by rfl⟩ : syracuseStep 5774489 = 4330867) B4330867
theorem B4627651 : Blo 1140634 4627651 := bstep (se 1 (by rfl) ⟨3470738, by rfl⟩ : syracuseStep 4627651 = 6941477) B6941477
theorem B4332811 : Blo 1140634 4332811 := bstep (se 1 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 4332811 = 6499217) B6499217
theorem B1711535 : Blo 1140634 1711535 := bstep (se 1 (by rfl) ⟨1283651, by rfl⟩ : syracuseStep 1711535 = 2567303) B2567303
theorem B7806451 : Blo 1140634 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B1711625 : Blo 1140634 1711625 := bstep (se 2 (by rfl) ⟨641859, by rfl⟩ : syracuseStep 1711625 = 1283719) B1283719
theorem B1711655 : Blo 1140634 1711655 := bstep (se 1 (by rfl) ⟨1283741, by rfl⟩ : syracuseStep 1711655 = 2567483) B2567483
theorem B6954535 : Blo 1140634 6954535 := bstep (se 1 (by rfl) ⟨5215901, by rfl⟩ : syracuseStep 6954535 = 10431803) B10431803
theorem B4333115 : Blo 1140634 4333115 := bstep (se 1 (by rfl) ⟨3249836, by rfl⟩ : syracuseStep 4333115 = 6499673) B6499673
theorem B1711739 : Blo 1140634 1711739 := bstep (se 1 (by rfl) ⟨1283804, by rfl⟩ : syracuseStep 1711739 = 2567609) B2567609
theorem B2170567 : Blo 1140634 2170567 := bstep (se 1 (by rfl) ⟨1627925, by rfl⟩ : syracuseStep 2170567 = 3255851) B3255851
theorem B1711865 : Blo 1140634 1711865 := bstep (se 2 (by rfl) ⟨641949, by rfl⟩ : syracuseStep 1711865 = 1283899) B1283899
theorem B7806779 : Blo 1140634 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B1711967 : Blo 1140634 1711967 := bstep (se 1 (by rfl) ⟨1283975, by rfl⟩ : syracuseStep 1711967 = 2567951) B2567951
theorem B1711979 : Blo 1140634 1711979 := bstep (se 1 (by rfl) ⟨1283984, by rfl⟩ : syracuseStep 1711979 = 2567969) B2567969
theorem B1712207 : Blo 1140634 1712207 := bstep (se 1 (by rfl) ⟨1284155, by rfl⟩ : syracuseStep 1712207 = 2568311) B2568311
theorem B9052249 : Blo 1140634 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B1712327 : Blo 1140634 1712327 := bstep (se 1 (by rfl) ⟨1284245, by rfl⟩ : syracuseStep 1712327 = 2568491) B2568491
theorem B9281765 : Blo 1140634 9281765 := bstep (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) B1740331
theorem B1712489 : Blo 1140634 1712489 := bstep (se 2 (by rfl) ⟨642183, by rfl⟩ : syracuseStep 1712489 = 1284367) B1284367
theorem B1712567 : Blo 1140634 1712567 := bstep (se 1 (by rfl) ⟨1284425, by rfl⟩ : syracuseStep 1712567 = 2568851) B2568851
theorem B1712603 : Blo 1140634 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B1286779 : Blo 1140634 1286779 := bstep (se 1 (by rfl) ⟨965084, by rfl⟩ : syracuseStep 1286779 = 1930169) B1930169
theorem B8233645 : Blo 1140634 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B4334269 : Blo 1140634 4334269 := bstep (se 3 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 4334269 = 1625351) B1625351
theorem B3252935 : Blo 1140634 3252935 := bstep (se 1 (by rfl) ⟨2439701, by rfl⟩ : syracuseStep 3252935 = 4879403) B4879403
theorem B1713071 : Blo 1140634 1713071 := bstep (se 1 (by rfl) ⟨1284803, by rfl⟩ : syracuseStep 1713071 = 2569607) B2569607
theorem B1713161 : Blo 1140634 1713161 := bstep (se 2 (by rfl) ⟨642435, by rfl⟩ : syracuseStep 1713161 = 1284871) B1284871
theorem B1713191 : Blo 1140634 1713191 := bstep (se 1 (by rfl) ⟨1284893, by rfl⟩ : syracuseStep 1713191 = 2569787) B2569787
theorem B1287247 : Blo 1140634 1287247 := bstep (se 1 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 1287247 = 1930871) B1930871
theorem B1713275 : Blo 1140634 1713275 := bstep (se 1 (by rfl) ⟨1284956, by rfl⟩ : syracuseStep 1713275 = 2569913) B2569913
theorem B1713401 : Blo 1140634 1713401 := bstep (se 2 (by rfl) ⟨642525, by rfl⟩ : syracuseStep 1713401 = 1285051) B1285051
theorem B1713503 : Blo 1140634 1713503 := bstep (se 1 (by rfl) ⟨1285127, by rfl⟩ : syracuseStep 1713503 = 2570255) B2570255
theorem B1713515 : Blo 1140634 1713515 := bstep (se 1 (by rfl) ⟨1285136, by rfl⟩ : syracuseStep 1713515 = 2570273) B2570273
theorem B1287643 : Blo 1140634 1287643 := bstep (se 1 (by rfl) ⟨965732, by rfl⟩ : syracuseStep 1287643 = 1931465) B1931465
theorem B1713743 : Blo 1140634 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B4335227 : Blo 1140634 4335227 := bstep (se 1 (by rfl) ⟨3251420, by rfl⟩ : syracuseStep 4335227 = 6502841) B6502841
theorem B1713863 : Blo 1140634 1713863 := bstep (se 1 (by rfl) ⟨1285397, by rfl⟩ : syracuseStep 1713863 = 2570795) B2570795
theorem B1714025 : Blo 1140634 1714025 := bstep (se 2 (by rfl) ⟨642759, by rfl⟩ : syracuseStep 1714025 = 1285519) B1285519
theorem B2172815 : Blo 1140634 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B1714103 : Blo 1140634 1714103 := bstep (se 1 (by rfl) ⟨1285577, by rfl⟩ : syracuseStep 1714103 = 2571155) B2571155
theorem B1714139 : Blo 1140634 1714139 := bstep (se 1 (by rfl) ⟨1285604, by rfl⟩ : syracuseStep 1714139 = 2571209) B2571209
theorem B3254519 : Blo 1140634 3254519 := bstep (se 1 (by rfl) ⟨2440889, by rfl⟩ : syracuseStep 3254519 = 4881779) B4881779
theorem B4336001 : Blo 1140634 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B1714607 : Blo 1140634 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B2566619 : Blo 1140634 2566619 := bstep (se 1 (by rfl) ⟨1924964, by rfl⟩ : syracuseStep 2566619 = 3849929) B3849929
theorem B1714697 : Blo 1140634 1714697 := bstep (se 2 (by rfl) ⟨643011, by rfl⟩ : syracuseStep 1714697 = 1286023) B1286023
theorem B1714727 : Blo 1140634 1714727 := bstep (se 1 (by rfl) ⟨1286045, by rfl⟩ : syracuseStep 1714727 = 2572091) B2572091
theorem B1714811 : Blo 1140634 1714811 := bstep (se 1 (by rfl) ⟨1286108, by rfl⟩ : syracuseStep 1714811 = 2572217) B2572217
theorem B1714937 : Blo 1140634 1714937 := bstep (se 2 (by rfl) ⟨643101, by rfl⟩ : syracuseStep 1714937 = 1286203) B1286203
theorem B4631363 : Blo 1140634 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B1715039 : Blo 1140634 1715039 := bstep (se 1 (by rfl) ⟨1286279, by rfl⟩ : syracuseStep 1715039 = 2572559) B2572559
theorem B2894687 : Blo 1140634 2894687 := bstep (se 1 (by rfl) ⟨2171015, by rfl⟩ : syracuseStep 2894687 = 4342031) B4342031
theorem B1715051 : Blo 1140634 1715051 := bstep (se 1 (by rfl) ⟨1286288, by rfl⟩ : syracuseStep 1715051 = 2572577) B2572577
theorem B2567087 : Blo 1140634 2567087 := bstep (se 1 (by rfl) ⟨1925315, by rfl⟩ : syracuseStep 2567087 = 3850631) B3850631
theorem B5483447 : Blo 1140634 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B15641527 : Blo 1140634 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B1715279 : Blo 1140634 1715279 := bstep (se 1 (by rfl) ⟨1286459, by rfl⟩ : syracuseStep 1715279 = 2572919) B2572919
theorem B2567339 : Blo 1140634 2567339 := bstep (se 1 (by rfl) ⟨1925504, by rfl⟩ : syracuseStep 2567339 = 3851009) B3851009
theorem B5942443 : Blo 1140634 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B1715399 : Blo 1140634 1715399 := bstep (se 1 (by rfl) ⟨1286549, by rfl⟩ : syracuseStep 1715399 = 2573099) B2573099
theorem B1715561 : Blo 1140634 1715561 := bstep (se 2 (by rfl) ⟨643335, by rfl⟩ : syracuseStep 1715561 = 1286671) B1286671
theorem B1715639 : Blo 1140634 1715639 := bstep (se 1 (by rfl) ⟨1286729, by rfl⟩ : syracuseStep 1715639 = 2573459) B2573459
theorem B1715675 : Blo 1140634 1715675 := bstep (se 1 (by rfl) ⟨1286756, by rfl⟩ : syracuseStep 1715675 = 2573513) B2573513
theorem B2895385 : Blo 1140634 2895385 := bstep (se 2 (by rfl) ⟨1085769, by rfl⟩ : syracuseStep 2895385 = 2171539) B2171539
theorem B4337185 : Blo 1140634 4337185 := bstep (se 2 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 4337185 = 3252889) B3252889
theorem B12365435 : Blo 1140634 12365435 := bstep (se 1 (by rfl) ⟨9274076, by rfl⟩ : syracuseStep 12365435 = 18548153) B18548153
theorem B2567879 : Blo 1140634 2567879 := bstep (se 1 (by rfl) ⟨1925909, by rfl⟩ : syracuseStep 2567879 = 3851819) B3851819
theorem B2895689 : Blo 1140634 2895689 := bstep (se 2 (by rfl) ⟨1085883, by rfl⟩ : syracuseStep 2895689 = 2171767) B2171767
theorem B3256159 : Blo 1140634 3256159 := bstep (se 1 (by rfl) ⟨2442119, by rfl⟩ : syracuseStep 3256159 = 4884239) B4884239
theorem B1716143 : Blo 1140634 1716143 := bstep (se 1 (by rfl) ⟨1287107, by rfl⟩ : syracuseStep 1716143 = 2574215) B2574215
theorem B16461755 : Blo 1140634 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B4337671 : Blo 1140634 4337671 := bstep (se 1 (by rfl) ⟨3253253, by rfl⟩ : syracuseStep 4337671 = 6506507) B6506507
theorem B1716233 : Blo 1140634 1716233 := bstep (se 2 (by rfl) ⟨643587, by rfl⟩ : syracuseStep 1716233 = 1287175) B1287175
theorem B1716263 : Blo 1140634 1716263 := bstep (se 1 (by rfl) ⟨1287197, by rfl⟩ : syracuseStep 1716263 = 2574395) B2574395
theorem B2437199 : Blo 1140634 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B1716347 : Blo 1140634 1716347 := bstep (se 1 (by rfl) ⟨1287260, by rfl⟩ : syracuseStep 1716347 = 2574521) B2574521
theorem B8335523 : Blo 1140634 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B1716473 : Blo 1140634 1716473 := bstep (se 2 (by rfl) ⟨643677, by rfl⟩ : syracuseStep 1716473 = 1287355) B1287355
theorem B1716575 : Blo 1140634 1716575 := bstep (se 1 (by rfl) ⟨1287431, by rfl⟩ : syracuseStep 1716575 = 2574863) B2574863
theorem B1716587 : Blo 1140634 1716587 := bstep (se 1 (by rfl) ⟨1287440, by rfl⟩ : syracuseStep 1716587 = 2574881) B2574881
theorem B3912065 : Blo 1140634 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B4338157 : Blo 1140634 4338157 := bstep (se 3 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 4338157 = 1626809) B1626809
theorem B27832841 : Blo 1140634 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B2568743 : Blo 1140634 2568743 := bstep (se 1 (by rfl) ⟨1926557, by rfl⟩ : syracuseStep 2568743 = 3853115) B3853115
theorem B1716815 : Blo 1140634 1716815 := bstep (se 1 (by rfl) ⟨1287611, by rfl⟩ : syracuseStep 1716815 = 2575223) B2575223
theorem B1716935 : Blo 1140634 1716935 := bstep (se 1 (by rfl) ⟨1287701, by rfl⟩ : syracuseStep 1716935 = 2575403) B2575403
theorem B3257081 : Blo 1140634 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B3093241 : Blo 1140634 3093241 := bstep (se 2 (by rfl) ⟨1159965, by rfl⟩ : syracuseStep 3093241 = 2319931) B2319931
theorem B4338461 : Blo 1140634 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B16495433 : Blo 1140634 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B2569067 : Blo 1140634 2569067 := bstep (se 1 (by rfl) ⟨1926800, by rfl⟩ : syracuseStep 2569067 = 3853601) B3853601
theorem B2569121 : Blo 1140634 2569121 := bstep (se 2 (by rfl) ⟨963420, by rfl⟩ : syracuseStep 2569121 = 1926841) B1926841
theorem B3257263 : Blo 1140634 3257263 := bstep (se 1 (by rfl) ⟨2442947, by rfl⟩ : syracuseStep 3257263 = 4885895) B4885895
theorem B2896823 : Blo 1140634 2896823 := bstep (se 1 (by rfl) ⟨2172617, by rfl⟩ : syracuseStep 2896823 = 4345235) B4345235
theorem B10433555 : Blo 1140634 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B74036375 : Blo 1140634 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B2569463 : Blo 1140634 2569463 := bstep (se 1 (by rfl) ⟨1927097, by rfl⟩ : syracuseStep 2569463 = 3854195) B3854195
theorem B15840731 : Blo 1140634 15840731 := bstep (se 1 (by rfl) ⟨11880548, by rfl⟩ : syracuseStep 15840731 = 23761097) B23761097
theorem B16463371 : Blo 1140634 16463371 := bstep (se 1 (by rfl) ⟨12347528, by rfl⟩ : syracuseStep 16463371 = 24695057) B24695057
theorem B5781131 : Blo 1140634 5781131 := bstep (se 1 (by rfl) ⟨4335848, by rfl⟩ : syracuseStep 5781131 = 8671697) B8671697
theorem B5486329 : Blo 1140634 5486329 := bstep (se 2 (by rfl) ⟨2057373, by rfl⟩ : syracuseStep 5486329 = 4114747) B4114747
theorem B2570057 : Blo 1140634 2570057 := bstep (se 2 (by rfl) ⟨963771, by rfl⟩ : syracuseStep 2570057 = 1927543) B1927543
theorem B37140569 : Blo 1140634 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B3258539 : Blo 1140634 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B17611057 : Blo 1140634 17611057 := bstep (se 2 (by rfl) ⟨6604146, by rfl⟩ : syracuseStep 17611057 = 13208293) B13208293
theorem B3258767 : Blo 1140634 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B2570849 : Blo 1140634 2570849 := bstep (se 2 (by rfl) ⟨964068, by rfl⟩ : syracuseStep 2570849 = 1928137) B1928137
theorem B55589561 : Blo 1140634 55589561 := bstep (se 2 (by rfl) ⟨20846085, by rfl⟩ : syracuseStep 55589561 = 41692171) B41692171
theorem B5487389 : Blo 1140634 5487389 := bstep (se 3 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 5487389 = 2057771) B2057771
theorem B4340587 : Blo 1140634 4340587 := bstep (se 1 (by rfl) ⟨3255440, by rfl⟩ : syracuseStep 4340587 = 6510881) B6510881
theorem B2571191 : Blo 1140634 2571191 := bstep (se 1 (by rfl) ⟨1928393, by rfl⟩ : syracuseStep 2571191 = 3856787) B3856787
theorem B7322795 : Blo 1140634 7322795 := bstep (se 1 (by rfl) ⟨5492096, by rfl⟩ : syracuseStep 7322795 = 10984193) B10984193
theorem B2571785 : Blo 1140634 2571785 := bstep (se 2 (by rfl) ⟨964419, by rfl⟩ : syracuseStep 2571785 = 1928839) B1928839
theorem B1883657 : Blo 1140634 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B3849767 : Blo 1140634 3849767 := bstep (se 1 (by rfl) ⟨2887325, by rfl⟩ : syracuseStep 3849767 = 5774651) B5774651
theorem B1392167 : Blo 1140634 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B3849875 : Blo 1140634 3849875 := bstep (se 1 (by rfl) ⟨2887406, by rfl⟩ : syracuseStep 3849875 = 5774813) B5774813
theorem B2572127 : Blo 1140634 2572127 := bstep (se 1 (by rfl) ⟨1929095, by rfl⟩ : syracuseStep 2572127 = 3858191) B3858191
theorem B3850091 : Blo 1140634 3850091 := bstep (se 1 (by rfl) ⟨2887568, by rfl⟩ : syracuseStep 3850091 = 5775137) B5775137
theorem B3850145 : Blo 1140634 3850145 := bstep (se 2 (by rfl) ⟨1443804, by rfl⟩ : syracuseStep 3850145 = 2887609) B2887609
theorem B18530315 : Blo 1140634 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B2572307 : Blo 1140634 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B4112441 : Blo 1140634 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B2572649 : Blo 1140634 2572649 := bstep (se 2 (by rfl) ⟨964743, by rfl⟩ : syracuseStep 2572649 = 1929487) B1929487
theorem B3850739 : Blo 1140634 3850739 := bstep (se 1 (by rfl) ⟨2888054, by rfl⟩ : syracuseStep 3850739 = 5776109) B5776109
theorem B2933371 : Blo 1140634 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B59294339 : Blo 1140634 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B8241949 : Blo 1140634 8241949 := bstep (se 3 (by rfl) ⟨1545365, by rfl⟩ : syracuseStep 8241949 = 3090731) B3090731
theorem B2442145 : Blo 1140634 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B2573243 : Blo 1140634 2573243 := bstep (se 1 (by rfl) ⟨1929932, by rfl⟩ : syracuseStep 2573243 = 3859865) B3859865
theorem B3851279 : Blo 1140634 3851279 := bstep (se 1 (by rfl) ⟨2888459, by rfl⟩ : syracuseStep 3851279 = 5776919) B5776919
theorem B2573369 : Blo 1140634 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B2442487 : Blo 1140634 2442487 := bstep (se 1 (by rfl) ⟨1831865, by rfl⟩ : syracuseStep 2442487 = 3663731) B3663731
theorem B4638077 : Blo 1140634 4638077 := bstep (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) B1739279
theorem B2573711 : Blo 1140634 2573711 := bstep (se 1 (by rfl) ⟨1930283, by rfl⟩ : syracuseStep 2573711 = 3860567) B3860567
theorem B4343321 : Blo 1140634 4343321 := bstep (se 2 (by rfl) ⟨1628745, by rfl⟩ : syracuseStep 4343321 = 3257491) B3257491
theorem B3851873 : Blo 1140634 3851873 := bstep (se 2 (by rfl) ⟨1444452, by rfl⟩ : syracuseStep 3851873 = 2888905) B2888905
theorem B4114055 : Blo 1140634 4114055 := bstep (se 1 (by rfl) ⟨3085541, by rfl⟩ : syracuseStep 4114055 = 6171083) B6171083
theorem B2574035 : Blo 1140634 2574035 := bstep (se 1 (by rfl) ⟨1930526, by rfl⟩ : syracuseStep 2574035 = 3861053) B3861053
theorem B5785505 : Blo 1140634 5785505 := bstep (se 2 (by rfl) ⟨2169564, by rfl⟩ : syracuseStep 5785505 = 4339129) B4339129
theorem B9258961 : Blo 1140634 9258961 := bstep (se 2 (by rfl) ⟨3472110, by rfl⟩ : syracuseStep 9258961 = 6944221) B6944221
theorem B18795037 : Blo 1140634 18795037 := bstep (se 3 (by rfl) ⟨3524069, by rfl⟩ : syracuseStep 18795037 = 7048139) B7048139
theorem B2574971 : Blo 1140634 2574971 := bstep (se 1 (by rfl) ⟨1931228, by rfl⟩ : syracuseStep 2574971 = 3862457) B3862457
theorem B2575097 : Blo 1140634 2575097 := bstep (se 2 (by rfl) ⟨965661, by rfl⟩ : syracuseStep 2575097 = 1931323) B1931323
theorem B3656477 : Blo 1140634 3656477 := bstep (se 3 (by rfl) ⟨685589, by rfl⟩ : syracuseStep 3656477 = 1371179) B1371179
theorem B36162449 : Blo 1140634 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B1952695 : Blo 1140634 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B2575367 : Blo 1140634 2575367 := bstep (se 1 (by rfl) ⟨1931525, by rfl⟩ : syracuseStep 2575367 = 3863051) B3863051
theorem B3853331 : Blo 1140634 3853331 := bstep (se 1 (by rfl) ⟨2889998, by rfl⟩ : syracuseStep 3853331 = 5779997) B5779997
theorem B4344947 : Blo 1140634 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B5491907 : Blo 1140634 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B7818443 : Blo 1140634 7818443 := bstep (se 1 (by rfl) ⟨5863832, by rfl⟩ : syracuseStep 7818443 = 11727665) B11727665
theorem B3853655 : Blo 1140634 3853655 := bstep (se 1 (by rfl) ⟨2890241, by rfl⟩ : syracuseStep 3853655 = 5780483) B5780483
theorem B29314547 : Blo 1140634 29314547 := bstep (se 1 (by rfl) ⟨21985910, by rfl⟩ : syracuseStep 29314547 = 43971821) B43971821
theorem B10407865 : Blo 1140634 10407865 := bstep (se 2 (by rfl) ⟨3902949, by rfl⟩ : syracuseStep 10407865 = 7805899) B7805899
theorem B5951495 : Blo 1140634 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B3854735 : Blo 1140634 3854735 := bstep (se 1 (by rfl) ⟨2891051, by rfl⟩ : syracuseStep 3854735 = 5782103) B5782103
theorem B24728273 : Blo 1140634 24728273 := bstep (se 2 (by rfl) ⟨9273102, by rfl⟩ : syracuseStep 24728273 = 18546205) B18546205
theorem B3855059 : Blo 1140634 3855059 := bstep (se 1 (by rfl) ⟨2891294, by rfl⟩ : syracuseStep 3855059 = 5782589) B5782589
theorem B8672183 : Blo 1140634 8672183 := bstep (se 1 (by rfl) ⟨6504137, by rfl⟩ : syracuseStep 8672183 = 13008275) B13008275
theorem B7328819 : Blo 1140634 7328819 := bstep (se 1 (by rfl) ⟨5496614, by rfl⟩ : syracuseStep 7328819 = 10993229) B10993229
theorem B4117661 : Blo 1140634 4117661 := bstep (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) B1544123
theorem B3298475 : Blo 1140634 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B10966589 : Blo 1140634 10966589 := bstep (se 3 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 10966589 = 4112471) B4112471
theorem B35149463 : Blo 1140634 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B16307905 : Blo 1140634 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B2741975 : Blo 1140634 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B16897901 : Blo 1140634 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B3856247 : Blo 1140634 3856247 := bstep (se 1 (by rfl) ⟨2892185, by rfl⟩ : syracuseStep 3856247 = 5784371) B5784371
theorem B3856463 : Blo 1140634 3856463 := bstep (se 1 (by rfl) ⟨2892347, by rfl⟩ : syracuseStep 3856463 = 5784695) B5784695
theorem B8673641 : Blo 1140634 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B3856841 : Blo 1140634 3856841 := bstep (se 2 (by rfl) ⟨1446315, by rfl⟩ : syracuseStep 3856841 = 2892631) B2892631
theorem B2316809 : Blo 1140634 2316809 := bstep (se 2 (by rfl) ⟨868803, by rfl⟩ : syracuseStep 2316809 = 1737607) B1737607
theorem B71293505 : Blo 1140634 71293505 := bstep (se 2 (by rfl) ⟨26735064, by rfl⟩ : syracuseStep 71293505 = 53470129) B53470129
theorem B10967737 : Blo 1140634 10967737 := bstep (se 2 (by rfl) ⟨4112901, by rfl⟩ : syracuseStep 10967737 = 8225803) B8225803
theorem B3857111 : Blo 1140634 3857111 := bstep (se 1 (by rfl) ⟨2892833, by rfl⟩ : syracuseStep 3857111 = 5785667) B5785667
theorem B8248067 : Blo 1140634 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B3857327 : Blo 1140634 3857327 := bstep (se 1 (by rfl) ⟨2892995, by rfl⟩ : syracuseStep 3857327 = 5785991) B5785991
theorem B3660731 : Blo 1140634 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B6511589 : Blo 1140634 6511589 := bstep (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) B1220923
theorem B9886967 : Blo 1140634 9886967 := bstep (se 1 (by rfl) ⟨7415225, by rfl⟩ : syracuseStep 9886967 = 14830451) B14830451
theorem B4873715 : Blo 1140634 4873715 := bstep (se 1 (by rfl) ⟨3655286, by rfl⟩ : syracuseStep 4873715 = 7310573) B7310573
theorem B8806087 : Blo 1140634 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B9756449 : Blo 1140634 9756449 := bstep (se 2 (by rfl) ⟨3658668, by rfl⟩ : syracuseStep 9756449 = 7317337) B7317337
theorem B4120429 : Blo 1140634 4120429 := bstep (se 3 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 4120429 = 1545161) B1545161
theorem B1925039 : Blo 1140634 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B31252493 : Blo 1140634 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B2318375 : Blo 1140634 2318375 := bstep (se 1 (by rfl) ⟨1738781, by rfl⟩ : syracuseStep 2318375 = 3477563) B3477563
theorem B15622307 : Blo 1140634 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B8675585 : Blo 1140634 8675585 := bstep (se 2 (by rfl) ⟨3253344, by rfl⟩ : syracuseStep 8675585 = 6506689) B6506689
theorem B4120919 : Blo 1140634 4120919 := bstep (se 1 (by rfl) ⟨3090689, by rfl⟩ : syracuseStep 4120919 = 6181379) B6181379
theorem B1925471 : Blo 1140634 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B2744819 : Blo 1140634 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B1926031 : Blo 1140634 1926031 := bstep (se 1 (by rfl) ⟨1444523, by rfl⟩ : syracuseStep 1926031 = 2889047) B2889047
theorem B7332943 : Blo 1140634 7332943 := bstep (se 1 (by rfl) ⟨5499707, by rfl⟩ : syracuseStep 7332943 = 10999415) B10999415
theorem B3859703 : Blo 1140634 3859703 := bstep (se 1 (by rfl) ⟨2894777, by rfl⟩ : syracuseStep 3859703 = 5789555) B5789555
theorem B3663191 : Blo 1140634 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B1828315 : Blo 1140634 1828315 := bstep (se 1 (by rfl) ⟨1371236, by rfl⟩ : syracuseStep 1828315 = 2742473) B2742473
theorem B4875815 : Blo 1140634 4875815 := bstep (se 1 (by rfl) ⟨3656861, by rfl⟩ : syracuseStep 4875815 = 7313723) B7313723
theorem B2745895 : Blo 1140634 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B1926713 : Blo 1140634 1926713 := bstep (se 2 (by rfl) ⟨722517, by rfl⟩ : syracuseStep 1926713 = 1445035) B1445035
theorem B3860027 : Blo 1140634 3860027 := bstep (se 1 (by rfl) ⟨2895020, by rfl⟩ : syracuseStep 3860027 = 5790041) B5790041
theorem B2778839 : Blo 1140634 2778839 := bstep (se 1 (by rfl) ⟨2084129, by rfl⟩ : syracuseStep 2778839 = 4168259) B4168259
theorem B166750001 : Blo 1140634 166750001 := bstep (se 2 (by rfl) ⟨62531250, by rfl⟩ : syracuseStep 166750001 = 125062501) B125062501
theorem B3860297 : Blo 1140634 3860297 := bstep (se 2 (by rfl) ⟨1447611, by rfl⟩ : syracuseStep 3860297 = 2895223) B2895223
theorem B1140655 : Blo 1140634 1140655 := bstep (se 1 (by rfl) ⟨855491, by rfl⟩ : syracuseStep 1140655 = 1710983) B1710983
theorem B1140679 : Blo 1140634 1140679 := bstep (se 1 (by rfl) ⟨855509, by rfl⟩ : syracuseStep 1140679 = 1711019) B1711019
theorem B10971085 : Blo 1140634 10971085 := bstep (se 3 (by rfl) ⟨2057078, by rfl⟩ : syracuseStep 10971085 = 4114157) B4114157
theorem B1140699 : Blo 1140634 1140699 := bstep (se 1 (by rfl) ⟨855524, by rfl⟩ : syracuseStep 1140699 = 1711049) B1711049
theorem B1140775 : Blo 1140634 1140775 := bstep (se 1 (by rfl) ⟨855581, by rfl⟩ : syracuseStep 1140775 = 1711163) B1711163
theorem B1140815 : Blo 1140634 1140815 := bstep (se 1 (by rfl) ⟨855611, by rfl⟩ : syracuseStep 1140815 = 1711223) B1711223
theorem B1140831 : Blo 1140634 1140831 := bstep (se 1 (by rfl) ⟨855623, by rfl⟩ : syracuseStep 1140831 = 1711247) B1711247
theorem B1140859 : Blo 1140634 1140859 := bstep (se 1 (by rfl) ⟨855644, by rfl⟩ : syracuseStep 1140859 = 1711289) B1711289
theorem B1140911 : Blo 1140634 1140911 := bstep (se 1 (by rfl) ⟨855683, by rfl⟩ : syracuseStep 1140911 = 1711367) B1711367
theorem B1140935 : Blo 1140634 1140935 := bstep (se 1 (by rfl) ⟨855701, by rfl⟩ : syracuseStep 1140935 = 1711403) B1711403
theorem B1140955 : Blo 1140634 1140955 := bstep (se 1 (by rfl) ⟨855716, by rfl⟩ : syracuseStep 1140955 = 1711433) B1711433
theorem B1927415 : Blo 1140634 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B1141031 : Blo 1140634 1141031 := bstep (se 1 (by rfl) ⟨855773, by rfl⟩ : syracuseStep 1141031 = 1711547) B1711547
theorem B1141071 : Blo 1140634 1141071 := bstep (se 1 (by rfl) ⟨855803, by rfl⟩ : syracuseStep 1141071 = 1711607) B1711607
theorem B1141087 : Blo 1140634 1141087 := bstep (se 1 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 1141087 = 1711631) B1711631
theorem B1141115 : Blo 1140634 1141115 := bstep (se 1 (by rfl) ⟨855836, by rfl⟩ : syracuseStep 1141115 = 1711673) B1711673
theorem B1141167 : Blo 1140634 1141167 := bstep (se 1 (by rfl) ⟨855875, by rfl⟩ : syracuseStep 1141167 = 1711751) B1711751
theorem B1141191 : Blo 1140634 1141191 := bstep (se 1 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 1141191 = 1711787) B1711787
theorem B1141211 : Blo 1140634 1141211 := bstep (se 1 (by rfl) ⟨855908, by rfl⟩ : syracuseStep 1141211 = 1711817) B1711817
theorem B4123169 : Blo 1140634 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B1141287 : Blo 1140634 1141287 := bstep (se 1 (by rfl) ⟨855965, by rfl⟩ : syracuseStep 1141287 = 1711931) B1711931
theorem B1141327 : Blo 1140634 1141327 := bstep (se 1 (by rfl) ⟨855995, by rfl⟩ : syracuseStep 1141327 = 1711991) B1711991
theorem B1927759 : Blo 1140634 1927759 := bstep (se 1 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 1927759 = 2891639) B2891639
theorem B1141343 : Blo 1140634 1141343 := bstep (se 1 (by rfl) ⟨856007, by rfl⟩ : syracuseStep 1141343 = 1712015) B1712015
theorem B1141371 : Blo 1140634 1141371 := bstep (se 1 (by rfl) ⟨856028, by rfl⟩ : syracuseStep 1141371 = 1712057) B1712057
theorem B1141423 : Blo 1140634 1141423 := bstep (se 1 (by rfl) ⟨856067, by rfl⟩ : syracuseStep 1141423 = 1712135) B1712135
theorem B1141447 : Blo 1140634 1141447 := bstep (se 1 (by rfl) ⟨856085, by rfl⟩ : syracuseStep 1141447 = 1712171) B1712171
theorem B1141467 : Blo 1140634 1141467 := bstep (se 1 (by rfl) ⟨856100, by rfl⟩ : syracuseStep 1141467 = 1712201) B1712201
theorem B1829623 : Blo 1140634 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B1141543 : Blo 1140634 1141543 := bstep (se 1 (by rfl) ⟨856157, by rfl⟩ : syracuseStep 1141543 = 1712315) B1712315
theorem B7039817 : Blo 1140634 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B1928009 : Blo 1140634 1928009 := bstep (se 2 (by rfl) ⟨723003, by rfl⟩ : syracuseStep 1928009 = 1446007) B1446007
theorem B1141583 : Blo 1140634 1141583 := bstep (se 1 (by rfl) ⟨856187, by rfl⟩ : syracuseStep 1141583 = 1712375) B1712375
theorem B1141599 : Blo 1140634 1141599 := bstep (se 1 (by rfl) ⟨856199, by rfl⟩ : syracuseStep 1141599 = 1712399) B1712399
theorem B1141627 : Blo 1140634 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B1141679 : Blo 1140634 1141679 := bstep (se 1 (by rfl) ⟨856259, by rfl⟩ : syracuseStep 1141679 = 1712519) B1712519
theorem B2780087 : Blo 1140634 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B3861431 : Blo 1140634 3861431 := bstep (se 1 (by rfl) ⟨2896073, by rfl⟩ : syracuseStep 3861431 = 5792147) B5792147
theorem B1141703 : Blo 1140634 1141703 := bstep (se 1 (by rfl) ⟨856277, by rfl⟩ : syracuseStep 1141703 = 1712555) B1712555
theorem B1141723 : Blo 1140634 1141723 := bstep (se 1 (by rfl) ⟨856292, by rfl⟩ : syracuseStep 1141723 = 1712585) B1712585
theorem B3435527 : Blo 1140634 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B1141799 : Blo 1140634 1141799 := bstep (se 1 (by rfl) ⟨856349, by rfl⟩ : syracuseStep 1141799 = 1712699) B1712699
theorem B1141839 : Blo 1140634 1141839 := bstep (se 1 (by rfl) ⟨856379, by rfl⟩ : syracuseStep 1141839 = 1712759) B1712759
theorem B1141855 : Blo 1140634 1141855 := bstep (se 1 (by rfl) ⟨856391, by rfl⟩ : syracuseStep 1141855 = 1712783) B1712783
theorem B1141883 : Blo 1140634 1141883 := bstep (se 1 (by rfl) ⟨856412, by rfl⟩ : syracuseStep 1141883 = 1712825) B1712825
theorem B1141935 : Blo 1140634 1141935 := bstep (se 1 (by rfl) ⟨856451, by rfl⟩ : syracuseStep 1141935 = 1712903) B1712903
theorem B1141959 : Blo 1140634 1141959 := bstep (se 1 (by rfl) ⟨856469, by rfl⟩ : syracuseStep 1141959 = 1712939) B1712939
theorem B1141979 : Blo 1140634 1141979 := bstep (se 1 (by rfl) ⟨856484, by rfl⟩ : syracuseStep 1141979 = 1712969) B1712969
theorem B1928441 : Blo 1140634 1928441 := bstep (se 2 (by rfl) ⟨723165, by rfl⟩ : syracuseStep 1928441 = 1446331) B1446331
theorem B1142055 : Blo 1140634 1142055 := bstep (se 1 (by rfl) ⟨856541, by rfl⟩ : syracuseStep 1142055 = 1713083) B1713083
theorem B1142095 : Blo 1140634 1142095 := bstep (se 1 (by rfl) ⟨856571, by rfl⟩ : syracuseStep 1142095 = 1713143) B1713143
theorem B1371487 : Blo 1140634 1371487 := bstep (se 1 (by rfl) ⟨1028615, by rfl⟩ : syracuseStep 1371487 = 2057231) B2057231
theorem B1142111 : Blo 1140634 1142111 := bstep (se 1 (by rfl) ⟨856583, by rfl⟩ : syracuseStep 1142111 = 1713167) B1713167
theorem B1142139 : Blo 1140634 1142139 := bstep (se 1 (by rfl) ⟨856604, by rfl⟩ : syracuseStep 1142139 = 1713209) B1713209
theorem B2059681 : Blo 1140634 2059681 := bstep (se 2 (by rfl) ⟨772380, by rfl⟩ : syracuseStep 2059681 = 1544761) B1544761
theorem B1142191 : Blo 1140634 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B1928623 : Blo 1140634 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B1142215 : Blo 1140634 1142215 := bstep (se 1 (by rfl) ⟨856661, by rfl⟩ : syracuseStep 1142215 = 1713323) B1713323
theorem B1142235 : Blo 1140634 1142235 := bstep (se 1 (by rfl) ⟨856676, by rfl⟩ : syracuseStep 1142235 = 1713353) B1713353
theorem B2059739 : Blo 1140634 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B3665371 : Blo 1140634 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B1928711 : Blo 1140634 1928711 := bstep (se 1 (by rfl) ⟨1446533, by rfl⟩ : syracuseStep 1928711 = 2893067) B2893067
theorem B3862025 : Blo 1140634 3862025 := bstep (se 2 (by rfl) ⟨1448259, by rfl⟩ : syracuseStep 3862025 = 2896519) B2896519
theorem B1142311 : Blo 1140634 1142311 := bstep (se 1 (by rfl) ⟨856733, by rfl⟩ : syracuseStep 1142311 = 1713467) B1713467
theorem B1142351 : Blo 1140634 1142351 := bstep (se 1 (by rfl) ⟨856763, by rfl⟩ : syracuseStep 1142351 = 1713527) B1713527
theorem B1142367 : Blo 1140634 1142367 := bstep (se 1 (by rfl) ⟨856775, by rfl⟩ : syracuseStep 1142367 = 1713551) B1713551
theorem B1142395 : Blo 1140634 1142395 := bstep (se 1 (by rfl) ⟨856796, by rfl⟩ : syracuseStep 1142395 = 1713593) B1713593
theorem B1142447 : Blo 1140634 1142447 := bstep (se 1 (by rfl) ⟨856835, by rfl⟩ : syracuseStep 1142447 = 1713671) B1713671
theorem B4943549 : Blo 1140634 4943549 := bstep (se 3 (by rfl) ⟨926915, by rfl⟩ : syracuseStep 4943549 = 1853831) B1853831
theorem B9760445 : Blo 1140634 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B1142471 : Blo 1140634 1142471 := bstep (se 1 (by rfl) ⟨856853, by rfl⟩ : syracuseStep 1142471 = 1713707) B1713707
theorem B9268951 : Blo 1140634 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B1142491 : Blo 1140634 1142491 := bstep (se 1 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 1142491 = 1713737) B1713737
theorem B1142567 : Blo 1140634 1142567 := bstep (se 1 (by rfl) ⟨856925, by rfl⟩ : syracuseStep 1142567 = 1713851) B1713851
theorem B1142607 : Blo 1140634 1142607 := bstep (se 1 (by rfl) ⟨856955, by rfl⟩ : syracuseStep 1142607 = 1713911) B1713911
theorem B1142623 : Blo 1140634 1142623 := bstep (se 1 (by rfl) ⟨856967, by rfl⟩ : syracuseStep 1142623 = 1713935) B1713935
theorem B1929055 : Blo 1140634 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B1142651 : Blo 1140634 1142651 := bstep (se 1 (by rfl) ⟨856988, by rfl⟩ : syracuseStep 1142651 = 1713977) B1713977
theorem B1142703 : Blo 1140634 1142703 := bstep (se 1 (by rfl) ⟨857027, by rfl⟩ : syracuseStep 1142703 = 1714055) B1714055
theorem B1929143 : Blo 1140634 1929143 := bstep (se 1 (by rfl) ⟨1446857, by rfl⟩ : syracuseStep 1929143 = 2893715) B2893715
theorem B1142727 : Blo 1140634 1142727 := bstep (se 1 (by rfl) ⟨857045, by rfl⟩ : syracuseStep 1142727 = 1714091) B1714091
theorem B1142747 : Blo 1140634 1142747 := bstep (se 1 (by rfl) ⟨857060, by rfl⟩ : syracuseStep 1142747 = 1714121) B1714121
theorem B1142823 : Blo 1140634 1142823 := bstep (se 1 (by rfl) ⟨857117, by rfl⟩ : syracuseStep 1142823 = 1714235) B1714235
theorem B1142863 : Blo 1140634 1142863 := bstep (se 1 (by rfl) ⟨857147, by rfl⟩ : syracuseStep 1142863 = 1714295) B1714295
theorem B1142879 : Blo 1140634 1142879 := bstep (se 1 (by rfl) ⟨857159, by rfl⟩ : syracuseStep 1142879 = 1714319) B1714319
theorem B1142907 : Blo 1140634 1142907 := bstep (se 1 (by rfl) ⟨857180, by rfl⟩ : syracuseStep 1142907 = 1714361) B1714361
theorem B1142959 : Blo 1140634 1142959 := bstep (se 1 (by rfl) ⟨857219, by rfl⟩ : syracuseStep 1142959 = 1714439) B1714439
theorem B1142983 : Blo 1140634 1142983 := bstep (se 1 (by rfl) ⟨857237, by rfl⟩ : syracuseStep 1142983 = 1714475) B1714475
theorem B1143003 : Blo 1140634 1143003 := bstep (se 1 (by rfl) ⟨857252, by rfl⟩ : syracuseStep 1143003 = 1714505) B1714505
theorem B9269477 : Blo 1140634 9269477 := bstep (se 4 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 9269477 = 1738027) B1738027
theorem B1143079 : Blo 1140634 1143079 := bstep (se 1 (by rfl) ⟨857309, by rfl⟩ : syracuseStep 1143079 = 1714619) B1714619
theorem B1143119 : Blo 1140634 1143119 := bstep (se 1 (by rfl) ⟨857339, by rfl⟩ : syracuseStep 1143119 = 1714679) B1714679
theorem B1143135 : Blo 1140634 1143135 := bstep (se 1 (by rfl) ⟨857351, by rfl⟩ : syracuseStep 1143135 = 1714703) B1714703
theorem B3862889 : Blo 1140634 3862889 := bstep (se 2 (by rfl) ⟨1448583, by rfl⟩ : syracuseStep 3862889 = 2897167) B2897167
theorem B1143163 : Blo 1140634 1143163 := bstep (se 1 (by rfl) ⟨857372, by rfl⟩ : syracuseStep 1143163 = 1714745) B1714745
theorem B1143215 : Blo 1140634 1143215 := bstep (se 1 (by rfl) ⟨857411, by rfl⟩ : syracuseStep 1143215 = 1714823) B1714823
theorem B1143239 : Blo 1140634 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B1143259 : Blo 1140634 1143259 := bstep (se 1 (by rfl) ⟨857444, by rfl⟩ : syracuseStep 1143259 = 1714889) B1714889
theorem B1929737 : Blo 1140634 1929737 := bstep (se 2 (by rfl) ⟨723651, by rfl⟩ : syracuseStep 1929737 = 1447303) B1447303
theorem B8679959 : Blo 1140634 8679959 := bstep (se 1 (by rfl) ⟨6509969, by rfl⟩ : syracuseStep 8679959 = 13019939) B13019939
theorem B1143335 : Blo 1140634 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B1143375 : Blo 1140634 1143375 := bstep (se 1 (by rfl) ⟨857531, by rfl⟩ : syracuseStep 1143375 = 1715063) B1715063
theorem B1143391 : Blo 1140634 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1143419 : Blo 1140634 1143419 := bstep (se 1 (by rfl) ⟨857564, by rfl⟩ : syracuseStep 1143419 = 1715129) B1715129
theorem B1929899 : Blo 1140634 1929899 := bstep (se 1 (by rfl) ⟨1447424, by rfl⟩ : syracuseStep 1929899 = 2894849) B2894849
theorem B1143471 : Blo 1140634 1143471 := bstep (se 1 (by rfl) ⟨857603, by rfl⟩ : syracuseStep 1143471 = 1715207) B1715207
theorem B1143495 : Blo 1140634 1143495 := bstep (se 1 (by rfl) ⟨857621, by rfl⟩ : syracuseStep 1143495 = 1715243) B1715243
theorem B1143515 : Blo 1140634 1143515 := bstep (se 1 (by rfl) ⟨857636, by rfl⟩ : syracuseStep 1143515 = 1715273) B1715273
theorem B1831673 : Blo 1140634 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1143591 : Blo 1140634 1143591 := bstep (se 1 (by rfl) ⟨857693, by rfl⟩ : syracuseStep 1143591 = 1715387) B1715387
theorem B5567305 : Blo 1140634 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B1143631 : Blo 1140634 1143631 := bstep (se 1 (by rfl) ⟨857723, by rfl⟩ : syracuseStep 1143631 = 1715447) B1715447
theorem B1143647 : Blo 1140634 1143647 := bstep (se 1 (by rfl) ⟨857735, by rfl⟩ : syracuseStep 1143647 = 1715471) B1715471
theorem B1143675 : Blo 1140634 1143675 := bstep (se 1 (by rfl) ⟨857756, by rfl⟩ : syracuseStep 1143675 = 1715513) B1715513
theorem B1143727 : Blo 1140634 1143727 := bstep (se 1 (by rfl) ⟨857795, by rfl⟩ : syracuseStep 1143727 = 1715591) B1715591
theorem B1143751 : Blo 1140634 1143751 := bstep (se 1 (by rfl) ⟨857813, by rfl⟩ : syracuseStep 1143751 = 1715627) B1715627
theorem B1143771 : Blo 1140634 1143771 := bstep (se 1 (by rfl) ⟨857828, by rfl⟩ : syracuseStep 1143771 = 1715657) B1715657
theorem B1143847 : Blo 1140634 1143847 := bstep (se 1 (by rfl) ⟨857885, by rfl⟩ : syracuseStep 1143847 = 1715771) B1715771
theorem B1930297 : Blo 1140634 1930297 := bstep (se 2 (by rfl) ⟨723861, by rfl⟩ : syracuseStep 1930297 = 1447723) B1447723
theorem B10974275 : Blo 1140634 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B1143887 : Blo 1140634 1143887 := bstep (se 1 (by rfl) ⟨857915, by rfl⟩ : syracuseStep 1143887 = 1715831) B1715831
theorem B1143903 : Blo 1140634 1143903 := bstep (se 1 (by rfl) ⟨857927, by rfl⟩ : syracuseStep 1143903 = 1715855) B1715855
theorem B1143931 : Blo 1140634 1143931 := bstep (se 1 (by rfl) ⟨857948, by rfl⟩ : syracuseStep 1143931 = 1715897) B1715897
theorem B1143983 : Blo 1140634 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B1930439 : Blo 1140634 1930439 := bstep (se 1 (by rfl) ⟨1447829, by rfl⟩ : syracuseStep 1930439 = 2895659) B2895659
theorem B1144007 : Blo 1140634 1144007 := bstep (se 1 (by rfl) ⟨858005, by rfl⟩ : syracuseStep 1144007 = 1716011) B1716011
theorem B1144027 : Blo 1140634 1144027 := bstep (se 1 (by rfl) ⟨858020, by rfl⟩ : syracuseStep 1144027 = 1716041) B1716041
theorem B1144103 : Blo 1140634 1144103 := bstep (se 1 (by rfl) ⟨858077, by rfl⟩ : syracuseStep 1144103 = 1716155) B1716155
theorem B2061641 : Blo 1140634 2061641 := bstep (se 2 (by rfl) ⟨773115, by rfl⟩ : syracuseStep 2061641 = 1546231) B1546231
theorem B1144143 : Blo 1140634 1144143 := bstep (se 1 (by rfl) ⟨858107, by rfl⟩ : syracuseStep 1144143 = 1716215) B1716215
theorem B1144159 : Blo 1140634 1144159 := bstep (se 1 (by rfl) ⟨858119, by rfl⟩ : syracuseStep 1144159 = 1716239) B1716239
theorem B1930601 : Blo 1140634 1930601 := bstep (se 2 (by rfl) ⟨723975, by rfl⟩ : syracuseStep 1930601 = 1447951) B1447951
theorem B31257971 : Blo 1140634 31257971 := bstep (se 1 (by rfl) ⟨23443478, by rfl⟩ : syracuseStep 31257971 = 46886957) B46886957
theorem B1144187 : Blo 1140634 1144187 := bstep (se 1 (by rfl) ⟨858140, by rfl⟩ : syracuseStep 1144187 = 1716281) B1716281
theorem B2225569 : Blo 1140634 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B1144239 : Blo 1140634 1144239 := bstep (se 1 (by rfl) ⟨858179, by rfl⟩ : syracuseStep 1144239 = 1716359) B1716359
theorem B1144263 : Blo 1140634 1144263 := bstep (se 1 (by rfl) ⟨858197, by rfl⟩ : syracuseStep 1144263 = 1716395) B1716395
theorem B1144283 : Blo 1140634 1144283 := bstep (se 1 (by rfl) ⟨858212, by rfl⟩ : syracuseStep 1144283 = 1716425) B1716425
theorem B1144359 : Blo 1140634 1144359 := bstep (se 1 (by rfl) ⟨858269, by rfl⟩ : syracuseStep 1144359 = 1716539) B1716539
theorem B1144399 : Blo 1140634 1144399 := bstep (se 1 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 1144399 = 1716599) B1716599
theorem B1144415 : Blo 1140634 1144415 := bstep (se 1 (by rfl) ⟨858311, by rfl⟩ : syracuseStep 1144415 = 1716623) B1716623
theorem B1144443 : Blo 1140634 1144443 := bstep (se 1 (by rfl) ⟨858332, by rfl⟩ : syracuseStep 1144443 = 1716665) B1716665
theorem B1144495 : Blo 1140634 1144495 := bstep (se 1 (by rfl) ⟨858371, by rfl⟩ : syracuseStep 1144495 = 1716743) B1716743
theorem B1832647 : Blo 1140634 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B1144519 : Blo 1140634 1144519 := bstep (se 1 (by rfl) ⟨858389, by rfl⟩ : syracuseStep 1144519 = 1716779) B1716779
theorem B4880087 : Blo 1140634 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B1144539 : Blo 1140634 1144539 := bstep (se 1 (by rfl) ⟨858404, by rfl⟩ : syracuseStep 1144539 = 1716809) B1716809
theorem B1930999 : Blo 1140634 1930999 := bstep (se 1 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 1930999 = 2896499) B2896499
theorem B1144615 : Blo 1140634 1144615 := bstep (se 1 (by rfl) ⟨858461, by rfl⟩ : syracuseStep 1144615 = 1716923) B1716923
theorem B1931195 : Blo 1140634 1931195 := bstep (se 1 (by rfl) ⟨1448396, by rfl⟩ : syracuseStep 1931195 = 2896793) B2896793
theorem B1931303 : Blo 1140634 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B13891945 : Blo 1140634 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B8223241 : Blo 1140634 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B3177377 : Blo 1140634 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B31292689 : Blo 1140634 31292689 := bstep (se 2 (by rfl) ⟨11734758, by rfl⟩ : syracuseStep 31292689 = 23469517) B23469517
theorem B55639385 : Blo 1140634 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B12353543 : Blo 1140634 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3670447 : Blo 1140634 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B10978193 : Blo 1140634 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B4392791 : Blo 1140634 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B1443739 : Blo 1140634 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B4884461 : Blo 1140634 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B5212295 : Blo 1140634 5212295 := bstep (se 1 (by rfl) ⟨3909221, by rfl⟩ : syracuseStep 5212295 = 7818443) B7818443
theorem B3967663 : Blo 1140634 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B1444655 : Blo 1140634 1444655 := bstep (se 1 (by rfl) ⟨1083491, by rfl⟩ : syracuseStep 1444655 = 2166983) B2166983
theorem B16485515 : Blo 1140634 16485515 := bstep (se 1 (by rfl) ⟨12364136, by rfl⟩ : syracuseStep 16485515 = 24728273) B24728273
theorem B4885879 : Blo 1140634 4885879 := bstep (se 1 (by rfl) ⟨3664409, by rfl⟩ : syracuseStep 4885879 = 7328819) B7328819
theorem B2198983 : Blo 1140634 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B9768509 : Blo 1140634 9768509 := bstep (se 3 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 9768509 = 3663191) B3663191
theorem B7311059 : Blo 1140634 7311059 := bstep (se 1 (by rfl) ⟨5483294, by rfl⟩ : syracuseStep 7311059 = 10966589) B10966589
theorem B23432975 : Blo 1140634 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B42241949 : Blo 1140634 42241949 := bstep (se 3 (by rfl) ⟨7920365, by rfl⟩ : syracuseStep 42241949 = 15840731) B15840731
theorem B19534283 : Blo 1140634 19534283 := bstep (se 1 (by rfl) ⟨14650712, by rfl⟩ : syracuseStep 19534283 = 29301425) B29301425
theorem B4887161 : Blo 1140634 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B6591311 : Blo 1140634 6591311 := bstep (se 1 (by rfl) ⟨4943483, by rfl⟩ : syracuseStep 6591311 = 9886967) B9886967
theorem B12358601 : Blo 1140634 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B45061069 : Blo 1140634 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B3249143 : Blo 1140634 3249143 := bstep (se 1 (by rfl) ⟨2436857, by rfl⟩ : syracuseStep 3249143 = 4873715) B4873715
theorem B2888743 : Blo 1140634 2888743 := bstep (se 1 (by rfl) ⟨2166557, by rfl⟩ : syracuseStep 2888743 = 4333115) B4333115
theorem B1283359 : Blo 1140634 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B1545583 : Blo 1140634 1545583 := bstep (se 1 (by rfl) ⟨1159187, by rfl⟩ : syracuseStep 1545583 = 2318375) B2318375
theorem B2889209 : Blo 1140634 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B1283647 : Blo 1140634 1283647 := bstep (se 1 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 1283647 = 1925471) B1925471
theorem B2168623 : Blo 1140634 2168623 := bstep (se 1 (by rfl) ⟨1626467, by rfl⟩ : syracuseStep 2168623 = 3252935) B3252935
theorem B2889857 : Blo 1140634 2889857 := bstep (se 2 (by rfl) ⟨1083696, by rfl⟩ : syracuseStep 2889857 = 2167393) B2167393
theorem B3250543 : Blo 1140634 3250543 := bstep (se 1 (by rfl) ⟨2437907, by rfl⟩ : syracuseStep 3250543 = 4875815) B4875815
theorem B1284475 : Blo 1140634 1284475 := bstep (se 1 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 1284475 = 1926713) B1926713
theorem B2890151 : Blo 1140634 2890151 := bstep (se 1 (by rfl) ⟨2167613, by rfl⟩ : syracuseStep 2890151 = 4335227) B4335227
theorem B2890313 : Blo 1140634 2890313 := bstep (se 2 (by rfl) ⟨1083867, by rfl⟩ : syracuseStep 2890313 = 2167735) B2167735
theorem B1448543 : Blo 1140634 1448543 := bstep (se 1 (by rfl) ⟨1086407, by rfl⟩ : syracuseStep 1448543 = 2172815) B2172815
theorem B1284943 : Blo 1140634 1284943 := bstep (se 1 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 1284943 = 1927415) B1927415
theorem B2169679 : Blo 1140634 2169679 := bstep (se 1 (by rfl) ⟨1627259, by rfl⟩ : syracuseStep 2169679 = 3254519) B3254519
theorem B2890667 : Blo 1140634 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B1711079 : Blo 1140634 1711079 := bstep (se 1 (by rfl) ⟨1283309, by rfl⟩ : syracuseStep 1711079 = 2566619) B2566619
theorem B2890849 : Blo 1140634 2890849 := bstep (se 2 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 2890849 = 2168137) B2168137
theorem B3087575 : Blo 1140634 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B4693211 : Blo 1140634 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B1285339 : Blo 1140634 1285339 := bstep (se 1 (by rfl) ⟨964004, by rfl⟩ : syracuseStep 1285339 = 1928009) B1928009
theorem B1711337 : Blo 1140634 1711337 := bstep (se 2 (by rfl) ⟨641751, by rfl⟩ : syracuseStep 1711337 = 1283503) B1283503
theorem B1711391 : Blo 1140634 1711391 := bstep (se 1 (by rfl) ⟨1283543, by rfl⟩ : syracuseStep 1711391 = 2567087) B2567087
theorem B1711559 : Blo 1140634 1711559 := bstep (se 1 (by rfl) ⟨1283669, by rfl⟩ : syracuseStep 1711559 = 2567339) B2567339
theorem B1285627 : Blo 1140634 1285627 := bstep (se 1 (by rfl) ⟨964220, by rfl⟩ : syracuseStep 1285627 = 1928441) B1928441
theorem B7315105 : Blo 1140634 7315105 := bstep (se 2 (by rfl) ⟨2743164, by rfl⟩ : syracuseStep 7315105 = 5486329) B5486329
theorem B1285807 : Blo 1140634 1285807 := bstep (se 1 (by rfl) ⟨964355, by rfl⟩ : syracuseStep 1285807 = 1928711) B1928711
theorem B1711913 : Blo 1140634 1711913 := bstep (se 2 (by rfl) ⟨641967, by rfl⟩ : syracuseStep 1711913 = 1283935) B1283935
theorem B1711919 : Blo 1140634 1711919 := bstep (se 1 (by rfl) ⟨1283939, by rfl⟩ : syracuseStep 1711919 = 2567879) B2567879
theorem B7413565 : Blo 1140634 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B1286095 : Blo 1140634 1286095 := bstep (se 1 (by rfl) ⟨964571, by rfl⟩ : syracuseStep 1286095 = 1929143) B1929143
theorem B2891801 : Blo 1140634 2891801 := bstep (se 2 (by rfl) ⟨1084425, by rfl⟩ : syracuseStep 2891801 = 2168851) B2168851
theorem B1712393 : Blo 1140634 1712393 := bstep (se 2 (by rfl) ⟨642147, by rfl⟩ : syracuseStep 1712393 = 1284295) B1284295
theorem B1286491 : Blo 1140634 1286491 := bstep (se 1 (by rfl) ⟨964868, by rfl⟩ : syracuseStep 1286491 = 1929737) B1929737
theorem B18555227 : Blo 1140634 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B1712495 : Blo 1140634 1712495 := bstep (se 1 (by rfl) ⟨1284371, by rfl⟩ : syracuseStep 1712495 = 2568743) B2568743
theorem B1286599 : Blo 1140634 1286599 := bstep (se 1 (by rfl) ⟨964949, by rfl⟩ : syracuseStep 1286599 = 1929899) B1929899
theorem B18522593 : Blo 1140634 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B2892257 : Blo 1140634 2892257 := bstep (se 2 (by rfl) ⟨1084596, by rfl⟩ : syracuseStep 2892257 = 2169193) B2169193
theorem B2171387 : Blo 1140634 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B2892307 : Blo 1140634 2892307 := bstep (se 1 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 2892307 = 4338461) B4338461
theorem B1712711 : Blo 1140634 1712711 := bstep (se 1 (by rfl) ⟨1284533, by rfl⟩ : syracuseStep 1712711 = 2569067) B2569067
theorem B1712747 : Blo 1140634 1712747 := bstep (se 1 (by rfl) ⟨1284560, by rfl⟩ : syracuseStep 1712747 = 2569121) B2569121
theorem B6955703 : Blo 1140634 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B7316183 : Blo 1140634 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B49357583 : Blo 1140634 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B1286959 : Blo 1140634 1286959 := bstep (se 1 (by rfl) ⟨965219, by rfl⟩ : syracuseStep 1286959 = 1930439) B1930439
theorem B1712975 : Blo 1140634 1712975 := bstep (se 1 (by rfl) ⟨1284731, by rfl⟩ : syracuseStep 1712975 = 2569463) B2569463
theorem B1287067 : Blo 1140634 1287067 := bstep (se 1 (by rfl) ⟨965300, by rfl⟩ : syracuseStep 1287067 = 1930601) B1930601
theorem B14623649 : Blo 1140634 14623649 := bstep (se 2 (by rfl) ⟨5483868, by rfl⟩ : syracuseStep 14623649 = 10967737) B10967737
theorem B3253391 : Blo 1140634 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B1713371 : Blo 1140634 1713371 := bstep (se 1 (by rfl) ⟨1285028, by rfl⟩ : syracuseStep 1713371 = 2570057) B2570057
theorem B1287463 : Blo 1140634 1287463 := bstep (se 1 (by rfl) ⟨965597, by rfl⟩ : syracuseStep 1287463 = 1931195) B1931195
theorem B1287535 : Blo 1140634 1287535 := bstep (se 1 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 1287535 = 1931303) B1931303
theorem B1713545 : Blo 1140634 1713545 := bstep (se 2 (by rfl) ⟨642579, by rfl⟩ : syracuseStep 1713545 = 1285159) B1285159
theorem B3712445 : Blo 1140634 3712445 := bstep (se 3 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 3712445 = 1392167) B1392167
theorem B2172359 : Blo 1140634 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B6170201 : Blo 1140634 6170201 := bstep (se 2 (by rfl) ⟨2313825, by rfl⟩ : syracuseStep 6170201 = 4627651) B4627651
theorem B2172511 : Blo 1140634 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B5777081 : Blo 1140634 5777081 := bstep (se 2 (by rfl) ⟨2166405, by rfl⟩ : syracuseStep 5777081 = 4332811) B4332811
theorem B41723585 : Blo 1140634 41723585 := bstep (se 2 (by rfl) ⟨15646344, by rfl⟩ : syracuseStep 41723585 = 31292689) B31292689
theorem B1713899 : Blo 1140634 1713899 := bstep (se 1 (by rfl) ⟨1285424, by rfl⟩ : syracuseStep 1713899 = 2570849) B2570849
theorem B13182797 : Blo 1140634 13182797 := bstep (se 3 (by rfl) ⟨2471774, by rfl⟩ : syracuseStep 13182797 = 4943549) B4943549
theorem B1714127 : Blo 1140634 1714127 := bstep (se 1 (by rfl) ⟨1285595, by rfl⟩ : syracuseStep 1714127 = 2571191) B2571191
theorem B2894089 : Blo 1140634 2894089 := bstep (se 2 (by rfl) ⟨1085283, by rfl⟩ : syracuseStep 2894089 = 2170567) B2170567
theorem B11741449 : Blo 1140634 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B1714523 : Blo 1140634 1714523 := bstep (se 1 (by rfl) ⟨1285892, by rfl⟩ : syracuseStep 1714523 = 2571785) B2571785
theorem B1255771 : Blo 1140634 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B2566511 : Blo 1140634 2566511 := bstep (se 1 (by rfl) ⟨1924883, by rfl⟩ : syracuseStep 2566511 = 3849767) B3849767
theorem B2566583 : Blo 1140634 2566583 := bstep (se 1 (by rfl) ⟨1924937, by rfl⟩ : syracuseStep 2566583 = 3849875) B3849875
theorem B1714751 : Blo 1140634 1714751 := bstep (se 1 (by rfl) ⟨1286063, by rfl⟩ : syracuseStep 1714751 = 2572127) B2572127
theorem B2566727 : Blo 1140634 2566727 := bstep (se 1 (by rfl) ⟨1925045, by rfl⟩ : syracuseStep 2566727 = 3850091) B3850091
theorem B2566763 : Blo 1140634 2566763 := bstep (se 1 (by rfl) ⟨1925072, by rfl⟩ : syracuseStep 2566763 = 3850145) B3850145
theorem B1714871 : Blo 1140634 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B12069665 : Blo 1140634 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B1715099 : Blo 1140634 1715099 := bstep (se 1 (by rfl) ⟨1286324, by rfl⟩ : syracuseStep 1715099 = 2572649) B2572649
theorem B46836701 : Blo 1140634 46836701 := bstep (se 3 (by rfl) ⟨8781881, by rfl⟩ : syracuseStep 46836701 = 17563763) B17563763
theorem B2567159 : Blo 1140634 2567159 := bstep (se 1 (by rfl) ⟨1925369, by rfl⟩ : syracuseStep 2567159 = 3850739) B3850739
theorem B39529559 : Blo 1140634 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B1715495 : Blo 1140634 1715495 := bstep (se 1 (by rfl) ⟨1286621, by rfl⟩ : syracuseStep 1715495 = 2573243) B2573243
theorem B2567519 : Blo 1140634 2567519 := bstep (se 1 (by rfl) ⟨1925639, by rfl⟩ : syracuseStep 2567519 = 3851279) B3851279
theorem B1715579 : Blo 1140634 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B3911161 : Blo 1140634 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B1715705 : Blo 1140634 1715705 := bstep (se 2 (by rfl) ⟨643389, by rfl⟩ : syracuseStep 1715705 = 1286779) B1286779
theorem B5779025 : Blo 1140634 5779025 := bstep (se 2 (by rfl) ⟨2167134, by rfl⟩ : syracuseStep 5779025 = 4334269) B4334269
theorem B3092051 : Blo 1140634 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B1715807 : Blo 1140634 1715807 := bstep (se 1 (by rfl) ⟨1286855, by rfl⟩ : syracuseStep 1715807 = 2573711) B2573711
theorem B2895547 : Blo 1140634 2895547 := bstep (se 1 (by rfl) ⟨2171660, by rfl⟩ : syracuseStep 2895547 = 4343321) B4343321
theorem B10989265 : Blo 1140634 10989265 := bstep (se 2 (by rfl) ⟨4120974, by rfl⟩ : syracuseStep 10989265 = 8241949) B8241949
theorem B2567915 : Blo 1140634 2567915 := bstep (se 1 (by rfl) ⟨1925936, by rfl⟩ : syracuseStep 2567915 = 3851873) B3851873
theorem B1716023 : Blo 1140634 1716023 := bstep (se 1 (by rfl) ⟨1287017, by rfl⟩ : syracuseStep 1716023 = 2574035) B2574035
theorem B2568041 : Blo 1140634 2568041 := bstep (se 2 (by rfl) ⟨963015, by rfl⟩ : syracuseStep 2568041 = 1926031) B1926031
theorem B3256193 : Blo 1140634 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B1716329 : Blo 1140634 1716329 := bstep (se 2 (by rfl) ⟨643623, by rfl⟩ : syracuseStep 1716329 = 1287247) B1287247
theorem B9777257 : Blo 1140634 9777257 := bstep (se 2 (by rfl) ⟨3666471, by rfl⟩ : syracuseStep 9777257 = 7332943) B7332943
theorem B3256649 : Blo 1140634 3256649 := bstep (se 2 (by rfl) ⟨1221243, by rfl⟩ : syracuseStep 3256649 = 2442487) B2442487
theorem B1716647 : Blo 1140634 1716647 := bstep (se 1 (by rfl) ⟨1287485, by rfl⟩ : syracuseStep 1716647 = 2574971) B2574971
theorem B1716731 : Blo 1140634 1716731 := bstep (se 1 (by rfl) ⟨1287548, by rfl⟩ : syracuseStep 1716731 = 2575097) B2575097
theorem B2437651 : Blo 1140634 2437651 := bstep (se 1 (by rfl) ⟨1828238, by rfl⟩ : syracuseStep 2437651 = 3656477) B3656477
theorem B1716857 : Blo 1140634 1716857 := bstep (se 2 (by rfl) ⟨643821, by rfl⟩ : syracuseStep 1716857 = 1287643) B1287643
theorem B1716911 : Blo 1140634 1716911 := bstep (se 1 (by rfl) ⟨1287683, by rfl⟩ : syracuseStep 1716911 = 2575367) B2575367
theorem B2568887 : Blo 1140634 2568887 := bstep (se 1 (by rfl) ⟨1926665, by rfl⟩ : syracuseStep 2568887 = 3853331) B3853331
theorem B2896631 : Blo 1140634 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B5485391 : Blo 1140634 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B2569103 : Blo 1140634 2569103 := bstep (se 1 (by rfl) ⟨1926827, by rfl⟩ : syracuseStep 2569103 = 3853655) B3853655
theorem B19543031 : Blo 1140634 19543031 := bstep (se 1 (by rfl) ⟨14657273, by rfl⟩ : syracuseStep 19543031 = 29314547) B29314547
theorem B5485715 : Blo 1140634 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B14628113 : Blo 1140634 14628113 := bstep (se 2 (by rfl) ⟨5485542, by rfl⟩ : syracuseStep 14628113 = 10971085) B10971085
theorem B2569823 : Blo 1140634 2569823 := bstep (se 1 (by rfl) ⟨1927367, by rfl⟩ : syracuseStep 2569823 = 3854735) B3854735
theorem B2570039 : Blo 1140634 2570039 := bstep (se 1 (by rfl) ⟨1927529, by rfl⟩ : syracuseStep 2570039 = 3855059) B3855059
theorem B5781455 : Blo 1140634 5781455 := bstep (se 1 (by rfl) ⟨4336091, by rfl⟩ : syracuseStep 5781455 = 8672183) B8672183
theorem B4634657 : Blo 1140634 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B2570345 : Blo 1140634 2570345 := bstep (se 2 (by rfl) ⟨963879, by rfl⟩ : syracuseStep 2570345 = 1927759) B1927759
theorem B2930899 : Blo 1140634 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B2439497 : Blo 1140634 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B2603593 : Blo 1140634 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B20855369 : Blo 1140634 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B2570831 : Blo 1140634 2570831 := bstep (se 1 (by rfl) ⟨1928123, by rfl⟩ : syracuseStep 2570831 = 3856247) B3856247
theorem B2570975 : Blo 1140634 2570975 := bstep (se 1 (by rfl) ⟨1928231, by rfl⟩ : syracuseStep 2570975 = 3856463) B3856463
theorem B5782427 : Blo 1140634 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B3259291 : Blo 1140634 3259291 := bstep (se 1 (by rfl) ⟨2444468, by rfl⟩ : syracuseStep 3259291 = 4888937) B4888937
theorem B2571227 : Blo 1140634 2571227 := bstep (se 1 (by rfl) ⟨1928420, by rfl⟩ : syracuseStep 2571227 = 3856841) B3856841
theorem B2571407 : Blo 1140634 2571407 := bstep (se 1 (by rfl) ⟨1928555, by rfl⟩ : syracuseStep 2571407 = 3857111) B3857111
theorem B2571497 : Blo 1140634 2571497 := bstep (se 2 (by rfl) ⟨964311, by rfl⟩ : syracuseStep 2571497 = 1928623) B1928623
theorem B2571551 : Blo 1140634 2571551 := bstep (se 1 (by rfl) ⟨1928663, by rfl⟩ : syracuseStep 2571551 = 3857327) B3857327
theorem B2440487 : Blo 1140634 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B4341059 : Blo 1140634 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B5782913 : Blo 1140634 5782913 := bstep (se 2 (by rfl) ⟨2168592, by rfl⟩ : syracuseStep 5782913 = 4337185) B4337185
theorem B3849659 : Blo 1140634 3849659 := bstep (se 1 (by rfl) ⟨2887244, by rfl⟩ : syracuseStep 3849659 = 5774489) B5774489
theorem B2572073 : Blo 1140634 2572073 := bstep (se 2 (by rfl) ⟨964527, by rfl⟩ : syracuseStep 2572073 = 1929055) B1929055
theorem B4341545 : Blo 1140634 4341545 := bstep (se 2 (by rfl) ⟨1628079, by rfl⟩ : syracuseStep 4341545 = 3256159) B3256159
theorem B6504299 : Blo 1140634 6504299 := bstep (se 1 (by rfl) ⟨4878224, by rfl⟩ : syracuseStep 6504299 = 9756449) B9756449
theorem B13877153 : Blo 1140634 13877153 := bstep (se 2 (by rfl) ⟨5203932, by rfl⟩ : syracuseStep 13877153 = 10407865) B10407865
theorem B5783561 : Blo 1140634 5783561 := bstep (se 2 (by rfl) ⟨2168835, by rfl⟩ : syracuseStep 5783561 = 4337671) B4337671
theorem B5783723 : Blo 1140634 5783723 := bstep (se 1 (by rfl) ⟨4337792, by rfl⟩ : syracuseStep 5783723 = 8675585) B8675585
theorem B5784209 : Blo 1140634 5784209 := bstep (se 2 (by rfl) ⟨2169078, by rfl⟩ : syracuseStep 5784209 = 4338157) B4338157
theorem B2573135 : Blo 1140634 2573135 := bstep (se 1 (by rfl) ⟨1929851, by rfl⟩ : syracuseStep 2573135 = 3859703) B3859703
theorem B2573351 : Blo 1140634 2573351 := bstep (se 1 (by rfl) ⟨1930013, by rfl⟩ : syracuseStep 2573351 = 3860027) B3860027
theorem B7423073 : Blo 1140634 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B1852559 : Blo 1140634 1852559 := bstep (se 1 (by rfl) ⟨1389419, by rfl⟩ : syracuseStep 1852559 = 2778839) B2778839
theorem B111166667 : Blo 1140634 111166667 := bstep (se 1 (by rfl) ⟨83375000, by rfl⟩ : syracuseStep 111166667 = 166750001) B166750001
theorem B2573531 : Blo 1140634 2573531 := bstep (se 1 (by rfl) ⟨1930148, by rfl⟩ : syracuseStep 2573531 = 3860297) B3860297
theorem B4343017 : Blo 1140634 4343017 := bstep (se 2 (by rfl) ⟨1628631, by rfl⟩ : syracuseStep 4343017 = 3257263) B3257263
theorem B6178157 : Blo 1140634 6178157 := bstep (se 3 (by rfl) ⟨1158404, by rfl⟩ : syracuseStep 6178157 = 2316809) B2316809
theorem B2573729 : Blo 1140634 2573729 := bstep (se 2 (by rfl) ⟨965148, by rfl⟩ : syracuseStep 2573729 = 1930297) B1930297
theorem B2967425 : Blo 1140634 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B3655631 : Blo 1140634 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B2574287 : Blo 1140634 2574287 := bstep (se 1 (by rfl) ⟨1930715, by rfl⟩ : syracuseStep 2574287 = 3861431) B3861431
theorem B21743873 : Blo 1140634 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B2443529 : Blo 1140634 2443529 := bstep (se 2 (by rfl) ⟨916323, by rfl⟩ : syracuseStep 2443529 = 1832647) B1832647
theorem B5556505 : Blo 1140634 5556505 := bstep (se 2 (by rfl) ⟨2083689, by rfl⟩ : syracuseStep 5556505 = 4167379) B4167379
theorem B2574665 : Blo 1140634 2574665 := bstep (se 2 (by rfl) ⟨965499, by rfl⟩ : syracuseStep 2574665 = 1930999) B1930999
theorem B2574683 : Blo 1140634 2574683 := bstep (se 1 (by rfl) ⟨1931012, by rfl⟩ : syracuseStep 2574683 = 3862025) B3862025
theorem B8243623 : Blo 1140634 8243623 := bstep (se 1 (by rfl) ⟨6182717, by rfl⟩ : syracuseStep 8243623 = 12365435) B12365435
theorem B6506963 : Blo 1140634 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B9751013 : Blo 1140634 9751013 := bstep (se 4 (by rfl) ⟨914157, by rfl⟩ : syracuseStep 9751013 = 1828315) B1828315
theorem B1624799 : Blo 1140634 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B5557015 : Blo 1140634 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B6179651 : Blo 1140634 6179651 := bstep (se 1 (by rfl) ⟨4634738, by rfl⟩ : syracuseStep 6179651 = 9269477) B9269477
theorem B2575259 : Blo 1140634 2575259 := bstep (se 1 (by rfl) ⟨1931444, by rfl⟩ : syracuseStep 2575259 = 3862889) B3862889
theorem B2608043 : Blo 1140634 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B5786639 : Blo 1140634 5786639 := bstep (se 1 (by rfl) ⟨4339979, by rfl⟩ : syracuseStep 5786639 = 8679959) B8679959
theorem B23481409 : Blo 1140634 23481409 := bstep (se 2 (by rfl) ⟨8805528, by rfl⟩ : syracuseStep 23481409 = 17611057) B17611057
theorem B10996955 : Blo 1140634 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B10964321 : Blo 1140634 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B3853817 : Blo 1140634 3853817 := bstep (se 2 (by rfl) ⟨1445181, by rfl⟩ : syracuseStep 3853817 = 2890363) B2890363
theorem B4640249 : Blo 1140634 4640249 := bstep (se 2 (by rfl) ⟨1740093, by rfl⟩ : syracuseStep 4640249 = 3480187) B3480187
theorem B3854087 : Blo 1140634 3854087 := bstep (se 1 (by rfl) ⟨2890565, by rfl⟩ : syracuseStep 3854087 = 5781131) B5781131
theorem B5787449 : Blo 1140634 5787449 := bstep (se 2 (by rfl) ⟨2170293, by rfl⟩ : syracuseStep 5787449 = 4340587) B4340587
theorem B3854141 : Blo 1140634 3854141 := bstep (se 3 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 3854141 = 1445303) B1445303
theorem B24760379 : Blo 1140634 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B3658259 : Blo 1140634 3658259 := bstep (se 1 (by rfl) ⟨2743694, by rfl⟩ : syracuseStep 3658259 = 5487389) B5487389
theorem B2118251 : Blo 1140634 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B10408601 : Blo 1140634 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B5493905 : Blo 1140634 5493905 := bstep (se 2 (by rfl) ⟨2060214, by rfl⟩ : syracuseStep 5493905 = 4120429) B4120429
theorem B2741627 : Blo 1140634 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B2742703 : Blo 1140634 2742703 := bstep (se 1 (by rfl) ⟨2057027, by rfl⟩ : syracuseStep 2742703 = 4114055) B4114055
theorem B5790203 : Blo 1140634 5790203 := bstep (se 1 (by rfl) ⟨4342652, by rfl⟩ : syracuseStep 5790203 = 8685305) B8685305
theorem B3857003 : Blo 1140634 3857003 := bstep (se 1 (by rfl) ⟨2892752, by rfl⟩ : syracuseStep 3857003 = 5785505) B5785505
theorem B4873115 : Blo 1140634 4873115 := bstep (se 1 (by rfl) ⟨3654836, by rfl⟩ : syracuseStep 4873115 = 7309673) B7309673
theorem B4873355 : Blo 1140634 4873355 := bstep (se 1 (by rfl) ⟨3655016, by rfl⟩ : syracuseStep 4873355 = 7310033) B7310033
theorem B3857597 : Blo 1140634 3857597 := bstep (se 3 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 3857597 = 1446599) B1446599
theorem B24108299 : Blo 1140634 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B3661193 : Blo 1140634 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B5791175 : Blo 1140634 5791175 := bstep (se 1 (by rfl) ⟨4343381, by rfl⟩ : syracuseStep 5791175 = 8686763) B8686763
theorem B3661271 : Blo 1140634 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2055775 : Blo 1140634 2055775 := bstep (se 1 (by rfl) ⟨1541831, by rfl⟩ : syracuseStep 2055775 = 3083663) B3083663
theorem B1924843 : Blo 1140634 1924843 := bstep (se 1 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 1924843 = 2887265) B2887265
theorem B5791499 : Blo 1140634 5791499 := bstep (se 1 (by rfl) ⟨4343624, by rfl⟩ : syracuseStep 5791499 = 8687249) B8687249
theorem B12345281 : Blo 1140634 12345281 := bstep (se 2 (by rfl) ⟨4629480, by rfl⟩ : syracuseStep 12345281 = 9258961) B9258961
theorem B1925815 : Blo 1140634 1925815 := bstep (se 1 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 1925815 = 2888723) B2888723
theorem B25060049 : Blo 1140634 25060049 := bstep (se 2 (by rfl) ⟨9397518, by rfl⟩ : syracuseStep 25060049 = 18795037) B18795037
theorem B5792471 : Blo 1140634 5792471 := bstep (se 1 (by rfl) ⟨4344353, by rfl⟩ : syracuseStep 5792471 = 8688707) B8688707
theorem B2745107 : Blo 1140634 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B1926119 : Blo 1140634 1926119 := bstep (se 1 (by rfl) ⟨1444589, by rfl⟩ : syracuseStep 1926119 = 2889179) B2889179
theorem B1827983 : Blo 1140634 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B5793119 : Blo 1140634 5793119 := bstep (se 1 (by rfl) ⟨4344839, by rfl⟩ : syracuseStep 5793119 = 8689679) B8689679
theorem B4875643 : Blo 1140634 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B7923257 : Blo 1140634 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B1828649 : Blo 1140634 1828649 := bstep (se 2 (by rfl) ⟨685743, by rfl⟩ : syracuseStep 1828649 = 1371487) B1371487
theorem B5498711 : Blo 1140634 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B2746241 : Blo 1140634 2746241 := bstep (se 2 (by rfl) ⟨1029840, by rfl⟩ : syracuseStep 2746241 = 2059681) B2059681
theorem B1140635 : Blo 1140634 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1140687 : Blo 1140634 1140687 := bstep (se 1 (by rfl) ⟨855515, by rfl⟩ : syracuseStep 1140687 = 1711031) B1711031
theorem B1140711 : Blo 1140634 1140711 := bstep (se 1 (by rfl) ⟨855533, by rfl⟩ : syracuseStep 1140711 = 1711067) B1711067
theorem B3860513 : Blo 1140634 3860513 := bstep (se 2 (by rfl) ⟨1447692, by rfl⟩ : syracuseStep 3860513 = 2895385) B2895385
theorem B1927273 : Blo 1140634 1927273 := bstep (se 2 (by rfl) ⟨722727, by rfl⟩ : syracuseStep 1927273 = 1445455) B1445455
theorem B1141023 : Blo 1140634 1141023 := bstep (se 1 (by rfl) ⟨855767, by rfl⟩ : syracuseStep 1141023 = 1711535) B1711535
theorem B1141083 : Blo 1140634 1141083 := bstep (se 1 (by rfl) ⟨855812, by rfl⟩ : syracuseStep 1141083 = 1711625) B1711625
theorem B1141103 : Blo 1140634 1141103 := bstep (se 1 (by rfl) ⟨855827, by rfl⟩ : syracuseStep 1141103 = 1711655) B1711655
theorem B1141159 : Blo 1140634 1141159 := bstep (se 1 (by rfl) ⟨855869, by rfl⟩ : syracuseStep 1141159 = 1711739) B1711739
theorem B1141243 : Blo 1140634 1141243 := bstep (se 1 (by rfl) ⟨855932, by rfl⟩ : syracuseStep 1141243 = 1711865) B1711865
theorem B5204519 : Blo 1140634 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B1141311 : Blo 1140634 1141311 := bstep (se 1 (by rfl) ⟨855983, by rfl⟩ : syracuseStep 1141311 = 1711967) B1711967
theorem B1141319 : Blo 1140634 1141319 := bstep (se 1 (by rfl) ⟨855989, by rfl⟩ : syracuseStep 1141319 = 1711979) B1711979
theorem B20834995 : Blo 1140634 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B1141471 : Blo 1140634 1141471 := bstep (se 1 (by rfl) ⟨856103, by rfl⟩ : syracuseStep 1141471 = 1712207) B1712207
theorem B10414871 : Blo 1140634 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1141551 : Blo 1140634 1141551 := bstep (se 1 (by rfl) ⟨856163, by rfl⟩ : syracuseStep 1141551 = 1712327) B1712327
theorem B6187843 : Blo 1140634 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B2747279 : Blo 1140634 2747279 := bstep (se 1 (by rfl) ⟨2060459, by rfl⟩ : syracuseStep 2747279 = 4120919) B4120919
theorem B1141659 : Blo 1140634 1141659 := bstep (se 1 (by rfl) ⟨856244, by rfl⟩ : syracuseStep 1141659 = 1712489) B1712489
theorem B5434285 : Blo 1140634 5434285 := bstep (se 3 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 5434285 = 2037857) B2037857
theorem B1141711 : Blo 1140634 1141711 := bstep (se 1 (by rfl) ⟨856283, by rfl⟩ : syracuseStep 1141711 = 1712567) B1712567
theorem B1141735 : Blo 1140634 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B1829879 : Blo 1140634 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B9268301 : Blo 1140634 9268301 := bstep (se 3 (by rfl) ⟨1737806, by rfl⟩ : syracuseStep 9268301 = 3475613) B3475613
theorem B1142047 : Blo 1140634 1142047 := bstep (se 1 (by rfl) ⟨856535, by rfl⟩ : syracuseStep 1142047 = 1713071) B1713071
theorem B1142107 : Blo 1140634 1142107 := bstep (se 1 (by rfl) ⟨856580, by rfl⟩ : syracuseStep 1142107 = 1713161) B1713161
theorem B1142127 : Blo 1140634 1142127 := bstep (se 1 (by rfl) ⟨856595, by rfl⟩ : syracuseStep 1142127 = 1713191) B1713191
theorem B1142183 : Blo 1140634 1142183 := bstep (se 1 (by rfl) ⟨856637, by rfl⟩ : syracuseStep 1142183 = 1713275) B1713275
theorem B1142267 : Blo 1140634 1142267 := bstep (se 1 (by rfl) ⟨856700, by rfl⟩ : syracuseStep 1142267 = 1713401) B1713401
theorem B1142335 : Blo 1140634 1142335 := bstep (se 1 (by rfl) ⟨856751, by rfl⟩ : syracuseStep 1142335 = 1713503) B1713503
theorem B1142343 : Blo 1140634 1142343 := bstep (se 1 (by rfl) ⟨856757, by rfl⟩ : syracuseStep 1142343 = 1713515) B1713515
theorem B4124321 : Blo 1140634 4124321 := bstep (se 2 (by rfl) ⟨1546620, by rfl⟩ : syracuseStep 4124321 = 3093241) B3093241
theorem B1142495 : Blo 1140634 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B1929001 : Blo 1140634 1929001 := bstep (se 2 (by rfl) ⟨723375, by rfl⟩ : syracuseStep 1929001 = 1446751) B1446751
theorem B1142575 : Blo 1140634 1142575 := bstep (se 1 (by rfl) ⟨856931, by rfl⟩ : syracuseStep 1142575 = 1713863) B1713863
theorem B1142683 : Blo 1140634 1142683 := bstep (se 1 (by rfl) ⟨857012, by rfl⟩ : syracuseStep 1142683 = 1714025) B1714025
theorem B1142735 : Blo 1140634 1142735 := bstep (se 1 (by rfl) ⟨857051, by rfl⟩ : syracuseStep 1142735 = 1714103) B1714103
theorem B1142759 : Blo 1140634 1142759 := bstep (se 1 (by rfl) ⟨857069, by rfl⟩ : syracuseStep 1142759 = 1714139) B1714139
theorem B190116013 : Blo 1140634 190116013 := bstep (se 3 (by rfl) ⟨35646752, by rfl⟩ : syracuseStep 190116013 = 71293505) B71293505
theorem B1143071 : Blo 1140634 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B1143131 : Blo 1140634 1143131 := bstep (se 1 (by rfl) ⟨857348, by rfl⟩ : syracuseStep 1143131 = 1714697) B1714697
theorem B2748779 : Blo 1140634 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B1143151 : Blo 1140634 1143151 := bstep (se 1 (by rfl) ⟨857363, by rfl⟩ : syracuseStep 1143151 = 1714727) B1714727
theorem B1143207 : Blo 1140634 1143207 := bstep (se 1 (by rfl) ⟨857405, by rfl⟩ : syracuseStep 1143207 = 1714811) B1714811
theorem B1143291 : Blo 1140634 1143291 := bstep (se 1 (by rfl) ⟨857468, by rfl⟩ : syracuseStep 1143291 = 1714937) B1714937
theorem B1143359 : Blo 1140634 1143359 := bstep (se 1 (by rfl) ⟨857519, by rfl⟩ : syracuseStep 1143359 = 1715039) B1715039
theorem B1929791 : Blo 1140634 1929791 := bstep (se 1 (by rfl) ⟨1447343, by rfl⟩ : syracuseStep 1929791 = 2894687) B2894687
theorem B1143367 : Blo 1140634 1143367 := bstep (se 1 (by rfl) ⟨857525, by rfl⟩ : syracuseStep 1143367 = 1715051) B1715051
theorem B2290351 : Blo 1140634 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B21951161 : Blo 1140634 21951161 := bstep (se 2 (by rfl) ⟨8231685, by rfl⟩ : syracuseStep 21951161 = 16463371) B16463371
theorem B1143519 : Blo 1140634 1143519 := bstep (se 1 (by rfl) ⟨857639, by rfl⟩ : syracuseStep 1143519 = 1715279) B1715279
theorem B1143599 : Blo 1140634 1143599 := bstep (se 1 (by rfl) ⟨857699, by rfl⟩ : syracuseStep 1143599 = 1715399) B1715399
theorem B1143707 : Blo 1140634 1143707 := bstep (se 1 (by rfl) ⟨857780, by rfl⟩ : syracuseStep 1143707 = 1715561) B1715561
theorem B1143759 : Blo 1140634 1143759 := bstep (se 1 (by rfl) ⟨857819, by rfl⟩ : syracuseStep 1143759 = 1715639) B1715639
theorem B1373159 : Blo 1140634 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B1143783 : Blo 1140634 1143783 := bstep (se 1 (by rfl) ⟨857837, by rfl⟩ : syracuseStep 1143783 = 1715675) B1715675
theorem B1930459 : Blo 1140634 1930459 := bstep (se 1 (by rfl) ⟨1447844, by rfl⟩ : syracuseStep 1930459 = 2895689) B2895689
theorem B1144095 : Blo 1140634 1144095 := bstep (se 1 (by rfl) ⟨858071, by rfl⟩ : syracuseStep 1144095 = 1716143) B1716143
theorem B10974503 : Blo 1140634 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B1144155 : Blo 1140634 1144155 := bstep (se 1 (by rfl) ⟨858116, by rfl⟩ : syracuseStep 1144155 = 1716233) B1716233
theorem B1144175 : Blo 1140634 1144175 := bstep (se 1 (by rfl) ⟨858131, by rfl⟩ : syracuseStep 1144175 = 1716263) B1716263
theorem B1144231 : Blo 1140634 1144231 := bstep (se 1 (by rfl) ⟨858173, by rfl⟩ : syracuseStep 1144231 = 1716347) B1716347
theorem B1144315 : Blo 1140634 1144315 := bstep (se 1 (by rfl) ⟨858236, by rfl⟩ : syracuseStep 1144315 = 1716473) B1716473
theorem B1144383 : Blo 1140634 1144383 := bstep (se 1 (by rfl) ⟨858287, by rfl⟩ : syracuseStep 1144383 = 1716575) B1716575
theorem B1144391 : Blo 1140634 1144391 := bstep (se 1 (by rfl) ⟨858293, by rfl⟩ : syracuseStep 1144391 = 1716587) B1716587
theorem B1144543 : Blo 1140634 1144543 := bstep (se 1 (by rfl) ⟨858407, by rfl⟩ : syracuseStep 1144543 = 1716815) B1716815
theorem B1144623 : Blo 1140634 1144623 := bstep (se 1 (by rfl) ⟨858467, by rfl⟩ : syracuseStep 1144623 = 1716935) B1716935
theorem B1931215 : Blo 1140634 1931215 := bstep (se 1 (by rfl) ⟨1448411, by rfl⟩ : syracuseStep 1931215 = 2896823) B2896823
theorem B1374427 : Blo 1140634 1374427 := bstep (se 1 (by rfl) ⟨1030820, by rfl⟩ : syracuseStep 1374427 = 2061641) B2061641
theorem B20838647 : Blo 1140634 20838647 := bstep (se 1 (by rfl) ⟨15628985, by rfl⟩ : syracuseStep 20838647 = 31257971) B31257971
theorem B37059707 : Blo 1140634 37059707 := bstep (se 1 (by rfl) ⟨27794780, by rfl⟩ : syracuseStep 37059707 = 55589561) B55589561
theorem B9272713 : Blo 1140634 9272713 := bstep (se 2 (by rfl) ⟨3477267, by rfl⟩ : syracuseStep 9272713 = 6954535) B6954535
theorem B4881863 : Blo 1140634 4881863 := bstep (se 1 (by rfl) ⟨3661397, by rfl⟩ : syracuseStep 4881863 = 7322795) B7322795
theorem B37092923 : Blo 1140634 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B4948715 : Blo 1140634 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B3474863 : Blo 1140634 3474863 := bstep (se 1 (by rfl) ⟨2606147, by rfl⟩ : syracuseStep 3474863 = 5212295) B5212295
theorem B7309547 : Blo 1140634 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B7408673 : Blo 1140634 7408673 := bstep (se 2 (by rfl) ⟨2778252, by rfl⟩ : syracuseStep 7408673 = 5556505) B5556505
theorem B1674361 : Blo 1140634 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B4394207 : Blo 1140634 4394207 := bstep (se 1 (by rfl) ⟨3295655, by rfl⟩ : syracuseStep 4394207 = 6591311) B6591311
theorem B2166095 : Blo 1140634 2166095 := bstep (se 1 (by rfl) ⟨1624571, by rfl⟩ : syracuseStep 2166095 = 3249143) B3249143
theorem B7311005 : Blo 1140634 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B7245713 : Blo 1140634 7245713 := bstep (se 2 (by rfl) ⟨2717142, by rfl⟩ : syracuseStep 7245713 = 5434285) B5434285
theorem B33001829 : Blo 1140634 33001829 := bstep (se 4 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 33001829 = 6187843) B6187843
theorem B3248743 : Blo 1140634 3248743 := bstep (se 1 (by rfl) ⟨2436557, by rfl⟩ : syracuseStep 3248743 = 4873115) B4873115
theorem B5214881 : Blo 1140634 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B3248903 : Blo 1140634 3248903 := bstep (se 1 (by rfl) ⟨2436677, by rfl⟩ : syracuseStep 3248903 = 4873355) B4873355
theorem B14652353 : Blo 1140634 14652353 := bstep (se 2 (by rfl) ⟨5494632, by rfl⟩ : syracuseStep 14652353 = 10989265) B10989265
theorem B8230187 : Blo 1140634 8230187 := bstep (se 1 (by rfl) ⟨6172640, by rfl⟩ : syracuseStep 8230187 = 12345281) B12345281
theorem B32905055 : Blo 1140634 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B1284079 : Blo 1140634 1284079 := bstep (se 1 (by rfl) ⟨963059, by rfl⟩ : syracuseStep 1284079 = 1926119) B1926119
theorem B3250201 : Blo 1140634 3250201 := bstep (se 2 (by rfl) ⟨1218825, by rfl⟩ : syracuseStep 3250201 = 2437651) B2437651
theorem B1218655 : Blo 1140634 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B2168927 : Blo 1140634 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B3053801 : Blo 1140634 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B5282171 : Blo 1140634 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B1219099 : Blo 1140634 1219099 := bstep (se 1 (by rfl) ⟨914324, by rfl⟩ : syracuseStep 1219099 = 1828649) B1828649
theorem B8788531 : Blo 1140634 8788531 := bstep (se 1 (by rfl) ⟨6591398, by rfl⟩ : syracuseStep 8788531 = 13182797) B13182797
theorem B1711007 : Blo 1140634 1711007 := bstep (se 1 (by rfl) ⟨1283255, by rfl⟩ : syracuseStep 1711007 = 2566511) B2566511
theorem B1711055 : Blo 1140634 1711055 := bstep (se 1 (by rfl) ⟨1283291, by rfl⟩ : syracuseStep 1711055 = 2566583) B2566583
theorem B1711145 : Blo 1140634 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B1711151 : Blo 1140634 1711151 := bstep (se 1 (by rfl) ⟨1283363, by rfl⟩ : syracuseStep 1711151 = 2566727) B2566727
theorem B1711175 : Blo 1140634 1711175 := bstep (se 1 (by rfl) ⟨1283381, by rfl⟩ : syracuseStep 1711175 = 2566763) B2566763
theorem B4332797 : Blo 1140634 4332797 := bstep (se 3 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 4332797 = 1624799) B1624799
theorem B1711439 : Blo 1140634 1711439 := bstep (se 1 (by rfl) ⟨1283579, by rfl⟩ : syracuseStep 1711439 = 2567159) B2567159
theorem B1219919 : Blo 1140634 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B26353039 : Blo 1140634 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B1711529 : Blo 1140634 1711529 := bstep (se 2 (by rfl) ⟨641823, by rfl⟩ : syracuseStep 1711529 = 1283647) B1283647
theorem B1711679 : Blo 1140634 1711679 := bstep (se 1 (by rfl) ⟨1283759, by rfl⟩ : syracuseStep 1711679 = 2567519) B2567519
theorem B2891497 : Blo 1140634 2891497 := bstep (se 2 (by rfl) ⟨1084311, by rfl⟩ : syracuseStep 2891497 = 2168623) B2168623
theorem B6954781 : Blo 1140634 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B1711943 : Blo 1140634 1711943 := bstep (se 1 (by rfl) ⟨1283957, by rfl⟩ : syracuseStep 1711943 = 2567915) B2567915
theorem B1712027 : Blo 1140634 1712027 := bstep (se 1 (by rfl) ⟨1284020, by rfl⟩ : syracuseStep 1712027 = 2568041) B2568041
theorem B2170795 : Blo 1140634 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B24715469 : Blo 1140634 24715469 := bstep (se 3 (by rfl) ⟨4634150, by rfl⟩ : syracuseStep 24715469 = 9268301) B9268301
theorem B2171099 : Blo 1140634 2171099 := bstep (se 1 (by rfl) ⟨1628324, by rfl⟩ : syracuseStep 2171099 = 3256649) B3256649
theorem B3907865 : Blo 1140634 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B1286527 : Blo 1140634 1286527 := bstep (se 1 (by rfl) ⟨964895, by rfl⟩ : syracuseStep 1286527 = 1929791) B1929791
theorem B1712591 : Blo 1140634 1712591 := bstep (se 1 (by rfl) ⟨1284443, by rfl⟩ : syracuseStep 1712591 = 2568887) B2568887
theorem B4334057 : Blo 1140634 4334057 := bstep (se 2 (by rfl) ⟨1625271, by rfl⟩ : syracuseStep 4334057 = 3250543) B3250543
theorem B1712633 : Blo 1140634 1712633 := bstep (se 2 (by rfl) ⟨642237, by rfl⟩ : syracuseStep 1712633 = 1284475) B1284475
theorem B1712735 : Blo 1140634 1712735 := bstep (se 1 (by rfl) ⟨1284551, by rfl⟩ : syracuseStep 1712735 = 2569103) B2569103
theorem B7316335 : Blo 1140634 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B1713215 : Blo 1140634 1713215 := bstep (se 1 (by rfl) ⟨1284911, by rfl⟩ : syracuseStep 1713215 = 2569823) B2569823
theorem B1713257 : Blo 1140634 1713257 := bstep (se 2 (by rfl) ⟨642471, by rfl⟩ : syracuseStep 1713257 = 1284943) B1284943
theorem B2892905 : Blo 1140634 2892905 := bstep (se 2 (by rfl) ⟨1084839, by rfl⟩ : syracuseStep 2892905 = 2169679) B2169679
theorem B1713359 : Blo 1140634 1713359 := bstep (se 1 (by rfl) ⟨1285019, by rfl⟩ : syracuseStep 1713359 = 2570039) B2570039
theorem B3089771 : Blo 1140634 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B1713563 : Blo 1140634 1713563 := bstep (se 1 (by rfl) ⟨1285172, by rfl⟩ : syracuseStep 1713563 = 2570345) B2570345
theorem B1713785 : Blo 1140634 1713785 := bstep (se 2 (by rfl) ⟨642669, by rfl⟩ : syracuseStep 1713785 = 1285339) B1285339
theorem B13903579 : Blo 1140634 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B1713887 : Blo 1140634 1713887 := bstep (se 1 (by rfl) ⟨1285415, by rfl⟩ : syracuseStep 1713887 = 2570831) B2570831
theorem B1713983 : Blo 1140634 1713983 := bstep (se 1 (by rfl) ⟨1285487, by rfl⟩ : syracuseStep 1713983 = 2570975) B2570975
theorem B12363617 : Blo 1140634 12363617 := bstep (se 2 (by rfl) ⟨4636356, by rfl⟩ : syracuseStep 12363617 = 9272713) B9272713
theorem B1714151 : Blo 1140634 1714151 := bstep (se 1 (by rfl) ⟨1285613, by rfl⟩ : syracuseStep 1714151 = 2571227) B2571227
theorem B1714169 : Blo 1140634 1714169 := bstep (se 2 (by rfl) ⟨642813, by rfl⟩ : syracuseStep 1714169 = 1285627) B1285627
theorem B1714271 : Blo 1140634 1714271 := bstep (se 1 (by rfl) ⟨1285703, by rfl⟩ : syracuseStep 1714271 = 2571407) B2571407
theorem B1714331 : Blo 1140634 1714331 := bstep (se 1 (by rfl) ⟨1285748, by rfl⟩ : syracuseStep 1714331 = 2571497) B2571497
theorem B1714367 : Blo 1140634 1714367 := bstep (se 1 (by rfl) ⟨1285775, by rfl⟩ : syracuseStep 1714367 = 2571551) B2571551
theorem B2894039 : Blo 1140634 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B1714409 : Blo 1140634 1714409 := bstep (se 2 (by rfl) ⟨642903, by rfl⟩ : syracuseStep 1714409 = 1285807) B1285807
theorem B2566439 : Blo 1140634 2566439 := bstep (se 1 (by rfl) ⟨1924829, by rfl⟩ : syracuseStep 2566439 = 3849659) B3849659
theorem B3254575 : Blo 1140634 3254575 := bstep (se 1 (by rfl) ⟨2440931, by rfl⟩ : syracuseStep 3254575 = 4881863) B4881863
theorem B2566457 : Blo 1140634 2566457 := bstep (se 2 (by rfl) ⟨962421, by rfl⟩ : syracuseStep 2566457 = 1924843) B1924843
theorem B1714715 : Blo 1140634 1714715 := bstep (se 1 (by rfl) ⟨1286036, by rfl⟩ : syracuseStep 1714715 = 2572073) B2572073
theorem B2894363 : Blo 1140634 2894363 := bstep (se 1 (by rfl) ⟨2170772, by rfl⟩ : syracuseStep 2894363 = 4341545) B4341545
theorem B4336199 : Blo 1140634 4336199 := bstep (se 1 (by rfl) ⟨3252149, by rfl⟩ : syracuseStep 4336199 = 6504299) B6504299
theorem B1714793 : Blo 1140634 1714793 := bstep (se 2 (by rfl) ⟨643047, by rfl⟩ : syracuseStep 1714793 = 1286095) B1286095
theorem B9251435 : Blo 1140634 9251435 := bstep (se 1 (by rfl) ⟨6938576, by rfl⟩ : syracuseStep 9251435 = 13877153) B13877153
theorem B8235695 : Blo 1140634 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B1715321 : Blo 1140634 1715321 := bstep (se 2 (by rfl) ⟨643245, by rfl⟩ : syracuseStep 1715321 = 1286491) B1286491
theorem B1715423 : Blo 1140634 1715423 := bstep (se 1 (by rfl) ⟨1286567, by rfl⟩ : syracuseStep 1715423 = 2573135) B2573135
theorem B4893929 : Blo 1140634 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B1715465 : Blo 1140634 1715465 := bstep (se 2 (by rfl) ⟨643299, by rfl⟩ : syracuseStep 1715465 = 1286599) B1286599
theorem B1715567 : Blo 1140634 1715567 := bstep (se 1 (by rfl) ⟨1286675, by rfl⟩ : syracuseStep 1715567 = 2573351) B2573351
theorem B1715687 : Blo 1140634 1715687 := bstep (se 1 (by rfl) ⟨1286765, by rfl⟩ : syracuseStep 1715687 = 2573531) B2573531
theorem B2567753 : Blo 1140634 2567753 := bstep (se 2 (by rfl) ⟨962907, by rfl⟩ : syracuseStep 2567753 = 1925815) B1925815
theorem B1715819 : Blo 1140634 1715819 := bstep (se 1 (by rfl) ⟨1286864, by rfl⟩ : syracuseStep 1715819 = 2573729) B2573729
theorem B1715945 : Blo 1140634 1715945 := bstep (se 2 (by rfl) ⟨643479, by rfl⟩ : syracuseStep 1715945 = 1286959) B1286959
theorem B1716089 : Blo 1140634 1716089 := bstep (se 2 (by rfl) ⟨643533, by rfl⟩ : syracuseStep 1716089 = 1287067) B1287067
theorem B2928527 : Blo 1140634 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B1978283 : Blo 1140634 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B1716191 : Blo 1140634 1716191 := bstep (se 1 (by rfl) ⟨1287143, by rfl⟩ : syracuseStep 1716191 = 2574287) B2574287
theorem B3256307 : Blo 1140634 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B14495915 : Blo 1140634 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B1716443 : Blo 1140634 1716443 := bstep (se 1 (by rfl) ⟨1287332, by rfl⟩ : syracuseStep 1716443 = 2574665) B2574665
theorem B1716455 : Blo 1140634 1716455 := bstep (se 1 (by rfl) ⟨1287341, by rfl⟩ : syracuseStep 1716455 = 2574683) B2574683
theorem B5648669 : Blo 1140634 5648669 := bstep (se 3 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 5648669 = 2118251) B2118251
theorem B4337975 : Blo 1140634 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B6500675 : Blo 1140634 6500675 := bstep (se 1 (by rfl) ⟨4875506, by rfl⟩ : syracuseStep 6500675 = 9751013) B9751013
theorem B1716617 : Blo 1140634 1716617 := bstep (se 2 (by rfl) ⟨643731, by rfl⟩ : syracuseStep 1716617 = 1287463) B1287463
theorem B1716713 : Blo 1140634 1716713 := bstep (se 2 (by rfl) ⟨643767, by rfl⟩ : syracuseStep 1716713 = 1287535) B1287535
theorem B6500857 : Blo 1140634 6500857 := bstep (se 2 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 6500857 = 4875643) B4875643
theorem B1716839 : Blo 1140634 1716839 := bstep (se 1 (by rfl) ⟨1287629, by rfl⟩ : syracuseStep 1716839 = 2575259) B2575259
theorem B10990343 : Blo 1140634 10990343 := bstep (se 1 (by rfl) ⟨8242757, by rfl⟩ : syracuseStep 10990343 = 16485515) B16485515
theorem B2896681 : Blo 1140634 2896681 := bstep (se 2 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 2896681 = 2172511) B2172511
theorem B14627749 : Blo 1140634 14627749 := bstep (se 4 (by rfl) ⟨1371351, by rfl⟩ : syracuseStep 14627749 = 2742703) B2742703
theorem B2569211 : Blo 1140634 2569211 := bstep (se 1 (by rfl) ⟨1926908, by rfl⟩ : syracuseStep 2569211 = 3853817) B3853817
theorem B3093499 : Blo 1140634 3093499 := bstep (se 1 (by rfl) ⟨2320124, by rfl⟩ : syracuseStep 3093499 = 4640249) B4640249
theorem B29275181 : Blo 1140634 29275181 := bstep (se 3 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 29275181 = 10978193) B10978193
theorem B2569391 : Blo 1140634 2569391 := bstep (se 1 (by rfl) ⟨1927043, by rfl⟩ : syracuseStep 2569391 = 3854087) B3854087
theorem B2569427 : Blo 1140634 2569427 := bstep (se 1 (by rfl) ⟨1927070, by rfl⟩ : syracuseStep 2569427 = 3854141) B3854141
theorem B28161299 : Blo 1140634 28161299 := bstep (se 1 (by rfl) ⟨21120974, by rfl⟩ : syracuseStep 28161299 = 42241949) B42241949
theorem B2569697 : Blo 1140634 2569697 := bstep (se 2 (by rfl) ⟨963636, by rfl⟩ : syracuseStep 2569697 = 1927273) B1927273
theorem B13022855 : Blo 1140634 13022855 := bstep (se 1 (by rfl) ⟨9767141, by rfl⟩ : syracuseStep 13022855 = 19534283) B19534283
theorem B2438839 : Blo 1140634 2438839 := bstep (se 1 (by rfl) ⟨1829129, by rfl⟩ : syracuseStep 2438839 = 3658259) B3658259
theorem B3258107 : Blo 1140634 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B10991497 : Blo 1140634 10991497 := bstep (se 2 (by rfl) ⟨4121811, by rfl⟩ : syracuseStep 10991497 = 8243623) B8243623
theorem B8239067 : Blo 1140634 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B5290217 : Blo 1140634 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B31308545 : Blo 1140634 31308545 := bstep (se 2 (by rfl) ⟨11740704, by rfl⟩ : syracuseStep 31308545 = 23481409) B23481409
theorem B29637413 : Blo 1140634 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B2571335 : Blo 1140634 2571335 := bstep (se 1 (by rfl) ⟨1928501, by rfl⟩ : syracuseStep 2571335 = 3857003) B3857003
theorem B2931977 : Blo 1140634 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B2571731 : Blo 1140634 2571731 := bstep (se 1 (by rfl) ⟨1928798, by rfl⟩ : syracuseStep 2571731 = 3857597) B3857597
theorem B3128807 : Blo 1140634 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B16072199 : Blo 1140634 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B2440795 : Blo 1140634 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B2440847 : Blo 1140634 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B2572001 : Blo 1140634 2572001 := bstep (se 2 (by rfl) ⟨964500, by rfl⟩ : syracuseStep 2572001 = 1929001) B1929001
theorem B9748349 : Blo 1140634 9748349 := bstep (se 3 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 9748349 = 3655631) B3655631
theorem B12370151 : Blo 1140634 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B4637135 : Blo 1140634 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B9749099 : Blo 1140634 9749099 := bstep (se 1 (by rfl) ⟨7311824, by rfl⟩ : syracuseStep 9749099 = 14623649) B14623649
theorem B2474963 : Blo 1140634 2474963 := bstep (se 1 (by rfl) ⟨1856222, by rfl⟩ : syracuseStep 2474963 = 3712445) B3712445
theorem B4113467 : Blo 1140634 4113467 := bstep (se 1 (by rfl) ⟨3085100, by rfl⟩ : syracuseStep 4113467 = 6170201) B6170201
theorem B3851387 : Blo 1140634 3851387 := bstep (se 1 (by rfl) ⟨2888540, by rfl⟩ : syracuseStep 3851387 = 5777081) B5777081
theorem B60081425 : Blo 1140634 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B2573675 : Blo 1140634 2573675 := bstep (se 1 (by rfl) ⟨1930256, by rfl⟩ : syracuseStep 2573675 = 3860513) B3860513
theorem B3851657 : Blo 1140634 3851657 := bstep (se 2 (by rfl) ⟨1444371, by rfl⟩ : syracuseStep 3851657 = 2888743) B2888743
theorem B2573945 : Blo 1140634 2573945 := bstep (se 2 (by rfl) ⟨965229, by rfl⟩ : syracuseStep 2573945 = 1930459) B1930459
theorem B8046443 : Blo 1140634 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B3852413 : Blo 1140634 3852413 := bstep (se 3 (by rfl) ⟨722327, by rfl⟩ : syracuseStep 3852413 = 1444655) B1444655
theorem B3852683 : Blo 1140634 3852683 := bstep (se 1 (by rfl) ⟨2889512, by rfl⟩ : syracuseStep 3852683 = 5779025) B5779025
theorem B2574953 : Blo 1140634 2574953 := bstep (se 2 (by rfl) ⟨965607, by rfl⟩ : syracuseStep 2574953 = 1931215) B1931215
theorem B14634107 : Blo 1140634 14634107 := bstep (se 1 (by rfl) ⟨10975580, by rfl⟩ : syracuseStep 14634107 = 21951161) B21951161
theorem B3656927 : Blo 1140634 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B13028687 : Blo 1140634 13028687 := bstep (se 1 (by rfl) ⟨9771515, by rfl⟩ : syracuseStep 13028687 = 19543031) B19543031
theorem B3657143 : Blo 1140634 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B6507965 : Blo 1140634 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B9752075 : Blo 1140634 9752075 := bstep (se 1 (by rfl) ⟨7314056, by rfl⟩ : syracuseStep 9752075 = 14628113) B14628113
theorem B4345721 : Blo 1140634 4345721 := bstep (se 2 (by rfl) ⟨1629645, by rfl⟩ : syracuseStep 4345721 = 3259291) B3259291
theorem B3854303 : Blo 1140634 3854303 := bstep (se 1 (by rfl) ⟨2890727, by rfl⟩ : syracuseStep 3854303 = 5781455) B5781455
theorem B3854465 : Blo 1140634 3854465 := bstep (se 2 (by rfl) ⟨1445424, by rfl⟩ : syracuseStep 3854465 = 2890849) B2890849
theorem B1626331 : Blo 1140634 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B8245469 : Blo 1140634 8245469 := bstep (se 3 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 8245469 = 3092051) B3092051
theorem B3854951 : Blo 1140634 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B2741033 : Blo 1140634 2741033 := bstep (se 2 (by rfl) ⟨1027887, by rfl⟩ : syracuseStep 2741033 = 2055775) B2055775
theorem B9753473 : Blo 1140634 9753473 := bstep (se 2 (by rfl) ⟨3657552, by rfl⟩ : syracuseStep 9753473 = 7315105) B7315105
theorem B3855275 : Blo 1140634 3855275 := bstep (se 1 (by rfl) ⟨2891456, by rfl⟩ : syracuseStep 3855275 = 5782913) B5782913
theorem B24728615 : Blo 1140634 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B9884753 : Blo 1140634 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B3855707 : Blo 1140634 3855707 := bstep (se 1 (by rfl) ⟨2891780, by rfl⟩ : syracuseStep 3855707 = 5783561) B5783561
theorem B3855815 : Blo 1140634 3855815 := bstep (se 1 (by rfl) ⟨2891861, by rfl⟩ : syracuseStep 3855815 = 5783723) B5783723
theorem B3856139 : Blo 1140634 3856139 := bstep (se 1 (by rfl) ⟨2892104, by rfl⟩ : syracuseStep 3856139 = 5784209) B5784209
theorem B3856409 : Blo 1140634 3856409 := bstep (se 2 (by rfl) ⟨1446153, by rfl⟩ : syracuseStep 3856409 = 2892307) B2892307
theorem B1235039 : Blo 1140634 1235039 := bstep (se 1 (by rfl) ⟨926279, by rfl⟩ : syracuseStep 1235039 = 1852559) B1852559
theorem B74111111 : Blo 1140634 74111111 := bstep (se 1 (by rfl) ⟨55583333, by rfl⟩ : syracuseStep 74111111 = 111166667) B111166667
theorem B4118771 : Blo 1140634 4118771 := bstep (se 1 (by rfl) ⟨3089078, by rfl⟩ : syracuseStep 4118771 = 6178157) B6178157
theorem B7330277 : Blo 1140634 7330277 := bstep (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) B1374427
theorem B5790365 : Blo 1140634 5790365 := bstep (se 3 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 5790365 = 2171387) B2171387
theorem B1629019 : Blo 1140634 1629019 := bstep (se 1 (by rfl) ⟨1221764, by rfl⟩ : syracuseStep 1629019 = 2443529) B2443529
theorem B5790689 : Blo 1140634 5790689 := bstep (se 2 (by rfl) ⟨2171508, by rfl⟩ : syracuseStep 5790689 = 4343017) B4343017
theorem B4119767 : Blo 1140634 4119767 := bstep (se 1 (by rfl) ⟨3089825, by rfl⟩ : syracuseStep 4119767 = 6179651) B6179651
theorem B3857759 : Blo 1140634 3857759 := bstep (se 1 (by rfl) ⟨2893319, by rfl⟩ : syracuseStep 3857759 = 5786639) B5786639
theorem B7331303 : Blo 1140634 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B6512339 : Blo 1140634 6512339 := bstep (se 1 (by rfl) ⟨4884254, by rfl⟩ : syracuseStep 6512339 = 9768509) B9768509
theorem B4874039 : Blo 1140634 4874039 := bstep (se 1 (by rfl) ⟨3655529, by rfl⟩ : syracuseStep 4874039 = 7311059) B7311059
theorem B15621983 : Blo 1140634 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B1924985 : Blo 1140634 1924985 := bstep (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) B1443739
theorem B3858299 : Blo 1140634 3858299 := bstep (se 1 (by rfl) ⟨2893724, by rfl⟩ : syracuseStep 3858299 = 5787449) B5787449
theorem B3661757 : Blo 1140634 3661757 := bstep (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) B1373159
theorem B16506919 : Blo 1140634 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B3858785 : Blo 1140634 3858785 := bstep (se 2 (by rfl) ⟨1447044, by rfl⟩ : syracuseStep 3858785 = 2894089) B2894089
theorem B15655265 : Blo 1140634 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B6939067 : Blo 1140634 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B3662603 : Blo 1140634 3662603 := bstep (se 1 (by rfl) ⟨2746952, by rfl⟩ : syracuseStep 3662603 = 5493905) B5493905
theorem B27779993 : Blo 1140634 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B1926139 : Blo 1140634 1926139 := bstep (se 1 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 1926139 = 2889209) B2889209
theorem B5792957 : Blo 1140634 5792957 := bstep (se 3 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 5792957 = 2172359) B2172359
theorem B1926571 : Blo 1140634 1926571 := bstep (se 1 (by rfl) ⟨1444928, by rfl⟩ : syracuseStep 1926571 = 2889857) B2889857
theorem B1926767 : Blo 1140634 1926767 := bstep (se 1 (by rfl) ⟨1445075, by rfl⟩ : syracuseStep 1926767 = 2890151) B2890151
theorem B3860135 : Blo 1140634 3860135 := bstep (se 1 (by rfl) ⟨2895101, by rfl⟩ : syracuseStep 3860135 = 5790203) B5790203
theorem B1926875 : Blo 1140634 1926875 := bstep (se 1 (by rfl) ⟨1445156, by rfl⟩ : syracuseStep 1926875 = 2890313) B2890313
theorem B6514505 : Blo 1140634 6514505 := bstep (se 2 (by rfl) ⟨2442939, by rfl⟩ : syracuseStep 6514505 = 4885879) B4885879
theorem B1927111 : Blo 1140634 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B1140719 : Blo 1140634 1140719 := bstep (se 1 (by rfl) ⟨855539, by rfl⟩ : syracuseStep 1140719 = 1711079) B1711079
theorem B2058383 : Blo 1140634 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B1140891 : Blo 1140634 1140891 := bstep (se 1 (by rfl) ⟨855668, by rfl⟩ : syracuseStep 1140891 = 1711337) B1711337
theorem B1140927 : Blo 1140634 1140927 := bstep (se 1 (by rfl) ⟨855695, by rfl⟩ : syracuseStep 1140927 = 1711391) B1711391
theorem B3860729 : Blo 1140634 3860729 := bstep (se 2 (by rfl) ⟨1447773, by rfl⟩ : syracuseStep 3860729 = 2895547) B2895547
theorem B1141039 : Blo 1140634 1141039 := bstep (se 1 (by rfl) ⟨855779, by rfl⟩ : syracuseStep 1141039 = 1711559) B1711559
theorem B3860783 : Blo 1140634 3860783 := bstep (se 1 (by rfl) ⟨2895587, by rfl⟩ : syracuseStep 3860783 = 5791175) B5791175
theorem B3860999 : Blo 1140634 3860999 := bstep (se 1 (by rfl) ⟨2895749, by rfl⟩ : syracuseStep 3860999 = 5791499) B5791499
theorem B1141275 : Blo 1140634 1141275 := bstep (se 1 (by rfl) ⟨855956, by rfl⟩ : syracuseStep 1141275 = 1711913) B1711913
theorem B1141279 : Blo 1140634 1141279 := bstep (se 1 (by rfl) ⟨855959, by rfl⟩ : syracuseStep 1141279 = 1711919) B1711919
theorem B1927867 : Blo 1140634 1927867 := bstep (se 1 (by rfl) ⟨1445900, by rfl⟩ : syracuseStep 1927867 = 2891801) B2891801
theorem B1141595 : Blo 1140634 1141595 := bstep (se 1 (by rfl) ⟨856196, by rfl⟩ : syracuseStep 1141595 = 1712393) B1712393
theorem B253488017 : Blo 1140634 253488017 := bstep (se 2 (by rfl) ⟨95058006, by rfl⟩ : syracuseStep 253488017 = 190116013) B190116013
theorem B1141663 : Blo 1140634 1141663 := bstep (se 1 (by rfl) ⟨856247, by rfl⟩ : syracuseStep 1141663 = 1712495) B1712495
theorem B12348395 : Blo 1140634 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B1928171 : Blo 1140634 1928171 := bstep (se 1 (by rfl) ⟨1446128, by rfl⟩ : syracuseStep 1928171 = 2892257) B2892257
theorem B1141807 : Blo 1140634 1141807 := bstep (se 1 (by rfl) ⟨856355, by rfl⟩ : syracuseStep 1141807 = 1712711) B1712711
theorem B1141831 : Blo 1140634 1141831 := bstep (se 1 (by rfl) ⟨856373, by rfl⟩ : syracuseStep 1141831 = 1712747) B1712747
theorem B16706699 : Blo 1140634 16706699 := bstep (se 1 (by rfl) ⟨12530024, by rfl⟩ : syracuseStep 16706699 = 25060049) B25060049
theorem B4877455 : Blo 1140634 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B3861647 : Blo 1140634 3861647 := bstep (se 1 (by rfl) ⟨2896235, by rfl⟩ : syracuseStep 3861647 = 5792471) B5792471
theorem B1830071 : Blo 1140634 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B1141983 : Blo 1140634 1141983 := bstep (se 1 (by rfl) ⟨856487, by rfl⟩ : syracuseStep 1141983 = 1712975) B1712975
theorem B55569725 : Blo 1140634 55569725 := bstep (se 3 (by rfl) ⟨10419323, by rfl⟩ : syracuseStep 55569725 = 20838647) B20838647
theorem B1142247 : Blo 1140634 1142247 := bstep (se 1 (by rfl) ⟨856685, by rfl⟩ : syracuseStep 1142247 = 1713371) B1713371
theorem B3862079 : Blo 1140634 3862079 := bstep (se 1 (by rfl) ⟨2896559, by rfl⟩ : syracuseStep 3862079 = 5793119) B5793119
theorem B1142363 : Blo 1140634 1142363 := bstep (se 1 (by rfl) ⟨856772, by rfl⟩ : syracuseStep 1142363 = 1713545) B1713545
theorem B27815723 : Blo 1140634 27815723 := bstep (se 1 (by rfl) ⟨20861792, by rfl⟩ : syracuseStep 27815723 = 41723585) B41723585
theorem B1142599 : Blo 1140634 1142599 := bstep (se 1 (by rfl) ⟨856949, by rfl⟩ : syracuseStep 1142599 = 1713899) B1713899
theorem B3665807 : Blo 1140634 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B1830827 : Blo 1140634 1830827 := bstep (se 1 (by rfl) ⟨1373120, by rfl⟩ : syracuseStep 1830827 = 2746241) B2746241
theorem B1142751 : Blo 1140634 1142751 := bstep (se 1 (by rfl) ⟨857063, by rfl⟩ : syracuseStep 1142751 = 1714127) B1714127
theorem B1143015 : Blo 1140634 1143015 := bstep (se 1 (by rfl) ⟨857261, by rfl⟩ : syracuseStep 1143015 = 1714523) B1714523
theorem B3862781 : Blo 1140634 3862781 := bstep (se 3 (by rfl) ⟨724271, by rfl⟩ : syracuseStep 3862781 = 1448543) B1448543
theorem B3469679 : Blo 1140634 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B1143167 : Blo 1140634 1143167 := bstep (se 1 (by rfl) ⟨857375, by rfl⟩ : syracuseStep 1143167 = 1714751) B1714751
theorem B1143247 : Blo 1140634 1143247 := bstep (se 1 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 1143247 = 1714871) B1714871
theorem B2060777 : Blo 1140634 2060777 := bstep (se 2 (by rfl) ⟨772791, by rfl⟩ : syracuseStep 2060777 = 1545583) B1545583
theorem B6943247 : Blo 1140634 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B1831519 : Blo 1140634 1831519 := bstep (se 1 (by rfl) ⟨1373639, by rfl⟩ : syracuseStep 1831519 = 2747279) B2747279
theorem B1143399 : Blo 1140634 1143399 := bstep (se 1 (by rfl) ⟨857549, by rfl⟩ : syracuseStep 1143399 = 1715099) B1715099
theorem B31224467 : Blo 1140634 31224467 := bstep (se 1 (by rfl) ⟨23418350, by rfl⟩ : syracuseStep 31224467 = 46836701) B46836701
theorem B1143663 : Blo 1140634 1143663 := bstep (se 1 (by rfl) ⟨857747, by rfl⟩ : syracuseStep 1143663 = 1715495) B1715495
theorem B1143719 : Blo 1140634 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B1143803 : Blo 1140634 1143803 := bstep (se 1 (by rfl) ⟨857852, by rfl⟩ : syracuseStep 1143803 = 1715705) B1715705
theorem B1143871 : Blo 1140634 1143871 := bstep (se 1 (by rfl) ⟨857903, by rfl⟩ : syracuseStep 1143871 = 1715807) B1715807
theorem B2749547 : Blo 1140634 2749547 := bstep (se 1 (by rfl) ⟨2062160, by rfl⟩ : syracuseStep 2749547 = 4124321) B4124321
theorem B1144015 : Blo 1140634 1144015 := bstep (se 1 (by rfl) ⟨858011, by rfl⟩ : syracuseStep 1144015 = 1716023) B1716023
theorem B1144219 : Blo 1140634 1144219 := bstep (se 1 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 1144219 = 1716329) B1716329
theorem B6518171 : Blo 1140634 6518171 := bstep (se 1 (by rfl) ⟨4888628, by rfl⟩ : syracuseStep 6518171 = 9777257) B9777257
theorem B1832519 : Blo 1140634 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B1144431 : Blo 1140634 1144431 := bstep (se 1 (by rfl) ⟨858323, by rfl⟩ : syracuseStep 1144431 = 1716647) B1716647
theorem B1144487 : Blo 1140634 1144487 := bstep (se 1 (by rfl) ⟨858365, by rfl⟩ : syracuseStep 1144487 = 1716731) B1716731
theorem B1144571 : Blo 1140634 1144571 := bstep (se 1 (by rfl) ⟨858428, by rfl⟩ : syracuseStep 1144571 = 1716857) B1716857
theorem B1144607 : Blo 1140634 1144607 := bstep (se 1 (by rfl) ⟨858455, by rfl⟩ : syracuseStep 1144607 = 1716911) B1716911
theorem B1931087 : Blo 1140634 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B3471457 : Blo 1140634 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B24706471 : Blo 1140634 24706471 := bstep (se 1 (by rfl) ⟨18529853, by rfl⟩ : syracuseStep 24706471 = 37059707) B37059707
theorem B10420973 : Blo 1140634 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B13173749 : Blo 1140634 13173749 := bstep (se 5 (by rfl) ⟨617519, by rfl⟩ : syracuseStep 13173749 = 1235039) B1235039
theorem B1444063 : Blo 1140634 1444063 := bstep (se 1 (by rfl) ⟨1083047, by rfl⟩ : syracuseStep 1444063 = 2166095) B2166095
theorem B8685791 : Blo 1140634 8685791 := bstep (se 1 (by rfl) ⟨6514343, by rfl⟩ : syracuseStep 8685791 = 13028687) B13028687
theorem B2165935 : Blo 1140634 2165935 := bstep (se 1 (by rfl) ⟨1624451, by rfl⟩ : syracuseStep 2165935 = 3248903) B3248903
theorem B9768235 : Blo 1140634 9768235 := bstep (se 1 (by rfl) ⟨7326176, by rfl⟩ : syracuseStep 9768235 = 14652353) B14652353
theorem B16485743 : Blo 1140634 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B6589835 : Blo 1140634 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B1445951 : Blo 1140634 1445951 := bstep (se 1 (by rfl) ⟨1084463, by rfl⟩ : syracuseStep 1445951 = 2168927) B2168927
theorem B2035867 : Blo 1140634 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B2232481 : Blo 1140634 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B2888531 : Blo 1140634 2888531 := bstep (se 1 (by rfl) ⟨2166398, by rfl⟩ : syracuseStep 2888531 = 4332797) B4332797
theorem B4887535 : Blo 1140634 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B3249359 : Blo 1140634 3249359 := bstep (se 1 (by rfl) ⟨2437019, by rfl⟩ : syracuseStep 3249359 = 4874039) B4874039
theorem B1283323 : Blo 1140634 1283323 := bstep (se 1 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 1283323 = 1924985) B1924985
theorem B1447399 : Blo 1140634 1447399 := bstep (se 1 (by rfl) ⟨1085549, by rfl⟩ : syracuseStep 1447399 = 2171099) B2171099
theorem B2168441 : Blo 1140634 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B2889371 : Blo 1140634 2889371 := bstep (se 1 (by rfl) ⟨2167028, by rfl⟩ : syracuseStep 2889371 = 4334057) B4334057
theorem B18519995 : Blo 1140634 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B4331657 : Blo 1140634 4331657 := bstep (se 2 (by rfl) ⟨1624371, by rfl⟩ : syracuseStep 4331657 = 3248743) B3248743
theorem B1284511 : Blo 1140634 1284511 := bstep (se 1 (by rfl) ⟨963383, by rfl⟩ : syracuseStep 1284511 = 1926767) B1926767
theorem B1284583 : Blo 1140634 1284583 := bstep (se 1 (by rfl) ⟨963437, by rfl⟩ : syracuseStep 1284583 = 1926875) B1926875
theorem B19503665 : Blo 1140634 19503665 := bstep (se 2 (by rfl) ⟨7313874, by rfl⟩ : syracuseStep 19503665 = 14627749) B14627749
theorem B1710959 : Blo 1140634 1710959 := bstep (se 1 (by rfl) ⟨1283219, by rfl⟩ : syracuseStep 1710959 = 2566439) B2566439
theorem B1710971 : Blo 1140634 1710971 := bstep (se 1 (by rfl) ⟨1283228, by rfl⟩ : syracuseStep 1710971 = 2566457) B2566457
theorem B2890799 : Blo 1140634 2890799 := bstep (se 1 (by rfl) ⟨2168099, by rfl⟩ : syracuseStep 2890799 = 4336199) B4336199
theorem B6167623 : Blo 1140634 6167623 := bstep (se 1 (by rfl) ⟨4625717, by rfl⟩ : syracuseStep 6167623 = 9251435) B9251435
theorem B21961853 : Blo 1140634 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B168992011 : Blo 1140634 168992011 := bstep (se 1 (by rfl) ⟨126744008, by rfl⟩ : syracuseStep 168992011 = 253488017) B253488017
theorem B8232263 : Blo 1140634 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B1285447 : Blo 1140634 1285447 := bstep (se 1 (by rfl) ⟨964085, by rfl⟩ : syracuseStep 1285447 = 1928171) B1928171
theorem B3251785 : Blo 1140634 3251785 := bstep (se 2 (by rfl) ⟨1219419, by rfl⟩ : syracuseStep 3251785 = 2438839) B2438839
theorem B1711835 : Blo 1140634 1711835 := bstep (se 1 (by rfl) ⟨1283876, by rfl⟩ : syracuseStep 1711835 = 2567753) B2567753
theorem B14655329 : Blo 1140634 14655329 := bstep (se 2 (by rfl) ⟨5495748, by rfl⟩ : syracuseStep 14655329 = 10991497) B10991497
theorem B1220551 : Blo 1140634 1220551 := bstep (se 1 (by rfl) ⟨915413, by rfl⟩ : syracuseStep 1220551 = 1830827) B1830827
theorem B1712105 : Blo 1140634 1712105 := bstep (se 2 (by rfl) ⟨642039, by rfl⟩ : syracuseStep 1712105 = 1284079) B1284079
theorem B2170871 : Blo 1140634 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B4333601 : Blo 1140634 4333601 := bstep (se 2 (by rfl) ⟨1625100, by rfl⟩ : syracuseStep 4333601 = 3250201) B3250201
theorem B4628609 : Blo 1140634 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B2891983 : Blo 1140634 2891983 := bstep (se 1 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 2891983 = 4337975) B4337975
theorem B4333783 : Blo 1140634 4333783 := bstep (se 1 (by rfl) ⟨3250337, by rfl⟩ : syracuseStep 4333783 = 6500675) B6500675
theorem B4628831 : Blo 1140634 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B20816311 : Blo 1140634 20816311 := bstep (se 1 (by rfl) ⟨15612233, by rfl⟩ : syracuseStep 20816311 = 31224467) B31224467
theorem B1712807 : Blo 1140634 1712807 := bstep (se 1 (by rfl) ⟨1284605, by rfl⟩ : syracuseStep 1712807 = 2569211) B2569211
theorem B1712927 : Blo 1140634 1712927 := bstep (se 1 (by rfl) ⟨1284695, by rfl⟩ : syracuseStep 1712927 = 2569391) B2569391
theorem B1712951 : Blo 1140634 1712951 := bstep (se 1 (by rfl) ⟨1284713, by rfl⟩ : syracuseStep 1712951 = 2569427) B2569427
theorem B3253117 : Blo 1140634 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B1713131 : Blo 1140634 1713131 := bstep (se 1 (by rfl) ⟨1284848, by rfl⟩ : syracuseStep 1713131 = 2569697) B2569697
theorem B1221679 : Blo 1140634 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B2172025 : Blo 1140634 2172025 := bstep (se 2 (by rfl) ⟨814509, by rfl⟩ : syracuseStep 2172025 = 1629019) B1629019
theorem B2172071 : Blo 1140634 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B1287391 : Blo 1140634 1287391 := bstep (se 1 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 1287391 = 1931087) B1931087
theorem B35137385 : Blo 1140634 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B32941961 : Blo 1140634 32941961 := bstep (se 2 (by rfl) ⟨12353235, by rfl⟩ : syracuseStep 32941961 = 24706471) B24706471
theorem B1714223 : Blo 1140634 1714223 := bstep (se 1 (by rfl) ⟨1285667, by rfl⟩ : syracuseStep 1714223 = 2571335) B2571335
theorem B3254393 : Blo 1140634 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B1714487 : Blo 1140634 1714487 := bstep (se 1 (by rfl) ⟨1285865, by rfl⟩ : syracuseStep 1714487 = 2571731) B2571731
theorem B1714667 : Blo 1140634 1714667 := bstep (se 1 (by rfl) ⟨1286000, by rfl⟩ : syracuseStep 1714667 = 2572001) B2572001
theorem B2894393 : Blo 1140634 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B6498899 : Blo 1140634 6498899 := bstep (se 1 (by rfl) ⟨4874174, by rfl⟩ : syracuseStep 6498899 = 9748349) B9748349
theorem B6499399 : Blo 1140634 6499399 := bstep (se 1 (by rfl) ⟨4874549, by rfl⟩ : syracuseStep 6499399 = 9749099) B9749099
theorem B1715369 : Blo 1140634 1715369 := bstep (se 2 (by rfl) ⟨643263, by rfl⟩ : syracuseStep 1715369 = 1286527) B1286527
theorem B9252089 : Blo 1140634 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B1649975 : Blo 1140634 1649975 := bstep (se 1 (by rfl) ⟨1237481, by rfl⟩ : syracuseStep 1649975 = 2474963) B2474963
theorem B2567591 : Blo 1140634 2567591 := bstep (se 1 (by rfl) ⟨1925693, by rfl⟩ : syracuseStep 2567591 = 3851387) B3851387
theorem B40054283 : Blo 1140634 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B1715783 : Blo 1140634 1715783 := bstep (se 1 (by rfl) ⟨1286837, by rfl⟩ : syracuseStep 1715783 = 2573675) B2573675
theorem B2567771 : Blo 1140634 2567771 := bstep (se 1 (by rfl) ⟨1925828, by rfl⟩ : syracuseStep 2567771 = 3851657) B3851657
theorem B1715963 : Blo 1140634 1715963 := bstep (se 1 (by rfl) ⟨1286972, by rfl⟩ : syracuseStep 1715963 = 2573945) B2573945
theorem B12365693 : Blo 1140634 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B2568185 : Blo 1140634 2568185 := bstep (se 2 (by rfl) ⟨963069, by rfl⟩ : syracuseStep 2568185 = 1926139) B1926139
theorem B2568275 : Blo 1140634 2568275 := bstep (se 1 (by rfl) ⟨1926206, by rfl⟩ : syracuseStep 2568275 = 3852413) B3852413
theorem B2568455 : Blo 1140634 2568455 := bstep (se 1 (by rfl) ⟨1926341, by rfl⟩ : syracuseStep 2568455 = 3852683) B3852683
theorem B1716635 : Blo 1140634 1716635 := bstep (se 1 (by rfl) ⟨1287476, by rfl⟩ : syracuseStep 1716635 = 2574953) B2574953
theorem B13906349 : Blo 1140634 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B2568761 : Blo 1140634 2568761 := bstep (se 2 (by rfl) ⟨963285, by rfl⟩ : syracuseStep 2568761 = 1926571) B1926571
theorem B2437951 : Blo 1140634 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B2438095 : Blo 1140634 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B4338643 : Blo 1140634 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B6501383 : Blo 1140634 6501383 := bstep (se 1 (by rfl) ⟨4876037, by rfl⟩ : syracuseStep 6501383 = 9752075) B9752075
theorem B2897147 : Blo 1140634 2897147 := bstep (se 1 (by rfl) ⟨2172860, by rfl⟩ : syracuseStep 2897147 = 4345721) B4345721
theorem B2569481 : Blo 1140634 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B4830475 : Blo 1140634 4830475 := bstep (se 1 (by rfl) ⟨3622856, by rfl⟩ : syracuseStep 4830475 = 7245713) B7245713
theorem B2569535 : Blo 1140634 2569535 := bstep (se 1 (by rfl) ⟨1927151, by rfl⟩ : syracuseStep 2569535 = 3854303) B3854303
theorem B2569643 : Blo 1140634 2569643 := bstep (se 1 (by rfl) ⟨1927232, by rfl⟩ : syracuseStep 2569643 = 3854465) B3854465
theorem B22001219 : Blo 1140634 22001219 := bstep (se 1 (by rfl) ⟨16500914, by rfl⟩ : syracuseStep 22001219 = 33001829) B33001829
theorem B4339433 : Blo 1140634 4339433 := bstep (se 2 (by rfl) ⟨1627287, by rfl⟩ : syracuseStep 4339433 = 3254575) B3254575
theorem B2569967 : Blo 1140634 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B6502315 : Blo 1140634 6502315 := bstep (se 1 (by rfl) ⟨4876736, by rfl⟩ : syracuseStep 6502315 = 9753473) B9753473
theorem B2570183 : Blo 1140634 2570183 := bstep (se 1 (by rfl) ⟨1927637, by rfl⟩ : syracuseStep 2570183 = 3855275) B3855275
theorem B5486791 : Blo 1140634 5486791 := bstep (se 1 (by rfl) ⟨4115093, by rfl⟩ : syracuseStep 5486791 = 8230187) B8230187
theorem B2570471 : Blo 1140634 2570471 := bstep (se 1 (by rfl) ⟨1927853, by rfl⟩ : syracuseStep 2570471 = 3855707) B3855707
theorem B2570489 : Blo 1140634 2570489 := bstep (se 2 (by rfl) ⟨963933, by rfl⟩ : syracuseStep 2570489 = 1927867) B1927867
theorem B2570543 : Blo 1140634 2570543 := bstep (se 1 (by rfl) ⟨1927907, by rfl⟩ : syracuseStep 2570543 = 3855815) B3855815
theorem B2570759 : Blo 1140634 2570759 := bstep (se 1 (by rfl) ⟨1928069, by rfl⟩ : syracuseStep 2570759 = 3856139) B3856139
theorem B21936703 : Blo 1140634 21936703 := bstep (se 1 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 21936703 = 32905055) B32905055
theorem B2570939 : Blo 1140634 2570939 := bstep (se 1 (by rfl) ⟨1928204, by rfl⟩ : syracuseStep 2570939 = 3856409) B3856409
theorem B6503273 : Blo 1140634 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B3521447 : Blo 1140634 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B2571839 : Blo 1140634 2571839 := bstep (se 1 (by rfl) ⟨1928879, by rfl⟩ : syracuseStep 2571839 = 3857759) B3857759
theorem B4341559 : Blo 1140634 4341559 := bstep (se 1 (by rfl) ⟨3256169, by rfl⟩ : syracuseStep 4341559 = 6512339) B6512339
theorem B2572199 : Blo 1140634 2572199 := bstep (se 1 (by rfl) ⟨1929149, by rfl⟩ : syracuseStep 2572199 = 3858299) B3858299
theorem B2441171 : Blo 1140634 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B2572523 : Blo 1140634 2572523 := bstep (se 1 (by rfl) ⟨1929392, by rfl⟩ : syracuseStep 2572523 = 3858785) B3858785
theorem B10436843 : Blo 1140634 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B5489021 : Blo 1140634 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B2441735 : Blo 1140634 2441735 := bstep (se 1 (by rfl) ⟨1831301, by rfl⟩ : syracuseStep 2441735 = 3662603) B3662603
theorem B8667809 : Blo 1140634 8667809 := bstep (se 2 (by rfl) ⟨3250428, by rfl⟩ : syracuseStep 8667809 = 6500857) B6500857
theorem B2442025 : Blo 1140634 2442025 := bstep (se 2 (by rfl) ⟨915759, by rfl⟩ : syracuseStep 2442025 = 1831519) B1831519
theorem B2573423 : Blo 1140634 2573423 := bstep (se 1 (by rfl) ⟨1930067, by rfl⟩ : syracuseStep 2573423 = 3860135) B3860135
theorem B4343003 : Blo 1140634 4343003 := bstep (se 1 (by rfl) ⟨3257252, by rfl⟩ : syracuseStep 4343003 = 6514505) B6514505
theorem B8242411 : Blo 1140634 8242411 := bstep (se 1 (by rfl) ⟨6181808, by rfl⟩ : syracuseStep 8242411 = 12363617) B12363617
theorem B19547405 : Blo 1140634 19547405 := bstep (se 3 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 19547405 = 7330277) B7330277
theorem B2573819 : Blo 1140634 2573819 := bstep (se 1 (by rfl) ⟨1930364, by rfl⟩ : syracuseStep 2573819 = 3860729) B3860729
theorem B2573855 : Blo 1140634 2573855 := bstep (se 1 (by rfl) ⟨1930391, by rfl⟩ : syracuseStep 2573855 = 3860783) B3860783
theorem B2573999 : Blo 1140634 2573999 := bstep (se 1 (by rfl) ⟨1930499, by rfl⟩ : syracuseStep 2573999 = 3860999) B3860999
theorem B2574431 : Blo 1140634 2574431 := bstep (se 1 (by rfl) ⟨1930823, by rfl⟩ : syracuseStep 2574431 = 3861647) B3861647
theorem B3262619 : Blo 1140634 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B37046483 : Blo 1140634 37046483 := bstep (se 1 (by rfl) ⟨27784862, by rfl⟩ : syracuseStep 37046483 = 55569725) B55569725
theorem B2574719 : Blo 1140634 2574719 := bstep (se 1 (by rfl) ⟨1931039, by rfl⟩ : syracuseStep 2574719 = 3862079) B3862079
theorem B1952351 : Blo 1140634 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B2443871 : Blo 1140634 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B1624873 : Blo 1140634 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B2575187 : Blo 1140634 2575187 := bstep (se 1 (by rfl) ⟨1931390, by rfl⟩ : syracuseStep 2575187 = 3862781) B3862781
theorem B2313119 : Blo 1140634 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B7326895 : Blo 1140634 7326895 := bstep (se 1 (by rfl) ⟨5495171, by rfl⟩ : syracuseStep 7326895 = 10990343) B10990343
theorem B11717885 : Blo 1140634 11717885 := bstep (se 3 (by rfl) ⟨2197103, by rfl⟩ : syracuseStep 11717885 = 4394207) B4394207
theorem B19516787 : Blo 1140634 19516787 := bstep (se 1 (by rfl) ⟨14637590, by rfl⟩ : syracuseStep 19516787 = 29275181) B29275181
theorem B1625465 : Blo 1140634 1625465 := bstep (se 2 (by rfl) ⟨609549, by rfl⟩ : syracuseStep 1625465 = 1219099) B1219099
theorem B11718041 : Blo 1140634 11718041 := bstep (se 2 (by rfl) ⟨4394265, by rfl⟩ : syracuseStep 11718041 = 8788531) B8788531
theorem B4345447 : Blo 1140634 4345447 := bstep (se 1 (by rfl) ⟨3259085, by rfl⟩ : syracuseStep 4345447 = 6518171) B6518171
theorem B5492711 : Blo 1140634 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B3526811 : Blo 1140634 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B1954651 : Blo 1140634 1954651 := bstep (se 1 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 1954651 = 2931977) B2931977
theorem B3855329 : Blo 1140634 3855329 := bstep (se 2 (by rfl) ⟨1445748, by rfl⟩ : syracuseStep 3855329 = 2891497) B2891497
theorem B2085871 : Blo 1140634 2085871 := bstep (se 1 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 2085871 = 3128807) B3128807
theorem B1627231 : Blo 1140634 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B8246767 : Blo 1140634 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B88036901 : Blo 1140634 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B3299143 : Blo 1140634 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B2742311 : Blo 1140634 2742311 := bstep (se 1 (by rfl) ⟨2056733, by rfl⟩ : syracuseStep 2742311 = 4113467) B4113467
theorem B2316575 : Blo 1140634 2316575 := bstep (se 1 (by rfl) ⟨1737431, by rfl⟩ : syracuseStep 2316575 = 3474863) B3474863
theorem B9755113 : Blo 1140634 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B4873031 : Blo 1140634 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B4939115 : Blo 1140634 4939115 := bstep (se 1 (by rfl) ⟨3704336, by rfl⟩ : syracuseStep 4939115 = 7408673) B7408673
theorem B9756071 : Blo 1140634 9756071 := bstep (se 1 (by rfl) ⟨7317053, by rfl⟩ : syracuseStep 9756071 = 14634107) B14634107
theorem B18538105 : Blo 1140634 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B4874003 : Blo 1140634 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B5496979 : Blo 1140634 5496979 := bstep (se 1 (by rfl) ⟨4122734, by rfl⟩ : syracuseStep 5496979 = 8245469) B8245469
theorem B1827355 : Blo 1140634 1827355 := bstep (se 1 (by rfl) ⟨1370516, by rfl⟩ : syracuseStep 1827355 = 2741033) B2741033
theorem B49407407 : Blo 1140634 49407407 := bstep (se 1 (by rfl) ⟨37055555, by rfl⟩ : syracuseStep 49407407 = 74111111) B74111111
theorem B2745847 : Blo 1140634 2745847 := bstep (se 1 (by rfl) ⟨2059385, by rfl⟩ : syracuseStep 2745847 = 4118771) B4118771
theorem B3860243 : Blo 1140634 3860243 := bstep (se 1 (by rfl) ⟨2895182, by rfl⟩ : syracuseStep 3860243 = 5790365) B5790365
theorem B1140671 : Blo 1140634 1140671 := bstep (se 1 (by rfl) ⟨855503, by rfl⟩ : syracuseStep 1140671 = 1711007) B1711007
theorem B1140703 : Blo 1140634 1140703 := bstep (se 1 (by rfl) ⟨855527, by rfl⟩ : syracuseStep 1140703 = 1711055) B1711055
theorem B3860459 : Blo 1140634 3860459 := bstep (se 1 (by rfl) ⟨2895344, by rfl⟩ : syracuseStep 3860459 = 5790689) B5790689
theorem B1140763 : Blo 1140634 1140763 := bstep (se 1 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 1140763 = 1711145) B1711145
theorem B1140767 : Blo 1140634 1140767 := bstep (se 1 (by rfl) ⟨855575, by rfl⟩ : syracuseStep 1140767 = 1711151) B1711151
theorem B1140783 : Blo 1140634 1140783 := bstep (se 1 (by rfl) ⟨855587, by rfl⟩ : syracuseStep 1140783 = 1711175) B1711175
theorem B2746511 : Blo 1140634 2746511 := bstep (se 1 (by rfl) ⟨2059883, by rfl⟩ : syracuseStep 2746511 = 4119767) B4119767
theorem B1140959 : Blo 1140634 1140959 := bstep (se 1 (by rfl) ⟨855719, by rfl⟩ : syracuseStep 1140959 = 1711439) B1711439
theorem B1141019 : Blo 1140634 1141019 := bstep (se 1 (by rfl) ⟨855764, by rfl⟩ : syracuseStep 1141019 = 1711529) B1711529
theorem B21457181 : Blo 1140634 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B1141119 : Blo 1140634 1141119 := bstep (se 1 (by rfl) ⟨855839, by rfl⟩ : syracuseStep 1141119 = 1711679) B1711679
theorem B1141295 : Blo 1140634 1141295 := bstep (se 1 (by rfl) ⟨855971, by rfl⟩ : syracuseStep 1141295 = 1711943) B1711943
theorem B10414655 : Blo 1140634 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B1141351 : Blo 1140634 1141351 := bstep (se 1 (by rfl) ⟨856013, by rfl⟩ : syracuseStep 1141351 = 1712027) B1712027
theorem B16476979 : Blo 1140634 16476979 := bstep (se 1 (by rfl) ⟨12357734, by rfl⟩ : syracuseStep 16476979 = 24715469) B24715469
theorem B1141727 : Blo 1140634 1141727 := bstep (se 1 (by rfl) ⟨856295, by rfl⟩ : syracuseStep 1141727 = 1712591) B1712591
theorem B1141755 : Blo 1140634 1141755 := bstep (se 1 (by rfl) ⟨856316, by rfl⟩ : syracuseStep 1141755 = 1712633) B1712633
theorem B1141823 : Blo 1140634 1141823 := bstep (se 1 (by rfl) ⟨856367, by rfl⟩ : syracuseStep 1141823 = 1712735) B1712735
theorem B1142143 : Blo 1140634 1142143 := bstep (se 1 (by rfl) ⟨856607, by rfl⟩ : syracuseStep 1142143 = 1713215) B1713215
theorem B1142171 : Blo 1140634 1142171 := bstep (se 1 (by rfl) ⟨856628, by rfl⟩ : syracuseStep 1142171 = 1713257) B1713257
theorem B1928603 : Blo 1140634 1928603 := bstep (se 1 (by rfl) ⟨1446452, by rfl⟩ : syracuseStep 1928603 = 2892905) B2892905
theorem B3861971 : Blo 1140634 3861971 := bstep (se 1 (by rfl) ⟨2896478, by rfl⟩ : syracuseStep 3861971 = 5792957) B5792957
theorem B1142239 : Blo 1140634 1142239 := bstep (se 1 (by rfl) ⟨856679, by rfl⟩ : syracuseStep 1142239 = 1713359) B1713359
theorem B2059847 : Blo 1140634 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1142375 : Blo 1140634 1142375 := bstep (se 1 (by rfl) ⟨856781, by rfl⟩ : syracuseStep 1142375 = 1713563) B1713563
theorem B3862241 : Blo 1140634 3862241 := bstep (se 2 (by rfl) ⟨1448340, by rfl⟩ : syracuseStep 3862241 = 2896681) B2896681
theorem B1142523 : Blo 1140634 1142523 := bstep (se 1 (by rfl) ⟨856892, by rfl⟩ : syracuseStep 1142523 = 1713785) B1713785
theorem B1142591 : Blo 1140634 1142591 := bstep (se 1 (by rfl) ⟨856943, by rfl⟩ : syracuseStep 1142591 = 1713887) B1713887
theorem B1142655 : Blo 1140634 1142655 := bstep (se 1 (by rfl) ⟨856991, by rfl⟩ : syracuseStep 1142655 = 1713983) B1713983
theorem B1142767 : Blo 1140634 1142767 := bstep (se 1 (by rfl) ⟨857075, by rfl⟩ : syracuseStep 1142767 = 1714151) B1714151
theorem B4124665 : Blo 1140634 4124665 := bstep (se 2 (by rfl) ⟨1546749, by rfl⟩ : syracuseStep 4124665 = 3093499) B3093499
theorem B1142779 : Blo 1140634 1142779 := bstep (se 1 (by rfl) ⟨857084, by rfl⟩ : syracuseStep 1142779 = 1714169) B1714169
theorem B1142847 : Blo 1140634 1142847 := bstep (se 1 (by rfl) ⟨857135, by rfl⟩ : syracuseStep 1142847 = 1714271) B1714271
theorem B1142887 : Blo 1140634 1142887 := bstep (se 1 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 1142887 = 1714331) B1714331
theorem B1142911 : Blo 1140634 1142911 := bstep (se 1 (by rfl) ⟨857183, by rfl⟩ : syracuseStep 1142911 = 1714367) B1714367
theorem B1929359 : Blo 1140634 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B1142939 : Blo 1140634 1142939 := bstep (se 1 (by rfl) ⟨857204, by rfl⟩ : syracuseStep 1142939 = 1714409) B1714409
theorem B1143143 : Blo 1140634 1143143 := bstep (se 1 (by rfl) ⟨857357, by rfl⟩ : syracuseStep 1143143 = 1714715) B1714715
theorem B1929575 : Blo 1140634 1929575 := bstep (se 1 (by rfl) ⟨1447181, by rfl⟩ : syracuseStep 1929575 = 2894363) B2894363
theorem B1143195 : Blo 1140634 1143195 := bstep (se 1 (by rfl) ⟨857396, by rfl⟩ : syracuseStep 1143195 = 1714793) B1714793
theorem B1143547 : Blo 1140634 1143547 := bstep (se 1 (by rfl) ⟨857660, by rfl⟩ : syracuseStep 1143547 = 1715321) B1715321
theorem B11137799 : Blo 1140634 11137799 := bstep (se 1 (by rfl) ⟨8353349, by rfl⟩ : syracuseStep 11137799 = 16706699) B16706699
theorem B1143615 : Blo 1140634 1143615 := bstep (se 1 (by rfl) ⟨857711, by rfl⟩ : syracuseStep 1143615 = 1715423) B1715423
theorem B1143643 : Blo 1140634 1143643 := bstep (se 1 (by rfl) ⟨857732, by rfl⟩ : syracuseStep 1143643 = 1715465) B1715465
theorem B1143711 : Blo 1140634 1143711 := bstep (se 1 (by rfl) ⟨857783, by rfl⟩ : syracuseStep 1143711 = 1715567) B1715567
theorem B1143791 : Blo 1140634 1143791 := bstep (se 1 (by rfl) ⟨857843, by rfl⟩ : syracuseStep 1143791 = 1715687) B1715687
theorem B1143879 : Blo 1140634 1143879 := bstep (se 1 (by rfl) ⟨857909, by rfl⟩ : syracuseStep 1143879 = 1715819) B1715819
theorem B1143963 : Blo 1140634 1143963 := bstep (se 1 (by rfl) ⟨857972, by rfl⟩ : syracuseStep 1143963 = 1715945) B1715945
theorem B18543815 : Blo 1140634 18543815 := bstep (se 1 (by rfl) ⟨13907861, by rfl⟩ : syracuseStep 18543815 = 27815723) B27815723
theorem B1144059 : Blo 1140634 1144059 := bstep (se 1 (by rfl) ⟨858044, by rfl⟩ : syracuseStep 1144059 = 1716089) B1716089
theorem B1144127 : Blo 1140634 1144127 := bstep (se 1 (by rfl) ⟨858095, by rfl⟩ : syracuseStep 1144127 = 1716191) B1716191
theorem B9663943 : Blo 1140634 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B1144295 : Blo 1140634 1144295 := bstep (se 1 (by rfl) ⟨858221, by rfl⟩ : syracuseStep 1144295 = 1716443) B1716443
theorem B1144303 : Blo 1140634 1144303 := bstep (se 1 (by rfl) ⟨858227, by rfl⟩ : syracuseStep 1144303 = 1716455) B1716455
theorem B3765779 : Blo 1140634 3765779 := bstep (se 1 (by rfl) ⟨2824334, by rfl⟩ : syracuseStep 3765779 = 5648669) B5648669
theorem B1144411 : Blo 1140634 1144411 := bstep (se 1 (by rfl) ⟨858308, by rfl⟩ : syracuseStep 1144411 = 1716617) B1716617
theorem B1373851 : Blo 1140634 1373851 := bstep (se 1 (by rfl) ⟨1030388, by rfl⟩ : syracuseStep 1373851 = 2060777) B2060777
theorem B1144475 : Blo 1140634 1144475 := bstep (se 1 (by rfl) ⟨858356, by rfl⟩ : syracuseStep 1144475 = 1716713) B1716713
theorem B1144559 : Blo 1140634 1144559 := bstep (se 1 (by rfl) ⟨858419, by rfl⟩ : syracuseStep 1144559 = 1716839) B1716839
theorem B4880189 : Blo 1140634 4880189 := bstep (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) B1830071
theorem B1833031 : Blo 1140634 1833031 := bstep (se 1 (by rfl) ⟨1374773, by rfl⟩ : syracuseStep 1833031 = 2749547) B2749547
theorem B18774199 : Blo 1140634 18774199 := bstep (se 1 (by rfl) ⟨14080649, by rfl⟩ : syracuseStep 18774199 = 28161299) B28161299
theorem B8681903 : Blo 1140634 8681903 := bstep (se 1 (by rfl) ⟨6511427, by rfl⟩ : syracuseStep 8681903 = 13022855) B13022855
theorem B20872363 : Blo 1140634 20872363 := bstep (se 1 (by rfl) ⟨15654272, by rfl⟩ : syracuseStep 20872363 = 31308545) B31308545
theorem B19758275 : Blo 1140634 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B10714799 : Blo 1140634 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B9273041 : Blo 1140634 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B5275421 : Blo 1140634 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B6947315 : Blo 1140634 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B27755081 : Blo 1140634 27755081 := bstep (se 2 (by rfl) ⟨10408155, by rfl⟩ : syracuseStep 27755081 = 20816311) B20816311
theorem B8782499 : Blo 1140634 8782499 := bstep (se 1 (by rfl) ⟨6586874, by rfl⟩ : syracuseStep 8782499 = 13173749) B13173749
theorem B1542079 : Blo 1140634 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B13011191 : Blo 1140634 13011191 := bstep (se 1 (by rfl) ⟨9758393, by rfl⟩ : syracuseStep 13011191 = 19516787) B19516787
theorem B4393223 : Blo 1140634 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B2166239 : Blo 1140634 2166239 := bstep (se 1 (by rfl) ⟨1624679, by rfl⟩ : syracuseStep 2166239 = 3249359) B3249359
theorem B58691267 : Blo 1140634 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B2166497 : Blo 1140634 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1445627 : Blo 1140634 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B2887771 : Blo 1140634 2887771 := bstep (se 1 (by rfl) ⟨2165828, by rfl⟩ : syracuseStep 2887771 = 4331657) B4331657
theorem B1544383 : Blo 1140634 1544383 := bstep (se 1 (by rfl) ⟨1158287, by rfl⟩ : syracuseStep 1544383 = 2316575) B2316575
theorem B2887913 : Blo 1140634 2887913 := bstep (se 2 (by rfl) ⟨1082967, by rfl⟩ : syracuseStep 2887913 = 2165935) B2165935
theorem B9769193 : Blo 1140634 9769193 := bstep (se 2 (by rfl) ⟨3663447, by rfl⟩ : syracuseStep 9769193 = 7326895) B7326895
theorem B3248687 : Blo 1140634 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B3249335 : Blo 1140634 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B9770219 : Blo 1140634 9770219 := bstep (se 1 (by rfl) ⟨7327664, by rfl⟩ : syracuseStep 9770219 = 14655329) B14655329
theorem B1447247 : Blo 1140634 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B2889067 : Blo 1140634 2889067 := bstep (se 1 (by rfl) ⟨2166800, by rfl⟩ : syracuseStep 2889067 = 4333601) B4333601
theorem B3085739 : Blo 1140634 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B57219149 : Blo 1140634 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B1448047 : Blo 1140634 1448047 := bstep (se 1 (by rfl) ⟨1086035, by rfl⟩ : syracuseStep 1448047 = 2172071) B2172071
theorem B32938271 : Blo 1140634 32938271 := bstep (se 1 (by rfl) ⟨24703703, by rfl⟩ : syracuseStep 32938271 = 49407407) B49407407
theorem B3250601 : Blo 1140634 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B21961307 : Blo 1140634 21961307 := bstep (se 1 (by rfl) ⟨16470980, by rfl⟩ : syracuseStep 21961307 = 32941961) B32941961
theorem B3250793 : Blo 1140634 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B2169595 : Blo 1140634 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B2169641 : Blo 1140634 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B1711097 : Blo 1140634 1711097 := bstep (se 2 (by rfl) ⟨641661, by rfl⟩ : syracuseStep 1711097 = 1283323) B1283323
theorem B4332599 : Blo 1140634 4332599 := bstep (se 1 (by rfl) ⟨3249449, by rfl⟩ : syracuseStep 4332599 = 6498899) B6498899
theorem B12885257 : Blo 1140634 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B6168059 : Blo 1140634 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B1285735 : Blo 1140634 1285735 := bstep (se 1 (by rfl) ⟨964301, by rfl⟩ : syracuseStep 1285735 = 1928603) B1928603
theorem B1711727 : Blo 1140634 1711727 := bstep (se 1 (by rfl) ⟨1283795, by rfl⟩ : syracuseStep 1711727 = 2567591) B2567591
theorem B1711847 : Blo 1140634 1711847 := bstep (se 1 (by rfl) ⟨1283885, by rfl⟩ : syracuseStep 1711847 = 2567771) B2567771
theorem B4398857 : Blo 1140634 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B1712123 : Blo 1140634 1712123 := bstep (se 1 (by rfl) ⟨1284092, by rfl⟩ : syracuseStep 1712123 = 2568185) B2568185
theorem B1712183 : Blo 1140634 1712183 := bstep (se 1 (by rfl) ⟨1284137, by rfl⟩ : syracuseStep 1712183 = 2568275) B2568275
theorem B1286239 : Blo 1140634 1286239 := bstep (se 1 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 1286239 = 1929359) B1929359
theorem B1712303 : Blo 1140634 1712303 := bstep (se 1 (by rfl) ⟨1284227, by rfl⟩ : syracuseStep 1712303 = 2568455) B2568455
theorem B1286383 : Blo 1140634 1286383 := bstep (se 1 (by rfl) ⟨964787, by rfl⟩ : syracuseStep 1286383 = 1929575) B1929575
theorem B7315721 : Blo 1140634 7315721 := bstep (se 2 (by rfl) ⟨2743395, by rfl⟩ : syracuseStep 7315721 = 5486791) B5486791
theorem B1712507 : Blo 1140634 1712507 := bstep (se 1 (by rfl) ⟨1284380, by rfl⟩ : syracuseStep 1712507 = 2568761) B2568761
theorem B1712681 : Blo 1140634 1712681 := bstep (se 2 (by rfl) ⟨642255, by rfl⟩ : syracuseStep 1712681 = 1284511) B1284511
theorem B1712777 : Blo 1140634 1712777 := bstep (se 2 (by rfl) ⟨642291, by rfl⟩ : syracuseStep 1712777 = 1284583) B1284583
theorem B4334255 : Blo 1140634 4334255 := bstep (se 1 (by rfl) ⟨3250691, by rfl⟩ : syracuseStep 4334255 = 6501383) B6501383
theorem B12362543 : Blo 1140634 12362543 := bstep (se 1 (by rfl) ⟨9271907, by rfl⟩ : syracuseStep 12362543 = 18543815) B18543815
theorem B4399933 : Blo 1140634 4399933 := bstep (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) B1649975
theorem B1712987 : Blo 1140634 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B1713023 : Blo 1140634 1713023 := bstep (se 1 (by rfl) ⟨1284767, by rfl⟩ : syracuseStep 1713023 = 2569535) B2569535
theorem B1713095 : Blo 1140634 1713095 := bstep (se 1 (by rfl) ⟨1284821, by rfl⟩ : syracuseStep 1713095 = 2569643) B2569643
theorem B4334573 : Blo 1140634 4334573 := bstep (se 3 (by rfl) ⟨812732, by rfl⟩ : syracuseStep 4334573 = 1625465) B1625465
theorem B2892955 : Blo 1140634 2892955 := bstep (se 1 (by rfl) ⟨2169716, by rfl⟩ : syracuseStep 2892955 = 4339433) B4339433
theorem B1713311 : Blo 1140634 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B3253459 : Blo 1140634 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B1713455 : Blo 1140634 1713455 := bstep (se 1 (by rfl) ⟨1285091, by rfl⟩ : syracuseStep 1713455 = 2570183) B2570183
theorem B1713647 : Blo 1140634 1713647 := bstep (se 1 (by rfl) ⟨1285235, by rfl⟩ : syracuseStep 1713647 = 2570471) B2570471
theorem B1713659 : Blo 1140634 1713659 := bstep (se 1 (by rfl) ⟨1285244, by rfl⟩ : syracuseStep 1713659 = 2570489) B2570489
theorem B1713695 : Blo 1140634 1713695 := bstep (se 1 (by rfl) ⟨1285271, by rfl⟩ : syracuseStep 1713695 = 2570543) B2570543
theorem B27829817 : Blo 1140634 27829817 := bstep (se 2 (by rfl) ⟨10436181, by rfl⟩ : syracuseStep 27829817 = 20872363) B20872363
theorem B1713839 : Blo 1140634 1713839 := bstep (se 1 (by rfl) ⟨1285379, by rfl⟩ : syracuseStep 1713839 = 2570759) B2570759
theorem B225322681 : Blo 1140634 225322681 := bstep (se 2 (by rfl) ⟨84496005, by rfl⟩ : syracuseStep 225322681 = 168992011) B168992011
theorem B1713929 : Blo 1140634 1713929 := bstep (se 2 (by rfl) ⟨642723, by rfl⟩ : syracuseStep 1713929 = 1285447) B1285447
theorem B1713959 : Blo 1140634 1713959 := bstep (se 1 (by rfl) ⟨1285469, by rfl⟩ : syracuseStep 1713959 = 2570939) B2570939
theorem B4335515 : Blo 1140634 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B4335713 : Blo 1140634 4335713 := bstep (se 2 (by rfl) ⟨1625892, by rfl⟩ : syracuseStep 4335713 = 3251785) B3251785
theorem B24717473 : Blo 1140634 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B1714559 : Blo 1140634 1714559 := bstep (se 1 (by rfl) ⟨1285919, by rfl⟩ : syracuseStep 1714559 = 2571839) B2571839
theorem B3516947 : Blo 1140634 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B1714799 : Blo 1140634 1714799 := bstep (se 1 (by rfl) ⟨1286099, by rfl⟩ : syracuseStep 1714799 = 2572199) B2572199
theorem B21998213 : Blo 1140634 21998213 := bstep (se 4 (by rfl) ⟨2062332, by rfl⟩ : syracuseStep 21998213 = 4124665) B4124665
theorem B1715015 : Blo 1140634 1715015 := bstep (se 1 (by rfl) ⟨1286261, by rfl⟩ : syracuseStep 1715015 = 2572523) B2572523
theorem B6957895 : Blo 1140634 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B5778377 : Blo 1140634 5778377 := bstep (se 2 (by rfl) ⟨2166891, by rfl⟩ : syracuseStep 5778377 = 4333783) B4333783
theorem B5778539 : Blo 1140634 5778539 := bstep (se 1 (by rfl) ⟨4333904, by rfl⟩ : syracuseStep 5778539 = 8667809) B8667809
theorem B2436473 : Blo 1140634 2436473 := bstep (se 2 (by rfl) ⟨913677, by rfl⟩ : syracuseStep 2436473 = 1827355) B1827355
theorem B1715615 : Blo 1140634 1715615 := bstep (se 1 (by rfl) ⟨1286711, by rfl⟩ : syracuseStep 1715615 = 2573423) B2573423
theorem B2895335 : Blo 1140634 2895335 := bstep (se 1 (by rfl) ⟨2171501, by rfl⟩ : syracuseStep 2895335 = 4343003) B4343003
theorem B1715879 : Blo 1140634 1715879 := bstep (se 1 (by rfl) ⟨1286909, by rfl⟩ : syracuseStep 1715879 = 2573819) B2573819
theorem B1715903 : Blo 1140634 1715903 := bstep (se 1 (by rfl) ⟨1286927, by rfl⟩ : syracuseStep 1715903 = 2573855) B2573855
theorem B3256033 : Blo 1140634 3256033 := bstep (se 2 (by rfl) ⟨1221012, by rfl⟩ : syracuseStep 3256033 = 2442025) B2442025
theorem B1715999 : Blo 1140634 1715999 := bstep (se 1 (by rfl) ⟨1286999, by rfl⟩ : syracuseStep 1715999 = 2573999) B2573999
theorem B4337489 : Blo 1140634 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B1716287 : Blo 1140634 1716287 := bstep (se 1 (by rfl) ⟨1287215, by rfl⟩ : syracuseStep 1716287 = 2574431) B2574431
theorem B2896033 : Blo 1140634 2896033 := bstep (se 2 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 2896033 = 2172025) B2172025
theorem B1716479 : Blo 1140634 1716479 := bstep (se 1 (by rfl) ⟨1287359, by rfl⟩ : syracuseStep 1716479 = 2574719) B2574719
theorem B1716521 : Blo 1140634 1716521 := bstep (se 2 (by rfl) ⟨643695, by rfl⟩ : syracuseStep 1716521 = 1287391) B1287391
theorem B10989881 : Blo 1140634 10989881 := bstep (se 2 (by rfl) ⟨4121205, by rfl⟩ : syracuseStep 10989881 = 8242411) B8242411
theorem B1716791 : Blo 1140634 1716791 := bstep (se 1 (by rfl) ⟨1287593, by rfl⟩ : syracuseStep 1716791 = 2575187) B2575187
theorem B7811923 : Blo 1140634 7811923 := bstep (se 1 (by rfl) ⟨5858942, by rfl⟩ : syracuseStep 7811923 = 11717885) B11717885
theorem B10990495 : Blo 1140634 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B2570219 : Blo 1140634 2570219 := bstep (se 1 (by rfl) ⟨1927664, by rfl⟩ : syracuseStep 2570219 = 3855329) B3855329
theorem B21969305 : Blo 1140634 21969305 := bstep (se 2 (by rfl) ⟨8238489, by rfl⟩ : syracuseStep 21969305 = 16476979) B16476979
theorem B8665865 : Blo 1140634 8665865 := bstep (se 2 (by rfl) ⟨3249699, by rfl⟩ : syracuseStep 8665865 = 6499399) B6499399
theorem B13024313 : Blo 1140634 13024313 := bstep (se 2 (by rfl) ⟨4884117, by rfl⟩ : syracuseStep 13024313 = 9768235) B9768235
theorem B5488175 : Blo 1140634 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B6504047 : Blo 1140634 6504047 := bstep (se 1 (by rfl) ⟨4878035, by rfl⟩ : syracuseStep 6504047 = 9756071) B9756071
theorem B8700317 : Blo 1140634 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B2606201 : Blo 1140634 2606201 := bstep (se 2 (by rfl) ⟨977325, by rfl⟩ : syracuseStep 2606201 = 1954651) B1954651
theorem B2573495 : Blo 1140634 2573495 := bstep (se 1 (by rfl) ⟨1930121, by rfl⟩ : syracuseStep 2573495 = 3860243) B3860243
theorem B5784857 : Blo 1140634 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B2573639 : Blo 1140634 2573639 := bstep (se 1 (by rfl) ⟨1930229, by rfl⟩ : syracuseStep 2573639 = 3860459) B3860459
theorem B6440633 : Blo 1140634 6440633 := bstep (se 2 (by rfl) ⟨2415237, by rfl⟩ : syracuseStep 6440633 = 4830475) B4830475
theorem B10995689 : Blo 1140634 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B2574647 : Blo 1140634 2574647 := bstep (se 1 (by rfl) ⟨1930985, by rfl⟩ : syracuseStep 2574647 = 3861971) B3861971
theorem B2574827 : Blo 1140634 2574827 := bstep (se 1 (by rfl) ⟨1931120, by rfl⟩ : syracuseStep 2574827 = 3862241) B3862241
theorem B8669753 : Blo 1140634 8669753 := bstep (se 2 (by rfl) ⟨3251157, by rfl⟩ : syracuseStep 8669753 = 6502315) B6502315
theorem B8243795 : Blo 1140634 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B2444041 : Blo 1140634 2444041 := bstep (se 2 (by rfl) ⟨916515, by rfl⟩ : syracuseStep 2444041 = 1833031) B1833031
theorem B7425199 : Blo 1140634 7425199 := bstep (se 1 (by rfl) ⟨5568899, by rfl⟩ : syracuseStep 7425199 = 11137799) B11137799
theorem B29248937 : Blo 1140634 29248937 := bstep (se 2 (by rfl) ⟨10968351, by rfl⟩ : syracuseStep 29248937 = 21936703) B21936703
theorem B2510519 : Blo 1140634 2510519 := bstep (se 1 (by rfl) ⟨1882889, by rfl⟩ : syracuseStep 2510519 = 3765779) B3765779
theorem B14667479 : Blo 1140634 14667479 := bstep (se 1 (by rfl) ⟨11000609, by rfl⟩ : syracuseStep 14667479 = 22001219) B22001219
theorem B31248109 : Blo 1140634 31248109 := bstep (se 3 (by rfl) ⟨5859020, by rfl⟩ : syracuseStep 31248109 = 11718041) B11718041
theorem B5787935 : Blo 1140634 5787935 := bstep (se 1 (by rfl) ⟨4340951, by rfl⟩ : syracuseStep 5787935 = 8681903) B8681903
theorem B2347631 : Blo 1140634 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B6509605 : Blo 1140634 6509605 := bstep (se 4 (by rfl) ⟨610275, by rfl⟩ : syracuseStep 6509605 = 1220551) B1220551
theorem B5788745 : Blo 1140634 5788745 := bstep (se 2 (by rfl) ⟨2170779, by rfl⟩ : syracuseStep 5788745 = 4341559) B4341559
theorem B6182027 : Blo 1140634 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1627447 : Blo 1140634 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B3855869 : Blo 1140634 3855869 := bstep (se 3 (by rfl) ⟨722975, by rfl⟩ : syracuseStep 3855869 = 1445951) B1445951
theorem B7329305 : Blo 1140634 7329305 := bstep (se 2 (by rfl) ⟨2748489, by rfl⟩ : syracuseStep 7329305 = 5496979) B5496979
theorem B3659347 : Blo 1140634 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B3855977 : Blo 1140634 3855977 := bstep (se 2 (by rfl) ⟨1445991, by rfl⟩ : syracuseStep 3855977 = 2891983) B2891983
theorem B1627823 : Blo 1140634 1627823 := bstep (se 1 (by rfl) ⟨1220867, by rfl⟩ : syracuseStep 1627823 = 2441735) B2441735
theorem B13031603 : Blo 1140634 13031603 := bstep (se 1 (by rfl) ⟨9773702, by rfl⟩ : syracuseStep 13031603 = 19547405) B19547405
theorem B12343549 : Blo 1140634 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B100129061 : Blo 1140634 100129061 := bstep (se 4 (by rfl) ⟨9387099, by rfl⟩ : syracuseStep 100129061 = 18774199) B18774199
theorem B1628905 : Blo 1140634 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B24697655 : Blo 1140634 24697655 := bstep (se 1 (by rfl) ⟨18523241, by rfl⟩ : syracuseStep 24697655 = 37046483) B37046483
theorem B5790527 : Blo 1140634 5790527 := bstep (se 1 (by rfl) ⟨4342895, by rfl⟩ : syracuseStep 5790527 = 8685791) B8685791
theorem B1301567 : Blo 1140634 1301567 := bstep (se 1 (by rfl) ⟨976175, by rfl⟩ : syracuseStep 1301567 = 1952351) B1952351
theorem B1629247 : Blo 1140634 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B3661129 : Blo 1140634 3661129 := bstep (se 2 (by rfl) ⟨1372923, by rfl⟩ : syracuseStep 3661129 = 2745847) B2745847
theorem B2351207 : Blo 1140634 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B1925417 : Blo 1140634 1925417 := bstep (se 2 (by rfl) ⟨722031, by rfl⟩ : syracuseStep 1925417 = 1444063) B1444063
theorem B1925687 : Blo 1140634 1925687 := bstep (se 1 (by rfl) ⟨1444265, by rfl⟩ : syracuseStep 1925687 = 2888531) B2888531
theorem B1926247 : Blo 1140634 1926247 := bstep (se 1 (by rfl) ⟨1444685, by rfl⟩ : syracuseStep 1926247 = 2889371) B2889371
theorem B12346663 : Blo 1140634 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1828207 : Blo 1140634 1828207 := bstep (se 1 (by rfl) ⟨1371155, by rfl⟩ : syracuseStep 1828207 = 2742311) B2742311
theorem B13002443 : Blo 1140634 13002443 := bstep (se 1 (by rfl) ⟨9751832, by rfl⟩ : syracuseStep 13002443 = 19503665) B19503665
theorem B1140639 : Blo 1140634 1140639 := bstep (se 1 (by rfl) ⟨855479, by rfl⟩ : syracuseStep 1140639 = 1710959) B1710959
theorem B1140647 : Blo 1140634 1140647 := bstep (se 1 (by rfl) ⟨855485, by rfl⟩ : syracuseStep 1140647 = 1710971) B1710971
theorem B1927199 : Blo 1140634 1927199 := bstep (se 1 (by rfl) ⟨1445399, by rfl⟩ : syracuseStep 1927199 = 2890799) B2890799
theorem B14641235 : Blo 1140634 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B5793929 : Blo 1140634 5793929 := bstep (se 2 (by rfl) ⟨2172723, by rfl⟩ : syracuseStep 5793929 = 4345447) B4345447
theorem B1141223 : Blo 1140634 1141223 := bstep (se 1 (by rfl) ⟨855917, by rfl⟩ : syracuseStep 1141223 = 1711835) B1711835
theorem B1141403 : Blo 1140634 1141403 := bstep (se 1 (by rfl) ⟨856052, by rfl⟩ : syracuseStep 1141403 = 1712105) B1712105
theorem B2714489 : Blo 1140634 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B2976641 : Blo 1140634 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B1141871 : Blo 1140634 1141871 := bstep (se 1 (by rfl) ⟨856403, by rfl⟩ : syracuseStep 1141871 = 1712807) B1712807
theorem B1141951 : Blo 1140634 1141951 := bstep (se 1 (by rfl) ⟨856463, by rfl⟩ : syracuseStep 1141951 = 1712927) B1712927
theorem B1141967 : Blo 1140634 1141967 := bstep (se 1 (by rfl) ⟨856475, by rfl⟩ : syracuseStep 1141967 = 1712951) B1712951
theorem B1142087 : Blo 1140634 1142087 := bstep (se 1 (by rfl) ⟨856565, by rfl⟩ : syracuseStep 1142087 = 1713131) B1713131
theorem B23424923 : Blo 1140634 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B2781161 : Blo 1140634 2781161 := bstep (se 2 (by rfl) ⟨1042935, by rfl⟩ : syracuseStep 2781161 = 2085871) B2085871
theorem B6516713 : Blo 1140634 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B1142815 : Blo 1140634 1142815 := bstep (se 1 (by rfl) ⟨857111, by rfl⟩ : syracuseStep 1142815 = 1714223) B1714223
theorem B1831007 : Blo 1140634 1831007 := bstep (se 1 (by rfl) ⟨1373255, by rfl⟩ : syracuseStep 1831007 = 2746511) B2746511
theorem B1142991 : Blo 1140634 1142991 := bstep (se 1 (by rfl) ⟨857243, by rfl⟩ : syracuseStep 1142991 = 1714487) B1714487
theorem B1143111 : Blo 1140634 1143111 := bstep (se 1 (by rfl) ⟨857333, by rfl⟩ : syracuseStep 1143111 = 1714667) B1714667
theorem B1929595 : Blo 1140634 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B6943103 : Blo 1140634 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B1929865 : Blo 1140634 1929865 := bstep (se 2 (by rfl) ⟨723699, by rfl⟩ : syracuseStep 1929865 = 1447399) B1447399
theorem B1143579 : Blo 1140634 1143579 := bstep (se 1 (by rfl) ⟨857684, by rfl⟩ : syracuseStep 1143579 = 1715369) B1715369
theorem B1831801 : Blo 1140634 1831801 := bstep (se 2 (by rfl) ⟨686925, by rfl⟩ : syracuseStep 1831801 = 1373851) B1373851
theorem B26702855 : Blo 1140634 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B1373231 : Blo 1140634 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B1143855 : Blo 1140634 1143855 := bstep (se 1 (by rfl) ⟨857891, by rfl⟩ : syracuseStep 1143855 = 1715783) B1715783
theorem B1143975 : Blo 1140634 1143975 := bstep (se 1 (by rfl) ⟨857981, by rfl⟩ : syracuseStep 1143975 = 1715963) B1715963
theorem B1144423 : Blo 1140634 1144423 := bstep (se 1 (by rfl) ⟨858317, by rfl⟩ : syracuseStep 1144423 = 1716635) B1716635
theorem B9270899 : Blo 1140634 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B13006817 : Blo 1140634 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B1931431 : Blo 1140634 1931431 := bstep (se 1 (by rfl) ⟨1448573, by rfl⟩ : syracuseStep 1931431 = 2897147) B2897147
theorem B13170973 : Blo 1140634 13170973 := bstep (se 3 (by rfl) ⟨2469557, by rfl⟩ : syracuseStep 13170973 = 4939115) B4939115
theorem B8223497 : Blo 1140634 8223497 := bstep (se 2 (by rfl) ⟨3083811, by rfl⟩ : syracuseStep 8223497 = 6167623) B6167623
theorem B28572797 : Blo 1140634 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B13172183 : Blo 1140634 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B14647229 : Blo 1140634 14647229 := bstep (se 3 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 14647229 = 5492711) B5492711
theorem B5800211 : Blo 1140634 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B1737467 : Blo 1140634 1737467 := bstep (se 1 (by rfl) ⟨1303100, by rfl⟩ : syracuseStep 1737467 = 2606201) B2606201
theorem B5866577 : Blo 1140634 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B4293755 : Blo 1140634 4293755 := bstep (se 1 (by rfl) ⟨3220316, by rfl⟩ : syracuseStep 4293755 = 6440633) B6440633
theorem B19499291 : Blo 1140634 19499291 := bstep (se 1 (by rfl) ⟨14624468, by rfl⟩ : syracuseStep 19499291 = 29248937) B29248937
theorem B1444159 : Blo 1140634 1444159 := bstep (se 1 (by rfl) ⟨1083119, by rfl⟩ : syracuseStep 1444159 = 2166239) B2166239
theorem B39127511 : Blo 1140634 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B1444331 : Blo 1140634 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B2165791 : Blo 1140634 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B4886203 : Blo 1140634 4886203 := bstep (se 1 (by rfl) ⟨3664652, by rfl⟩ : syracuseStep 4886203 = 7329305) B7329305
theorem B9277193 : Blo 1140634 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B8687735 : Blo 1140634 8687735 := bstep (se 1 (by rfl) ⟨6515801, by rfl⟩ : syracuseStep 8687735 = 13031603) B13031603
theorem B21958847 : Blo 1140634 21958847 := bstep (se 1 (by rfl) ⟨16469135, by rfl⟩ : syracuseStep 21958847 = 32938271) B32938271
theorem B66752707 : Blo 1140634 66752707 := bstep (se 1 (by rfl) ⟨50064530, by rfl⟩ : syracuseStep 66752707 = 100129061) B100129061
theorem B9900265 : Blo 1140634 9900265 := bstep (se 2 (by rfl) ⟨3712599, by rfl⟩ : syracuseStep 9900265 = 7425199) B7425199
theorem B2167067 : Blo 1140634 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B1446427 : Blo 1140634 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B2888399 : Blo 1140634 2888399 := bstep (se 1 (by rfl) ⟨2166299, by rfl⟩ : syracuseStep 2888399 = 4332599) B4332599
theorem B8590171 : Blo 1140634 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B1283611 : Blo 1140634 1283611 := bstep (se 1 (by rfl) ⟨962708, by rfl⟩ : syracuseStep 1283611 = 1925417) B1925417
theorem B1283791 : Blo 1140634 1283791 := bstep (se 1 (by rfl) ⟨962843, by rfl⟩ : syracuseStep 1283791 = 1925687) B1925687
theorem B2889503 : Blo 1140634 2889503 := bstep (se 1 (by rfl) ⟨2167127, by rfl⟩ : syracuseStep 2889503 = 4334255) B4334255
theorem B2889715 : Blo 1140634 2889715 := bstep (se 1 (by rfl) ⟨2167286, by rfl⟩ : syracuseStep 2889715 = 4334573) B4334573
theorem B18553211 : Blo 1140634 18553211 := bstep (se 1 (by rfl) ⟨13914908, by rfl⟩ : syracuseStep 18553211 = 27829817) B27829817
theorem B14653993 : Blo 1140634 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B2890343 : Blo 1140634 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B1284799 : Blo 1140634 1284799 := bstep (se 1 (by rfl) ⟨963599, by rfl⟩ : syracuseStep 1284799 = 1927199) B1927199
theorem B2890475 : Blo 1140634 2890475 := bstep (se 1 (by rfl) ⟨2167856, by rfl⟩ : syracuseStep 2890475 = 4335713) B4335713
theorem B2169929 : Blo 1140634 2169929 := bstep (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) B1627447
theorem B1809659 : Blo 1140634 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B2891659 : Blo 1140634 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B1220671 : Blo 1140634 1220671 := bstep (se 1 (by rfl) ⟨915503, by rfl⟩ : syracuseStep 1220671 = 1831007) B1831007
theorem B4628735 : Blo 1140634 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B16458065 : Blo 1140634 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B17801903 : Blo 1140634 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B2171873 : Blo 1140634 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2892793 : Blo 1140634 2892793 := bstep (se 2 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 2892793 = 2169595) B2169595
theorem B1713479 : Blo 1140634 1713479 := bstep (se 1 (by rfl) ⟨1285109, by rfl⟩ : syracuseStep 1713479 = 2570219) B2570219
theorem B2172329 : Blo 1140634 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B6694717 : Blo 1140634 6694717 := bstep (se 3 (by rfl) ⟨1255259, by rfl⟩ : syracuseStep 6694717 = 2510519) B2510519
theorem B5482331 : Blo 1140634 5482331 := bstep (se 1 (by rfl) ⟨4111748, by rfl⟩ : syracuseStep 5482331 = 8223497) B8223497
theorem B5777243 : Blo 1140634 5777243 := bstep (se 1 (by rfl) ⟨4332932, by rfl⟩ : syracuseStep 5777243 = 8665865) B8665865
theorem B19048531 : Blo 1140634 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B1714313 : Blo 1140634 1714313 := bstep (se 2 (by rfl) ⟨642867, by rfl⟩ : syracuseStep 1714313 = 1285735) B1285735
theorem B62466461 : Blo 1140634 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B4336031 : Blo 1140634 4336031 := bstep (se 1 (by rfl) ⟨3252023, by rfl⟩ : syracuseStep 4336031 = 6504047) B6504047
theorem B1714985 : Blo 1140634 1714985 := bstep (se 2 (by rfl) ⟨643119, by rfl⟩ : syracuseStep 1714985 = 1286239) B1286239
theorem B6269885 : Blo 1140634 6269885 := bstep (se 3 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 6269885 = 2351207) B2351207
theorem B1715177 : Blo 1140634 1715177 := bstep (se 2 (by rfl) ⟨643191, by rfl⟩ : syracuseStep 1715177 = 1286383) B1286383
theorem B4631543 : Blo 1140634 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B1715663 : Blo 1140634 1715663 := bstep (se 1 (by rfl) ⟨1286747, by rfl⟩ : syracuseStep 1715663 = 2573495) B2573495
theorem B1715759 : Blo 1140634 1715759 := bstep (se 1 (by rfl) ⟨1286819, by rfl⟩ : syracuseStep 1715759 = 2573639) B2573639
theorem B2568329 : Blo 1140634 2568329 := bstep (se 2 (by rfl) ⟨963123, by rfl⟩ : syracuseStep 2568329 = 1926247) B1926247
theorem B2928815 : Blo 1140634 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B1716431 : Blo 1140634 1716431 := bstep (se 1 (by rfl) ⟨1287323, by rfl⟩ : syracuseStep 1716431 = 2574647) B2574647
theorem B4337945 : Blo 1140634 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B1716551 : Blo 1140634 1716551 := bstep (se 1 (by rfl) ⟨1287413, by rfl⟩ : syracuseStep 1716551 = 2574827) B2574827
theorem B5779835 : Blo 1140634 5779835 := bstep (se 1 (by rfl) ⟨4334876, by rfl⟩ : syracuseStep 5779835 = 8669753) B8669753
theorem B16462217 : Blo 1140634 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B2437609 : Blo 1140634 2437609 := bstep (se 2 (by rfl) ⟨914103, by rfl⟩ : syracuseStep 2437609 = 1828207) B1828207
theorem B300430241 : Blo 1140634 300430241 := bstep (se 2 (by rfl) ⟨112661340, by rfl⟩ : syracuseStep 300430241 = 225322681) B225322681
theorem B9778319 : Blo 1140634 9778319 := bstep (se 1 (by rfl) ⟨7333739, by rfl⟩ : syracuseStep 9778319 = 14667479) B14667479
theorem B8664893 : Blo 1140634 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B2570579 : Blo 1140634 2570579 := bstep (se 1 (by rfl) ⟨1927934, by rfl⟩ : syracuseStep 2570579 = 3855869) B3855869
theorem B3258721 : Blo 1140634 3258721 := bstep (se 2 (by rfl) ⟨1222020, by rfl⟩ : syracuseStep 3258721 = 2444041) B2444041
theorem B2570651 : Blo 1140634 2570651 := bstep (se 1 (by rfl) ⟨1927988, by rfl⟩ : syracuseStep 2570651 = 3855977) B3855977
theorem B4340861 : Blo 1140634 4340861 := bstep (se 3 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 4340861 = 1627823) B1627823
theorem B16465103 : Blo 1140634 16465103 := bstep (se 1 (by rfl) ⟨12348827, by rfl⟩ : syracuseStep 16465103 = 24697655) B24697655
theorem B4341377 : Blo 1140634 4341377 := bstep (se 2 (by rfl) ⟨1628016, by rfl⟩ : syracuseStep 4341377 = 3256033) B3256033
theorem B41664145 : Blo 1140634 41664145 := bstep (se 2 (by rfl) ⟨15624054, by rfl⟩ : syracuseStep 41664145 = 31248109) B31248109
theorem B4112039 : Blo 1140634 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B2932571 : Blo 1140634 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B3850361 : Blo 1140634 3850361 := bstep (se 2 (by rfl) ⟨1443885, by rfl⟩ : syracuseStep 3850361 = 2887771) B2887771
theorem B152584397 : Blo 1140634 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B2572793 : Blo 1140634 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B8241695 : Blo 1140634 8241695 := bstep (se 1 (by rfl) ⟨6181271, by rfl⟩ : syracuseStep 8241695 = 12362543) B12362543
theorem B2573153 : Blo 1140634 2573153 := bstep (se 2 (by rfl) ⟨964932, by rfl⟩ : syracuseStep 2573153 = 1929865) B1929865
theorem B8668295 : Blo 1140634 8668295 := bstep (se 1 (by rfl) ⟨6501221, by rfl⟩ : syracuseStep 8668295 = 13002443) B13002443
theorem B2442401 : Blo 1140634 2442401 := bstep (se 2 (by rfl) ⟨915900, by rfl⟩ : syracuseStep 2442401 = 1831801) B1831801
theorem B8668781 : Blo 1140634 8668781 := bstep (se 3 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 8668781 = 3250793) B3250793
theorem B2344631 : Blo 1140634 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B14665475 : Blo 1140634 14665475 := bstep (se 1 (by rfl) ⟨10999106, by rfl⟩ : syracuseStep 14665475 = 21998213) B21998213
theorem B3852089 : Blo 1140634 3852089 := bstep (se 2 (by rfl) ⟨1444533, by rfl⟩ : syracuseStep 3852089 = 2889067) B2889067
theorem B1984427 : Blo 1140634 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B3852251 : Blo 1140634 3852251 := bstep (se 1 (by rfl) ⟨2889188, by rfl⟩ : syracuseStep 3852251 = 5778377) B5778377
theorem B3852359 : Blo 1140634 3852359 := bstep (se 1 (by rfl) ⟨2889269, by rfl⟩ : syracuseStep 3852359 = 5778539) B5778539
theorem B1624315 : Blo 1140634 1624315 := bstep (se 1 (by rfl) ⟨1218236, by rfl⟩ : syracuseStep 1624315 = 2436473) B2436473
theorem B1854107 : Blo 1140634 1854107 := bstep (se 1 (by rfl) ⟨1390580, by rfl⟩ : syracuseStep 1854107 = 2781161) B2781161
theorem B4344475 : Blo 1140634 4344475 := bstep (se 1 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 4344475 = 6516713) B6516713
theorem B7326587 : Blo 1140634 7326587 := bstep (se 1 (by rfl) ⟨5494940, by rfl⟩ : syracuseStep 7326587 = 10989881) B10989881
theorem B2575241 : Blo 1140634 2575241 := bstep (se 2 (by rfl) ⟨965715, by rfl⟩ : syracuseStep 2575241 = 1931431) B1931431
theorem B6180599 : Blo 1140634 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B8671211 : Blo 1140634 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B3855005 : Blo 1140634 3855005 := bstep (se 3 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 3855005 = 1445627) B1445627
theorem B3658783 : Blo 1140634 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B18503387 : Blo 1140634 18503387 := bstep (se 1 (by rfl) ⟨13877540, by rfl⟩ : syracuseStep 18503387 = 27755081) B27755081
theorem B5854999 : Blo 1140634 5854999 := bstep (se 1 (by rfl) ⟨4391249, by rfl⟩ : syracuseStep 5854999 = 8782499) B8782499
theorem B3856571 : Blo 1140634 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B7330459 : Blo 1140634 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B8674127 : Blo 1140634 8674127 := bstep (se 1 (by rfl) ⟨6505595, by rfl⟩ : syracuseStep 8674127 = 13011191) B13011191
theorem B3857273 : Blo 1140634 3857273 := bstep (se 2 (by rfl) ⟨1446477, by rfl⟩ : syracuseStep 3857273 = 2892955) B2892955
theorem B5495863 : Blo 1140634 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B2056105 : Blo 1140634 2056105 := bstep (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) B1542079
theorem B3661949 : Blo 1140634 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B1925275 : Blo 1140634 1925275 := bstep (se 1 (by rfl) ⟨1443956, by rfl⟩ : syracuseStep 1925275 = 2887913) B2887913
theorem B6512795 : Blo 1140634 6512795 := bstep (se 1 (by rfl) ⟨4884596, by rfl⟩ : syracuseStep 6512795 = 9769193) B9769193
theorem B3858623 : Blo 1140634 3858623 := bstep (se 1 (by rfl) ⟨2893967, by rfl⟩ : syracuseStep 3858623 = 5787935) B5787935
theorem B1565087 : Blo 1140634 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B3859163 : Blo 1140634 3859163 := bstep (se 1 (by rfl) ⟨2894372, by rfl⟩ : syracuseStep 3859163 = 5788745) B5788745
theorem B4121351 : Blo 1140634 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B6513479 : Blo 1140634 6513479 := bstep (se 1 (by rfl) ⟨4885109, by rfl⟩ : syracuseStep 6513479 = 9770219) B9770219
theorem B3859325 : Blo 1140634 3859325 := bstep (se 3 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 3859325 = 1447247) B1447247
theorem B2057159 : Blo 1140634 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B14640871 : Blo 1140634 14640871 := bstep (se 1 (by rfl) ⟨10980653, by rfl⟩ : syracuseStep 14640871 = 21961307) B21961307
theorem B3860351 : Blo 1140634 3860351 := bstep (se 1 (by rfl) ⟨2895263, by rfl⟩ : syracuseStep 3860351 = 5790527) B5790527
theorem B1140731 : Blo 1140634 1140731 := bstep (se 1 (by rfl) ⟨855548, by rfl⟩ : syracuseStep 1140731 = 1711097) B1711097
theorem B1141151 : Blo 1140634 1141151 := bstep (se 1 (by rfl) ⟨855863, by rfl⟩ : syracuseStep 1141151 = 1711727) B1711727
theorem B1141231 : Blo 1140634 1141231 := bstep (se 1 (by rfl) ⟨855923, by rfl⟩ : syracuseStep 1141231 = 1711847) B1711847
theorem B1141415 : Blo 1140634 1141415 := bstep (se 1 (by rfl) ⟨856061, by rfl⟩ : syracuseStep 1141415 = 1712123) B1712123
theorem B1141455 : Blo 1140634 1141455 := bstep (se 1 (by rfl) ⟨856091, by rfl⟩ : syracuseStep 1141455 = 1712183) B1712183
theorem B1141535 : Blo 1140634 1141535 := bstep (se 1 (by rfl) ⟨856151, by rfl⟩ : syracuseStep 1141535 = 1712303) B1712303
theorem B4877147 : Blo 1140634 4877147 := bstep (se 1 (by rfl) ⟨3657860, by rfl⟩ : syracuseStep 4877147 = 7315721) B7315721
theorem B3861377 : Blo 1140634 3861377 := bstep (se 2 (by rfl) ⟨1448016, by rfl⟩ : syracuseStep 3861377 = 2896033) B2896033
theorem B1141671 : Blo 1140634 1141671 := bstep (se 1 (by rfl) ⟨856253, by rfl⟩ : syracuseStep 1141671 = 1712507) B1712507
theorem B2059177 : Blo 1140634 2059177 := bstep (se 2 (by rfl) ⟨772191, by rfl⟩ : syracuseStep 2059177 = 1544383) B1544383
theorem B1141787 : Blo 1140634 1141787 := bstep (se 1 (by rfl) ⟨856340, by rfl⟩ : syracuseStep 1141787 = 1712681) B1712681
theorem B1141851 : Blo 1140634 1141851 := bstep (se 1 (by rfl) ⟨856388, by rfl⟩ : syracuseStep 1141851 = 1712777) B1712777
theorem B1141991 : Blo 1140634 1141991 := bstep (se 1 (by rfl) ⟨856493, by rfl⟩ : syracuseStep 1141991 = 1712987) B1712987
theorem B1142015 : Blo 1140634 1142015 := bstep (se 1 (by rfl) ⟨856511, by rfl⟩ : syracuseStep 1142015 = 1713023) B1713023
theorem B1142063 : Blo 1140634 1142063 := bstep (se 1 (by rfl) ⟨856547, by rfl⟩ : syracuseStep 1142063 = 1713095) B1713095
theorem B1142207 : Blo 1140634 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B1142303 : Blo 1140634 1142303 := bstep (se 1 (by rfl) ⟨856727, by rfl⟩ : syracuseStep 1142303 = 1713455) B1713455
theorem B1142431 : Blo 1140634 1142431 := bstep (se 1 (by rfl) ⟨856823, by rfl⟩ : syracuseStep 1142431 = 1713647) B1713647
theorem B1142439 : Blo 1140634 1142439 := bstep (se 1 (by rfl) ⟨856829, by rfl⟩ : syracuseStep 1142439 = 1713659) B1713659
theorem B1142463 : Blo 1140634 1142463 := bstep (se 1 (by rfl) ⟨856847, by rfl⟩ : syracuseStep 1142463 = 1713695) B1713695
theorem B10415897 : Blo 1140634 10415897 := bstep (se 2 (by rfl) ⟨3905961, by rfl⟩ : syracuseStep 10415897 = 7811923) B7811923
theorem B1142559 : Blo 1140634 1142559 := bstep (se 1 (by rfl) ⟨856919, by rfl⟩ : syracuseStep 1142559 = 1713839) B1713839
theorem B1142619 : Blo 1140634 1142619 := bstep (se 1 (by rfl) ⟨856964, by rfl⟩ : syracuseStep 1142619 = 1713929) B1713929
theorem B1142639 : Blo 1140634 1142639 := bstep (se 1 (by rfl) ⟨856979, by rfl⟩ : syracuseStep 1142639 = 1713959) B1713959
theorem B8679473 : Blo 1140634 8679473 := bstep (se 2 (by rfl) ⟨3254802, by rfl⟩ : syracuseStep 8679473 = 6509605) B6509605
theorem B9760823 : Blo 1140634 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B3862619 : Blo 1140634 3862619 := bstep (se 1 (by rfl) ⟨2896964, by rfl⟩ : syracuseStep 3862619 = 5793929) B5793929
theorem B16478315 : Blo 1140634 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B1143039 : Blo 1140634 1143039 := bstep (se 1 (by rfl) ⟨857279, by rfl⟩ : syracuseStep 1143039 = 1714559) B1714559
theorem B1143199 : Blo 1140634 1143199 := bstep (se 1 (by rfl) ⟨857399, by rfl⟩ : syracuseStep 1143199 = 1714799) B1714799
theorem B1143343 : Blo 1140634 1143343 := bstep (se 1 (by rfl) ⟨857507, by rfl⟩ : syracuseStep 1143343 = 1715015) B1715015
theorem B4879129 : Blo 1140634 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B1143743 : Blo 1140634 1143743 := bstep (se 1 (by rfl) ⟨857807, by rfl⟩ : syracuseStep 1143743 = 1715615) B1715615
theorem B1930223 : Blo 1140634 1930223 := bstep (se 1 (by rfl) ⟨1447667, by rfl⟩ : syracuseStep 1930223 = 2895335) B2895335
theorem B1143919 : Blo 1140634 1143919 := bstep (se 1 (by rfl) ⟨857939, by rfl⟩ : syracuseStep 1143919 = 1715879) B1715879
theorem B1143935 : Blo 1140634 1143935 := bstep (se 1 (by rfl) ⟨857951, by rfl⟩ : syracuseStep 1143935 = 1715903) B1715903
theorem B1143999 : Blo 1140634 1143999 := bstep (se 1 (by rfl) ⟨857999, by rfl⟩ : syracuseStep 1143999 = 1715999) B1715999
theorem B1144191 : Blo 1140634 1144191 := bstep (se 1 (by rfl) ⟨858143, by rfl⟩ : syracuseStep 1144191 = 1716287) B1716287
theorem B1930729 : Blo 1140634 1930729 := bstep (se 2 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 1930729 = 1448047) B1448047
theorem B3470845 : Blo 1140634 3470845 := bstep (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) B1301567
theorem B1144319 : Blo 1140634 1144319 := bstep (se 1 (by rfl) ⟨858239, by rfl⟩ : syracuseStep 1144319 = 1716479) B1716479
theorem B1144347 : Blo 1140634 1144347 := bstep (se 1 (by rfl) ⟨858260, by rfl⟩ : syracuseStep 1144347 = 1716521) B1716521
theorem B1144527 : Blo 1140634 1144527 := bstep (se 1 (by rfl) ⟨858395, by rfl⟩ : syracuseStep 1144527 = 1716791) B1716791
theorem B17561297 : Blo 1140634 17561297 := bstep (se 2 (by rfl) ⟨6585486, by rfl⟩ : syracuseStep 17561297 = 13170973) B13170973
theorem B14646203 : Blo 1140634 14646203 := bstep (se 1 (by rfl) ⟨10984652, by rfl⟩ : syracuseStep 14646203 = 21969305) B21969305
theorem B4881505 : Blo 1140634 4881505 := bstep (se 2 (by rfl) ⟨1830564, by rfl⟩ : syracuseStep 4881505 = 3661129) B3661129
theorem B8682875 : Blo 1140634 8682875 := bstep (se 1 (by rfl) ⟨6512156, by rfl⟩ : syracuseStep 8682875 = 13024313) B13024313
theorem B8781455 : Blo 1140634 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B9764819 : Blo 1140634 9764819 := bstep (se 1 (by rfl) ⟨7323614, by rfl⟩ : syracuseStep 9764819 = 14647229) B14647229
theorem B3866807 : Blo 1140634 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B9765197 : Blo 1140634 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B26085007 : Blo 1140634 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B4884391 : Blo 1140634 4884391 := bstep (se 1 (by rfl) ⟨3663293, by rfl⟩ : syracuseStep 4884391 = 7326587) B7326587
theorem B25398041 : Blo 1140634 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B1444711 : Blo 1140634 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B2165753 : Blo 1140634 2165753 := bstep (se 2 (by rfl) ⟨812157, by rfl⟩ : syracuseStep 2165753 = 1624315) B1624315
theorem B2887721 : Blo 1140634 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B46830125 : Blo 1140634 46830125 := bstep (se 3 (by rfl) ⟨8780648, by rfl⟩ : syracuseStep 46830125 = 17561297) B17561297
theorem B3085823 : Blo 1140634 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B89003609 : Blo 1140634 89003609 := bstep (se 2 (by rfl) ⟨33376353, by rfl⟩ : syracuseStep 89003609 = 66752707) B66752707
theorem B3250145 : Blo 1140634 3250145 := bstep (se 2 (by rfl) ⟨1218804, by rfl⟩ : syracuseStep 3250145 = 2437609) B2437609
theorem B1448219 : Blo 1140634 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B2890687 : Blo 1140634 2890687 := bstep (se 1 (by rfl) ⟨2168015, by rfl⟩ : syracuseStep 2890687 = 4336031) B4336031
theorem B3251431 : Blo 1140634 3251431 := bstep (se 1 (by rfl) ⟨2438573, by rfl⟩ : syracuseStep 3251431 = 4877147) B4877147
theorem B3087695 : Blo 1140634 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B4627793 : Blo 1140634 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B1711481 : Blo 1140634 1711481 := bstep (se 2 (by rfl) ⟨641805, by rfl⟩ : syracuseStep 1711481 = 1283611) B1283611
theorem B1711721 : Blo 1140634 1711721 := bstep (se 2 (by rfl) ⟨641895, by rfl⟩ : syracuseStep 1711721 = 1283791) B1283791
theorem B7806665 : Blo 1140634 7806665 := bstep (se 2 (by rfl) ⟨2927499, by rfl⟩ : syracuseStep 7806665 = 5854999) B5854999
theorem B10985543 : Blo 1140634 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B1712219 : Blo 1140634 1712219 := bstep (se 1 (by rfl) ⟨1284164, by rfl⟩ : syracuseStep 1712219 = 2568329) B2568329
theorem B2891963 : Blo 1140634 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B200286827 : Blo 1140634 200286827 := bstep (se 1 (by rfl) ⟨150215120, by rfl⟩ : syracuseStep 200286827 = 300430241) B300430241
theorem B4825757 : Blo 1140634 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B1286815 : Blo 1140634 1286815 := bstep (se 1 (by rfl) ⟨965111, by rfl⟩ : syracuseStep 1286815 = 1930223) B1930223
theorem B19538657 : Blo 1140634 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B9773945 : Blo 1140634 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B1713065 : Blo 1140634 1713065 := bstep (se 2 (by rfl) ⟨642399, by rfl⟩ : syracuseStep 1713065 = 1284799) B1284799
theorem B5776595 : Blo 1140634 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B1713719 : Blo 1140634 1713719 := bstep (se 1 (by rfl) ⟨1285289, by rfl⟩ : syracuseStep 1713719 = 2570579) B2570579
theorem B1713767 : Blo 1140634 1713767 := bstep (se 1 (by rfl) ⟨1285325, by rfl⟩ : syracuseStep 1713767 = 2570651) B2570651
theorem B2893907 : Blo 1140634 2893907 := bstep (se 1 (by rfl) ⟨2170430, by rfl⟩ : syracuseStep 2893907 = 4340861) B4340861
theorem B55552193 : Blo 1140634 55552193 := bstep (se 2 (by rfl) ⟨20832072, by rfl⟩ : syracuseStep 55552193 = 41664145) B41664145
theorem B2894251 : Blo 1140634 2894251 := bstep (se 1 (by rfl) ⟨2170688, by rfl⟩ : syracuseStep 2894251 = 4341377) B4341377
theorem B2566907 : Blo 1140634 2566907 := bstep (se 1 (by rfl) ⟨1925180, by rfl⟩ : syracuseStep 2566907 = 3850361) B3850361
theorem B101722931 : Blo 1140634 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B2567033 : Blo 1140634 2567033 := bstep (se 2 (by rfl) ⟨962637, by rfl⟩ : syracuseStep 2567033 = 1925275) B1925275
theorem B1715195 : Blo 1140634 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B1158311 : Blo 1140634 1158311 := bstep (se 1 (by rfl) ⟨868733, by rfl⟩ : syracuseStep 1158311 = 1737467) B1737467
theorem B1715435 : Blo 1140634 1715435 := bstep (se 1 (by rfl) ⟨1286576, by rfl⟩ : syracuseStep 1715435 = 2573153) B2573153
theorem B3911051 : Blo 1140634 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B2862503 : Blo 1140634 2862503 := bstep (se 1 (by rfl) ⟨2146877, by rfl⟩ : syracuseStep 2862503 = 4293755) B4293755
theorem B5778863 : Blo 1140634 5778863 := bstep (se 1 (by rfl) ⟨4334147, by rfl⟩ : syracuseStep 5778863 = 8668295) B8668295
theorem B5779187 : Blo 1140634 5779187 := bstep (se 1 (by rfl) ⟨4334390, by rfl⟩ : syracuseStep 5779187 = 8668781) B8668781
theorem B9776983 : Blo 1140634 9776983 := bstep (se 1 (by rfl) ⟨7332737, by rfl⟩ : syracuseStep 9776983 = 14665475) B14665475
theorem B2568059 : Blo 1140634 2568059 := bstep (se 1 (by rfl) ⟨1926044, by rfl⟩ : syracuseStep 2568059 = 3852089) B3852089
theorem B1322951 : Blo 1140634 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B2568167 : Blo 1140634 2568167 := bstep (se 1 (by rfl) ⟨1926125, by rfl⟩ : syracuseStep 2568167 = 3852251) B3852251
theorem B2568239 : Blo 1140634 2568239 := bstep (se 1 (by rfl) ⟨1926179, by rfl⟩ : syracuseStep 2568239 = 3852359) B3852359
theorem B1716827 : Blo 1140634 1716827 := bstep (se 1 (by rfl) ⟨1287620, by rfl⟩ : syracuseStep 1716827 = 2575241) B2575241
theorem B8926289 : Blo 1140634 8926289 := bstep (se 2 (by rfl) ⟨3347358, by rfl⟩ : syracuseStep 8926289 = 6694717) B6694717
theorem B5780807 : Blo 1140634 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B2570003 : Blo 1140634 2570003 := bstep (se 1 (by rfl) ⟨1927502, by rfl⟩ : syracuseStep 2570003 = 3855005) B3855005
theorem B12335591 : Blo 1140634 12335591 := bstep (se 1 (by rfl) ⟨9251693, by rfl⟩ : syracuseStep 12335591 = 18503387) B18503387
theorem B2571047 : Blo 1140634 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B12368807 : Blo 1140634 12368807 := bstep (se 1 (by rfl) ⟨9276605, by rfl⟩ : syracuseStep 12368807 = 18553211) B18553211
theorem B16694261 : Blo 1140634 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B5782751 : Blo 1140634 5782751 := bstep (se 1 (by rfl) ⟨4337063, by rfl⟩ : syracuseStep 5782751 = 8674127) B8674127
theorem B2571515 : Blo 1140634 2571515 := bstep (se 1 (by rfl) ⟨1928636, by rfl⟩ : syracuseStep 2571515 = 3857273) B3857273
theorem B4341863 : Blo 1140634 4341863 := bstep (se 1 (by rfl) ⟨3256397, by rfl⟩ : syracuseStep 4341863 = 6512795) B6512795
theorem B2572415 : Blo 1140634 2572415 := bstep (se 1 (by rfl) ⟨1929311, by rfl⟩ : syracuseStep 2572415 = 3858623) B3858623
theorem B2572775 : Blo 1140634 2572775 := bstep (se 1 (by rfl) ⟨1929581, by rfl⟩ : syracuseStep 2572775 = 3859163) B3859163
theorem B4342319 : Blo 1140634 4342319 := bstep (se 1 (by rfl) ⟨3256739, by rfl⟩ : syracuseStep 4342319 = 6513479) B6513479
theorem B2572883 : Blo 1140634 2572883 := bstep (se 1 (by rfl) ⟨1929662, by rfl⟩ : syracuseStep 2572883 = 3859325) B3859325
theorem B6505505 : Blo 1140634 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B11453561 : Blo 1140634 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B3654887 : Blo 1140634 3654887 := bstep (se 1 (by rfl) ⟨2741165, by rfl⟩ : syracuseStep 3654887 = 5482331) B5482331
theorem B3851495 : Blo 1140634 3851495 := bstep (se 1 (by rfl) ⟨2888621, by rfl⟩ : syracuseStep 3851495 = 5777243) B5777243
theorem B2573567 : Blo 1140634 2573567 := bstep (se 1 (by rfl) ⟨1930175, by rfl⟩ : syracuseStep 2573567 = 3860351) B3860351
theorem B3851549 : Blo 1140634 3851549 := bstep (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) B1444331
theorem B2574251 : Blo 1140634 2574251 := bstep (se 1 (by rfl) ⟨1930688, by rfl⟩ : syracuseStep 2574251 = 3861377) B3861377
theorem B4179923 : Blo 1140634 4179923 := bstep (se 1 (by rfl) ⟨3134942, by rfl⟩ : syracuseStep 4179923 = 6269885) B6269885
theorem B2574305 : Blo 1140634 2574305 := bstep (se 2 (by rfl) ⟨965364, by rfl⟩ : syracuseStep 2574305 = 1930729) B1930729
theorem B3852953 : Blo 1140634 3852953 := bstep (se 2 (by rfl) ⟨1444857, by rfl⟩ : syracuseStep 3852953 = 2889715) B2889715
theorem B5786315 : Blo 1140634 5786315 := bstep (se 1 (by rfl) ⟨4339736, by rfl⟩ : syracuseStep 5786315 = 8679473) B8679473
theorem B6507215 : Blo 1140634 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B2575079 : Blo 1140634 2575079 := bstep (se 1 (by rfl) ⟨1931309, by rfl⟩ : syracuseStep 2575079 = 3862619) B3862619
theorem B1952543 : Blo 1140634 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B5786477 : Blo 1140634 5786477 := bstep (se 3 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 5786477 = 2169929) B2169929
theorem B3853223 : Blo 1140634 3853223 := bstep (se 1 (by rfl) ⟨2889917, by rfl⟩ : syracuseStep 3853223 = 5779835) B5779835
theorem B4344961 : Blo 1140634 4344961 := bstep (se 2 (by rfl) ⟨1629360, by rfl⟩ : syracuseStep 4344961 = 3258721) B3258721
theorem B7327817 : Blo 1140634 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B6508673 : Blo 1140634 6508673 := bstep (se 2 (by rfl) ⟨2440752, by rfl⟩ : syracuseStep 6508673 = 4881505) B4881505
theorem B7820189 : Blo 1140634 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B5788583 : Blo 1140634 5788583 := bstep (se 1 (by rfl) ⟨4341437, by rfl⟩ : syracuseStep 5788583 = 8682875) B8682875
theorem B5854303 : Blo 1140634 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B2741359 : Blo 1140634 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B3855545 : Blo 1140634 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B2741473 : Blo 1140634 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B6509879 : Blo 1140634 6509879 := bstep (se 1 (by rfl) ⟨4882409, by rfl⟩ : syracuseStep 6509879 = 9764819) B9764819
theorem B1627561 : Blo 1140634 1627561 := bstep (se 2 (by rfl) ⟨610335, by rfl⟩ : syracuseStep 1627561 = 1220671) B1220671
theorem B5494463 : Blo 1140634 5494463 := bstep (se 1 (by rfl) ⟨4120847, by rfl⟩ : syracuseStep 5494463 = 8241695) B8241695
theorem B1628267 : Blo 1140634 1628267 := bstep (se 1 (by rfl) ⟨1221200, by rfl⟩ : syracuseStep 1628267 = 2442401) B2442401
theorem B3857057 : Blo 1140634 3857057 := bstep (se 2 (by rfl) ⟨1446396, by rfl⟩ : syracuseStep 3857057 = 2892793) B2892793
theorem B12999527 : Blo 1140634 12999527 := bstep (se 1 (by rfl) ⟨9749645, by rfl⟩ : syracuseStep 12999527 = 19499291) B19499291
theorem B1236071 : Blo 1140634 1236071 := bstep (se 1 (by rfl) ⟨927053, by rfl⟩ : syracuseStep 1236071 = 1854107) B1854107
theorem B47471741 : Blo 1140634 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B19521161 : Blo 1140634 19521161 := bstep (se 2 (by rfl) ⟨7320435, by rfl⟩ : syracuseStep 19521161 = 14640871) B14640871
theorem B4120399 : Blo 1140634 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B6184795 : Blo 1140634 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B5791661 : Blo 1140634 5791661 := bstep (se 3 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 5791661 = 2171873) B2171873
theorem B5791823 : Blo 1140634 5791823 := bstep (se 1 (by rfl) ⟨4343867, by rfl⟩ : syracuseStep 5791823 = 8687735) B8687735
theorem B14639231 : Blo 1140634 14639231 := bstep (se 1 (by rfl) ⟨10979423, by rfl⟩ : syracuseStep 14639231 = 21958847) B21958847
theorem B1925545 : Blo 1140634 1925545 := bstep (se 2 (by rfl) ⟨722079, by rfl⟩ : syracuseStep 1925545 = 1444159) B1444159
theorem B1925599 : Blo 1140634 1925599 := bstep (se 1 (by rfl) ⟨1444199, by rfl⟩ : syracuseStep 1925599 = 2888399) B2888399
theorem B5792633 : Blo 1140634 5792633 := bstep (se 2 (by rfl) ⟨2172237, by rfl⟩ : syracuseStep 5792633 = 4344475) B4344475
theorem B1926335 : Blo 1140634 1926335 := bstep (se 1 (by rfl) ⟨1444751, by rfl⟩ : syracuseStep 1926335 = 2889503) B2889503
theorem B2745569 : Blo 1140634 2745569 := bstep (se 2 (by rfl) ⟨1029588, by rfl⟩ : syracuseStep 2745569 = 2059177) B2059177
theorem B1926895 : Blo 1140634 1926895 := bstep (se 1 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 1926895 = 2890343) B2890343
theorem B6252349 : Blo 1140634 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B1926983 : Blo 1140634 1926983 := bstep (se 1 (by rfl) ⟨1445237, by rfl⟩ : syracuseStep 1926983 = 2890475) B2890475
theorem B6514937 : Blo 1140634 6514937 := bstep (se 2 (by rfl) ⟨2443101, by rfl⟩ : syracuseStep 6514937 = 4886203) B4886203
theorem B10972043 : Blo 1140634 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B13200353 : Blo 1140634 13200353 := bstep (se 2 (by rfl) ⟨4950132, by rfl⟩ : syracuseStep 13200353 = 9900265) B9900265
theorem B2747567 : Blo 1140634 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B1371439 : Blo 1140634 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B1928569 : Blo 1140634 1928569 := bstep (se 2 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 1928569 = 1446427) B1446427
theorem B1142319 : Blo 1140634 1142319 := bstep (se 1 (by rfl) ⟨856739, by rfl⟩ : syracuseStep 1142319 = 1713479) B1713479
theorem B4878377 : Blo 1140634 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B1142875 : Blo 1140634 1142875 := bstep (se 1 (by rfl) ⟨857156, by rfl⟩ : syracuseStep 1142875 = 1714313) B1714313
theorem B41644307 : Blo 1140634 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B1143323 : Blo 1140634 1143323 := bstep (se 1 (by rfl) ⟨857492, by rfl⟩ : syracuseStep 1143323 = 1714985) B1714985
theorem B1143451 : Blo 1140634 1143451 := bstep (se 1 (by rfl) ⟨857588, by rfl⟩ : syracuseStep 1143451 = 1715177) B1715177
theorem B1143775 : Blo 1140634 1143775 := bstep (se 1 (by rfl) ⟨857831, by rfl⟩ : syracuseStep 1143775 = 1715663) B1715663
theorem B1143839 : Blo 1140634 1143839 := bstep (se 1 (by rfl) ⟨857879, by rfl⟩ : syracuseStep 1143839 = 1715759) B1715759
theorem B6943931 : Blo 1140634 6943931 := bstep (se 1 (by rfl) ⟨5207948, by rfl⟩ : syracuseStep 6943931 = 10415897) B10415897
theorem B1144287 : Blo 1140634 1144287 := bstep (se 1 (by rfl) ⟨858215, by rfl⟩ : syracuseStep 1144287 = 1716431) B1716431
theorem B1144367 : Blo 1140634 1144367 := bstep (se 1 (by rfl) ⟨858275, by rfl⟩ : syracuseStep 1144367 = 1716551) B1716551
theorem B10974811 : Blo 1140634 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B6518879 : Blo 1140634 6518879 := bstep (se 1 (by rfl) ⟨4889159, by rfl⟩ : syracuseStep 6518879 = 9778319) B9778319
theorem B9764135 : Blo 1140634 9764135 := bstep (se 1 (by rfl) ⟨7323101, by rfl⟩ : syracuseStep 9764135 = 14646203) B14646203
theorem B10976735 : Blo 1140634 10976735 := bstep (se 1 (by rfl) ⟨8232551, by rfl⟩ : syracuseStep 10976735 = 16465103) B16465103
theorem B7635707 : Blo 1140634 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B2786615 : Blo 1140634 2786615 := bstep (se 1 (by rfl) ⟨2089961, by rfl⟩ : syracuseStep 2786615 = 4179923) B4179923
theorem B1443835 : Blo 1140634 1443835 := bstep (se 1 (by rfl) ⟨1082876, by rfl⟩ : syracuseStep 1443835 = 2165753) B2165753
theorem B4885211 : Blo 1140634 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B5213459 : Blo 1140634 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B2166763 : Blo 1140634 2166763 := bstep (se 1 (by rfl) ⟨1625072, by rfl⟩ : syracuseStep 2166763 = 3250145) B3250145
theorem B8228861 : Blo 1140634 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B13014107 : Blo 1140634 13014107 := bstep (se 1 (by rfl) ⟨9760580, by rfl⟩ : syracuseStep 13014107 = 19521161) B19521161
theorem B3217171 : Blo 1140634 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B1284223 : Blo 1140634 1284223 := bstep (se 1 (by rfl) ⟨963167, by rfl⟩ : syracuseStep 1284223 = 1926335) B1926335
theorem B1284655 : Blo 1140634 1284655 := bstep (se 1 (by rfl) ⟨963491, by rfl⟩ : syracuseStep 1284655 = 1926983) B1926983
theorem B7805737 : Blo 1140634 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B37034795 : Blo 1140634 37034795 := bstep (se 1 (by rfl) ⟨27776096, by rfl⟩ : syracuseStep 37034795 = 55552193) B55552193
theorem B1711271 : Blo 1140634 1711271 := bstep (se 1 (by rfl) ⟨1283453, by rfl⟩ : syracuseStep 1711271 = 2566907) B2566907
theorem B2170081 : Blo 1140634 2170081 := bstep (se 2 (by rfl) ⟨813780, by rfl⟩ : syracuseStep 2170081 = 1627561) B1627561
theorem B1711355 : Blo 1140634 1711355 := bstep (se 1 (by rfl) ⟨1283516, by rfl⟩ : syracuseStep 1711355 = 2567033) B2567033
theorem B7314695 : Blo 1140634 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1908335 : Blo 1140634 1908335 := bstep (se 1 (by rfl) ⟨1431251, by rfl⟩ : syracuseStep 1908335 = 2862503) B2862503
theorem B1712039 : Blo 1140634 1712039 := bstep (se 1 (by rfl) ⟨1284029, by rfl⟩ : syracuseStep 1712039 = 2568059) B2568059
theorem B1712111 : Blo 1140634 1712111 := bstep (se 1 (by rfl) ⟨1284083, by rfl⟩ : syracuseStep 1712111 = 2568167) B2568167
theorem B3252251 : Blo 1140634 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B1712159 : Blo 1140634 1712159 := bstep (se 1 (by rfl) ⟨1284119, by rfl⟩ : syracuseStep 1712159 = 2568239) B2568239
theorem B27762871 : Blo 1140634 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B3088829 : Blo 1140634 3088829 := bstep (se 3 (by rfl) ⟨579155, by rfl⟩ : syracuseStep 3088829 = 1158311) B1158311
theorem B4629287 : Blo 1140634 4629287 := bstep (se 1 (by rfl) ⟨3471965, by rfl⟩ : syracuseStep 4629287 = 6943931) B6943931
theorem B10429469 : Blo 1140634 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B1713335 : Blo 1140634 1713335 := bstep (se 1 (by rfl) ⟨1285001, by rfl⟩ : syracuseStep 1713335 = 2570003) B2570003
theorem B4335241 : Blo 1140634 4335241 := bstep (se 2 (by rfl) ⟨1625715, by rfl⟩ : syracuseStep 4335241 = 3251431) B3251431
theorem B20817773 : Blo 1140634 20817773 := bstep (se 3 (by rfl) ⟨3903332, by rfl⟩ : syracuseStep 20817773 = 7806665) B7806665
theorem B1714031 : Blo 1140634 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B1714343 : Blo 1140634 1714343 := bstep (se 1 (by rfl) ⟨1285757, by rfl⟩ : syracuseStep 1714343 = 2571515) B2571515
theorem B7317823 : Blo 1140634 7317823 := bstep (se 1 (by rfl) ⟨5488367, by rfl⟩ : syracuseStep 7317823 = 10976735) B10976735
theorem B2894575 : Blo 1140634 2894575 := bstep (se 1 (by rfl) ⟨2170931, by rfl⟩ : syracuseStep 2894575 = 4341863) B4341863
theorem B1714943 : Blo 1140634 1714943 := bstep (se 1 (by rfl) ⟨1286207, by rfl⟩ : syracuseStep 1714943 = 2572415) B2572415
theorem B1715183 : Blo 1140634 1715183 := bstep (se 1 (by rfl) ⟨1286387, by rfl⟩ : syracuseStep 1715183 = 2572775) B2572775
theorem B2894879 : Blo 1140634 2894879 := bstep (se 1 (by rfl) ⟨2171159, by rfl⟩ : syracuseStep 2894879 = 4342319) B4342319
theorem B1715255 : Blo 1140634 1715255 := bstep (se 1 (by rfl) ⟨1286441, by rfl⟩ : syracuseStep 1715255 = 2572883) B2572883
theorem B2567393 : Blo 1140634 2567393 := bstep (se 2 (by rfl) ⟨962772, by rfl⟩ : syracuseStep 2567393 = 1925545) B1925545
theorem B2567465 : Blo 1140634 2567465 := bstep (se 2 (by rfl) ⟨962799, by rfl⟩ : syracuseStep 2567465 = 1925599) B1925599
theorem B4337003 : Blo 1140634 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B2567663 : Blo 1140634 2567663 := bstep (se 1 (by rfl) ⟨1925747, by rfl⟩ : syracuseStep 2567663 = 3851495) B3851495
theorem B1715711 : Blo 1140634 1715711 := bstep (se 1 (by rfl) ⟨1286783, by rfl⟩ : syracuseStep 1715711 = 2573567) B2573567
theorem B2567699 : Blo 1140634 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B1715753 : Blo 1140634 1715753 := bstep (se 2 (by rfl) ⟨643407, by rfl⟩ : syracuseStep 1715753 = 1286815) B1286815
theorem B1716167 : Blo 1140634 1716167 := bstep (se 1 (by rfl) ⟨1287125, by rfl⟩ : syracuseStep 1716167 = 2574251) B2574251
theorem B1716203 : Blo 1140634 1716203 := bstep (se 1 (by rfl) ⟨1287152, by rfl⟩ : syracuseStep 1716203 = 2574305) B2574305
theorem B2568635 : Blo 1140634 2568635 := bstep (se 1 (by rfl) ⟨1926476, by rfl⟩ : syracuseStep 2568635 = 3852953) B3852953
theorem B4338143 : Blo 1140634 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B1716719 : Blo 1140634 1716719 := bstep (se 1 (by rfl) ⟨1287539, by rfl⟩ : syracuseStep 1716719 = 2575079) B2575079
theorem B2568815 : Blo 1140634 2568815 := bstep (se 1 (by rfl) ⟨1926611, by rfl⟩ : syracuseStep 2568815 = 3853223) B3853223
theorem B34780009 : Blo 1140634 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B2569193 : Blo 1140634 2569193 := bstep (se 2 (by rfl) ⟨963447, by rfl⟩ : syracuseStep 2569193 = 1926895) B1926895
theorem B8336465 : Blo 1140634 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B4339115 : Blo 1140634 4339115 := bstep (se 1 (by rfl) ⟨3254336, by rfl⟩ : syracuseStep 4339115 = 6508673) B6508673
theorem B9746365 : Blo 1140634 9746365 := bstep (se 3 (by rfl) ⟨1827443, by rfl⟩ : syracuseStep 9746365 = 3654887) B3654887
theorem B2570363 : Blo 1140634 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B4339919 : Blo 1140634 4339919 := bstep (se 1 (by rfl) ⟨3254939, by rfl⟩ : syracuseStep 4339919 = 6509879) B6509879
theorem B2571371 : Blo 1140634 2571371 := bstep (se 1 (by rfl) ⟨1928528, by rfl⟩ : syracuseStep 2571371 = 3857057) B3857057
theorem B2571425 : Blo 1140634 2571425 := bstep (se 2 (by rfl) ⟨964284, by rfl⟩ : syracuseStep 2571425 = 1928569) B1928569
theorem B8666351 : Blo 1140634 8666351 := bstep (se 1 (by rfl) ⟨6499763, by rfl⟩ : syracuseStep 8666351 = 12999527) B12999527
theorem B7323695 : Blo 1140634 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B4342045 : Blo 1140634 4342045 := bstep (se 3 (by rfl) ⟨814133, by rfl⟩ : syracuseStep 4342045 = 1628267) B1628267
theorem B13025771 : Blo 1140634 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B3851063 : Blo 1140634 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B3655145 : Blo 1140634 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B4343291 : Blo 1140634 4343291 := bstep (se 1 (by rfl) ⟨3257468, by rfl⟩ : syracuseStep 4343291 = 6514937) B6514937
theorem B3655297 : Blo 1140634 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B67815287 : Blo 1140634 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B8800235 : Blo 1140634 8800235 := bstep (se 1 (by rfl) ⟨6600176, by rfl⟩ : syracuseStep 8800235 = 13200353) B13200353
theorem B14633081 : Blo 1140634 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B3852575 : Blo 1140634 3852575 := bstep (se 1 (by rfl) ⟨2889431, by rfl⟩ : syracuseStep 3852575 = 5778863) B5778863
theorem B3852791 : Blo 1140634 3852791 := bstep (se 1 (by rfl) ⟨2889593, by rfl⟩ : syracuseStep 3852791 = 5779187) B5779187
theorem B270912437 : Blo 1140634 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B3296189 : Blo 1140634 3296189 := bstep (se 3 (by rfl) ⟨618035, by rfl⟩ : syracuseStep 3296189 = 1236071) B1236071
theorem B7326845 : Blo 1140634 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B5950859 : Blo 1140634 5950859 := bstep (se 1 (by rfl) ⟨4463144, by rfl⟩ : syracuseStep 5950859 = 8926289) B8926289
theorem B12340781 : Blo 1140634 12340781 := bstep (se 3 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 12340781 = 4627793) B4627793
theorem B3853871 : Blo 1140634 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B3854249 : Blo 1140634 3854249 := bstep (se 2 (by rfl) ⟨1445343, by rfl⟩ : syracuseStep 3854249 = 2890687) B2890687
theorem B4345919 : Blo 1140634 4345919 := bstep (se 1 (by rfl) ⟨3259439, by rfl⟩ : syracuseStep 4345919 = 6518879) B6518879
theorem B8245871 : Blo 1140634 8245871 := bstep (se 1 (by rfl) ⟨6184403, by rfl⟩ : syracuseStep 8245871 = 12368807) B12368807
theorem B11129507 : Blo 1140634 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B3855167 : Blo 1140634 3855167 := bstep (se 1 (by rfl) ⟨2891375, by rfl⟩ : syracuseStep 3855167 = 5782751) B5782751
theorem B6509423 : Blo 1140634 6509423 := bstep (se 1 (by rfl) ⟨4882067, by rfl⟩ : syracuseStep 6509423 = 9764135) B9764135
theorem B5493865 : Blo 1140634 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B8246393 : Blo 1140634 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B3527869 : Blo 1140634 3527869 := bstep (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) B1322951
theorem B2577871 : Blo 1140634 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B6510131 : Blo 1140634 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B3857543 : Blo 1140634 3857543 := bstep (se 1 (by rfl) ⟨2893157, by rfl⟩ : syracuseStep 3857543 = 5786315) B5786315
theorem B3857651 : Blo 1140634 3857651 := bstep (se 1 (by rfl) ⟨2893238, by rfl⟩ : syracuseStep 3857651 = 5786477) B5786477
theorem B6512521 : Blo 1140634 6512521 := bstep (se 2 (by rfl) ⟨2442195, by rfl⟩ : syracuseStep 6512521 = 4884391) B4884391
theorem B1925147 : Blo 1140634 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B31220083 : Blo 1140634 31220083 := bstep (se 1 (by rfl) ⟨23415062, by rfl⟩ : syracuseStep 31220083 = 46830125) B46830125
theorem B3859001 : Blo 1140634 3859001 := bstep (se 2 (by rfl) ⟨1447125, by rfl⟩ : syracuseStep 3859001 = 2894251) B2894251
theorem B3859055 : Blo 1140634 3859055 := bstep (se 1 (by rfl) ⟨2894291, by rfl⟩ : syracuseStep 3859055 = 5788583) B5788583
theorem B59335739 : Blo 1140634 59335739 := bstep (se 1 (by rfl) ⟨44501804, by rfl⟩ : syracuseStep 59335739 = 89003609) B89003609
theorem B3662975 : Blo 1140634 3662975 := bstep (se 1 (by rfl) ⟨2747231, by rfl⟩ : syracuseStep 3662975 = 5494463) B5494463
theorem B1926281 : Blo 1140634 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B5793281 : Blo 1140634 5793281 := bstep (se 2 (by rfl) ⟨2172480, by rfl⟩ : syracuseStep 5793281 = 4344961) B4344961
theorem B1828585 : Blo 1140634 1828585 := bstep (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) B1371439
theorem B31647827 : Blo 1140634 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B2058463 : Blo 1140634 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B1140987 : Blo 1140634 1140987 := bstep (se 1 (by rfl) ⟨855740, by rfl⟩ : syracuseStep 1140987 = 1711481) B1711481
theorem B1141147 : Blo 1140634 1141147 := bstep (se 1 (by rfl) ⟨855860, by rfl⟩ : syracuseStep 1141147 = 1711721) B1711721
theorem B13035977 : Blo 1140634 13035977 := bstep (se 2 (by rfl) ⟨4888491, by rfl⟩ : syracuseStep 13035977 = 9776983) B9776983
theorem B3861107 : Blo 1140634 3861107 := bstep (se 1 (by rfl) ⟨2895830, by rfl⟩ : syracuseStep 3861107 = 5791661) B5791661
theorem B3861215 : Blo 1140634 3861215 := bstep (se 1 (by rfl) ⟨2895911, by rfl⟩ : syracuseStep 3861215 = 5791823) B5791823
theorem B1141479 : Blo 1140634 1141479 := bstep (se 1 (by rfl) ⟨856109, by rfl⟩ : syracuseStep 1141479 = 1712219) B1712219
theorem B9759487 : Blo 1140634 9759487 := bstep (se 1 (by rfl) ⟨7319615, by rfl⟩ : syracuseStep 9759487 = 14639231) B14639231
theorem B1927975 : Blo 1140634 1927975 := bstep (se 1 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 1927975 = 2891963) B2891963
theorem B133524551 : Blo 1140634 133524551 := bstep (se 1 (by rfl) ⟨100143413, by rfl⟩ : syracuseStep 133524551 = 200286827) B200286827
theorem B6515963 : Blo 1140634 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B3861755 : Blo 1140634 3861755 := bstep (se 1 (by rfl) ⟨2896316, by rfl⟩ : syracuseStep 3861755 = 5792633) B5792633
theorem B1142043 : Blo 1140634 1142043 := bstep (se 1 (by rfl) ⟨856532, by rfl⟩ : syracuseStep 1142043 = 1713065) B1713065
theorem B3861917 : Blo 1140634 3861917 := bstep (se 3 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 3861917 = 1448219) B1448219
theorem B1830379 : Blo 1140634 1830379 := bstep (se 1 (by rfl) ⟨1372784, by rfl⟩ : syracuseStep 1830379 = 2745569) B2745569
theorem B1142479 : Blo 1140634 1142479 := bstep (se 1 (by rfl) ⟨856859, by rfl⟩ : syracuseStep 1142479 = 1713719) B1713719
theorem B1142511 : Blo 1140634 1142511 := bstep (se 1 (by rfl) ⟨856883, by rfl⟩ : syracuseStep 1142511 = 1713767) B1713767
theorem B32894909 : Blo 1140634 32894909 := bstep (se 3 (by rfl) ⟨6167795, by rfl⟩ : syracuseStep 32894909 = 12335591) B12335591
theorem B1929271 : Blo 1140634 1929271 := bstep (se 1 (by rfl) ⟨1446953, by rfl⟩ : syracuseStep 1929271 = 2893907) B2893907
theorem B1143463 : Blo 1140634 1143463 := bstep (se 1 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 1143463 = 1715195) B1715195
theorem B5206781 : Blo 1140634 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B1143623 : Blo 1140634 1143623 := bstep (se 1 (by rfl) ⟨857717, by rfl⟩ : syracuseStep 1143623 = 1715435) B1715435
theorem B1144551 : Blo 1140634 1144551 := bstep (se 1 (by rfl) ⟨858413, by rfl⟩ : syracuseStep 1144551 = 1716827) B1716827
theorem B4882463 : Blo 1140634 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B8683847 : Blo 1140634 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B5866823 : Blo 1140634 5866823 := bstep (se 1 (by rfl) ⟨4400117, by rfl⟩ : syracuseStep 5866823 = 8800235) B8800235
theorem B2197459 : Blo 1140634 2197459 := bstep (se 1 (by rfl) ⟨1648094, by rfl⟩ : syracuseStep 2197459 = 3296189) B3296189
theorem B4884563 : Blo 1140634 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3475639 : Blo 1140634 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B8227187 : Blo 1140634 8227187 := bstep (se 1 (by rfl) ⟨6170390, by rfl⟩ : syracuseStep 8227187 = 12340781) B12340781
theorem B13012649 : Blo 1140634 13012649 := bstep (se 2 (by rfl) ⟨4879743, by rfl⟩ : syracuseStep 13012649 = 9759487) B9759487
theorem B2889017 : Blo 1140634 2889017 := bstep (se 2 (by rfl) ⟨1083381, by rfl⟩ : syracuseStep 2889017 = 2166763) B2166763
theorem B1283431 : Blo 1140634 1283431 := bstep (se 1 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 1283431 = 1925147) B1925147
theorem B3086191 : Blo 1140634 3086191 := bstep (se 1 (by rfl) ⟨2314643, by rfl⟩ : syracuseStep 3086191 = 4629287) B4629287
theorem B6952979 : Blo 1140634 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B39557159 : Blo 1140634 39557159 := bstep (se 1 (by rfl) ⟨29667869, by rfl⟩ : syracuseStep 39557159 = 59335739) B59335739
theorem B1284187 : Blo 1140634 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B46373345 : Blo 1140634 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B8690651 : Blo 1140634 8690651 := bstep (se 1 (by rfl) ⟨6517988, by rfl⟩ : syracuseStep 8690651 = 13035977) B13035977
theorem B1711595 : Blo 1140634 1711595 := bstep (se 1 (by rfl) ⟨1283696, by rfl⟩ : syracuseStep 1711595 = 2567393) B2567393
theorem B1711643 : Blo 1140634 1711643 := bstep (se 1 (by rfl) ⟨1283732, by rfl⟩ : syracuseStep 1711643 = 2567465) B2567465
theorem B2891335 : Blo 1140634 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B1711775 : Blo 1140634 1711775 := bstep (se 1 (by rfl) ⟨1283831, by rfl⟩ : syracuseStep 1711775 = 2567663) B2567663
theorem B1711799 : Blo 1140634 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B21929939 : Blo 1140634 21929939 := bstep (se 1 (by rfl) ⟨16447454, by rfl⟩ : syracuseStep 21929939 = 32894909) B32894909
theorem B1712297 : Blo 1140634 1712297 := bstep (se 2 (by rfl) ⟨642111, by rfl⟩ : syracuseStep 1712297 = 1284223) B1284223
theorem B1712423 : Blo 1140634 1712423 := bstep (se 1 (by rfl) ⟨1284317, by rfl⟩ : syracuseStep 1712423 = 2568635) B2568635
theorem B2892095 : Blo 1140634 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B1712543 : Blo 1140634 1712543 := bstep (se 1 (by rfl) ⟨1284407, by rfl⟩ : syracuseStep 1712543 = 2568815) B2568815
theorem B1712795 : Blo 1140634 1712795 := bstep (se 1 (by rfl) ⟨1284596, by rfl⟩ : syracuseStep 1712795 = 2569193) B2569193
theorem B1712873 : Blo 1140634 1712873 := bstep (se 2 (by rfl) ⟨642327, by rfl⟩ : syracuseStep 1712873 = 1284655) B1284655
theorem B2892743 : Blo 1140634 2892743 := bstep (se 1 (by rfl) ⟨2169557, by rfl⟩ : syracuseStep 2892743 = 4339115) B4339115
theorem B15868957 : Blo 1140634 15868957 := bstep (se 3 (by rfl) ⟨2975429, by rfl⟩ : syracuseStep 15868957 = 5950859) B5950859
theorem B1713575 : Blo 1140634 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B2893279 : Blo 1140634 2893279 := bstep (se 1 (by rfl) ⟨2169959, by rfl⟩ : syracuseStep 2893279 = 4339919) B4339919
theorem B2893441 : Blo 1140634 2893441 := bstep (se 2 (by rfl) ⟨1085040, by rfl⟩ : syracuseStep 2893441 = 2170081) B2170081
theorem B1714247 : Blo 1140634 1714247 := bstep (se 1 (by rfl) ⟨1285685, by rfl⟩ : syracuseStep 1714247 = 2571371) B2571371
theorem B1714283 : Blo 1140634 1714283 := bstep (se 1 (by rfl) ⟨1285712, by rfl⟩ : syracuseStep 1714283 = 2571425) B2571425
theorem B5777567 : Blo 1140634 5777567 := bstep (se 1 (by rfl) ⟨4333175, by rfl⟩ : syracuseStep 5777567 = 8666351) B8666351
theorem B5090471 : Blo 1140634 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B2567375 : Blo 1140634 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B2436763 : Blo 1140634 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B2895527 : Blo 1140634 2895527 := bstep (se 1 (by rfl) ⟨2171645, by rfl⟩ : syracuseStep 2895527 = 4343291) B4343291
theorem B2568383 : Blo 1140634 2568383 := bstep (se 1 (by rfl) ⟨1926287, by rfl⟩ : syracuseStep 2568383 = 3852575) B3852575
theorem B2568527 : Blo 1140634 2568527 := bstep (se 1 (by rfl) ⟨1926395, by rfl⟩ : syracuseStep 2568527 = 3852791) B3852791
theorem B166507109 : Blo 1140634 166507109 := bstep (se 4 (by rfl) ⟨15610041, by rfl⟩ : syracuseStep 166507109 = 31220083) B31220083
theorem B5780321 : Blo 1140634 5780321 := bstep (se 2 (by rfl) ⟨2167620, by rfl⟩ : syracuseStep 5780321 = 4335241) B4335241
theorem B2438113 : Blo 1140634 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B2569247 : Blo 1140634 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B2569499 : Blo 1140634 2569499 := bstep (se 1 (by rfl) ⟨1927124, by rfl⟩ : syracuseStep 2569499 = 3854249) B3854249
theorem B5485907 : Blo 1140634 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B2897279 : Blo 1140634 2897279 := bstep (se 1 (by rfl) ⟨2172959, by rfl⟩ : syracuseStep 2897279 = 4345919) B4345919
theorem B7419671 : Blo 1140634 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B2570111 : Blo 1140634 2570111 := bstep (se 1 (by rfl) ⟨1927583, by rfl⟩ : syracuseStep 2570111 = 3855167) B3855167
theorem B4339615 : Blo 1140634 4339615 := bstep (se 1 (by rfl) ⟨3254711, by rfl⟩ : syracuseStep 4339615 = 6509423) B6509423
theorem B4340087 : Blo 1140634 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B2570633 : Blo 1140634 2570633 := bstep (se 2 (by rfl) ⟨963987, by rfl⟩ : syracuseStep 2570633 = 1927975) B1927975
theorem B24689863 : Blo 1140634 24689863 := bstep (se 1 (by rfl) ⟨18517397, by rfl⟩ : syracuseStep 24689863 = 37034795) B37034795
theorem B2440505 : Blo 1140634 2440505 := bstep (se 2 (by rfl) ⟨915189, by rfl⟩ : syracuseStep 2440505 = 1830379) B1830379
theorem B2571695 : Blo 1140634 2571695 := bstep (se 1 (by rfl) ⟨1928771, by rfl⟩ : syracuseStep 2571695 = 3857543) B3857543
theorem B2571767 : Blo 1140634 2571767 := bstep (se 1 (by rfl) ⟨1928825, by rfl⟩ : syracuseStep 2571767 = 3857651) B3857651
theorem B2572361 : Blo 1140634 2572361 := bstep (se 2 (by rfl) ⟨964635, by rfl⟩ : syracuseStep 2572361 = 1929271) B1929271
theorem B2572667 : Blo 1140634 2572667 := bstep (se 1 (by rfl) ⟨1929500, by rfl⟩ : syracuseStep 2572667 = 3859001) B3859001
theorem B2572703 : Blo 1140634 2572703 := bstep (se 1 (by rfl) ⟨1929527, by rfl⟩ : syracuseStep 2572703 = 3859055) B3859055
theorem B2441983 : Blo 1140634 2441983 := bstep (se 1 (by rfl) ⟨1831487, by rfl⟩ : syracuseStep 2441983 = 3662975) B3662975
theorem B13878515 : Blo 1140634 13878515 := bstep (se 1 (by rfl) ⟨10408886, by rfl⟩ : syracuseStep 13878515 = 20817773) B20817773
theorem B7325153 : Blo 1140634 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B4703825 : Blo 1140634 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B2574071 : Blo 1140634 2574071 := bstep (se 1 (by rfl) ⟨1930553, by rfl⟩ : syracuseStep 2574071 = 3861107) B3861107
theorem B2574143 : Blo 1140634 2574143 := bstep (se 1 (by rfl) ⟨1930607, by rfl⟩ : syracuseStep 2574143 = 3861215) B3861215
theorem B13027229 : Blo 1140634 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B89016367 : Blo 1140634 89016367 := bstep (se 1 (by rfl) ⟨66762275, by rfl⟩ : syracuseStep 89016367 = 133524551) B133524551
theorem B4343975 : Blo 1140634 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B2574503 : Blo 1140634 2574503 := bstep (se 1 (by rfl) ⟨1930877, by rfl⟩ : syracuseStep 2574503 = 3861755) B3861755
theorem B2574611 : Blo 1140634 2574611 := bstep (se 1 (by rfl) ⟨1930958, by rfl⟩ : syracuseStep 2574611 = 3861917) B3861917
theorem B12995153 : Blo 1140634 12995153 := bstep (se 2 (by rfl) ⟨4873182, by rfl⟩ : syracuseStep 12995153 = 9746365) B9746365
theorem B5557643 : Blo 1140634 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B10407649 : Blo 1140634 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B8672669 : Blo 1140634 8672669 := bstep (se 3 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 8672669 = 3252251) B3252251
theorem B37017161 : Blo 1140634 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B5789393 : Blo 1140634 5789393 := bstep (se 2 (by rfl) ⟨2171022, by rfl⟩ : syracuseStep 5789393 = 4342045) B4342045
theorem B1857743 : Blo 1140634 1857743 := bstep (se 1 (by rfl) ⟨1393307, by rfl⟩ : syracuseStep 1857743 = 2786615) B2786615
theorem B45210191 : Blo 1140634 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B9755387 : Blo 1140634 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B180608291 : Blo 1140634 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B1925113 : Blo 1140634 1925113 := bstep (se 2 (by rfl) ⟨721917, by rfl⟩ : syracuseStep 1925113 = 1443835) B1443835
theorem B2744617 : Blo 1140634 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B5497247 : Blo 1140634 5497247 := bstep (se 1 (by rfl) ⟨4122935, by rfl⟩ : syracuseStep 5497247 = 8245871) B8245871
theorem B9757097 : Blo 1140634 9757097 := bstep (se 2 (by rfl) ⟨3658911, by rfl⟩ : syracuseStep 9757097 = 7317823) B7317823
theorem B8676071 : Blo 1140634 8676071 := bstep (se 1 (by rfl) ⟨6507053, by rfl⟩ : syracuseStep 8676071 = 13014107) B13014107
theorem B5497595 : Blo 1140634 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B3859433 : Blo 1140634 3859433 := bstep (se 2 (by rfl) ⟨1447287, by rfl⟩ : syracuseStep 3859433 = 2894575) B2894575
theorem B1140847 : Blo 1140634 1140847 := bstep (se 1 (by rfl) ⟨855635, by rfl⟩ : syracuseStep 1140847 = 1711271) B1711271
theorem B1140903 : Blo 1140634 1140903 := bstep (se 1 (by rfl) ⟨855677, by rfl⟩ : syracuseStep 1140903 = 1711355) B1711355
theorem B4876463 : Blo 1140634 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B1272223 : Blo 1140634 1272223 := bstep (se 1 (by rfl) ⟨954167, by rfl⟩ : syracuseStep 1272223 = 1908335) B1908335
theorem B1141359 : Blo 1140634 1141359 := bstep (se 1 (by rfl) ⟨856019, by rfl⟩ : syracuseStep 1141359 = 1712039) B1712039
theorem B1141407 : Blo 1140634 1141407 := bstep (se 1 (by rfl) ⟨856055, by rfl⟩ : syracuseStep 1141407 = 1712111) B1712111
theorem B1141439 : Blo 1140634 1141439 := bstep (se 1 (by rfl) ⟨856079, by rfl⟩ : syracuseStep 1141439 = 1712159) B1712159
theorem B2059219 : Blo 1140634 2059219 := bstep (se 1 (by rfl) ⟨1544414, by rfl⟩ : syracuseStep 2059219 = 3088829) B3088829
theorem B1142223 : Blo 1140634 1142223 := bstep (se 1 (by rfl) ⟨856667, by rfl⟩ : syracuseStep 1142223 = 1713335) B1713335
theorem B3862187 : Blo 1140634 3862187 := bstep (se 1 (by rfl) ⟨2896640, by rfl⟩ : syracuseStep 3862187 = 5793281) B5793281
theorem B1142687 : Blo 1140634 1142687 := bstep (se 1 (by rfl) ⟨857015, by rfl⟩ : syracuseStep 1142687 = 1714031) B1714031
theorem B21098551 : Blo 1140634 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B1142895 : Blo 1140634 1142895 := bstep (se 1 (by rfl) ⟨857171, by rfl⟩ : syracuseStep 1142895 = 1714343) B1714343
theorem B1143295 : Blo 1140634 1143295 := bstep (se 1 (by rfl) ⟨857471, by rfl⟩ : syracuseStep 1143295 = 1714943) B1714943
theorem B3437161 : Blo 1140634 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B1143455 : Blo 1140634 1143455 := bstep (se 1 (by rfl) ⟨857591, by rfl⟩ : syracuseStep 1143455 = 1715183) B1715183
theorem B1929919 : Blo 1140634 1929919 := bstep (se 1 (by rfl) ⟨1447439, by rfl⟩ : syracuseStep 1929919 = 2894879) B2894879
theorem B1143503 : Blo 1140634 1143503 := bstep (se 1 (by rfl) ⟨857627, by rfl⟩ : syracuseStep 1143503 = 1715255) B1715255
theorem B1143807 : Blo 1140634 1143807 := bstep (se 1 (by rfl) ⟨857855, by rfl⟩ : syracuseStep 1143807 = 1715711) B1715711
theorem B4289561 : Blo 1140634 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B1143835 : Blo 1140634 1143835 := bstep (se 1 (by rfl) ⟨857876, by rfl⟩ : syracuseStep 1143835 = 1715753) B1715753
theorem B1144111 : Blo 1140634 1144111 := bstep (se 1 (by rfl) ⟨858083, by rfl⟩ : syracuseStep 1144111 = 1716167) B1716167
theorem B1144135 : Blo 1140634 1144135 := bstep (se 1 (by rfl) ⟨858101, by rfl⟩ : syracuseStep 1144135 = 1716203) B1716203
theorem B1144479 : Blo 1140634 1144479 := bstep (se 1 (by rfl) ⟨858359, by rfl⟩ : syracuseStep 1144479 = 1716719) B1716719
theorem B3471187 : Blo 1140634 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B19494917 : Blo 1140634 19494917 := bstep (se 4 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 19494917 = 3655297) B3655297
theorem B8683361 : Blo 1140634 8683361 := bstep (se 2 (by rfl) ⟨3256260, by rfl⟩ : syracuseStep 8683361 = 6512521) B6512521
theorem B4883435 : Blo 1140634 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B8684819 : Blo 1140634 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B3705095 : Blo 1140634 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B118688489 : Blo 1140634 118688489 := bstep (se 2 (by rfl) ⟨44508183, by rfl⟩ : syracuseStep 118688489 = 89016367) B89016367
theorem B24678107 : Blo 1140634 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B3249017 : Blo 1140634 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B14619959 : Blo 1140634 14619959 := bstep (se 1 (by rfl) ⟨10964969, by rfl⟩ : syracuseStep 14619959 = 21929939) B21929939
theorem B3250817 : Blo 1140634 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B120560509 : Blo 1140634 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B1711241 : Blo 1140634 1711241 := bstep (se 2 (by rfl) ⟨641715, by rfl⟩ : syracuseStep 1711241 = 1283431) B1283431
theorem B1711583 : Blo 1140634 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B4628249 : Blo 1140634 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B1712249 : Blo 1140634 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B1712255 : Blo 1140634 1712255 := bstep (se 1 (by rfl) ⟨1284191, by rfl⟩ : syracuseStep 1712255 = 2568383) B2568383
theorem B1712351 : Blo 1140634 1712351 := bstep (se 1 (by rfl) ⟨1284263, by rfl⟩ : syracuseStep 1712351 = 2568527) B2568527
theorem B2859707 : Blo 1140634 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B1712831 : Blo 1140634 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B1712999 : Blo 1140634 1712999 := bstep (se 1 (by rfl) ⟨1284749, by rfl⟩ : syracuseStep 1712999 = 2569499) B2569499
theorem B1713407 : Blo 1140634 1713407 := bstep (se 1 (by rfl) ⟨1285055, by rfl⟩ : syracuseStep 1713407 = 2570111) B2570111
theorem B2893391 : Blo 1140634 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B1713755 : Blo 1140634 1713755 := bstep (se 1 (by rfl) ⟨1285316, by rfl⟩ : syracuseStep 1713755 = 2570633) B2570633
theorem B1714463 : Blo 1140634 1714463 := bstep (se 1 (by rfl) ⟨1285847, by rfl⟩ : syracuseStep 1714463 = 2571695) B2571695
theorem B1714511 : Blo 1140634 1714511 := bstep (se 1 (by rfl) ⟨1285883, by rfl⟩ : syracuseStep 1714511 = 2571767) B2571767
theorem B2566817 : Blo 1140634 2566817 := bstep (se 2 (by rfl) ⟨962556, by rfl⟩ : syracuseStep 2566817 = 1925113) B1925113
theorem B3254975 : Blo 1140634 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B1714907 : Blo 1140634 1714907 := bstep (se 1 (by rfl) ⟨1286180, by rfl⟩ : syracuseStep 1714907 = 2572361) B2572361
theorem B1715111 : Blo 1140634 1715111 := bstep (se 1 (by rfl) ⟨1286333, by rfl⟩ : syracuseStep 1715111 = 2572667) B2572667
theorem B1715135 : Blo 1140634 1715135 := bstep (se 1 (by rfl) ⟨1286351, by rfl⟩ : syracuseStep 1715135 = 2572703) B2572703
theorem B9252343 : Blo 1140634 9252343 := bstep (se 1 (by rfl) ⟨6939257, by rfl⟩ : syracuseStep 9252343 = 13878515) B13878515
theorem B3911215 : Blo 1140634 3911215 := bstep (se 1 (by rfl) ⟨2933411, by rfl⟩ : syracuseStep 3911215 = 5866823) B5866823
theorem B3255977 : Blo 1140634 3255977 := bstep (se 2 (by rfl) ⟨1220991, by rfl⟩ : syracuseStep 3255977 = 2441983) B2441983
theorem B14659325 : Blo 1140634 14659325 := bstep (se 3 (by rfl) ⟨2748623, by rfl⟩ : syracuseStep 14659325 = 5497247) B5497247
theorem B1716047 : Blo 1140634 1716047 := bstep (se 1 (by rfl) ⟨1287035, by rfl⟩ : syracuseStep 1716047 = 2574071) B2574071
theorem B1716095 : Blo 1140634 1716095 := bstep (se 1 (by rfl) ⟨1287071, by rfl⟩ : syracuseStep 1716095 = 2574143) B2574143
theorem B3256375 : Blo 1140634 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B2895983 : Blo 1140634 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B1716335 : Blo 1140634 1716335 := bstep (se 1 (by rfl) ⟨1287251, by rfl⟩ : syracuseStep 1716335 = 2574503) B2574503
theorem B1716407 : Blo 1140634 1716407 := bstep (se 1 (by rfl) ⟨1287305, by rfl⟩ : syracuseStep 1716407 = 2574611) B2574611
theorem B5484791 : Blo 1140634 5484791 := bstep (se 1 (by rfl) ⟨4113593, by rfl⟩ : syracuseStep 5484791 = 8227187) B8227187
theorem B8663435 : Blo 1140634 8663435 := bstep (se 1 (by rfl) ⟨6497576, by rfl⟩ : syracuseStep 8663435 = 12995153) B12995153
theorem B2929945 : Blo 1140634 2929945 := bstep (se 2 (by rfl) ⟨1098729, by rfl⟩ : syracuseStep 2929945 = 2197459) B2197459
theorem B4634185 : Blo 1140634 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B18331525 : Blo 1140634 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B14629085 : Blo 1140634 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B5781779 : Blo 1140634 5781779 := bstep (se 1 (by rfl) ⟨4336334, by rfl⟩ : syracuseStep 5781779 = 8672669) B8672669
theorem B4635319 : Blo 1140634 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B30915563 : Blo 1140634 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B6503591 : Blo 1140634 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B120405527 : Blo 1140634 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B13876865 : Blo 1140634 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B28131401 : Blo 1140634 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B6504731 : Blo 1140634 6504731 := bstep (se 1 (by rfl) ⟨4878548, by rfl⟩ : syracuseStep 6504731 = 9757097) B9757097
theorem B5784047 : Blo 1140634 5784047 := bstep (se 1 (by rfl) ⟨4338035, by rfl⟩ : syracuseStep 5784047 = 8676071) B8676071
theorem B2572955 : Blo 1140634 2572955 := bstep (se 1 (by rfl) ⟨1929716, by rfl⟩ : syracuseStep 2572955 = 3859433) B3859433
theorem B2573225 : Blo 1140634 2573225 := bstep (se 2 (by rfl) ⟨964959, by rfl⟩ : syracuseStep 2573225 = 1929919) B1929919
theorem B3851711 : Blo 1140634 3851711 := bstep (se 1 (by rfl) ⟨2888783, by rfl⟩ : syracuseStep 3851711 = 5777567) B5777567
theorem B3393647 : Blo 1140634 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B2574791 : Blo 1140634 2574791 := bstep (se 1 (by rfl) ⟨1931093, by rfl⟩ : syracuseStep 2574791 = 3862187) B3862187
theorem B4114921 : Blo 1140634 4114921 := bstep (se 2 (by rfl) ⟨1543095, by rfl⟩ : syracuseStep 4114921 = 3086191) B3086191
theorem B5786153 : Blo 1140634 5786153 := bstep (se 2 (by rfl) ⟨2169807, by rfl⟩ : syracuseStep 5786153 = 4339615) B4339615
theorem B111004739 : Blo 1140634 111004739 := bstep (se 1 (by rfl) ⟨83253554, by rfl⟩ : syracuseStep 111004739 = 166507109) B166507109
theorem B3853547 : Blo 1140634 3853547 := bstep (se 1 (by rfl) ⟨2890160, by rfl⟩ : syracuseStep 3853547 = 5780321) B5780321
theorem B12996611 : Blo 1140634 12996611 := bstep (se 1 (by rfl) ⟨9747458, by rfl⟩ : syracuseStep 12996611 = 19494917) B19494917
theorem B32919817 : Blo 1140634 32919817 := bstep (se 2 (by rfl) ⟨12344931, by rfl⟩ : syracuseStep 32919817 = 24689863) B24689863
theorem B3855113 : Blo 1140634 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B1627003 : Blo 1140634 1627003 := bstep (se 1 (by rfl) ⟨1220252, by rfl⟩ : syracuseStep 1627003 = 2440505) B2440505
theorem B5788907 : Blo 1140634 5788907 := bstep (se 1 (by rfl) ⟨4341680, by rfl⟩ : syracuseStep 5788907 = 8683361) B8683361
theorem B5789231 : Blo 1140634 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B3659489 : Blo 1140634 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B3135883 : Blo 1140634 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B21158609 : Blo 1140634 21158609 := bstep (se 2 (by rfl) ⟨7934478, by rfl⟩ : syracuseStep 21158609 = 15868957) B15868957
theorem B3857705 : Blo 1140634 3857705 := bstep (se 2 (by rfl) ⟨1446639, by rfl⟩ : syracuseStep 3857705 = 2893279) B2893279
theorem B3857921 : Blo 1140634 3857921 := bstep (se 2 (by rfl) ⟨1446720, by rfl⟩ : syracuseStep 3857921 = 2893441) B2893441
theorem B8675099 : Blo 1140634 8675099 := bstep (se 1 (by rfl) ⟨6506324, by rfl⟩ : syracuseStep 8675099 = 13012649) B13012649
theorem B1696297 : Blo 1140634 1696297 := bstep (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) B1272223
theorem B1926011 : Blo 1140634 1926011 := bstep (se 1 (by rfl) ⟨1444508, by rfl⟩ : syracuseStep 1926011 = 2889017) B2889017
theorem B3859595 : Blo 1140634 3859595 := bstep (se 1 (by rfl) ⟨2894696, by rfl⟩ : syracuseStep 3859595 = 5789393) B5789393
theorem B2745625 : Blo 1140634 2745625 := bstep (se 2 (by rfl) ⟨1029609, by rfl⟩ : syracuseStep 2745625 = 2059219) B2059219
theorem B26371439 : Blo 1140634 26371439 := bstep (se 1 (by rfl) ⟨19778579, by rfl⟩ : syracuseStep 26371439 = 39557159) B39557159
theorem B1238495 : Blo 1140634 1238495 := bstep (se 1 (by rfl) ⟨928871, by rfl⟩ : syracuseStep 1238495 = 1857743) B1857743
theorem B5793767 : Blo 1140634 5793767 := bstep (se 1 (by rfl) ⟨4345325, by rfl⟩ : syracuseStep 5793767 = 8690651) B8690651
theorem B1141063 : Blo 1140634 1141063 := bstep (se 1 (by rfl) ⟨855797, by rfl⟩ : syracuseStep 1141063 = 1711595) B1711595
theorem B1141095 : Blo 1140634 1141095 := bstep (se 1 (by rfl) ⟨855821, by rfl⟩ : syracuseStep 1141095 = 1711643) B1711643
theorem B1141183 : Blo 1140634 1141183 := bstep (se 1 (by rfl) ⟨855887, by rfl⟩ : syracuseStep 1141183 = 1711775) B1711775
theorem B1141199 : Blo 1140634 1141199 := bstep (se 1 (by rfl) ⟨855899, by rfl⟩ : syracuseStep 1141199 = 1711799) B1711799
theorem B1141531 : Blo 1140634 1141531 := bstep (se 1 (by rfl) ⟨856148, by rfl⟩ : syracuseStep 1141531 = 1712297) B1712297
theorem B1141615 : Blo 1140634 1141615 := bstep (se 1 (by rfl) ⟨856211, by rfl⟩ : syracuseStep 1141615 = 1712423) B1712423
theorem B1928063 : Blo 1140634 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B1141695 : Blo 1140634 1141695 := bstep (se 1 (by rfl) ⟨856271, by rfl⟩ : syracuseStep 1141695 = 1712543) B1712543
theorem B1141863 : Blo 1140634 1141863 := bstep (se 1 (by rfl) ⟨856397, by rfl⟩ : syracuseStep 1141863 = 1712795) B1712795
theorem B13003901 : Blo 1140634 13003901 := bstep (se 3 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 13003901 = 4876463) B4876463
theorem B1141915 : Blo 1140634 1141915 := bstep (se 1 (by rfl) ⟨856436, by rfl⟩ : syracuseStep 1141915 = 1712873) B1712873
theorem B3665063 : Blo 1140634 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B1928495 : Blo 1140634 1928495 := bstep (se 1 (by rfl) ⟨1446371, by rfl⟩ : syracuseStep 1928495 = 2892743) B2892743
theorem B1142383 : Blo 1140634 1142383 := bstep (se 1 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 1142383 = 1713575) B1713575
theorem B1142831 : Blo 1140634 1142831 := bstep (se 1 (by rfl) ⟨857123, by rfl⟩ : syracuseStep 1142831 = 1714247) B1714247
theorem B1142855 : Blo 1140634 1142855 := bstep (se 1 (by rfl) ⟨857141, by rfl⟩ : syracuseStep 1142855 = 1714283) B1714283
theorem B1930351 : Blo 1140634 1930351 := bstep (se 1 (by rfl) ⟨1447763, by rfl⟩ : syracuseStep 1930351 = 2895527) B2895527
theorem B1931519 : Blo 1140634 1931519 := bstep (se 1 (by rfl) ⟨1448639, by rfl⟩ : syracuseStep 1931519 = 2897279) B2897279
theorem B4946447 : Blo 1140634 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B2261729 : Blo 1140634 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B2262431 : Blo 1140634 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B16452071 : Blo 1140634 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B2166011 : Blo 1140634 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B2167211 : Blo 1140634 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B5214953 : Blo 1140634 5214953 := bstep (se 2 (by rfl) ⟨1955607, by rfl⟩ : syracuseStep 5214953 = 3911215) B3911215
theorem B3085499 : Blo 1140634 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B1906471 : Blo 1140634 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B1284007 : Blo 1140634 1284007 := bstep (se 1 (by rfl) ⟨963005, by rfl⟩ : syracuseStep 1284007 = 1926011) B1926011
theorem B2169337 : Blo 1140634 2169337 := bstep (se 2 (by rfl) ⟨813501, by rfl⟩ : syracuseStep 2169337 = 1627003) B1627003
theorem B3906593 : Blo 1140634 3906593 := bstep (se 2 (by rfl) ⟨1464972, by rfl⟩ : syracuseStep 3906593 = 2929945) B2929945
theorem B1711211 : Blo 1140634 1711211 := bstep (se 1 (by rfl) ⟨1283408, by rfl⟩ : syracuseStep 1711211 = 2566817) B2566817
theorem B2169983 : Blo 1140634 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B1285375 : Blo 1140634 1285375 := bstep (se 1 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 1285375 = 1928063) B1928063
theorem B1285663 : Blo 1140634 1285663 := bstep (se 1 (by rfl) ⟨964247, by rfl⟩ : syracuseStep 1285663 = 1928495) B1928495
theorem B2170651 : Blo 1140634 2170651 := bstep (se 1 (by rfl) ⟨1627988, by rfl⟩ : syracuseStep 2170651 = 3255977) B3255977
theorem B9772883 : Blo 1140634 9772883 := bstep (se 1 (by rfl) ⟨7329662, by rfl⟩ : syracuseStep 9772883 = 14659325) B14659325
theorem B5775623 : Blo 1140634 5775623 := bstep (se 1 (by rfl) ⟨4331717, by rfl⟩ : syracuseStep 5775623 = 8663435) B8663435
theorem B1287679 : Blo 1140634 1287679 := bstep (se 1 (by rfl) ⟨965759, by rfl⟩ : syracuseStep 1287679 = 1931519) B1931519
theorem B4335727 : Blo 1140634 4335727 := bstep (se 1 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 4335727 = 6503591) B6503591
theorem B9251243 : Blo 1140634 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B18754267 : Blo 1140634 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B4336487 : Blo 1140634 4336487 := bstep (se 1 (by rfl) ⟨3252365, by rfl⟩ : syracuseStep 4336487 = 6504731) B6504731
theorem B1715303 : Blo 1140634 1715303 := bstep (se 1 (by rfl) ⟨1286477, by rfl⟩ : syracuseStep 1715303 = 2572955) B2572955
theorem B1715483 : Blo 1140634 1715483 := bstep (se 1 (by rfl) ⟨1286612, by rfl⟩ : syracuseStep 1715483 = 2573225) B2573225
theorem B14626109 : Blo 1140634 14626109 := bstep (se 3 (by rfl) ⟨2742395, by rfl⟩ : syracuseStep 14626109 = 5484791) B5484791
theorem B3255623 : Blo 1140634 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B2567807 : Blo 1140634 2567807 := bstep (se 1 (by rfl) ⟨1925855, by rfl⟩ : syracuseStep 2567807 = 3851711) B3851711
theorem B2470063 : Blo 1140634 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B1716527 : Blo 1140634 1716527 := bstep (se 1 (by rfl) ⟨1287395, by rfl⟩ : syracuseStep 1716527 = 2574791) B2574791
theorem B74003159 : Blo 1140634 74003159 := bstep (se 1 (by rfl) ⟨55502369, by rfl⟩ : syracuseStep 74003159 = 111004739) B111004739
theorem B2569031 : Blo 1140634 2569031 := bstep (se 1 (by rfl) ⟨1926773, by rfl⟩ : syracuseStep 2569031 = 3853547) B3853547
theorem B8664407 : Blo 1140634 8664407 := bstep (se 1 (by rfl) ⟨6498305, by rfl⟩ : syracuseStep 8664407 = 12996611) B12996611
theorem B2570075 : Blo 1140634 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B5486561 : Blo 1140634 5486561 := bstep (se 2 (by rfl) ⟨2057460, by rfl⟩ : syracuseStep 5486561 = 4114921) B4114921
theorem B9746639 : Blo 1140634 9746639 := bstep (se 1 (by rfl) ⟨7309979, by rfl⟩ : syracuseStep 9746639 = 14619959) B14619959
theorem B2439659 : Blo 1140634 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B12336457 : Blo 1140634 12336457 := bstep (se 2 (by rfl) ⟨4626171, by rfl⟩ : syracuseStep 12336457 = 9252343) B9252343
theorem B2571803 : Blo 1140634 2571803 := bstep (se 1 (by rfl) ⟨1928852, by rfl⟩ : syracuseStep 2571803 = 3857705) B3857705
theorem B2571947 : Blo 1140634 2571947 := bstep (se 1 (by rfl) ⟨1928960, by rfl⟩ : syracuseStep 2571947 = 3857921) B3857921
theorem B5783399 : Blo 1140634 5783399 := bstep (se 1 (by rfl) ⟨4337549, by rfl⟩ : syracuseStep 5783399 = 8675099) B8675099
theorem B4341833 : Blo 1140634 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B43893089 : Blo 1140634 43893089 := bstep (se 2 (by rfl) ⟨16459908, by rfl⟩ : syracuseStep 43893089 = 32919817) B32919817
theorem B2573063 : Blo 1140634 2573063 := bstep (se 1 (by rfl) ⟨1929797, by rfl⟩ : syracuseStep 2573063 = 3859595) B3859595
theorem B17580959 : Blo 1140634 17580959 := bstep (se 1 (by rfl) ⟨13185719, by rfl⟩ : syracuseStep 17580959 = 26371439) B26371439
theorem B13190525 : Blo 1140634 13190525 := bstep (se 3 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 13190525 = 4946447) B4946447
theorem B2573801 : Blo 1140634 2573801 := bstep (se 2 (by rfl) ⟨965175, by rfl⟩ : syracuseStep 2573801 = 1930351) B1930351
theorem B8669267 : Blo 1140634 8669267 := bstep (se 1 (by rfl) ⟨6501950, by rfl⟩ : syracuseStep 8669267 = 13003901) B13003901
theorem B6178913 : Blo 1140634 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B2443375 : Blo 1140634 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B225691829 : Blo 1140634 225691829 := bstep (se 5 (by rfl) ⟨10579304, by rfl⟩ : syracuseStep 225691829 = 21158609) B21158609
theorem B4181177 : Blo 1140634 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B6180425 : Blo 1140634 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B160747345 : Blo 1140634 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B9752723 : Blo 1140634 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B3854519 : Blo 1140634 3854519 := bstep (se 1 (by rfl) ⟨2890889, by rfl⟩ : syracuseStep 3854519 = 5781779) B5781779
theorem B80270351 : Blo 1140634 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B329766005 : Blo 1140634 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B3856031 : Blo 1140634 3856031 := bstep (se 1 (by rfl) ⟨2892023, by rfl⟩ : syracuseStep 3856031 = 5784047) B5784047
theorem B5789879 : Blo 1140634 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B3857435 : Blo 1140634 3857435 := bstep (se 1 (by rfl) ⟨2893076, by rfl⟩ : syracuseStep 3857435 = 5786153) B5786153
theorem B3660833 : Blo 1140634 3660833 := bstep (se 2 (by rfl) ⟨1372812, by rfl⟩ : syracuseStep 3660833 = 2745625) B2745625
theorem B79125659 : Blo 1140634 79125659 := bstep (se 1 (by rfl) ⟨59344244, by rfl⟩ : syracuseStep 79125659 = 118688489) B118688489
theorem B3859271 : Blo 1140634 3859271 := bstep (se 1 (by rfl) ⟨2894453, by rfl⟩ : syracuseStep 3859271 = 5788907) B5788907
theorem B3859487 : Blo 1140634 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B3302653 : Blo 1140634 3302653 := bstep (se 3 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 3302653 = 1238495) B1238495
theorem B1140827 : Blo 1140634 1140827 := bstep (se 1 (by rfl) ⟨855620, by rfl⟩ : syracuseStep 1140827 = 1711241) B1711241
theorem B1141055 : Blo 1140634 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B1141499 : Blo 1140634 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B1141503 : Blo 1140634 1141503 := bstep (se 1 (by rfl) ⟨856127, by rfl⟩ : syracuseStep 1141503 = 1712255) B1712255
theorem B1141567 : Blo 1140634 1141567 := bstep (se 1 (by rfl) ⟨856175, by rfl⟩ : syracuseStep 1141567 = 1712351) B1712351
theorem B1141887 : Blo 1140634 1141887 := bstep (se 1 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 1141887 = 1712831) B1712831
theorem B1141999 : Blo 1140634 1141999 := bstep (se 1 (by rfl) ⟨856499, by rfl⟩ : syracuseStep 1141999 = 1712999) B1712999
theorem B1142271 : Blo 1140634 1142271 := bstep (se 1 (by rfl) ⟨856703, by rfl⟩ : syracuseStep 1142271 = 1713407) B1713407
theorem B1928927 : Blo 1140634 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B1142503 : Blo 1140634 1142503 := bstep (se 1 (by rfl) ⟨856877, by rfl⟩ : syracuseStep 1142503 = 1713755) B1713755
theorem B3862511 : Blo 1140634 3862511 := bstep (se 1 (by rfl) ⟨2896883, by rfl⟩ : syracuseStep 3862511 = 5793767) B5793767
theorem B1142975 : Blo 1140634 1142975 := bstep (se 1 (by rfl) ⟨857231, by rfl⟩ : syracuseStep 1142975 = 1714463) B1714463
theorem B1143007 : Blo 1140634 1143007 := bstep (se 1 (by rfl) ⟨857255, by rfl⟩ : syracuseStep 1143007 = 1714511) B1714511
theorem B1143271 : Blo 1140634 1143271 := bstep (se 1 (by rfl) ⟨857453, by rfl⟩ : syracuseStep 1143271 = 1714907) B1714907
theorem B1143407 : Blo 1140634 1143407 := bstep (se 1 (by rfl) ⟨857555, by rfl⟩ : syracuseStep 1143407 = 1715111) B1715111
theorem B1143423 : Blo 1140634 1143423 := bstep (se 1 (by rfl) ⟨857567, by rfl⟩ : syracuseStep 1143423 = 1715135) B1715135
theorem B24442033 : Blo 1140634 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B1144031 : Blo 1140634 1144031 := bstep (se 1 (by rfl) ⟨858023, by rfl⟩ : syracuseStep 1144031 = 1716047) B1716047
theorem B1144063 : Blo 1140634 1144063 := bstep (se 1 (by rfl) ⟨858047, by rfl⟩ : syracuseStep 1144063 = 1716095) B1716095
theorem B1930655 : Blo 1140634 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B1144223 : Blo 1140634 1144223 := bstep (se 1 (by rfl) ⟨858167, by rfl⟩ : syracuseStep 1144223 = 1716335) B1716335
theorem B1144271 : Blo 1140634 1144271 := bstep (se 1 (by rfl) ⟨858203, by rfl⟩ : syracuseStep 1144271 = 1716407) B1716407
theorem B29262059 : Blo 1140634 29262059 := bstep (se 1 (by rfl) ⟨21946544, by rfl⟩ : syracuseStep 29262059 = 43893089) B43893089
theorem B1508287 : Blo 1140634 1508287 := bstep (se 1 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 1508287 = 2262431) B2262431
theorem B6031277 : Blo 1140634 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B1444007 : Blo 1140634 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B1444807 : Blo 1140634 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B53513567 : Blo 1140634 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B219844003 : Blo 1140634 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B25005689 : Blo 1140634 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B1446655 : Blo 1140634 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B6167495 : Blo 1140634 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B2890991 : Blo 1140634 2890991 := bstep (se 1 (by rfl) ⟨2168243, by rfl⟩ : syracuseStep 2890991 = 4336487) B4336487
theorem B2170415 : Blo 1140634 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B1711871 : Blo 1140634 1711871 := bstep (se 1 (by rfl) ⟨1283903, by rfl⟩ : syracuseStep 1711871 = 2567807) B2567807
theorem B1285951 : Blo 1140634 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B1712009 : Blo 1140634 1712009 := bstep (se 2 (by rfl) ⟨642003, by rfl⟩ : syracuseStep 1712009 = 1284007) B1284007
theorem B11149805 : Blo 1140634 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B1712687 : Blo 1140634 1712687 := bstep (se 1 (by rfl) ⟨1284515, by rfl⟩ : syracuseStep 1712687 = 2569031) B2569031
theorem B2892449 : Blo 1140634 2892449 := bstep (se 2 (by rfl) ⟨1084668, by rfl⟩ : syracuseStep 2892449 = 2169337) B2169337
theorem B5776271 : Blo 1140634 5776271 := bstep (se 1 (by rfl) ⟨4332203, by rfl⟩ : syracuseStep 5776271 = 8664407) B8664407
theorem B1287103 : Blo 1140634 1287103 := bstep (se 1 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 1287103 = 1930655) B1930655
theorem B1713383 : Blo 1140634 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B6497759 : Blo 1140634 6497759 := bstep (se 1 (by rfl) ⟨4873319, by rfl⟩ : syracuseStep 6497759 = 9746639) B9746639
theorem B1713833 : Blo 1140634 1713833 := bstep (se 2 (by rfl) ⟨642687, by rfl⟩ : syracuseStep 1713833 = 1285375) B1285375
theorem B857319173 : Blo 1140634 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B1714217 : Blo 1140634 1714217 := bstep (se 2 (by rfl) ⟨642831, by rfl⟩ : syracuseStep 1714217 = 1285663) B1285663
theorem B1714535 : Blo 1140634 1714535 := bstep (se 1 (by rfl) ⟨1285901, by rfl⟩ : syracuseStep 1714535 = 2571803) B2571803
theorem B2894201 : Blo 1140634 2894201 := bstep (se 2 (by rfl) ⟨1085325, by rfl⟩ : syracuseStep 2894201 = 2170651) B2170651
theorem B1714631 : Blo 1140634 1714631 := bstep (se 1 (by rfl) ⟨1285973, by rfl⟩ : syracuseStep 1714631 = 2571947) B2571947
theorem B2894555 : Blo 1140634 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B1715375 : Blo 1140634 1715375 := bstep (se 1 (by rfl) ⟨1286531, by rfl⟩ : syracuseStep 1715375 = 2573063) B2573063
theorem B8793683 : Blo 1140634 8793683 := bstep (se 1 (by rfl) ⟨6595262, by rfl⟩ : syracuseStep 8793683 = 13190525) B13190525
theorem B1715867 : Blo 1140634 1715867 := bstep (se 1 (by rfl) ⟨1286900, by rfl⟩ : syracuseStep 1715867 = 2573801) B2573801
theorem B5779511 : Blo 1140634 5779511 := bstep (se 1 (by rfl) ⟨4334633, by rfl⟩ : syracuseStep 5779511 = 8669267) B8669267
theorem B4403537 : Blo 1140634 4403537 := bstep (se 2 (by rfl) ⟨1651326, by rfl⟩ : syracuseStep 4403537 = 3302653) B3302653
theorem B13906541 : Blo 1140634 13906541 := bstep (se 3 (by rfl) ⟨2607476, by rfl⟩ : syracuseStep 13906541 = 5214953) B5214953
theorem B1716905 : Blo 1140634 1716905 := bstep (se 2 (by rfl) ⟨643839, by rfl⟩ : syracuseStep 1716905 = 1287679) B1287679
theorem B6501815 : Blo 1140634 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B2569679 : Blo 1140634 2569679 := bstep (se 1 (by rfl) ⟨1927259, by rfl⟩ : syracuseStep 2569679 = 3854519) B3854519
theorem B5780969 : Blo 1140634 5780969 := bstep (se 2 (by rfl) ⟨2167863, by rfl⟩ : syracuseStep 5780969 = 4335727) B4335727
theorem B3257833 : Blo 1140634 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B2570687 : Blo 1140634 2570687 := bstep (se 1 (by rfl) ⟨1928015, by rfl⟩ : syracuseStep 2570687 = 3856031) B3856031
theorem B2571623 : Blo 1140634 2571623 := bstep (se 1 (by rfl) ⟨1928717, by rfl⟩ : syracuseStep 2571623 = 3857435) B3857435
theorem B2604395 : Blo 1140634 2604395 := bstep (se 1 (by rfl) ⟨1953296, by rfl⟩ : syracuseStep 2604395 = 3906593) B3906593
theorem B3850415 : Blo 1140634 3850415 := bstep (se 1 (by rfl) ⟨2887811, by rfl⟩ : syracuseStep 3850415 = 5775623) B5775623
theorem B3293417 : Blo 1140634 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B2572847 : Blo 1140634 2572847 := bstep (se 1 (by rfl) ⟨1929635, by rfl⟩ : syracuseStep 2572847 = 3859271) B3859271
theorem B2572991 : Blo 1140634 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B6505757 : Blo 1140634 6505757 := bstep (se 3 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 6505757 = 2439659) B2439659
theorem B32589377 : Blo 1140634 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B9750739 : Blo 1140634 9750739 := bstep (se 1 (by rfl) ⟨7313054, by rfl⟩ : syracuseStep 9750739 = 14626109) B14626109
theorem B2541961 : Blo 1140634 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B2575007 : Blo 1140634 2575007 := bstep (se 1 (by rfl) ⟨1931255, by rfl⟩ : syracuseStep 2575007 = 3862511) B3862511
theorem B49335439 : Blo 1140634 49335439 := bstep (se 1 (by rfl) ⟨37001579, by rfl⟩ : syracuseStep 49335439 = 74003159) B74003159
theorem B3657707 : Blo 1140634 3657707 := bstep (se 1 (by rfl) ⟨2743280, by rfl⟩ : syracuseStep 3657707 = 5486561) B5486561
theorem B3855599 : Blo 1140634 3855599 := bstep (se 1 (by rfl) ⟨2891699, by rfl⟩ : syracuseStep 3855599 = 5783399) B5783399
theorem B11720639 : Blo 1140634 11720639 := bstep (se 1 (by rfl) ⟨8790479, by rfl⟩ : syracuseStep 11720639 = 17580959) B17580959
theorem B4119275 : Blo 1140634 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B150461219 : Blo 1140634 150461219 := bstep (se 1 (by rfl) ⟨112845914, by rfl⟩ : syracuseStep 150461219 = 225691829) B225691829
theorem B10968047 : Blo 1140634 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B4120283 : Blo 1140634 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B2056999 : Blo 1140634 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B3859919 : Blo 1140634 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B1140807 : Blo 1140634 1140807 := bstep (se 1 (by rfl) ⟨855605, by rfl⟩ : syracuseStep 1140807 = 1711211) B1711211
theorem B52750439 : Blo 1140634 52750439 := bstep (se 1 (by rfl) ⟨39562829, by rfl⟩ : syracuseStep 52750439 = 79125659) B79125659
theorem B6515255 : Blo 1140634 6515255 := bstep (se 1 (by rfl) ⟨4886441, by rfl⟩ : syracuseStep 6515255 = 9772883) B9772883
theorem B1143535 : Blo 1140634 1143535 := bstep (se 1 (by rfl) ⟨857651, by rfl⟩ : syracuseStep 1143535 = 1715303) B1715303
theorem B1143655 : Blo 1140634 1143655 := bstep (se 1 (by rfl) ⟨857741, by rfl⟩ : syracuseStep 1143655 = 1715483) B1715483
theorem B9762221 : Blo 1140634 9762221 := bstep (se 3 (by rfl) ⟨1830416, by rfl⟩ : syracuseStep 9762221 = 3660833) B3660833
theorem B1144351 : Blo 1140634 1144351 := bstep (se 1 (by rfl) ⟨858263, by rfl⟩ : syracuseStep 1144351 = 1716527) B1716527
theorem B16448609 : Blo 1140634 16448609 := bstep (se 2 (by rfl) ⟨6168228, by rfl⟩ : syracuseStep 16448609 = 12336457) B12336457
theorem B8782445 : Blo 1140634 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B21726251 : Blo 1140634 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B100307479 : Blo 1140634 100307479 := bstep (se 1 (by rfl) ⟨75230609, by rfl⟩ : syracuseStep 100307479 = 150461219) B150461219
theorem B7312031 : Blo 1140634 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B4331839 : Blo 1140634 4331839 := bstep (se 1 (by rfl) ⟨3248879, by rfl⟩ : syracuseStep 4331839 = 6497759) B6497759
theorem B571546115 : Blo 1140634 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B35166959 : Blo 1140634 35166959 := bstep (se 1 (by rfl) ⟨26375219, by rfl⟩ : syracuseStep 35166959 = 52750439) B52750439
theorem B10984733 : Blo 1140634 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B4334543 : Blo 1140634 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B1713119 : Blo 1140634 1713119 := bstep (se 1 (by rfl) ⟨1284839, by rfl⟩ : syracuseStep 1713119 = 2569679) B2569679
theorem B1713791 : Blo 1140634 1713791 := bstep (se 1 (by rfl) ⟨1285343, by rfl⟩ : syracuseStep 1713791 = 2570687) B2570687
theorem B1714415 : Blo 1140634 1714415 := bstep (se 1 (by rfl) ⟨1285811, by rfl⟩ : syracuseStep 1714415 = 2571623) B2571623
theorem B1714601 : Blo 1140634 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B2566943 : Blo 1140634 2566943 := bstep (se 1 (by rfl) ⟨1925207, by rfl⟩ : syracuseStep 2566943 = 3850415) B3850415
theorem B19508039 : Blo 1140634 19508039 := bstep (se 1 (by rfl) ⟨14631029, by rfl⟩ : syracuseStep 19508039 = 29262059) B29262059
theorem B1715231 : Blo 1140634 1715231 := bstep (se 1 (by rfl) ⟨1286423, by rfl⟩ : syracuseStep 1715231 = 2572847) B2572847
theorem B1715327 : Blo 1140634 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B4337171 : Blo 1140634 4337171 := bstep (se 1 (by rfl) ⟨3252878, by rfl⟩ : syracuseStep 4337171 = 6505757) B6505757
theorem B1716137 : Blo 1140634 1716137 := bstep (se 2 (by rfl) ⟨643551, by rfl⟩ : syracuseStep 1716137 = 1287103) B1287103
theorem B2011049 : Blo 1140634 2011049 := bstep (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) B1508287
theorem B1716671 : Blo 1140634 1716671 := bstep (se 1 (by rfl) ⟨1287503, by rfl⟩ : syracuseStep 1716671 = 2575007) B2575007
theorem B2438471 : Blo 1140634 2438471 := bstep (se 1 (by rfl) ⟨1828853, by rfl⟩ : syracuseStep 2438471 = 3657707) B3657707
theorem B2570399 : Blo 1140634 2570399 := bstep (se 1 (by rfl) ⟨1927799, by rfl⟩ : syracuseStep 2570399 = 3855599) B3855599
theorem B7813759 : Blo 1140634 7813759 := bstep (se 1 (by rfl) ⟨5860319, by rfl⟩ : syracuseStep 7813759 = 11720639) B11720639
theorem B65780585 : Blo 1140634 65780585 := bstep (se 2 (by rfl) ⟨24667719, by rfl⟩ : syracuseStep 65780585 = 49335439) B49335439
theorem B293125337 : Blo 1140634 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B4111663 : Blo 1140634 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B3850685 : Blo 1140634 3850685 := bstep (se 3 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 3850685 = 1444007) B1444007
theorem B3850847 : Blo 1140634 3850847 := bstep (se 1 (by rfl) ⟨2888135, by rfl⟩ : syracuseStep 3850847 = 5776271) B5776271
theorem B2573279 : Blo 1140634 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B4343503 : Blo 1140634 4343503 := bstep (se 1 (by rfl) ⟨3257627, by rfl⟩ : syracuseStep 4343503 = 6515255) B6515255
theorem B4343777 : Blo 1140634 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B3853007 : Blo 1140634 3853007 := bstep (se 1 (by rfl) ⟨2889755, by rfl⟩ : syracuseStep 3853007 = 5779511) B5779511
theorem B2935691 : Blo 1140634 2935691 := bstep (se 1 (by rfl) ⟨2201768, by rfl⟩ : syracuseStep 2935691 = 4403537) B4403537
theorem B6508147 : Blo 1140634 6508147 := bstep (se 1 (by rfl) ⟨4881110, by rfl⟩ : syracuseStep 6508147 = 9762221) B9762221
theorem B3853979 : Blo 1140634 3853979 := bstep (se 1 (by rfl) ⟨2890484, by rfl⟩ : syracuseStep 3853979 = 5780969) B5780969
theorem B5787773 : Blo 1140634 5787773 := bstep (se 3 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 5787773 = 2170415) B2170415
theorem B10965739 : Blo 1140634 10965739 := bstep (se 1 (by rfl) ⟨8224304, by rfl⟩ : syracuseStep 10965739 = 16448609) B16448609
theorem B2742665 : Blo 1140634 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B4020851 : Blo 1140634 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B13557125 : Blo 1140634 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B35675711 : Blo 1140634 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B16670459 : Blo 1140634 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B13000985 : Blo 1140634 13000985 := bstep (se 2 (by rfl) ⟨4875369, by rfl⟩ : syracuseStep 13000985 = 9750739) B9750739
theorem B1926409 : Blo 1140634 1926409 := bstep (se 2 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 1926409 = 1444807) B1444807
theorem B1927327 : Blo 1140634 1927327 := bstep (se 1 (by rfl) ⟨1445495, by rfl⟩ : syracuseStep 1927327 = 2890991) B2890991
theorem B2746855 : Blo 1140634 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B1141247 : Blo 1140634 1141247 := bstep (se 1 (by rfl) ⟨855935, by rfl⟩ : syracuseStep 1141247 = 1711871) B1711871
theorem B1141339 : Blo 1140634 1141339 := bstep (se 1 (by rfl) ⟨856004, by rfl⟩ : syracuseStep 1141339 = 1712009) B1712009
theorem B7433203 : Blo 1140634 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B1141791 : Blo 1140634 1141791 := bstep (se 1 (by rfl) ⟨856343, by rfl⟩ : syracuseStep 1141791 = 1712687) B1712687
theorem B1928299 : Blo 1140634 1928299 := bstep (se 1 (by rfl) ⟨1446224, by rfl⟩ : syracuseStep 1928299 = 2892449) B2892449
theorem B1142255 : Blo 1140634 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B1928873 : Blo 1140634 1928873 := bstep (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) B1446655
theorem B1142555 : Blo 1140634 1142555 := bstep (se 1 (by rfl) ⟨856916, by rfl⟩ : syracuseStep 1142555 = 1713833) B1713833
theorem B1142811 : Blo 1140634 1142811 := bstep (se 1 (by rfl) ⟨857108, by rfl⟩ : syracuseStep 1142811 = 1714217) B1714217
theorem B1143023 : Blo 1140634 1143023 := bstep (se 1 (by rfl) ⟨857267, by rfl⟩ : syracuseStep 1143023 = 1714535) B1714535
theorem B1929467 : Blo 1140634 1929467 := bstep (se 1 (by rfl) ⟨1447100, by rfl⟩ : syracuseStep 1929467 = 2894201) B2894201
theorem B1143087 : Blo 1140634 1143087 := bstep (se 1 (by rfl) ⟨857315, by rfl⟩ : syracuseStep 1143087 = 1714631) B1714631
theorem B1929703 : Blo 1140634 1929703 := bstep (se 1 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 1929703 = 2894555) B2894555
theorem B1143583 : Blo 1140634 1143583 := bstep (se 1 (by rfl) ⟨857687, by rfl⟩ : syracuseStep 1143583 = 1715375) B1715375
theorem B5862455 : Blo 1140634 5862455 := bstep (se 1 (by rfl) ⟨4396841, by rfl⟩ : syracuseStep 5862455 = 8793683) B8793683
theorem B1143911 : Blo 1140634 1143911 := bstep (se 1 (by rfl) ⟨857933, by rfl⟩ : syracuseStep 1143911 = 1715867) B1715867
theorem B9271027 : Blo 1140634 9271027 := bstep (se 1 (by rfl) ⟨6953270, by rfl⟩ : syracuseStep 9271027 = 13906541) B13906541
theorem B1144603 : Blo 1140634 1144603 := bstep (se 1 (by rfl) ⟨858452, by rfl⟩ : syracuseStep 1144603 = 1716905) B1716905
theorem B1736263 : Blo 1140634 1736263 := bstep (se 1 (by rfl) ⟨1302197, by rfl⟩ : syracuseStep 1736263 = 2604395) B2604395
theorem B14484167 : Blo 1140634 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B14649893 : Blo 1140634 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B381030743 : Blo 1140634 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B2889695 : Blo 1140634 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B14620985 : Blo 1140634 14620985 := bstep (se 2 (by rfl) ⟨5482869, by rfl⟩ : syracuseStep 14620985 = 10965739) B10965739
theorem B7313773 : Blo 1140634 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B10722269 : Blo 1140634 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B1711295 : Blo 1140634 1711295 := bstep (se 1 (by rfl) ⟨1283471, by rfl⟩ : syracuseStep 1711295 = 2566943) B2566943
theorem B12361369 : Blo 1140634 12361369 := bstep (se 2 (by rfl) ⟨4635513, by rfl⟩ : syracuseStep 12361369 = 9271027) B9271027
theorem B2891447 : Blo 1140634 2891447 := bstep (se 1 (by rfl) ⟨2168585, by rfl⟩ : syracuseStep 2891447 = 4337171) B4337171
theorem B1285915 : Blo 1140634 1285915 := bstep (se 1 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 1285915 = 1928873) B1928873
theorem B1286311 : Blo 1140634 1286311 := bstep (se 1 (by rfl) ⟨964733, by rfl⟩ : syracuseStep 1286311 = 1929467) B1929467
theorem B5775785 : Blo 1140634 5775785 := bstep (se 2 (by rfl) ⟨2165919, by rfl⟩ : syracuseStep 5775785 = 4331839) B4331839
theorem B3908303 : Blo 1140634 3908303 := bstep (se 1 (by rfl) ⟨2931227, by rfl⟩ : syracuseStep 3908303 = 5862455) B5862455
theorem B1713599 : Blo 1140634 1713599 := bstep (se 1 (by rfl) ⟨1285199, by rfl⟩ : syracuseStep 1713599 = 2570399) B2570399
theorem B5482217 : Blo 1140634 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B43853723 : Blo 1140634 43853723 := bstep (se 1 (by rfl) ⟨32890292, by rfl⟩ : syracuseStep 43853723 = 65780585) B65780585
theorem B2567123 : Blo 1140634 2567123 := bstep (se 1 (by rfl) ⟨1925342, by rfl⟩ : syracuseStep 2567123 = 3850685) B3850685
theorem B2567231 : Blo 1140634 2567231 := bstep (se 1 (by rfl) ⟨1925423, by rfl⟩ : syracuseStep 2567231 = 3850847) B3850847
theorem B1715519 : Blo 1140634 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B2895851 : Blo 1140634 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B2568545 : Blo 1140634 2568545 := bstep (se 2 (by rfl) ⟨963204, by rfl⟩ : syracuseStep 2568545 = 1926409) B1926409
theorem B2568671 : Blo 1140634 2568671 := bstep (se 1 (by rfl) ⟨1926503, by rfl⟩ : syracuseStep 2568671 = 3853007) B3853007
theorem B2569319 : Blo 1140634 2569319 := bstep (se 1 (by rfl) ⟨1926989, by rfl⟩ : syracuseStep 2569319 = 3853979) B3853979
theorem B2569769 : Blo 1140634 2569769 := bstep (se 2 (by rfl) ⟨963663, by rfl⟩ : syracuseStep 2569769 = 1927327) B1927327
theorem B6502589 : Blo 1140634 6502589 := bstep (se 3 (by rfl) ⟨1219235, by rfl⟩ : syracuseStep 6502589 = 2438471) B2438471
theorem B9910937 : Blo 1140634 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B2571065 : Blo 1140634 2571065 := bstep (se 2 (by rfl) ⟨964149, by rfl⟩ : syracuseStep 2571065 = 1928299) B1928299
theorem B23444639 : Blo 1140634 23444639 := bstep (se 1 (by rfl) ⟨17583479, by rfl⟩ : syracuseStep 23444639 = 35166959) B35166959
theorem B7323155 : Blo 1140634 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B8667323 : Blo 1140634 8667323 := bstep (se 1 (by rfl) ⟨6500492, by rfl⟩ : syracuseStep 8667323 = 13000985) B13000985
theorem B2572937 : Blo 1140634 2572937 := bstep (se 2 (by rfl) ⟨964851, by rfl⟩ : syracuseStep 2572937 = 1929703) B1929703
theorem B133743305 : Blo 1140634 133743305 := bstep (se 2 (by rfl) ⟨50153739, by rfl⟩ : syracuseStep 133743305 = 100307479) B100307479
theorem B21451189 : Blo 1140634 21451189 := bstep (se 5 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 21451189 = 2011049) B2011049
theorem B44454557 : Blo 1140634 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B2315017 : Blo 1140634 2315017 := bstep (se 2 (by rfl) ⟨868131, by rfl⟩ : syracuseStep 2315017 = 1736263) B1736263
theorem B195416891 : Blo 1140634 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B23419853 : Blo 1140634 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B1957127 : Blo 1140634 1957127 := bstep (se 1 (by rfl) ⟨1467845, by rfl⟩ : syracuseStep 1957127 = 2935691) B2935691
theorem B5791337 : Blo 1140634 5791337 := bstep (se 2 (by rfl) ⟨2171751, by rfl⟩ : syracuseStep 5791337 = 4343503) B4343503
theorem B3858515 : Blo 1140634 3858515 := bstep (se 1 (by rfl) ⟨2893886, by rfl⟩ : syracuseStep 3858515 = 5787773) B5787773
theorem B4874687 : Blo 1140634 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B8677529 : Blo 1140634 8677529 := bstep (se 2 (by rfl) ⟨3254073, by rfl⟩ : syracuseStep 8677529 = 6508147) B6508147
theorem B9038083 : Blo 1140634 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B23783807 : Blo 1140634 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B1142079 : Blo 1140634 1142079 := bstep (se 1 (by rfl) ⟨856559, by rfl⟩ : syracuseStep 1142079 = 1713119) B1713119
theorem B1142527 : Blo 1140634 1142527 := bstep (se 1 (by rfl) ⟨856895, by rfl⟩ : syracuseStep 1142527 = 1713791) B1713791
theorem B1142943 : Blo 1140634 1142943 := bstep (se 1 (by rfl) ⟨857207, by rfl⟩ : syracuseStep 1142943 = 1714415) B1714415
theorem B1143067 : Blo 1140634 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B13005359 : Blo 1140634 13005359 := bstep (se 1 (by rfl) ⟨9754019, by rfl⟩ : syracuseStep 13005359 = 19508039) B19508039
theorem B1143487 : Blo 1140634 1143487 := bstep (se 1 (by rfl) ⟨857615, by rfl⟩ : syracuseStep 1143487 = 1715231) B1715231
theorem B1143551 : Blo 1140634 1143551 := bstep (se 1 (by rfl) ⟨857663, by rfl⟩ : syracuseStep 1143551 = 1715327) B1715327
theorem B1144091 : Blo 1140634 1144091 := bstep (se 1 (by rfl) ⟨858068, by rfl⟩ : syracuseStep 1144091 = 1716137) B1716137
theorem B1144447 : Blo 1140634 1144447 := bstep (se 1 (by rfl) ⟨858335, by rfl⟩ : syracuseStep 1144447 = 1716671) B1716671
theorem B10418345 : Blo 1140634 10418345 := bstep (se 2 (by rfl) ⟨3906879, by rfl⟩ : syracuseStep 10418345 = 7813759) B7813759
theorem B89162203 : Blo 1140634 89162203 := bstep (se 1 (by rfl) ⟨66871652, by rfl⟩ : syracuseStep 89162203 = 133743305) B133743305
theorem B9766595 : Blo 1140634 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B254020495 : Blo 1140634 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B7148179 : Blo 1140634 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B3249791 : Blo 1140634 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B3086689 : Blo 1140634 3086689 := bstep (se 2 (by rfl) ⟨1157508, by rfl⟩ : syracuseStep 3086689 = 2315017) B2315017
theorem B29235815 : Blo 1140634 29235815 := bstep (se 1 (by rfl) ⟨21926861, by rfl⟩ : syracuseStep 29235815 = 43853723) B43853723
theorem B1711415 : Blo 1140634 1711415 := bstep (se 1 (by rfl) ⟨1283561, by rfl⟩ : syracuseStep 1711415 = 2567123) B2567123
theorem B1711487 : Blo 1140634 1711487 := bstep (se 1 (by rfl) ⟨1283615, by rfl⟩ : syracuseStep 1711487 = 2567231) B2567231
theorem B1712363 : Blo 1140634 1712363 := bstep (se 1 (by rfl) ⟨1284272, by rfl⟩ : syracuseStep 1712363 = 2568545) B2568545
theorem B1712447 : Blo 1140634 1712447 := bstep (se 1 (by rfl) ⟨1284335, by rfl⟩ : syracuseStep 1712447 = 2568671) B2568671
theorem B5219005 : Blo 1140634 5219005 := bstep (se 3 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 5219005 = 1957127) B1957127
theorem B1712879 : Blo 1140634 1712879 := bstep (se 1 (by rfl) ⟨1284659, by rfl⟩ : syracuseStep 1712879 = 2569319) B2569319
theorem B1713179 : Blo 1140634 1713179 := bstep (se 1 (by rfl) ⟨1284884, by rfl⟩ : syracuseStep 1713179 = 2569769) B2569769
theorem B4335059 : Blo 1140634 4335059 := bstep (se 1 (by rfl) ⟨3251294, by rfl⟩ : syracuseStep 4335059 = 6502589) B6502589
theorem B1714043 : Blo 1140634 1714043 := bstep (se 1 (by rfl) ⟨1285532, by rfl⟩ : syracuseStep 1714043 = 2571065) B2571065
theorem B1714553 : Blo 1140634 1714553 := bstep (se 2 (by rfl) ⟨642957, by rfl⟩ : syracuseStep 1714553 = 1285915) B1285915
theorem B5778215 : Blo 1140634 5778215 := bstep (se 1 (by rfl) ⟨4333661, by rfl⟩ : syracuseStep 5778215 = 8667323) B8667323
theorem B1715081 : Blo 1140634 1715081 := bstep (se 2 (by rfl) ⟨643155, by rfl⟩ : syracuseStep 1715081 = 1286311) B1286311
theorem B1715291 : Blo 1140634 1715291 := bstep (se 1 (by rfl) ⟨1286468, by rfl⟩ : syracuseStep 1715291 = 2572937) B2572937
theorem B29636371 : Blo 1140634 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B9747323 : Blo 1140634 9747323 := bstep (se 1 (by rfl) ⟨7310492, by rfl⟩ : syracuseStep 9747323 = 14620985) B14620985
theorem B15613235 : Blo 1140634 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B2572343 : Blo 1140634 2572343 := bstep (se 1 (by rfl) ⟨1929257, by rfl⟩ : syracuseStep 2572343 = 3858515) B3858515
theorem B3850523 : Blo 1140634 3850523 := bstep (se 1 (by rfl) ⟨2887892, by rfl⟩ : syracuseStep 3850523 = 5775785) B5775785
theorem B2605535 : Blo 1140634 2605535 := bstep (se 1 (by rfl) ⟨1954151, by rfl⟩ : syracuseStep 2605535 = 3908303) B3908303
theorem B3654811 : Blo 1140634 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B5785019 : Blo 1140634 5785019 := bstep (se 1 (by rfl) ⟨4338764, by rfl⟩ : syracuseStep 5785019 = 8677529) B8677529
theorem B26429165 : Blo 1140634 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B8670239 : Blo 1140634 8670239 := bstep (se 1 (by rfl) ⟨6502679, by rfl⟩ : syracuseStep 8670239 = 13005359) B13005359
theorem B9751697 : Blo 1140634 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B9656111 : Blo 1140634 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B12050777 : Blo 1140634 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B130277927 : Blo 1140634 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B1926463 : Blo 1140634 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B1140863 : Blo 1140634 1140863 := bstep (se 1 (by rfl) ⟨855647, by rfl⟩ : syracuseStep 1140863 = 1711295) B1711295
theorem B3860891 : Blo 1140634 3860891 := bstep (se 1 (by rfl) ⟨2895668, by rfl⟩ : syracuseStep 3860891 = 5791337) B5791337
theorem B1927631 : Blo 1140634 1927631 := bstep (se 1 (by rfl) ⟨1445723, by rfl⟩ : syracuseStep 1927631 = 2891447) B2891447
theorem B28601585 : Blo 1140634 28601585 := bstep (se 2 (by rfl) ⟨10725594, by rfl⟩ : syracuseStep 28601585 = 21451189) B21451189
theorem B1142399 : Blo 1140634 1142399 := bstep (se 1 (by rfl) ⟨856799, by rfl⟩ : syracuseStep 1142399 = 1713599) B1713599
theorem B15855871 : Blo 1140634 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B1143679 : Blo 1140634 1143679 := bstep (se 1 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 1143679 = 1715519) B1715519
theorem B1930567 : Blo 1140634 1930567 := bstep (se 1 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 1930567 = 2895851) B2895851
theorem B6945563 : Blo 1140634 6945563 := bstep (se 1 (by rfl) ⟨5209172, by rfl⟩ : syracuseStep 6945563 = 10418345) B10418345
theorem B15629759 : Blo 1140634 15629759 := bstep (se 1 (by rfl) ⟨11722319, by rfl⟩ : syracuseStep 15629759 = 23444639) B23444639
theorem B16481825 : Blo 1140634 16481825 := bstep (se 2 (by rfl) ⟨6180684, by rfl⟩ : syracuseStep 16481825 = 12361369) B12361369
theorem B4882103 : Blo 1140634 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B1737023 : Blo 1140634 1737023 := bstep (se 1 (by rfl) ⟨1302767, by rfl⟩ : syracuseStep 1737023 = 2605535) B2605535
theorem B118882937 : Blo 1140634 118882937 := bstep (se 2 (by rfl) ⟨44581101, by rfl⟩ : syracuseStep 118882937 = 89162203) B89162203
theorem B347407805 : Blo 1140634 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B2166527 : Blo 1140634 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B338693993 : Blo 1140634 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B8033851 : Blo 1140634 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B21141161 : Blo 1140634 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B2890039 : Blo 1140634 2890039 := bstep (se 1 (by rfl) ⟨2167529, by rfl⟩ : syracuseStep 2890039 = 4335059) B4335059
theorem B1285087 : Blo 1140634 1285087 := bstep (se 1 (by rfl) ⟨963815, by rfl⟩ : syracuseStep 1285087 = 1927631) B1927631
theorem B4630375 : Blo 1140634 4630375 := bstep (se 1 (by rfl) ⟨3472781, by rfl⟩ : syracuseStep 4630375 = 6945563) B6945563
theorem B6498215 : Blo 1140634 6498215 := bstep (se 1 (by rfl) ⟨4873661, by rfl⟩ : syracuseStep 6498215 = 9747323) B9747323
theorem B10987883 : Blo 1140634 10987883 := bstep (se 1 (by rfl) ⟨8240912, by rfl⟩ : syracuseStep 10987883 = 16481825) B16481825
theorem B3254735 : Blo 1140634 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B1714895 : Blo 1140634 1714895 := bstep (se 1 (by rfl) ⟨1286171, by rfl⟩ : syracuseStep 1714895 = 2572343) B2572343
theorem B2567015 : Blo 1140634 2567015 := bstep (se 1 (by rfl) ⟨1925261, by rfl⟩ : syracuseStep 2567015 = 3850523) B3850523
theorem B6958673 : Blo 1140634 6958673 := bstep (se 2 (by rfl) ⟨2609502, by rfl⟩ : syracuseStep 6958673 = 5219005) B5219005
theorem B2568617 : Blo 1140634 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B5780159 : Blo 1140634 5780159 := bstep (se 1 (by rfl) ⟨4335119, by rfl⟩ : syracuseStep 5780159 = 8670239) B8670239
theorem B6501131 : Blo 1140634 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B6437407 : Blo 1140634 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B2573927 : Blo 1140634 2573927 := bstep (se 1 (by rfl) ⟨1930445, by rfl⟩ : syracuseStep 2573927 = 3860891) B3860891
theorem B2574089 : Blo 1140634 2574089 := bstep (se 2 (by rfl) ⟨965283, by rfl⟩ : syracuseStep 2574089 = 1930567) B1930567
theorem B3852143 : Blo 1140634 3852143 := bstep (se 1 (by rfl) ⟨2889107, by rfl⟩ : syracuseStep 3852143 = 5778215) B5778215
theorem B4115585 : Blo 1140634 4115585 := bstep (se 2 (by rfl) ⟨1543344, by rfl⟩ : syracuseStep 4115585 = 3086689) B3086689
theorem B10408823 : Blo 1140634 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B3856679 : Blo 1140634 3856679 := bstep (se 1 (by rfl) ⟨2892509, by rfl⟩ : syracuseStep 3856679 = 5785019) B5785019
theorem B6511063 : Blo 1140634 6511063 := bstep (se 1 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 6511063 = 9766595) B9766595
theorem B17619443 : Blo 1140634 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B4873081 : Blo 1140634 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B19490543 : Blo 1140634 19490543 := bstep (se 1 (by rfl) ⟨14617907, by rfl⟩ : syracuseStep 19490543 = 29235815) B29235815
theorem B1140943 : Blo 1140634 1140943 := bstep (se 1 (by rfl) ⟨855707, by rfl⟩ : syracuseStep 1140943 = 1711415) B1711415
theorem B1140991 : Blo 1140634 1140991 := bstep (se 1 (by rfl) ⟨855743, by rfl⟩ : syracuseStep 1140991 = 1711487) B1711487
theorem B1141575 : Blo 1140634 1141575 := bstep (se 1 (by rfl) ⟨856181, by rfl⟩ : syracuseStep 1141575 = 1712363) B1712363
theorem B1141631 : Blo 1140634 1141631 := bstep (se 1 (by rfl) ⟨856223, by rfl⟩ : syracuseStep 1141631 = 1712447) B1712447
theorem B1141919 : Blo 1140634 1141919 := bstep (se 1 (by rfl) ⟨856439, by rfl⟩ : syracuseStep 1141919 = 1712879) B1712879
theorem B1142119 : Blo 1140634 1142119 := bstep (se 1 (by rfl) ⟨856589, by rfl⟩ : syracuseStep 1142119 = 1713179) B1713179
theorem B9530905 : Blo 1140634 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B1142695 : Blo 1140634 1142695 := bstep (se 1 (by rfl) ⟨857021, by rfl⟩ : syracuseStep 1142695 = 1714043) B1714043
theorem B1143035 : Blo 1140634 1143035 := bstep (se 1 (by rfl) ⟨857276, by rfl⟩ : syracuseStep 1143035 = 1714553) B1714553
theorem B1143387 : Blo 1140634 1143387 := bstep (se 1 (by rfl) ⟨857540, by rfl⟩ : syracuseStep 1143387 = 1715081) B1715081
theorem B1143527 : Blo 1140634 1143527 := bstep (se 1 (by rfl) ⟨857645, by rfl⟩ : syracuseStep 1143527 = 1715291) B1715291
theorem B19067723 : Blo 1140634 19067723 := bstep (se 1 (by rfl) ⟨14300792, by rfl⟩ : syracuseStep 19067723 = 28601585) B28601585
theorem B39515161 : Blo 1140634 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B10419839 : Blo 1140634 10419839 := bstep (se 1 (by rfl) ⟨7814879, by rfl⟩ : syracuseStep 10419839 = 15629759) B15629759
theorem B231605203 : Blo 1140634 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B14094107 : Blo 1140634 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B4332143 : Blo 1140634 4332143 := bstep (se 1 (by rfl) ⟨3249107, by rfl⟩ : syracuseStep 4332143 = 6498215) B6498215
theorem B2169823 : Blo 1140634 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B1711343 : Blo 1140634 1711343 := bstep (se 1 (by rfl) ⟨1283507, by rfl⟩ : syracuseStep 1711343 = 2567015) B2567015
theorem B1712411 : Blo 1140634 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B4334087 : Blo 1140634 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B6497441 : Blo 1140634 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B1713449 : Blo 1140634 1713449 := bstep (se 2 (by rfl) ⟨642543, by rfl⟩ : syracuseStep 1713449 = 1285087) B1285087
theorem B5777405 : Blo 1140634 5777405 := bstep (se 3 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 5777405 = 2166527) B2166527
theorem B4632061 : Blo 1140634 4632061 := bstep (se 3 (by rfl) ⟨868511, by rfl⟩ : syracuseStep 4632061 = 1737023) B1737023
theorem B1715951 : Blo 1140634 1715951 := bstep (se 1 (by rfl) ⟨1286963, by rfl⟩ : syracuseStep 1715951 = 2573927) B2573927
theorem B1716059 : Blo 1140634 1716059 := bstep (se 1 (by rfl) ⟨1287044, by rfl⟩ : syracuseStep 1716059 = 2574089) B2574089
theorem B2568095 : Blo 1140634 2568095 := bstep (se 1 (by rfl) ⟨1926071, by rfl⟩ : syracuseStep 2568095 = 3852143) B3852143
theorem B6173833 : Blo 1140634 6173833 := bstep (se 2 (by rfl) ⟨2315187, by rfl⟩ : syracuseStep 6173833 = 4630375) B4630375
theorem B2571119 : Blo 1140634 2571119 := bstep (se 1 (by rfl) ⟨1928339, by rfl⟩ : syracuseStep 2571119 = 3856679) B3856679
theorem B11746295 : Blo 1140634 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B12993695 : Blo 1140634 12993695 := bstep (se 1 (by rfl) ⟨9745271, by rfl⟩ : syracuseStep 12993695 = 19490543) B19490543
theorem B7325255 : Blo 1140634 7325255 := bstep (se 1 (by rfl) ⟨5493941, by rfl⟩ : syracuseStep 7325255 = 10987883) B10987883
theorem B4639115 : Blo 1140634 4639115 := bstep (se 1 (by rfl) ⟨3479336, by rfl⟩ : syracuseStep 4639115 = 6958673) B6958673
theorem B3853385 : Blo 1140634 3853385 := bstep (se 2 (by rfl) ⟨1445019, by rfl⟩ : syracuseStep 3853385 = 2890039) B2890039
theorem B3853439 : Blo 1140634 3853439 := bstep (se 1 (by rfl) ⟨2890079, by rfl⟩ : syracuseStep 3853439 = 5780159) B5780159
theorem B317021165 : Blo 1140634 317021165 := bstep (se 3 (by rfl) ⟨59441468, by rfl⟩ : syracuseStep 317021165 = 118882937) B118882937
theorem B2743723 : Blo 1140634 2743723 := bstep (se 1 (by rfl) ⟨2057792, by rfl⟩ : syracuseStep 2743723 = 4115585) B4115585
theorem B225795995 : Blo 1140634 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B6939215 : Blo 1140634 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B12707873 : Blo 1140634 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B52686881 : Blo 1140634 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B1143263 : Blo 1140634 1143263 := bstep (se 1 (by rfl) ⟨857447, by rfl⟩ : syracuseStep 1143263 = 1714895) B1714895
theorem B10711801 : Blo 1140634 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B12711815 : Blo 1140634 12711815 := bstep (se 1 (by rfl) ⟨9533861, by rfl⟩ : syracuseStep 12711815 = 19067723) B19067723
theorem B8681417 : Blo 1140634 8681417 := bstep (se 2 (by rfl) ⟨3255531, by rfl⟩ : syracuseStep 8681417 = 6511063) B6511063
theorem B8583209 : Blo 1140634 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B6946559 : Blo 1140634 6946559 := bstep (se 1 (by rfl) ⟨5209919, by rfl⟩ : syracuseStep 6946559 = 10419839) B10419839
theorem B4883503 : Blo 1140634 4883503 := bstep (se 1 (by rfl) ⟨3662627, by rfl⟩ : syracuseStep 4883503 = 7325255) B7325255
theorem B308806937 : Blo 1140634 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B2888095 : Blo 1140634 2888095 := bstep (se 1 (by rfl) ⟨2166071, by rfl⟩ : syracuseStep 2888095 = 4332143) B4332143
theorem B2889391 : Blo 1140634 2889391 := bstep (se 1 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 2889391 = 4334087) B4334087
theorem B4626143 : Blo 1140634 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B4331627 : Blo 1140634 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B8231777 : Blo 1140634 8231777 := bstep (se 2 (by rfl) ⟨3086916, by rfl⟩ : syracuseStep 8231777 = 6173833) B6173833
theorem B1712063 : Blo 1140634 1712063 := bstep (se 1 (by rfl) ⟨1284047, by rfl⟩ : syracuseStep 1712063 = 2568095) B2568095
theorem B2893097 : Blo 1140634 2893097 := bstep (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) B2169823
theorem B1714079 : Blo 1140634 1714079 := bstep (se 1 (by rfl) ⟨1285559, by rfl⟩ : syracuseStep 1714079 = 2571119) B2571119
theorem B4631039 : Blo 1140634 4631039 := bstep (se 1 (by rfl) ⟨3473279, by rfl⟩ : syracuseStep 4631039 = 6946559) B6946559
theorem B8662463 : Blo 1140634 8662463 := bstep (se 1 (by rfl) ⟨6496847, by rfl⟩ : syracuseStep 8662463 = 12993695) B12993695
theorem B3092743 : Blo 1140634 3092743 := bstep (se 1 (by rfl) ⟨2319557, by rfl⟩ : syracuseStep 3092743 = 4639115) B4639115
theorem B2568923 : Blo 1140634 2568923 := bstep (se 1 (by rfl) ⟨1926692, by rfl⟩ : syracuseStep 2568923 = 3853385) B3853385
theorem B2568959 : Blo 1140634 2568959 := bstep (se 1 (by rfl) ⟨1926719, by rfl⟩ : syracuseStep 2568959 = 3853439) B3853439
theorem B6176081 : Blo 1140634 6176081 := bstep (se 2 (by rfl) ⟨2316030, by rfl⟩ : syracuseStep 6176081 = 4632061) B4632061
theorem B3851603 : Blo 1140634 3851603 := bstep (se 1 (by rfl) ⟨2888702, by rfl⟩ : syracuseStep 3851603 = 5777405) B5777405
theorem B8471915 : Blo 1140634 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B8474543 : Blo 1140634 8474543 := bstep (se 1 (by rfl) ⟨6355907, by rfl⟩ : syracuseStep 8474543 = 12711815) B12711815
theorem B5787611 : Blo 1140634 5787611 := bstep (se 1 (by rfl) ⟨4340708, by rfl⟩ : syracuseStep 5787611 = 8681417) B8681417
theorem B5722139 : Blo 1140634 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B3658297 : Blo 1140634 3658297 := bstep (se 2 (by rfl) ⟨1371861, by rfl⟩ : syracuseStep 3658297 = 2743723) B2743723
theorem B9396071 : Blo 1140634 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B211347443 : Blo 1140634 211347443 := bstep (se 1 (by rfl) ⟨158510582, by rfl⟩ : syracuseStep 211347443 = 317021165) B317021165
theorem B1140895 : Blo 1140634 1140895 := bstep (se 1 (by rfl) ⟨855671, by rfl⟩ : syracuseStep 1140895 = 1711343) B1711343
theorem B150530663 : Blo 1140634 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B1141607 : Blo 1140634 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B1142299 : Blo 1140634 1142299 := bstep (se 1 (by rfl) ⟨856724, by rfl⟩ : syracuseStep 1142299 = 1713449) B1713449
theorem B14282401 : Blo 1140634 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B1143967 : Blo 1140634 1143967 := bstep (se 1 (by rfl) ⟨857975, by rfl⟩ : syracuseStep 1143967 = 1715951) B1715951
theorem B1144039 : Blo 1140634 1144039 := bstep (se 1 (by rfl) ⟨858029, by rfl⟩ : syracuseStep 1144039 = 1716059) B1716059
theorem B35124587 : Blo 1140634 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B7830863 : Blo 1140634 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B3084095 : Blo 1140634 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B2887751 : Blo 1140634 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B19043201 : Blo 1140634 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B6264047 : Blo 1140634 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B401415101 : Blo 1140634 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B3087359 : Blo 1140634 3087359 := bstep (se 1 (by rfl) ⟨2315519, by rfl⟩ : syracuseStep 3087359 = 4631039) B4631039
theorem B5774975 : Blo 1140634 5774975 := bstep (se 1 (by rfl) ⟨4331231, by rfl⟩ : syracuseStep 5774975 = 8662463) B8662463
theorem B1712615 : Blo 1140634 1712615 := bstep (se 1 (by rfl) ⟨1284461, by rfl⟩ : syracuseStep 1712615 = 2568923) B2568923
theorem B1712639 : Blo 1140634 1712639 := bstep (se 1 (by rfl) ⟨1284479, by rfl⟩ : syracuseStep 1712639 = 2568959) B2568959
theorem B5220575 : Blo 1140634 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B2567735 : Blo 1140634 2567735 := bstep (se 1 (by rfl) ⟨1925801, by rfl⟩ : syracuseStep 2567735 = 3851603) B3851603
theorem B5647943 : Blo 1140634 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B5649695 : Blo 1140634 5649695 := bstep (se 1 (by rfl) ⟨4237271, by rfl⟩ : syracuseStep 5649695 = 8474543) B8474543
theorem B3814759 : Blo 1140634 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B5487851 : Blo 1140634 5487851 := bstep (se 1 (by rfl) ⟨4115888, by rfl⟩ : syracuseStep 5487851 = 8231777) B8231777
theorem B3850793 : Blo 1140634 3850793 := bstep (se 2 (by rfl) ⟨1444047, by rfl⟩ : syracuseStep 3850793 = 2888095) B2888095
theorem B3852521 : Blo 1140634 3852521 := bstep (se 2 (by rfl) ⟨1444695, by rfl⟩ : syracuseStep 3852521 = 2889391) B2889391
theorem B23416391 : Blo 1140634 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B4117387 : Blo 1140634 4117387 := bstep (se 1 (by rfl) ⟨3088040, by rfl⟩ : syracuseStep 4117387 = 6176081) B6176081
theorem B205871291 : Blo 1140634 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B6511337 : Blo 1140634 6511337 := bstep (se 2 (by rfl) ⟨2441751, by rfl⟩ : syracuseStep 6511337 = 4883503) B4883503
theorem B3858407 : Blo 1140634 3858407 := bstep (se 1 (by rfl) ⟨2893805, by rfl⟩ : syracuseStep 3858407 = 5787611) B5787611
theorem B1141375 : Blo 1140634 1141375 := bstep (se 1 (by rfl) ⟨856031, by rfl⟩ : syracuseStep 1141375 = 1712063) B1712063
theorem B4123657 : Blo 1140634 4123657 := bstep (se 2 (by rfl) ⟨1546371, by rfl⟩ : syracuseStep 4123657 = 3092743) B3092743
theorem B4877729 : Blo 1140634 4877729 := bstep (se 2 (by rfl) ⟨1829148, by rfl⟩ : syracuseStep 4877729 = 3658297) B3658297
theorem B1928731 : Blo 1140634 1928731 := bstep (se 1 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 1928731 = 2893097) B2893097
theorem B1142719 : Blo 1140634 1142719 := bstep (se 1 (by rfl) ⟨857039, by rfl⟩ : syracuseStep 1142719 = 1714079) B1714079
theorem B140898295 : Blo 1140634 140898295 := bstep (se 1 (by rfl) ⟨105673721, by rfl⟩ : syracuseStep 140898295 = 211347443) B211347443
theorem B187864393 : Blo 1140634 187864393 := bstep (se 2 (by rfl) ⟨70449147, by rfl⟩ : syracuseStep 187864393 = 140898295) B140898295
theorem B3480383 : Blo 1140634 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B3251819 : Blo 1140634 3251819 := bstep (se 1 (by rfl) ⟨2438864, by rfl⟩ : syracuseStep 3251819 = 4877729) B4877729
theorem B1711823 : Blo 1140634 1711823 := bstep (se 1 (by rfl) ⟨1283867, by rfl⟩ : syracuseStep 1711823 = 2567735) B2567735
theorem B2567195 : Blo 1140634 2567195 := bstep (se 1 (by rfl) ⟨1925396, by rfl⟩ : syracuseStep 2567195 = 3850793) B3850793
theorem B2568347 : Blo 1140634 2568347 := bstep (se 1 (by rfl) ⟨1926260, by rfl⟩ : syracuseStep 2568347 = 3852521) B3852521
theorem B15610927 : Blo 1140634 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B12695467 : Blo 1140634 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B4176031 : Blo 1140634 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B137247527 : Blo 1140634 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B4340891 : Blo 1140634 4340891 := bstep (se 1 (by rfl) ⟨3255668, by rfl⟩ : syracuseStep 4340891 = 6511337) B6511337
theorem B2571641 : Blo 1140634 2571641 := bstep (se 2 (by rfl) ⟨964365, by rfl⟩ : syracuseStep 2571641 = 1928731) B1928731
theorem B3849983 : Blo 1140634 3849983 := bstep (se 1 (by rfl) ⟨2887487, by rfl⟩ : syracuseStep 3849983 = 5774975) B5774975
theorem B2572271 : Blo 1140634 2572271 := bstep (se 1 (by rfl) ⟨1929203, by rfl⟩ : syracuseStep 2572271 = 3858407) B3858407
theorem B5489849 : Blo 1140634 5489849 := bstep (se 2 (by rfl) ⟨2058693, by rfl⟩ : syracuseStep 5489849 = 4117387) B4117387
theorem B3658567 : Blo 1140634 3658567 := bstep (se 1 (by rfl) ⟨2743925, by rfl⟩ : syracuseStep 3658567 = 5487851) B5487851
theorem B2056063 : Blo 1140634 2056063 := bstep (se 1 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 2056063 = 3084095) B3084095
theorem B1925167 : Blo 1140634 1925167 := bstep (se 1 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 1925167 = 2887751) B2887751
theorem B5498209 : Blo 1140634 5498209 := bstep (se 2 (by rfl) ⟨2061828, by rfl⟩ : syracuseStep 5498209 = 4123657) B4123657
theorem B267610067 : Blo 1140634 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B2058239 : Blo 1140634 2058239 := bstep (se 1 (by rfl) ⟨1543679, by rfl⟩ : syracuseStep 2058239 = 3087359) B3087359
theorem B1141743 : Blo 1140634 1141743 := bstep (se 1 (by rfl) ⟨856307, by rfl⟩ : syracuseStep 1141743 = 1712615) B1712615
theorem B1141759 : Blo 1140634 1141759 := bstep (se 1 (by rfl) ⟨856319, by rfl⟩ : syracuseStep 1141759 = 1712639) B1712639
theorem B20345381 : Blo 1140634 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B3765295 : Blo 1140634 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B3766463 : Blo 1140634 3766463 := bstep (se 1 (by rfl) ⟨2824847, by rfl⟩ : syracuseStep 3766463 = 5649695) B5649695
theorem B2167879 : Blo 1140634 2167879 := bstep (se 1 (by rfl) ⟨1625909, by rfl⟩ : syracuseStep 2167879 = 3251819) B3251819
theorem B20814569 : Blo 1140634 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B5020393 : Blo 1140634 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B250485857 : Blo 1140634 250485857 := bstep (se 2 (by rfl) ⟨93932196, by rfl⟩ : syracuseStep 250485857 = 187864393) B187864393
theorem B1711463 : Blo 1140634 1711463 := bstep (se 1 (by rfl) ⟨1283597, by rfl⟩ : syracuseStep 1711463 = 2567195) B2567195
theorem B1712231 : Blo 1140634 1712231 := bstep (se 1 (by rfl) ⟨1284173, by rfl⟩ : syracuseStep 1712231 = 2568347) B2568347
theorem B91498351 : Blo 1140634 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B2893927 : Blo 1140634 2893927 := bstep (se 1 (by rfl) ⟨2170445, by rfl⟩ : syracuseStep 2893927 = 4340891) B4340891
theorem B1714427 : Blo 1140634 1714427 := bstep (se 1 (by rfl) ⟨1285820, by rfl⟩ : syracuseStep 1714427 = 2571641) B2571641
theorem B2566655 : Blo 1140634 2566655 := bstep (se 1 (by rfl) ⟨1924991, by rfl⟩ : syracuseStep 2566655 = 3849983) B3849983
theorem B1714847 : Blo 1140634 1714847 := bstep (se 1 (by rfl) ⟨1286135, by rfl⟩ : syracuseStep 1714847 = 2572271) B2572271
theorem B2566889 : Blo 1140634 2566889 := bstep (se 2 (by rfl) ⟨962583, by rfl⟩ : syracuseStep 2566889 = 1925167) B1925167
theorem B178406711 : Blo 1140634 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B16927289 : Blo 1140634 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B2510975 : Blo 1140634 2510975 := bstep (se 1 (by rfl) ⟨1883231, by rfl⟩ : syracuseStep 2510975 = 3766463) B3766463
theorem B2741417 : Blo 1140634 2741417 := bstep (se 2 (by rfl) ⟨1028031, by rfl⟩ : syracuseStep 2741417 = 2056063) B2056063
theorem B3659899 : Blo 1140634 3659899 := bstep (se 1 (by rfl) ⟨2744924, by rfl⟩ : syracuseStep 3659899 = 5489849) B5489849
theorem B7330945 : Blo 1140634 7330945 := bstep (se 2 (by rfl) ⟨2749104, by rfl⟩ : syracuseStep 7330945 = 5498209) B5498209
theorem B2320255 : Blo 1140634 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B1141215 : Blo 1140634 1141215 := bstep (se 1 (by rfl) ⟨855911, by rfl⟩ : syracuseStep 1141215 = 1711823) B1711823
theorem B4878089 : Blo 1140634 4878089 := bstep (se 2 (by rfl) ⟨1829283, by rfl⟩ : syracuseStep 4878089 = 3658567) B3658567
theorem B1372159 : Blo 1140634 1372159 := bstep (se 1 (by rfl) ⟨1029119, by rfl⟩ : syracuseStep 1372159 = 2058239) B2058239
theorem B5568041 : Blo 1140634 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B13563587 : Blo 1140634 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B121997801 : Blo 1140634 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B14848109 : Blo 1140634 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B166990571 : Blo 1140634 166990571 := bstep (se 1 (by rfl) ⟨125242928, by rfl⟩ : syracuseStep 166990571 = 250485857) B250485857
theorem B2890505 : Blo 1140634 2890505 := bstep (se 2 (by rfl) ⟨1083939, by rfl⟩ : syracuseStep 2890505 = 2167879) B2167879
theorem B1711103 : Blo 1140634 1711103 := bstep (se 1 (by rfl) ⟨1283327, by rfl⟩ : syracuseStep 1711103 = 2566655) B2566655
theorem B1711259 : Blo 1140634 1711259 := bstep (se 1 (by rfl) ⟨1283444, by rfl⟩ : syracuseStep 1711259 = 2566889) B2566889
theorem B3252059 : Blo 1140634 3252059 := bstep (se 1 (by rfl) ⟨2439044, by rfl⟩ : syracuseStep 3252059 = 4878089) B4878089
theorem B6693857 : Blo 1140634 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B9774593 : Blo 1140634 9774593 := bstep (se 2 (by rfl) ⟨3665472, by rfl⟩ : syracuseStep 9774593 = 7330945) B7330945
theorem B7318181 : Blo 1140634 7318181 := bstep (se 4 (by rfl) ⟨686079, by rfl⟩ : syracuseStep 7318181 = 1372159) B1372159
theorem B6695933 : Blo 1140634 6695933 := bstep (se 3 (by rfl) ⟨1255487, by rfl⟩ : syracuseStep 6695933 = 2510975) B2510975
theorem B11284859 : Blo 1140634 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B3093673 : Blo 1140634 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B13876379 : Blo 1140634 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B118937807 : Blo 1140634 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B3858569 : Blo 1140634 3858569 := bstep (se 2 (by rfl) ⟨1446963, by rfl⟩ : syracuseStep 3858569 = 2893927) B2893927
theorem B1827611 : Blo 1140634 1827611 := bstep (se 1 (by rfl) ⟨1370708, by rfl⟩ : syracuseStep 1827611 = 2741417) B2741417
theorem B1140975 : Blo 1140634 1140975 := bstep (se 1 (by rfl) ⟨855731, by rfl⟩ : syracuseStep 1140975 = 1711463) B1711463
theorem B1141487 : Blo 1140634 1141487 := bstep (se 1 (by rfl) ⟨856115, by rfl⟩ : syracuseStep 1141487 = 1712231) B1712231
theorem B1142951 : Blo 1140634 1142951 := bstep (se 1 (by rfl) ⟨857213, by rfl⟩ : syracuseStep 1142951 = 1714427) B1714427
theorem B1143231 : Blo 1140634 1143231 := bstep (se 1 (by rfl) ⟨857423, by rfl⟩ : syracuseStep 1143231 = 1714847) B1714847
theorem B4879865 : Blo 1140634 4879865 := bstep (se 2 (by rfl) ⟨1829949, by rfl⟩ : syracuseStep 4879865 = 3659899) B3659899
theorem B9042391 : Blo 1140634 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B81331867 : Blo 1140634 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B9898739 : Blo 1140634 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B2168039 : Blo 1140634 2168039 := bstep (se 1 (by rfl) ⟨1626029, by rfl⟩ : syracuseStep 2168039 = 3252059) B3252059
theorem B1218407 : Blo 1140634 1218407 := bstep (se 1 (by rfl) ⟨913805, by rfl⟩ : syracuseStep 1218407 = 1827611) B1827611
theorem B4462571 : Blo 1140634 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B3253243 : Blo 1140634 3253243 := bstep (se 1 (by rfl) ⟨2439932, by rfl⟩ : syracuseStep 3253243 = 4879865) B4879865
theorem B9250919 : Blo 1140634 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B111327047 : Blo 1140634 111327047 := bstep (se 1 (by rfl) ⟨83495285, by rfl⟩ : syracuseStep 111327047 = 166990571) B166990571
theorem B2572379 : Blo 1140634 2572379 := bstep (se 1 (by rfl) ⟨1929284, by rfl⟩ : syracuseStep 2572379 = 3858569) B3858569
theorem B7523239 : Blo 1140634 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B79291871 : Blo 1140634 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B1927003 : Blo 1140634 1927003 := bstep (se 1 (by rfl) ⟨1445252, by rfl⟩ : syracuseStep 1927003 = 2890505) B2890505
theorem B1140735 : Blo 1140634 1140735 := bstep (se 1 (by rfl) ⟨855551, by rfl⟩ : syracuseStep 1140735 = 1711103) B1711103
theorem B1140839 : Blo 1140634 1140839 := bstep (se 1 (by rfl) ⟨855629, by rfl⟩ : syracuseStep 1140839 = 1711259) B1711259
theorem B6516395 : Blo 1140634 6516395 := bstep (se 1 (by rfl) ⟨4887296, by rfl⟩ : syracuseStep 6516395 = 9774593) B9774593
theorem B4124897 : Blo 1140634 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B4878787 : Blo 1140634 4878787 := bstep (se 1 (by rfl) ⟨3659090, by rfl⟩ : syracuseStep 4878787 = 7318181) B7318181
theorem B17855821 : Blo 1140634 17855821 := bstep (se 3 (by rfl) ⟨3347966, by rfl⟩ : syracuseStep 17855821 = 6695933) B6695933
theorem B12056521 : Blo 1140634 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B1445359 : Blo 1140634 1445359 := bstep (se 1 (by rfl) ⟨1084019, by rfl⟩ : syracuseStep 1445359 = 2168039) B2168039
theorem B10030985 : Blo 1140634 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B3249085 : Blo 1140634 3249085 := bstep (se 3 (by rfl) ⟨609203, by rfl⟩ : syracuseStep 3249085 = 1218407) B1218407
theorem B11900189 : Blo 1140634 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B52861247 : Blo 1140634 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B6167279 : Blo 1140634 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B95231045 : Blo 1140634 95231045 := bstep (se 4 (by rfl) ⟨8927910, by rfl⟩ : syracuseStep 95231045 = 17855821) B17855821
theorem B1714919 : Blo 1140634 1714919 := bstep (se 1 (by rfl) ⟨1286189, by rfl⟩ : syracuseStep 1714919 = 2572379) B2572379
theorem B4337657 : Blo 1140634 4337657 := bstep (se 2 (by rfl) ⟨1626621, by rfl⟩ : syracuseStep 4337657 = 3253243) B3253243
theorem B6599159 : Blo 1140634 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B108442489 : Blo 1140634 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B2569337 : Blo 1140634 2569337 := bstep (se 2 (by rfl) ⟨963501, by rfl⟩ : syracuseStep 2569337 = 1927003) B1927003
theorem B6505049 : Blo 1140634 6505049 := bstep (se 2 (by rfl) ⟨2439393, by rfl⟩ : syracuseStep 6505049 = 4878787) B4878787
theorem B4344263 : Blo 1140634 4344263 := bstep (se 1 (by rfl) ⟨3258197, by rfl⟩ : syracuseStep 4344263 = 6516395) B6516395
theorem B16075361 : Blo 1140634 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B2749931 : Blo 1140634 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B74218031 : Blo 1140634 74218031 := bstep (se 1 (by rfl) ⟨55663523, by rfl⟩ : syracuseStep 74218031 = 111327047) B111327047
theorem B10716907 : Blo 1140634 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B6687323 : Blo 1140634 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B7933459 : Blo 1140634 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B4332113 : Blo 1140634 4332113 := bstep (se 2 (by rfl) ⟨1624542, by rfl⟩ : syracuseStep 4332113 = 3249085) B3249085
theorem B2891771 : Blo 1140634 2891771 := bstep (se 1 (by rfl) ⟨2168828, by rfl⟩ : syracuseStep 2891771 = 4337657) B4337657
theorem B4399439 : Blo 1140634 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B1712891 : Blo 1140634 1712891 := bstep (se 1 (by rfl) ⟨1284668, by rfl⟩ : syracuseStep 1712891 = 2569337) B2569337
theorem B4336699 : Blo 1140634 4336699 := bstep (se 1 (by rfl) ⟨3252524, by rfl⟩ : syracuseStep 4336699 = 6505049) B6505049
theorem B2896175 : Blo 1140634 2896175 := bstep (se 1 (by rfl) ⟨2172131, by rfl⟩ : syracuseStep 2896175 = 4344263) B4344263
theorem B35240831 : Blo 1140634 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B4111519 : Blo 1140634 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B63487363 : Blo 1140634 63487363 := bstep (se 1 (by rfl) ⟨47615522, by rfl⟩ : syracuseStep 63487363 = 95231045) B95231045
theorem B144589985 : Blo 1140634 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B1927145 : Blo 1140634 1927145 := bstep (se 2 (by rfl) ⟨722679, by rfl⟩ : syracuseStep 1927145 = 1445359) B1445359
theorem B1143279 : Blo 1140634 1143279 := bstep (se 1 (by rfl) ⟨857459, by rfl⟩ : syracuseStep 1143279 = 1714919) B1714919
theorem B1833287 : Blo 1140634 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B49478687 : Blo 1140634 49478687 := bstep (se 1 (by rfl) ⟨37109015, by rfl⟩ : syracuseStep 49478687 = 74218031) B74218031
theorem B4458215 : Blo 1140634 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B14289209 : Blo 1140634 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B46927349 : Blo 1140634 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B2888075 : Blo 1140634 2888075 := bstep (se 1 (by rfl) ⟨2166056, by rfl⟩ : syracuseStep 2888075 = 4332113) B4332113
theorem B4888765 : Blo 1140634 4888765 := bstep (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) B1833287
theorem B1284763 : Blo 1140634 1284763 := bstep (se 1 (by rfl) ⟨963572, by rfl⟩ : syracuseStep 1284763 = 1927145) B1927145
theorem B5482025 : Blo 1140634 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B84649817 : Blo 1140634 84649817 := bstep (se 2 (by rfl) ⟨31743681, by rfl⟩ : syracuseStep 84649817 = 63487363) B63487363
theorem B5782265 : Blo 1140634 5782265 := bstep (se 2 (by rfl) ⟨2168349, by rfl⟩ : syracuseStep 5782265 = 4336699) B4336699
theorem B32985791 : Blo 1140634 32985791 := bstep (se 1 (by rfl) ⟨24739343, by rfl⟩ : syracuseStep 32985791 = 49478687) B49478687
theorem B96393323 : Blo 1140634 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B10577945 : Blo 1140634 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B1927847 : Blo 1140634 1927847 := bstep (se 1 (by rfl) ⟨1445885, by rfl⟩ : syracuseStep 1927847 = 2891771) B2891771
theorem B1141927 : Blo 1140634 1141927 := bstep (se 1 (by rfl) ⟨856445, by rfl⟩ : syracuseStep 1141927 = 1712891) B1712891
theorem B1930783 : Blo 1140634 1930783 := bstep (se 1 (by rfl) ⟨1448087, by rfl⟩ : syracuseStep 1930783 = 2896175) B2896175
theorem B23493887 : Blo 1140634 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B21990527 : Blo 1140634 21990527 := bstep (se 1 (by rfl) ⟨16492895, by rfl⟩ : syracuseStep 21990527 = 32985791) B32985791
theorem B64262215 : Blo 1140634 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B7051963 : Blo 1140634 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B1285231 : Blo 1140634 1285231 := bstep (se 1 (by rfl) ⟨963923, by rfl⟩ : syracuseStep 1285231 = 1927847) B1927847
theorem B1713017 : Blo 1140634 1713017 := bstep (se 2 (by rfl) ⟨642381, by rfl⟩ : syracuseStep 1713017 = 1284763) B1284763
theorem B3654683 : Blo 1140634 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B2574377 : Blo 1140634 2574377 := bstep (se 2 (by rfl) ⟨965391, by rfl⟩ : syracuseStep 2574377 = 1930783) B1930783
theorem B3854843 : Blo 1140634 3854843 := bstep (se 1 (by rfl) ⟨2891132, by rfl⟩ : syracuseStep 3854843 = 5782265) B5782265
theorem B2972143 : Blo 1140634 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B9526139 : Blo 1140634 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B31284899 : Blo 1140634 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B1925383 : Blo 1140634 1925383 := bstep (se 1 (by rfl) ⟨1444037, by rfl⟩ : syracuseStep 1925383 = 2888075) B2888075
theorem B225732845 : Blo 1140634 225732845 := bstep (se 3 (by rfl) ⟨42324908, by rfl⟩ : syracuseStep 225732845 = 84649817) B84649817
theorem B6518353 : Blo 1140634 6518353 := bstep (se 2 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 6518353 = 4888765) B4888765
theorem B15662591 : Blo 1140634 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B601954253 : Blo 1140634 601954253 := bstep (se 3 (by rfl) ⟨112866422, by rfl⟩ : syracuseStep 601954253 = 225732845) B225732845
theorem B8691137 : Blo 1140634 8691137 := bstep (se 2 (by rfl) ⟨3259176, by rfl⟩ : syracuseStep 8691137 = 6518353) B6518353
theorem B1713641 : Blo 1140634 1713641 := bstep (se 2 (by rfl) ⟨642615, by rfl⟩ : syracuseStep 1713641 = 1285231) B1285231
theorem B2567177 : Blo 1140634 2567177 := bstep (se 2 (by rfl) ⟨962691, by rfl⟩ : syracuseStep 2567177 = 1925383) B1925383
theorem B2436455 : Blo 1140634 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B1716251 : Blo 1140634 1716251 := bstep (se 1 (by rfl) ⟨1287188, by rfl⟩ : syracuseStep 1716251 = 2574377) B2574377
theorem B14660351 : Blo 1140634 14660351 := bstep (se 1 (by rfl) ⟨10995263, by rfl⟩ : syracuseStep 14660351 = 21990527) B21990527
theorem B2569895 : Blo 1140634 2569895 := bstep (se 1 (by rfl) ⟨1927421, by rfl⟩ : syracuseStep 2569895 = 3854843) B3854843
theorem B20856599 : Blo 1140634 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B10441727 : Blo 1140634 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B6350759 : Blo 1140634 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B85682953 : Blo 1140634 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B1142011 : Blo 1140634 1142011 := bstep (se 1 (by rfl) ⟨856508, by rfl⟩ : syracuseStep 1142011 = 1713017) B1713017
theorem B3962857 : Blo 1140634 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B9402617 : Blo 1140634 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B1711451 : Blo 1140634 1711451 := bstep (se 1 (by rfl) ⟨1283588, by rfl⟩ : syracuseStep 1711451 = 2567177) B2567177
theorem B5283809 : Blo 1140634 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B9773567 : Blo 1140634 9773567 := bstep (se 1 (by rfl) ⟨7330175, by rfl⟩ : syracuseStep 9773567 = 14660351) B14660351
theorem B1713263 : Blo 1140634 1713263 := bstep (se 1 (by rfl) ⟨1284947, by rfl⟩ : syracuseStep 1713263 = 2569895) B2569895
theorem B6268411 : Blo 1140634 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B67741429 : Blo 1140634 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B13904399 : Blo 1140634 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B6961151 : Blo 1140634 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B1624303 : Blo 1140634 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B401302835 : Blo 1140634 401302835 := bstep (se 1 (by rfl) ⟨300977126, by rfl⟩ : syracuseStep 401302835 = 601954253) B601954253
theorem B456975749 : Blo 1140634 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B5794091 : Blo 1140634 5794091 := bstep (se 1 (by rfl) ⟨4345568, by rfl⟩ : syracuseStep 5794091 = 8691137) B8691137
theorem B1142427 : Blo 1140634 1142427 := bstep (se 1 (by rfl) ⟨856820, by rfl⟩ : syracuseStep 1142427 = 1713641) B1713641
theorem B1144167 : Blo 1140634 1144167 := bstep (se 1 (by rfl) ⟨858125, by rfl⟩ : syracuseStep 1144167 = 1716251) B1716251
theorem B304650499 : Blo 1140634 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B33431525 : Blo 1140634 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B8662949 : Blo 1140634 8662949 := bstep (se 4 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 8662949 = 1624303) B1624303
theorem B90321905 : Blo 1140634 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B3522539 : Blo 1140634 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B18563069 : Blo 1140634 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B267535223 : Blo 1140634 267535223 := bstep (se 1 (by rfl) ⟨200651417, by rfl⟩ : syracuseStep 267535223 = 401302835) B401302835
theorem B37078397 : Blo 1140634 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B1140967 : Blo 1140634 1140967 := bstep (se 1 (by rfl) ⟨855725, by rfl⟩ : syracuseStep 1140967 = 1711451) B1711451
theorem B6515711 : Blo 1140634 6515711 := bstep (se 1 (by rfl) ⟨4886783, by rfl⟩ : syracuseStep 6515711 = 9773567) B9773567
theorem B1142175 : Blo 1140634 1142175 := bstep (se 1 (by rfl) ⟨856631, by rfl⟩ : syracuseStep 1142175 = 1713263) B1713263
theorem B3862727 : Blo 1140634 3862727 := bstep (se 1 (by rfl) ⟨2897045, by rfl⟩ : syracuseStep 3862727 = 5794091) B5794091
theorem B178356815 : Blo 1140634 178356815 := bstep (se 1 (by rfl) ⟨133767611, by rfl⟩ : syracuseStep 178356815 = 267535223) B267535223
theorem B22287683 : Blo 1140634 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B5775299 : Blo 1140634 5775299 := bstep (se 1 (by rfl) ⟨4331474, by rfl⟩ : syracuseStep 5775299 = 8662949) B8662949
theorem B406200665 : Blo 1140634 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B24718931 : Blo 1140634 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B4343807 : Blo 1140634 4343807 := bstep (se 1 (by rfl) ⟨3257855, by rfl⟩ : syracuseStep 4343807 = 6515711) B6515711
theorem B2575151 : Blo 1140634 2575151 := bstep (se 1 (by rfl) ⟨1931363, by rfl⟩ : syracuseStep 2575151 = 3862727) B3862727
theorem B60214603 : Blo 1140634 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B2348359 : Blo 1140634 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B12375379 : Blo 1140634 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B80286137 : Blo 1140634 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B270800443 : Blo 1140634 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B12524581 : Blo 1140634 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B2895871 : Blo 1140634 2895871 := bstep (se 1 (by rfl) ⟨2171903, by rfl⟩ : syracuseStep 2895871 = 4343807) B4343807
theorem B1716767 : Blo 1140634 1716767 := bstep (se 1 (by rfl) ⟨1287575, by rfl⟩ : syracuseStep 1716767 = 2575151) B2575151
theorem B3850199 : Blo 1140634 3850199 := bstep (se 1 (by rfl) ⟨2887649, by rfl⟩ : syracuseStep 3850199 = 5775299) B5775299
theorem B16500505 : Blo 1140634 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B118904543 : Blo 1140634 118904543 := bstep (se 1 (by rfl) ⟨89178407, by rfl⟩ : syracuseStep 118904543 = 178356815) B178356815
theorem B59433821 : Blo 1140634 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B16479287 : Blo 1140634 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B79269695 : Blo 1140634 79269695 := bstep (se 1 (by rfl) ⟨59452271, by rfl⟩ : syracuseStep 79269695 = 118904543) B118904543
theorem B39622547 : Blo 1140634 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B10986191 : Blo 1140634 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B2566799 : Blo 1140634 2566799 := bstep (se 1 (by rfl) ⟨1925099, by rfl⟩ : syracuseStep 2566799 = 3850199) B3850199
theorem B22000673 : Blo 1140634 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B53524091 : Blo 1140634 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B16699441 : Blo 1140634 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B3861161 : Blo 1140634 3861161 := bstep (se 2 (by rfl) ⟨1447935, by rfl⟩ : syracuseStep 3861161 = 2895871) B2895871
theorem B361067257 : Blo 1140634 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B1144511 : Blo 1140634 1144511 := bstep (se 1 (by rfl) ⟨858383, by rfl⟩ : syracuseStep 1144511 = 1716767) B1716767
theorem B26415031 : Blo 1140634 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B1711199 : Blo 1140634 1711199 := bstep (se 1 (by rfl) ⟨1283399, by rfl⟩ : syracuseStep 1711199 = 2566799) B2566799
theorem B22265921 : Blo 1140634 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B7324127 : Blo 1140634 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B2574107 : Blo 1140634 2574107 := bstep (se 1 (by rfl) ⟨1930580, by rfl⟩ : syracuseStep 2574107 = 3861161) B3861161
theorem B14667115 : Blo 1140634 14667115 := bstep (se 1 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 14667115 = 22000673) B22000673
theorem B52846463 : Blo 1140634 52846463 := bstep (se 1 (by rfl) ⟨39634847, by rfl⟩ : syracuseStep 52846463 = 79269695) B79269695
theorem B481423009 : Blo 1140634 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B35682727 : Blo 1140634 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B14843947 : Blo 1140634 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B4882751 : Blo 1140634 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B641897345 : Blo 1140634 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B1716071 : Blo 1140634 1716071 := bstep (se 1 (by rfl) ⟨1287053, by rfl⟩ : syracuseStep 1716071 = 2574107) B2574107
theorem B140923901 : Blo 1140634 140923901 := bstep (se 3 (by rfl) ⟨26423231, by rfl⟩ : syracuseStep 140923901 = 52846463) B52846463
theorem B19556153 : Blo 1140634 19556153 := bstep (se 2 (by rfl) ⟨7333557, by rfl⟩ : syracuseStep 19556153 = 14667115) B14667115
theorem B1140799 : Blo 1140634 1140799 := bstep (se 1 (by rfl) ⟨855599, by rfl⟩ : syracuseStep 1140799 = 1711199) B1711199
theorem B35220041 : Blo 1140634 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B47576969 : Blo 1140634 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B19791929 : Blo 1140634 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B93949267 : Blo 1140634 93949267 := bstep (se 1 (by rfl) ⟨70461950, by rfl⟩ : syracuseStep 93949267 = 140923901) B140923901
theorem B3255167 : Blo 1140634 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B23480027 : Blo 1140634 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B1711726253 : Blo 1140634 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B13037435 : Blo 1140634 13037435 := bstep (se 1 (by rfl) ⟨9778076, by rfl⟩ : syracuseStep 13037435 = 19556153) B19556153
theorem B1144047 : Blo 1140634 1144047 := bstep (se 1 (by rfl) ⟨858035, by rfl⟩ : syracuseStep 1144047 = 1716071) B1716071
theorem B31717979 : Blo 1140634 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B1141150835 : Blo 1140634 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B8691623 : Blo 1140634 8691623 := bstep (se 1 (by rfl) ⟨6518717, by rfl⟩ : syracuseStep 8691623 = 13037435) B13037435
theorem B21145319 : Blo 1140634 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B13194619 : Blo 1140634 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B15653351 : Blo 1140634 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B125265689 : Blo 1140634 125265689 := bstep (se 2 (by rfl) ⟨46974633, by rfl⟩ : syracuseStep 125265689 = 93949267) B93949267
theorem B8680445 : Blo 1140634 8680445 := bstep (se 3 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 8680445 = 3255167) B3255167
theorem B14096879 : Blo 1140634 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B10435567 : Blo 1140634 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B83510459 : Blo 1140634 83510459 := bstep (se 1 (by rfl) ⟨62632844, by rfl⟩ : syracuseStep 83510459 = 125265689) B125265689
theorem B70371301 : Blo 1140634 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B5786963 : Blo 1140634 5786963 := bstep (se 1 (by rfl) ⟨4340222, by rfl⟩ : syracuseStep 5786963 = 8680445) B8680445
theorem B760767223 : Blo 1140634 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B5794415 : Blo 1140634 5794415 := bstep (se 1 (by rfl) ⟨4345811, by rfl⟩ : syracuseStep 5794415 = 8691623) B8691623
theorem B55673639 : Blo 1140634 55673639 := bstep (se 1 (by rfl) ⟨41755229, by rfl⟩ : syracuseStep 55673639 = 83510459) B83510459
theorem B93828401 : Blo 1140634 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B13914089 : Blo 1140634 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B1014356297 : Blo 1140634 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B3857975 : Blo 1140634 3857975 := bstep (se 1 (by rfl) ⟨2893481, by rfl⟩ : syracuseStep 3857975 = 5786963) B5786963
theorem B9397919 : Blo 1140634 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B3862943 : Blo 1140634 3862943 := bstep (se 1 (by rfl) ⟨2897207, by rfl⟩ : syracuseStep 3862943 = 5794415) B5794415
theorem B9276059 : Blo 1140634 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B676237531 : Blo 1140634 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B6265279 : Blo 1140634 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B2571983 : Blo 1140634 2571983 := bstep (se 1 (by rfl) ⟨1928987, by rfl⟩ : syracuseStep 2571983 = 3857975) B3857975
theorem B2575295 : Blo 1140634 2575295 := bstep (se 1 (by rfl) ⟨1931471, by rfl⟩ : syracuseStep 2575295 = 3862943) B3862943
theorem B37115759 : Blo 1140634 37115759 := bstep (se 1 (by rfl) ⟨27836819, by rfl⟩ : syracuseStep 37115759 = 55673639) B55673639
theorem B62552267 : Blo 1140634 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B24743839 : Blo 1140634 24743839 := bstep (se 1 (by rfl) ⟨18557879, by rfl⟩ : syracuseStep 24743839 = 37115759) B37115759
theorem B901650041 : Blo 1140634 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B1714655 : Blo 1140634 1714655 := bstep (se 1 (by rfl) ⟨1285991, by rfl⟩ : syracuseStep 1714655 = 2571983) B2571983
theorem B1716863 : Blo 1140634 1716863 := bstep (se 1 (by rfl) ⟨1287647, by rfl⟩ : syracuseStep 1716863 = 2575295) B2575295
theorem B41701511 : Blo 1140634 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B6184039 : Blo 1140634 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B8353705 : Blo 1140634 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B601100027 : Blo 1140634 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B8245385 : Blo 1140634 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B111204029 : Blo 1140634 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B32991785 : Blo 1140634 32991785 := bstep (se 2 (by rfl) ⟨12371919, by rfl⟩ : syracuseStep 32991785 = 24743839) B24743839
theorem B1143103 : Blo 1140634 1143103 := bstep (se 1 (by rfl) ⟨857327, by rfl⟩ : syracuseStep 1143103 = 1714655) B1714655
theorem B11138273 : Blo 1140634 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B1144575 : Blo 1140634 1144575 := bstep (se 1 (by rfl) ⟨858431, by rfl⟩ : syracuseStep 1144575 = 1716863) B1716863
theorem B21994523 : Blo 1140634 21994523 := bstep (se 1 (by rfl) ⟨16495892, by rfl⟩ : syracuseStep 21994523 = 32991785) B32991785
theorem B400733351 : Blo 1140634 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B74136019 : Blo 1140634 74136019 := bstep (se 1 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 74136019 = 111204029) B111204029
theorem B7425515 : Blo 1140634 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B5496923 : Blo 1140634 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B4950343 : Blo 1140634 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B14663015 : Blo 1140634 14663015 := bstep (se 1 (by rfl) ⟨10997261, by rfl⟩ : syracuseStep 14663015 = 21994523) B21994523
theorem B98848025 : Blo 1140634 98848025 := bstep (se 2 (by rfl) ⟨37068009, by rfl⟩ : syracuseStep 98848025 = 74136019) B74136019
theorem B3664615 : Blo 1140634 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B267155567 : Blo 1140634 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B65898683 : Blo 1140634 65898683 := bstep (se 1 (by rfl) ⟨49424012, by rfl⟩ : syracuseStep 65898683 = 98848025) B98848025
theorem B4886153 : Blo 1140634 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B178103711 : Blo 1140634 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B9775343 : Blo 1140634 9775343 := bstep (se 1 (by rfl) ⟨7331507, by rfl⟩ : syracuseStep 9775343 = 14663015) B14663015
theorem B6600457 : Blo 1140634 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B3257435 : Blo 1140634 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B118735807 : Blo 1140634 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B8800609 : Blo 1140634 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B43932455 : Blo 1140634 43932455 := bstep (se 1 (by rfl) ⟨32949341, by rfl⟩ : syracuseStep 43932455 = 65898683) B65898683
theorem B6516895 : Blo 1140634 6516895 := bstep (se 1 (by rfl) ⟨4887671, by rfl⟩ : syracuseStep 6516895 = 9775343) B9775343
theorem B11734145 : Blo 1140634 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B8689193 : Blo 1140634 8689193 := bstep (se 2 (by rfl) ⟨3258447, by rfl⟩ : syracuseStep 8689193 = 6516895) B6516895
theorem B2171623 : Blo 1140634 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B158314409 : Blo 1140634 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B29288303 : Blo 1140634 29288303 := bstep (se 1 (by rfl) ⟨21966227, by rfl⟩ : syracuseStep 29288303 = 43932455) B43932455
theorem B2895497 : Blo 1140634 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B7822763 : Blo 1140634 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5792795 : Blo 1140634 5792795 := bstep (se 1 (by rfl) ⟨4344596, by rfl⟩ : syracuseStep 5792795 = 8689193) B8689193
theorem B19525535 : Blo 1140634 19525535 := bstep (se 1 (by rfl) ⟨14644151, by rfl⟩ : syracuseStep 19525535 = 29288303) B29288303
theorem B105542939 : Blo 1140634 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B5215175 : Blo 1140634 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B13017023 : Blo 1140634 13017023 := bstep (se 1 (by rfl) ⟨9762767, by rfl⟩ : syracuseStep 13017023 = 19525535) B19525535
theorem B70361959 : Blo 1140634 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B3861863 : Blo 1140634 3861863 := bstep (se 1 (by rfl) ⟨2896397, by rfl⟩ : syracuseStep 3861863 = 5792795) B5792795
theorem B1930331 : Blo 1140634 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B93815945 : Blo 1140634 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B3476783 : Blo 1140634 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B1286887 : Blo 1140634 1286887 := bstep (se 1 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 1286887 = 1930331) B1930331
theorem B2574575 : Blo 1140634 2574575 := bstep (se 1 (by rfl) ⟨1930931, by rfl⟩ : syracuseStep 2574575 = 3861863) B3861863
theorem B8678015 : Blo 1140634 8678015 := bstep (se 1 (by rfl) ⟨6508511, by rfl⟩ : syracuseStep 8678015 = 13017023) B13017023
theorem B1715849 : Blo 1140634 1715849 := bstep (se 2 (by rfl) ⟨643443, by rfl⟩ : syracuseStep 1715849 = 1286887) B1286887
theorem B1716383 : Blo 1140634 1716383 := bstep (se 1 (by rfl) ⟨1287287, by rfl⟩ : syracuseStep 1716383 = 2574575) B2574575
theorem B5785343 : Blo 1140634 5785343 := bstep (se 1 (by rfl) ⟨4339007, by rfl⟩ : syracuseStep 5785343 = 8678015) B8678015
theorem B62543963 : Blo 1140634 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B9271421 : Blo 1140634 9271421 := bstep (se 3 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 9271421 = 3476783) B3476783
theorem B41695975 : Blo 1140634 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B6180947 : Blo 1140634 6180947 := bstep (se 1 (by rfl) ⟨4635710, by rfl⟩ : syracuseStep 6180947 = 9271421) B9271421
theorem B3856895 : Blo 1140634 3856895 := bstep (se 1 (by rfl) ⟨2892671, by rfl⟩ : syracuseStep 3856895 = 5785343) B5785343
theorem B1143899 : Blo 1140634 1143899 := bstep (se 1 (by rfl) ⟨857924, by rfl⟩ : syracuseStep 1143899 = 1715849) B1715849
theorem B1144255 : Blo 1140634 1144255 := bstep (se 1 (by rfl) ⟨858191, by rfl⟩ : syracuseStep 1144255 = 1716383) B1716383
theorem B2571263 : Blo 1140634 2571263 := bstep (se 1 (by rfl) ⟨1928447, by rfl⟩ : syracuseStep 2571263 = 3856895) B3856895
theorem B55594633 : Blo 1140634 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B4120631 : Blo 1140634 4120631 := bstep (se 1 (by rfl) ⟨3090473, by rfl⟩ : syracuseStep 4120631 = 6180947) B6180947
theorem B74126177 : Blo 1140634 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B1714175 : Blo 1140634 1714175 := bstep (se 1 (by rfl) ⟨1285631, by rfl⟩ : syracuseStep 1714175 = 2571263) B2571263
theorem B2747087 : Blo 1140634 2747087 := bstep (se 1 (by rfl) ⟨2060315, by rfl⟩ : syracuseStep 2747087 = 4120631) B4120631
theorem B49417451 : Blo 1140634 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B1142783 : Blo 1140634 1142783 := bstep (se 1 (by rfl) ⟨857087, by rfl⟩ : syracuseStep 1142783 = 1714175) B1714175
theorem B1831391 : Blo 1140634 1831391 := bstep (se 1 (by rfl) ⟨1373543, by rfl⟩ : syracuseStep 1831391 = 2747087) B2747087
theorem B1220927 : Blo 1140634 1220927 := bstep (se 1 (by rfl) ⟨915695, by rfl⟩ : syracuseStep 1220927 = 1831391) B1831391
theorem B32944967 : Blo 1140634 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B21963311 : Blo 1140634 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B3255805 : Blo 1140634 3255805 := bstep (se 3 (by rfl) ⟨610463, by rfl⟩ : syracuseStep 3255805 = 1220927) B1220927
theorem B4341073 : Blo 1140634 4341073 := bstep (se 2 (by rfl) ⟨1627902, by rfl⟩ : syracuseStep 4341073 = 3255805) B3255805
theorem B14642207 : Blo 1140634 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B5788097 : Blo 1140634 5788097 := bstep (se 2 (by rfl) ⟨2170536, by rfl⟩ : syracuseStep 5788097 = 4341073) B4341073
theorem B9761471 : Blo 1140634 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B6507647 : Blo 1140634 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B3858731 : Blo 1140634 3858731 := bstep (se 1 (by rfl) ⟨2894048, by rfl⟩ : syracuseStep 3858731 = 5788097) B5788097
theorem B4338431 : Blo 1140634 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B2572487 : Blo 1140634 2572487 := bstep (se 1 (by rfl) ⟨1929365, by rfl⟩ : syracuseStep 2572487 = 3858731) B3858731
theorem B2892287 : Blo 1140634 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B1714991 : Blo 1140634 1714991 := bstep (se 1 (by rfl) ⟨1286243, by rfl⟩ : syracuseStep 1714991 = 2572487) B2572487
theorem B1928191 : Blo 1140634 1928191 := bstep (se 1 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 1928191 = 2892287) B2892287
theorem B1143327 : Blo 1140634 1143327 := bstep (se 1 (by rfl) ⟨857495, by rfl⟩ : syracuseStep 1143327 = 1714991) B1714991
theorem B2570921 : Blo 1140634 2570921 := bstep (se 2 (by rfl) ⟨964095, by rfl⟩ : syracuseStep 2570921 = 1928191) B1928191
theorem B1713947 : Blo 1140634 1713947 := bstep (se 1 (by rfl) ⟨1285460, by rfl⟩ : syracuseStep 1713947 = 2570921) B2570921
theorem B1142631 : Blo 1140634 1142631 := bstep (se 1 (by rfl) ⟨856973, by rfl⟩ : syracuseStep 1142631 = 1713947) B1713947

theorem C0 (j : ℕ) (h1 : 285158 ≤ j) (h2 : j ≤ 285857) : Blo 1140634 (4 * j + 3) := by
  interval_cases j
  · exact B1140635
  · exact B1140639
  · exact B1140643
  · exact B1140647
  · exact B1140651
  · exact B1140655
  · exact B1140659
  · exact B1140663
  · exact B1140667
  · exact B1140671
  · exact B1140675
  · exact B1140679
  · exact B1140683
  · exact B1140687
  · exact B1140691
  · exact B1140695
  · exact B1140699
  · exact B1140703
  · exact B1140707
  · exact B1140711
  · exact B1140715
  · exact B1140719
  · exact B1140723
  · exact B1140727
  · exact B1140731
  · exact B1140735
  · exact B1140739
  · exact B1140743
  · exact B1140747
  · exact B1140751
  · exact B1140755
  · exact B1140759
  · exact B1140763
  · exact B1140767
  · exact B1140771
  · exact B1140775
  · exact B1140779
  · exact B1140783
  · exact B1140787
  · exact B1140791
  · exact B1140795
  · exact B1140799
  · exact B1140803
  · exact B1140807
  · exact B1140811
  · exact B1140815
  · exact B1140819
  · exact B1140823
  · exact B1140827
  · exact B1140831
  · exact B1140835
  · exact B1140839
  · exact B1140843
  · exact B1140847
  · exact B1140851
  · exact B1140855
  · exact B1140859
  · exact B1140863
  · exact B1140867
  · exact B1140871
  · exact B1140875
  · exact B1140879
  · exact B1140883
  · exact B1140887
  · exact B1140891
  · exact B1140895
  · exact B1140899
  · exact B1140903
  · exact B1140907
  · exact B1140911
  · exact B1140915
  · exact B1140919
  · exact B1140923
  · exact B1140927
  · exact B1140931
  · exact B1140935
  · exact B1140939
  · exact B1140943
  · exact B1140947
  · exact B1140951
  · exact B1140955
  · exact B1140959
  · exact B1140963
  · exact B1140967
  · exact B1140971
  · exact B1140975
  · exact B1140979
  · exact B1140983
  · exact B1140987
  · exact B1140991
  · exact B1140995
  · exact B1140999
  · exact B1141003
  · exact B1141007
  · exact B1141011
  · exact B1141015
  · exact B1141019
  · exact B1141023
  · exact B1141027
  · exact B1141031
  · exact B1141035
  · exact B1141039
  · exact B1141043
  · exact B1141047
  · exact B1141051
  · exact B1141055
  · exact B1141059
  · exact B1141063
  · exact B1141067
  · exact B1141071
  · exact B1141075
  · exact B1141079
  · exact B1141083
  · exact B1141087
  · exact B1141091
  · exact B1141095
  · exact B1141099
  · exact B1141103
  · exact B1141107
  · exact B1141111
  · exact B1141115
  · exact B1141119
  · exact B1141123
  · exact B1141127
  · exact B1141131
  · exact B1141135
  · exact B1141139
  · exact B1141143
  · exact B1141147
  · exact B1141151
  · exact B1141155
  · exact B1141159
  · exact B1141163
  · exact B1141167
  · exact B1141171
  · exact B1141175
  · exact B1141179
  · exact B1141183
  · exact B1141187
  · exact B1141191
  · exact B1141195
  · exact B1141199
  · exact B1141203
  · exact B1141207
  · exact B1141211
  · exact B1141215
  · exact B1141219
  · exact B1141223
  · exact B1141227
  · exact B1141231
  · exact B1141235
  · exact B1141239
  · exact B1141243
  · exact B1141247
  · exact B1141251
  · exact B1141255
  · exact B1141259
  · exact B1141263
  · exact B1141267
  · exact B1141271
  · exact B1141275
  · exact B1141279
  · exact B1141283
  · exact B1141287
  · exact B1141291
  · exact B1141295
  · exact B1141299
  · exact B1141303
  · exact B1141307
  · exact B1141311
  · exact B1141315
  · exact B1141319
  · exact B1141323
  · exact B1141327
  · exact B1141331
  · exact B1141335
  · exact B1141339
  · exact B1141343
  · exact B1141347
  · exact B1141351
  · exact B1141355
  · exact B1141359
  · exact B1141363
  · exact B1141367
  · exact B1141371
  · exact B1141375
  · exact B1141379
  · exact B1141383
  · exact B1141387
  · exact B1141391
  · exact B1141395
  · exact B1141399
  · exact B1141403
  · exact B1141407
  · exact B1141411
  · exact B1141415
  · exact B1141419
  · exact B1141423
  · exact B1141427
  · exact B1141431
  · exact B1141435
  · exact B1141439
  · exact B1141443
  · exact B1141447
  · exact B1141451
  · exact B1141455
  · exact B1141459
  · exact B1141463
  · exact B1141467
  · exact B1141471
  · exact B1141475
  · exact B1141479
  · exact B1141483
  · exact B1141487
  · exact B1141491
  · exact B1141495
  · exact B1141499
  · exact B1141503
  · exact B1141507
  · exact B1141511
  · exact B1141515
  · exact B1141519
  · exact B1141523
  · exact B1141527
  · exact B1141531
  · exact B1141535
  · exact B1141539
  · exact B1141543
  · exact B1141547
  · exact B1141551
  · exact B1141555
  · exact B1141559
  · exact B1141563
  · exact B1141567
  · exact B1141571
  · exact B1141575
  · exact B1141579
  · exact B1141583
  · exact B1141587
  · exact B1141591
  · exact B1141595
  · exact B1141599
  · exact B1141603
  · exact B1141607
  · exact B1141611
  · exact B1141615
  · exact B1141619
  · exact B1141623
  · exact B1141627
  · exact B1141631
  · exact B1141635
  · exact B1141639
  · exact B1141643
  · exact B1141647
  · exact B1141651
  · exact B1141655
  · exact B1141659
  · exact B1141663
  · exact B1141667
  · exact B1141671
  · exact B1141675
  · exact B1141679
  · exact B1141683
  · exact B1141687
  · exact B1141691
  · exact B1141695
  · exact B1141699
  · exact B1141703
  · exact B1141707
  · exact B1141711
  · exact B1141715
  · exact B1141719
  · exact B1141723
  · exact B1141727
  · exact B1141731
  · exact B1141735
  · exact B1141739
  · exact B1141743
  · exact B1141747
  · exact B1141751
  · exact B1141755
  · exact B1141759
  · exact B1141763
  · exact B1141767
  · exact B1141771
  · exact B1141775
  · exact B1141779
  · exact B1141783
  · exact B1141787
  · exact B1141791
  · exact B1141795
  · exact B1141799
  · exact B1141803
  · exact B1141807
  · exact B1141811
  · exact B1141815
  · exact B1141819
  · exact B1141823
  · exact B1141827
  · exact B1141831
  · exact B1141835
  · exact B1141839
  · exact B1141843
  · exact B1141847
  · exact B1141851
  · exact B1141855
  · exact B1141859
  · exact B1141863
  · exact B1141867
  · exact B1141871
  · exact B1141875
  · exact B1141879
  · exact B1141883
  · exact B1141887
  · exact B1141891
  · exact B1141895
  · exact B1141899
  · exact B1141903
  · exact B1141907
  · exact B1141911
  · exact B1141915
  · exact B1141919
  · exact B1141923
  · exact B1141927
  · exact B1141931
  · exact B1141935
  · exact B1141939
  · exact B1141943
  · exact B1141947
  · exact B1141951
  · exact B1141955
  · exact B1141959
  · exact B1141963
  · exact B1141967
  · exact B1141971
  · exact B1141975
  · exact B1141979
  · exact B1141983
  · exact B1141987
  · exact B1141991
  · exact B1141995
  · exact B1141999
  · exact B1142003
  · exact B1142007
  · exact B1142011
  · exact B1142015
  · exact B1142019
  · exact B1142023
  · exact B1142027
  · exact B1142031
  · exact B1142035
  · exact B1142039
  · exact B1142043
  · exact B1142047
  · exact B1142051
  · exact B1142055
  · exact B1142059
  · exact B1142063
  · exact B1142067
  · exact B1142071
  · exact B1142075
  · exact B1142079
  · exact B1142083
  · exact B1142087
  · exact B1142091
  · exact B1142095
  · exact B1142099
  · exact B1142103
  · exact B1142107
  · exact B1142111
  · exact B1142115
  · exact B1142119
  · exact B1142123
  · exact B1142127
  · exact B1142131
  · exact B1142135
  · exact B1142139
  · exact B1142143
  · exact B1142147
  · exact B1142151
  · exact B1142155
  · exact B1142159
  · exact B1142163
  · exact B1142167
  · exact B1142171
  · exact B1142175
  · exact B1142179
  · exact B1142183
  · exact B1142187
  · exact B1142191
  · exact B1142195
  · exact B1142199
  · exact B1142203
  · exact B1142207
  · exact B1142211
  · exact B1142215
  · exact B1142219
  · exact B1142223
  · exact B1142227
  · exact B1142231
  · exact B1142235
  · exact B1142239
  · exact B1142243
  · exact B1142247
  · exact B1142251
  · exact B1142255
  · exact B1142259
  · exact B1142263
  · exact B1142267
  · exact B1142271
  · exact B1142275
  · exact B1142279
  · exact B1142283
  · exact B1142287
  · exact B1142291
  · exact B1142295
  · exact B1142299
  · exact B1142303
  · exact B1142307
  · exact B1142311
  · exact B1142315
  · exact B1142319
  · exact B1142323
  · exact B1142327
  · exact B1142331
  · exact B1142335
  · exact B1142339
  · exact B1142343
  · exact B1142347
  · exact B1142351
  · exact B1142355
  · exact B1142359
  · exact B1142363
  · exact B1142367
  · exact B1142371
  · exact B1142375
  · exact B1142379
  · exact B1142383
  · exact B1142387
  · exact B1142391
  · exact B1142395
  · exact B1142399
  · exact B1142403
  · exact B1142407
  · exact B1142411
  · exact B1142415
  · exact B1142419
  · exact B1142423
  · exact B1142427
  · exact B1142431
  · exact B1142435
  · exact B1142439
  · exact B1142443
  · exact B1142447
  · exact B1142451
  · exact B1142455
  · exact B1142459
  · exact B1142463
  · exact B1142467
  · exact B1142471
  · exact B1142475
  · exact B1142479
  · exact B1142483
  · exact B1142487
  · exact B1142491
  · exact B1142495
  · exact B1142499
  · exact B1142503
  · exact B1142507
  · exact B1142511
  · exact B1142515
  · exact B1142519
  · exact B1142523
  · exact B1142527
  · exact B1142531
  · exact B1142535
  · exact B1142539
  · exact B1142543
  · exact B1142547
  · exact B1142551
  · exact B1142555
  · exact B1142559
  · exact B1142563
  · exact B1142567
  · exact B1142571
  · exact B1142575
  · exact B1142579
  · exact B1142583
  · exact B1142587
  · exact B1142591
  · exact B1142595
  · exact B1142599
  · exact B1142603
  · exact B1142607
  · exact B1142611
  · exact B1142615
  · exact B1142619
  · exact B1142623
  · exact B1142627
  · exact B1142631
  · exact B1142635
  · exact B1142639
  · exact B1142643
  · exact B1142647
  · exact B1142651
  · exact B1142655
  · exact B1142659
  · exact B1142663
  · exact B1142667
  · exact B1142671
  · exact B1142675
  · exact B1142679
  · exact B1142683
  · exact B1142687
  · exact B1142691
  · exact B1142695
  · exact B1142699
  · exact B1142703
  · exact B1142707
  · exact B1142711
  · exact B1142715
  · exact B1142719
  · exact B1142723
  · exact B1142727
  · exact B1142731
  · exact B1142735
  · exact B1142739
  · exact B1142743
  · exact B1142747
  · exact B1142751
  · exact B1142755
  · exact B1142759
  · exact B1142763
  · exact B1142767
  · exact B1142771
  · exact B1142775
  · exact B1142779
  · exact B1142783
  · exact B1142787
  · exact B1142791
  · exact B1142795
  · exact B1142799
  · exact B1142803
  · exact B1142807
  · exact B1142811
  · exact B1142815
  · exact B1142819
  · exact B1142823
  · exact B1142827
  · exact B1142831
  · exact B1142835
  · exact B1142839
  · exact B1142843
  · exact B1142847
  · exact B1142851
  · exact B1142855
  · exact B1142859
  · exact B1142863
  · exact B1142867
  · exact B1142871
  · exact B1142875
  · exact B1142879
  · exact B1142883
  · exact B1142887
  · exact B1142891
  · exact B1142895
  · exact B1142899
  · exact B1142903
  · exact B1142907
  · exact B1142911
  · exact B1142915
  · exact B1142919
  · exact B1142923
  · exact B1142927
  · exact B1142931
  · exact B1142935
  · exact B1142939
  · exact B1142943
  · exact B1142947
  · exact B1142951
  · exact B1142955
  · exact B1142959
  · exact B1142963
  · exact B1142967
  · exact B1142971
  · exact B1142975
  · exact B1142979
  · exact B1142983
  · exact B1142987
  · exact B1142991
  · exact B1142995
  · exact B1142999
  · exact B1143003
  · exact B1143007
  · exact B1143011
  · exact B1143015
  · exact B1143019
  · exact B1143023
  · exact B1143027
  · exact B1143031
  · exact B1143035
  · exact B1143039
  · exact B1143043
  · exact B1143047
  · exact B1143051
  · exact B1143055
  · exact B1143059
  · exact B1143063
  · exact B1143067
  · exact B1143071
  · exact B1143075
  · exact B1143079
  · exact B1143083
  · exact B1143087
  · exact B1143091
  · exact B1143095
  · exact B1143099
  · exact B1143103
  · exact B1143107
  · exact B1143111
  · exact B1143115
  · exact B1143119
  · exact B1143123
  · exact B1143127
  · exact B1143131
  · exact B1143135
  · exact B1143139
  · exact B1143143
  · exact B1143147
  · exact B1143151
  · exact B1143155
  · exact B1143159
  · exact B1143163
  · exact B1143167
  · exact B1143171
  · exact B1143175
  · exact B1143179
  · exact B1143183
  · exact B1143187
  · exact B1143191
  · exact B1143195
  · exact B1143199
  · exact B1143203
  · exact B1143207
  · exact B1143211
  · exact B1143215
  · exact B1143219
  · exact B1143223
  · exact B1143227
  · exact B1143231
  · exact B1143235
  · exact B1143239
  · exact B1143243
  · exact B1143247
  · exact B1143251
  · exact B1143255
  · exact B1143259
  · exact B1143263
  · exact B1143267
  · exact B1143271
  · exact B1143275
  · exact B1143279
  · exact B1143283
  · exact B1143287
  · exact B1143291
  · exact B1143295
  · exact B1143299
  · exact B1143303
  · exact B1143307
  · exact B1143311
  · exact B1143315
  · exact B1143319
  · exact B1143323
  · exact B1143327
  · exact B1143331
  · exact B1143335
  · exact B1143339
  · exact B1143343
  · exact B1143347
  · exact B1143351
  · exact B1143355
  · exact B1143359
  · exact B1143363
  · exact B1143367
  · exact B1143371
  · exact B1143375
  · exact B1143379
  · exact B1143383
  · exact B1143387
  · exact B1143391
  · exact B1143395
  · exact B1143399
  · exact B1143403
  · exact B1143407
  · exact B1143411
  · exact B1143415
  · exact B1143419
  · exact B1143423
  · exact B1143427
  · exact B1143431

theorem C1 (j : ℕ) (h1 : 285858 ≤ j) (h2 : j ≤ 286157) : Blo 1140634 (4 * j + 3) := by
  interval_cases j
  · exact B1143435
  · exact B1143439
  · exact B1143443
  · exact B1143447
  · exact B1143451
  · exact B1143455
  · exact B1143459
  · exact B1143463
  · exact B1143467
  · exact B1143471
  · exact B1143475
  · exact B1143479
  · exact B1143483
  · exact B1143487
  · exact B1143491
  · exact B1143495
  · exact B1143499
  · exact B1143503
  · exact B1143507
  · exact B1143511
  · exact B1143515
  · exact B1143519
  · exact B1143523
  · exact B1143527
  · exact B1143531
  · exact B1143535
  · exact B1143539
  · exact B1143543
  · exact B1143547
  · exact B1143551
  · exact B1143555
  · exact B1143559
  · exact B1143563
  · exact B1143567
  · exact B1143571
  · exact B1143575
  · exact B1143579
  · exact B1143583
  · exact B1143587
  · exact B1143591
  · exact B1143595
  · exact B1143599
  · exact B1143603
  · exact B1143607
  · exact B1143611
  · exact B1143615
  · exact B1143619
  · exact B1143623
  · exact B1143627
  · exact B1143631
  · exact B1143635
  · exact B1143639
  · exact B1143643
  · exact B1143647
  · exact B1143651
  · exact B1143655
  · exact B1143659
  · exact B1143663
  · exact B1143667
  · exact B1143671
  · exact B1143675
  · exact B1143679
  · exact B1143683
  · exact B1143687
  · exact B1143691
  · exact B1143695
  · exact B1143699
  · exact B1143703
  · exact B1143707
  · exact B1143711
  · exact B1143715
  · exact B1143719
  · exact B1143723
  · exact B1143727
  · exact B1143731
  · exact B1143735
  · exact B1143739
  · exact B1143743
  · exact B1143747
  · exact B1143751
  · exact B1143755
  · exact B1143759
  · exact B1143763
  · exact B1143767
  · exact B1143771
  · exact B1143775
  · exact B1143779
  · exact B1143783
  · exact B1143787
  · exact B1143791
  · exact B1143795
  · exact B1143799
  · exact B1143803
  · exact B1143807
  · exact B1143811
  · exact B1143815
  · exact B1143819
  · exact B1143823
  · exact B1143827
  · exact B1143831
  · exact B1143835
  · exact B1143839
  · exact B1143843
  · exact B1143847
  · exact B1143851
  · exact B1143855
  · exact B1143859
  · exact B1143863
  · exact B1143867
  · exact B1143871
  · exact B1143875
  · exact B1143879
  · exact B1143883
  · exact B1143887
  · exact B1143891
  · exact B1143895
  · exact B1143899
  · exact B1143903
  · exact B1143907
  · exact B1143911
  · exact B1143915
  · exact B1143919
  · exact B1143923
  · exact B1143927
  · exact B1143931
  · exact B1143935
  · exact B1143939
  · exact B1143943
  · exact B1143947
  · exact B1143951
  · exact B1143955
  · exact B1143959
  · exact B1143963
  · exact B1143967
  · exact B1143971
  · exact B1143975
  · exact B1143979
  · exact B1143983
  · exact B1143987
  · exact B1143991
  · exact B1143995
  · exact B1143999
  · exact B1144003
  · exact B1144007
  · exact B1144011
  · exact B1144015
  · exact B1144019
  · exact B1144023
  · exact B1144027
  · exact B1144031
  · exact B1144035
  · exact B1144039
  · exact B1144043
  · exact B1144047
  · exact B1144051
  · exact B1144055
  · exact B1144059
  · exact B1144063
  · exact B1144067
  · exact B1144071
  · exact B1144075
  · exact B1144079
  · exact B1144083
  · exact B1144087
  · exact B1144091
  · exact B1144095
  · exact B1144099
  · exact B1144103
  · exact B1144107
  · exact B1144111
  · exact B1144115
  · exact B1144119
  · exact B1144123
  · exact B1144127
  · exact B1144131
  · exact B1144135
  · exact B1144139
  · exact B1144143
  · exact B1144147
  · exact B1144151
  · exact B1144155
  · exact B1144159
  · exact B1144163
  · exact B1144167
  · exact B1144171
  · exact B1144175
  · exact B1144179
  · exact B1144183
  · exact B1144187
  · exact B1144191
  · exact B1144195
  · exact B1144199
  · exact B1144203
  · exact B1144207
  · exact B1144211
  · exact B1144215
  · exact B1144219
  · exact B1144223
  · exact B1144227
  · exact B1144231
  · exact B1144235
  · exact B1144239
  · exact B1144243
  · exact B1144247
  · exact B1144251
  · exact B1144255
  · exact B1144259
  · exact B1144263
  · exact B1144267
  · exact B1144271
  · exact B1144275
  · exact B1144279
  · exact B1144283
  · exact B1144287
  · exact B1144291
  · exact B1144295
  · exact B1144299
  · exact B1144303
  · exact B1144307
  · exact B1144311
  · exact B1144315
  · exact B1144319
  · exact B1144323
  · exact B1144327
  · exact B1144331
  · exact B1144335
  · exact B1144339
  · exact B1144343
  · exact B1144347
  · exact B1144351
  · exact B1144355
  · exact B1144359
  · exact B1144363
  · exact B1144367
  · exact B1144371
  · exact B1144375
  · exact B1144379
  · exact B1144383
  · exact B1144387
  · exact B1144391
  · exact B1144395
  · exact B1144399
  · exact B1144403
  · exact B1144407
  · exact B1144411
  · exact B1144415
  · exact B1144419
  · exact B1144423
  · exact B1144427
  · exact B1144431
  · exact B1144435
  · exact B1144439
  · exact B1144443
  · exact B1144447
  · exact B1144451
  · exact B1144455
  · exact B1144459
  · exact B1144463
  · exact B1144467
  · exact B1144471
  · exact B1144475
  · exact B1144479
  · exact B1144483
  · exact B1144487
  · exact B1144491
  · exact B1144495
  · exact B1144499
  · exact B1144503
  · exact B1144507
  · exact B1144511
  · exact B1144515
  · exact B1144519
  · exact B1144523
  · exact B1144527
  · exact B1144531
  · exact B1144535
  · exact B1144539
  · exact B1144543
  · exact B1144547
  · exact B1144551
  · exact B1144555
  · exact B1144559
  · exact B1144563
  · exact B1144567
  · exact B1144571
  · exact B1144575
  · exact B1144579
  · exact B1144583
  · exact B1144587
  · exact B1144591
  · exact B1144595
  · exact B1144599
  · exact B1144603
  · exact B1144607
  · exact B1144611
  · exact B1144615
  · exact B1144619
  · exact B1144623
  · exact B1144627
  · exact B1144631

theorem solution (m : ℕ) (hlo : 1140634 ≤ m) (hhi : m ≤ 1144634) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 285158 ≤ j := by omega
    have hj2 : j ≤ 286157 := by omega
    have hb : Blo 1140634 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 285858 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
