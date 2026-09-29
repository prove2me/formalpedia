-- Prove2me | solution 1 for syracuse_descends_range_906576_908575
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:16:22.670688+00:00
-- url     : https://prove2.me/submissions/27dde80f-cfb2-48d5-bef2-c1fc6d675ab0

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


theorem B2039813 : Blo 906576 2039813 := bbase (se 4 (by rfl) ⟨191232, by rfl⟩ : syracuseStep 2039813 = 382465) (by norm_num)
theorem B1359893 : Blo 906576 1359893 := bbase (se 6 (by rfl) ⟨31872, by rfl⟩ : syracuseStep 1359893 = 63745) (by norm_num)
theorem B1359917 : Blo 906576 1359917 := bbase (se 3 (by rfl) ⟨254984, by rfl⟩ : syracuseStep 1359917 = 509969) (by norm_num)
theorem B1359941 : Blo 906576 1359941 := bbase (se 4 (by rfl) ⟨127494, by rfl⟩ : syracuseStep 1359941 = 254989) (by norm_num)
theorem B1531973 : Blo 906576 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B2039885 : Blo 906576 2039885 := bbase (se 3 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 2039885 = 764957) (by norm_num)
theorem B1359965 : Blo 906576 1359965 := bbase (se 3 (by rfl) ⟨254993, by rfl⟩ : syracuseStep 1359965 = 509987) (by norm_num)
theorem B1359989 : Blo 906576 1359989 := bbase (se 5 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 1359989 = 127499) (by norm_num)
theorem B1360013 : Blo 906576 1360013 := bbase (se 3 (by rfl) ⟨255002, by rfl⟩ : syracuseStep 1360013 = 510005) (by norm_num)
theorem B2039957 : Blo 906576 2039957 := bbase (se 6 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 2039957 = 95623) (by norm_num)
theorem B1360037 : Blo 906576 1360037 := bbase (se 4 (by rfl) ⟨127503, by rfl⟩ : syracuseStep 1360037 = 255007) (by norm_num)
theorem B1360061 : Blo 906576 1360061 := bbase (se 3 (by rfl) ⟨255011, by rfl⟩ : syracuseStep 1360061 = 510023) (by norm_num)
theorem B1532101 : Blo 906576 1532101 := bbase (se 4 (by rfl) ⟨143634, by rfl⟩ : syracuseStep 1532101 = 287269) (by norm_num)
theorem B1745101 : Blo 906576 1745101 := bbase (se 3 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 1745101 = 654413) (by norm_num)
theorem B1360085 : Blo 906576 1360085 := bbase (se 7 (by rfl) ⟨15938, by rfl⟩ : syracuseStep 1360085 = 31877) (by norm_num)
theorem B2040029 : Blo 906576 2040029 := bbase (se 3 (by rfl) ⟨382505, by rfl⟩ : syracuseStep 2040029 = 765011) (by norm_num)
theorem B1360109 : Blo 906576 1360109 := bbase (se 3 (by rfl) ⟨255020, by rfl⟩ : syracuseStep 1360109 = 510041) (by norm_num)
theorem B1360133 : Blo 906576 1360133 := bbase (se 4 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 1360133 = 255025) (by norm_num)
theorem B1360157 : Blo 906576 1360157 := bbase (se 3 (by rfl) ⟨255029, by rfl⟩ : syracuseStep 1360157 = 510059) (by norm_num)
theorem B1532189 : Blo 906576 1532189 := bbase (se 3 (by rfl) ⟨287285, by rfl⟩ : syracuseStep 1532189 = 574571) (by norm_num)
theorem B2040101 : Blo 906576 2040101 := bbase (se 4 (by rfl) ⟨191259, by rfl⟩ : syracuseStep 2040101 = 382519) (by norm_num)
theorem B1360181 : Blo 906576 1360181 := bbase (se 5 (by rfl) ⟨63758, by rfl⟩ : syracuseStep 1360181 = 127517) (by norm_num)
theorem B1360205 : Blo 906576 1360205 := bbase (se 3 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 1360205 = 510077) (by norm_num)
theorem B1360229 : Blo 906576 1360229 := bbase (se 4 (by rfl) ⟨127521, by rfl⟩ : syracuseStep 1360229 = 255043) (by norm_num)
theorem B2040173 : Blo 906576 2040173 := bbase (se 3 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 2040173 = 765065) (by norm_num)
theorem B1360253 : Blo 906576 1360253 := bbase (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) (by norm_num)
theorem B4596101 : Blo 906576 4596101 := bbase (se 4 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 4596101 = 861769) (by norm_num)
theorem B1360277 : Blo 906576 1360277 := bbase (se 6 (by rfl) ⟨31881, by rfl⟩ : syracuseStep 1360277 = 63763) (by norm_num)
theorem B1532317 : Blo 906576 1532317 := bbase (se 3 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 1532317 = 574619) (by norm_num)
theorem B3064229 : Blo 906576 3064229 := bbase (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) (by norm_num)
theorem B1360301 : Blo 906576 1360301 := bbase (se 3 (by rfl) ⟨255056, by rfl⟩ : syracuseStep 1360301 = 510113) (by norm_num)
theorem B2040245 : Blo 906576 2040245 := bbase (se 5 (by rfl) ⟨95636, by rfl⟩ : syracuseStep 2040245 = 191273) (by norm_num)
theorem B1089985 : Blo 906576 1089985 := bbase (se 2 (by rfl) ⟨408744, by rfl⟩ : syracuseStep 1089985 = 817489) (by norm_num)
theorem B1360325 : Blo 906576 1360325 := bbase (se 4 (by rfl) ⟨127530, by rfl⟩ : syracuseStep 1360325 = 255061) (by norm_num)
theorem B1360349 : Blo 906576 1360349 := bbase (se 3 (by rfl) ⟨255065, by rfl⟩ : syracuseStep 1360349 = 510131) (by norm_num)
theorem B1360373 : Blo 906576 1360373 := bbase (se 5 (by rfl) ⟨63767, by rfl⟩ : syracuseStep 1360373 = 127535) (by norm_num)
theorem B1532405 : Blo 906576 1532405 := bbase (se 5 (by rfl) ⟨71831, by rfl⟩ : syracuseStep 1532405 = 143663) (by norm_num)
theorem B2040317 : Blo 906576 2040317 := bbase (se 3 (by rfl) ⟨382559, by rfl⟩ : syracuseStep 2040317 = 765119) (by norm_num)
theorem B1049093 : Blo 906576 1049093 := bbase (se 4 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 1049093 = 196705) (by norm_num)
theorem B1360397 : Blo 906576 1360397 := bbase (se 3 (by rfl) ⟨255074, by rfl⟩ : syracuseStep 1360397 = 510149) (by norm_num)
theorem B1090081 : Blo 906576 1090081 := bbase (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) (by norm_num)
theorem B1360421 : Blo 906576 1360421 := bbase (se 4 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 1360421 = 255079) (by norm_num)
theorem B1147441 : Blo 906576 1147441 := bbase (se 2 (by rfl) ⟨430290, by rfl⟩ : syracuseStep 1147441 = 860581) (by norm_num)
theorem B1360445 : Blo 906576 1360445 := bbase (se 3 (by rfl) ⟨255083, by rfl⟩ : syracuseStep 1360445 = 510167) (by norm_num)
theorem B2040389 : Blo 906576 2040389 := bbase (se 4 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 2040389 = 382573) (by norm_num)
theorem B1360469 : Blo 906576 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B27927125 : Blo 906576 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B1360493 : Blo 906576 1360493 := bbase (se 3 (by rfl) ⟨255092, by rfl⟩ : syracuseStep 1360493 = 510185) (by norm_num)
theorem B1532533 : Blo 906576 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B1360517 : Blo 906576 1360517 := bbase (se 4 (by rfl) ⟨127548, by rfl⟩ : syracuseStep 1360517 = 255097) (by norm_num)
theorem B2040461 : Blo 906576 2040461 := bbase (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) (by norm_num)
theorem B1147537 : Blo 906576 1147537 := bbase (se 2 (by rfl) ⟨430326, by rfl⟩ : syracuseStep 1147537 = 860653) (by norm_num)
theorem B1360541 : Blo 906576 1360541 := bbase (se 3 (by rfl) ⟨255101, by rfl⟩ : syracuseStep 1360541 = 510203) (by norm_num)
theorem B1360565 : Blo 906576 1360565 := bbase (se 5 (by rfl) ⟨63776, by rfl⟩ : syracuseStep 1360565 = 127553) (by norm_num)
theorem B1360589 : Blo 906576 1360589 := bbase (se 3 (by rfl) ⟨255110, by rfl⟩ : syracuseStep 1360589 = 510221) (by norm_num)
theorem B1532621 : Blo 906576 1532621 := bbase (se 3 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 1532621 = 574733) (by norm_num)
theorem B2040533 : Blo 906576 2040533 := bbase (se 7 (by rfl) ⟨23912, by rfl⟩ : syracuseStep 2040533 = 47825) (by norm_num)
theorem B1360613 : Blo 906576 1360613 := bbase (se 4 (by rfl) ⟨127557, by rfl⟩ : syracuseStep 1360613 = 255115) (by norm_num)
theorem B1360637 : Blo 906576 1360637 := bbase (se 3 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 1360637 = 510239) (by norm_num)
theorem B1721101 : Blo 906576 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B1360661 : Blo 906576 1360661 := bbase (se 6 (by rfl) ⟨31890, by rfl⟩ : syracuseStep 1360661 = 63781) (by norm_num)
theorem B2040605 : Blo 906576 2040605 := bbase (se 3 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 2040605 = 765227) (by norm_num)
theorem B1360685 : Blo 906576 1360685 := bbase (se 3 (by rfl) ⟨255128, by rfl⟩ : syracuseStep 1360685 = 510257) (by norm_num)
theorem B2179885 : Blo 906576 2179885 := bbase (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) (by norm_num)
theorem B1147709 : Blo 906576 1147709 := bbase (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) (by norm_num)
theorem B1360709 : Blo 906576 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B1532749 : Blo 906576 1532749 := bbase (se 3 (by rfl) ⟨287390, by rfl⟩ : syracuseStep 1532749 = 574781) (by norm_num)
theorem B3064661 : Blo 906576 3064661 := bbase (se 9 (by rfl) ⟨8978, by rfl⟩ : syracuseStep 3064661 = 17957) (by norm_num)
theorem B1360733 : Blo 906576 1360733 := bbase (se 3 (by rfl) ⟨255137, by rfl⟩ : syracuseStep 1360733 = 510275) (by norm_num)
theorem B2040677 : Blo 906576 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B1147765 : Blo 906576 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1360757 : Blo 906576 1360757 := bbase (se 5 (by rfl) ⟨63785, by rfl⟩ : syracuseStep 1360757 = 127571) (by norm_num)
theorem B1360781 : Blo 906576 1360781 := bbase (se 3 (by rfl) ⟨255146, by rfl⟩ : syracuseStep 1360781 = 510293) (by norm_num)
theorem B3449749 : Blo 906576 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B1721245 : Blo 906576 1721245 := bbase (se 3 (by rfl) ⟨322733, by rfl⟩ : syracuseStep 1721245 = 645467) (by norm_num)
theorem B1360805 : Blo 906576 1360805 := bbase (se 4 (by rfl) ⟨127575, by rfl⟩ : syracuseStep 1360805 = 255151) (by norm_num)
theorem B1532837 : Blo 906576 1532837 := bbase (se 4 (by rfl) ⟨143703, by rfl⟩ : syracuseStep 1532837 = 287407) (by norm_num)
theorem B2040749 : Blo 906576 2040749 := bbase (se 3 (by rfl) ⟨382640, by rfl⟩ : syracuseStep 2040749 = 765281) (by norm_num)
theorem B1360829 : Blo 906576 1360829 := bbase (se 3 (by rfl) ⟨255155, by rfl⟩ : syracuseStep 1360829 = 510311) (by norm_num)
theorem B1147861 : Blo 906576 1147861 := bbase (se 7 (by rfl) ⟨13451, by rfl⟩ : syracuseStep 1147861 = 26903) (by norm_num)
theorem B1360853 : Blo 906576 1360853 := bbase (se 7 (by rfl) ⟨15947, by rfl⟩ : syracuseStep 1360853 = 31895) (by norm_num)
theorem B1360877 : Blo 906576 1360877 := bbase (se 3 (by rfl) ⟨255164, by rfl⟩ : syracuseStep 1360877 = 510329) (by norm_num)
theorem B2040821 : Blo 906576 2040821 := bbase (se 5 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 2040821 = 191327) (by norm_num)
theorem B1360901 : Blo 906576 1360901 := bbase (se 4 (by rfl) ⟨127584, by rfl⟩ : syracuseStep 1360901 = 255169) (by norm_num)
theorem B2909189 : Blo 906576 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B3679253 : Blo 906576 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B1360925 : Blo 906576 1360925 := bbase (se 3 (by rfl) ⟨255173, by rfl⟩ : syracuseStep 1360925 = 510347) (by norm_num)
theorem B1532965 : Blo 906576 1532965 := bbase (se 4 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 1532965 = 287431) (by norm_num)
theorem B1360949 : Blo 906576 1360949 := bbase (se 5 (by rfl) ⟨63794, by rfl⟩ : syracuseStep 1360949 = 127589) (by norm_num)
theorem B5170229 : Blo 906576 5170229 := bbase (se 5 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 5170229 = 484709) (by norm_num)
theorem B1721405 : Blo 906576 1721405 := bbase (se 3 (by rfl) ⟨322763, by rfl⟩ : syracuseStep 1721405 = 645527) (by norm_num)
theorem B2040893 : Blo 906576 2040893 := bbase (se 3 (by rfl) ⟨382667, by rfl⟩ : syracuseStep 2040893 = 765335) (by norm_num)
theorem B1360973 : Blo 906576 1360973 := bbase (se 3 (by rfl) ⟨255182, by rfl⟩ : syracuseStep 1360973 = 510365) (by norm_num)
theorem B1360997 : Blo 906576 1360997 := bbase (se 4 (by rfl) ⟨127593, by rfl⟩ : syracuseStep 1360997 = 255187) (by norm_num)
theorem B1361021 : Blo 906576 1361021 := bbase (se 3 (by rfl) ⟨255191, by rfl⟩ : syracuseStep 1361021 = 510383) (by norm_num)
theorem B1533053 : Blo 906576 1533053 := bbase (se 3 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 1533053 = 574895) (by norm_num)
theorem B1148033 : Blo 906576 1148033 := bbase (se 2 (by rfl) ⟨430512, by rfl⟩ : syracuseStep 1148033 = 861025) (by norm_num)
theorem B2040965 : Blo 906576 2040965 := bbase (se 4 (by rfl) ⟨191340, by rfl⟩ : syracuseStep 2040965 = 382681) (by norm_num)
theorem B1361045 : Blo 906576 1361045 := bbase (se 6 (by rfl) ⟨31899, by rfl⟩ : syracuseStep 1361045 = 63799) (by norm_num)
theorem B1746085 : Blo 906576 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B1361069 : Blo 906576 1361069 := bbase (se 3 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 1361069 = 510401) (by norm_num)
theorem B1148089 : Blo 906576 1148089 := bbase (se 2 (by rfl) ⟨430533, by rfl⟩ : syracuseStep 1148089 = 861067) (by norm_num)
theorem B4359365 : Blo 906576 4359365 := bbase (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) (by norm_num)
theorem B1361093 : Blo 906576 1361093 := bbase (se 4 (by rfl) ⟨127602, by rfl⟩ : syracuseStep 1361093 = 255205) (by norm_num)
theorem B1721549 : Blo 906576 1721549 := bbase (se 3 (by rfl) ⟨322790, by rfl⟩ : syracuseStep 1721549 = 645581) (by norm_num)
theorem B2041037 : Blo 906576 2041037 := bbase (se 3 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 2041037 = 765389) (by norm_num)
theorem B5817557 : Blo 906576 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B1361117 : Blo 906576 1361117 := bbase (se 3 (by rfl) ⟨255209, by rfl⟩ : syracuseStep 1361117 = 510419) (by norm_num)
theorem B2295013 : Blo 906576 2295013 := bbase (se 4 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 2295013 = 430315) (by norm_num)
theorem B1361141 : Blo 906576 1361141 := bbase (se 5 (by rfl) ⟨63803, by rfl⟩ : syracuseStep 1361141 = 127607) (by norm_num)
theorem B1533181 : Blo 906576 1533181 := bbase (se 3 (by rfl) ⟨287471, by rfl⟩ : syracuseStep 1533181 = 574943) (by norm_num)
theorem B3065093 : Blo 906576 3065093 := bbase (se 4 (by rfl) ⟨287352, by rfl⟩ : syracuseStep 3065093 = 574705) (by norm_num)
theorem B1361165 : Blo 906576 1361165 := bbase (se 3 (by rfl) ⟨255218, by rfl⟩ : syracuseStep 1361165 = 510437) (by norm_num)
theorem B2041109 : Blo 906576 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B1148185 : Blo 906576 1148185 := bbase (se 2 (by rfl) ⟨430569, by rfl⟩ : syracuseStep 1148185 = 861139) (by norm_num)
theorem B1361189 : Blo 906576 1361189 := bbase (se 4 (by rfl) ⟨127611, by rfl⟩ : syracuseStep 1361189 = 255223) (by norm_num)
theorem B1090865 : Blo 906576 1090865 := bbase (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) (by norm_num)
theorem B1361213 : Blo 906576 1361213 := bbase (se 3 (by rfl) ⟨255227, by rfl⟩ : syracuseStep 1361213 = 510455) (by norm_num)
theorem B2295125 : Blo 906576 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B1361237 : Blo 906576 1361237 := bbase (se 12 (by rfl) ⟨498, by rfl⟩ : syracuseStep 1361237 = 997) (by norm_num)
theorem B2041181 : Blo 906576 2041181 := bbase (se 3 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 2041181 = 765443) (by norm_num)
theorem B1361261 : Blo 906576 1361261 := bbase (se 3 (by rfl) ⟨255236, by rfl⟩ : syracuseStep 1361261 = 510473) (by norm_num)
theorem B1361285 : Blo 906576 1361285 := bbase (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) (by norm_num)
theorem B1361309 : Blo 906576 1361309 := bbase (se 3 (by rfl) ⟨255245, by rfl⟩ : syracuseStep 1361309 = 510491) (by norm_num)
theorem B2041253 : Blo 906576 2041253 := bbase (se 4 (by rfl) ⟨191367, by rfl⟩ : syracuseStep 2041253 = 382735) (by norm_num)
theorem B1361333 : Blo 906576 1361333 := bbase (se 5 (by rfl) ⟨63812, by rfl⟩ : syracuseStep 1361333 = 127625) (by norm_num)
theorem B1148357 : Blo 906576 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B1361357 : Blo 906576 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B1361381 : Blo 906576 1361381 := bbase (se 4 (by rfl) ⟨127629, by rfl⟩ : syracuseStep 1361381 = 255259) (by norm_num)
theorem B1721837 : Blo 906576 1721837 := bbase (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) (by norm_num)
theorem B2041325 : Blo 906576 2041325 := bbase (se 3 (by rfl) ⟨382748, by rfl⟩ : syracuseStep 2041325 = 765497) (by norm_num)
theorem B1148413 : Blo 906576 1148413 := bbase (se 3 (by rfl) ⟨215327, by rfl⟩ : syracuseStep 1148413 = 430655) (by norm_num)
theorem B1361405 : Blo 906576 1361405 := bbase (se 3 (by rfl) ⟨255263, by rfl⟩ : syracuseStep 1361405 = 510527) (by norm_num)
theorem B2295317 : Blo 906576 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B1361429 : Blo 906576 1361429 := bbase (se 6 (by rfl) ⟨31908, by rfl⟩ : syracuseStep 1361429 = 63817) (by norm_num)
theorem B1361453 : Blo 906576 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B2041397 : Blo 906576 2041397 := bbase (se 5 (by rfl) ⟨95690, by rfl⟩ : syracuseStep 2041397 = 191381) (by norm_num)
theorem B1361477 : Blo 906576 1361477 := bbase (se 4 (by rfl) ⟨127638, by rfl⟩ : syracuseStep 1361477 = 255277) (by norm_num)
theorem B968269 : Blo 906576 968269 := bbase (se 3 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 968269 = 363101) (by norm_num)
theorem B1148509 : Blo 906576 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1361501 : Blo 906576 1361501 := bbase (se 3 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 1361501 = 510563) (by norm_num)
theorem B3442277 : Blo 906576 3442277 := bbase (se 4 (by rfl) ⟨322713, by rfl⟩ : syracuseStep 3442277 = 645427) (by norm_num)
theorem B1091173 : Blo 906576 1091173 := bbase (se 4 (by rfl) ⟨102297, by rfl⟩ : syracuseStep 1091173 = 204595) (by norm_num)
theorem B1033841 : Blo 906576 1033841 := bbase (se 2 (by rfl) ⟨387690, by rfl⟩ : syracuseStep 1033841 = 775381) (by norm_num)
theorem B1361525 : Blo 906576 1361525 := bbase (se 5 (by rfl) ⟨63821, by rfl⟩ : syracuseStep 1361525 = 127643) (by norm_num)
theorem B3106421 : Blo 906576 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2041469 : Blo 906576 2041469 := bbase (se 3 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 2041469 = 765551) (by norm_num)
theorem B1721989 : Blo 906576 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B1361549 : Blo 906576 1361549 := bbase (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) (by norm_num)
theorem B4597397 : Blo 906576 4597397 := bbase (se 6 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 4597397 = 215503) (by norm_num)
theorem B1361573 : Blo 906576 1361573 := bbase (se 4 (by rfl) ⟨127647, by rfl⟩ : syracuseStep 1361573 = 255295) (by norm_num)
theorem B3065525 : Blo 906576 3065525 := bbase (se 5 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 3065525 = 287393) (by norm_num)
theorem B1361597 : Blo 906576 1361597 := bbase (se 3 (by rfl) ⟨255299, by rfl⟩ : syracuseStep 1361597 = 510599) (by norm_num)
theorem B2041541 : Blo 906576 2041541 := bbase (se 4 (by rfl) ⟨191394, by rfl⟩ : syracuseStep 2041541 = 382789) (by norm_num)
theorem B968393 : Blo 906576 968393 := bbase (se 2 (by rfl) ⟨363147, by rfl⟩ : syracuseStep 968393 = 726295) (by norm_num)
theorem B919253 : Blo 906576 919253 := bbase (se 7 (by rfl) ⟨10772, by rfl⟩ : syracuseStep 919253 = 21545) (by norm_num)
theorem B1361621 : Blo 906576 1361621 := bbase (se 7 (by rfl) ⟨15956, by rfl⟩ : syracuseStep 1361621 = 31913) (by norm_num)
theorem B3106517 : Blo 906576 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B1361645 : Blo 906576 1361645 := bbase (se 3 (by rfl) ⟨255308, by rfl⟩ : syracuseStep 1361645 = 510617) (by norm_num)
theorem B1361669 : Blo 906576 1361669 := bbase (se 4 (by rfl) ⟨127656, by rfl⟩ : syracuseStep 1361669 = 255313) (by norm_num)
theorem B1148681 : Blo 906576 1148681 := bbase (se 2 (by rfl) ⟨430755, by rfl⟩ : syracuseStep 1148681 = 861511) (by norm_num)
theorem B2041613 : Blo 906576 2041613 := bbase (se 3 (by rfl) ⟨382802, by rfl⟩ : syracuseStep 2041613 = 765605) (by norm_num)
theorem B1361693 : Blo 906576 1361693 := bbase (se 3 (by rfl) ⟨255317, by rfl⟩ : syracuseStep 1361693 = 510635) (by norm_num)
theorem B1361717 : Blo 906576 1361717 := bbase (se 5 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 1361717 = 127661) (by norm_num)
theorem B1148737 : Blo 906576 1148737 := bbase (se 2 (by rfl) ⟨430776, by rfl⟩ : syracuseStep 1148737 = 861553) (by norm_num)
theorem B1361741 : Blo 906576 1361741 := bbase (se 3 (by rfl) ⟨255326, by rfl⟩ : syracuseStep 1361741 = 510653) (by norm_num)
theorem B2041685 : Blo 906576 2041685 := bbase (se 9 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 2041685 = 11963) (by norm_num)
theorem B1361765 : Blo 906576 1361765 := bbase (se 4 (by rfl) ⟨127665, by rfl⟩ : syracuseStep 1361765 = 255331) (by norm_num)
theorem B2295661 : Blo 906576 2295661 := bbase (se 3 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 2295661 = 860873) (by norm_num)
theorem B1361789 : Blo 906576 1361789 := bbase (se 3 (by rfl) ⟨255335, by rfl⟩ : syracuseStep 1361789 = 510671) (by norm_num)
theorem B1361813 : Blo 906576 1361813 := bbase (se 6 (by rfl) ⟨31917, by rfl⟩ : syracuseStep 1361813 = 63835) (by norm_num)
theorem B2041757 : Blo 906576 2041757 := bbase (se 3 (by rfl) ⟨382829, by rfl⟩ : syracuseStep 2041757 = 765659) (by norm_num)
theorem B1148833 : Blo 906576 1148833 := bbase (se 2 (by rfl) ⟨430812, by rfl⟩ : syracuseStep 1148833 = 861625) (by norm_num)
theorem B2582437 : Blo 906576 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B1361837 : Blo 906576 1361837 := bbase (se 3 (by rfl) ⟨255344, by rfl⟩ : syracuseStep 1361837 = 510689) (by norm_num)
theorem B1722293 : Blo 906576 1722293 := bbase (se 5 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 1722293 = 161465) (by norm_num)
theorem B1574845 : Blo 906576 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B968645 : Blo 906576 968645 := bbase (se 4 (by rfl) ⟨90810, by rfl⟩ : syracuseStep 968645 = 181621) (by norm_num)
theorem B1361861 : Blo 906576 1361861 := bbase (se 4 (by rfl) ⟨127674, by rfl⟩ : syracuseStep 1361861 = 255349) (by norm_num)
theorem B919513 : Blo 906576 919513 := bbase (se 2 (by rfl) ⟨344817, by rfl⟩ : syracuseStep 919513 = 689635) (by norm_num)
theorem B2295773 : Blo 906576 2295773 := bbase (se 3 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 2295773 = 860915) (by norm_num)
theorem B1361885 : Blo 906576 1361885 := bbase (se 3 (by rfl) ⟨255353, by rfl⟩ : syracuseStep 1361885 = 510707) (by norm_num)
theorem B2041829 : Blo 906576 2041829 := bbase (se 4 (by rfl) ⟨191421, by rfl⟩ : syracuseStep 2041829 = 382843) (by norm_num)
theorem B1361909 : Blo 906576 1361909 := bbase (se 5 (by rfl) ⟨63839, by rfl⟩ : syracuseStep 1361909 = 127679) (by norm_num)
theorem B1361933 : Blo 906576 1361933 := bbase (se 3 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 1361933 = 510725) (by norm_num)
theorem B1361957 : Blo 906576 1361957 := bbase (se 4 (by rfl) ⟨127683, by rfl⟩ : syracuseStep 1361957 = 255367) (by norm_num)
theorem B2041901 : Blo 906576 2041901 := bbase (se 3 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 2041901 = 765713) (by norm_num)
theorem B4589621 : Blo 906576 4589621 := bbase (se 5 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 4589621 = 430277) (by norm_num)
theorem B1361981 : Blo 906576 1361981 := bbase (se 3 (by rfl) ⟨255371, by rfl⟩ : syracuseStep 1361981 = 510743) (by norm_num)
theorem B2582597 : Blo 906576 2582597 := bbase (se 4 (by rfl) ⟨242118, by rfl⟩ : syracuseStep 2582597 = 484237) (by norm_num)
theorem B1149005 : Blo 906576 1149005 := bbase (se 3 (by rfl) ⟨215438, by rfl⟩ : syracuseStep 1149005 = 430877) (by norm_num)
theorem B1362005 : Blo 906576 1362005 := bbase (se 8 (by rfl) ⟨7980, by rfl⟩ : syracuseStep 1362005 = 15961) (by norm_num)
theorem B3065957 : Blo 906576 3065957 := bbase (se 4 (by rfl) ⟨287433, by rfl⟩ : syracuseStep 3065957 = 574867) (by norm_num)
theorem B1362029 : Blo 906576 1362029 := bbase (se 3 (by rfl) ⟨255380, by rfl⟩ : syracuseStep 1362029 = 510761) (by norm_num)
theorem B2041973 : Blo 906576 2041973 := bbase (se 5 (by rfl) ⟨95717, by rfl⟩ : syracuseStep 2041973 = 191435) (by norm_num)
theorem B1149061 : Blo 906576 1149061 := bbase (se 4 (by rfl) ⟨107724, by rfl⟩ : syracuseStep 1149061 = 215449) (by norm_num)
theorem B1362053 : Blo 906576 1362053 := bbase (se 4 (by rfl) ⟨127692, by rfl⟩ : syracuseStep 1362053 = 255385) (by norm_num)
theorem B2295965 : Blo 906576 2295965 := bbase (se 3 (by rfl) ⟨430493, by rfl⟩ : syracuseStep 2295965 = 860987) (by norm_num)
theorem B1362077 : Blo 906576 1362077 := bbase (se 3 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 1362077 = 510779) (by norm_num)
theorem B1747117 : Blo 906576 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B1362101 : Blo 906576 1362101 := bbase (se 5 (by rfl) ⟨63848, by rfl⟩ : syracuseStep 1362101 = 127697) (by norm_num)
theorem B2042045 : Blo 906576 2042045 := bbase (se 3 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 2042045 = 765767) (by norm_num)
theorem B1362125 : Blo 906576 1362125 := bbase (se 3 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 1362125 = 510797) (by norm_num)
theorem B1149157 : Blo 906576 1149157 := bbase (se 4 (by rfl) ⟨107733, by rfl⟩ : syracuseStep 1149157 = 215467) (by norm_num)
theorem B1362149 : Blo 906576 1362149 := bbase (se 4 (by rfl) ⟨127701, by rfl⟩ : syracuseStep 1362149 = 255403) (by norm_num)
theorem B1362173 : Blo 906576 1362173 := bbase (se 3 (by rfl) ⟨255407, by rfl⟩ : syracuseStep 1362173 = 510815) (by norm_num)
theorem B2042117 : Blo 906576 2042117 := bbase (se 4 (by rfl) ⟨191448, by rfl⟩ : syracuseStep 2042117 = 382897) (by norm_num)
theorem B3877141 : Blo 906576 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B1362197 : Blo 906576 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B1362221 : Blo 906576 1362221 := bbase (se 3 (by rfl) ⟨255416, by rfl⟩ : syracuseStep 1362221 = 510833) (by norm_num)
theorem B2582837 : Blo 906576 2582837 := bbase (se 5 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 2582837 = 242141) (by norm_num)
theorem B3680581 : Blo 906576 3680581 := bbase (se 4 (by rfl) ⟨345054, by rfl⟩ : syracuseStep 3680581 = 690109) (by norm_num)
theorem B1362245 : Blo 906576 1362245 := bbase (se 4 (by rfl) ⟨127710, by rfl⟩ : syracuseStep 1362245 = 255421) (by norm_num)
theorem B2042189 : Blo 906576 2042189 := bbase (se 3 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 2042189 = 765821) (by norm_num)
theorem B1362269 : Blo 906576 1362269 := bbase (se 3 (by rfl) ⟨255425, by rfl⟩ : syracuseStep 1362269 = 510851) (by norm_num)
theorem B1362293 : Blo 906576 1362293 := bbase (se 5 (by rfl) ⟨63857, by rfl⟩ : syracuseStep 1362293 = 127715) (by norm_num)
theorem B969089 : Blo 906576 969089 := bbase (se 2 (by rfl) ⟨363408, by rfl⟩ : syracuseStep 969089 = 726817) (by norm_num)
theorem B1362317 : Blo 906576 1362317 := bbase (se 3 (by rfl) ⟨255434, by rfl⟩ : syracuseStep 1362317 = 510869) (by norm_num)
theorem B1149329 : Blo 906576 1149329 := bbase (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) (by norm_num)
theorem B2042261 : Blo 906576 2042261 := bbase (se 6 (by rfl) ⟨47865, by rfl⟩ : syracuseStep 2042261 = 95731) (by norm_num)
theorem B2910613 : Blo 906576 2910613 := bbase (se 6 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 2910613 = 136435) (by norm_num)
theorem B1362341 : Blo 906576 1362341 := bbase (se 4 (by rfl) ⟨127719, by rfl⟩ : syracuseStep 1362341 = 255439) (by norm_num)
theorem B1362365 : Blo 906576 1362365 := bbase (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) (by norm_num)
theorem B1149385 : Blo 906576 1149385 := bbase (se 2 (by rfl) ⟨431019, by rfl⟩ : syracuseStep 1149385 = 862039) (by norm_num)
theorem B1452493 : Blo 906576 1452493 := bbase (se 3 (by rfl) ⟨272342, by rfl⟩ : syracuseStep 1452493 = 544685) (by norm_num)
theorem B1362389 : Blo 906576 1362389 := bbase (se 7 (by rfl) ⟨15965, by rfl⟩ : syracuseStep 1362389 = 31931) (by norm_num)
theorem B2042333 : Blo 906576 2042333 := bbase (se 3 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 2042333 = 765875) (by norm_num)
theorem B1362413 : Blo 906576 1362413 := bbase (se 3 (by rfl) ⟨255452, by rfl⟩ : syracuseStep 1362413 = 510905) (by norm_num)
theorem B2583029 : Blo 906576 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B2296309 : Blo 906576 2296309 := bbase (se 5 (by rfl) ⟨107639, by rfl⟩ : syracuseStep 2296309 = 215279) (by norm_num)
theorem B1362437 : Blo 906576 1362437 := bbase (se 4 (by rfl) ⟨127728, by rfl⟩ : syracuseStep 1362437 = 255457) (by norm_num)
theorem B3066389 : Blo 906576 3066389 := bbase (se 6 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 3066389 = 143737) (by norm_num)
theorem B1362461 : Blo 906576 1362461 := bbase (se 3 (by rfl) ⟨255461, by rfl⟩ : syracuseStep 1362461 = 510923) (by norm_num)
theorem B2042405 : Blo 906576 2042405 := bbase (se 4 (by rfl) ⟨191475, by rfl⟩ : syracuseStep 2042405 = 382951) (by norm_num)
theorem B1149481 : Blo 906576 1149481 := bbase (se 2 (by rfl) ⟨431055, by rfl⟩ : syracuseStep 1149481 = 862111) (by norm_num)
theorem B1362485 : Blo 906576 1362485 := bbase (se 5 (by rfl) ⟨63866, by rfl⟩ : syracuseStep 1362485 = 127733) (by norm_num)
theorem B920129 : Blo 906576 920129 := bbase (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) (by norm_num)
theorem B1362509 : Blo 906576 1362509 := bbase (se 3 (by rfl) ⟨255470, by rfl⟩ : syracuseStep 1362509 = 510941) (by norm_num)
theorem B2296421 : Blo 906576 2296421 := bbase (se 4 (by rfl) ⟨215289, by rfl⟩ : syracuseStep 2296421 = 430579) (by norm_num)
theorem B1362533 : Blo 906576 1362533 := bbase (se 4 (by rfl) ⟨127737, by rfl⟩ : syracuseStep 1362533 = 255475) (by norm_num)
theorem B2042477 : Blo 906576 2042477 := bbase (se 3 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 2042477 = 765929) (by norm_num)
theorem B969337 : Blo 906576 969337 := bbase (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) (by norm_num)
theorem B1362557 : Blo 906576 1362557 := bbase (se 3 (by rfl) ⟨255479, by rfl⟩ : syracuseStep 1362557 = 510959) (by norm_num)
theorem B1362581 : Blo 906576 1362581 := bbase (se 6 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 1362581 = 63871) (by norm_num)
theorem B1723045 : Blo 906576 1723045 := bbase (se 4 (by rfl) ⟨161535, by rfl⟩ : syracuseStep 1723045 = 323071) (by norm_num)
theorem B1362605 : Blo 906576 1362605 := bbase (se 3 (by rfl) ⟨255488, by rfl⟩ : syracuseStep 1362605 = 510977) (by norm_num)
theorem B2042549 : Blo 906576 2042549 := bbase (se 5 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 2042549 = 191489) (by norm_num)
theorem B1362629 : Blo 906576 1362629 := bbase (se 4 (by rfl) ⟨127746, by rfl⟩ : syracuseStep 1362629 = 255493) (by norm_num)
theorem B1452749 : Blo 906576 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B1149653 : Blo 906576 1149653 := bbase (se 7 (by rfl) ⟨13472, by rfl⟩ : syracuseStep 1149653 = 26945) (by norm_num)
theorem B1362653 : Blo 906576 1362653 := bbase (se 3 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 1362653 = 510995) (by norm_num)
theorem B1362677 : Blo 906576 1362677 := bbase (se 5 (by rfl) ⟨63875, by rfl⟩ : syracuseStep 1362677 = 127751) (by norm_num)
theorem B2042621 : Blo 906576 2042621 := bbase (se 3 (by rfl) ⟨382991, by rfl⟩ : syracuseStep 2042621 = 765983) (by norm_num)
theorem B1149709 : Blo 906576 1149709 := bbase (se 3 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 1149709 = 431141) (by norm_num)
theorem B1362701 : Blo 906576 1362701 := bbase (se 3 (by rfl) ⟨255506, by rfl⟩ : syracuseStep 1362701 = 511013) (by norm_num)
theorem B2296613 : Blo 906576 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B1362725 : Blo 906576 1362725 := bbase (se 4 (by rfl) ⟨127755, by rfl⟩ : syracuseStep 1362725 = 255511) (by norm_num)
theorem B1723189 : Blo 906576 1723189 := bbase (se 5 (by rfl) ⟨80774, by rfl⟩ : syracuseStep 1723189 = 161549) (by norm_num)
theorem B1362749 : Blo 906576 1362749 := bbase (se 3 (by rfl) ⟨255515, by rfl⟩ : syracuseStep 1362749 = 511031) (by norm_num)
theorem B2042693 : Blo 906576 2042693 := bbase (se 4 (by rfl) ⟨191502, by rfl⟩ : syracuseStep 2042693 = 383005) (by norm_num)
theorem B23554901 : Blo 906576 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B2796373 : Blo 906576 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B1362773 : Blo 906576 1362773 := bbase (se 9 (by rfl) ⟨3992, by rfl⟩ : syracuseStep 1362773 = 7985) (by norm_num)
theorem B1035109 : Blo 906576 1035109 := bbase (se 4 (by rfl) ⟨97041, by rfl⟩ : syracuseStep 1035109 = 194083) (by norm_num)
theorem B1149805 : Blo 906576 1149805 := bbase (se 3 (by rfl) ⟨215588, by rfl⟩ : syracuseStep 1149805 = 431177) (by norm_num)
theorem B1362797 : Blo 906576 1362797 := bbase (se 3 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 1362797 = 511049) (by norm_num)
theorem B1362821 : Blo 906576 1362821 := bbase (se 4 (by rfl) ⟨127764, by rfl⟩ : syracuseStep 1362821 = 255529) (by norm_num)
theorem B2042765 : Blo 906576 2042765 := bbase (se 3 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 2042765 = 766037) (by norm_num)
theorem B1362845 : Blo 906576 1362845 := bbase (se 3 (by rfl) ⟨255533, by rfl⟩ : syracuseStep 1362845 = 511067) (by norm_num)
theorem B4598693 : Blo 906576 4598693 := bbase (se 4 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 4598693 = 862255) (by norm_num)
theorem B1723349 : Blo 906576 1723349 := bbase (se 7 (by rfl) ⟨20195, by rfl⟩ : syracuseStep 1723349 = 40391) (by norm_num)
theorem B2042837 : Blo 906576 2042837 := bbase (se 7 (by rfl) ⟨23939, by rfl⟩ : syracuseStep 2042837 = 47879) (by norm_num)
theorem B2042909 : Blo 906576 2042909 := bbase (se 3 (by rfl) ⟨383045, by rfl⟩ : syracuseStep 2042909 = 766091) (by norm_num)
theorem B1838117 : Blo 906576 1838117 := bbase (se 4 (by rfl) ⟨172323, by rfl⟩ : syracuseStep 1838117 = 344647) (by norm_num)
theorem B969781 : Blo 906576 969781 := bbase (se 5 (by rfl) ⟨45458, by rfl⟩ : syracuseStep 969781 = 90917) (by norm_num)
theorem B1723493 : Blo 906576 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B2042981 : Blo 906576 2042981 := bbase (se 4 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 2042981 = 383059) (by norm_num)
theorem B969841 : Blo 906576 969841 := bbase (se 2 (by rfl) ⟨363690, by rfl⟩ : syracuseStep 969841 = 727381) (by norm_num)
theorem B2296957 : Blo 906576 2296957 := bbase (se 3 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 2296957 = 861359) (by norm_num)
theorem B2182277 : Blo 906576 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B2043053 : Blo 906576 2043053 := bbase (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) (by norm_num)
theorem B5172437 : Blo 906576 5172437 := bbase (se 7 (by rfl) ⟨60614, by rfl⟩ : syracuseStep 5172437 = 121229) (by norm_num)
theorem B2297069 : Blo 906576 2297069 := bbase (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) (by norm_num)
theorem B2043125 : Blo 906576 2043125 := bbase (se 5 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 2043125 = 191543) (by norm_num)
theorem B1551637 : Blo 906576 1551637 := bbase (se 6 (by rfl) ⟨36366, by rfl⟩ : syracuseStep 1551637 = 72733) (by norm_num)
theorem B2182421 : Blo 906576 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B6548789 : Blo 906576 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B2043197 : Blo 906576 2043197 := bbase (se 3 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 2043197 = 766199) (by norm_num)
theorem B4590917 : Blo 906576 4590917 := bbase (se 4 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 4590917 = 860797) (by norm_num)
theorem B1723781 : Blo 906576 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B2043269 : Blo 906576 2043269 := bbase (se 4 (by rfl) ⟨191556, by rfl⟩ : syracuseStep 2043269 = 383113) (by norm_num)
theorem B2297261 : Blo 906576 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B970157 : Blo 906576 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B2043341 : Blo 906576 2043341 := bbase (se 3 (by rfl) ⟨383126, by rfl⟩ : syracuseStep 2043341 = 766253) (by norm_num)
theorem B2584021 : Blo 906576 2584021 := bbase (se 7 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 2584021 = 60563) (by norm_num)
theorem B2797061 : Blo 906576 2797061 := bbase (se 4 (by rfl) ⟨262224, by rfl⟩ : syracuseStep 2797061 = 524449) (by norm_num)
theorem B2043413 : Blo 906576 2043413 := bbase (se 6 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 2043413 = 95785) (by norm_num)
theorem B1723933 : Blo 906576 1723933 := bbase (se 3 (by rfl) ⟨323237, by rfl⟩ : syracuseStep 1723933 = 646475) (by norm_num)
theorem B1453621 : Blo 906576 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B2043485 : Blo 906576 2043485 := bbase (se 3 (by rfl) ⟨383153, by rfl⟩ : syracuseStep 2043485 = 766307) (by norm_num)
theorem B2944613 : Blo 906576 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B8728181 : Blo 906576 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B1453717 : Blo 906576 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B3444389 : Blo 906576 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B2043557 : Blo 906576 2043557 := bbase (se 4 (by rfl) ⟨191583, by rfl⟩ : syracuseStep 2043557 = 383167) (by norm_num)
theorem B5516981 : Blo 906576 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B4140725 : Blo 906576 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B4419269 : Blo 906576 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B2330309 : Blo 906576 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B1633997 : Blo 906576 1633997 := bbase (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) (by norm_num)
theorem B1035985 : Blo 906576 1035985 := bbase (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) (by norm_num)
theorem B2043629 : Blo 906576 2043629 := bbase (se 3 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 2043629 = 766361) (by norm_num)
theorem B2297605 : Blo 906576 2297605 := bbase (se 4 (by rfl) ⟨215400, by rfl⟩ : syracuseStep 2297605 = 430801) (by norm_num)
theorem B2838277 : Blo 906576 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B1453877 : Blo 906576 1453877 := bbase (se 5 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 1453877 = 136301) (by norm_num)
theorem B2043701 : Blo 906576 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1724237 : Blo 906576 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B2297717 : Blo 906576 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B2043773 : Blo 906576 2043773 := bbase (se 3 (by rfl) ⟨383207, by rfl⟩ : syracuseStep 2043773 = 766415) (by norm_num)
theorem B1937333 : Blo 906576 1937333 := bbase (se 5 (by rfl) ⟨90812, by rfl⟩ : syracuseStep 1937333 = 181625) (by norm_num)
theorem B3444677 : Blo 906576 3444677 := bbase (se 4 (by rfl) ⟨322938, by rfl⟩ : syracuseStep 3444677 = 645877) (by norm_num)
theorem B2043845 : Blo 906576 2043845 := bbase (se 4 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 2043845 = 383221) (by norm_num)
theorem B2043917 : Blo 906576 2043917 := bbase (se 3 (by rfl) ⟨383234, by rfl⟩ : syracuseStep 2043917 = 766469) (by norm_num)
theorem B1019929 : Blo 906576 1019929 := bbase (se 2 (by rfl) ⟨382473, by rfl⟩ : syracuseStep 1019929 = 764947) (by norm_num)
theorem B2297909 : Blo 906576 2297909 := bbase (se 5 (by rfl) ⟨107714, by rfl⟩ : syracuseStep 2297909 = 215429) (by norm_num)
theorem B1019965 : Blo 906576 1019965 := bbase (se 3 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 1019965 = 382487) (by norm_num)
theorem B1380413 : Blo 906576 1380413 := bbase (se 3 (by rfl) ⟨258827, by rfl⟩ : syracuseStep 1380413 = 517655) (by norm_num)
theorem B1937477 : Blo 906576 1937477 := bbase (se 4 (by rfl) ⟨181638, by rfl⟩ : syracuseStep 1937477 = 363277) (by norm_num)
theorem B2043989 : Blo 906576 2043989 := bbase (se 8 (by rfl) ⟨11976, by rfl⟩ : syracuseStep 2043989 = 23953) (by norm_num)
theorem B1020001 : Blo 906576 1020001 := bbase (se 2 (by rfl) ⟨382500, by rfl⟩ : syracuseStep 1020001 = 765001) (by norm_num)
theorem B1863805 : Blo 906576 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B1020037 : Blo 906576 1020037 := bbase (se 4 (by rfl) ⟨95628, by rfl⟩ : syracuseStep 1020037 = 191257) (by norm_num)
theorem B2044061 : Blo 906576 2044061 := bbase (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) (by norm_num)
theorem B1020073 : Blo 906576 1020073 := bbase (se 2 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 1020073 = 765055) (by norm_num)
theorem B4657333 : Blo 906576 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B3059909 : Blo 906576 3059909 := bbase (se 4 (by rfl) ⟨286866, by rfl⟩ : syracuseStep 3059909 = 573733) (by norm_num)
theorem B1020109 : Blo 906576 1020109 := bbase (se 3 (by rfl) ⟨191270, by rfl⟩ : syracuseStep 1020109 = 382541) (by norm_num)
theorem B2044133 : Blo 906576 2044133 := bbase (se 4 (by rfl) ⟨191637, by rfl⟩ : syracuseStep 2044133 = 383275) (by norm_num)
theorem B1020145 : Blo 906576 1020145 := bbase (se 2 (by rfl) ⟨382554, by rfl⟩ : syracuseStep 1020145 = 765109) (by norm_num)
theorem B1020181 : Blo 906576 1020181 := bbase (se 6 (by rfl) ⟨23910, by rfl⟩ : syracuseStep 1020181 = 47821) (by norm_num)
theorem B2044205 : Blo 906576 2044205 := bbase (se 3 (by rfl) ⟨383288, by rfl⟩ : syracuseStep 2044205 = 766577) (by norm_num)
theorem B1020217 : Blo 906576 1020217 := bbase (se 2 (by rfl) ⟨382581, by rfl⟩ : syracuseStep 1020217 = 765163) (by norm_num)
theorem B6893909 : Blo 906576 6893909 := bbase (se 10 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 6893909 = 20197) (by norm_num)
theorem B1020253 : Blo 906576 1020253 := bbase (se 3 (by rfl) ⟨191297, by rfl⟩ : syracuseStep 1020253 = 382595) (by norm_num)
theorem B995689 : Blo 906576 995689 := bbase (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) (by norm_num)
theorem B9318773 : Blo 906576 9318773 := bbase (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) (by norm_num)
theorem B2044277 : Blo 906576 2044277 := bbase (se 5 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 2044277 = 191651) (by norm_num)
theorem B1020289 : Blo 906576 1020289 := bbase (se 2 (by rfl) ⟨382608, by rfl⟩ : syracuseStep 1020289 = 765217) (by norm_num)
theorem B2298253 : Blo 906576 2298253 := bbase (se 3 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 2298253 = 861845) (by norm_num)
theorem B1020325 : Blo 906576 1020325 := bbase (se 4 (by rfl) ⟨95655, by rfl⟩ : syracuseStep 1020325 = 191311) (by norm_num)
theorem B1937837 : Blo 906576 1937837 := bbase (se 3 (by rfl) ⟨363344, by rfl⟩ : syracuseStep 1937837 = 726689) (by norm_num)
theorem B1020361 : Blo 906576 1020361 := bbase (se 2 (by rfl) ⟨382635, by rfl⟩ : syracuseStep 1020361 = 765271) (by norm_num)
theorem B1020397 : Blo 906576 1020397 := bbase (se 3 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 1020397 = 382649) (by norm_num)
theorem B2298365 : Blo 906576 2298365 := bbase (se 3 (by rfl) ⟨430943, by rfl⟩ : syracuseStep 2298365 = 861887) (by norm_num)
theorem B1020433 : Blo 906576 1020433 := bbase (se 2 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 1020433 = 765325) (by norm_num)
theorem B11637269 : Blo 906576 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B2585125 : Blo 906576 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B3682853 : Blo 906576 3682853 := bbase (se 4 (by rfl) ⟨345267, by rfl⟩ : syracuseStep 3682853 = 690535) (by norm_num)
theorem B1020469 : Blo 906576 1020469 := bbase (se 5 (by rfl) ⟨47834, by rfl⟩ : syracuseStep 1020469 = 95669) (by norm_num)
theorem B4592213 : Blo 906576 4592213 := bbase (se 8 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 4592213 = 53815) (by norm_num)
theorem B9810517 : Blo 906576 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B1020505 : Blo 906576 1020505 := bbase (se 2 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 1020505 = 765379) (by norm_num)
theorem B1225325 : Blo 906576 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B3060341 : Blo 906576 3060341 := bbase (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) (by norm_num)
theorem B1020541 : Blo 906576 1020541 := bbase (se 3 (by rfl) ⟨191351, by rfl⟩ : syracuseStep 1020541 = 382703) (by norm_num)
theorem B1380997 : Blo 906576 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B1020577 : Blo 906576 1020577 := bbase (se 2 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 1020577 = 765433) (by norm_num)
theorem B1290917 : Blo 906576 1290917 := bbase (se 4 (by rfl) ⟨121023, by rfl⟩ : syracuseStep 1290917 = 242047) (by norm_num)
theorem B2298557 : Blo 906576 2298557 := bbase (se 3 (by rfl) ⟨430979, by rfl⟩ : syracuseStep 2298557 = 861959) (by norm_num)
theorem B1020613 : Blo 906576 1020613 := bbase (se 4 (by rfl) ⟨95682, by rfl⟩ : syracuseStep 1020613 = 191365) (by norm_num)
theorem B1020649 : Blo 906576 1020649 := bbase (se 2 (by rfl) ⟨382743, by rfl⟩ : syracuseStep 1020649 = 765487) (by norm_num)
theorem B6886133 : Blo 906576 6886133 := bbase (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) (by norm_num)
theorem B4362997 : Blo 906576 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B1020685 : Blo 906576 1020685 := bbase (se 3 (by rfl) ⟨191378, by rfl⟩ : syracuseStep 1020685 = 382757) (by norm_num)
theorem B1020721 : Blo 906576 1020721 := bbase (se 2 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 1020721 = 765541) (by norm_num)
theorem B1020757 : Blo 906576 1020757 := bbase (se 9 (by rfl) ⟨2990, by rfl⟩ : syracuseStep 1020757 = 5981) (by norm_num)
theorem B1020793 : Blo 906576 1020793 := bbase (se 2 (by rfl) ⟨382797, by rfl⟩ : syracuseStep 1020793 = 765595) (by norm_num)
theorem B1020829 : Blo 906576 1020829 := bbase (se 3 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 1020829 = 382811) (by norm_num)
theorem B1455005 : Blo 906576 1455005 := bbase (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) (by norm_num)
theorem B1381277 : Blo 906576 1381277 := bbase (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) (by norm_num)
theorem B1020865 : Blo 906576 1020865 := bbase (se 2 (by rfl) ⟨382824, by rfl⟩ : syracuseStep 1020865 = 765649) (by norm_num)
theorem B1020901 : Blo 906576 1020901 := bbase (se 4 (by rfl) ⟨95709, by rfl⟩ : syracuseStep 1020901 = 191419) (by norm_num)
theorem B5821429 : Blo 906576 5821429 := bbase (se 5 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 5821429 = 545759) (by norm_num)
theorem B1020937 : Blo 906576 1020937 := bbase (se 2 (by rfl) ⟨382851, by rfl⟩ : syracuseStep 1020937 = 765703) (by norm_num)
theorem B2298901 : Blo 906576 2298901 := bbase (se 6 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 2298901 = 107761) (by norm_num)
theorem B3060773 : Blo 906576 3060773 := bbase (se 4 (by rfl) ⟨286947, by rfl⟩ : syracuseStep 3060773 = 573895) (by norm_num)
theorem B1020973 : Blo 906576 1020973 := bbase (se 3 (by rfl) ⟨191432, by rfl⟩ : syracuseStep 1020973 = 382865) (by norm_num)
theorem B1021009 : Blo 906576 1021009 := bbase (se 2 (by rfl) ⟨382878, by rfl⟩ : syracuseStep 1021009 = 765757) (by norm_num)
theorem B3445861 : Blo 906576 3445861 := bbase (se 4 (by rfl) ⟨323049, by rfl⟩ : syracuseStep 3445861 = 646099) (by norm_num)
theorem B1021045 : Blo 906576 1021045 := bbase (se 5 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 1021045 = 95723) (by norm_num)
theorem B2299013 : Blo 906576 2299013 := bbase (se 4 (by rfl) ⟨215532, by rfl⟩ : syracuseStep 2299013 = 431065) (by norm_num)
theorem B1021081 : Blo 906576 1021081 := bbase (se 2 (by rfl) ⟨382905, by rfl⟩ : syracuseStep 1021081 = 765811) (by norm_num)
theorem B1021117 : Blo 906576 1021117 := bbase (se 3 (by rfl) ⟨191459, by rfl⟩ : syracuseStep 1021117 = 382919) (by norm_num)
theorem B3880133 : Blo 906576 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B1291469 : Blo 906576 1291469 := bbase (se 3 (by rfl) ⟨242150, by rfl⟩ : syracuseStep 1291469 = 484301) (by norm_num)
theorem B1021153 : Blo 906576 1021153 := bbase (se 2 (by rfl) ⟨382932, by rfl⟩ : syracuseStep 1021153 = 765865) (by norm_num)
theorem B1021189 : Blo 906576 1021189 := bbase (se 4 (by rfl) ⟨95736, by rfl⟩ : syracuseStep 1021189 = 191473) (by norm_num)
theorem B1938725 : Blo 906576 1938725 := bbase (se 4 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 1938725 = 363511) (by norm_num)
theorem B1840421 : Blo 906576 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1021225 : Blo 906576 1021225 := bbase (se 2 (by rfl) ⟨382959, by rfl⟩ : syracuseStep 1021225 = 765919) (by norm_num)
theorem B2299205 : Blo 906576 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1021261 : Blo 906576 1021261 := bbase (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) (by norm_num)
theorem B1021297 : Blo 906576 1021297 := bbase (se 2 (by rfl) ⟨382986, by rfl⟩ : syracuseStep 1021297 = 765973) (by norm_num)
theorem B7853429 : Blo 906576 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B3446165 : Blo 906576 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1021333 : Blo 906576 1021333 := bbase (se 6 (by rfl) ⟨23937, by rfl⟩ : syracuseStep 1021333 = 47875) (by norm_num)
theorem B1021369 : Blo 906576 1021369 := bbase (se 2 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 1021369 = 766027) (by norm_num)
theorem B3061205 : Blo 906576 3061205 := bbase (se 7 (by rfl) ⟨35873, by rfl⟩ : syracuseStep 3061205 = 71747) (by norm_num)
theorem B8721877 : Blo 906576 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B1021405 : Blo 906576 1021405 := bbase (se 3 (by rfl) ⟨191513, by rfl⟩ : syracuseStep 1021405 = 383027) (by norm_num)
theorem B1553917 : Blo 906576 1553917 := bbase (se 3 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 1553917 = 582719) (by norm_num)
theorem B1021441 : Blo 906576 1021441 := bbase (se 2 (by rfl) ⟨383040, by rfl⟩ : syracuseStep 1021441 = 766081) (by norm_num)
theorem B1938973 : Blo 906576 1938973 := bbase (se 3 (by rfl) ⟨363557, by rfl⟩ : syracuseStep 1938973 = 727115) (by norm_num)
theorem B1021477 : Blo 906576 1021477 := bbase (se 4 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 1021477 = 191527) (by norm_num)
theorem B1963565 : Blo 906576 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1021513 : Blo 906576 1021513 := bbase (se 2 (by rfl) ⟨383067, by rfl⟩ : syracuseStep 1021513 = 766135) (by norm_num)
theorem B1119853 : Blo 906576 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B1021549 : Blo 906576 1021549 := bbase (se 3 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 1021549 = 383081) (by norm_num)
theorem B2619013 : Blo 906576 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B1021585 : Blo 906576 1021585 := bbase (se 2 (by rfl) ⟨383094, by rfl⟩ : syracuseStep 1021585 = 766189) (by norm_num)
theorem B2299549 : Blo 906576 2299549 := bbase (se 3 (by rfl) ⟨431165, by rfl⟩ : syracuseStep 2299549 = 862331) (by norm_num)
theorem B1021621 : Blo 906576 1021621 := bbase (se 5 (by rfl) ⟨47888, by rfl⟩ : syracuseStep 1021621 = 95777) (by norm_num)
theorem B1021657 : Blo 906576 1021657 := bbase (se 2 (by rfl) ⟨383121, by rfl⟩ : syracuseStep 1021657 = 766243) (by norm_num)
theorem B1021693 : Blo 906576 1021693 := bbase (se 3 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 1021693 = 383135) (by norm_num)
theorem B2299661 : Blo 906576 2299661 := bbase (se 3 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 2299661 = 862373) (by norm_num)
theorem B1021729 : Blo 906576 1021729 := bbase (se 2 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 1021729 = 766297) (by norm_num)
theorem B1021765 : Blo 906576 1021765 := bbase (se 4 (by rfl) ⟨95790, by rfl⟩ : syracuseStep 1021765 = 191581) (by norm_num)
theorem B4593509 : Blo 906576 4593509 := bbase (se 4 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 4593509 = 861283) (by norm_num)
theorem B1021801 : Blo 906576 1021801 := bbase (se 2 (by rfl) ⟨383175, by rfl⟩ : syracuseStep 1021801 = 766351) (by norm_num)
theorem B3061637 : Blo 906576 3061637 := bbase (se 4 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 3061637 = 574057) (by norm_num)
theorem B2455429 : Blo 906576 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B1021837 : Blo 906576 1021837 := bbase (se 3 (by rfl) ⟨191594, by rfl⟩ : syracuseStep 1021837 = 383189) (by norm_num)
theorem B1021873 : Blo 906576 1021873 := bbase (se 2 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 1021873 = 766405) (by norm_num)
theorem B1226677 : Blo 906576 1226677 := bbase (se 5 (by rfl) ⟨57500, by rfl⟩ : syracuseStep 1226677 = 115001) (by norm_num)
theorem B1292221 : Blo 906576 1292221 := bbase (se 3 (by rfl) ⟨242291, by rfl⟩ : syracuseStep 1292221 = 484583) (by norm_num)
theorem B2947013 : Blo 906576 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B2455493 : Blo 906576 2455493 := bbase (se 4 (by rfl) ⟨230202, by rfl⟩ : syracuseStep 2455493 = 460405) (by norm_num)
theorem B5167061 : Blo 906576 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B1021909 : Blo 906576 1021909 := bbase (se 7 (by rfl) ⟨11975, by rfl⟩ : syracuseStep 1021909 = 23951) (by norm_num)
theorem B1021945 : Blo 906576 1021945 := bbase (se 2 (by rfl) ⟨383229, by rfl⟩ : syracuseStep 1021945 = 766459) (by norm_num)
theorem B2586629 : Blo 906576 2586629 := bbase (se 4 (by rfl) ⟨242496, by rfl⟩ : syracuseStep 2586629 = 484993) (by norm_num)
theorem B1939477 : Blo 906576 1939477 := bbase (se 6 (by rfl) ⟨45456, by rfl⟩ : syracuseStep 1939477 = 90913) (by norm_num)
theorem B1021981 : Blo 906576 1021981 := bbase (se 3 (by rfl) ⟨191621, by rfl⟩ : syracuseStep 1021981 = 383243) (by norm_num)
theorem B1022017 : Blo 906576 1022017 := bbase (se 2 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 1022017 = 766513) (by norm_num)
theorem B1529941 : Blo 906576 1529941 := bbase (se 8 (by rfl) ⟨8964, by rfl⟩ : syracuseStep 1529941 = 17929) (by norm_num)
theorem B1022053 : Blo 906576 1022053 := bbase (se 4 (by rfl) ⟨95817, by rfl⟩ : syracuseStep 1022053 = 191635) (by norm_num)
theorem B1022089 : Blo 906576 1022089 := bbase (se 2 (by rfl) ⟨383283, by rfl⟩ : syracuseStep 1022089 = 766567) (by norm_num)
theorem B1063057 : Blo 906576 1063057 := bbase (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) (by norm_num)
theorem B1530029 : Blo 906576 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B1022125 : Blo 906576 1022125 := bbase (se 3 (by rfl) ⟨191648, by rfl⟩ : syracuseStep 1022125 = 383297) (by norm_num)
theorem B1530157 : Blo 906576 1530157 := bbase (se 3 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 1530157 = 573809) (by norm_num)
theorem B3062069 : Blo 906576 3062069 := bbase (se 5 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 3062069 = 287069) (by norm_num)
theorem B3873109 : Blo 906576 3873109 := bbase (se 10 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 3873109 = 11347) (by norm_num)
theorem B2070893 : Blo 906576 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B1530245 : Blo 906576 1530245 := bbase (se 4 (by rfl) ⟨143460, by rfl⟩ : syracuseStep 1530245 = 286921) (by norm_num)
theorem B15702421 : Blo 906576 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B1530373 : Blo 906576 1530373 := bbase (se 4 (by rfl) ⟨143472, by rfl⟩ : syracuseStep 1530373 = 286945) (by norm_num)
theorem B4659797 : Blo 906576 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B1530461 : Blo 906576 1530461 := bbase (se 3 (by rfl) ⟨286961, by rfl⟩ : syracuseStep 1530461 = 573923) (by norm_num)
theorem B1399445 : Blo 906576 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B7756469 : Blo 906576 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B1637053 : Blo 906576 1637053 := bbase (se 3 (by rfl) ⟨306947, by rfl⟩ : syracuseStep 1637053 = 613895) (by norm_num)
theorem B1293013 : Blo 906576 1293013 := bbase (se 7 (by rfl) ⟨15152, by rfl⟩ : syracuseStep 1293013 = 30305) (by norm_num)
theorem B1530589 : Blo 906576 1530589 := bbase (se 3 (by rfl) ⟨286985, by rfl⟩ : syracuseStep 1530589 = 573971) (by norm_num)
theorem B3062501 : Blo 906576 3062501 := bbase (se 4 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 3062501 = 574219) (by norm_num)
theorem B3496693 : Blo 906576 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B7748405 : Blo 906576 7748405 := bbase (se 5 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 7748405 = 726413) (by norm_num)
theorem B1530677 : Blo 906576 1530677 := bbase (se 5 (by rfl) ⟨71750, by rfl⟩ : syracuseStep 1530677 = 143501) (by norm_num)
theorem B2906933 : Blo 906576 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B1940365 : Blo 906576 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B1530805 : Blo 906576 1530805 := bbase (se 5 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 1530805 = 143513) (by norm_num)
theorem B18889685 : Blo 906576 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B1530893 : Blo 906576 1530893 := bbase (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) (by norm_num)
theorem B1293349 : Blo 906576 1293349 := bbase (se 4 (by rfl) ⟨121251, by rfl⟩ : syracuseStep 1293349 = 242503) (by norm_num)
theorem B3873845 : Blo 906576 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B5168245 : Blo 906576 5168245 := bbase (se 5 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 5168245 = 484523) (by norm_num)
theorem B4594805 : Blo 906576 4594805 := bbase (se 5 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 4594805 = 430763) (by norm_num)
theorem B1531021 : Blo 906576 1531021 := bbase (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) (by norm_num)
theorem B3062933 : Blo 906576 3062933 := bbase (se 6 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 3062933 = 143575) (by norm_num)
theorem B14351573 : Blo 906576 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B1531109 : Blo 906576 1531109 := bbase (se 4 (by rfl) ⟨143541, by rfl⟩ : syracuseStep 1531109 = 287083) (by norm_num)
theorem B1293565 : Blo 906576 1293565 := bbase (se 3 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 1293565 = 485087) (by norm_num)
theorem B1531237 : Blo 906576 1531237 := bbase (se 4 (by rfl) ⟨143553, by rfl⟩ : syracuseStep 1531237 = 287107) (by norm_num)
theorem B1531325 : Blo 906576 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B3448277 : Blo 906576 3448277 := bbase (se 7 (by rfl) ⟨40409, by rfl⟩ : syracuseStep 3448277 = 80819) (by norm_num)
theorem B2211293 : Blo 906576 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B3726853 : Blo 906576 3726853 := bbase (se 4 (by rfl) ⟨349392, by rfl⟩ : syracuseStep 3726853 = 698785) (by norm_num)
theorem B1531453 : Blo 906576 1531453 := bbase (se 3 (by rfl) ⟨287147, by rfl⟩ : syracuseStep 1531453 = 574295) (by norm_num)
theorem B3063365 : Blo 906576 3063365 := bbase (se 4 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 3063365 = 574381) (by norm_num)
theorem B1531541 : Blo 906576 1531541 := bbase (se 6 (by rfl) ⟨35895, by rfl⟩ : syracuseStep 1531541 = 71791) (by norm_num)
theorem B9313973 : Blo 906576 9313973 := bbase (se 5 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 9313973 = 873185) (by norm_num)
theorem B2907845 : Blo 906576 2907845 := bbase (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) (by norm_num)
theorem B3448565 : Blo 906576 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B1089293 : Blo 906576 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B1531669 : Blo 906576 1531669 := bbase (se 6 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 1531669 = 71797) (by norm_num)
theorem B3358549 : Blo 906576 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1531757 : Blo 906576 1531757 := bbase (se 3 (by rfl) ⟨287204, by rfl⟩ : syracuseStep 1531757 = 574409) (by norm_num)
theorem B1531885 : Blo 906576 1531885 := bbase (se 3 (by rfl) ⟨287228, by rfl⟩ : syracuseStep 1531885 = 574457) (by norm_num)
theorem B3063797 : Blo 906576 3063797 := bbase (se 5 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 3063797 = 287231) (by norm_num)
theorem B1359869 : Blo 906576 1359869 := bbase (se 3 (by rfl) ⟨254975, by rfl⟩ : syracuseStep 1359869 = 509951) (by norm_num)
theorem B1359875 : Blo 906576 1359875 := bstep (se 1 (by rfl) ⟨1019906, by rfl⟩ : syracuseStep 1359875 = 2039813) B2039813
theorem B1359905 : Blo 906576 1359905 := bstep (se 2 (by rfl) ⟨509964, by rfl⟩ : syracuseStep 1359905 = 1019929) B1019929
theorem B1531939 : Blo 906576 1531939 := bstep (se 1 (by rfl) ⟨1148954, by rfl⟩ : syracuseStep 1531939 = 2297909) B2297909
theorem B1359923 : Blo 906576 1359923 := bstep (se 1 (by rfl) ⟨1019942, by rfl⟩ : syracuseStep 1359923 = 2039885) B2039885
theorem B29835317 : Blo 906576 29835317 := bstep (se 5 (by rfl) ⟨1398530, by rfl⟩ : syracuseStep 29835317 = 2797061) B2797061
theorem B11190325 : Blo 906576 11190325 := bstep (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) B1049093
theorem B1359953 : Blo 906576 1359953 := bstep (se 2 (by rfl) ⟨509982, by rfl⟩ : syracuseStep 1359953 = 1019965) B1019965
theorem B1359971 : Blo 906576 1359971 := bstep (se 1 (by rfl) ⟨1019978, by rfl⟩ : syracuseStep 1359971 = 2039957) B2039957
theorem B2039921 : Blo 906576 2039921 := bstep (se 2 (by rfl) ⟨764970, by rfl⟩ : syracuseStep 2039921 = 1529941) B1529941
theorem B1360001 : Blo 906576 1360001 := bstep (se 2 (by rfl) ⟨510000, by rfl⟩ : syracuseStep 1360001 = 1020001) B1020001
theorem B2039939 : Blo 906576 2039939 := bstep (se 1 (by rfl) ⟨1529954, by rfl⟩ : syracuseStep 2039939 = 3059909) B3059909
theorem B1360019 : Blo 906576 1360019 := bstep (se 1 (by rfl) ⟨1020014, by rfl⟩ : syracuseStep 1360019 = 2040029) B2040029
theorem B1360049 : Blo 906576 1360049 := bstep (se 2 (by rfl) ⟨510018, by rfl⟩ : syracuseStep 1360049 = 1020037) B1020037
theorem B1532081 : Blo 906576 1532081 := bstep (se 2 (by rfl) ⟨574530, by rfl⟩ : syracuseStep 1532081 = 1149061) B1149061
theorem B1417409 : Blo 906576 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B1360067 : Blo 906576 1360067 := bstep (se 1 (by rfl) ⟨1020050, by rfl⟩ : syracuseStep 1360067 = 2040101) B2040101
theorem B3064013 : Blo 906576 3064013 := bstep (se 3 (by rfl) ⟨574502, by rfl⟩ : syracuseStep 3064013 = 1149005) B1149005
theorem B1360097 : Blo 906576 1360097 := bstep (se 2 (by rfl) ⟨510036, by rfl⟩ : syracuseStep 1360097 = 1020073) B1020073
theorem B4595939 : Blo 906576 4595939 := bstep (se 1 (by rfl) ⟨3446954, by rfl⟩ : syracuseStep 4595939 = 6893909) B6893909
theorem B6209777 : Blo 906576 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B1360115 : Blo 906576 1360115 := bstep (se 1 (by rfl) ⟨1020086, by rfl⟩ : syracuseStep 1360115 = 2040173) B2040173
theorem B3064067 : Blo 906576 3064067 := bstep (se 1 (by rfl) ⟨2298050, by rfl⟩ : syracuseStep 3064067 = 4596101) B4596101
theorem B1360145 : Blo 906576 1360145 := bstep (se 2 (by rfl) ⟨510054, by rfl⟩ : syracuseStep 1360145 = 1020109) B1020109
theorem B2326801 : Blo 906576 2326801 := bstep (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) B1745101
theorem B1360163 : Blo 906576 1360163 := bstep (se 1 (by rfl) ⟨1020122, by rfl⟩ : syracuseStep 1360163 = 2040245) B2040245
theorem B1532209 : Blo 906576 1532209 := bstep (se 2 (by rfl) ⟨574578, by rfl⟩ : syracuseStep 1532209 = 1149157) B1149157
theorem B1360193 : Blo 906576 1360193 := bstep (se 2 (by rfl) ⟨510072, by rfl⟩ : syracuseStep 1360193 = 1020145) B1020145
theorem B1360211 : Blo 906576 1360211 := bstep (se 1 (by rfl) ⟨1020158, by rfl⟩ : syracuseStep 1360211 = 2040317) B2040317
theorem B1532243 : Blo 906576 1532243 := bstep (se 1 (by rfl) ⟨1149182, by rfl⟩ : syracuseStep 1532243 = 2298365) B2298365
theorem B7758179 : Blo 906576 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B1360241 : Blo 906576 1360241 := bstep (se 2 (by rfl) ⟨510090, by rfl⟩ : syracuseStep 1360241 = 1020181) B1020181
theorem B5169521 : Blo 906576 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B1360259 : Blo 906576 1360259 := bstep (se 1 (by rfl) ⟨1020194, by rfl⟩ : syracuseStep 1360259 = 2040389) B2040389
theorem B2040209 : Blo 906576 2040209 := bstep (se 2 (by rfl) ⟨765078, by rfl⟩ : syracuseStep 2040209 = 1530157) B1530157
theorem B1360289 : Blo 906576 1360289 := bstep (se 2 (by rfl) ⟨510108, by rfl⟩ : syracuseStep 1360289 = 1020217) B1020217
theorem B2040227 : Blo 906576 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B4907441 : Blo 906576 4907441 := bstep (se 2 (by rfl) ⟨1840290, by rfl⟩ : syracuseStep 4907441 = 3680581) B3680581
theorem B1360307 : Blo 906576 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B1360337 : Blo 906576 1360337 := bstep (se 2 (by rfl) ⟨510126, by rfl⟩ : syracuseStep 1360337 = 1020253) B1020253
theorem B1532371 : Blo 906576 1532371 := bstep (se 1 (by rfl) ⟨1149278, by rfl⟩ : syracuseStep 1532371 = 2298557) B2298557
theorem B1327585 : Blo 906576 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B1360355 : Blo 906576 1360355 := bstep (se 1 (by rfl) ⟨1020266, by rfl⟩ : syracuseStep 1360355 = 2040533) B2040533
theorem B1360385 : Blo 906576 1360385 := bstep (se 2 (by rfl) ⟨510144, by rfl⟩ : syracuseStep 1360385 = 1020289) B1020289
theorem B3064337 : Blo 906576 3064337 := bstep (se 2 (by rfl) ⟨1149126, by rfl⟩ : syracuseStep 3064337 = 2298253) B2298253
theorem B1360403 : Blo 906576 1360403 := bstep (se 1 (by rfl) ⟨1020302, by rfl⟩ : syracuseStep 1360403 = 2040605) B2040605
theorem B1360433 : Blo 906576 1360433 := bstep (se 2 (by rfl) ⟨510162, by rfl⟩ : syracuseStep 1360433 = 1020325) B1020325
theorem B1360451 : Blo 906576 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B5972549 : Blo 906576 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B1360481 : Blo 906576 1360481 := bstep (se 2 (by rfl) ⟨510180, by rfl⟩ : syracuseStep 1360481 = 1020361) B1020361
theorem B1532513 : Blo 906576 1532513 := bstep (se 2 (by rfl) ⟨574692, by rfl⟩ : syracuseStep 1532513 = 1149385) B1149385
theorem B1360499 : Blo 906576 1360499 := bstep (se 1 (by rfl) ⟨1020374, by rfl⟩ : syracuseStep 1360499 = 2040749) B2040749
theorem B1360529 : Blo 906576 1360529 := bstep (se 2 (by rfl) ⟨510198, by rfl⟩ : syracuseStep 1360529 = 1020397) B1020397
theorem B1360547 : Blo 906576 1360547 := bstep (se 1 (by rfl) ⟨1020410, by rfl⟩ : syracuseStep 1360547 = 2040821) B2040821
theorem B2040497 : Blo 906576 2040497 := bstep (se 2 (by rfl) ⟨765186, by rfl⟩ : syracuseStep 2040497 = 1530373) B1530373
theorem B9814709 : Blo 906576 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B1360577 : Blo 906576 1360577 := bstep (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) B1020433
theorem B2040515 : Blo 906576 2040515 := bstep (se 1 (by rfl) ⟨1530386, by rfl⟩ : syracuseStep 2040515 = 3060773) B3060773
theorem B1147603 : Blo 906576 1147603 := bstep (se 1 (by rfl) ⟨860702, by rfl⟩ : syracuseStep 1147603 = 1721405) B1721405
theorem B1360595 : Blo 906576 1360595 := bstep (se 1 (by rfl) ⟨1020446, by rfl⟩ : syracuseStep 1360595 = 2040893) B2040893
theorem B1532641 : Blo 906576 1532641 := bstep (se 2 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 1532641 = 1149481) B1149481
theorem B1360625 : Blo 906576 1360625 := bstep (se 2 (by rfl) ⟨510234, by rfl⟩ : syracuseStep 1360625 = 1020469) B1020469
theorem B1360643 : Blo 906576 1360643 := bstep (se 1 (by rfl) ⟨1020482, by rfl⟩ : syracuseStep 1360643 = 2040965) B2040965
theorem B1532675 : Blo 906576 1532675 := bstep (se 1 (by rfl) ⟨1149506, by rfl⟩ : syracuseStep 1532675 = 2299013) B2299013
theorem B4907789 : Blo 906576 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B1360673 : Blo 906576 1360673 := bstep (se 2 (by rfl) ⟨510252, by rfl⟩ : syracuseStep 1360673 = 1020505) B1020505
theorem B2908973 : Blo 906576 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B1147699 : Blo 906576 1147699 := bstep (se 1 (by rfl) ⟨860774, by rfl⟩ : syracuseStep 1147699 = 1721549) B1721549
theorem B1360691 : Blo 906576 1360691 := bstep (se 1 (by rfl) ⟨1020518, by rfl⟩ : syracuseStep 1360691 = 2041037) B2041037
theorem B1360721 : Blo 906576 1360721 := bstep (se 2 (by rfl) ⟨510270, by rfl⟩ : syracuseStep 1360721 = 1020541) B1020541
theorem B1360739 : Blo 906576 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B1360769 : Blo 906576 1360769 := bstep (se 2 (by rfl) ⟨510288, by rfl⟩ : syracuseStep 1360769 = 1020577) B1020577
theorem B1532803 : Blo 906576 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B1360787 : Blo 906576 1360787 := bstep (se 1 (by rfl) ⟨1020590, by rfl⟩ : syracuseStep 1360787 = 2041181) B2041181
theorem B5235619 : Blo 906576 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1360817 : Blo 906576 1360817 := bstep (se 2 (by rfl) ⟨510306, by rfl⟩ : syracuseStep 1360817 = 1020613) B1020613
theorem B1360835 : Blo 906576 1360835 := bstep (se 1 (by rfl) ⟨1020626, by rfl⟩ : syracuseStep 1360835 = 2041253) B2041253
theorem B5522381 : Blo 906576 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B2040785 : Blo 906576 2040785 := bstep (se 2 (by rfl) ⟨765294, by rfl⟩ : syracuseStep 2040785 = 1530589) B1530589
theorem B1360865 : Blo 906576 1360865 := bstep (se 2 (by rfl) ⟨510324, by rfl⟩ : syracuseStep 1360865 = 1020649) B1020649
theorem B2040803 : Blo 906576 2040803 := bstep (se 1 (by rfl) ⟨1530602, by rfl⟩ : syracuseStep 2040803 = 3061205) B3061205
theorem B5817329 : Blo 906576 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B4662257 : Blo 906576 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B1360883 : Blo 906576 1360883 := bstep (se 1 (by rfl) ⟨1020662, by rfl⟩ : syracuseStep 1360883 = 2041325) B2041325
theorem B4596749 : Blo 906576 4596749 := bstep (se 3 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 4596749 = 1723781) B1723781
theorem B2294801 : Blo 906576 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1360913 : Blo 906576 1360913 := bstep (se 2 (by rfl) ⟨510342, by rfl⟩ : syracuseStep 1360913 = 1020685) B1020685
theorem B1532945 : Blo 906576 1532945 := bstep (se 2 (by rfl) ⟨574854, by rfl⟩ : syracuseStep 1532945 = 1149709) B1149709
theorem B1360931 : Blo 906576 1360931 := bstep (se 1 (by rfl) ⟨1020698, by rfl⟩ : syracuseStep 1360931 = 2041397) B2041397
theorem B3064877 : Blo 906576 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B1360961 : Blo 906576 1360961 := bstep (se 2 (by rfl) ⟨510360, by rfl⟩ : syracuseStep 1360961 = 1020721) B1020721
theorem B2294851 : Blo 906576 2294851 := bstep (se 1 (by rfl) ⟨1721138, by rfl⟩ : syracuseStep 2294851 = 3442277) B3442277
theorem B1360979 : Blo 906576 1360979 := bstep (se 1 (by rfl) ⟨1020734, by rfl⟩ : syracuseStep 1360979 = 2041469) B2041469
theorem B3064931 : Blo 906576 3064931 := bstep (se 1 (by rfl) ⟨2298698, by rfl⟩ : syracuseStep 3064931 = 4597397) B4597397
theorem B1361009 : Blo 906576 1361009 := bstep (se 2 (by rfl) ⟨510378, by rfl⟩ : syracuseStep 1361009 = 1020757) B1020757
theorem B1361027 : Blo 906576 1361027 := bstep (se 1 (by rfl) ⟨1020770, by rfl⟩ : syracuseStep 1361027 = 2041541) B2041541
theorem B1533073 : Blo 906576 1533073 := bstep (se 2 (by rfl) ⟨574902, by rfl⟩ : syracuseStep 1533073 = 1149805) B1149805
theorem B1361057 : Blo 906576 1361057 := bstep (se 2 (by rfl) ⟨510396, by rfl⟩ : syracuseStep 1361057 = 1020793) B1020793
theorem B1361075 : Blo 906576 1361075 := bstep (se 1 (by rfl) ⟨1020806, by rfl⟩ : syracuseStep 1361075 = 2041613) B2041613
theorem B1533107 : Blo 906576 1533107 := bstep (se 1 (by rfl) ⟨1149830, by rfl⟩ : syracuseStep 1533107 = 2299661) B2299661
theorem B2294993 : Blo 906576 2294993 := bstep (se 2 (by rfl) ⟨860622, by rfl⟩ : syracuseStep 2294993 = 1721245) B1721245
theorem B1361105 : Blo 906576 1361105 := bstep (se 2 (by rfl) ⟨510414, by rfl⟩ : syracuseStep 1361105 = 1020829) B1020829
theorem B1361123 : Blo 906576 1361123 := bstep (se 1 (by rfl) ⟨1020842, by rfl⟩ : syracuseStep 1361123 = 2041685) B2041685
theorem B2041073 : Blo 906576 2041073 := bstep (se 2 (by rfl) ⟨765402, by rfl⟩ : syracuseStep 2041073 = 1530805) B1530805
theorem B1361153 : Blo 906576 1361153 := bstep (se 2 (by rfl) ⟨510432, by rfl⟩ : syracuseStep 1361153 = 1020865) B1020865
theorem B2041091 : Blo 906576 2041091 := bstep (se 1 (by rfl) ⟨1530818, by rfl⟩ : syracuseStep 2041091 = 3061637) B3061637
theorem B1361171 : Blo 906576 1361171 := bstep (se 1 (by rfl) ⟨1020878, by rfl⟩ : syracuseStep 1361171 = 2041757) B2041757
theorem B33596693 : Blo 906576 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B1148195 : Blo 906576 1148195 := bstep (se 1 (by rfl) ⟨861146, by rfl⟩ : syracuseStep 1148195 = 1722293) B1722293
theorem B1361201 : Blo 906576 1361201 := bstep (se 2 (by rfl) ⟨510450, by rfl⟩ : syracuseStep 1361201 = 1020901) B1020901
theorem B1361219 : Blo 906576 1361219 := bstep (se 1 (by rfl) ⟨1020914, by rfl⟩ : syracuseStep 1361219 = 2041829) B2041829
theorem B1361249 : Blo 906576 1361249 := bstep (se 2 (by rfl) ⟨510468, by rfl⟩ : syracuseStep 1361249 = 1020937) B1020937
theorem B3065201 : Blo 906576 3065201 := bstep (se 2 (by rfl) ⟨1149450, by rfl⟩ : syracuseStep 3065201 = 2298901) B2298901
theorem B1361267 : Blo 906576 1361267 := bstep (se 1 (by rfl) ⟨1020950, by rfl⟩ : syracuseStep 1361267 = 2041901) B2041901
theorem B1721731 : Blo 906576 1721731 := bstep (se 1 (by rfl) ⟨1291298, by rfl⟩ : syracuseStep 1721731 = 2582597) B2582597
theorem B1361297 : Blo 906576 1361297 := bstep (se 2 (by rfl) ⟨510486, by rfl⟩ : syracuseStep 1361297 = 1020973) B1020973
theorem B1361315 : Blo 906576 1361315 := bstep (se 1 (by rfl) ⟨1020986, by rfl⟩ : syracuseStep 1361315 = 2041973) B2041973
theorem B1361345 : Blo 906576 1361345 := bstep (se 2 (by rfl) ⟨510504, by rfl⟩ : syracuseStep 1361345 = 1021009) B1021009
theorem B1361363 : Blo 906576 1361363 := bstep (se 1 (by rfl) ⟨1021022, by rfl⟩ : syracuseStep 1361363 = 2042045) B2042045
theorem B6890993 : Blo 906576 6890993 := bstep (se 2 (by rfl) ⟨2584122, by rfl⟩ : syracuseStep 6890993 = 5168245) B5168245
theorem B1361393 : Blo 906576 1361393 := bstep (se 2 (by rfl) ⟨510522, by rfl⟩ : syracuseStep 1361393 = 1021045) B1021045
theorem B1361411 : Blo 906576 1361411 := bstep (se 1 (by rfl) ⟨1021058, by rfl⟩ : syracuseStep 1361411 = 2042117) B2042117
theorem B2041361 : Blo 906576 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B1361441 : Blo 906576 1361441 := bstep (se 2 (by rfl) ⟨510540, by rfl⟩ : syracuseStep 1361441 = 1021081) B1021081
theorem B1721891 : Blo 906576 1721891 := bstep (se 1 (by rfl) ⟨1291418, by rfl⟩ : syracuseStep 1721891 = 2582837) B2582837
theorem B2041379 : Blo 906576 2041379 := bstep (se 1 (by rfl) ⟨1531034, by rfl⟩ : syracuseStep 2041379 = 3062069) B3062069
theorem B2328113 : Blo 906576 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B1361459 : Blo 906576 1361459 := bstep (se 1 (by rfl) ⟨1021094, by rfl⟩ : syracuseStep 1361459 = 2042189) B2042189
theorem B1361489 : Blo 906576 1361489 := bstep (se 2 (by rfl) ⟨510558, by rfl⟩ : syracuseStep 1361489 = 1021117) B1021117
theorem B1361507 : Blo 906576 1361507 := bstep (se 1 (by rfl) ⟨1021130, by rfl⟩ : syracuseStep 1361507 = 2042261) B2042261
theorem B1361537 : Blo 906576 1361537 := bstep (se 2 (by rfl) ⟨510576, by rfl⟩ : syracuseStep 1361537 = 1021153) B1021153
theorem B1361555 : Blo 906576 1361555 := bstep (se 1 (by rfl) ⟨1021166, by rfl⟩ : syracuseStep 1361555 = 2042333) B2042333
theorem B1361585 : Blo 906576 1361585 := bstep (se 2 (by rfl) ⟨510594, by rfl⟩ : syracuseStep 1361585 = 1021189) B1021189
theorem B1361603 : Blo 906576 1361603 := bstep (se 1 (by rfl) ⟨1021202, by rfl⟩ : syracuseStep 1361603 = 2042405) B2042405
theorem B1361633 : Blo 906576 1361633 := bstep (se 2 (by rfl) ⟨510612, by rfl⟩ : syracuseStep 1361633 = 1021225) B1021225
theorem B3106531 : Blo 906576 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B1361651 : Blo 906576 1361651 := bstep (se 1 (by rfl) ⟨1021238, by rfl⟩ : syracuseStep 1361651 = 2042477) B2042477
theorem B3442445 : Blo 906576 3442445 := bstep (se 3 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 3442445 = 1290917) B1290917
theorem B1361681 : Blo 906576 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B1361699 : Blo 906576 1361699 := bstep (se 1 (by rfl) ⟨1021274, by rfl⟩ : syracuseStep 1361699 = 2042549) B2042549
theorem B5170979 : Blo 906576 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B2041649 : Blo 906576 2041649 := bstep (se 2 (by rfl) ⟨765618, by rfl⟩ : syracuseStep 2041649 = 1531237) B1531237
theorem B1361729 : Blo 906576 1361729 := bstep (se 2 (by rfl) ⟨510648, by rfl⟩ : syracuseStep 1361729 = 1021297) B1021297
theorem B2041667 : Blo 906576 2041667 := bstep (se 1 (by rfl) ⟨1531250, by rfl⟩ : syracuseStep 2041667 = 3062501) B3062501
theorem B1361747 : Blo 906576 1361747 := bstep (se 1 (by rfl) ⟨1021310, by rfl⟩ : syracuseStep 1361747 = 2042621) B2042621
theorem B2582381 : Blo 906576 2582381 := bstep (se 3 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 2582381 = 968393) B968393
theorem B1361777 : Blo 906576 1361777 := bstep (se 2 (by rfl) ⟨510666, by rfl⟩ : syracuseStep 1361777 = 1021333) B1021333
theorem B1361795 : Blo 906576 1361795 := bstep (se 1 (by rfl) ⟨1021346, by rfl⟩ : syracuseStep 1361795 = 2042693) B2042693
theorem B2451341 : Blo 906576 2451341 := bstep (se 3 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 2451341 = 919253) B919253
theorem B8284045 : Blo 906576 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B3065741 : Blo 906576 3065741 := bstep (se 3 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 3065741 = 1149653) B1149653
theorem B1361825 : Blo 906576 1361825 := bstep (se 2 (by rfl) ⟨510684, by rfl⟩ : syracuseStep 1361825 = 1021369) B1021369
theorem B1361843 : Blo 906576 1361843 := bstep (se 1 (by rfl) ⟨1021382, by rfl⟩ : syracuseStep 1361843 = 2042765) B2042765
theorem B3065795 : Blo 906576 3065795 := bstep (se 1 (by rfl) ⟨2299346, by rfl⟩ : syracuseStep 3065795 = 4598693) B4598693
theorem B1361873 : Blo 906576 1361873 := bstep (se 2 (by rfl) ⟨510702, by rfl⟩ : syracuseStep 1361873 = 1021405) B1021405
theorem B1148899 : Blo 906576 1148899 := bstep (se 1 (by rfl) ⟨861674, by rfl⟩ : syracuseStep 1148899 = 1723349) B1723349
theorem B12593123 : Blo 906576 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B1361891 : Blo 906576 1361891 := bstep (se 1 (by rfl) ⟨1021418, by rfl⟩ : syracuseStep 1361891 = 2042837) B2042837
theorem B1361921 : Blo 906576 1361921 := bstep (se 2 (by rfl) ⟨510720, by rfl⟩ : syracuseStep 1361921 = 1021441) B1021441
theorem B1361939 : Blo 906576 1361939 := bstep (se 1 (by rfl) ⟨1021454, by rfl⟩ : syracuseStep 1361939 = 2042909) B2042909
theorem B2582563 : Blo 906576 2582563 := bstep (se 1 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 2582563 = 3873845) B3873845
theorem B1361969 : Blo 906576 1361969 := bstep (se 2 (by rfl) ⟨510738, by rfl⟩ : syracuseStep 1361969 = 1021477) B1021477
theorem B1148995 : Blo 906576 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1361987 : Blo 906576 1361987 := bstep (se 1 (by rfl) ⟨1021490, by rfl⟩ : syracuseStep 1361987 = 2042981) B2042981
theorem B2041937 : Blo 906576 2041937 := bstep (se 2 (by rfl) ⟨765726, by rfl⟩ : syracuseStep 2041937 = 1531453) B1531453
theorem B1362017 : Blo 906576 1362017 := bstep (se 2 (by rfl) ⟨510756, by rfl⟩ : syracuseStep 1362017 = 1021513) B1021513
theorem B2041955 : Blo 906576 2041955 := bstep (se 1 (by rfl) ⟨1531466, by rfl⟩ : syracuseStep 2041955 = 3062933) B3062933
theorem B1362035 : Blo 906576 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B7751821 : Blo 906576 7751821 := bstep (se 3 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 7751821 = 2906933) B2906933
theorem B1362065 : Blo 906576 1362065 := bstep (se 2 (by rfl) ⟨510774, by rfl⟩ : syracuseStep 1362065 = 1021549) B1021549
theorem B1362083 : Blo 906576 1362083 := bstep (se 1 (by rfl) ⟨1021562, by rfl⟩ : syracuseStep 1362083 = 2043125) B2043125
theorem B2295985 : Blo 906576 2295985 := bstep (se 2 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 2295985 = 1721989) B1721989
theorem B3492017 : Blo 906576 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B1362113 : Blo 906576 1362113 := bstep (se 2 (by rfl) ⟨510792, by rfl⟩ : syracuseStep 1362113 = 1021585) B1021585
theorem B3066065 : Blo 906576 3066065 := bstep (se 2 (by rfl) ⟨1149774, by rfl⟩ : syracuseStep 3066065 = 2299549) B2299549
theorem B1362131 : Blo 906576 1362131 := bstep (se 1 (by rfl) ⟨1021598, by rfl⟩ : syracuseStep 1362131 = 2043197) B2043197
theorem B1362161 : Blo 906576 1362161 := bstep (se 2 (by rfl) ⟨510810, by rfl⟩ : syracuseStep 1362161 = 1021621) B1021621
theorem B1362179 : Blo 906576 1362179 := bstep (se 1 (by rfl) ⟨1021634, by rfl⟩ : syracuseStep 1362179 = 2043269) B2043269
theorem B1362209 : Blo 906576 1362209 := bstep (se 2 (by rfl) ⟨510828, by rfl⟩ : syracuseStep 1362209 = 1021657) B1021657
theorem B1362227 : Blo 906576 1362227 := bstep (se 1 (by rfl) ⟨1021670, by rfl⟩ : syracuseStep 1362227 = 2043341) B2043341
theorem B1362257 : Blo 906576 1362257 := bstep (se 2 (by rfl) ⟨510846, by rfl⟩ : syracuseStep 1362257 = 1021693) B1021693
theorem B1362275 : Blo 906576 1362275 := bstep (se 1 (by rfl) ⟨1021706, by rfl⟩ : syracuseStep 1362275 = 2043413) B2043413
theorem B2042225 : Blo 906576 2042225 := bstep (se 2 (by rfl) ⟨765834, by rfl⟩ : syracuseStep 2042225 = 1531669) B1531669
theorem B1362305 : Blo 906576 1362305 := bstep (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) B1021729
theorem B2042243 : Blo 906576 2042243 := bstep (se 1 (by rfl) ⟨1531682, by rfl⟩ : syracuseStep 2042243 = 3063365) B3063365
theorem B1362323 : Blo 906576 1362323 := bstep (se 1 (by rfl) ⟨1021742, by rfl⟩ : syracuseStep 1362323 = 2043485) B2043485
theorem B5818787 : Blo 906576 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B1362353 : Blo 906576 1362353 := bstep (se 2 (by rfl) ⟨510882, by rfl⟩ : syracuseStep 1362353 = 1021765) B1021765
theorem B2296259 : Blo 906576 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B1362371 : Blo 906576 1362371 := bstep (se 1 (by rfl) ⟨1021778, by rfl⟩ : syracuseStep 1362371 = 2043557) B2043557
theorem B1362401 : Blo 906576 1362401 := bstep (se 2 (by rfl) ⟨510900, by rfl⟩ : syracuseStep 1362401 = 1021801) B1021801
theorem B1362419 : Blo 906576 1362419 := bstep (se 1 (by rfl) ⟨1021814, by rfl⟩ : syracuseStep 1362419 = 2043629) B2043629
theorem B2583053 : Blo 906576 2583053 := bstep (se 3 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 2583053 = 968645) B968645
theorem B6547981 : Blo 906576 6547981 := bstep (se 3 (by rfl) ⟨1227746, by rfl⟩ : syracuseStep 6547981 = 2455493) B2455493
theorem B1362449 : Blo 906576 1362449 := bstep (se 2 (by rfl) ⟨510918, by rfl⟩ : syracuseStep 1362449 = 1021837) B1021837
theorem B969251 : Blo 906576 969251 := bstep (se 1 (by rfl) ⟨726938, by rfl⟩ : syracuseStep 969251 = 1453877) B1453877
theorem B1362467 : Blo 906576 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B3443249 : Blo 906576 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B1149491 : Blo 906576 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B1362497 : Blo 906576 1362497 := bstep (se 2 (by rfl) ⟨510936, by rfl⟩ : syracuseStep 1362497 = 1021873) B1021873
theorem B1722961 : Blo 906576 1722961 := bstep (se 2 (by rfl) ⟨646110, by rfl⟩ : syracuseStep 1722961 = 1292221) B1292221
theorem B1362515 : Blo 906576 1362515 := bstep (se 1 (by rfl) ⟨1021886, by rfl⟩ : syracuseStep 1362515 = 2043773) B2043773
theorem B1362545 : Blo 906576 1362545 := bstep (se 2 (by rfl) ⟨510954, by rfl⟩ : syracuseStep 1362545 = 1021909) B1021909
theorem B2296451 : Blo 906576 2296451 := bstep (se 1 (by rfl) ⟨1722338, by rfl⟩ : syracuseStep 2296451 = 3444677) B3444677
theorem B1362563 : Blo 906576 1362563 := bstep (se 1 (by rfl) ⟨1021922, by rfl⟩ : syracuseStep 1362563 = 2043845) B2043845
theorem B2042513 : Blo 906576 2042513 := bstep (se 2 (by rfl) ⟨765942, by rfl⟩ : syracuseStep 2042513 = 1531885) B1531885
theorem B1362593 : Blo 906576 1362593 := bstep (se 2 (by rfl) ⟨510972, by rfl⟩ : syracuseStep 1362593 = 1021945) B1021945
theorem B2042531 : Blo 906576 2042531 := bstep (se 1 (by rfl) ⟨1531898, by rfl⟩ : syracuseStep 2042531 = 3063797) B3063797
theorem B1362611 : Blo 906576 1362611 := bstep (se 1 (by rfl) ⟨1021958, by rfl⟩ : syracuseStep 1362611 = 2043917) B2043917
theorem B19876549 : Blo 906576 19876549 := bstep (se 4 (by rfl) ⟨1863426, by rfl⟩ : syracuseStep 19876549 = 3726853) B3726853
theorem B1362641 : Blo 906576 1362641 := bstep (se 2 (by rfl) ⟨510990, by rfl⟩ : syracuseStep 1362641 = 1021981) B1021981
theorem B1362659 : Blo 906576 1362659 := bstep (se 1 (by rfl) ⟨1021994, by rfl⟩ : syracuseStep 1362659 = 2043989) B2043989
theorem B1362689 : Blo 906576 1362689 := bstep (se 2 (by rfl) ⟨511008, by rfl⟩ : syracuseStep 1362689 = 1022017) B1022017
theorem B1362707 : Blo 906576 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B1362737 : Blo 906576 1362737 := bstep (se 2 (by rfl) ⟨511026, by rfl⟩ : syracuseStep 1362737 = 1022053) B1022053
theorem B1362755 : Blo 906576 1362755 := bstep (se 1 (by rfl) ⟨1022066, by rfl⟩ : syracuseStep 1362755 = 2044133) B2044133
theorem B3681101 : Blo 906576 3681101 := bstep (se 3 (by rfl) ⟨690206, by rfl⟩ : syracuseStep 3681101 = 1380413) B1380413
theorem B2485073 : Blo 906576 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B1362785 : Blo 906576 1362785 := bstep (se 2 (by rfl) ⟨511044, by rfl⟩ : syracuseStep 1362785 = 1022089) B1022089
theorem B1362803 : Blo 906576 1362803 := bstep (se 1 (by rfl) ⟨1022102, by rfl⟩ : syracuseStep 1362803 = 2044205) B2044205
theorem B2329489 : Blo 906576 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1362833 : Blo 906576 1362833 := bstep (se 2 (by rfl) ⟨511062, by rfl⟩ : syracuseStep 1362833 = 1022125) B1022125
theorem B1362851 : Blo 906576 1362851 := bstep (se 1 (by rfl) ⟨1022138, by rfl⟩ : syracuseStep 1362851 = 2044277) B2044277
theorem B2042801 : Blo 906576 2042801 := bstep (se 2 (by rfl) ⟨766050, by rfl⟩ : syracuseStep 2042801 = 1532101) B1532101
theorem B2042819 : Blo 906576 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B5164145 : Blo 906576 5164145 := bstep (se 2 (by rfl) ⟨1936554, by rfl⟩ : syracuseStep 5164145 = 3873109) B3873109
theorem B4590755 : Blo 906576 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B3443917 : Blo 906576 3443917 := bstep (se 3 (by rfl) ⟨645734, by rfl⟩ : syracuseStep 3443917 = 1291469) B1291469
theorem B2043089 : Blo 906576 2043089 := bstep (se 2 (by rfl) ⟨766158, by rfl⟩ : syracuseStep 2043089 = 1532317) B1532317
theorem B2043107 : Blo 906576 2043107 := bstep (se 1 (by rfl) ⟨1532330, by rfl⟩ : syracuseStep 2043107 = 3064661) B3064661
theorem B1453313 : Blo 906576 1453313 := bstep (se 2 (by rfl) ⟨544992, by rfl⟩ : syracuseStep 1453313 = 1089985) B1089985
theorem B1936657 : Blo 906576 1936657 := bstep (se 2 (by rfl) ⟨726246, by rfl⟩ : syracuseStep 1936657 = 1452493) B1452493
theorem B970003 : Blo 906576 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B920851 : Blo 906576 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B2452835 : Blo 906576 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B5819789 : Blo 906576 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B7753157 : Blo 906576 7753157 := bstep (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) B1453717
theorem B3878371 : Blo 906576 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B2043377 : Blo 906576 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B2043395 : Blo 906576 2043395 := bstep (se 1 (by rfl) ⟨1532546, by rfl⟩ : syracuseStep 2043395 = 3065093) B3065093
theorem B2297393 : Blo 906576 2297393 := bstep (se 2 (by rfl) ⟨861522, by rfl⟩ : syracuseStep 2297393 = 1723045) B1723045
theorem B2297443 : Blo 906576 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B1724017 : Blo 906576 1724017 := bstep (se 2 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 1724017 = 1293013) B1293013
theorem B24850061 : Blo 906576 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B2584237 : Blo 906576 2584237 := bstep (se 3 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 2584237 = 969089) B969089
theorem B2297585 : Blo 906576 2297585 := bstep (se 2 (by rfl) ⟨861594, by rfl⟩ : syracuseStep 2297585 = 1723189) B1723189
theorem B2043665 : Blo 906576 2043665 := bstep (se 2 (by rfl) ⟨766374, by rfl⟩ : syracuseStep 2043665 = 1532749) B1532749
theorem B2043683 : Blo 906576 2043683 := bstep (se 1 (by rfl) ⟨1532762, by rfl⟩ : syracuseStep 2043683 = 3065525) B3065525
theorem B1380145 : Blo 906576 1380145 := bstep (se 2 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 1380145 = 1035109) B1035109
theorem B4599665 : Blo 906576 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B4591565 : Blo 906576 4591565 := bstep (se 3 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 4591565 = 1721837) B1721837
theorem B3444707 : Blo 906576 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B7761905 : Blo 906576 7761905 := bstep (se 2 (by rfl) ⟨2910714, by rfl⟩ : syracuseStep 7761905 = 5821429) B5821429
theorem B1724419 : Blo 906576 1724419 := bstep (se 1 (by rfl) ⟨1293314, by rfl⟩ : syracuseStep 1724419 = 2586629) B2586629
theorem B3059747 : Blo 906576 3059747 := bstep (se 1 (by rfl) ⟨2294810, by rfl⟩ : syracuseStep 3059747 = 4589621) B4589621
theorem B1724465 : Blo 906576 1724465 := bstep (se 2 (by rfl) ⟨646674, by rfl⟩ : syracuseStep 1724465 = 1293349) B1293349
theorem B2043953 : Blo 906576 2043953 := bstep (se 2 (by rfl) ⟨766482, by rfl⟩ : syracuseStep 2043953 = 1532965) B1532965
theorem B2043971 : Blo 906576 2043971 := bstep (se 1 (by rfl) ⟨1532978, by rfl⟩ : syracuseStep 2043971 = 3065957) B3065957
theorem B1020019 : Blo 906576 1020019 := bstep (se 1 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 1020019 = 1530029) B1530029
theorem B1020163 : Blo 906576 1020163 := bstep (se 1 (by rfl) ⟨765122, by rfl⟩ : syracuseStep 1020163 = 1530245) B1530245
theorem B7852301 : Blo 906576 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B2756909 : Blo 906576 2756909 := bstep (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) B1033841
theorem B3060017 : Blo 906576 3060017 := bstep (se 2 (by rfl) ⟨1147506, by rfl⟩ : syracuseStep 3060017 = 2295013) B2295013
theorem B1724753 : Blo 906576 1724753 := bstep (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) B1293565
theorem B2044241 : Blo 906576 2044241 := bstep (se 2 (by rfl) ⟨766590, by rfl⟩ : syracuseStep 2044241 = 1533181) B1533181
theorem B2044259 : Blo 906576 2044259 := bstep (se 1 (by rfl) ⟨1533194, by rfl⟩ : syracuseStep 2044259 = 3066389) B3066389
theorem B2068849 : Blo 906576 2068849 := bstep (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) B1551637
theorem B1020307 : Blo 906576 1020307 := bstep (se 1 (by rfl) ⟨765230, by rfl⟩ : syracuseStep 1020307 = 1530461) B1530461
theorem B17912261 : Blo 906576 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B14913989 : Blo 906576 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B6214157 : Blo 906576 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B5165603 : Blo 906576 5165603 := bstep (se 1 (by rfl) ⟨3874202, by rfl⟩ : syracuseStep 5165603 = 7748405) B7748405
theorem B1020451 : Blo 906576 1020451 := bstep (se 1 (by rfl) ⟨765338, by rfl⟩ : syracuseStep 1020451 = 1530677) B1530677
theorem B3445361 : Blo 906576 3445361 := bstep (se 2 (by rfl) ⟨1292010, by rfl⟩ : syracuseStep 3445361 = 2584021) B2584021
theorem B11629169 : Blo 906576 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B1020595 : Blo 906576 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B1225411 : Blo 906576 1225411 := bstep (se 1 (by rfl) ⟨919058, by rfl⟩ : syracuseStep 1225411 = 1838117) B1838117
theorem B2904781 : Blo 906576 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B2585297 : Blo 906576 2585297 := bstep (se 2 (by rfl) ⟨969486, by rfl⟩ : syracuseStep 2585297 = 1938973) B1938973
theorem B2298577 : Blo 906576 2298577 := bstep (se 2 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 2298577 = 1723933) B1723933
theorem B1938161 : Blo 906576 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1454851 : Blo 906576 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B1291025 : Blo 906576 1291025 := bstep (se 2 (by rfl) ⟨484134, by rfl⟩ : syracuseStep 1291025 = 968269) B968269
theorem B1454897 : Blo 906576 1454897 := bstep (se 2 (by rfl) ⟨545586, by rfl⟩ : syracuseStep 1454897 = 1091173) B1091173
theorem B1020739 : Blo 906576 1020739 := bstep (se 1 (by rfl) ⟨765554, by rfl⟩ : syracuseStep 1020739 = 1531109) B1531109
theorem B3060557 : Blo 906576 3060557 := bstep (se 3 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 3060557 = 1147709) B1147709
theorem B3060611 : Blo 906576 3060611 := bstep (se 1 (by rfl) ⟨2295458, by rfl⟩ : syracuseStep 3060611 = 4590917) B4590917
theorem B62813069 : Blo 906576 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B1381313 : Blo 906576 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B1020883 : Blo 906576 1020883 := bstep (se 1 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 1020883 = 1531325) B1531325
theorem B2298851 : Blo 906576 2298851 := bstep (se 1 (by rfl) ⟨1724138, by rfl⟩ : syracuseStep 2298851 = 3448277) B3448277
theorem B1021027 : Blo 906576 1021027 := bstep (se 1 (by rfl) ⟨765770, by rfl⟩ : syracuseStep 1021027 = 1531541) B1531541
theorem B2946179 : Blo 906576 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1938563 : Blo 906576 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B3060881 : Blo 906576 3060881 := bstep (se 2 (by rfl) ⟨1147830, by rfl⟩ : syracuseStep 3060881 = 2295661) B2295661
theorem B2299043 : Blo 906576 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B3273905 : Blo 906576 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B1635569 : Blo 906576 1635569 := bstep (se 2 (by rfl) ⟨613338, by rfl⟩ : syracuseStep 1635569 = 1226677) B1226677
theorem B1021171 : Blo 906576 1021171 := bstep (se 1 (by rfl) ⟨765878, by rfl⟩ : syracuseStep 1021171 = 1531757) B1531757
theorem B1226017 : Blo 906576 1226017 := bstep (se 2 (by rfl) ⟨459756, by rfl⟩ : syracuseStep 1226017 = 919513) B919513
theorem B1291555 : Blo 906576 1291555 := bstep (se 1 (by rfl) ⟨968666, by rfl⟩ : syracuseStep 1291555 = 1937333) B1937333
theorem B906579 : Blo 906576 906579 := bstep (se 1 (by rfl) ⟨679934, by rfl⟩ : syracuseStep 906579 = 1359869) B1359869
theorem B906595 : Blo 906576 906595 := bstep (se 1 (by rfl) ⟨679946, by rfl⟩ : syracuseStep 906595 = 1359893) B1359893
theorem B2585969 : Blo 906576 2585969 := bstep (se 2 (by rfl) ⟨969738, by rfl⟩ : syracuseStep 2585969 = 1939477) B1939477
theorem B906611 : Blo 906576 906611 := bstep (se 1 (by rfl) ⟨679958, by rfl⟩ : syracuseStep 906611 = 1359917) B1359917
theorem B906627 : Blo 906576 906627 := bstep (se 1 (by rfl) ⟨679970, by rfl⟩ : syracuseStep 906627 = 1359941) B1359941
theorem B1021315 : Blo 906576 1021315 := bstep (se 1 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 1021315 = 1531973) B1531973
theorem B906643 : Blo 906576 906643 := bstep (se 1 (by rfl) ⟨679982, by rfl⟩ : syracuseStep 906643 = 1359965) B1359965
theorem B906659 : Blo 906576 906659 := bstep (se 1 (by rfl) ⟨679994, by rfl⟩ : syracuseStep 906659 = 1359989) B1359989
theorem B906675 : Blo 906576 906675 := bstep (se 1 (by rfl) ⟨680006, by rfl⟩ : syracuseStep 906675 = 1360013) B1360013
theorem B906691 : Blo 906576 906691 := bstep (se 1 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 906691 = 1360037) B1360037
theorem B906707 : Blo 906576 906707 := bstep (se 1 (by rfl) ⟨680030, by rfl⟩ : syracuseStep 906707 = 1360061) B1360061
theorem B906723 : Blo 906576 906723 := bstep (se 1 (by rfl) ⟨680042, by rfl⟩ : syracuseStep 906723 = 1360085) B1360085
theorem B906739 : Blo 906576 906739 := bstep (se 1 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 906739 = 1360109) B1360109
theorem B906755 : Blo 906576 906755 := bstep (se 1 (by rfl) ⟨680066, by rfl⟩ : syracuseStep 906755 = 1360133) B1360133
theorem B5813765 : Blo 906576 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B5166605 : Blo 906576 5166605 := bstep (se 3 (by rfl) ⟨968738, by rfl⟩ : syracuseStep 5166605 = 1937477) B1937477
theorem B906771 : Blo 906576 906771 := bstep (se 1 (by rfl) ⟨680078, by rfl⟩ : syracuseStep 906771 = 1360157) B1360157
theorem B1021459 : Blo 906576 1021459 := bstep (se 1 (by rfl) ⟨766094, by rfl⟩ : syracuseStep 1021459 = 1532189) B1532189
theorem B906787 : Blo 906576 906787 := bstep (se 1 (by rfl) ⟨680090, by rfl⟩ : syracuseStep 906787 = 1360181) B1360181
theorem B906803 : Blo 906576 906803 := bstep (se 1 (by rfl) ⟨680102, by rfl⟩ : syracuseStep 906803 = 1360205) B1360205
theorem B906819 : Blo 906576 906819 := bstep (se 1 (by rfl) ⟨680114, by rfl⟩ : syracuseStep 906819 = 1360229) B1360229
theorem B906835 : Blo 906576 906835 := bstep (se 1 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 906835 = 1360253) B1360253
theorem B906851 : Blo 906576 906851 := bstep (se 1 (by rfl) ⟨680138, by rfl⟩ : syracuseStep 906851 = 1360277) B1360277
theorem B906867 : Blo 906576 906867 := bstep (se 1 (by rfl) ⟨680150, by rfl⟩ : syracuseStep 906867 = 1360301) B1360301
theorem B1291891 : Blo 906576 1291891 := bstep (se 1 (by rfl) ⟨968918, by rfl⟩ : syracuseStep 1291891 = 1937837) B1937837
theorem B906883 : Blo 906576 906883 := bstep (se 1 (by rfl) ⟨680162, by rfl⟩ : syracuseStep 906883 = 1360325) B1360325
theorem B906899 : Blo 906576 906899 := bstep (se 1 (by rfl) ⟨680174, by rfl⟩ : syracuseStep 906899 = 1360349) B1360349
theorem B906915 : Blo 906576 906915 := bstep (se 1 (by rfl) ⟨680186, by rfl⟩ : syracuseStep 906915 = 1360373) B1360373
theorem B1021603 : Blo 906576 1021603 := bstep (se 1 (by rfl) ⟨766202, by rfl⟩ : syracuseStep 1021603 = 1532405) B1532405
theorem B3061421 : Blo 906576 3061421 := bstep (se 3 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 3061421 = 1148033) B1148033
theorem B906931 : Blo 906576 906931 := bstep (se 1 (by rfl) ⟨680198, by rfl⟩ : syracuseStep 906931 = 1360397) B1360397
theorem B906947 : Blo 906576 906947 := bstep (se 1 (by rfl) ⟨680210, by rfl⟩ : syracuseStep 906947 = 1360421) B1360421
theorem B2455235 : Blo 906576 2455235 := bstep (se 1 (by rfl) ⟨1841426, by rfl⟩ : syracuseStep 2455235 = 3682853) B3682853
theorem B906963 : Blo 906576 906963 := bstep (se 1 (by rfl) ⟨680222, by rfl⟩ : syracuseStep 906963 = 1360445) B1360445
theorem B906979 : Blo 906576 906979 := bstep (se 1 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 906979 = 1360469) B1360469
theorem B18618083 : Blo 906576 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B3061475 : Blo 906576 3061475 := bstep (se 1 (by rfl) ⟨2296106, by rfl⟩ : syracuseStep 3061475 = 4592213) B4592213
theorem B906995 : Blo 906576 906995 := bstep (se 1 (by rfl) ⟨680246, by rfl⟩ : syracuseStep 906995 = 1360493) B1360493
theorem B907011 : Blo 906576 907011 := bstep (se 1 (by rfl) ⟨680258, by rfl⟩ : syracuseStep 907011 = 1360517) B1360517
theorem B907027 : Blo 906576 907027 := bstep (se 1 (by rfl) ⟨680270, by rfl⟩ : syracuseStep 907027 = 1360541) B1360541
theorem B907043 : Blo 906576 907043 := bstep (se 1 (by rfl) ⟨680282, by rfl⟩ : syracuseStep 907043 = 1360565) B1360565
theorem B907059 : Blo 906576 907059 := bstep (se 1 (by rfl) ⟨680294, by rfl⟩ : syracuseStep 907059 = 1360589) B1360589
theorem B1021747 : Blo 906576 1021747 := bstep (se 1 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 1021747 = 1532621) B1532621
theorem B907075 : Blo 906576 907075 := bstep (se 1 (by rfl) ⟨680306, by rfl⟩ : syracuseStep 907075 = 1360613) B1360613
theorem B907091 : Blo 906576 907091 := bstep (se 1 (by rfl) ⟨680318, by rfl⟩ : syracuseStep 907091 = 1360637) B1360637
theorem B907107 : Blo 906576 907107 := bstep (se 1 (by rfl) ⟨680330, by rfl⟩ : syracuseStep 907107 = 1360661) B1360661
theorem B20936561 : Blo 906576 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B3880817 : Blo 906576 3880817 := bstep (se 2 (by rfl) ⟨1455306, by rfl⟩ : syracuseStep 3880817 = 2910613) B2910613
theorem B907123 : Blo 906576 907123 := bstep (se 1 (by rfl) ⟨680342, by rfl⟩ : syracuseStep 907123 = 1360685) B1360685
theorem B907139 : Blo 906576 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B907155 : Blo 906576 907155 := bstep (se 1 (by rfl) ⟨680366, by rfl⟩ : syracuseStep 907155 = 1360733) B1360733
theorem B907171 : Blo 906576 907171 := bstep (se 1 (by rfl) ⟨680378, by rfl⟩ : syracuseStep 907171 = 1360757) B1360757
theorem B907187 : Blo 906576 907187 := bstep (se 1 (by rfl) ⟨680390, by rfl⟩ : syracuseStep 907187 = 1360781) B1360781
theorem B907203 : Blo 906576 907203 := bstep (se 1 (by rfl) ⟨680402, by rfl⟩ : syracuseStep 907203 = 1360805) B1360805
theorem B1021891 : Blo 906576 1021891 := bstep (se 1 (by rfl) ⟨766418, by rfl⟩ : syracuseStep 1021891 = 1532837) B1532837
theorem B907219 : Blo 906576 907219 := bstep (se 1 (by rfl) ⟨680414, by rfl⟩ : syracuseStep 907219 = 1360829) B1360829
theorem B907235 : Blo 906576 907235 := bstep (se 1 (by rfl) ⟨680426, by rfl⟩ : syracuseStep 907235 = 1360853) B1360853
theorem B3061745 : Blo 906576 3061745 := bstep (se 2 (by rfl) ⟨1148154, by rfl⟩ : syracuseStep 3061745 = 2296309) B2296309
theorem B907251 : Blo 906576 907251 := bstep (se 1 (by rfl) ⟨680438, by rfl⟩ : syracuseStep 907251 = 1360877) B1360877
theorem B907267 : Blo 906576 907267 := bstep (se 1 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 907267 = 1360901) B1360901
theorem B1939459 : Blo 906576 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B907283 : Blo 906576 907283 := bstep (se 1 (by rfl) ⟨680462, by rfl⟩ : syracuseStep 907283 = 1360925) B1360925
theorem B907299 : Blo 906576 907299 := bstep (se 1 (by rfl) ⟨680474, by rfl⟩ : syracuseStep 907299 = 1360949) B1360949
theorem B3446819 : Blo 906576 3446819 := bstep (se 1 (by rfl) ⟨2585114, by rfl⟩ : syracuseStep 3446819 = 5170229) B5170229
theorem B3446833 : Blo 906576 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B907315 : Blo 906576 907315 := bstep (se 1 (by rfl) ⟨680486, by rfl⟩ : syracuseStep 907315 = 1360973) B1360973
theorem B1529921 : Blo 906576 1529921 := bstep (se 2 (by rfl) ⟨573720, by rfl⟩ : syracuseStep 1529921 = 1147441) B1147441
theorem B907331 : Blo 906576 907331 := bstep (se 1 (by rfl) ⟨680498, by rfl⟩ : syracuseStep 907331 = 1360997) B1360997
theorem B907347 : Blo 906576 907347 := bstep (se 1 (by rfl) ⟨680510, by rfl⟩ : syracuseStep 907347 = 1361021) B1361021
theorem B1022035 : Blo 906576 1022035 := bstep (se 1 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 1022035 = 1533053) B1533053
theorem B907363 : Blo 906576 907363 := bstep (se 1 (by rfl) ⟨680522, by rfl⟩ : syracuseStep 907363 = 1361045) B1361045
theorem B13080689 : Blo 906576 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B907379 : Blo 906576 907379 := bstep (se 1 (by rfl) ⟨680534, by rfl⟩ : syracuseStep 907379 = 1361069) B1361069
theorem B2906243 : Blo 906576 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B907395 : Blo 906576 907395 := bstep (se 1 (by rfl) ⟨680546, by rfl⟩ : syracuseStep 907395 = 1361093) B1361093
theorem B2586755 : Blo 906576 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B17463437 : Blo 906576 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B907411 : Blo 906576 907411 := bstep (se 1 (by rfl) ⟨680558, by rfl⟩ : syracuseStep 907411 = 1361117) B1361117
theorem B1292449 : Blo 906576 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B907427 : Blo 906576 907427 := bstep (se 1 (by rfl) ⟨680570, by rfl⟩ : syracuseStep 907427 = 1361141) B1361141
theorem B1841329 : Blo 906576 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B907443 : Blo 906576 907443 := bstep (se 1 (by rfl) ⟨680582, by rfl⟩ : syracuseStep 907443 = 1361165) B1361165
theorem B1530049 : Blo 906576 1530049 := bstep (se 2 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 1530049 = 1147537) B1147537
theorem B907459 : Blo 906576 907459 := bstep (se 1 (by rfl) ⟨680594, by rfl⟩ : syracuseStep 907459 = 1361189) B1361189
theorem B1292483 : Blo 906576 1292483 := bstep (se 1 (by rfl) ⟨969362, by rfl⟩ : syracuseStep 1292483 = 1938725) B1938725
theorem B907475 : Blo 906576 907475 := bstep (se 1 (by rfl) ⟨680606, by rfl⟩ : syracuseStep 907475 = 1361213) B1361213
theorem B1530083 : Blo 906576 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B907491 : Blo 906576 907491 := bstep (se 1 (by rfl) ⟨680618, by rfl⟩ : syracuseStep 907491 = 1361237) B1361237
theorem B907507 : Blo 906576 907507 := bstep (se 1 (by rfl) ⟨680630, by rfl⟩ : syracuseStep 907507 = 1361261) B1361261
theorem B907523 : Blo 906576 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B907539 : Blo 906576 907539 := bstep (se 1 (by rfl) ⟨680654, by rfl⟩ : syracuseStep 907539 = 1361309) B1361309
theorem B907555 : Blo 906576 907555 := bstep (se 1 (by rfl) ⟨680666, by rfl⟩ : syracuseStep 907555 = 1361333) B1361333
theorem B907571 : Blo 906576 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B907587 : Blo 906576 907587 := bstep (se 1 (by rfl) ⟨680690, by rfl⟩ : syracuseStep 907587 = 1361381) B1361381
theorem B8730949 : Blo 906576 8730949 := bstep (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) B1637053
theorem B907603 : Blo 906576 907603 := bstep (se 1 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 907603 = 1361405) B1361405
theorem B1530211 : Blo 906576 1530211 := bstep (se 1 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 1530211 = 2295317) B2295317
theorem B907619 : Blo 906576 907619 := bstep (se 1 (by rfl) ⟨680714, by rfl⟩ : syracuseStep 907619 = 1361429) B1361429
theorem B1309043 : Blo 906576 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B907635 : Blo 906576 907635 := bstep (se 1 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 907635 = 1361453) B1361453
theorem B907651 : Blo 906576 907651 := bstep (se 1 (by rfl) ⟨680738, by rfl⟩ : syracuseStep 907651 = 1361477) B1361477
theorem B2906513 : Blo 906576 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B907667 : Blo 906576 907667 := bstep (se 1 (by rfl) ⟨680750, by rfl⟩ : syracuseStep 907667 = 1361501) B1361501
theorem B907683 : Blo 906576 907683 := bstep (se 1 (by rfl) ⟨680762, by rfl⟩ : syracuseStep 907683 = 1361525) B1361525
theorem B2070947 : Blo 906576 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B907699 : Blo 906576 907699 := bstep (se 1 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 907699 = 1361549) B1361549
theorem B907715 : Blo 906576 907715 := bstep (se 1 (by rfl) ⟨680786, by rfl⟩ : syracuseStep 907715 = 1361573) B1361573
theorem B2587085 : Blo 906576 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B907731 : Blo 906576 907731 := bstep (se 1 (by rfl) ⟨680798, by rfl⟩ : syracuseStep 907731 = 1361597) B1361597
theorem B907747 : Blo 906576 907747 := bstep (se 1 (by rfl) ⟨680810, by rfl⟩ : syracuseStep 907747 = 1361621) B1361621
theorem B1530353 : Blo 906576 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B907763 : Blo 906576 907763 := bstep (se 1 (by rfl) ⟨680822, by rfl⟩ : syracuseStep 907763 = 1361645) B1361645
theorem B907779 : Blo 906576 907779 := bstep (se 1 (by rfl) ⟨680834, by rfl⟩ : syracuseStep 907779 = 1361669) B1361669
theorem B3062285 : Blo 906576 3062285 := bstep (se 3 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 3062285 = 1148357) B1148357
theorem B2587153 : Blo 906576 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B907795 : Blo 906576 907795 := bstep (se 1 (by rfl) ⟨680846, by rfl⟩ : syracuseStep 907795 = 1361693) B1361693
theorem B907811 : Blo 906576 907811 := bstep (se 1 (by rfl) ⟨680858, by rfl⟩ : syracuseStep 907811 = 1361717) B1361717
theorem B907827 : Blo 906576 907827 := bstep (se 1 (by rfl) ⟨680870, by rfl⟩ : syracuseStep 907827 = 1361741) B1361741
theorem B3062339 : Blo 906576 3062339 := bstep (se 1 (by rfl) ⟨2296754, by rfl⟩ : syracuseStep 3062339 = 4593509) B4593509
theorem B907843 : Blo 906576 907843 := bstep (se 1 (by rfl) ⟨680882, by rfl⟩ : syracuseStep 907843 = 1361765) B1361765
theorem B907859 : Blo 906576 907859 := bstep (se 1 (by rfl) ⟨680894, by rfl⟩ : syracuseStep 907859 = 1361789) B1361789
theorem B907875 : Blo 906576 907875 := bstep (se 1 (by rfl) ⟨680906, by rfl⟩ : syracuseStep 907875 = 1361813) B1361813
theorem B1530481 : Blo 906576 1530481 := bstep (se 2 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 1530481 = 1147861) B1147861
theorem B907891 : Blo 906576 907891 := bstep (se 1 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 907891 = 1361837) B1361837
theorem B1964675 : Blo 906576 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B907907 : Blo 906576 907907 := bstep (se 1 (by rfl) ⟨680930, by rfl⟩ : syracuseStep 907907 = 1361861) B1361861
theorem B6888077 : Blo 906576 6888077 := bstep (se 3 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 6888077 = 2583029) B2583029
theorem B1530515 : Blo 906576 1530515 := bstep (se 1 (by rfl) ⟨1147886, by rfl⟩ : syracuseStep 1530515 = 2295773) B2295773
theorem B907923 : Blo 906576 907923 := bstep (se 1 (by rfl) ⟨680942, by rfl⟩ : syracuseStep 907923 = 1361885) B1361885
theorem B907939 : Blo 906576 907939 := bstep (se 1 (by rfl) ⟨680954, by rfl⟩ : syracuseStep 907939 = 1361909) B1361909
theorem B907955 : Blo 906576 907955 := bstep (se 1 (by rfl) ⟨680966, by rfl⟩ : syracuseStep 907955 = 1361933) B1361933
theorem B907971 : Blo 906576 907971 := bstep (se 1 (by rfl) ⟨680978, by rfl⟩ : syracuseStep 907971 = 1361957) B1361957
theorem B907987 : Blo 906576 907987 := bstep (se 1 (by rfl) ⟨680990, by rfl⟩ : syracuseStep 907987 = 1361981) B1361981
theorem B908003 : Blo 906576 908003 := bstep (se 1 (by rfl) ⟨681002, by rfl⟩ : syracuseStep 908003 = 1362005) B1362005
theorem B1293041 : Blo 906576 1293041 := bstep (se 2 (by rfl) ⟨484890, by rfl⟩ : syracuseStep 1293041 = 969781) B969781
theorem B908019 : Blo 906576 908019 := bstep (se 1 (by rfl) ⟨681014, by rfl⟩ : syracuseStep 908019 = 1362029) B1362029
theorem B908035 : Blo 906576 908035 := bstep (se 1 (by rfl) ⟨681026, by rfl⟩ : syracuseStep 908035 = 1362053) B1362053
theorem B1530643 : Blo 906576 1530643 := bstep (se 1 (by rfl) ⟨1147982, by rfl⟩ : syracuseStep 1530643 = 2295965) B2295965
theorem B908051 : Blo 906576 908051 := bstep (se 1 (by rfl) ⟨681038, by rfl⟩ : syracuseStep 908051 = 1362077) B1362077
theorem B908067 : Blo 906576 908067 := bstep (se 1 (by rfl) ⟨681050, by rfl⟩ : syracuseStep 908067 = 1362101) B1362101
theorem B4594481 : Blo 906576 4594481 := bstep (se 2 (by rfl) ⟨1722930, by rfl⟩ : syracuseStep 4594481 = 3445861) B3445861
theorem B908083 : Blo 906576 908083 := bstep (se 1 (by rfl) ⟨681062, by rfl⟩ : syracuseStep 908083 = 1362125) B1362125
theorem B1293121 : Blo 906576 1293121 := bstep (se 2 (by rfl) ⟨484920, by rfl⟩ : syracuseStep 1293121 = 969841) B969841
theorem B908099 : Blo 906576 908099 := bstep (se 1 (by rfl) ⟨681074, by rfl⟩ : syracuseStep 908099 = 1362149) B1362149
theorem B3062609 : Blo 906576 3062609 := bstep (se 2 (by rfl) ⟨1148478, by rfl⟩ : syracuseStep 3062609 = 2296957) B2296957
theorem B908115 : Blo 906576 908115 := bstep (se 1 (by rfl) ⟨681086, by rfl⟩ : syracuseStep 908115 = 1362173) B1362173
theorem B908131 : Blo 906576 908131 := bstep (se 1 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 908131 = 1362197) B1362197
theorem B908147 : Blo 906576 908147 := bstep (se 1 (by rfl) ⟨681110, by rfl⟩ : syracuseStep 908147 = 1362221) B1362221
theorem B908163 : Blo 906576 908163 := bstep (se 1 (by rfl) ⟨681122, by rfl⟩ : syracuseStep 908163 = 1362245) B1362245
theorem B908179 : Blo 906576 908179 := bstep (se 1 (by rfl) ⟨681134, by rfl⟩ : syracuseStep 908179 = 1362269) B1362269
theorem B1530785 : Blo 906576 1530785 := bstep (se 2 (by rfl) ⟨574044, by rfl⟩ : syracuseStep 1530785 = 1148089) B1148089
theorem B908195 : Blo 906576 908195 := bstep (se 1 (by rfl) ⟨681146, by rfl⟩ : syracuseStep 908195 = 1362293) B1362293
theorem B908211 : Blo 906576 908211 := bstep (se 1 (by rfl) ⟨681158, by rfl⟩ : syracuseStep 908211 = 1362317) B1362317
theorem B908227 : Blo 906576 908227 := bstep (se 1 (by rfl) ⟨681170, by rfl⟩ : syracuseStep 908227 = 1362341) B1362341
theorem B3267533 : Blo 906576 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B908243 : Blo 906576 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B908259 : Blo 906576 908259 := bstep (se 1 (by rfl) ⟨681194, by rfl⟩ : syracuseStep 908259 = 1362389) B1362389
theorem B908275 : Blo 906576 908275 := bstep (se 1 (by rfl) ⟨681206, by rfl⟩ : syracuseStep 908275 = 1362413) B1362413
theorem B908291 : Blo 906576 908291 := bstep (se 1 (by rfl) ⟨681218, by rfl⟩ : syracuseStep 908291 = 1362437) B1362437
theorem B908307 : Blo 906576 908307 := bstep (se 1 (by rfl) ⟨681230, by rfl⟩ : syracuseStep 908307 = 1362461) B1362461
theorem B1530913 : Blo 906576 1530913 := bstep (se 2 (by rfl) ⟨574092, by rfl⟩ : syracuseStep 1530913 = 1148185) B1148185
theorem B908323 : Blo 906576 908323 := bstep (se 1 (by rfl) ⟨681242, by rfl⟩ : syracuseStep 908323 = 1362485) B1362485
theorem B908339 : Blo 906576 908339 := bstep (se 1 (by rfl) ⟨681254, by rfl⟩ : syracuseStep 908339 = 1362509) B1362509
theorem B1530947 : Blo 906576 1530947 := bstep (se 1 (by rfl) ⟨1148210, by rfl⟩ : syracuseStep 1530947 = 2296421) B2296421
theorem B908355 : Blo 906576 908355 := bstep (se 1 (by rfl) ⟨681266, by rfl⟩ : syracuseStep 908355 = 1362533) B1362533
theorem B908371 : Blo 906576 908371 := bstep (se 1 (by rfl) ⟨681278, by rfl⟩ : syracuseStep 908371 = 1362557) B1362557
theorem B932963 : Blo 906576 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B908387 : Blo 906576 908387 := bstep (se 1 (by rfl) ⟨681290, by rfl⟩ : syracuseStep 908387 = 1362581) B1362581
theorem B908403 : Blo 906576 908403 := bstep (se 1 (by rfl) ⟨681302, by rfl⟩ : syracuseStep 908403 = 1362605) B1362605
theorem B908419 : Blo 906576 908419 := bstep (se 1 (by rfl) ⟨681314, by rfl⟩ : syracuseStep 908419 = 1362629) B1362629
theorem B11041933 : Blo 906576 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B908435 : Blo 906576 908435 := bstep (se 1 (by rfl) ⟨681326, by rfl⟩ : syracuseStep 908435 = 1362653) B1362653
theorem B908451 : Blo 906576 908451 := bstep (se 1 (by rfl) ⟨681338, by rfl⟩ : syracuseStep 908451 = 1362677) B1362677
theorem B908467 : Blo 906576 908467 := bstep (se 1 (by rfl) ⟨681350, by rfl⟩ : syracuseStep 908467 = 1362701) B1362701
theorem B1531075 : Blo 906576 1531075 := bstep (se 1 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 1531075 = 2296613) B2296613
theorem B908483 : Blo 906576 908483 := bstep (se 1 (by rfl) ⟨681362, by rfl⟩ : syracuseStep 908483 = 1362725) B1362725
theorem B3873997 : Blo 906576 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B908499 : Blo 906576 908499 := bstep (se 1 (by rfl) ⟨681374, by rfl⟩ : syracuseStep 908499 = 1362749) B1362749
theorem B908515 : Blo 906576 908515 := bstep (se 1 (by rfl) ⟨681386, by rfl⟩ : syracuseStep 908515 = 1362773) B1362773
theorem B908531 : Blo 906576 908531 := bstep (se 1 (by rfl) ⟨681398, by rfl⟩ : syracuseStep 908531 = 1362797) B1362797
theorem B908547 : Blo 906576 908547 := bstep (se 1 (by rfl) ⟨681410, by rfl⟩ : syracuseStep 908547 = 1362821) B1362821
theorem B908563 : Blo 906576 908563 := bstep (se 1 (by rfl) ⟨681422, by rfl⟩ : syracuseStep 908563 = 1362845) B1362845
theorem B1531217 : Blo 906576 1531217 := bstep (se 2 (by rfl) ⟨574206, by rfl⟩ : syracuseStep 1531217 = 1148413) B1148413
theorem B2071889 : Blo 906576 2071889 := bstep (se 2 (by rfl) ⟨776958, by rfl⟩ : syracuseStep 2071889 = 1553917) B1553917
theorem B3063149 : Blo 906576 3063149 := bstep (se 3 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 3063149 = 1148681) B1148681
theorem B3063203 : Blo 906576 3063203 := bstep (se 1 (by rfl) ⟨2297402, by rfl⟩ : syracuseStep 3063203 = 4594805) B4594805
theorem B1531345 : Blo 906576 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B9567715 : Blo 906576 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B3448291 : Blo 906576 3448291 := bstep (se 1 (by rfl) ⟨2586218, by rfl⟩ : syracuseStep 3448291 = 5172437) B5172437
theorem B1531379 : Blo 906576 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B1531507 : Blo 906576 1531507 := bstep (se 1 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 1531507 = 2297261) B2297261
theorem B1474195 : Blo 906576 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B3063473 : Blo 906576 3063473 := bstep (se 2 (by rfl) ⟨1148802, by rfl⟩ : syracuseStep 3063473 = 2297605) B2297605
theorem B3784369 : Blo 906576 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B1531649 : Blo 906576 1531649 := bstep (se 2 (by rfl) ⟨574368, by rfl⟩ : syracuseStep 1531649 = 1148737) B1148737
theorem B3677987 : Blo 906576 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B6209315 : Blo 906576 6209315 := bstep (se 1 (by rfl) ⟨4656986, by rfl⟩ : syracuseStep 6209315 = 9313973) B9313973
theorem B1089331 : Blo 906576 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B1531777 : Blo 906576 1531777 := bstep (se 2 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 1531777 = 1148833) B1148833
theorem B1531811 : Blo 906576 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B2039831 : Blo 906576 2039831 := bstep (se 1 (by rfl) ⟨1529873, by rfl⟩ : syracuseStep 2039831 = 3059747) B3059747
theorem B19890211 : Blo 906576 19890211 := bstep (se 1 (by rfl) ⟨14917658, by rfl⟩ : syracuseStep 19890211 = 29835317) B29835317
theorem B4595777 : Blo 906576 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B1359947 : Blo 906576 1359947 := bstep (se 1 (by rfl) ⟨1019960, by rfl⟩ : syracuseStep 1359947 = 2039921) B2039921
theorem B1359959 : Blo 906576 1359959 := bstep (se 1 (by rfl) ⟨1019969, by rfl⟩ : syracuseStep 1359959 = 2039939) B2039939
theorem B1531993 : Blo 906576 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B3063959 : Blo 906576 3063959 := bstep (se 1 (by rfl) ⟨2297969, by rfl⟩ : syracuseStep 3063959 = 4595939) B4595939
theorem B1360025 : Blo 906576 1360025 := bstep (se 2 (by rfl) ⟨510009, by rfl⟩ : syracuseStep 1360025 = 1020019) B1020019
theorem B5234867 : Blo 906576 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B2040011 : Blo 906576 2040011 := bstep (se 1 (by rfl) ⟨1530008, by rfl⟩ : syracuseStep 2040011 = 3060017) B3060017
theorem B2040065 : Blo 906576 2040065 := bstep (se 2 (by rfl) ⟨765024, by rfl⟩ : syracuseStep 2040065 = 1530049) B1530049
theorem B1360139 : Blo 906576 1360139 := bstep (se 1 (by rfl) ⟨1020104, by rfl⟩ : syracuseStep 1360139 = 2040209) B2040209
theorem B1360151 : Blo 906576 1360151 := bstep (se 1 (by rfl) ⟨1020113, by rfl⟩ : syracuseStep 1360151 = 2040227) B2040227
theorem B1360217 : Blo 906576 1360217 := bstep (se 2 (by rfl) ⟨510081, by rfl⟩ : syracuseStep 1360217 = 1020163) B1020163
theorem B10338677 : Blo 906576 10338677 := bstep (se 5 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 10338677 = 969251) B969251
theorem B11641265 : Blo 906576 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B1360331 : Blo 906576 1360331 := bstep (se 1 (by rfl) ⟨1020248, by rfl⟩ : syracuseStep 1360331 = 2040497) B2040497
theorem B1360343 : Blo 906576 1360343 := bstep (se 1 (by rfl) ⟨1020257, by rfl⟩ : syracuseStep 1360343 = 2040515) B2040515
theorem B2040281 : Blo 906576 2040281 := bstep (se 2 (by rfl) ⟨765105, by rfl⟩ : syracuseStep 2040281 = 1530211) B1530211
theorem B1360409 : Blo 906576 1360409 := bstep (se 2 (by rfl) ⟨510153, by rfl⟩ : syracuseStep 1360409 = 1020307) B1020307
theorem B2040371 : Blo 906576 2040371 := bstep (se 1 (by rfl) ⟨1530278, by rfl⟩ : syracuseStep 2040371 = 3060557) B3060557
theorem B2040407 : Blo 906576 2040407 := bstep (se 1 (by rfl) ⟨1530305, by rfl⟩ : syracuseStep 2040407 = 3060611) B3060611
theorem B1770113 : Blo 906576 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B1360523 : Blo 906576 1360523 := bstep (se 1 (by rfl) ⟨1020392, by rfl⟩ : syracuseStep 1360523 = 2040785) B2040785
theorem B1360535 : Blo 906576 1360535 := bstep (se 1 (by rfl) ⟨1020401, by rfl⟩ : syracuseStep 1360535 = 2040803) B2040803
theorem B1532567 : Blo 906576 1532567 := bstep (se 1 (by rfl) ⟨1149425, by rfl⟩ : syracuseStep 1532567 = 2298851) B2298851
theorem B3875501 : Blo 906576 3875501 := bstep (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) B1453313
theorem B3064499 : Blo 906576 3064499 := bstep (se 1 (by rfl) ⟨2298374, by rfl⟩ : syracuseStep 3064499 = 4596749) B4596749
theorem B3449537 : Blo 906576 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B1360601 : Blo 906576 1360601 := bstep (se 2 (by rfl) ⟨510225, by rfl⟩ : syracuseStep 1360601 = 1020451) B1020451
theorem B2040587 : Blo 906576 2040587 := bstep (se 1 (by rfl) ⟨1530440, by rfl⟩ : syracuseStep 2040587 = 3060881) B3060881
theorem B1532695 : Blo 906576 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B2040641 : Blo 906576 2040641 := bstep (se 2 (by rfl) ⟨765240, by rfl⟩ : syracuseStep 2040641 = 1530481) B1530481
theorem B1360715 : Blo 906576 1360715 := bstep (se 1 (by rfl) ⟨1020536, by rfl⟩ : syracuseStep 1360715 = 2041073) B2041073
theorem B1090379 : Blo 906576 1090379 := bstep (se 1 (by rfl) ⟨817784, by rfl⟩ : syracuseStep 1090379 = 1635569) B1635569
theorem B1360727 : Blo 906576 1360727 := bstep (se 1 (by rfl) ⟨1020545, by rfl⟩ : syracuseStep 1360727 = 2041091) B2041091
theorem B22397795 : Blo 906576 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B1360793 : Blo 906576 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B26502065 : Blo 906576 26502065 := bstep (se 2 (by rfl) ⟨9938274, by rfl⟩ : syracuseStep 26502065 = 19876549) B19876549
theorem B3064769 : Blo 906576 3064769 := bstep (se 2 (by rfl) ⟨1149288, by rfl⟩ : syracuseStep 3064769 = 2298577) B2298577
theorem B3490781 : Blo 906576 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B3875843 : Blo 906576 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B1360907 : Blo 906576 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B1147927 : Blo 906576 1147927 := bstep (se 1 (by rfl) ⟨860945, by rfl⟩ : syracuseStep 1147927 = 1721891) B1721891
theorem B2040857 : Blo 906576 2040857 := bstep (se 2 (by rfl) ⟨765321, by rfl⟩ : syracuseStep 2040857 = 1530643) B1530643
theorem B1360919 : Blo 906576 1360919 := bstep (se 1 (by rfl) ⟨1020689, by rfl⟩ : syracuseStep 1360919 = 2041379) B2041379
theorem B1360985 : Blo 906576 1360985 := bstep (se 2 (by rfl) ⟨510369, by rfl⟩ : syracuseStep 1360985 = 1020739) B1020739
theorem B5522525 : Blo 906576 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B2040947 : Blo 906576 2040947 := bstep (se 1 (by rfl) ⟨1530710, by rfl⟩ : syracuseStep 2040947 = 3061421) B3061421
theorem B12412055 : Blo 906576 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B2040983 : Blo 906576 2040983 := bstep (se 1 (by rfl) ⟨1530737, by rfl⟩ : syracuseStep 2040983 = 3061475) B3061475
theorem B2294963 : Blo 906576 2294963 := bstep (se 1 (by rfl) ⟨1721222, by rfl⟩ : syracuseStep 2294963 = 3442445) B3442445
theorem B223323317 : Blo 906576 223323317 := bstep (se 5 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 223323317 = 20936561) B20936561
theorem B3105985 : Blo 906576 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B1361099 : Blo 906576 1361099 := bstep (se 1 (by rfl) ⟨1020824, by rfl⟩ : syracuseStep 1361099 = 2041649) B2041649
theorem B1361111 : Blo 906576 1361111 := bstep (se 1 (by rfl) ⟨1020833, by rfl⟩ : syracuseStep 1361111 = 2041667) B2041667
theorem B6980825 : Blo 906576 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1721587 : Blo 906576 1721587 := bstep (se 1 (by rfl) ⟨1291190, by rfl⟩ : syracuseStep 1721587 = 2582381) B2582381
theorem B1361177 : Blo 906576 1361177 := bstep (se 2 (by rfl) ⟨510441, by rfl⟩ : syracuseStep 1361177 = 1020883) B1020883
theorem B2041163 : Blo 906576 2041163 := bstep (se 1 (by rfl) ⟨1530872, by rfl⟩ : syracuseStep 2041163 = 3061745) B3061745
theorem B2041217 : Blo 906576 2041217 := bstep (se 2 (by rfl) ⟨765456, by rfl⟩ : syracuseStep 2041217 = 1530913) B1530913
theorem B1361291 : Blo 906576 1361291 := bstep (se 1 (by rfl) ⟨1020968, by rfl⟩ : syracuseStep 1361291 = 2041937) B2041937
theorem B26142101 : Blo 906576 26142101 := bstep (se 6 (by rfl) ⟨612705, by rfl⟩ : syracuseStep 26142101 = 1225411) B1225411
theorem B1361303 : Blo 906576 1361303 := bstep (se 1 (by rfl) ⟨1020977, by rfl⟩ : syracuseStep 1361303 = 2041955) B2041955
theorem B11642291 : Blo 906576 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B2328011 : Blo 906576 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B1361369 : Blo 906576 1361369 := bstep (se 2 (by rfl) ⟨510513, by rfl⟩ : syracuseStep 1361369 = 1021027) B1021027
theorem B3065309 : Blo 906576 3065309 := bstep (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) B1149491
theorem B15926797 : Blo 906576 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B14722577 : Blo 906576 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B1361483 : Blo 906576 1361483 := bstep (se 1 (by rfl) ⟨1021112, by rfl⟩ : syracuseStep 1361483 = 2042225) B2042225
theorem B1361495 : Blo 906576 1361495 := bstep (se 1 (by rfl) ⟨1021121, by rfl⟩ : syracuseStep 1361495 = 2042243) B2042243
theorem B2041433 : Blo 906576 2041433 := bstep (se 2 (by rfl) ⟨765537, by rfl⟩ : syracuseStep 2041433 = 1531075) B1531075
theorem B1361561 : Blo 906576 1361561 := bstep (se 2 (by rfl) ⟨510585, by rfl⟩ : syracuseStep 1361561 = 1021171) B1021171
theorem B1722035 : Blo 906576 1722035 := bstep (se 1 (by rfl) ⟨1291526, by rfl⟩ : syracuseStep 1722035 = 2583053) B2583053
theorem B2041523 : Blo 906576 2041523 := bstep (se 1 (by rfl) ⟨1531142, by rfl⟩ : syracuseStep 2041523 = 3062285) B3062285
theorem B2582209 : Blo 906576 2582209 := bstep (se 2 (by rfl) ⟨968328, by rfl⟩ : syracuseStep 2582209 = 1936657) B1936657
theorem B2295499 : Blo 906576 2295499 := bstep (se 1 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 2295499 = 3443249) B3443249
theorem B2041559 : Blo 906576 2041559 := bstep (se 1 (by rfl) ⟨1531169, by rfl⟩ : syracuseStep 2041559 = 3062339) B3062339
theorem B1722073 : Blo 906576 1722073 := bstep (se 2 (by rfl) ⟨645777, by rfl⟩ : syracuseStep 1722073 = 1291555) B1291555
theorem B1361675 : Blo 906576 1361675 := bstep (se 1 (by rfl) ⟨1021256, by rfl⟩ : syracuseStep 1361675 = 2042513) B2042513
theorem B1361687 : Blo 906576 1361687 := bstep (se 1 (by rfl) ⟨1021265, by rfl⟩ : syracuseStep 1361687 = 2042531) B2042531
theorem B2295641 : Blo 906576 2295641 := bstep (se 2 (by rfl) ⟨860865, by rfl⟩ : syracuseStep 2295641 = 1721731) B1721731
theorem B1361753 : Blo 906576 1361753 := bstep (se 2 (by rfl) ⟨510657, by rfl⟩ : syracuseStep 1361753 = 1021315) B1021315
theorem B2041739 : Blo 906576 2041739 := bstep (se 1 (by rfl) ⟨1531304, by rfl⟩ : syracuseStep 2041739 = 3062609) B3062609
theorem B2041793 : Blo 906576 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B1361867 : Blo 906576 1361867 := bstep (se 1 (by rfl) ⟨1021400, by rfl⟩ : syracuseStep 1361867 = 2042801) B2042801
theorem B1361879 : Blo 906576 1361879 := bstep (se 1 (by rfl) ⟨1021409, by rfl⟩ : syracuseStep 1361879 = 2042819) B2042819
theorem B12756953 : Blo 906576 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B5171161 : Blo 906576 5171161 := bstep (se 2 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 5171161 = 3878371) B3878371
theorem B4597721 : Blo 906576 4597721 := bstep (se 2 (by rfl) ⟨1724145, by rfl⟩ : syracuseStep 4597721 = 3448291) B3448291
theorem B1361945 : Blo 906576 1361945 := bstep (se 2 (by rfl) ⟨510729, by rfl⟩ : syracuseStep 1361945 = 1021459) B1021459
theorem B3442733 : Blo 906576 3442733 := bstep (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) B1291025
theorem B3442763 : Blo 906576 3442763 := bstep (se 1 (by rfl) ⟨2582072, by rfl⟩ : syracuseStep 3442763 = 5164145) B5164145
theorem B9807965 : Blo 906576 9807965 := bstep (se 3 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 9807965 = 3677987) B3677987
theorem B1362059 : Blo 906576 1362059 := bstep (se 1 (by rfl) ⟨1021544, by rfl⟩ : syracuseStep 1362059 = 2043089) B2043089
theorem B1362071 : Blo 906576 1362071 := bstep (se 1 (by rfl) ⟨1021553, by rfl⟩ : syracuseStep 1362071 = 2043107) B2043107
theorem B1722521 : Blo 906576 1722521 := bstep (se 2 (by rfl) ⟨645945, by rfl⟩ : syracuseStep 1722521 = 1291891) B1291891
theorem B2042009 : Blo 906576 2042009 := bstep (se 2 (by rfl) ⟨765753, by rfl⟩ : syracuseStep 2042009 = 1531507) B1531507
theorem B1362137 : Blo 906576 1362137 := bstep (se 2 (by rfl) ⟨510801, by rfl⟩ : syracuseStep 1362137 = 1021603) B1021603
theorem B2042099 : Blo 906576 2042099 := bstep (se 1 (by rfl) ⟨1531574, by rfl⟩ : syracuseStep 2042099 = 3063149) B3063149
theorem B2042135 : Blo 906576 2042135 := bstep (se 1 (by rfl) ⟨1531601, by rfl⟩ : syracuseStep 2042135 = 3063203) B3063203
theorem B1362251 : Blo 906576 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B1362263 : Blo 906576 1362263 := bstep (se 1 (by rfl) ⟨1021697, by rfl⟩ : syracuseStep 1362263 = 2043395) B2043395
theorem B1362329 : Blo 906576 1362329 := bstep (se 2 (by rfl) ⟨510873, by rfl⟩ : syracuseStep 1362329 = 1021747) B1021747
theorem B16566707 : Blo 906576 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B2042315 : Blo 906576 2042315 := bstep (se 1 (by rfl) ⟨1531736, by rfl⟩ : syracuseStep 2042315 = 3063473) B3063473
theorem B2042369 : Blo 906576 2042369 := bstep (se 2 (by rfl) ⟨765888, by rfl⟩ : syracuseStep 2042369 = 1531777) B1531777
theorem B1362443 : Blo 906576 1362443 := bstep (se 1 (by rfl) ⟨1021832, by rfl⟩ : syracuseStep 1362443 = 2043665) B2043665
theorem B11045393 : Blo 906576 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B4139543 : Blo 906576 4139543 := bstep (se 1 (by rfl) ⟨3104657, by rfl⟩ : syracuseStep 4139543 = 6209315) B6209315
theorem B1362455 : Blo 906576 1362455 := bstep (se 1 (by rfl) ⟨1021841, by rfl⟩ : syracuseStep 1362455 = 2043683) B2043683
theorem B3066443 : Blo 906576 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1362521 : Blo 906576 1362521 := bstep (se 2 (by rfl) ⟨510945, by rfl⟩ : syracuseStep 1362521 = 1021891) B1021891
theorem B2296471 : Blo 906576 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B1149643 : Blo 906576 1149643 := bstep (se 1 (by rfl) ⟨862232, by rfl⟩ : syracuseStep 1149643 = 1724465) B1724465
theorem B1362635 : Blo 906576 1362635 := bstep (se 1 (by rfl) ⟨1021976, by rfl⟩ : syracuseStep 1362635 = 2043953) B2043953
theorem B1362647 : Blo 906576 1362647 := bstep (se 1 (by rfl) ⟨1021985, by rfl⟩ : syracuseStep 1362647 = 2043971) B2043971
theorem B3443417 : Blo 906576 3443417 := bstep (se 2 (by rfl) ⟨1291281, by rfl⟩ : syracuseStep 3443417 = 2582563) B2582563
theorem B2042585 : Blo 906576 2042585 := bstep (se 2 (by rfl) ⟨765969, by rfl⟩ : syracuseStep 2042585 = 1531939) B1531939
theorem B14920433 : Blo 906576 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B1362713 : Blo 906576 1362713 := bstep (se 2 (by rfl) ⟨511017, by rfl⟩ : syracuseStep 1362713 = 1022035) B1022035
theorem B944939 : Blo 906576 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B2042675 : Blo 906576 2042675 := bstep (se 1 (by rfl) ⟨1532006, by rfl⟩ : syracuseStep 2042675 = 3064013) B3064013
theorem B4139851 : Blo 906576 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B2042711 : Blo 906576 2042711 := bstep (se 1 (by rfl) ⟨1532033, by rfl⟩ : syracuseStep 2042711 = 3064067) B3064067
theorem B1837939 : Blo 906576 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B1723265 : Blo 906576 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1362827 : Blo 906576 1362827 := bstep (se 1 (by rfl) ⟨1022120, by rfl⟩ : syracuseStep 1362827 = 2044241) B2044241
theorem B5172119 : Blo 906576 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B1362839 : Blo 906576 1362839 := bstep (se 1 (by rfl) ⟨1022129, by rfl⟩ : syracuseStep 1362839 = 2044259) B2044259
theorem B3271627 : Blo 906576 3271627 := bstep (se 1 (by rfl) ⟨2453720, by rfl⟩ : syracuseStep 3271627 = 4907441) B4907441
theorem B2042891 : Blo 906576 2042891 := bstep (se 1 (by rfl) ⟨1532168, by rfl⟩ : syracuseStep 2042891 = 3064337) B3064337
theorem B3443735 : Blo 906576 3443735 := bstep (se 1 (by rfl) ⟨2582801, by rfl⟩ : syracuseStep 3443735 = 5165603) B5165603
theorem B2042945 : Blo 906576 2042945 := bstep (se 2 (by rfl) ⟨766104, by rfl⟩ : syracuseStep 2042945 = 1532209) B1532209
theorem B2296907 : Blo 906576 2296907 := bstep (se 1 (by rfl) ⟨1722680, by rfl⟩ : syracuseStep 2296907 = 3445361) B3445361
theorem B7752779 : Blo 906576 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B1723531 : Blo 906576 1723531 := bstep (se 1 (by rfl) ⟨1292648, by rfl⟩ : syracuseStep 1723531 = 2585297) B2585297
theorem B3271859 : Blo 906576 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B969931 : Blo 906576 969931 := bstep (se 1 (by rfl) ⟨727448, by rfl⟩ : syracuseStep 969931 = 1454897) B1454897
theorem B2043161 : Blo 906576 2043161 := bstep (se 2 (by rfl) ⟨766185, by rfl⟩ : syracuseStep 2043161 = 1532371) B1532371
theorem B3681587 : Blo 906576 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B3878219 : Blo 906576 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B2043251 : Blo 906576 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B2043287 : Blo 906576 2043287 := bstep (se 1 (by rfl) ⟨1532465, by rfl⟩ : syracuseStep 2043287 = 3064931) B3064931
theorem B2297281 : Blo 906576 2297281 := bstep (se 2 (by rfl) ⟨861480, by rfl⟩ : syracuseStep 2297281 = 1722961) B1722961
theorem B4599341 : Blo 906576 4599341 := bstep (se 3 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 4599341 = 1724753) B1724753
theorem B1723979 : Blo 906576 1723979 := bstep (se 1 (by rfl) ⟨1292984, by rfl⟩ : syracuseStep 1723979 = 2585969) B2585969
theorem B2043467 : Blo 906576 2043467 := bstep (se 1 (by rfl) ⟨1532600, by rfl⟩ : syracuseStep 2043467 = 3065201) B3065201
theorem B2043521 : Blo 906576 2043521 := bstep (se 2 (by rfl) ⟨766320, by rfl⟩ : syracuseStep 2043521 = 1532641) B1532641
theorem B3444403 : Blo 906576 3444403 := bstep (se 1 (by rfl) ⟨2583302, by rfl⟩ : syracuseStep 3444403 = 5166605) B5166605
theorem B1724161 : Blo 906576 1724161 := bstep (se 2 (by rfl) ⟨646560, by rfl⟩ : syracuseStep 1724161 = 1293121) B1293121
theorem B2043737 : Blo 906576 2043737 := bstep (se 2 (by rfl) ⟨766401, by rfl⟩ : syracuseStep 2043737 = 1532803) B1532803
theorem B16568165 : Blo 906576 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B2043827 : Blo 906576 2043827 := bstep (se 1 (by rfl) ⟨1532870, by rfl⟩ : syracuseStep 2043827 = 3065741) B3065741
theorem B2043863 : Blo 906576 2043863 := bstep (se 1 (by rfl) ⟨1532897, by rfl⟩ : syracuseStep 2043863 = 3065795) B3065795
theorem B2297879 : Blo 906576 2297879 := bstep (se 1 (by rfl) ⟨1723409, by rfl⟩ : syracuseStep 2297879 = 3446819) B3446819
theorem B1019947 : Blo 906576 1019947 := bstep (se 1 (by rfl) ⟨764960, by rfl⟩ : syracuseStep 1019947 = 1529921) B1529921
theorem B8720459 : Blo 906576 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B1937495 : Blo 906576 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B1724503 : Blo 906576 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B3059801 : Blo 906576 3059801 := bstep (se 2 (by rfl) ⟨1147425, by rfl⟩ : syracuseStep 3059801 = 2294851) B2294851
theorem B4911205 : Blo 906576 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B2044043 : Blo 906576 2044043 := bstep (se 1 (by rfl) ⟨1533032, by rfl⟩ : syracuseStep 2044043 = 3066065) B3066065
theorem B1020055 : Blo 906576 1020055 := bstep (se 1 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 1020055 = 1530083) B1530083
theorem B2044097 : Blo 906576 2044097 := bstep (se 2 (by rfl) ⟨766536, by rfl⟩ : syracuseStep 2044097 = 1533073) B1533073
theorem B1937675 : Blo 906576 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B5165329 : Blo 906576 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B4591889 : Blo 906576 4591889 := bstep (se 2 (by rfl) ⟨1721958, by rfl⟩ : syracuseStep 4591889 = 3443917) B3443917
theorem B3879191 : Blo 906576 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B1724723 : Blo 906576 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1020235 : Blo 906576 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B1634689 : Blo 906576 1634689 := bstep (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) B1226017
theorem B4592051 : Blo 906576 4592051 := bstep (se 1 (by rfl) ⟨3444038, by rfl⟩ : syracuseStep 4592051 = 6888077) B6888077
theorem B1020343 : Blo 906576 1020343 := bstep (se 1 (by rfl) ⟨765257, by rfl⟩ : syracuseStep 1020343 = 1530515) B1530515
theorem B2454067 : Blo 906576 2454067 := bstep (se 1 (by rfl) ⟨1840550, by rfl⟩ : syracuseStep 2454067 = 3681101) B3681101
theorem B1020523 : Blo 906576 1020523 := bstep (se 1 (by rfl) ⟨765392, by rfl⟩ : syracuseStep 1020523 = 1530785) B1530785
theorem B1020631 : Blo 906576 1020631 := bstep (se 1 (by rfl) ⟨765473, by rfl⟩ : syracuseStep 1020631 = 1530947) B1530947
theorem B3060503 : Blo 906576 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B2298689 : Blo 906576 2298689 := bstep (se 2 (by rfl) ⟨862008, by rfl⟩ : syracuseStep 2298689 = 1724017) B1724017
theorem B1020811 : Blo 906576 1020811 := bstep (se 1 (by rfl) ⟨765608, by rfl⟩ : syracuseStep 1020811 = 1531217) B1531217
theorem B1381259 : Blo 906576 1381259 := bstep (se 1 (by rfl) ⟨1035944, by rfl⟩ : syracuseStep 1381259 = 2071889) B2071889
theorem B3445649 : Blo 906576 3445649 := bstep (se 2 (by rfl) ⟨1292118, by rfl⟩ : syracuseStep 3445649 = 2584237) B2584237
theorem B1635223 : Blo 906576 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B3879859 : Blo 906576 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B1020919 : Blo 906576 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B1840193 : Blo 906576 1840193 := bstep (se 2 (by rfl) ⟨690072, by rfl⟩ : syracuseStep 1840193 = 1380145) B1380145
theorem B1021099 : Blo 906576 1021099 := bstep (se 1 (by rfl) ⟨765824, by rfl⟩ : syracuseStep 1021099 = 1531649) B1531649
theorem B3683501 : Blo 906576 3683501 := bstep (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) B1381313
theorem B1021207 : Blo 906576 1021207 := bstep (se 1 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 1021207 = 1531811) B1531811
theorem B12432685 : Blo 906576 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B3061043 : Blo 906576 3061043 := bstep (se 1 (by rfl) ⟨2295782, by rfl⟩ : syracuseStep 3061043 = 4591565) B4591565
theorem B5174603 : Blo 906576 5174603 := bstep (se 1 (by rfl) ⟨3880952, by rfl⟩ : syracuseStep 5174603 = 7761905) B7761905
theorem B906583 : Blo 906576 906583 := bstep (se 1 (by rfl) ⟨679937, by rfl⟩ : syracuseStep 906583 = 1359875) B1359875
theorem B2585945 : Blo 906576 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B2299225 : Blo 906576 2299225 := bstep (se 2 (by rfl) ⟨862209, by rfl⟩ : syracuseStep 2299225 = 1724419) B1724419
theorem B906603 : Blo 906576 906603 := bstep (se 1 (by rfl) ⟨679952, by rfl⟩ : syracuseStep 906603 = 1359905) B1359905
theorem B906615 : Blo 906576 906615 := bstep (se 1 (by rfl) ⟨679961, by rfl⟩ : syracuseStep 906615 = 1359923) B1359923
theorem B906635 : Blo 906576 906635 := bstep (se 1 (by rfl) ⟨679976, by rfl⟩ : syracuseStep 906635 = 1359953) B1359953
theorem B906647 : Blo 906576 906647 := bstep (se 1 (by rfl) ⟨679985, by rfl⟩ : syracuseStep 906647 = 1359971) B1359971
theorem B906667 : Blo 906576 906667 := bstep (se 1 (by rfl) ⟨680000, by rfl⟩ : syracuseStep 906667 = 1360001) B1360001
theorem B906679 : Blo 906576 906679 := bstep (se 1 (by rfl) ⟨680009, by rfl⟩ : syracuseStep 906679 = 1360019) B1360019
theorem B906699 : Blo 906576 906699 := bstep (se 1 (by rfl) ⟨680024, by rfl⟩ : syracuseStep 906699 = 1360049) B1360049
theorem B1021387 : Blo 906576 1021387 := bstep (se 1 (by rfl) ⟨766040, by rfl⟩ : syracuseStep 1021387 = 1532081) B1532081
theorem B906711 : Blo 906576 906711 := bstep (se 1 (by rfl) ⟨680033, by rfl⟩ : syracuseStep 906711 = 1360067) B1360067
theorem B906731 : Blo 906576 906731 := bstep (se 1 (by rfl) ⟨680048, by rfl⟩ : syracuseStep 906731 = 1360097) B1360097
theorem B906743 : Blo 906576 906743 := bstep (se 1 (by rfl) ⟨680057, by rfl⟩ : syracuseStep 906743 = 1360115) B1360115
theorem B906763 : Blo 906576 906763 := bstep (se 1 (by rfl) ⟨680072, by rfl⟩ : syracuseStep 906763 = 1360145) B1360145
theorem B10335761 : Blo 906576 10335761 := bstep (se 2 (by rfl) ⟨3875910, by rfl⟩ : syracuseStep 10335761 = 7751821) B7751821
theorem B906775 : Blo 906576 906775 := bstep (se 1 (by rfl) ⟨680081, by rfl⟩ : syracuseStep 906775 = 1360163) B1360163
theorem B906795 : Blo 906576 906795 := bstep (se 1 (by rfl) ⟨680096, by rfl⟩ : syracuseStep 906795 = 1360193) B1360193
theorem B906807 : Blo 906576 906807 := bstep (se 1 (by rfl) ⟨680105, by rfl⟩ : syracuseStep 906807 = 1360211) B1360211
theorem B1021495 : Blo 906576 1021495 := bstep (se 1 (by rfl) ⟨766121, by rfl⟩ : syracuseStep 1021495 = 1532243) B1532243
theorem B3061313 : Blo 906576 3061313 := bstep (se 2 (by rfl) ⟨1147992, by rfl⟩ : syracuseStep 3061313 = 2295985) B2295985
theorem B2455105 : Blo 906576 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B906827 : Blo 906576 906827 := bstep (se 1 (by rfl) ⟨680120, by rfl⟩ : syracuseStep 906827 = 1360241) B1360241
theorem B3446347 : Blo 906576 3446347 := bstep (se 1 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 3446347 = 5169521) B5169521
theorem B906839 : Blo 906576 906839 := bstep (se 1 (by rfl) ⟨680129, by rfl⟩ : syracuseStep 906839 = 1360259) B1360259
theorem B2487901 : Blo 906576 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B906859 : Blo 906576 906859 := bstep (se 1 (by rfl) ⟨680144, by rfl⟩ : syracuseStep 906859 = 1360289) B1360289
theorem B906871 : Blo 906576 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B11941507 : Blo 906576 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B9942659 : Blo 906576 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B906891 : Blo 906576 906891 := bstep (se 1 (by rfl) ⟨680168, by rfl⟩ : syracuseStep 906891 = 1360337) B1360337
theorem B906903 : Blo 906576 906903 := bstep (se 1 (by rfl) ⟨680177, by rfl⟩ : syracuseStep 906903 = 1360355) B1360355
theorem B906923 : Blo 906576 906923 := bstep (se 1 (by rfl) ⟨680192, by rfl⟩ : syracuseStep 906923 = 1360385) B1360385
theorem B4142771 : Blo 906576 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B906935 : Blo 906576 906935 := bstep (se 1 (by rfl) ⟨680201, by rfl⟩ : syracuseStep 906935 = 1360403) B1360403
theorem B3102401 : Blo 906576 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B906955 : Blo 906576 906955 := bstep (se 1 (by rfl) ⟨680216, by rfl⟩ : syracuseStep 906955 = 1360433) B1360433
theorem B906967 : Blo 906576 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B906987 : Blo 906576 906987 := bstep (se 1 (by rfl) ⟨680240, by rfl⟩ : syracuseStep 906987 = 1360481) B1360481
theorem B1021675 : Blo 906576 1021675 := bstep (se 1 (by rfl) ⟨766256, by rfl⟩ : syracuseStep 1021675 = 1532513) B1532513
theorem B906999 : Blo 906576 906999 := bstep (se 1 (by rfl) ⟨680249, by rfl⟩ : syracuseStep 906999 = 1360499) B1360499
theorem B907019 : Blo 906576 907019 := bstep (se 1 (by rfl) ⟨680264, by rfl⟩ : syracuseStep 907019 = 1360529) B1360529
theorem B907031 : Blo 906576 907031 := bstep (se 1 (by rfl) ⟨680273, by rfl⟩ : syracuseStep 907031 = 1360547) B1360547
theorem B6543139 : Blo 906576 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B907051 : Blo 906576 907051 := bstep (se 1 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 907051 = 1360577) B1360577
theorem B8730413 : Blo 906576 8730413 := bstep (se 3 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 8730413 = 3273905) B3273905
theorem B907063 : Blo 906576 907063 := bstep (se 1 (by rfl) ⟨680297, by rfl⟩ : syracuseStep 907063 = 1360595) B1360595
theorem B2758465 : Blo 906576 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B907083 : Blo 906576 907083 := bstep (se 1 (by rfl) ⟨680312, by rfl⟩ : syracuseStep 907083 = 1360625) B1360625
theorem B1292107 : Blo 906576 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B907095 : Blo 906576 907095 := bstep (se 1 (by rfl) ⟨680321, by rfl⟩ : syracuseStep 907095 = 1360643) B1360643
theorem B1021783 : Blo 906576 1021783 := bstep (se 1 (by rfl) ⟨766337, by rfl⟩ : syracuseStep 1021783 = 1532675) B1532675
theorem B3446621 : Blo 906576 3446621 := bstep (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) B1292483
theorem B907115 : Blo 906576 907115 := bstep (se 1 (by rfl) ⟨680336, by rfl⟩ : syracuseStep 907115 = 1360673) B1360673
theorem B1939315 : Blo 906576 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B907127 : Blo 906576 907127 := bstep (se 1 (by rfl) ⟨680345, by rfl⟩ : syracuseStep 907127 = 1360691) B1360691
theorem B907147 : Blo 906576 907147 := bstep (se 1 (by rfl) ⟨680360, by rfl⟩ : syracuseStep 907147 = 1360721) B1360721
theorem B907159 : Blo 906576 907159 := bstep (se 1 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 907159 = 1360739) B1360739
theorem B907179 : Blo 906576 907179 := bstep (se 1 (by rfl) ⟨680384, by rfl⟩ : syracuseStep 907179 = 1360769) B1360769
theorem B41875379 : Blo 906576 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B907191 : Blo 906576 907191 := bstep (se 1 (by rfl) ⟨680393, by rfl⟩ : syracuseStep 907191 = 1360787) B1360787
theorem B907211 : Blo 906576 907211 := bstep (se 1 (by rfl) ⟨680408, by rfl⟩ : syracuseStep 907211 = 1360817) B1360817
theorem B907223 : Blo 906576 907223 := bstep (se 1 (by rfl) ⟨680417, by rfl⟩ : syracuseStep 907223 = 1360835) B1360835
theorem B907243 : Blo 906576 907243 := bstep (se 1 (by rfl) ⟨680432, by rfl⟩ : syracuseStep 907243 = 1360865) B1360865
theorem B907255 : Blo 906576 907255 := bstep (se 1 (by rfl) ⟨680441, by rfl⟩ : syracuseStep 907255 = 1360883) B1360883
theorem B1529867 : Blo 906576 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B907275 : Blo 906576 907275 := bstep (se 1 (by rfl) ⟨680456, by rfl⟩ : syracuseStep 907275 = 1360913) B1360913
theorem B1021963 : Blo 906576 1021963 := bstep (se 1 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 1021963 = 1532945) B1532945
theorem B8730641 : Blo 906576 8730641 := bstep (se 2 (by rfl) ⟨3273990, by rfl⟩ : syracuseStep 8730641 = 6547981) B6547981
theorem B907287 : Blo 906576 907287 := bstep (se 1 (by rfl) ⟨680465, by rfl⟩ : syracuseStep 907287 = 1360931) B1360931
theorem B907307 : Blo 906576 907307 := bstep (se 1 (by rfl) ⟨680480, by rfl⟩ : syracuseStep 907307 = 1360961) B1360961
theorem B907319 : Blo 906576 907319 := bstep (se 1 (by rfl) ⟨680489, by rfl⟩ : syracuseStep 907319 = 1360979) B1360979
theorem B907339 : Blo 906576 907339 := bstep (se 1 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 907339 = 1361009) B1361009
theorem B1964119 : Blo 906576 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B907351 : Blo 906576 907351 := bstep (se 1 (by rfl) ⟨680513, by rfl⟩ : syracuseStep 907351 = 1361027) B1361027
theorem B1292375 : Blo 906576 1292375 := bstep (se 1 (by rfl) ⟨969281, by rfl⟩ : syracuseStep 1292375 = 1938563) B1938563
theorem B3061853 : Blo 906576 3061853 := bstep (se 3 (by rfl) ⟨574097, by rfl⟩ : syracuseStep 3061853 = 1148195) B1148195
theorem B907371 : Blo 906576 907371 := bstep (se 1 (by rfl) ⟨680528, by rfl⟩ : syracuseStep 907371 = 1361057) B1361057
theorem B907383 : Blo 906576 907383 := bstep (se 1 (by rfl) ⟨680537, by rfl⟩ : syracuseStep 907383 = 1361075) B1361075
theorem B1022071 : Blo 906576 1022071 := bstep (se 1 (by rfl) ⟨766553, by rfl⟩ : syracuseStep 1022071 = 1533107) B1533107
theorem B1529995 : Blo 906576 1529995 := bstep (se 1 (by rfl) ⟨1147496, by rfl⟩ : syracuseStep 1529995 = 2294993) B2294993
theorem B907403 : Blo 906576 907403 := bstep (se 1 (by rfl) ⟨680552, by rfl⟩ : syracuseStep 907403 = 1361105) B1361105
theorem B907415 : Blo 906576 907415 := bstep (se 1 (by rfl) ⟨680561, by rfl⟩ : syracuseStep 907415 = 1361123) B1361123
theorem B907435 : Blo 906576 907435 := bstep (se 1 (by rfl) ⟨680576, by rfl⟩ : syracuseStep 907435 = 1361153) B1361153
theorem B907447 : Blo 906576 907447 := bstep (se 1 (by rfl) ⟨680585, by rfl⟩ : syracuseStep 907447 = 1361171) B1361171
theorem B907467 : Blo 906576 907467 := bstep (se 1 (by rfl) ⟨680600, by rfl⟩ : syracuseStep 907467 = 1361201) B1361201
theorem B907479 : Blo 906576 907479 := bstep (se 1 (by rfl) ⟨680609, by rfl⟩ : syracuseStep 907479 = 1361219) B1361219
theorem B907499 : Blo 906576 907499 := bstep (se 1 (by rfl) ⟨680624, by rfl⟩ : syracuseStep 907499 = 1361249) B1361249
theorem B907511 : Blo 906576 907511 := bstep (se 1 (by rfl) ⟨680633, by rfl⟩ : syracuseStep 907511 = 1361267) B1361267
theorem B907531 : Blo 906576 907531 := bstep (se 1 (by rfl) ⟨680648, by rfl⟩ : syracuseStep 907531 = 1361297) B1361297
theorem B3873041 : Blo 906576 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B907543 : Blo 906576 907543 := bstep (se 1 (by rfl) ⟨680657, by rfl⟩ : syracuseStep 907543 = 1361315) B1361315
theorem B1530137 : Blo 906576 1530137 := bstep (se 2 (by rfl) ⟨573801, by rfl⟩ : syracuseStep 1530137 = 1147603) B1147603
theorem B907563 : Blo 906576 907563 := bstep (se 1 (by rfl) ⟨680672, by rfl⟩ : syracuseStep 907563 = 1361345) B1361345
theorem B907575 : Blo 906576 907575 := bstep (se 1 (by rfl) ⟨680681, by rfl⟩ : syracuseStep 907575 = 1361363) B1361363
theorem B4593995 : Blo 906576 4593995 := bstep (se 1 (by rfl) ⟨3445496, by rfl⟩ : syracuseStep 4593995 = 6890993) B6890993
theorem B907595 : Blo 906576 907595 := bstep (se 1 (by rfl) ⟨680696, by rfl⟩ : syracuseStep 907595 = 1361393) B1361393
theorem B907607 : Blo 906576 907607 := bstep (se 1 (by rfl) ⟨680705, by rfl⟩ : syracuseStep 907607 = 1361411) B1361411
theorem B1939801 : Blo 906576 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B907627 : Blo 906576 907627 := bstep (se 1 (by rfl) ⟨680720, by rfl⟩ : syracuseStep 907627 = 1361441) B1361441
theorem B907639 : Blo 906576 907639 := bstep (se 1 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 907639 = 1361459) B1361459
theorem B907659 : Blo 906576 907659 := bstep (se 1 (by rfl) ⟨680744, by rfl⟩ : syracuseStep 907659 = 1361489) B1361489
theorem B23239061 : Blo 906576 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B907671 : Blo 906576 907671 := bstep (se 1 (by rfl) ⟨680753, by rfl⟩ : syracuseStep 907671 = 1361507) B1361507
theorem B1530265 : Blo 906576 1530265 := bstep (se 2 (by rfl) ⟨573849, by rfl⟩ : syracuseStep 1530265 = 1147699) B1147699
theorem B907691 : Blo 906576 907691 := bstep (se 1 (by rfl) ⟨680768, by rfl⟩ : syracuseStep 907691 = 1361537) B1361537
theorem B907703 : Blo 906576 907703 := bstep (se 1 (by rfl) ⟨680777, by rfl⟩ : syracuseStep 907703 = 1361555) B1361555
theorem B907723 : Blo 906576 907723 := bstep (se 1 (by rfl) ⟨680792, by rfl⟩ : syracuseStep 907723 = 1361585) B1361585
theorem B907735 : Blo 906576 907735 := bstep (se 1 (by rfl) ⟨680801, by rfl⟩ : syracuseStep 907735 = 1361603) B1361603
theorem B1636823 : Blo 906576 1636823 := bstep (se 1 (by rfl) ⟨1227617, by rfl⟩ : syracuseStep 1636823 = 2455235) B2455235
theorem B907755 : Blo 906576 907755 := bstep (se 1 (by rfl) ⟨680816, by rfl⟩ : syracuseStep 907755 = 1361633) B1361633
theorem B907767 : Blo 906576 907767 := bstep (se 1 (by rfl) ⟨680825, by rfl⟩ : syracuseStep 907767 = 1361651) B1361651
theorem B907787 : Blo 906576 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B907799 : Blo 906576 907799 := bstep (se 1 (by rfl) ⟨680849, by rfl⟩ : syracuseStep 907799 = 1361699) B1361699
theorem B3447319 : Blo 906576 3447319 := bstep (se 1 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 3447319 = 5170979) B5170979
theorem B907819 : Blo 906576 907819 := bstep (se 1 (by rfl) ⟨680864, by rfl⟩ : syracuseStep 907819 = 1361729) B1361729
theorem B907831 : Blo 906576 907831 := bstep (se 1 (by rfl) ⟨680873, by rfl⟩ : syracuseStep 907831 = 1361747) B1361747
theorem B907851 : Blo 906576 907851 := bstep (se 1 (by rfl) ⟨680888, by rfl⟩ : syracuseStep 907851 = 1361777) B1361777
theorem B2587211 : Blo 906576 2587211 := bstep (se 1 (by rfl) ⟨1940408, by rfl⟩ : syracuseStep 2587211 = 3880817) B3880817
theorem B907863 : Blo 906576 907863 := bstep (se 1 (by rfl) ⟨680897, by rfl⟩ : syracuseStep 907863 = 1361795) B1361795
theorem B907883 : Blo 906576 907883 := bstep (se 1 (by rfl) ⟨680912, by rfl⟩ : syracuseStep 907883 = 1361825) B1361825
theorem B907895 : Blo 906576 907895 := bstep (se 1 (by rfl) ⟨680921, by rfl⟩ : syracuseStep 907895 = 1361843) B1361843
theorem B907915 : Blo 906576 907915 := bstep (se 1 (by rfl) ⟨680936, by rfl⟩ : syracuseStep 907915 = 1361873) B1361873
theorem B8395415 : Blo 906576 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B907927 : Blo 906576 907927 := bstep (se 1 (by rfl) ⟨680945, by rfl⟩ : syracuseStep 907927 = 1361891) B1361891
theorem B907947 : Blo 906576 907947 := bstep (se 1 (by rfl) ⟨680960, by rfl⟩ : syracuseStep 907947 = 1361921) B1361921
theorem B907959 : Blo 906576 907959 := bstep (se 1 (by rfl) ⟨680969, by rfl⟩ : syracuseStep 907959 = 1361939) B1361939
theorem B907979 : Blo 906576 907979 := bstep (se 1 (by rfl) ⟨680984, by rfl⟩ : syracuseStep 907979 = 1361969) B1361969
theorem B907991 : Blo 906576 907991 := bstep (se 1 (by rfl) ⟨680993, by rfl⟩ : syracuseStep 907991 = 1361987) B1361987
theorem B908011 : Blo 906576 908011 := bstep (se 1 (by rfl) ⟨681008, by rfl⟩ : syracuseStep 908011 = 1362017) B1362017
theorem B908023 : Blo 906576 908023 := bstep (se 1 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 908023 = 1362035) B1362035
theorem B908043 : Blo 906576 908043 := bstep (se 1 (by rfl) ⟨681032, by rfl⟩ : syracuseStep 908043 = 1362065) B1362065
theorem B908055 : Blo 906576 908055 := bstep (se 1 (by rfl) ⟨681041, by rfl⟩ : syracuseStep 908055 = 1362083) B1362083
theorem B908075 : Blo 906576 908075 := bstep (se 1 (by rfl) ⟨681056, by rfl⟩ : syracuseStep 908075 = 1362113) B1362113
theorem B6208301 : Blo 906576 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B908087 : Blo 906576 908087 := bstep (se 1 (by rfl) ⟨681065, by rfl⟩ : syracuseStep 908087 = 1362131) B1362131
theorem B908107 : Blo 906576 908107 := bstep (se 1 (by rfl) ⟨681080, by rfl⟩ : syracuseStep 908107 = 1362161) B1362161
theorem B908119 : Blo 906576 908119 := bstep (se 1 (by rfl) ⟨681089, by rfl⟩ : syracuseStep 908119 = 1362179) B1362179
theorem B908139 : Blo 906576 908139 := bstep (se 1 (by rfl) ⟨681104, by rfl⟩ : syracuseStep 908139 = 1362209) B1362209
theorem B908151 : Blo 906576 908151 := bstep (se 1 (by rfl) ⟨681113, by rfl⟩ : syracuseStep 908151 = 1362227) B1362227
theorem B908171 : Blo 906576 908171 := bstep (se 1 (by rfl) ⟨681128, by rfl⟩ : syracuseStep 908171 = 1362257) B1362257
theorem B908183 : Blo 906576 908183 := bstep (se 1 (by rfl) ⟨681137, by rfl⟩ : syracuseStep 908183 = 1362275) B1362275
theorem B908203 : Blo 906576 908203 := bstep (se 1 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 908203 = 1362305) B1362305
theorem B908215 : Blo 906576 908215 := bstep (se 1 (by rfl) ⟨681161, by rfl⟩ : syracuseStep 908215 = 1362323) B1362323
theorem B908235 : Blo 906576 908235 := bstep (se 1 (by rfl) ⟨681176, by rfl⟩ : syracuseStep 908235 = 1362353) B1362353
theorem B1530839 : Blo 906576 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B908247 : Blo 906576 908247 := bstep (se 1 (by rfl) ⟨681185, by rfl⟩ : syracuseStep 908247 = 1362371) B1362371
theorem B908267 : Blo 906576 908267 := bstep (se 1 (by rfl) ⟨681200, by rfl⟩ : syracuseStep 908267 = 1362401) B1362401
theorem B908279 : Blo 906576 908279 := bstep (se 1 (by rfl) ⟨681209, by rfl⟩ : syracuseStep 908279 = 1362419) B1362419
theorem B908299 : Blo 906576 908299 := bstep (se 1 (by rfl) ⟨681224, by rfl⟩ : syracuseStep 908299 = 1362449) B1362449
theorem B908311 : Blo 906576 908311 := bstep (se 1 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 908311 = 1362467) B1362467
theorem B1293337 : Blo 906576 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B908331 : Blo 906576 908331 := bstep (se 1 (by rfl) ⟨681248, by rfl⟩ : syracuseStep 908331 = 1362497) B1362497
theorem B908343 : Blo 906576 908343 := bstep (se 1 (by rfl) ⟨681257, by rfl⟩ : syracuseStep 908343 = 1362515) B1362515
theorem B908363 : Blo 906576 908363 := bstep (se 1 (by rfl) ⟨681272, by rfl⟩ : syracuseStep 908363 = 1362545) B1362545
theorem B1530967 : Blo 906576 1530967 := bstep (se 1 (by rfl) ⟨1148225, by rfl⟩ : syracuseStep 1530967 = 2296451) B2296451
theorem B1309783 : Blo 906576 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B908375 : Blo 906576 908375 := bstep (se 1 (by rfl) ⟨681281, by rfl⟩ : syracuseStep 908375 = 1362563) B1362563
theorem B908395 : Blo 906576 908395 := bstep (se 1 (by rfl) ⟨681296, by rfl⟩ : syracuseStep 908395 = 1362593) B1362593
theorem B908407 : Blo 906576 908407 := bstep (se 1 (by rfl) ⟨681305, by rfl⟩ : syracuseStep 908407 = 1362611) B1362611
theorem B908427 : Blo 906576 908427 := bstep (se 1 (by rfl) ⟨681320, by rfl⟩ : syracuseStep 908427 = 1362641) B1362641
theorem B908439 : Blo 906576 908439 := bstep (se 1 (by rfl) ⟨681329, by rfl⟩ : syracuseStep 908439 = 1362659) B1362659
theorem B908459 : Blo 906576 908459 := bstep (se 1 (by rfl) ⟨681344, by rfl⟩ : syracuseStep 908459 = 1362689) B1362689
theorem B908471 : Blo 906576 908471 := bstep (se 1 (by rfl) ⟨681353, by rfl⟩ : syracuseStep 908471 = 1362707) B1362707
theorem B3062987 : Blo 906576 3062987 := bstep (se 1 (by rfl) ⟨2297240, by rfl⟩ : syracuseStep 3062987 = 4594481) B4594481
theorem B908491 : Blo 906576 908491 := bstep (se 1 (by rfl) ⟨681368, by rfl⟩ : syracuseStep 908491 = 1362737) B1362737
theorem B908503 : Blo 906576 908503 := bstep (se 1 (by rfl) ⟨681377, by rfl⟩ : syracuseStep 908503 = 1362755) B1362755
theorem B908523 : Blo 906576 908523 := bstep (se 1 (by rfl) ⟨681392, by rfl⟩ : syracuseStep 908523 = 1362785) B1362785
theorem B908535 : Blo 906576 908535 := bstep (se 1 (by rfl) ⟨681401, by rfl⟩ : syracuseStep 908535 = 1362803) B1362803
theorem B908555 : Blo 906576 908555 := bstep (se 1 (by rfl) ⟨681416, by rfl⟩ : syracuseStep 908555 = 1362833) B1362833
theorem B908567 : Blo 906576 908567 := bstep (se 1 (by rfl) ⟨681425, by rfl⟩ : syracuseStep 908567 = 1362851) B1362851
theorem B3448109 : Blo 906576 3448109 := bstep (se 3 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 3448109 = 1293041) B1293041
theorem B2178355 : Blo 906576 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B3063257 : Blo 906576 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B1965593 : Blo 906576 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B6626861 : Blo 906576 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B5045825 : Blo 906576 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B5168771 : Blo 906576 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B1531595 : Blo 906576 1531595 := bstep (se 1 (by rfl) ⟨1148696, by rfl⟩ : syracuseStep 1531595 = 2297393) B2297393
theorem B6536909 : Blo 906576 6536909 := bstep (se 3 (by rfl) ⟨1225670, by rfl⟩ : syracuseStep 6536909 = 2451341) B2451341
theorem B1531723 : Blo 906576 1531723 := bstep (se 1 (by rfl) ⟨1148792, by rfl⟩ : syracuseStep 1531723 = 2297585) B2297585
theorem B1531865 : Blo 906576 1531865 := bstep (se 2 (by rfl) ⟨574449, by rfl⟩ : syracuseStep 1531865 = 1148899) B1148899
theorem B1359887 : Blo 906576 1359887 := bstep (se 1 (by rfl) ⟨1019915, by rfl⟩ : syracuseStep 1359887 = 2039831) B2039831
theorem B1531919 : Blo 906576 1531919 := bstep (se 1 (by rfl) ⟨1148939, by rfl⟩ : syracuseStep 1531919 = 2297879) B2297879
theorem B3063851 : Blo 906576 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B1359929 : Blo 906576 1359929 := bstep (se 2 (by rfl) ⟨509973, by rfl⟩ : syracuseStep 1359929 = 1019947) B1019947
theorem B2039867 : Blo 906576 2039867 := bstep (se 1 (by rfl) ⟨1529900, by rfl⟩ : syracuseStep 2039867 = 3059801) B3059801
theorem B3489911 : Blo 906576 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B6897797 : Blo 906576 6897797 := bstep (se 4 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 6897797 = 1293337) B1293337
theorem B1360007 : Blo 906576 1360007 := bstep (se 1 (by rfl) ⟨1020005, by rfl⟩ : syracuseStep 1360007 = 2040011) B2040011
theorem B1360043 : Blo 906576 1360043 := bstep (se 1 (by rfl) ⟨1020032, by rfl⟩ : syracuseStep 1360043 = 2040065) B2040065
theorem B2039993 : Blo 906576 2039993 := bstep (se 2 (by rfl) ⟨764997, by rfl⟩ : syracuseStep 2039993 = 1529995) B1529995
theorem B1360073 : Blo 906576 1360073 := bstep (se 2 (by rfl) ⟨510027, by rfl⟩ : syracuseStep 1360073 = 1020055) B1020055
theorem B1360187 : Blo 906576 1360187 := bstep (se 1 (by rfl) ⟨1020140, by rfl⟩ : syracuseStep 1360187 = 2040281) B2040281
theorem B1360247 : Blo 906576 1360247 := bstep (se 1 (by rfl) ⟨1020185, by rfl⟩ : syracuseStep 1360247 = 2040371) B2040371
theorem B1360271 : Blo 906576 1360271 := bstep (se 1 (by rfl) ⟨1020203, by rfl⟩ : syracuseStep 1360271 = 2040407) B2040407
theorem B1180075 : Blo 906576 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B1360313 : Blo 906576 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B2179585 : Blo 906576 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B1360391 : Blo 906576 1360391 := bstep (se 1 (by rfl) ⟨1020293, by rfl⟩ : syracuseStep 1360391 = 2040587) B2040587
theorem B2040335 : Blo 906576 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B2040353 : Blo 906576 2040353 := bstep (se 2 (by rfl) ⟨765132, by rfl⟩ : syracuseStep 2040353 = 1530265) B1530265
theorem B1360427 : Blo 906576 1360427 := bstep (se 1 (by rfl) ⟨1020320, by rfl⟩ : syracuseStep 1360427 = 2040641) B2040641
theorem B1532459 : Blo 906576 1532459 := bstep (se 1 (by rfl) ⟨1149344, by rfl⟩ : syracuseStep 1532459 = 2298689) B2298689
theorem B1360457 : Blo 906576 1360457 := bstep (se 2 (by rfl) ⟨510171, by rfl⟩ : syracuseStep 1360457 = 1020343) B1020343
theorem B1360571 : Blo 906576 1360571 := bstep (se 1 (by rfl) ⟨1020428, by rfl⟩ : syracuseStep 1360571 = 2040857) B2040857
theorem B4596425 : Blo 906576 4596425 := bstep (se 2 (by rfl) ⟨1723659, by rfl⟩ : syracuseStep 4596425 = 3447319) B3447319
theorem B1360631 : Blo 906576 1360631 := bstep (se 1 (by rfl) ⟨1020473, by rfl⟩ : syracuseStep 1360631 = 2040947) B2040947
theorem B8274703 : Blo 906576 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B1360655 : Blo 906576 1360655 := bstep (se 1 (by rfl) ⟨1020491, by rfl⟩ : syracuseStep 1360655 = 2040983) B2040983
theorem B148882211 : Blo 906576 148882211 := bstep (se 1 (by rfl) ⟨111661658, by rfl⟩ : syracuseStep 148882211 = 223323317) B223323317
theorem B1360697 : Blo 906576 1360697 := bstep (se 2 (by rfl) ⟨510261, by rfl⟩ : syracuseStep 1360697 = 1020523) B1020523
theorem B4653883 : Blo 906576 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2040695 : Blo 906576 2040695 := bstep (se 1 (by rfl) ⟨1530521, by rfl⟩ : syracuseStep 2040695 = 3061043) B3061043
theorem B1360775 : Blo 906576 1360775 := bstep (se 1 (by rfl) ⟨1020581, by rfl⟩ : syracuseStep 1360775 = 2041163) B2041163
theorem B3449735 : Blo 906576 3449735 := bstep (se 1 (by rfl) ⟨2587301, by rfl⟩ : syracuseStep 3449735 = 5174603) B5174603
theorem B1360811 : Blo 906576 1360811 := bstep (se 1 (by rfl) ⟨1020608, by rfl⟩ : syracuseStep 1360811 = 2041217) B2041217
theorem B1532857 : Blo 906576 1532857 := bstep (se 2 (by rfl) ⟨574821, by rfl⟩ : syracuseStep 1532857 = 1149643) B1149643
theorem B1360841 : Blo 906576 1360841 := bstep (se 2 (by rfl) ⟨510315, by rfl⟩ : syracuseStep 1360841 = 1020631) B1020631
theorem B6890507 : Blo 906576 6890507 := bstep (se 1 (by rfl) ⟨5167880, by rfl⟩ : syracuseStep 6890507 = 10335761) B10335761
theorem B9815051 : Blo 906576 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B2040875 : Blo 906576 2040875 := bstep (se 1 (by rfl) ⟨1530656, by rfl⟩ : syracuseStep 2040875 = 3061313) B3061313
theorem B1360955 : Blo 906576 1360955 := bstep (se 1 (by rfl) ⟨1020716, by rfl⟩ : syracuseStep 1360955 = 2041433) B2041433
theorem B6628439 : Blo 906576 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B1148023 : Blo 906576 1148023 := bstep (se 1 (by rfl) ⟨861017, by rfl⟩ : syracuseStep 1148023 = 1722035) B1722035
theorem B1361015 : Blo 906576 1361015 := bstep (se 1 (by rfl) ⟨1020761, by rfl⟩ : syracuseStep 1361015 = 2041523) B2041523
theorem B2761847 : Blo 906576 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B1361039 : Blo 906576 1361039 := bstep (se 1 (by rfl) ⟨1020779, by rfl⟩ : syracuseStep 1361039 = 2041559) B2041559
theorem B2450585 : Blo 906576 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B1361081 : Blo 906576 1361081 := bstep (se 2 (by rfl) ⟨510405, by rfl⟩ : syracuseStep 1361081 = 1020811) B1020811
theorem B2180297 : Blo 906576 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B1361159 : Blo 906576 1361159 := bstep (se 1 (by rfl) ⟨1020869, by rfl⟩ : syracuseStep 1361159 = 2041739) B2041739
theorem B1361195 : Blo 906576 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B8504635 : Blo 906576 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B3065147 : Blo 906576 3065147 := bstep (se 1 (by rfl) ⟨2298860, by rfl⟩ : syracuseStep 3065147 = 4597721) B4597721
theorem B1361225 : Blo 906576 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B2295155 : Blo 906576 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B2295175 : Blo 906576 2295175 := bstep (se 1 (by rfl) ⟨1721381, by rfl⟩ : syracuseStep 2295175 = 3442763) B3442763
theorem B6538643 : Blo 906576 6538643 := bstep (se 1 (by rfl) ⟨4903982, by rfl⟩ : syracuseStep 6538643 = 9807965) B9807965
theorem B2041235 : Blo 906576 2041235 := bstep (se 1 (by rfl) ⟨1530926, by rfl⟩ : syracuseStep 2041235 = 3061853) B3061853
theorem B1148347 : Blo 906576 1148347 := bstep (se 1 (by rfl) ⟨861260, by rfl⟩ : syracuseStep 1148347 = 1722521) B1722521
theorem B1361339 : Blo 906576 1361339 := bstep (se 1 (by rfl) ⟨1021004, by rfl⟩ : syracuseStep 1361339 = 2042009) B2042009
theorem B2041289 : Blo 906576 2041289 := bstep (se 2 (by rfl) ⟨765483, by rfl⟩ : syracuseStep 2041289 = 1530967) B1530967
theorem B1746377 : Blo 906576 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B1361399 : Blo 906576 1361399 := bstep (se 1 (by rfl) ⟨1021049, by rfl⟩ : syracuseStep 1361399 = 2042099) B2042099
theorem B2582027 : Blo 906576 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B1361423 : Blo 906576 1361423 := bstep (se 1 (by rfl) ⟨1021067, by rfl⟩ : syracuseStep 1361423 = 2042135) B2042135
theorem B1361465 : Blo 906576 1361465 := bstep (se 2 (by rfl) ⟨510549, by rfl⟩ : syracuseStep 1361465 = 1021099) B1021099
theorem B15492707 : Blo 906576 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B11044471 : Blo 906576 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B1361543 : Blo 906576 1361543 := bstep (se 1 (by rfl) ⟨1021157, by rfl⟩ : syracuseStep 1361543 = 2042315) B2042315
theorem B1091215 : Blo 906576 1091215 := bstep (se 1 (by rfl) ⟨818411, by rfl⟩ : syracuseStep 1091215 = 1636823) B1636823
theorem B2295449 : Blo 906576 2295449 := bstep (se 2 (by rfl) ⟨860793, by rfl⟩ : syracuseStep 2295449 = 1721587) B1721587
theorem B1361579 : Blo 906576 1361579 := bstep (se 1 (by rfl) ⟨1021184, by rfl⟩ : syracuseStep 1361579 = 2042369) B2042369
theorem B1361609 : Blo 906576 1361609 := bstep (se 2 (by rfl) ⟨510603, by rfl⟩ : syracuseStep 1361609 = 1021207) B1021207
theorem B5596943 : Blo 906576 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B3065633 : Blo 906576 3065633 := bstep (se 2 (by rfl) ⟨1149612, by rfl⟩ : syracuseStep 3065633 = 2299225) B2299225
theorem B2295611 : Blo 906576 2295611 := bstep (se 1 (by rfl) ⟨1721708, by rfl⟩ : syracuseStep 2295611 = 3443417) B3443417
theorem B1361723 : Blo 906576 1361723 := bstep (se 1 (by rfl) ⟨1021292, by rfl⟩ : syracuseStep 1361723 = 2042585) B2042585
theorem B9946955 : Blo 906576 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B4138867 : Blo 906576 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B1361783 : Blo 906576 1361783 := bstep (se 1 (by rfl) ⟨1021337, by rfl⟩ : syracuseStep 1361783 = 2042675) B2042675
theorem B1361807 : Blo 906576 1361807 := bstep (se 1 (by rfl) ⟨1021355, by rfl⟩ : syracuseStep 1361807 = 2042711) B2042711
theorem B1148843 : Blo 906576 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1361849 : Blo 906576 1361849 := bstep (se 2 (by rfl) ⟨510693, by rfl⟩ : syracuseStep 1361849 = 1021387) B1021387
theorem B1361927 : Blo 906576 1361927 := bstep (se 1 (by rfl) ⟨1021445, by rfl⟩ : syracuseStep 1361927 = 2042891) B2042891
theorem B2295823 : Blo 906576 2295823 := bstep (se 1 (by rfl) ⟨1721867, by rfl⟩ : syracuseStep 2295823 = 3443735) B3443735
theorem B21235729 : Blo 906576 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1361963 : Blo 906576 1361963 := bstep (se 1 (by rfl) ⟨1021472, by rfl⟩ : syracuseStep 1361963 = 2042945) B2042945
theorem B1361993 : Blo 906576 1361993 := bstep (se 2 (by rfl) ⟨510747, by rfl⟩ : syracuseStep 1361993 = 1021495) B1021495
theorem B2181239 : Blo 906576 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B2041991 : Blo 906576 2041991 := bstep (se 1 (by rfl) ⟨1531493, by rfl⟩ : syracuseStep 2041991 = 3062987) B3062987
theorem B1362107 : Blo 906576 1362107 := bstep (se 1 (by rfl) ⟨1021580, by rfl⟩ : syracuseStep 1362107 = 2043161) B2043161
theorem B1362167 : Blo 906576 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B3442945 : Blo 906576 3442945 := bstep (se 2 (by rfl) ⟨1291104, by rfl⟩ : syracuseStep 3442945 = 2582209) B2582209
theorem B1362191 : Blo 906576 1362191 := bstep (se 1 (by rfl) ⟨1021643, by rfl⟩ : syracuseStep 1362191 = 2043287) B2043287
theorem B2296097 : Blo 906576 2296097 := bstep (se 2 (by rfl) ⟨861036, by rfl⟩ : syracuseStep 2296097 = 1722073) B1722073
theorem B37234997 : Blo 906576 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B1362233 : Blo 906576 1362233 := bstep (se 2 (by rfl) ⟨510837, by rfl⟩ : syracuseStep 1362233 = 1021675) B1021675
theorem B2042171 : Blo 906576 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B4417907 : Blo 906576 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B3066227 : Blo 906576 3066227 := bstep (se 1 (by rfl) ⟨2299670, by rfl⟩ : syracuseStep 3066227 = 4599341) B4599341
theorem B1149319 : Blo 906576 1149319 := bstep (se 1 (by rfl) ⟨861989, by rfl⟩ : syracuseStep 1149319 = 1723979) B1723979
theorem B1362311 : Blo 906576 1362311 := bstep (se 1 (by rfl) ⟨1021733, by rfl⟩ : syracuseStep 1362311 = 2043467) B2043467
theorem B1362347 : Blo 906576 1362347 := bstep (se 1 (by rfl) ⟨1021760, by rfl⟩ : syracuseStep 1362347 = 2043521) B2043521
theorem B1722809 : Blo 906576 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B2042297 : Blo 906576 2042297 := bstep (se 2 (by rfl) ⟨765861, by rfl⟩ : syracuseStep 2042297 = 1531723) B1531723
theorem B1362377 : Blo 906576 1362377 := bstep (se 2 (by rfl) ⟨510891, by rfl⟩ : syracuseStep 1362377 = 1021783) B1021783
theorem B1362491 : Blo 906576 1362491 := bstep (se 1 (by rfl) ⟨1021868, by rfl⟩ : syracuseStep 1362491 = 2043737) B2043737
theorem B11045443 : Blo 906576 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B1362551 : Blo 906576 1362551 := bstep (se 1 (by rfl) ⟨1021913, by rfl⟩ : syracuseStep 1362551 = 2043827) B2043827
theorem B1362575 : Blo 906576 1362575 := bstep (se 1 (by rfl) ⟨1021931, by rfl⟩ : syracuseStep 1362575 = 2043863) B2043863
theorem B1362617 : Blo 906576 1362617 := bstep (se 2 (by rfl) ⟨510981, by rfl⟩ : syracuseStep 1362617 = 1021963) B1021963
theorem B26520281 : Blo 906576 26520281 := bstep (se 2 (by rfl) ⟨9945105, by rfl⟩ : syracuseStep 26520281 = 19890211) B19890211
theorem B1362695 : Blo 906576 1362695 := bstep (se 1 (by rfl) ⟨1022021, by rfl⟩ : syracuseStep 1362695 = 2044043) B2044043
theorem B2042639 : Blo 906576 2042639 := bstep (se 1 (by rfl) ⟨1531979, by rfl⟩ : syracuseStep 2042639 = 3063959) B3063959
theorem B2042657 : Blo 906576 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B1362731 : Blo 906576 1362731 := bstep (se 1 (by rfl) ⟨1022048, by rfl⟩ : syracuseStep 1362731 = 2044097) B2044097
theorem B6548273 : Blo 906576 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B1362761 : Blo 906576 1362761 := bstep (se 2 (by rfl) ⟨511035, by rfl⟩ : syracuseStep 1362761 = 1022071) B1022071
theorem B1149815 : Blo 906576 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B6892451 : Blo 906576 6892451 := bstep (se 1 (by rfl) ⟨5169338, by rfl⟩ : syracuseStep 6892451 = 10338677) B10338677
theorem B7760843 : Blo 906576 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B2583667 : Blo 906576 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B2042999 : Blo 906576 2042999 := bstep (se 1 (by rfl) ⟨1532249, by rfl⟩ : syracuseStep 2042999 = 3064499) B3064499
theorem B2297099 : Blo 906576 2297099 := bstep (se 1 (by rfl) ⟨1722824, by rfl⟩ : syracuseStep 2297099 = 3445649) B3445649
theorem B2043179 : Blo 906576 2043179 := bstep (se 1 (by rfl) ⟨1532384, by rfl⟩ : syracuseStep 2043179 = 3064769) B3064769
theorem B2583895 : Blo 906576 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B63688037 : Blo 906576 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B3681683 : Blo 906576 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B3272089 : Blo 906576 3272089 := bstep (se 2 (by rfl) ⟨1227033, by rfl⟩ : syracuseStep 3272089 = 2454067) B2454067
theorem B17428067 : Blo 906576 17428067 := bstep (se 1 (by rfl) ⟨13071050, by rfl⟩ : syracuseStep 17428067 = 26142101) B26142101
theorem B7761527 : Blo 906576 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B1552007 : Blo 906576 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B2043539 : Blo 906576 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B2043593 : Blo 906576 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B2068267 : Blo 906576 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B5820275 : Blo 906576 5820275 := bstep (se 1 (by rfl) ⟨4365206, by rfl⟩ : syracuseStep 5820275 = 8730413) B8730413
theorem B2297747 : Blo 906576 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B5173145 : Blo 906576 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B4362169 : Blo 906576 4362169 := bstep (se 2 (by rfl) ⟨1635813, by rfl⟩ : syracuseStep 4362169 = 3271627) B3271627
theorem B1019911 : Blo 906576 1019911 := bstep (se 1 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 1019911 = 1529867) B1529867
theorem B5820427 : Blo 906576 5820427 := bstep (se 1 (by rfl) ⟨4365320, by rfl⟩ : syracuseStep 5820427 = 8730641) B8730641
theorem B11038781 : Blo 906576 11038781 := bstep (se 3 (by rfl) ⟨2069771, by rfl⟩ : syracuseStep 11038781 = 4139543) B4139543
theorem B13455533 : Blo 906576 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B2298041 : Blo 906576 2298041 := bstep (se 2 (by rfl) ⟨861765, by rfl⟩ : syracuseStep 2298041 = 1723531) B1723531
theorem B1020091 : Blo 906576 1020091 := bstep (se 1 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 1020091 = 1530137) B1530137
theorem B4141313 : Blo 906576 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B1724807 : Blo 906576 1724807 := bstep (se 1 (by rfl) ⟨1293605, by rfl⟩ : syracuseStep 1724807 = 2587211) B2587211
theorem B2044295 : Blo 906576 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B16576913 : Blo 906576 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B2904473 : Blo 906576 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1020559 : Blo 906576 1020559 := bstep (se 1 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 1020559 = 1530839) B1530839
theorem B3273473 : Blo 906576 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B2519837 : Blo 906576 2519837 := bstep (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) B944939
theorem B2298739 : Blo 906576 2298739 := bstep (se 1 (by rfl) ⟨1724054, by rfl⟩ : syracuseStep 2298739 = 3448109) B3448109
theorem B2454391 : Blo 906576 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B2585479 : Blo 906576 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B4592537 : Blo 906576 4592537 := bstep (se 2 (by rfl) ⟨1722201, by rfl⟩ : syracuseStep 4592537 = 3444403) B3444403
theorem B3060665 : Blo 906576 3060665 := bstep (se 2 (by rfl) ⟨1147749, by rfl⟩ : syracuseStep 3060665 = 2295499) B2295499
theorem B2298881 : Blo 906576 2298881 := bstep (se 2 (by rfl) ⟨862080, by rfl⟩ : syracuseStep 2298881 = 1724161) B1724161
theorem B3683357 : Blo 906576 3683357 := bstep (se 3 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 3683357 = 1381259) B1381259
theorem B3445847 : Blo 906576 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1021063 : Blo 906576 1021063 := bstep (se 1 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 1021063 = 1531595) B1531595
theorem B2585753 : Blo 906576 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B6894881 : Blo 906576 6894881 := bstep (se 2 (by rfl) ⟨2585580, by rfl⟩ : syracuseStep 6894881 = 5171161) B5171161
theorem B1021243 : Blo 906576 1021243 := bstep (se 1 (by rfl) ⟨765932, by rfl⟩ : syracuseStep 1021243 = 1531865) B1531865
theorem B906631 : Blo 906576 906631 := bstep (se 1 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 906631 = 1359947) B1359947
theorem B5813639 : Blo 906576 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B906639 : Blo 906576 906639 := bstep (se 1 (by rfl) ⟨679979, by rfl⟩ : syracuseStep 906639 = 1359959) B1359959
theorem B1291663 : Blo 906576 1291663 := bstep (se 1 (by rfl) ⟨968747, by rfl⟩ : syracuseStep 1291663 = 1937495) B1937495
theorem B906683 : Blo 906576 906683 := bstep (se 1 (by rfl) ⟨680012, by rfl⟩ : syracuseStep 906683 = 1360025) B1360025
theorem B2618825 : Blo 906576 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2299337 : Blo 906576 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B906759 : Blo 906576 906759 := bstep (se 1 (by rfl) ⟨680069, by rfl⟩ : syracuseStep 906759 = 1360139) B1360139
theorem B1291783 : Blo 906576 1291783 := bstep (se 1 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 1291783 = 1937675) B1937675
theorem B3061259 : Blo 906576 3061259 := bstep (se 1 (by rfl) ⟨2295944, by rfl⟩ : syracuseStep 3061259 = 4591889) B4591889
theorem B906767 : Blo 906576 906767 := bstep (se 1 (by rfl) ⟨680075, by rfl⟩ : syracuseStep 906767 = 1360151) B1360151
theorem B906811 : Blo 906576 906811 := bstep (se 1 (by rfl) ⟨680108, by rfl⟩ : syracuseStep 906811 = 1360217) B1360217
theorem B3446333 : Blo 906576 3446333 := bstep (se 3 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 3446333 = 1292375) B1292375
theorem B3061367 : Blo 906576 3061367 := bstep (se 1 (by rfl) ⟨2296025, by rfl⟩ : syracuseStep 3061367 = 4592051) B4592051
theorem B906887 : Blo 906576 906887 := bstep (se 1 (by rfl) ⟨680165, by rfl⟩ : syracuseStep 906887 = 1360331) B1360331
theorem B906895 : Blo 906576 906895 := bstep (se 1 (by rfl) ⟨680171, by rfl⟩ : syracuseStep 906895 = 1360343) B1360343
theorem B906939 : Blo 906576 906939 := bstep (se 1 (by rfl) ⟨680204, by rfl⟩ : syracuseStep 906939 = 1360409) B1360409
theorem B6887105 : Blo 906576 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B907015 : Blo 906576 907015 := bstep (se 1 (by rfl) ⟨680261, by rfl⟩ : syracuseStep 907015 = 1360523) B1360523
theorem B907023 : Blo 906576 907023 := bstep (se 1 (by rfl) ⟨680267, by rfl⟩ : syracuseStep 907023 = 1360535) B1360535
theorem B1021711 : Blo 906576 1021711 := bstep (se 1 (by rfl) ⟨766283, by rfl⟩ : syracuseStep 1021711 = 1532567) B1532567
theorem B2586401 : Blo 906576 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B2299691 : Blo 906576 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B907067 : Blo 906576 907067 := bstep (se 1 (by rfl) ⟨680300, by rfl⟩ : syracuseStep 907067 = 1360601) B1360601
theorem B907143 : Blo 906576 907143 := bstep (se 1 (by rfl) ⟨680357, by rfl⟩ : syracuseStep 907143 = 1360715) B1360715
theorem B907151 : Blo 906576 907151 := bstep (se 1 (by rfl) ⟨680363, by rfl⟩ : syracuseStep 907151 = 1360727) B1360727
theorem B14931863 : Blo 906576 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B907195 : Blo 906576 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B17668043 : Blo 906576 17668043 := bstep (se 1 (by rfl) ⟨13251032, by rfl⟩ : syracuseStep 17668043 = 26502065) B26502065
theorem B907271 : Blo 906576 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B907279 : Blo 906576 907279 := bstep (se 1 (by rfl) ⟨680459, by rfl⟩ : syracuseStep 907279 = 1360919) B1360919
theorem B1226795 : Blo 906576 1226795 := bstep (se 1 (by rfl) ⟨920096, by rfl⟩ : syracuseStep 1226795 = 1840193) B1840193
theorem B907323 : Blo 906576 907323 := bstep (se 1 (by rfl) ⟨680492, by rfl⟩ : syracuseStep 907323 = 1360985) B1360985
theorem B10344509 : Blo 906576 10344509 := bstep (se 3 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 10344509 = 3879191) B3879191
theorem B2455667 : Blo 906576 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B1529975 : Blo 906576 1529975 := bstep (se 1 (by rfl) ⟨1147481, by rfl⟩ : syracuseStep 1529975 = 2294963) B2294963
theorem B907399 : Blo 906576 907399 := bstep (se 1 (by rfl) ⟨680549, by rfl⟩ : syracuseStep 907399 = 1361099) B1361099
theorem B907407 : Blo 906576 907407 := bstep (se 1 (by rfl) ⟨680555, by rfl⟩ : syracuseStep 907407 = 1361111) B1361111
theorem B907451 : Blo 906576 907451 := bstep (se 1 (by rfl) ⟨680588, by rfl⟩ : syracuseStep 907451 = 1361177) B1361177
theorem B3061961 : Blo 906576 3061961 := bstep (se 2 (by rfl) ⟨1148235, by rfl⟩ : syracuseStep 3061961 = 2296471) B2296471
theorem B6895853 : Blo 906576 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B907527 : Blo 906576 907527 := bstep (se 1 (by rfl) ⟨680645, by rfl⟩ : syracuseStep 907527 = 1361291) B1361291
theorem B907535 : Blo 906576 907535 := bstep (se 1 (by rfl) ⟨680651, by rfl⟩ : syracuseStep 907535 = 1361303) B1361303
theorem B907579 : Blo 906576 907579 := bstep (se 1 (by rfl) ⟨680684, by rfl⟩ : syracuseStep 907579 = 1361369) B1361369
theorem B907655 : Blo 906576 907655 := bstep (se 1 (by rfl) ⟨680741, by rfl⟩ : syracuseStep 907655 = 1361483) B1361483
theorem B907663 : Blo 906576 907663 := bstep (se 1 (by rfl) ⟨680747, by rfl⟩ : syracuseStep 907663 = 1361495) B1361495
theorem B5519801 : Blo 906576 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B907707 : Blo 906576 907707 := bstep (se 1 (by rfl) ⟨680780, by rfl⟩ : syracuseStep 907707 = 1361561) B1361561
theorem B907783 : Blo 906576 907783 := bstep (se 1 (by rfl) ⟨680837, by rfl⟩ : syracuseStep 907783 = 1361675) B1361675
theorem B907791 : Blo 906576 907791 := bstep (se 1 (by rfl) ⟨680843, by rfl⟩ : syracuseStep 907791 = 1361687) B1361687
theorem B1530427 : Blo 906576 1530427 := bstep (se 1 (by rfl) ⟨1147820, by rfl⟩ : syracuseStep 1530427 = 2295641) B2295641
theorem B907835 : Blo 906576 907835 := bstep (se 1 (by rfl) ⟨680876, by rfl⟩ : syracuseStep 907835 = 1361753) B1361753
theorem B27916919 : Blo 906576 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B907911 : Blo 906576 907911 := bstep (se 1 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 907911 = 1361867) B1361867
theorem B907919 : Blo 906576 907919 := bstep (se 1 (by rfl) ⟨680939, by rfl⟩ : syracuseStep 907919 = 1361879) B1361879
theorem B907963 : Blo 906576 907963 := bstep (se 1 (by rfl) ⟨680972, by rfl⟩ : syracuseStep 907963 = 1361945) B1361945
theorem B1530569 : Blo 906576 1530569 := bstep (se 2 (by rfl) ⟨573963, by rfl⟩ : syracuseStep 1530569 = 1147927) B1147927
theorem B5241581 : Blo 906576 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B908039 : Blo 906576 908039 := bstep (se 1 (by rfl) ⟨681029, by rfl⟩ : syracuseStep 908039 = 1362059) B1362059
theorem B908047 : Blo 906576 908047 := bstep (se 1 (by rfl) ⟨681035, by rfl⟩ : syracuseStep 908047 = 1362071) B1362071
theorem B908091 : Blo 906576 908091 := bstep (se 1 (by rfl) ⟨681068, by rfl⟩ : syracuseStep 908091 = 1362137) B1362137
theorem B3062663 : Blo 906576 3062663 := bstep (se 1 (by rfl) ⟨2296997, by rfl⟩ : syracuseStep 3062663 = 4593995) B4593995
theorem B908167 : Blo 906576 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B908175 : Blo 906576 908175 := bstep (se 1 (by rfl) ⟨681131, by rfl⟩ : syracuseStep 908175 = 1362263) B1362263
theorem B1293241 : Blo 906576 1293241 := bstep (se 2 (by rfl) ⟨484965, by rfl⟩ : syracuseStep 1293241 = 969931) B969931
theorem B908219 : Blo 906576 908219 := bstep (se 1 (by rfl) ⟨681164, by rfl⟩ : syracuseStep 908219 = 1362329) B1362329
theorem B14711813 : Blo 906576 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B908295 : Blo 906576 908295 := bstep (se 1 (by rfl) ⟨681221, by rfl⟩ : syracuseStep 908295 = 1362443) B1362443
theorem B7363595 : Blo 906576 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B908303 : Blo 906576 908303 := bstep (se 1 (by rfl) ⟨681227, by rfl⟩ : syracuseStep 908303 = 1362455) B1362455
theorem B908347 : Blo 906576 908347 := bstep (se 1 (by rfl) ⟨681260, by rfl⟩ : syracuseStep 908347 = 1362521) B1362521
theorem B908423 : Blo 906576 908423 := bstep (se 1 (by rfl) ⟨681317, by rfl⟩ : syracuseStep 908423 = 1362635) B1362635
theorem B908431 : Blo 906576 908431 := bstep (se 1 (by rfl) ⟨681323, by rfl⟩ : syracuseStep 908431 = 1362647) B1362647
theorem B908475 : Blo 906576 908475 := bstep (se 1 (by rfl) ⟨681356, by rfl⟩ : syracuseStep 908475 = 1362713) B1362713
theorem B17431757 : Blo 906576 17431757 := bstep (se 3 (by rfl) ⟨3268454, by rfl⟩ : syracuseStep 17431757 = 6536909) B6536909
theorem B3063041 : Blo 906576 3063041 := bstep (se 2 (by rfl) ⟨1148640, by rfl⟩ : syracuseStep 3063041 = 2297281) B2297281
theorem B908551 : Blo 906576 908551 := bstep (se 1 (by rfl) ⟨681413, by rfl⟩ : syracuseStep 908551 = 1362827) B1362827
theorem B3448079 : Blo 906576 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B908559 : Blo 906576 908559 := bstep (se 1 (by rfl) ⟨681419, by rfl⟩ : syracuseStep 908559 = 1362839) B1362839
theorem B1531271 : Blo 906576 1531271 := bstep (se 1 (by rfl) ⟨1148453, by rfl⟩ : syracuseStep 1531271 = 2296907) B2296907
theorem B5168519 : Blo 906576 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B4595129 : Blo 906576 4595129 := bstep (se 2 (by rfl) ⟨1723173, by rfl⟩ : syracuseStep 4595129 = 3446347) B3446347
theorem B3317201 : Blo 906576 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2907677 : Blo 906576 2907677 := bstep (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) B1090379
theorem B8724185 : Blo 906576 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B1359881 : Blo 906576 1359881 := bstep (se 2 (by rfl) ⟨509955, by rfl⟩ : syracuseStep 1359881 = 1019911) B1019911
theorem B26173469 : Blo 906576 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B19636253 : Blo 906576 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B1359911 : Blo 906576 1359911 := bstep (se 1 (by rfl) ⟨1019933, by rfl⟩ : syracuseStep 1359911 = 2039867) B2039867
theorem B2326607 : Blo 906576 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B8970355 : Blo 906576 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B1359995 : Blo 906576 1359995 := bstep (se 1 (by rfl) ⟨1019996, by rfl⟩ : syracuseStep 1359995 = 2039993) B2039993
theorem B1532027 : Blo 906576 1532027 := bstep (se 1 (by rfl) ⟨1149020, by rfl⟩ : syracuseStep 1532027 = 2298041) B2298041
theorem B2760875 : Blo 906576 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B1360121 : Blo 906576 1360121 := bstep (se 2 (by rfl) ⟨510045, by rfl⟩ : syracuseStep 1360121 = 1020091) B1020091
theorem B1360223 : Blo 906576 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B1360235 : Blo 906576 1360235 := bstep (se 1 (by rfl) ⟨1020176, by rfl⟩ : syracuseStep 1360235 = 2040353) B2040353
theorem B3064283 : Blo 906576 3064283 := bstep (se 1 (by rfl) ⟨2298212, by rfl⟩ : syracuseStep 3064283 = 4596425) B4596425
theorem B1532425 : Blo 906576 1532425 := bstep (se 2 (by rfl) ⟨574659, by rfl⟩ : syracuseStep 1532425 = 1149319) B1149319
theorem B1679891 : Blo 906576 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B99254807 : Blo 906576 99254807 := bstep (se 1 (by rfl) ⟨74441105, by rfl⟩ : syracuseStep 99254807 = 148882211) B148882211
theorem B1573433 : Blo 906576 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B1360463 : Blo 906576 1360463 := bstep (se 1 (by rfl) ⟨1020347, by rfl⟩ : syracuseStep 1360463 = 2040695) B2040695
theorem B2040443 : Blo 906576 2040443 := bstep (se 1 (by rfl) ⟨1530332, by rfl⟩ : syracuseStep 2040443 = 3060665) B3060665
theorem B1532587 : Blo 906576 1532587 := bstep (se 1 (by rfl) ⟨1149440, by rfl⟩ : syracuseStep 1532587 = 2298881) B2298881
theorem B1360583 : Blo 906576 1360583 := bstep (se 1 (by rfl) ⟨1020437, by rfl⟩ : syracuseStep 1360583 = 2040875) B2040875
theorem B2040569 : Blo 906576 2040569 := bstep (se 2 (by rfl) ⟨765213, by rfl⟩ : syracuseStep 2040569 = 1530427) B1530427
theorem B1360745 : Blo 906576 1360745 := bstep (se 2 (by rfl) ⟨510279, by rfl⟩ : syracuseStep 1360745 = 1020559) B1020559
theorem B4596587 : Blo 906576 4596587 := bstep (se 1 (by rfl) ⟨3447440, by rfl⟩ : syracuseStep 4596587 = 6894881) B6894881
theorem B3875759 : Blo 906576 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B4359095 : Blo 906576 4359095 := bstep (se 1 (by rfl) ⟨3269321, by rfl⟩ : syracuseStep 4359095 = 6538643) B6538643
theorem B1360823 : Blo 906576 1360823 := bstep (se 1 (by rfl) ⟨1020617, by rfl⟩ : syracuseStep 1360823 = 2041235) B2041235
theorem B1360859 : Blo 906576 1360859 := bstep (se 1 (by rfl) ⟨1020644, by rfl⟩ : syracuseStep 1360859 = 2041289) B2041289
theorem B1164251 : Blo 906576 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B11781085 : Blo 906576 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B1532891 : Blo 906576 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B1721351 : Blo 906576 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B2040839 : Blo 906576 2040839 := bstep (se 1 (by rfl) ⟨1530629, by rfl⟩ : syracuseStep 2040839 = 3061259) B3061259
theorem B44205101 : Blo 906576 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B2040911 : Blo 906576 2040911 := bstep (se 1 (by rfl) ⟨1530683, by rfl⟩ : syracuseStep 2040911 = 3061367) B3061367
theorem B3064985 : Blo 906576 3064985 := bstep (se 2 (by rfl) ⟨1149369, by rfl⟩ : syracuseStep 3064985 = 2298739) B2298739
theorem B1533127 : Blo 906576 1533127 := bstep (se 1 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 1533127 = 2299691) B2299691
theorem B9954575 : Blo 906576 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B1361327 : Blo 906576 1361327 := bstep (se 1 (by rfl) ⟨1020995, by rfl⟩ : syracuseStep 1361327 = 2041991) B2041991
theorem B2041307 : Blo 906576 2041307 := bstep (se 1 (by rfl) ⟨1530980, by rfl⟩ : syracuseStep 2041307 = 3061961) B3061961
theorem B4597235 : Blo 906576 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B1361417 : Blo 906576 1361417 := bstep (se 2 (by rfl) ⟨510531, by rfl⟩ : syracuseStep 1361417 = 1021063) B1021063
theorem B24823331 : Blo 906576 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B1361447 : Blo 906576 1361447 := bstep (se 1 (by rfl) ⟨1021085, by rfl⟩ : syracuseStep 1361447 = 2042171) B2042171
theorem B3679867 : Blo 906576 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B1361531 : Blo 906576 1361531 := bstep (se 1 (by rfl) ⟨1021148, by rfl⟩ : syracuseStep 1361531 = 2042297) B2042297
theorem B4138685 : Blo 906576 4138685 := bstep (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) B1552007
theorem B11339513 : Blo 906576 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B1361657 : Blo 906576 1361657 := bstep (se 2 (by rfl) ⟨510621, by rfl⟩ : syracuseStep 1361657 = 1021243) B1021243
theorem B17680187 : Blo 906576 17680187 := bstep (se 1 (by rfl) ⟨13260140, by rfl⟩ : syracuseStep 17680187 = 26520281) B26520281
theorem B1361759 : Blo 906576 1361759 := bstep (se 1 (by rfl) ⟨1021319, by rfl⟩ : syracuseStep 1361759 = 2042639) B2042639
theorem B1722217 : Blo 906576 1722217 := bstep (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) B1291663
theorem B1361771 : Blo 906576 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B2041775 : Blo 906576 2041775 := bstep (se 1 (by rfl) ⟨1531331, by rfl⟩ : syracuseStep 2041775 = 3062663) B3062663
theorem B9807875 : Blo 906576 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B1722377 : Blo 906576 1722377 := bstep (se 2 (by rfl) ⟨645891, by rfl⟩ : syracuseStep 1722377 = 1291783) B1291783
theorem B1361999 : Blo 906576 1361999 := bstep (se 1 (by rfl) ⟨1021499, by rfl⟩ : syracuseStep 1361999 = 2042999) B2042999
theorem B2042027 : Blo 906576 2042027 := bstep (se 1 (by rfl) ⟨1531520, by rfl⟩ : syracuseStep 2042027 = 3063041) B3063041
theorem B1362119 : Blo 906576 1362119 := bstep (se 1 (by rfl) ⟨1021589, by rfl⟩ : syracuseStep 1362119 = 2043179) B2043179
theorem B3066173 : Blo 906576 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B1362281 : Blo 906576 1362281 := bstep (se 2 (by rfl) ⟨510855, by rfl⟩ : syracuseStep 1362281 = 1021711) B1021711
theorem B11618711 : Blo 906576 11618711 := bstep (se 1 (by rfl) ⟨8714033, by rfl⟩ : syracuseStep 11618711 = 17428067) B17428067
theorem B1362359 : Blo 906576 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B1362395 : Blo 906576 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B7760569 : Blo 906576 7760569 := bstep (se 2 (by rfl) ⟨2910213, by rfl⟩ : syracuseStep 7760569 = 5820427) B5820427
theorem B28314305 : Blo 906576 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B2042567 : Blo 906576 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B7359187 : Blo 906576 7359187 := bstep (se 1 (by rfl) ⟨5519390, by rfl⟩ : syracuseStep 7359187 = 11038781) B11038781
theorem B4598531 : Blo 906576 4598531 := bstep (se 1 (by rfl) ⟨3448898, by rfl⟩ : syracuseStep 4598531 = 6897797) B6897797
theorem B1149871 : Blo 906576 1149871 := bstep (se 1 (by rfl) ⟨862403, by rfl⟩ : syracuseStep 1149871 = 1724807) B1724807
theorem B1362863 : Blo 906576 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B1936315 : Blo 906576 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B4590593 : Blo 906576 4590593 := bstep (se 2 (by rfl) ⟨1721472, by rfl⟩ : syracuseStep 4590593 = 3442945) B3442945
theorem B13085813 : Blo 906576 13085813 := bstep (se 5 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 13085813 = 1226795) B1226795
theorem B2182315 : Blo 906576 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B4418959 : Blo 906576 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B2297231 : Blo 906576 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B5819813 : Blo 906576 5819813 := bstep (se 4 (by rfl) ⟨545607, by rfl⟩ : syracuseStep 5819813 = 1091215) B1091215
theorem B1723835 : Blo 906576 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B2043431 : Blo 906576 2043431 := bstep (se 1 (by rfl) ⟨1532573, by rfl⟩ : syracuseStep 2043431 = 3065147) B3065147
theorem B2297555 : Blo 906576 2297555 := bstep (se 1 (by rfl) ⟨1723166, by rfl⟩ : syracuseStep 2297555 = 3446333) B3446333
theorem B6205177 : Blo 906576 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B4591403 : Blo 906576 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B1724267 : Blo 906576 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B2043755 : Blo 906576 2043755 := bstep (se 1 (by rfl) ⟨1532816, by rfl⟩ : syracuseStep 2043755 = 3065633) B3065633
theorem B6983533 : Blo 906576 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B6631303 : Blo 906576 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B1724321 : Blo 906576 1724321 := bstep (se 2 (by rfl) ⟨646620, by rfl⟩ : syracuseStep 1724321 = 1293241) B1293241
theorem B2043809 : Blo 906576 2043809 := bstep (se 2 (by rfl) ⟨766428, by rfl⟩ : syracuseStep 2043809 = 1532857) B1532857
theorem B7753805 : Blo 906576 7753805 := bstep (se 3 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 7753805 = 2907677) B2907677
theorem B1019983 : Blo 906576 1019983 := bstep (se 1 (by rfl) ⟨764987, by rfl⟩ : syracuseStep 1019983 = 1529975) B1529975
theorem B1454159 : Blo 906576 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B3444889 : Blo 906576 3444889 := bstep (se 2 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 3444889 = 2583667) B2583667
theorem B2044151 : Blo 906576 2044151 := bstep (se 1 (by rfl) ⟨1533113, by rfl⟩ : syracuseStep 2044151 = 3066227) B3066227
theorem B3445193 : Blo 906576 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B1020379 : Blo 906576 1020379 := bstep (se 1 (by rfl) ⟨765284, by rfl⟩ : syracuseStep 1020379 = 1530569) B1530569
theorem B3494387 : Blo 906576 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B3060233 : Blo 906576 3060233 := bstep (se 2 (by rfl) ⟨1147587, by rfl⟩ : syracuseStep 3060233 = 2295175) B2295175
theorem B4362785 : Blo 906576 4362785 := bstep (se 2 (by rfl) ⟨1636044, by rfl⟩ : syracuseStep 4362785 = 3272089) B3272089
theorem B5173895 : Blo 906576 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B11621171 : Blo 906576 11621171 := bstep (se 1 (by rfl) ⟨8715878, by rfl⟩ : syracuseStep 11621171 = 17431757) B17431757
theorem B14725961 : Blo 906576 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B2298719 : Blo 906576 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B1020847 : Blo 906576 1020847 := bstep (se 1 (by rfl) ⟨765635, by rfl⟩ : syracuseStep 1020847 = 1531271) B1531271
theorem B3445679 : Blo 906576 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B2454455 : Blo 906576 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B2757689 : Blo 906576 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B5174351 : Blo 906576 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B5518489 : Blo 906576 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B3880183 : Blo 906576 3880183 := bstep (se 1 (by rfl) ⟨2910137, by rfl⟩ : syracuseStep 3880183 = 5820275) B5820275
theorem B906591 : Blo 906576 906591 := bstep (se 1 (by rfl) ⟨679943, by rfl⟩ : syracuseStep 906591 = 1359887) B1359887
theorem B1021279 : Blo 906576 1021279 := bstep (se 1 (by rfl) ⟨765959, by rfl⟩ : syracuseStep 1021279 = 1531919) B1531919
theorem B3061097 : Blo 906576 3061097 := bstep (se 2 (by rfl) ⟨1147911, by rfl⟩ : syracuseStep 3061097 = 2295823) B2295823
theorem B906619 : Blo 906576 906619 := bstep (se 1 (by rfl) ⟨679964, by rfl⟩ : syracuseStep 906619 = 1359929) B1359929
theorem B906671 : Blo 906576 906671 := bstep (se 1 (by rfl) ⟨680003, by rfl⟩ : syracuseStep 906671 = 1360007) B1360007
theorem B906695 : Blo 906576 906695 := bstep (se 1 (by rfl) ⟨680021, by rfl⟩ : syracuseStep 906695 = 1360043) B1360043
theorem B906715 : Blo 906576 906715 := bstep (se 1 (by rfl) ⟨680036, by rfl⟩ : syracuseStep 906715 = 1360073) B1360073
theorem B906791 : Blo 906576 906791 := bstep (se 1 (by rfl) ⟨680093, by rfl⟩ : syracuseStep 906791 = 1360187) B1360187
theorem B906831 : Blo 906576 906831 := bstep (se 1 (by rfl) ⟨680123, by rfl⟩ : syracuseStep 906831 = 1360247) B1360247
theorem B906847 : Blo 906576 906847 := bstep (se 1 (by rfl) ⟨680135, by rfl⟩ : syracuseStep 906847 = 1360271) B1360271
theorem B906875 : Blo 906576 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B906927 : Blo 906576 906927 := bstep (se 1 (by rfl) ⟨680195, by rfl⟩ : syracuseStep 906927 = 1360391) B1360391
theorem B906951 : Blo 906576 906951 := bstep (se 1 (by rfl) ⟨680213, by rfl⟩ : syracuseStep 906951 = 1360427) B1360427
theorem B1021639 : Blo 906576 1021639 := bstep (se 1 (by rfl) ⟨766229, by rfl⟩ : syracuseStep 1021639 = 1532459) B1532459
theorem B906971 : Blo 906576 906971 := bstep (se 1 (by rfl) ⟨680228, by rfl⟩ : syracuseStep 906971 = 1360457) B1360457
theorem B6534893 : Blo 906576 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B907047 : Blo 906576 907047 := bstep (se 1 (by rfl) ⟨680285, by rfl⟩ : syracuseStep 907047 = 1360571) B1360571
theorem B907087 : Blo 906576 907087 := bstep (se 1 (by rfl) ⟨680315, by rfl⟩ : syracuseStep 907087 = 1360631) B1360631
theorem B907103 : Blo 906576 907103 := bstep (se 1 (by rfl) ⟨680327, by rfl⟩ : syracuseStep 907103 = 1360655) B1360655
theorem B5814125 : Blo 906576 5814125 := bstep (se 3 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 5814125 = 2180297) B2180297
theorem B907131 : Blo 906576 907131 := bstep (se 1 (by rfl) ⟨680348, by rfl⟩ : syracuseStep 907131 = 1360697) B1360697
theorem B907183 : Blo 906576 907183 := bstep (se 1 (by rfl) ⟨680387, by rfl⟩ : syracuseStep 907183 = 1360775) B1360775
theorem B2299823 : Blo 906576 2299823 := bstep (se 1 (by rfl) ⟨1724867, by rfl⟩ : syracuseStep 2299823 = 3449735) B3449735
theorem B3061691 : Blo 906576 3061691 := bstep (se 1 (by rfl) ⟨2296268, by rfl⟩ : syracuseStep 3061691 = 4592537) B4592537
theorem B907207 : Blo 906576 907207 := bstep (se 1 (by rfl) ⟨680405, by rfl⟩ : syracuseStep 907207 = 1360811) B1360811
theorem B907227 : Blo 906576 907227 := bstep (se 1 (by rfl) ⟨680420, by rfl⟩ : syracuseStep 907227 = 1360841) B1360841
theorem B2906113 : Blo 906576 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B4593671 : Blo 906576 4593671 := bstep (se 1 (by rfl) ⟨3445253, by rfl⟩ : syracuseStep 4593671 = 6890507) B6890507
theorem B2455571 : Blo 906576 2455571 := bstep (se 1 (by rfl) ⟨1841678, by rfl⟩ : syracuseStep 2455571 = 3683357) B3683357
theorem B907303 : Blo 906576 907303 := bstep (se 1 (by rfl) ⟨680477, by rfl⟩ : syracuseStep 907303 = 1360955) B1360955
theorem B907343 : Blo 906576 907343 := bstep (se 1 (by rfl) ⟨680507, by rfl⟩ : syracuseStep 907343 = 1361015) B1361015
theorem B1841231 : Blo 906576 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B14727257 : Blo 906576 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B907359 : Blo 906576 907359 := bstep (se 1 (by rfl) ⟨680519, by rfl⟩ : syracuseStep 907359 = 1361039) B1361039
theorem B907387 : Blo 906576 907387 := bstep (se 1 (by rfl) ⟨680540, by rfl⟩ : syracuseStep 907387 = 1361081) B1361081
theorem B907439 : Blo 906576 907439 := bstep (se 1 (by rfl) ⟨680579, by rfl⟩ : syracuseStep 907439 = 1361159) B1361159
theorem B907463 : Blo 906576 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B907483 : Blo 906576 907483 := bstep (se 1 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 907483 = 1361225) B1361225
theorem B1530103 : Blo 906576 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B169834765 : Blo 906576 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B907559 : Blo 906576 907559 := bstep (se 1 (by rfl) ⟨680669, by rfl⟩ : syracuseStep 907559 = 1361339) B1361339
theorem B907599 : Blo 906576 907599 := bstep (se 1 (by rfl) ⟨680699, by rfl⟩ : syracuseStep 907599 = 1361399) B1361399
theorem B907615 : Blo 906576 907615 := bstep (se 1 (by rfl) ⟨680711, by rfl⟩ : syracuseStep 907615 = 1361423) B1361423
theorem B11032937 : Blo 906576 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B907643 : Blo 906576 907643 := bstep (se 1 (by rfl) ⟨680732, by rfl⟩ : syracuseStep 907643 = 1361465) B1361465
theorem B10328471 : Blo 906576 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B907695 : Blo 906576 907695 := bstep (se 1 (by rfl) ⟨680771, by rfl⟩ : syracuseStep 907695 = 1361543) B1361543
theorem B1530299 : Blo 906576 1530299 := bstep (se 1 (by rfl) ⟨1147724, by rfl⟩ : syracuseStep 1530299 = 2295449) B2295449
theorem B907719 : Blo 906576 907719 := bstep (se 1 (by rfl) ⟨680789, by rfl⟩ : syracuseStep 907719 = 1361579) B1361579
theorem B907739 : Blo 906576 907739 := bstep (se 1 (by rfl) ⟨680804, by rfl⟩ : syracuseStep 907739 = 1361609) B1361609
theorem B4594157 : Blo 906576 4594157 := bstep (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) B1722809
theorem B3447305 : Blo 906576 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B1530407 : Blo 906576 1530407 := bstep (se 1 (by rfl) ⟨1147805, by rfl⟩ : syracuseStep 1530407 = 2295611) B2295611
theorem B907815 : Blo 906576 907815 := bstep (se 1 (by rfl) ⟨680861, by rfl⟩ : syracuseStep 907815 = 1361723) B1361723
theorem B907855 : Blo 906576 907855 := bstep (se 1 (by rfl) ⟨680891, by rfl⟩ : syracuseStep 907855 = 1361783) B1361783
theorem B907871 : Blo 906576 907871 := bstep (se 1 (by rfl) ⟨680903, by rfl⟩ : syracuseStep 907871 = 1361807) B1361807
theorem B907899 : Blo 906576 907899 := bstep (se 1 (by rfl) ⟨680924, by rfl⟩ : syracuseStep 907899 = 1361849) B1361849
theorem B11778695 : Blo 906576 11778695 := bstep (se 1 (by rfl) ⟨8834021, by rfl⟩ : syracuseStep 11778695 = 17668043) B17668043
theorem B907951 : Blo 906576 907951 := bstep (se 1 (by rfl) ⟨680963, by rfl⟩ : syracuseStep 907951 = 1361927) B1361927
theorem B907975 : Blo 906576 907975 := bstep (se 1 (by rfl) ⟨680981, by rfl⟩ : syracuseStep 907975 = 1361963) B1361963
theorem B6896339 : Blo 906576 6896339 := bstep (se 1 (by rfl) ⟨5172254, by rfl⟩ : syracuseStep 6896339 = 10344509) B10344509
theorem B907995 : Blo 906576 907995 := bstep (se 1 (by rfl) ⟨680996, by rfl⟩ : syracuseStep 907995 = 1361993) B1361993
theorem B1637111 : Blo 906576 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B908071 : Blo 906576 908071 := bstep (se 1 (by rfl) ⟨681053, by rfl⟩ : syracuseStep 908071 = 1362107) B1362107
theorem B1530697 : Blo 906576 1530697 := bstep (se 2 (by rfl) ⟨574011, by rfl⟩ : syracuseStep 1530697 = 1148023) B1148023
theorem B908111 : Blo 906576 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B908127 : Blo 906576 908127 := bstep (se 1 (by rfl) ⟨681095, by rfl⟩ : syracuseStep 908127 = 1362191) B1362191
theorem B1530731 : Blo 906576 1530731 := bstep (se 1 (by rfl) ⟨1148048, by rfl⟩ : syracuseStep 1530731 = 2296097) B2296097
theorem B908155 : Blo 906576 908155 := bstep (se 1 (by rfl) ⟨681116, by rfl⟩ : syracuseStep 908155 = 1362233) B1362233
theorem B908207 : Blo 906576 908207 := bstep (se 1 (by rfl) ⟨681155, by rfl⟩ : syracuseStep 908207 = 1362311) B1362311
theorem B908231 : Blo 906576 908231 := bstep (se 1 (by rfl) ⟨681173, by rfl⟩ : syracuseStep 908231 = 1362347) B1362347
theorem B908251 : Blo 906576 908251 := bstep (se 1 (by rfl) ⟨681188, by rfl⟩ : syracuseStep 908251 = 1362377) B1362377
theorem B908327 : Blo 906576 908327 := bstep (se 1 (by rfl) ⟨681245, by rfl⟩ : syracuseStep 908327 = 1362491) B1362491
theorem B18611279 : Blo 906576 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B908367 : Blo 906576 908367 := bstep (se 1 (by rfl) ⟨681275, by rfl⟩ : syracuseStep 908367 = 1362551) B1362551
theorem B908383 : Blo 906576 908383 := bstep (se 1 (by rfl) ⟨681287, by rfl⟩ : syracuseStep 908383 = 1362575) B1362575
theorem B908411 : Blo 906576 908411 := bstep (se 1 (by rfl) ⟨681308, by rfl⟩ : syracuseStep 908411 = 1362617) B1362617
theorem B908463 : Blo 906576 908463 := bstep (se 1 (by rfl) ⟨681347, by rfl⟩ : syracuseStep 908463 = 1362695) B1362695
theorem B908487 : Blo 906576 908487 := bstep (se 1 (by rfl) ⟨681365, by rfl⟩ : syracuseStep 908487 = 1362731) B1362731
theorem B4365515 : Blo 906576 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B908507 : Blo 906576 908507 := bstep (se 1 (by rfl) ⟨681380, by rfl⟩ : syracuseStep 908507 = 1362761) B1362761
theorem B1531129 : Blo 906576 1531129 := bstep (se 2 (by rfl) ⟨574173, by rfl⟩ : syracuseStep 1531129 = 1148347) B1148347
theorem B4594967 : Blo 906576 4594967 := bstep (se 1 (by rfl) ⟨3446225, by rfl⟩ : syracuseStep 4594967 = 6892451) B6892451
theorem B13090085 : Blo 906576 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B14925181 : Blo 906576 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B1531399 : Blo 906576 1531399 := bstep (se 1 (by rfl) ⟨1148549, by rfl⟩ : syracuseStep 1531399 = 2297099) B2297099
theorem B3063419 : Blo 906576 3063419 := bstep (se 1 (by rfl) ⟨2297564, by rfl⟩ : syracuseStep 3063419 = 4595129) B4595129
theorem B2211467 : Blo 906576 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B3063581 : Blo 906576 3063581 := bstep (se 3 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 3063581 = 1148843) B1148843
theorem B5816123 : Blo 906576 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B5816225 : Blo 906576 5816225 := bstep (se 2 (by rfl) ⟨2181084, by rfl⟩ : syracuseStep 5816225 = 4362169) B4362169
theorem B1531831 : Blo 906576 1531831 := bstep (se 1 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 1531831 = 2297747) B2297747
theorem B3448763 : Blo 906576 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B3874817 : Blo 906576 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B17448979 : Blo 906576 17448979 := bstep (se 1 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 17448979 = 26173469) B26173469
theorem B13090835 : Blo 906576 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B5169203 : Blo 906576 5169203 := bstep (se 1 (by rfl) ⟨3876902, by rfl⟩ : syracuseStep 5169203 = 7753805) B7753805
theorem B1359977 : Blo 906576 1359977 := bstep (se 2 (by rfl) ⟨509991, by rfl⟩ : syracuseStep 1359977 = 1019983) B1019983
theorem B11960473 : Blo 906576 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B2040137 : Blo 906576 2040137 := bstep (se 2 (by rfl) ⟨765051, by rfl⟩ : syracuseStep 2040137 = 1530103) B1530103
theorem B2040155 : Blo 906576 2040155 := bstep (se 1 (by rfl) ⟨1530116, by rfl⟩ : syracuseStep 2040155 = 3060233) B3060233
theorem B2908523 : Blo 906576 2908523 := bstep (se 1 (by rfl) ⟨2181392, by rfl⟩ : syracuseStep 2908523 = 4362785) B4362785
theorem B1048955 : Blo 906576 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B1360295 : Blo 906576 1360295 := bstep (se 1 (by rfl) ⟨1020221, by rfl⟩ : syracuseStep 1360295 = 2040443) B2040443
theorem B3449263 : Blo 906576 3449263 := bstep (se 1 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 3449263 = 5173895) B5173895
theorem B1360379 : Blo 906576 1360379 := bstep (se 1 (by rfl) ⟨1020284, by rfl⟩ : syracuseStep 1360379 = 2040569) B2040569
theorem B1532479 : Blo 906576 1532479 := bstep (se 1 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 1532479 = 2298719) B2298719
theorem B3064391 : Blo 906576 3064391 := bstep (se 1 (by rfl) ⟨2298293, by rfl⟩ : syracuseStep 3064391 = 4596587) B4596587
theorem B1360505 : Blo 906576 1360505 := bstep (se 2 (by rfl) ⟨510189, by rfl⟩ : syracuseStep 1360505 = 1020379) B1020379
theorem B1360559 : Blo 906576 1360559 := bstep (se 1 (by rfl) ⟨1020419, by rfl⟩ : syracuseStep 1360559 = 2040839) B2040839
theorem B1360607 : Blo 906576 1360607 := bstep (se 1 (by rfl) ⟨1020455, by rfl⟩ : syracuseStep 1360607 = 2040911) B2040911
theorem B3449567 : Blo 906576 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B6636383 : Blo 906576 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B2040731 : Blo 906576 2040731 := bstep (se 1 (by rfl) ⟨1530548, by rfl⟩ : syracuseStep 2040731 = 3061097) B3061097
theorem B10347425 : Blo 906576 10347425 := bstep (se 2 (by rfl) ⟨3880284, by rfl⟩ : syracuseStep 10347425 = 7760569) B7760569
theorem B1360871 : Blo 906576 1360871 := bstep (se 1 (by rfl) ⟨1020653, by rfl⟩ : syracuseStep 1360871 = 2041307) B2041307
theorem B3064823 : Blo 906576 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B16548887 : Blo 906576 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B2040929 : Blo 906576 2040929 := bstep (se 2 (by rfl) ⟨765348, by rfl⟩ : syracuseStep 2040929 = 1530697) B1530697
theorem B1361129 : Blo 906576 1361129 := bstep (se 2 (by rfl) ⟨510423, by rfl⟩ : syracuseStep 1361129 = 1020847) B1020847
theorem B1533161 : Blo 906576 1533161 := bstep (se 2 (by rfl) ⟨574935, by rfl⟩ : syracuseStep 1533161 = 1149871) B1149871
theorem B3876083 : Blo 906576 3876083 := bstep (se 1 (by rfl) ⟨2907062, by rfl⟩ : syracuseStep 3876083 = 5814125) B5814125
theorem B1361183 : Blo 906576 1361183 := bstep (se 1 (by rfl) ⟨1020887, by rfl⟩ : syracuseStep 1361183 = 2041775) B2041775
theorem B1533215 : Blo 906576 1533215 := bstep (se 1 (by rfl) ⟨1149911, by rfl⟩ : syracuseStep 1533215 = 2299823) B2299823
theorem B2041127 : Blo 906576 2041127 := bstep (se 1 (by rfl) ⟨1530845, by rfl⟩ : syracuseStep 2041127 = 3061691) B3061691
theorem B6538583 : Blo 906576 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B1148251 : Blo 906576 1148251 := bstep (se 1 (by rfl) ⟨861188, by rfl⟩ : syracuseStep 1148251 = 1722377) B1722377
theorem B1361351 : Blo 906576 1361351 := bstep (se 1 (by rfl) ⟨1021013, by rfl⟩ : syracuseStep 1361351 = 2042027) B2042027
theorem B7357985 : Blo 906576 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B2909753 : Blo 906576 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B2041505 : Blo 906576 2041505 := bstep (se 2 (by rfl) ⟨765564, by rfl⟩ : syracuseStep 2041505 = 1531129) B1531129
theorem B1361705 : Blo 906576 1361705 := bstep (se 2 (by rfl) ⟨510639, by rfl⟩ : syracuseStep 1361705 = 1021279) B1021279
theorem B18876203 : Blo 906576 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B1361711 : Blo 906576 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B4597559 : Blo 906576 4597559 := bstep (se 1 (by rfl) ⟨3448169, by rfl⟩ : syracuseStep 4597559 = 6896339) B6896339
theorem B19900241 : Blo 906576 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B3065687 : Blo 906576 3065687 := bstep (se 1 (by rfl) ⟨2299265, by rfl⟩ : syracuseStep 3065687 = 4598531) B4598531
theorem B5891945 : Blo 906576 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B2041865 : Blo 906576 2041865 := bstep (se 2 (by rfl) ⟨765699, by rfl⟩ : syracuseStep 2041865 = 1531399) B1531399
theorem B2910343 : Blo 906576 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B8726723 : Blo 906576 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B1362185 : Blo 906576 1362185 := bstep (se 2 (by rfl) ⟨510819, by rfl⟩ : syracuseStep 1362185 = 1021639) B1021639
theorem B4598045 : Blo 906576 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B1149223 : Blo 906576 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1362287 : Blo 906576 1362287 := bstep (se 1 (by rfl) ⟨1021715, by rfl⟩ : syracuseStep 1362287 = 2043431) B2043431
theorem B2042279 : Blo 906576 2042279 := bstep (se 1 (by rfl) ⟨1531709, by rfl⟩ : syracuseStep 2042279 = 3063419) B3063419
theorem B2296289 : Blo 906576 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B8841737 : Blo 906576 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B2042387 : Blo 906576 2042387 := bstep (se 1 (by rfl) ⟨1531790, by rfl⟩ : syracuseStep 2042387 = 3063581) B3063581
theorem B3877415 : Blo 906576 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B1362503 : Blo 906576 1362503 := bstep (se 1 (by rfl) ⟨1021877, by rfl⟩ : syracuseStep 1362503 = 2043755) B2043755
theorem B2042441 : Blo 906576 2042441 := bstep (se 2 (by rfl) ⟨765915, by rfl⟩ : syracuseStep 2042441 = 1531831) B1531831
theorem B3877483 : Blo 906576 3877483 := bstep (se 1 (by rfl) ⟨2908112, by rfl⟩ : syracuseStep 3877483 = 5816225) B5816225
theorem B1149547 : Blo 906576 1149547 := bstep (se 1 (by rfl) ⟨862160, by rfl⟩ : syracuseStep 1149547 = 1724321) B1724321
theorem B1362539 : Blo 906576 1362539 := bstep (se 1 (by rfl) ⟨1021904, by rfl⟩ : syracuseStep 1362539 = 2043809) B2043809
theorem B4590269 : Blo 906576 4590269 := bstep (se 3 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 4590269 = 1721351) B1721351
theorem B1551071 : Blo 906576 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B1362767 : Blo 906576 1362767 := bstep (se 1 (by rfl) ⟨1022075, by rfl⟩ : syracuseStep 1362767 = 2044151) B2044151
theorem B3877757 : Blo 906576 3877757 := bstep (se 3 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 3877757 = 1454159) B1454159
theorem B4909949 : Blo 906576 4909949 := bstep (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) B1841231
theorem B2296795 : Blo 906576 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B2042855 : Blo 906576 2042855 := bstep (se 1 (by rfl) ⟨1532141, by rfl⟩ : syracuseStep 2042855 = 3064283) B3064283
theorem B2329591 : Blo 906576 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B66169871 : Blo 906576 66169871 := bstep (se 1 (by rfl) ⟨49627403, by rfl⟩ : syracuseStep 66169871 = 99254807) B99254807
theorem B226446353 : Blo 906576 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B9817307 : Blo 906576 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B2583839 : Blo 906576 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B2297119 : Blo 906576 2297119 := bstep (se 1 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 2297119 = 3445679) B3445679
theorem B2043233 : Blo 906576 2043233 := bstep (se 2 (by rfl) ⟨766212, by rfl⟩ : syracuseStep 2043233 = 1532425) B1532425
theorem B29470067 : Blo 906576 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B1838459 : Blo 906576 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B2043323 : Blo 906576 2043323 := bstep (se 1 (by rfl) ⟨1532492, by rfl⟩ : syracuseStep 2043323 = 3064985) B3064985
theorem B2043449 : Blo 906576 2043449 := bstep (se 2 (by rfl) ⟨766293, by rfl⟩ : syracuseStep 2043449 = 1532587) B1532587
theorem B15708113 : Blo 906576 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B9818171 : Blo 906576 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B23588981 : Blo 906576 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B2044115 : Blo 906576 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B2044169 : Blo 906576 2044169 := bstep (se 2 (by rfl) ⟨766563, by rfl⟩ : syracuseStep 2044169 = 1533127) B1533127
theorem B7745807 : Blo 906576 7745807 := bstep (se 1 (by rfl) ⟨5809355, by rfl⟩ : syracuseStep 7745807 = 11618711) B11618711
theorem B6885647 : Blo 906576 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B1020199 : Blo 906576 1020199 := bstep (se 1 (by rfl) ⟨765149, by rfl⟩ : syracuseStep 1020199 = 1530299) B1530299
theorem B5173577 : Blo 906576 5173577 := bstep (se 2 (by rfl) ⟨1940091, by rfl⟩ : syracuseStep 5173577 = 3880183) B3880183
theorem B2298203 : Blo 906576 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B1020271 : Blo 906576 1020271 := bstep (se 1 (by rfl) ⟨765203, by rfl⟩ : syracuseStep 1020271 = 1530407) B1530407
theorem B7852463 : Blo 906576 7852463 := bstep (se 1 (by rfl) ⟨5889347, by rfl⟩ : syracuseStep 7852463 = 11778695) B11778695
theorem B1020487 : Blo 906576 1020487 := bstep (se 1 (by rfl) ⟨765365, by rfl⟩ : syracuseStep 1020487 = 1530731) B1530731
theorem B3060395 : Blo 906576 3060395 := bstep (se 1 (by rfl) ⟨2295296, by rfl⟩ : syracuseStep 3060395 = 4590593) B4590593
theorem B12407519 : Blo 906576 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B3879875 : Blo 906576 3879875 := bstep (se 1 (by rfl) ⟨2909906, by rfl⟩ : syracuseStep 3879875 = 5819813) B5819813
theorem B10327013 : Blo 906576 10327013 := bstep (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) B1936315
theorem B9311377 : Blo 906576 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B3060935 : Blo 906576 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B2299175 : Blo 906576 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B906587 : Blo 906576 906587 := bstep (se 1 (by rfl) ⟨679940, by rfl⟩ : syracuseStep 906587 = 1359881) B1359881
theorem B906607 : Blo 906576 906607 := bstep (se 1 (by rfl) ⟨679955, by rfl⟩ : syracuseStep 906607 = 1359911) B1359911
theorem B906663 : Blo 906576 906663 := bstep (se 1 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 906663 = 1359995) B1359995
theorem B1021351 : Blo 906576 1021351 := bstep (se 1 (by rfl) ⟨766013, by rfl⟩ : syracuseStep 1021351 = 1532027) B1532027
theorem B1840583 : Blo 906576 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B906747 : Blo 906576 906747 := bstep (se 1 (by rfl) ⟨680060, by rfl⟩ : syracuseStep 906747 = 1360121) B1360121
theorem B4593185 : Blo 906576 4593185 := bstep (se 2 (by rfl) ⟨1722444, by rfl⟩ : syracuseStep 4593185 = 3444889) B3444889
theorem B906815 : Blo 906576 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B906823 : Blo 906576 906823 := bstep (se 1 (by rfl) ⟨680117, by rfl⟩ : syracuseStep 906823 = 1360235) B1360235
theorem B906975 : Blo 906576 906975 := bstep (se 1 (by rfl) ⟨680231, by rfl⟩ : syracuseStep 906975 = 1360463) B1360463
theorem B907055 : Blo 906576 907055 := bstep (se 1 (by rfl) ⟨680291, by rfl⟩ : syracuseStep 907055 = 1360583) B1360583
theorem B7747447 : Blo 906576 7747447 := bstep (se 1 (by rfl) ⟨5810585, by rfl⟩ : syracuseStep 7747447 = 11621171) B11621171
theorem B907163 : Blo 906576 907163 := bstep (se 1 (by rfl) ⟨680372, by rfl⟩ : syracuseStep 907163 = 1360745) B1360745
theorem B2906063 : Blo 906576 2906063 := bstep (se 1 (by rfl) ⟨2179547, by rfl⟩ : syracuseStep 2906063 = 4359095) B4359095
theorem B907215 : Blo 906576 907215 := bstep (se 1 (by rfl) ⟨680411, by rfl⟩ : syracuseStep 907215 = 1360823) B1360823
theorem B907239 : Blo 906576 907239 := bstep (se 1 (by rfl) ⟨680429, by rfl⟩ : syracuseStep 907239 = 1360859) B1360859
theorem B1021927 : Blo 906576 1021927 := bstep (se 1 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 1021927 = 1532891) B1532891
theorem B9812249 : Blo 906576 9812249 := bstep (se 2 (by rfl) ⟨3679593, by rfl⟩ : syracuseStep 9812249 = 7359187) B7359187
theorem B907551 : Blo 906576 907551 := bstep (se 1 (by rfl) ⟨680663, by rfl⟩ : syracuseStep 907551 = 1361327) B1361327
theorem B907611 : Blo 906576 907611 := bstep (se 1 (by rfl) ⟨680708, by rfl⟩ : syracuseStep 907611 = 1361417) B1361417
theorem B907631 : Blo 906576 907631 := bstep (se 1 (by rfl) ⟨680723, by rfl⟩ : syracuseStep 907631 = 1361447) B1361447
theorem B907687 : Blo 906576 907687 := bstep (se 1 (by rfl) ⟨680765, by rfl⟩ : syracuseStep 907687 = 1361531) B1361531
theorem B2759123 : Blo 906576 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B4356595 : Blo 906576 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B7559675 : Blo 906576 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B907771 : Blo 906576 907771 := bstep (se 1 (by rfl) ⟨680828, by rfl⟩ : syracuseStep 907771 = 1361657) B1361657
theorem B11786791 : Blo 906576 11786791 := bstep (se 1 (by rfl) ⟨8840093, by rfl⟩ : syracuseStep 11786791 = 17680187) B17680187
theorem B907839 : Blo 906576 907839 := bstep (se 1 (by rfl) ⟨680879, by rfl⟩ : syracuseStep 907839 = 1361759) B1361759
theorem B907847 : Blo 906576 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B33094277 : Blo 906576 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B3062447 : Blo 906576 3062447 := bstep (se 1 (by rfl) ⟨2296835, by rfl⟩ : syracuseStep 3062447 = 4593671) B4593671
theorem B1637047 : Blo 906576 1637047 := bstep (se 1 (by rfl) ⟨1227785, by rfl⟩ : syracuseStep 1637047 = 2455571) B2455571
theorem B4479709 : Blo 906576 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B907999 : Blo 906576 907999 := bstep (se 1 (by rfl) ⟨680999, by rfl⟩ : syracuseStep 907999 = 1361999) B1361999
theorem B908079 : Blo 906576 908079 := bstep (se 1 (by rfl) ⟨681059, by rfl⟩ : syracuseStep 908079 = 1362119) B1362119
theorem B7355291 : Blo 906576 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B908187 : Blo 906576 908187 := bstep (se 1 (by rfl) ⟨681140, by rfl⟩ : syracuseStep 908187 = 1362281) B1362281
theorem B908239 : Blo 906576 908239 := bstep (se 1 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 908239 = 1362359) B1362359
theorem B908263 : Blo 906576 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B3062771 : Blo 906576 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B908575 : Blo 906576 908575 := bstep (se 1 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 908575 = 1362863) B1362863
theorem B4365629 : Blo 906576 4365629 := bstep (se 3 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 4365629 = 1637111) B1637111
theorem B8723875 : Blo 906576 8723875 := bstep (se 1 (by rfl) ⟨6542906, by rfl⟩ : syracuseStep 8723875 = 13085813) B13085813
theorem B4906489 : Blo 906576 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B3063311 : Blo 906576 3063311 := bstep (se 1 (by rfl) ⟨2297483, by rfl⟩ : syracuseStep 3063311 = 4594967) B4594967
theorem B1531487 : Blo 906576 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B1531703 : Blo 906576 1531703 := bstep (se 1 (by rfl) ⟨1148777, by rfl⟩ : syracuseStep 1531703 = 2297555) B2297555
theorem B6545213 : Blo 906576 6545213 := bstep (se 3 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 6545213 = 2454455) B2454455
theorem B3104669 : Blo 906576 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B23265305 : Blo 906576 23265305 := bstep (se 2 (by rfl) ⟨8724489, by rfl⟩ : syracuseStep 23265305 = 17448979) B17448979
theorem B6545447 : Blo 906576 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B44130365 : Blo 906576 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B1360091 : Blo 906576 1360091 := bstep (se 1 (by rfl) ⟨1020068, by rfl⟩ : syracuseStep 1360091 = 2040137) B2040137
theorem B3449051 : Blo 906576 3449051 := bstep (se 1 (by rfl) ⟨2586788, by rfl⟩ : syracuseStep 3449051 = 5173577) B5173577
theorem B1360103 : Blo 906576 1360103 := bstep (se 1 (by rfl) ⟨1020077, by rfl⟩ : syracuseStep 1360103 = 2040155) B2040155
theorem B1532135 : Blo 906576 1532135 := bstep (se 1 (by rfl) ⟨1149101, by rfl⟩ : syracuseStep 1532135 = 2298203) B2298203
theorem B5234975 : Blo 906576 5234975 := bstep (se 1 (by rfl) ⟨3926231, by rfl⟩ : syracuseStep 5234975 = 7852463) B7852463
theorem B1360265 : Blo 906576 1360265 := bstep (se 2 (by rfl) ⟨510099, by rfl⟩ : syracuseStep 1360265 = 1020199) B1020199
theorem B1532297 : Blo 906576 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B2040263 : Blo 906576 2040263 := bstep (se 1 (by rfl) ⟨1530197, by rfl⟩ : syracuseStep 2040263 = 3060395) B3060395
theorem B1360361 : Blo 906576 1360361 := bstep (se 2 (by rfl) ⟨510135, by rfl⟩ : syracuseStep 1360361 = 1020271) B1020271
theorem B4424255 : Blo 906576 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B1360487 : Blo 906576 1360487 := bstep (se 1 (by rfl) ⟨1020365, by rfl⟩ : syracuseStep 1360487 = 2040731) B2040731
theorem B6898283 : Blo 906576 6898283 := bstep (se 1 (by rfl) ⟨5173712, by rfl⟩ : syracuseStep 6898283 = 10347425) B10347425
theorem B5808793 : Blo 906576 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B1360619 : Blo 906576 1360619 := bstep (se 1 (by rfl) ⟨1020464, by rfl⟩ : syracuseStep 1360619 = 2040929) B2040929
theorem B1360649 : Blo 906576 1360649 := bstep (se 2 (by rfl) ⟨510243, by rfl⟩ : syracuseStep 1360649 = 1020487) B1020487
theorem B2040623 : Blo 906576 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B5169977 : Blo 906576 5169977 := bstep (se 2 (by rfl) ⟨1938741, by rfl⟩ : syracuseStep 5169977 = 3877483) B3877483
theorem B1532729 : Blo 906576 1532729 := bstep (se 2 (by rfl) ⟨574773, by rfl⟩ : syracuseStep 1532729 = 1149547) B1149547
theorem B1360751 : Blo 906576 1360751 := bstep (se 1 (by rfl) ⟨1020563, by rfl⟩ : syracuseStep 1360751 = 2041127) B2041127
theorem B1532783 : Blo 906576 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B5972945 : Blo 906576 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B1361003 : Blo 906576 1361003 := bstep (se 1 (by rfl) ⟨1020752, by rfl⟩ : syracuseStep 1361003 = 2041505) B2041505
theorem B12584135 : Blo 906576 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B3065039 : Blo 906576 3065039 := bstep (se 1 (by rfl) ⟨2298779, by rfl⟩ : syracuseStep 3065039 = 4597559) B4597559
theorem B7357661 : Blo 906576 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B3106121 : Blo 906576 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B1361243 : Blo 906576 1361243 := bstep (se 1 (by rfl) ⟨1020932, by rfl⟩ : syracuseStep 1361243 = 2041865) B2041865
theorem B23577965 : Blo 906576 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B5817815 : Blo 906576 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B3065363 : Blo 906576 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B1361519 : Blo 906576 1361519 := bstep (se 1 (by rfl) ⟨1021139, by rfl⟩ : syracuseStep 1361519 = 2042279) B2042279
theorem B5039783 : Blo 906576 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B1361591 : Blo 906576 1361591 := bstep (se 1 (by rfl) ⟨1021193, by rfl⟩ : syracuseStep 1361591 = 2042387) B2042387
theorem B1361627 : Blo 906576 1361627 := bstep (se 1 (by rfl) ⟨1021220, by rfl⟩ : syracuseStep 1361627 = 2042441) B2042441
theorem B22062851 : Blo 906576 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B2041631 : Blo 906576 2041631 := bstep (se 1 (by rfl) ⟨1531223, by rfl⟩ : syracuseStep 2041631 = 3062447) B3062447
theorem B1034047 : Blo 906576 1034047 := bstep (se 1 (by rfl) ⟨775535, by rfl⟩ : syracuseStep 1034047 = 1551071) B1551071
theorem B1361801 : Blo 906576 1361801 := bstep (se 2 (by rfl) ⟨510675, by rfl⟩ : syracuseStep 1361801 = 1021351) B1021351
theorem B1361903 : Blo 906576 1361903 := bstep (se 1 (by rfl) ⟨1021427, by rfl⟩ : syracuseStep 1361903 = 2042855) B2042855
theorem B2041847 : Blo 906576 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B150964235 : Blo 906576 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1722559 : Blo 906576 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B2910419 : Blo 906576 2910419 := bstep (se 1 (by rfl) ⟨2182814, by rfl⟩ : syracuseStep 2910419 = 4365629) B4365629
theorem B1362155 : Blo 906576 1362155 := bstep (se 1 (by rfl) ⟨1021616, by rfl⟩ : syracuseStep 1362155 = 2043233) B2043233
theorem B19646711 : Blo 906576 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B1362215 : Blo 906576 1362215 := bstep (se 1 (by rfl) ⟨1021661, by rfl⟩ : syracuseStep 1362215 = 2043323) B2043323
theorem B2042207 : Blo 906576 2042207 := bstep (se 1 (by rfl) ⟨1531655, by rfl⟩ : syracuseStep 2042207 = 3063311) B3063311
theorem B1362299 : Blo 906576 1362299 := bstep (se 1 (by rfl) ⟨1021724, by rfl⟩ : syracuseStep 1362299 = 2043449) B2043449
theorem B19614109 : Blo 906576 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B1362569 : Blo 906576 1362569 := bstep (se 2 (by rfl) ⟨510963, by rfl⟩ : syracuseStep 1362569 = 1021927) B1021927
theorem B10472075 : Blo 906576 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B10332845 : Blo 906576 10332845 := bstep (se 3 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 10332845 = 3874817) B3874817
theorem B8727223 : Blo 906576 8727223 := bstep (se 1 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 8727223 = 13090835) B13090835
theorem B1362743 : Blo 906576 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1362779 : Blo 906576 1362779 := bstep (se 1 (by rfl) ⟨1022084, by rfl⟩ : syracuseStep 1362779 = 2044169) B2044169
theorem B5163871 : Blo 906576 5163871 := bstep (se 1 (by rfl) ⟨3872903, by rfl⟩ : syracuseStep 5163871 = 7745807) B7745807
theorem B4590431 : Blo 906576 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B2042927 : Blo 906576 2042927 := bstep (se 1 (by rfl) ⟨1532195, by rfl⟩ : syracuseStep 2042927 = 3064391) B3064391
theorem B4599017 : Blo 906576 4599017 := bstep (se 2 (by rfl) ⟨1724631, by rfl⟩ : syracuseStep 4599017 = 3449263) B3449263
theorem B6884675 : Blo 906576 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B2043215 : Blo 906576 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B15715721 : Blo 906576 15715721 := bstep (se 2 (by rfl) ⟨5893395, by rfl⟩ : syracuseStep 15715721 = 11786791) B11786791
theorem B2043305 : Blo 906576 2043305 := bstep (se 2 (by rfl) ⟨766239, by rfl⟩ : syracuseStep 2043305 = 1532479) B1532479
theorem B2584055 : Blo 906576 2584055 := bstep (se 1 (by rfl) ⟨1938041, by rfl⟩ : syracuseStep 2584055 = 3876083) B3876083
theorem B17436221 : Blo 906576 17436221 := bstep (se 3 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 17436221 = 6538583) B6538583
theorem B2182729 : Blo 906576 2182729 := bstep (se 2 (by rfl) ⟨818523, by rfl⟩ : syracuseStep 2182729 = 1637047) B1637047
theorem B13266827 : Blo 906576 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B2043791 : Blo 906576 2043791 := bstep (se 1 (by rfl) ⟨1532843, by rfl⟩ : syracuseStep 2043791 = 3065687) B3065687
theorem B1937375 : Blo 906576 1937375 := bstep (se 1 (by rfl) ⟨1453031, by rfl⟩ : syracuseStep 1937375 = 2906063) B2906063
theorem B6541499 : Blo 906576 6541499 := bstep (se 1 (by rfl) ⟨4906124, by rfl⟩ : syracuseStep 6541499 = 9812249) B9812249
theorem B12415169 : Blo 906576 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B2584943 : Blo 906576 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B3060179 : Blo 906576 3060179 := bstep (se 1 (by rfl) ⟨2295134, by rfl⟩ : syracuseStep 3060179 = 4590269) B4590269
theorem B2585171 : Blo 906576 2585171 := bstep (se 1 (by rfl) ⟨1938878, by rfl⟩ : syracuseStep 2585171 = 3877757) B3877757
theorem B3273299 : Blo 906576 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B6541985 : Blo 906576 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B1225639 : Blo 906576 1225639 := bstep (se 1 (by rfl) ⟨919229, by rfl⟩ : syracuseStep 1225639 = 1838459) B1838459
theorem B1020991 : Blo 906576 1020991 := bstep (se 1 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 1020991 = 1531487) B1531487
theorem B8279117 : Blo 906576 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B1021135 : Blo 906576 1021135 := bstep (se 1 (by rfl) ⟨765851, by rfl⟩ : syracuseStep 1021135 = 1531703) B1531703
theorem B4363475 : Blo 906576 4363475 := bstep (se 1 (by rfl) ⟨3272606, by rfl⟩ : syracuseStep 4363475 = 6545213) B6545213
theorem B3446135 : Blo 906576 3446135 := bstep (se 1 (by rfl) ⟨2584601, by rfl⟩ : syracuseStep 3446135 = 5169203) B5169203
theorem B906651 : Blo 906576 906651 := bstep (se 1 (by rfl) ⟨679988, by rfl⟩ : syracuseStep 906651 = 1359977) B1359977
theorem B15725987 : Blo 906576 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B3880457 : Blo 906576 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B15947297 : Blo 906576 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B1939015 : Blo 906576 1939015 := bstep (se 1 (by rfl) ⟨1454261, by rfl⟩ : syracuseStep 1939015 = 2908523) B2908523
theorem B906863 : Blo 906576 906863 := bstep (se 1 (by rfl) ⟨680147, by rfl⟩ : syracuseStep 906863 = 1360295) B1360295
theorem B906919 : Blo 906576 906919 := bstep (se 1 (by rfl) ⟨680189, by rfl⟩ : syracuseStep 906919 = 1360379) B1360379
theorem B907003 : Blo 906576 907003 := bstep (se 1 (by rfl) ⟨680252, by rfl⟩ : syracuseStep 907003 = 1360505) B1360505
theorem B907039 : Blo 906576 907039 := bstep (se 1 (by rfl) ⟨680279, by rfl⟩ : syracuseStep 907039 = 1360559) B1360559
theorem B8271679 : Blo 906576 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B907071 : Blo 906576 907071 := bstep (se 1 (by rfl) ⟨680303, by rfl⟩ : syracuseStep 907071 = 1360607) B1360607
theorem B2299711 : Blo 906576 2299711 := bstep (se 1 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 2299711 = 3449567) B3449567
theorem B2586583 : Blo 906576 2586583 := bstep (se 1 (by rfl) ⟨1939937, by rfl⟩ : syracuseStep 2586583 = 3879875) B3879875
theorem B907247 : Blo 906576 907247 := bstep (se 1 (by rfl) ⟨680435, by rfl⟩ : syracuseStep 907247 = 1360871) B1360871
theorem B907419 : Blo 906576 907419 := bstep (se 1 (by rfl) ⟨680564, by rfl⟩ : syracuseStep 907419 = 1361129) B1361129
theorem B1022107 : Blo 906576 1022107 := bstep (se 1 (by rfl) ⟨766580, by rfl⟩ : syracuseStep 1022107 = 1533161) B1533161
theorem B907455 : Blo 906576 907455 := bstep (se 1 (by rfl) ⟨680591, by rfl⟩ : syracuseStep 907455 = 1361183) B1361183
theorem B1022143 : Blo 906576 1022143 := bstep (se 1 (by rfl) ⟨766607, by rfl⟩ : syracuseStep 1022143 = 1533215) B1533215
theorem B907567 : Blo 906576 907567 := bstep (se 1 (by rfl) ⟨680675, by rfl⟩ : syracuseStep 907567 = 1361351) B1361351
theorem B1227055 : Blo 906576 1227055 := bstep (se 1 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 1227055 = 1840583) B1840583
theorem B3062123 : Blo 906576 3062123 := bstep (se 1 (by rfl) ⟨2296592, by rfl⟩ : syracuseStep 3062123 = 4593185) B4593185
theorem B4905323 : Blo 906576 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B1939835 : Blo 906576 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B907803 : Blo 906576 907803 := bstep (se 1 (by rfl) ⟨680852, by rfl⟩ : syracuseStep 907803 = 1361705) B1361705
theorem B907807 : Blo 906576 907807 := bstep (se 1 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 907807 = 1361711) B1361711
theorem B11188853 : Blo 906576 11188853 := bstep (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) B1048955
theorem B3062393 : Blo 906576 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B908123 : Blo 906576 908123 := bstep (se 1 (by rfl) ⟨681092, by rfl⟩ : syracuseStep 908123 = 1362185) B1362185
theorem B908191 : Blo 906576 908191 := bstep (se 1 (by rfl) ⟨681143, by rfl⟩ : syracuseStep 908191 = 1362287) B1362287
theorem B1530859 : Blo 906576 1530859 := bstep (se 1 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 1530859 = 2296289) B2296289
theorem B3062825 : Blo 906576 3062825 := bstep (se 2 (by rfl) ⟨1148559, by rfl⟩ : syracuseStep 3062825 = 2297119) B2297119
theorem B908335 : Blo 906576 908335 := bstep (se 1 (by rfl) ⟨681251, by rfl⟩ : syracuseStep 908335 = 1362503) B1362503
theorem B908359 : Blo 906576 908359 := bstep (se 1 (by rfl) ⟨681269, by rfl⟩ : syracuseStep 908359 = 1362539) B1362539
theorem B1531001 : Blo 906576 1531001 := bstep (se 2 (by rfl) ⟨574125, by rfl⟩ : syracuseStep 1531001 = 1148251) B1148251
theorem B11631833 : Blo 906576 11631833 := bstep (se 2 (by rfl) ⟨4361937, by rfl⟩ : syracuseStep 11631833 = 8723875) B8723875
theorem B908511 : Blo 906576 908511 := bstep (se 1 (by rfl) ⟨681383, by rfl⟩ : syracuseStep 908511 = 1362767) B1362767
theorem B44113247 : Blo 906576 44113247 := bstep (se 1 (by rfl) ⟨33084935, by rfl⟩ : syracuseStep 44113247 = 66169871) B66169871
theorem B6544871 : Blo 906576 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B15711853 : Blo 906576 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B10329929 : Blo 906576 10329929 := bstep (se 2 (by rfl) ⟨3873723, by rfl⟩ : syracuseStep 10329929 = 7747447) B7747447
theorem B3489983 : Blo 906576 3489983 := bstep (se 1 (by rfl) ⟨2617487, by rfl⟩ : syracuseStep 3489983 = 5234975) B5234975
theorem B1360175 : Blo 906576 1360175 := bstep (se 1 (by rfl) ⟨1020131, by rfl⟩ : syracuseStep 1360175 = 2040263) B2040263
theorem B2040119 : Blo 906576 2040119 := bstep (se 1 (by rfl) ⟨1530089, by rfl⟩ : syracuseStep 2040119 = 3060179) B3060179
theorem B2949503 : Blo 906576 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B1360415 : Blo 906576 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B8389423 : Blo 906576 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B8282989 : Blo 906576 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B3359855 : Blo 906576 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B1361087 : Blo 906576 1361087 := bstep (se 1 (by rfl) ⟨1020815, by rfl⟩ : syracuseStep 1361087 = 2041631) B2041631
theorem B2041145 : Blo 906576 2041145 := bstep (se 2 (by rfl) ⟨765429, by rfl⟩ : syracuseStep 2041145 = 1530859) B1530859
theorem B1361231 : Blo 906576 1361231 := bstep (se 1 (by rfl) ⟨1020923, by rfl⟩ : syracuseStep 1361231 = 2041847) B2041847
theorem B1361321 : Blo 906576 1361321 := bstep (se 2 (by rfl) ⟨510495, by rfl⟩ : syracuseStep 1361321 = 1020991) B1020991
theorem B1361471 : Blo 906576 1361471 := bstep (se 1 (by rfl) ⟨1021103, by rfl⟩ : syracuseStep 1361471 = 2042207) B2042207
theorem B2041415 : Blo 906576 2041415 := bstep (se 1 (by rfl) ⟨1531061, by rfl⟩ : syracuseStep 2041415 = 3062123) B3062123
theorem B3270215 : Blo 906576 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B1361513 : Blo 906576 1361513 := bstep (se 2 (by rfl) ⟨510567, by rfl⟩ : syracuseStep 1361513 = 1021135) B1021135
theorem B2041595 : Blo 906576 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B6981383 : Blo 906576 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B2041883 : Blo 906576 2041883 := bstep (se 1 (by rfl) ⟨1531412, by rfl⟩ : syracuseStep 2041883 = 3062825) B3062825
theorem B1361951 : Blo 906576 1361951 := bstep (se 1 (by rfl) ⟨1021463, by rfl⟩ : syracuseStep 1361951 = 2042927) B2042927
theorem B2910305 : Blo 906576 2910305 := bstep (se 2 (by rfl) ⟨1091364, by rfl⟩ : syracuseStep 2910305 = 2182729) B2182729
theorem B20949137 : Blo 906576 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B3066011 : Blo 906576 3066011 := bstep (se 1 (by rfl) ⟨2299508, by rfl⟩ : syracuseStep 3066011 = 4599017) B4599017
theorem B4589783 : Blo 906576 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B1362143 : Blo 906576 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B1362203 : Blo 906576 1362203 := bstep (se 1 (by rfl) ⟨1021652, by rfl⟩ : syracuseStep 1362203 = 2043305) B2043305
theorem B1722703 : Blo 906576 1722703 := bstep (se 1 (by rfl) ⟨1292027, by rfl⟩ : syracuseStep 1722703 = 2584055) B2584055
theorem B11028905 : Blo 906576 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B1378729 : Blo 906576 1378729 := bstep (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) B1034047
theorem B3066281 : Blo 906576 3066281 := bstep (se 2 (by rfl) ⟨1149855, by rfl⟩ : syracuseStep 3066281 = 2299711) B2299711
theorem B15927853 : Blo 906576 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B1362527 : Blo 906576 1362527 := bstep (se 1 (by rfl) ⟨1021895, by rfl⟩ : syracuseStep 1362527 = 2043791) B2043791
theorem B15510203 : Blo 906576 15510203 := bstep (se 1 (by rfl) ⟨11632652, by rfl⟩ : syracuseStep 15510203 = 23265305) B23265305
theorem B29420243 : Blo 906576 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B4360999 : Blo 906576 4360999 := bstep (se 1 (by rfl) ⟨3270749, by rfl⟩ : syracuseStep 4360999 = 6541499) B6541499
theorem B8276779 : Blo 906576 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1362809 : Blo 906576 1362809 := bstep (se 2 (by rfl) ⟨511053, by rfl⟩ : syracuseStep 1362809 = 1022107) B1022107
theorem B1723295 : Blo 906576 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B2296745 : Blo 906576 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B1362857 : Blo 906576 1362857 := bstep (se 2 (by rfl) ⟨511071, by rfl⟩ : syracuseStep 1362857 = 1022143) B1022143
theorem B1723447 : Blo 906576 1723447 := bstep (se 1 (by rfl) ⟨1292585, by rfl⟩ : syracuseStep 1723447 = 2585171) B2585171
theorem B2182199 : Blo 906576 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B4598855 : Blo 906576 4598855 := bstep (se 1 (by rfl) ⟨3449141, by rfl⟩ : syracuseStep 4598855 = 6898283) B6898283
theorem B4361323 : Blo 906576 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B26152145 : Blo 906576 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B11635933 : Blo 906576 11635933 := bstep (se 3 (by rfl) ⟨2181737, by rfl⟩ : syracuseStep 11635933 = 4363475) B4363475
theorem B2043359 : Blo 906576 2043359 := bstep (se 1 (by rfl) ⟨1532519, by rfl⟩ : syracuseStep 2043359 = 3065039) B3065039
theorem B7745057 : Blo 906576 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B11636297 : Blo 906576 11636297 := bstep (se 2 (by rfl) ⟨4363611, by rfl⟩ : syracuseStep 11636297 = 8727223) B8727223
theorem B2297423 : Blo 906576 2297423 := bstep (se 1 (by rfl) ⟨1723067, by rfl⟩ : syracuseStep 2297423 = 3446135) B3446135
theorem B3878543 : Blo 906576 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B5172893 : Blo 906576 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B2043575 : Blo 906576 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B6885161 : Blo 906576 6885161 := bstep (se 2 (by rfl) ⟨2581935, by rfl⟩ : syracuseStep 6885161 = 5163871) B5163871
theorem B14708567 : Blo 906576 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1634185 : Blo 906576 1634185 := bstep (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) B1225639
theorem B100642823 : Blo 906576 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B7459235 : Blo 906576 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B3060287 : Blo 906576 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B1020667 : Blo 906576 1020667 := bstep (se 1 (by rfl) ⟨765500, by rfl⟩ : syracuseStep 1020667 = 1531001) B1531001
theorem B2585353 : Blo 906576 2585353 := bstep (se 2 (by rfl) ⟨969507, by rfl⟩ : syracuseStep 2585353 = 1939015) B1939015
theorem B7754555 : Blo 906576 7754555 := bstep (se 1 (by rfl) ⟨5815916, by rfl⟩ : syracuseStep 7754555 = 11631833) B11631833
theorem B4363247 : Blo 906576 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B6886619 : Blo 906576 6886619 := bstep (se 1 (by rfl) ⟨5164964, by rfl⟩ : syracuseStep 6886619 = 10329929) B10329929
theorem B8844551 : Blo 906576 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B1291583 : Blo 906576 1291583 := bstep (se 1 (by rfl) ⟨968687, by rfl⟩ : syracuseStep 1291583 = 1937375) B1937375
theorem B4363631 : Blo 906576 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B906727 : Blo 906576 906727 := bstep (se 1 (by rfl) ⟨680045, by rfl⟩ : syracuseStep 906727 = 1360091) B1360091
theorem B2299367 : Blo 906576 2299367 := bstep (se 1 (by rfl) ⟨1724525, by rfl⟩ : syracuseStep 2299367 = 3449051) B3449051
theorem B906735 : Blo 906576 906735 := bstep (se 1 (by rfl) ⟨680051, by rfl⟩ : syracuseStep 906735 = 1360103) B1360103
theorem B1021423 : Blo 906576 1021423 := bstep (se 1 (by rfl) ⟨766067, by rfl⟩ : syracuseStep 1021423 = 1532135) B1532135
theorem B906843 : Blo 906576 906843 := bstep (se 1 (by rfl) ⟨680132, by rfl⟩ : syracuseStep 906843 = 1360265) B1360265
theorem B1021531 : Blo 906576 1021531 := bstep (se 1 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 1021531 = 1532297) B1532297
theorem B906907 : Blo 906576 906907 := bstep (se 1 (by rfl) ⟨680180, by rfl⟩ : syracuseStep 906907 = 1360361) B1360361
theorem B1636073 : Blo 906576 1636073 := bstep (se 2 (by rfl) ⟨613527, by rfl⟩ : syracuseStep 1636073 = 1227055) B1227055
theorem B906991 : Blo 906576 906991 := bstep (se 1 (by rfl) ⟨680243, by rfl⟩ : syracuseStep 906991 = 1360487) B1360487
theorem B907079 : Blo 906576 907079 := bstep (se 1 (by rfl) ⟨680309, by rfl⟩ : syracuseStep 907079 = 1360619) B1360619
theorem B907099 : Blo 906576 907099 := bstep (se 1 (by rfl) ⟨680324, by rfl⟩ : syracuseStep 907099 = 1360649) B1360649
theorem B3446651 : Blo 906576 3446651 := bstep (se 1 (by rfl) ⟨2584988, by rfl⟩ : syracuseStep 3446651 = 5169977) B5169977
theorem B1021819 : Blo 906576 1021819 := bstep (se 1 (by rfl) ⟨766364, by rfl⟩ : syracuseStep 1021819 = 1532729) B1532729
theorem B907167 : Blo 906576 907167 := bstep (se 1 (by rfl) ⟨680375, by rfl⟩ : syracuseStep 907167 = 1360751) B1360751
theorem B1021855 : Blo 906576 1021855 := bstep (se 1 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 1021855 = 1532783) B1532783
theorem B5519411 : Blo 906576 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B907335 : Blo 906576 907335 := bstep (se 1 (by rfl) ⟨680501, by rfl⟩ : syracuseStep 907335 = 1361003) B1361003
theorem B4905107 : Blo 906576 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B907495 : Blo 906576 907495 := bstep (se 1 (by rfl) ⟨680621, by rfl⟩ : syracuseStep 907495 = 1361243) B1361243
theorem B15718643 : Blo 906576 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B10483991 : Blo 906576 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B2586971 : Blo 906576 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B41908589 : Blo 906576 41908589 := bstep (se 3 (by rfl) ⟨7857860, by rfl⟩ : syracuseStep 41908589 = 15715721) B15715721
theorem B10631531 : Blo 906576 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B907679 : Blo 906576 907679 := bstep (se 1 (by rfl) ⟨680759, by rfl⟩ : syracuseStep 907679 = 1361519) B1361519
theorem B907727 : Blo 906576 907727 := bstep (se 1 (by rfl) ⟨680795, by rfl⟩ : syracuseStep 907727 = 1361591) B1361591
theorem B907751 : Blo 906576 907751 := bstep (se 1 (by rfl) ⟨680813, by rfl⟩ : syracuseStep 907751 = 1361627) B1361627
theorem B907867 : Blo 906576 907867 := bstep (se 1 (by rfl) ⟨680900, by rfl⟩ : syracuseStep 907867 = 1361801) B1361801
theorem B907935 : Blo 906576 907935 := bstep (se 1 (by rfl) ⟨680951, by rfl⟩ : syracuseStep 907935 = 1361903) B1361903
theorem B1940279 : Blo 906576 1940279 := bstep (se 1 (by rfl) ⟨1455209, by rfl⟩ : syracuseStep 1940279 = 2910419) B2910419
theorem B908103 : Blo 906576 908103 := bstep (se 1 (by rfl) ⟨681077, by rfl⟩ : syracuseStep 908103 = 1362155) B1362155
theorem B13097807 : Blo 906576 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B908143 : Blo 906576 908143 := bstep (se 1 (by rfl) ⟨681107, by rfl⟩ : syracuseStep 908143 = 1362215) B1362215
theorem B908199 : Blo 906576 908199 := bstep (se 1 (by rfl) ⟨681149, by rfl⟩ : syracuseStep 908199 = 1362299) B1362299
theorem B908379 : Blo 906576 908379 := bstep (se 1 (by rfl) ⟨681284, by rfl⟩ : syracuseStep 908379 = 1362569) B1362569
theorem B6888563 : Blo 906576 6888563 := bstep (se 1 (by rfl) ⟨5166422, by rfl⟩ : syracuseStep 6888563 = 10332845) B10332845
theorem B908495 : Blo 906576 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B908519 : Blo 906576 908519 := bstep (se 1 (by rfl) ⟨681389, by rfl⟩ : syracuseStep 908519 = 1362779) B1362779
theorem B29408831 : Blo 906576 29408831 := bstep (se 1 (by rfl) ⟨22056623, by rfl⟩ : syracuseStep 29408831 = 44113247) B44113247
theorem B11624147 : Blo 906576 11624147 := bstep (se 1 (by rfl) ⟨8718110, by rfl⟩ : syracuseStep 11624147 = 17436221) B17436221
theorem B3448777 : Blo 906576 3448777 := bstep (se 2 (by rfl) ⟨1293291, by rfl⟩ : syracuseStep 3448777 = 2586583) B2586583
theorem B2326655 : Blo 906576 2326655 := bstep (se 1 (by rfl) ⟨1744991, by rfl⟩ : syracuseStep 2326655 = 3489983) B3489983
theorem B1360079 : Blo 906576 1360079 := bstep (se 1 (by rfl) ⟨1020059, by rfl⟩ : syracuseStep 1360079 = 2040119) B2040119
theorem B4972823 : Blo 906576 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B2040191 : Blo 906576 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B5169703 : Blo 906576 5169703 := bstep (se 1 (by rfl) ⟨3877277, by rfl⟩ : syracuseStep 5169703 = 7754555) B7754555
theorem B2908831 : Blo 906576 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B1360763 : Blo 906576 1360763 := bstep (se 1 (by rfl) ⟨1020572, by rfl⟩ : syracuseStep 1360763 = 2041145) B2041145
theorem B2909087 : Blo 906576 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B1532911 : Blo 906576 1532911 := bstep (se 1 (by rfl) ⟨1149683, by rfl⟩ : syracuseStep 1532911 = 2299367) B2299367
theorem B1360889 : Blo 906576 1360889 := bstep (se 2 (by rfl) ⟨510333, by rfl⟩ : syracuseStep 1360889 = 1020667) B1020667
theorem B1360943 : Blo 906576 1360943 := bstep (se 1 (by rfl) ⟨1020707, by rfl⟩ : syracuseStep 1360943 = 2041415) B2041415
theorem B2180143 : Blo 906576 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B11035705 : Blo 906576 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B11043985 : Blo 906576 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B1090715 : Blo 906576 1090715 := bstep (se 1 (by rfl) ⟨818036, by rfl⟩ : syracuseStep 1090715 = 1636073) B1636073
theorem B1361063 : Blo 906576 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B4654255 : Blo 906576 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B1361255 : Blo 906576 1361255 := bstep (se 1 (by rfl) ⟨1020941, by rfl⟩ : syracuseStep 1361255 = 2041883) B2041883
theorem B3679607 : Blo 906576 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B3270071 : Blo 906576 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B10479095 : Blo 906576 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B6989327 : Blo 906576 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B10340135 : Blo 906576 10340135 := bstep (se 1 (by rfl) ⟨7755101, by rfl⟩ : syracuseStep 10340135 = 15510203) B15510203
theorem B19613495 : Blo 906576 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B1361897 : Blo 906576 1361897 := bstep (se 2 (by rfl) ⟨510711, by rfl⟩ : syracuseStep 1361897 = 1021423) B1021423
theorem B3065903 : Blo 906576 3065903 := bstep (se 1 (by rfl) ⟨2299427, by rfl⟩ : syracuseStep 3065903 = 4598855) B4598855
theorem B1362041 : Blo 906576 1362041 := bstep (se 2 (by rfl) ⟨510765, by rfl⟩ : syracuseStep 1362041 = 1021531) B1021531
theorem B17434763 : Blo 906576 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B1362239 : Blo 906576 1362239 := bstep (se 1 (by rfl) ⟨1021679, by rfl⟩ : syracuseStep 1362239 = 2043359) B2043359
theorem B5163371 : Blo 906576 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B19605887 : Blo 906576 19605887 := bstep (se 1 (by rfl) ⟨14704415, by rfl⟩ : syracuseStep 19605887 = 29408831) B29408831
theorem B1362383 : Blo 906576 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B1362425 : Blo 906576 1362425 := bstep (se 2 (by rfl) ⟨510909, by rfl⟩ : syracuseStep 1362425 = 1021819) B1021819
theorem B4590107 : Blo 906576 4590107 := bstep (se 1 (by rfl) ⟨3442580, by rfl⟩ : syracuseStep 4590107 = 6885161) B6885161
theorem B1362473 : Blo 906576 1362473 := bstep (se 2 (by rfl) ⟨510927, by rfl⟩ : syracuseStep 1362473 = 1021855) B1021855
theorem B4598369 : Blo 906576 4598369 := bstep (se 2 (by rfl) ⟨1724388, by rfl⟩ : syracuseStep 4598369 = 3448777) B3448777
theorem B67095215 : Blo 906576 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B5819197 : Blo 906576 5819197 := bstep (se 3 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 5819197 = 2182199) B2182199
theorem B2296937 : Blo 906576 2296937 := bstep (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) B1722703
theorem B1838305 : Blo 906576 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B21237137 : Blo 906576 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B2239903 : Blo 906576 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B4591079 : Blo 906576 4591079 := bstep (se 1 (by rfl) ⟨3443309, by rfl⟩ : syracuseStep 4591079 = 6886619) B6886619
theorem B3444221 : Blo 906576 3444221 := bstep (se 3 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 3444221 = 1291583) B1291583
theorem B11185897 : Blo 906576 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B2297767 : Blo 906576 2297767 := bstep (se 1 (by rfl) ⟨1723325, by rfl⟩ : syracuseStep 2297767 = 3446651) B3446651
theorem B31461365 : Blo 906576 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B2297929 : Blo 906576 2297929 := bstep (se 2 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 2297929 = 1723447) B1723447
theorem B2044007 : Blo 906576 2044007 := bstep (se 1 (by rfl) ⟨1533005, by rfl⟩ : syracuseStep 2044007 = 3066011) B3066011
theorem B3059855 : Blo 906576 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B1724647 : Blo 906576 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B27939059 : Blo 906576 27939059 := bstep (se 1 (by rfl) ⟨20954294, by rfl⟩ : syracuseStep 27939059 = 41908589) B41908589
theorem B7352603 : Blo 906576 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B2044187 : Blo 906576 2044187 := bstep (se 1 (by rfl) ⟨1533140, by rfl⟩ : syracuseStep 2044187 = 3066281) B3066281
theorem B4592375 : Blo 906576 4592375 := bstep (se 1 (by rfl) ⟨3444281, by rfl⟩ : syracuseStep 4592375 = 6888563) B6888563
theorem B5174077 : Blo 906576 5174077 := bstep (se 3 (by rfl) ⟨970139, by rfl⟩ : syracuseStep 5174077 = 1940279) B1940279
theorem B2585695 : Blo 906576 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B906783 : Blo 906576 906783 := bstep (se 1 (by rfl) ⟨680087, by rfl⟩ : syracuseStep 906783 = 1360175) B1360175
theorem B906943 : Blo 906576 906943 := bstep (se 1 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 906943 = 1360415) B1360415
theorem B907391 : Blo 906576 907391 := bstep (se 1 (by rfl) ⟨680543, by rfl⟩ : syracuseStep 907391 = 1361087) B1361087
theorem B5896367 : Blo 906576 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B907487 : Blo 906576 907487 := bstep (se 1 (by rfl) ⟨680615, by rfl⟩ : syracuseStep 907487 = 1361231) B1361231
theorem B907547 : Blo 906576 907547 := bstep (se 1 (by rfl) ⟨680660, by rfl⟩ : syracuseStep 907547 = 1361321) B1361321
theorem B28350749 : Blo 906576 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B3447137 : Blo 906576 3447137 := bstep (se 2 (by rfl) ⟨1292676, by rfl⟩ : syracuseStep 3447137 = 2585353) B2585353
theorem B907647 : Blo 906576 907647 := bstep (se 1 (by rfl) ⟨680735, by rfl⟩ : syracuseStep 907647 = 1361471) B1361471
theorem B5814665 : Blo 906576 5814665 := bstep (se 2 (by rfl) ⟨2180499, by rfl⟩ : syracuseStep 5814665 = 4360999) B4360999
theorem B907675 : Blo 906576 907675 := bstep (se 1 (by rfl) ⟨680756, by rfl⟩ : syracuseStep 907675 = 1361513) B1361513
theorem B907967 : Blo 906576 907967 := bstep (se 1 (by rfl) ⟨680975, by rfl⟩ : syracuseStep 907967 = 1361951) B1361951
theorem B1940203 : Blo 906576 1940203 := bstep (se 1 (by rfl) ⟨1455152, by rfl⟩ : syracuseStep 1940203 = 2910305) B2910305
theorem B13966091 : Blo 906576 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B5815097 : Blo 906576 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B908095 : Blo 906576 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B908135 : Blo 906576 908135 := bstep (se 1 (by rfl) ⟨681101, by rfl⟩ : syracuseStep 908135 = 1362203) B1362203
theorem B15514577 : Blo 906576 15514577 := bstep (se 2 (by rfl) ⟨5817966, by rfl⟩ : syracuseStep 15514577 = 11635933) B11635933
theorem B908351 : Blo 906576 908351 := bstep (se 1 (by rfl) ⟨681263, by rfl⟩ : syracuseStep 908351 = 1362527) B1362527
theorem B8731871 : Blo 906576 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B908539 : Blo 906576 908539 := bstep (se 1 (by rfl) ⟨681404, by rfl⟩ : syracuseStep 908539 = 1362809) B1362809
theorem B1531163 : Blo 906576 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B908571 : Blo 906576 908571 := bstep (se 1 (by rfl) ⟨681428, by rfl⟩ : syracuseStep 908571 = 1362857) B1362857
theorem B7757531 : Blo 906576 7757531 := bstep (se 1 (by rfl) ⟨5818148, by rfl⟩ : syracuseStep 7757531 = 11636297) B11636297
theorem B1531615 : Blo 906576 1531615 := bstep (se 1 (by rfl) ⟨1148711, by rfl⟩ : syracuseStep 1531615 = 2297423) B2297423
theorem B4595453 : Blo 906576 4595453 := bstep (se 3 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 4595453 = 1723295) B1723295
theorem B3448595 : Blo 906576 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B7749431 : Blo 906576 7749431 := bstep (se 1 (by rfl) ⟨5812073, by rfl⟩ : syracuseStep 7749431 = 11624147) B11624147
theorem B2178913 : Blo 906576 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B9805711 : Blo 906576 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B2039903 : Blo 906576 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B3063905 : Blo 906576 3063905 := bstep (se 2 (by rfl) ⟨1148964, by rfl⟩ : syracuseStep 3063905 = 2297929) B2297929
theorem B1360127 : Blo 906576 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B2180047 : Blo 906576 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B7758929 : Blo 906576 7758929 := bstep (se 2 (by rfl) ⟨2909598, by rfl⟩ : syracuseStep 7758929 = 5819197) B5819197
theorem B6898769 : Blo 906576 6898769 := bstep (se 2 (by rfl) ⟨2587038, by rfl⟩ : syracuseStep 6898769 = 5174077) B5174077
theorem B13075663 : Blo 906576 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B14714273 : Blo 906576 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B18900499 : Blo 906576 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B3442247 : Blo 906576 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B3876443 : Blo 906576 3876443 := bstep (se 1 (by rfl) ⟨2907332, by rfl⟩ : syracuseStep 3876443 = 5814665) B5814665
theorem B11634293 : Blo 906576 11634293 := bstep (se 5 (by rfl) ⟨545357, by rfl⟩ : syracuseStep 11634293 = 1090715) B1090715
theorem B2451073 : Blo 906576 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B3065579 : Blo 906576 3065579 := bstep (se 1 (by rfl) ⟨2299184, by rfl⟩ : syracuseStep 3065579 = 4598369) B4598369
theorem B44730143 : Blo 906576 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B3876731 : Blo 906576 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B14158091 : Blo 906576 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B2042153 : Blo 906576 2042153 := bstep (se 2 (by rfl) ⟨765807, by rfl⟩ : syracuseStep 2042153 = 1531615) B1531615
theorem B2296147 : Blo 906576 2296147 := bstep (se 1 (by rfl) ⟨1722110, by rfl⟩ : syracuseStep 2296147 = 3444221) B3444221
theorem B5171687 : Blo 906576 5171687 := bstep (se 1 (by rfl) ⟨3878765, by rfl⟩ : syracuseStep 5171687 = 7757531) B7757531
theorem B20974243 : Blo 906576 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B1362671 : Blo 906576 1362671 := bstep (se 1 (by rfl) ⟨1022003, by rfl⟩ : syracuseStep 1362671 = 2044007) B2044007
theorem B4901735 : Blo 906576 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B1362791 : Blo 906576 1362791 := bstep (se 1 (by rfl) ⟨1022093, by rfl⟩ : syracuseStep 1362791 = 2044187) B2044187
theorem B6204413 : Blo 906576 6204413 := bstep (se 3 (by rfl) ⟨1163327, by rfl⟩ : syracuseStep 6204413 = 2326655) B2326655
theorem B6892937 : Blo 906576 6892937 := bstep (se 2 (by rfl) ⟨2584851, by rfl⟩ : syracuseStep 6892937 = 5169703) B5169703
theorem B3878441 : Blo 906576 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B6893423 : Blo 906576 6893423 := bstep (se 1 (by rfl) ⟨5170067, by rfl⟩ : syracuseStep 6893423 = 10340135) B10340135
theorem B2043881 : Blo 906576 2043881 := bstep (se 2 (by rfl) ⟨766455, by rfl⟩ : syracuseStep 2043881 = 1532911) B1532911
theorem B2043935 : Blo 906576 2043935 := bstep (se 1 (by rfl) ⟨1532951, by rfl⟩ : syracuseStep 2043935 = 3065903) B3065903
theorem B14725313 : Blo 906576 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B6205673 : Blo 906576 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B2298091 : Blo 906576 2298091 := bstep (se 1 (by rfl) ⟨1723568, by rfl⟩ : syracuseStep 2298091 = 3447137) B3447137
theorem B13070591 : Blo 906576 13070591 := bstep (se 1 (by rfl) ⟨9802943, by rfl⟩ : syracuseStep 13070591 = 19605887) B19605887
theorem B3060071 : Blo 906576 3060071 := bstep (se 1 (by rfl) ⟨2295053, by rfl⟩ : syracuseStep 3060071 = 4590107) B4590107
theorem B9310727 : Blo 906576 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B2986537 : Blo 906576 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B10343051 : Blo 906576 10343051 := bstep (se 1 (by rfl) ⟨7757288, by rfl⟩ : syracuseStep 10343051 = 15514577) B15514577
theorem B5821247 : Blo 906576 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B1020775 : Blo 906576 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B14914529 : Blo 906576 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B3060719 : Blo 906576 3060719 := bstep (se 1 (by rfl) ⟨2295539, by rfl⟩ : syracuseStep 3060719 = 4591079) B4591079
theorem B2905217 : Blo 906576 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B2299063 : Blo 906576 2299063 := bstep (se 1 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 2299063 = 3448595) B3448595
theorem B5166287 : Blo 906576 5166287 := bstep (se 1 (by rfl) ⟨3874715, by rfl⟩ : syracuseStep 5166287 = 7749431) B7749431
theorem B906719 : Blo 906576 906719 := bstep (se 1 (by rfl) ⟨680039, by rfl⟩ : syracuseStep 906719 = 1360079) B1360079
theorem B18626039 : Blo 906576 18626039 := bstep (se 1 (by rfl) ⟨13969529, by rfl⟩ : syracuseStep 18626039 = 27939059) B27939059
theorem B3315215 : Blo 906576 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2299529 : Blo 906576 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B3061583 : Blo 906576 3061583 := bstep (se 1 (by rfl) ⟨2296187, by rfl⟩ : syracuseStep 3061583 = 4592375) B4592375
theorem B907175 : Blo 906576 907175 := bstep (se 1 (by rfl) ⟨680381, by rfl⟩ : syracuseStep 907175 = 1360763) B1360763
theorem B1939391 : Blo 906576 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B907259 : Blo 906576 907259 := bstep (se 1 (by rfl) ⟨680444, by rfl⟩ : syracuseStep 907259 = 1360889) B1360889
theorem B907295 : Blo 906576 907295 := bstep (se 1 (by rfl) ⟨680471, by rfl⟩ : syracuseStep 907295 = 1360943) B1360943
theorem B907375 : Blo 906576 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B907503 : Blo 906576 907503 := bstep (se 1 (by rfl) ⟨680627, by rfl⟩ : syracuseStep 907503 = 1361255) B1361255
theorem B2586937 : Blo 906576 2586937 := bstep (se 2 (by rfl) ⟨970101, by rfl⟩ : syracuseStep 2586937 = 1940203) B1940203
theorem B9812285 : Blo 906576 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B6986063 : Blo 906576 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B4659551 : Blo 906576 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B907931 : Blo 906576 907931 := bstep (se 1 (by rfl) ⟨680948, by rfl⟩ : syracuseStep 907931 = 1361897) B1361897
theorem B2906857 : Blo 906576 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B908027 : Blo 906576 908027 := bstep (se 1 (by rfl) ⟨681020, by rfl⟩ : syracuseStep 908027 = 1362041) B1362041
theorem B11623175 : Blo 906576 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B3930911 : Blo 906576 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B3447593 : Blo 906576 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B908159 : Blo 906576 908159 := bstep (se 1 (by rfl) ⟨681119, by rfl⟩ : syracuseStep 908159 = 1362239) B1362239
theorem B908255 : Blo 906576 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B908283 : Blo 906576 908283 := bstep (se 1 (by rfl) ⟨681212, by rfl⟩ : syracuseStep 908283 = 1362425) B1362425
theorem B908315 : Blo 906576 908315 := bstep (se 1 (by rfl) ⟨681236, by rfl⟩ : syracuseStep 908315 = 1362473) B1362473
theorem B1531291 : Blo 906576 1531291 := bstep (se 1 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 1531291 = 2296937) B2296937
theorem B3063635 : Blo 906576 3063635 := bstep (se 1 (by rfl) ⟨2297726, by rfl⟩ : syracuseStep 3063635 = 4595453) B4595453
theorem B13074281 : Blo 906576 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B3063689 : Blo 906576 3063689 := bstep (se 2 (by rfl) ⟨1148883, by rfl⟩ : syracuseStep 3063689 = 2297767) B2297767
theorem B1359935 : Blo 906576 1359935 := bstep (se 1 (by rfl) ⟨1019951, by rfl⟩ : syracuseStep 1359935 = 2039903) B2039903
theorem B2040047 : Blo 906576 2040047 := bstep (se 1 (by rfl) ⟨1530035, by rfl⟩ : syracuseStep 2040047 = 3060071) B3060071
theorem B3064121 : Blo 906576 3064121 := bstep (se 2 (by rfl) ⟨1149045, by rfl⟩ : syracuseStep 3064121 = 2298091) B2298091
theorem B3449249 : Blo 906576 3449249 := bstep (se 2 (by rfl) ⟨1293468, by rfl⟩ : syracuseStep 3449249 = 2586937) B2586937
theorem B16548461 : Blo 906576 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B2040479 : Blo 906576 2040479 := bstep (se 1 (by rfl) ⟨1530359, by rfl⟩ : syracuseStep 2040479 = 3060719) B3060719
theorem B3982049 : Blo 906576 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B3875809 : Blo 906576 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B2294831 : Blo 906576 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B1533019 : Blo 906576 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B1361033 : Blo 906576 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B29820095 : Blo 906576 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B2041055 : Blo 906576 2041055 := bstep (se 1 (by rfl) ⟨1530791, by rfl⟩ : syracuseStep 2041055 = 3061583) B3061583
theorem B8840573 : Blo 906576 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B9438727 : Blo 906576 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B1361435 : Blo 906576 1361435 := bstep (se 1 (by rfl) ⟨1021076, by rfl⟩ : syracuseStep 1361435 = 2042153) B2042153
theorem B3106367 : Blo 906576 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B3065417 : Blo 906576 3065417 := bstep (se 2 (by rfl) ⟨1149531, by rfl⟩ : syracuseStep 3065417 = 2299063) B2299063
theorem B17434217 : Blo 906576 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B2041721 : Blo 906576 2041721 := bstep (se 2 (by rfl) ⟨765645, by rfl⟩ : syracuseStep 2041721 = 1531291) B1531291
theorem B25200665 : Blo 906576 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B2042423 : Blo 906576 2042423 := bstep (se 1 (by rfl) ⟨1531817, by rfl⟩ : syracuseStep 2042423 = 3063635) B3063635
theorem B2042459 : Blo 906576 2042459 := bstep (se 1 (by rfl) ⟨1531844, by rfl⟩ : syracuseStep 2042459 = 3063689) B3063689
theorem B1362587 : Blo 906576 1362587 := bstep (se 1 (by rfl) ⟨1021940, by rfl⟩ : syracuseStep 1362587 = 2043881) B2043881
theorem B1362623 : Blo 906576 1362623 := bstep (se 1 (by rfl) ⟨1021967, by rfl⟩ : syracuseStep 1362623 = 2043935) B2043935
theorem B2042603 : Blo 906576 2042603 := bstep (se 1 (by rfl) ⟨1531952, by rfl⟩ : syracuseStep 2042603 = 3063905) B3063905
theorem B9816875 : Blo 906576 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B5172619 : Blo 906576 5172619 := bstep (se 1 (by rfl) ⟨3879464, by rfl⟩ : syracuseStep 5172619 = 7758929) B7758929
theorem B4599179 : Blo 906576 4599179 := bstep (se 1 (by rfl) ⟨3449384, by rfl⟩ : syracuseStep 4599179 = 6898769) B6898769
theorem B1936811 : Blo 906576 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B3444191 : Blo 906576 3444191 := bstep (se 1 (by rfl) ⟨2583143, by rfl⟩ : syracuseStep 3444191 = 5166287) B5166287
theorem B9809515 : Blo 906576 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B2584295 : Blo 906576 2584295 := bstep (se 1 (by rfl) ⟨1938221, by rfl⟩ : syracuseStep 2584295 = 3876443) B3876443
theorem B2043719 : Blo 906576 2043719 := bstep (se 1 (by rfl) ⟨1532789, by rfl⟩ : syracuseStep 2043719 = 3065579) B3065579
theorem B2584487 : Blo 906576 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B6541523 : Blo 906576 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B4657375 : Blo 906576 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B2298395 : Blo 906576 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B2585627 : Blo 906576 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B906751 : Blo 906576 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B8713727 : Blo 906576 8713727 := bstep (se 1 (by rfl) ⟨6535295, by rfl⟩ : syracuseStep 8713727 = 13070591) B13070591
theorem B6207151 : Blo 906576 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B6895367 : Blo 906576 6895367 := bstep (se 1 (by rfl) ⟨5171525, by rfl⟩ : syracuseStep 6895367 = 10343051) B10343051
theorem B3061529 : Blo 906576 3061529 := bstep (se 2 (by rfl) ⟨1148073, by rfl⟩ : syracuseStep 3061529 = 2296147) B2296147
theorem B9943019 : Blo 906576 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B27965657 : Blo 906576 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B12417359 : Blo 906576 12417359 := bstep (se 1 (by rfl) ⟨9313019, by rfl⟩ : syracuseStep 12417359 = 18626039) B18626039
theorem B7756195 : Blo 906576 7756195 := bstep (se 1 (by rfl) ⟨5817146, by rfl⟩ : syracuseStep 7756195 = 11634293) B11634293
theorem B2906729 : Blo 906576 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B1292927 : Blo 906576 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B3447791 : Blo 906576 3447791 := bstep (se 1 (by rfl) ⟨2585843, by rfl⟩ : syracuseStep 3447791 = 5171687) B5171687
theorem B908447 : Blo 906576 908447 := bstep (se 1 (by rfl) ⟨681335, by rfl⟩ : syracuseStep 908447 = 1362671) B1362671
theorem B7748783 : Blo 906576 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B2620607 : Blo 906576 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B3267823 : Blo 906576 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B908527 : Blo 906576 908527 := bstep (se 1 (by rfl) ⟨681395, by rfl⟩ : syracuseStep 908527 = 1362791) B1362791
theorem B4136275 : Blo 906576 4136275 := bstep (se 1 (by rfl) ⟨3102206, by rfl⟩ : syracuseStep 4136275 = 6204413) B6204413
theorem B15523325 : Blo 906576 15523325 := bstep (se 3 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 15523325 = 5821247) B5821247
theorem B3268097 : Blo 906576 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B4595291 : Blo 906576 4595291 := bstep (se 1 (by rfl) ⟨3446468, by rfl⟩ : syracuseStep 4595291 = 6892937) B6892937
theorem B8716187 : Blo 906576 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B4595615 : Blo 906576 4595615 := bstep (se 1 (by rfl) ⟨3446711, by rfl⟩ : syracuseStep 4595615 = 6893423) B6893423
theorem B1360031 : Blo 906576 1360031 := bstep (se 1 (by rfl) ⟨1020023, by rfl⟩ : syracuseStep 1360031 = 2040047) B2040047
theorem B6209833 : Blo 906576 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B1532263 : Blo 906576 1532263 := bstep (se 1 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 1532263 = 2298395) B2298395
theorem B1360319 : Blo 906576 1360319 := bstep (se 1 (by rfl) ⟨1020239, by rfl⟩ : syracuseStep 1360319 = 2040479) B2040479
theorem B2654699 : Blo 906576 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B6988285 : Blo 906576 6988285 := bstep (se 3 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 6988285 = 2620607) B2620607
theorem B1360703 : Blo 906576 1360703 := bstep (se 1 (by rfl) ⟨1020527, by rfl⟩ : syracuseStep 1360703 = 2041055) B2041055
theorem B33112957 : Blo 906576 33112957 := bstep (se 3 (by rfl) ⟨6208679, by rfl⟩ : syracuseStep 33112957 = 12417359) B12417359
theorem B5809151 : Blo 906576 5809151 := bstep (se 1 (by rfl) ⟨4356863, by rfl⟩ : syracuseStep 5809151 = 8713727) B8713727
theorem B4596911 : Blo 906576 4596911 := bstep (se 1 (by rfl) ⟨3447683, by rfl⟩ : syracuseStep 4596911 = 6895367) B6895367
theorem B2041019 : Blo 906576 2041019 := bstep (se 1 (by rfl) ⟨1530764, by rfl⟩ : syracuseStep 2041019 = 3061529) B3061529
theorem B1361147 : Blo 906576 1361147 := bstep (se 1 (by rfl) ⟨1020860, by rfl⟩ : syracuseStep 1361147 = 2041721) B2041721
theorem B6628679 : Blo 906576 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B1361615 : Blo 906576 1361615 := bstep (se 1 (by rfl) ⟨1021211, by rfl⟩ : syracuseStep 1361615 = 2042423) B2042423
theorem B1361639 : Blo 906576 1361639 := bstep (se 1 (by rfl) ⟨1021229, by rfl⟩ : syracuseStep 1361639 = 2042459) B2042459
theorem B1361735 : Blo 906576 1361735 := bstep (se 1 (by rfl) ⟨1021301, by rfl⟩ : syracuseStep 1361735 = 2042603) B2042603
theorem B12584969 : Blo 906576 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B8276201 : Blo 906576 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B3066119 : Blo 906576 3066119 := bstep (se 1 (by rfl) ⟨2299589, by rfl⟩ : syracuseStep 3066119 = 4599179) B4599179
theorem B2296127 : Blo 906576 2296127 := bstep (se 1 (by rfl) ⟨1722095, by rfl⟩ : syracuseStep 2296127 = 3444191) B3444191
theorem B10348883 : Blo 906576 10348883 := bstep (se 1 (by rfl) ⟨7761662, by rfl⟩ : syracuseStep 10348883 = 15523325) B15523325
theorem B6891965 : Blo 906576 6891965 := bstep (se 3 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 6891965 = 2584487) B2584487
theorem B1722863 : Blo 906576 1722863 := bstep (se 1 (by rfl) ⟨1292147, by rfl⟩ : syracuseStep 1722863 = 2584295) B2584295
theorem B1362479 : Blo 906576 1362479 := bstep (se 1 (by rfl) ⟨1021859, by rfl⟩ : syracuseStep 1362479 = 2043719) B2043719
theorem B5810791 : Blo 906576 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B4361015 : Blo 906576 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B2042747 : Blo 906576 2042747 := bstep (se 1 (by rfl) ⟨1532060, by rfl⟩ : syracuseStep 2042747 = 3064121) B3064121
theorem B10341593 : Blo 906576 10341593 := bstep (se 2 (by rfl) ⟨3878097, by rfl⟩ : syracuseStep 10341593 = 7756195) B7756195
theorem B52317413 : Blo 906576 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1723751 : Blo 906576 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B5893715 : Blo 906576 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B2043611 : Blo 906576 2043611 := bstep (se 1 (by rfl) ⟨1532708, by rfl⟩ : syracuseStep 2043611 = 3065417) B3065417
theorem B5164829 : Blo 906576 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B2044025 : Blo 906576 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B1937819 : Blo 906576 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B2298527 : Blo 906576 2298527 := bstep (se 1 (by rfl) ⟨1723895, by rfl⟩ : syracuseStep 2298527 = 3447791) B3447791
theorem B5165855 : Blo 906576 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B906623 : Blo 906576 906623 := bstep (se 1 (by rfl) ⟨679967, by rfl⟩ : syracuseStep 906623 = 1359935) B1359935
theorem B2299499 : Blo 906576 2299499 := bstep (se 1 (by rfl) ⟨1724624, by rfl⟩ : syracuseStep 2299499 = 3449249) B3449249
theorem B11032307 : Blo 906576 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B1529887 : Blo 906576 1529887 := bstep (se 1 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 1529887 = 2294831) B2294831
theorem B907355 : Blo 906576 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B19880063 : Blo 906576 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B907623 : Blo 906576 907623 := bstep (se 1 (by rfl) ⟨680717, by rfl⟩ : syracuseStep 907623 = 1361435) B1361435
theorem B2070911 : Blo 906576 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B11622811 : Blo 906576 11622811 := bstep (se 1 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 11622811 = 17434217) B17434217
theorem B5167745 : Blo 906576 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B16800443 : Blo 906576 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B18643771 : Blo 906576 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B4357097 : Blo 906576 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B3447805 : Blo 906576 3447805 := bstep (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) B1292927
theorem B22060133 : Blo 906576 22060133 := bstep (se 4 (by rfl) ⟨2068137, by rfl⟩ : syracuseStep 22060133 = 4136275) B4136275
theorem B908391 : Blo 906576 908391 := bstep (se 1 (by rfl) ⟨681293, by rfl⟩ : syracuseStep 908391 = 1362587) B1362587
theorem B908415 : Blo 906576 908415 := bstep (se 1 (by rfl) ⟨681311, by rfl⟩ : syracuseStep 908415 = 1362623) B1362623
theorem B6896825 : Blo 906576 6896825 := bstep (se 2 (by rfl) ⟨2586309, by rfl⟩ : syracuseStep 6896825 = 5172619) B5172619
theorem B6544583 : Blo 906576 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B2178731 : Blo 906576 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B3063527 : Blo 906576 3063527 := bstep (se 1 (by rfl) ⟨2297645, by rfl⟩ : syracuseStep 3063527 = 4595291) B4595291
theorem B3063743 : Blo 906576 3063743 := bstep (se 1 (by rfl) ⟨2297807, by rfl⟩ : syracuseStep 3063743 = 4595615) B4595615
theorem B2039849 : Blo 906576 2039849 := bstep (se 2 (by rfl) ⟨764943, by rfl⟩ : syracuseStep 2039849 = 1529887) B1529887
theorem B1532351 : Blo 906576 1532351 := bstep (se 1 (by rfl) ⟨1149263, by rfl⟩ : syracuseStep 1532351 = 2298527) B2298527
theorem B3064607 : Blo 906576 3064607 := bstep (se 1 (by rfl) ⟨2298455, by rfl⟩ : syracuseStep 3064607 = 4596911) B4596911
theorem B1360679 : Blo 906576 1360679 := bstep (se 1 (by rfl) ⟨1020509, by rfl⟩ : syracuseStep 1360679 = 2041019) B2041019
theorem B1532999 : Blo 906576 1532999 := bstep (se 1 (by rfl) ⟨1149749, by rfl⟩ : syracuseStep 1532999 = 2299499) B2299499
theorem B4597073 : Blo 906576 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B8389979 : Blo 906576 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B6899255 : Blo 906576 6899255 := bstep (se 1 (by rfl) ⟨5174441, by rfl⟩ : syracuseStep 6899255 = 10348883) B10348883
theorem B1148575 : Blo 906576 1148575 := bstep (se 1 (by rfl) ⟨861431, by rfl⟩ : syracuseStep 1148575 = 1722863) B1722863
theorem B11200295 : Blo 906576 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B1361831 : Blo 906576 1361831 := bstep (se 1 (by rfl) ⟨1021373, by rfl⟩ : syracuseStep 1361831 = 2042747) B2042747
theorem B14706755 : Blo 906576 14706755 := bstep (se 1 (by rfl) ⟨11030066, by rfl⟩ : syracuseStep 14706755 = 22060133) B22060133
theorem B4597883 : Blo 906576 4597883 := bstep (se 1 (by rfl) ⟨3448412, by rfl⟩ : syracuseStep 4597883 = 6896825) B6896825
theorem B1149167 : Blo 906576 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B1452487 : Blo 906576 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B1362407 : Blo 906576 1362407 := bstep (se 1 (by rfl) ⟨1021805, by rfl⟩ : syracuseStep 1362407 = 2043611) B2043611
theorem B2042351 : Blo 906576 2042351 := bstep (se 1 (by rfl) ⟨1531763, by rfl⟩ : syracuseStep 2042351 = 3063527) B3063527
theorem B3443219 : Blo 906576 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B2042495 : Blo 906576 2042495 := bstep (se 1 (by rfl) ⟨1531871, by rfl⟩ : syracuseStep 2042495 = 3063743) B3063743
theorem B1362683 : Blo 906576 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B2043017 : Blo 906576 2043017 := bstep (se 2 (by rfl) ⟨766131, by rfl⟩ : syracuseStep 2043017 = 1532263) B1532263
theorem B3443903 : Blo 906576 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B9317713 : Blo 906576 9317713 := bstep (se 2 (by rfl) ⟨3494142, by rfl⟩ : syracuseStep 9317713 = 6988285) B6988285
theorem B4419119 : Blo 906576 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B24858361 : Blo 906576 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B44150609 : Blo 906576 44150609 := bstep (se 2 (by rfl) ⟨16556478, by rfl⟩ : syracuseStep 44150609 = 33112957) B33112957
theorem B5517467 : Blo 906576 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B2044079 : Blo 906576 2044079 := bstep (se 1 (by rfl) ⟨1533059, by rfl⟩ : syracuseStep 2044079 = 3066119) B3066119
theorem B1380607 : Blo 906576 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B3445163 : Blo 906576 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B2904731 : Blo 906576 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B4363055 : Blo 906576 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B6894395 : Blo 906576 6894395 := bstep (se 1 (by rfl) ⟨5170796, by rfl⟩ : syracuseStep 6894395 = 10341593) B10341593
theorem B34878275 : Blo 906576 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B3929143 : Blo 906576 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B28316789 : Blo 906576 28316789 := bstep (se 5 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 28316789 = 2654699) B2654699
theorem B906687 : Blo 906576 906687 := bstep (se 1 (by rfl) ⟨680015, by rfl⟩ : syracuseStep 906687 = 1360031) B1360031
theorem B1291879 : Blo 906576 1291879 := bstep (se 1 (by rfl) ⟨968909, by rfl⟩ : syracuseStep 1291879 = 1937819) B1937819
theorem B906879 : Blo 906576 906879 := bstep (se 1 (by rfl) ⟨680159, by rfl⟩ : syracuseStep 906879 = 1360319) B1360319
theorem B8279777 : Blo 906576 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B15497081 : Blo 906576 15497081 := bstep (se 2 (by rfl) ⟨5811405, by rfl⟩ : syracuseStep 15497081 = 11622811) B11622811
theorem B907135 : Blo 906576 907135 := bstep (se 1 (by rfl) ⟨680351, by rfl⟩ : syracuseStep 907135 = 1360703) B1360703
theorem B3872767 : Blo 906576 3872767 := bstep (se 1 (by rfl) ⟨2904575, by rfl⟩ : syracuseStep 3872767 = 5809151) B5809151
theorem B7747721 : Blo 906576 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B907431 : Blo 906576 907431 := bstep (se 1 (by rfl) ⟨680573, by rfl⟩ : syracuseStep 907431 = 1361147) B1361147
theorem B907743 : Blo 906576 907743 := bstep (se 1 (by rfl) ⟨680807, by rfl⟩ : syracuseStep 907743 = 1361615) B1361615
theorem B907759 : Blo 906576 907759 := bstep (se 1 (by rfl) ⟨680819, by rfl⟩ : syracuseStep 907759 = 1361639) B1361639
theorem B7354871 : Blo 906576 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B907823 : Blo 906576 907823 := bstep (se 1 (by rfl) ⟨680867, by rfl⟩ : syracuseStep 907823 = 1361735) B1361735
theorem B13253375 : Blo 906576 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B1530751 : Blo 906576 1530751 := bstep (se 1 (by rfl) ⟨1148063, by rfl⟩ : syracuseStep 1530751 = 2296127) B2296127
theorem B4594643 : Blo 906576 4594643 := bstep (se 1 (by rfl) ⟨3445982, by rfl⟩ : syracuseStep 4594643 = 6891965) B6891965
theorem B908319 : Blo 906576 908319 := bstep (se 1 (by rfl) ⟨681239, by rfl⟩ : syracuseStep 908319 = 1362479) B1362479
theorem B2907343 : Blo 906576 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B1359899 : Blo 906576 1359899 := bstep (se 1 (by rfl) ⟨1019924, by rfl⟩ : syracuseStep 1359899 = 2039849) B2039849
theorem B3678311 : Blo 906576 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B2908703 : Blo 906576 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B6890021 : Blo 906576 6890021 := bstep (se 4 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 6890021 = 1291879) B1291879
theorem B4596263 : Blo 906576 4596263 := bstep (se 1 (by rfl) ⟨3447197, by rfl⟩ : syracuseStep 4596263 = 6894395) B6894395
theorem B3064445 : Blo 906576 3064445 := bstep (se 3 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 3064445 = 1149167) B1149167
theorem B3064715 : Blo 906576 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B2041001 : Blo 906576 2041001 := bstep (se 2 (by rfl) ⟨765375, by rfl⟩ : syracuseStep 2041001 = 1530751) B1530751
theorem B10331387 : Blo 906576 10331387 := bstep (se 1 (by rfl) ⟨7748540, by rfl⟩ : syracuseStep 10331387 = 15497081) B15497081
theorem B3065255 : Blo 906576 3065255 := bstep (se 1 (by rfl) ⟨2298941, by rfl⟩ : syracuseStep 3065255 = 4597883) B4597883
theorem B1361567 : Blo 906576 1361567 := bstep (se 1 (by rfl) ⟨1021175, by rfl⟩ : syracuseStep 1361567 = 2042351) B2042351
theorem B2295479 : Blo 906576 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B1361663 : Blo 906576 1361663 := bstep (se 1 (by rfl) ⟨1021247, by rfl⟩ : syracuseStep 1361663 = 2042495) B2042495
theorem B22079405 : Blo 906576 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B1362011 : Blo 906576 1362011 := bstep (se 1 (by rfl) ⟨1021508, by rfl⟩ : syracuseStep 1362011 = 2043017) B2043017
theorem B2295935 : Blo 906576 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B5163689 : Blo 906576 5163689 := bstep (se 2 (by rfl) ⟨1936383, by rfl⟩ : syracuseStep 5163689 = 3872767) B3872767
theorem B1362719 : Blo 906576 1362719 := bstep (se 1 (by rfl) ⟨1022039, by rfl⟩ : syracuseStep 1362719 = 2044079) B2044079
theorem B2296775 : Blo 906576 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B1936487 : Blo 906576 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B2043071 : Blo 906576 2043071 := bstep (se 1 (by rfl) ⟨1532303, by rfl⟩ : syracuseStep 2043071 = 3064607) B3064607
theorem B23252183 : Blo 906576 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B1936649 : Blo 906576 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B18877859 : Blo 906576 18877859 := bstep (se 1 (by rfl) ⟨14158394, by rfl⟩ : syracuseStep 18877859 = 28316789) B28316789
theorem B4599503 : Blo 906576 4599503 := bstep (se 1 (by rfl) ⟨3449627, by rfl⟩ : syracuseStep 4599503 = 6899255) B6899255
theorem B7466863 : Blo 906576 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B5238857 : Blo 906576 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B5165147 : Blo 906576 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B4903247 : Blo 906576 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B12423617 : Blo 906576 12423617 := bstep (se 2 (by rfl) ⟨4658856, by rfl⟩ : syracuseStep 12423617 = 9317713) B9317713
theorem B8835583 : Blo 906576 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B2946079 : Blo 906576 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B1021567 : Blo 906576 1021567 := bstep (se 1 (by rfl) ⟨766175, by rfl⟩ : syracuseStep 1021567 = 1532351) B1532351
theorem B907119 : Blo 906576 907119 := bstep (se 1 (by rfl) ⟨680339, by rfl⟩ : syracuseStep 907119 = 1360679) B1360679
theorem B1021999 : Blo 906576 1021999 := bstep (se 1 (by rfl) ⟨766499, by rfl⟩ : syracuseStep 1021999 = 1532999) B1532999
theorem B5593319 : Blo 906576 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B15505829 : Blo 906576 15505829 := bstep (se 4 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 15505829 = 2907343) B2907343
theorem B907887 : Blo 906576 907887 := bstep (se 1 (by rfl) ⟨680915, by rfl⟩ : syracuseStep 907887 = 1361831) B1361831
theorem B7363237 : Blo 906576 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B9804503 : Blo 906576 9804503 := bstep (se 1 (by rfl) ⟨7353377, by rfl⟩ : syracuseStep 9804503 = 14706755) B14706755
theorem B908271 : Blo 906576 908271 := bstep (se 1 (by rfl) ⟨681203, by rfl⟩ : syracuseStep 908271 = 1362407) B1362407
theorem B908455 : Blo 906576 908455 := bstep (se 1 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 908455 = 1362683) B1362683
theorem B3063095 : Blo 906576 3063095 := bstep (se 1 (by rfl) ⟨2297321, by rfl⟩ : syracuseStep 3063095 = 4594643) B4594643
theorem B1531433 : Blo 906576 1531433 := bstep (se 2 (by rfl) ⟨574287, by rfl⟩ : syracuseStep 1531433 = 1148575) B1148575
theorem B33144481 : Blo 906576 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B29433739 : Blo 906576 29433739 := bstep (se 1 (by rfl) ⟨22075304, by rfl⟩ : syracuseStep 29433739 = 44150609) B44150609
theorem B3268831 : Blo 906576 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B8282411 : Blo 906576 8282411 := bstep (se 1 (by rfl) ⟨6211808, by rfl⟩ : syracuseStep 8282411 = 12423617) B12423617
theorem B3064175 : Blo 906576 3064175 := bstep (se 1 (by rfl) ⟨2298131, by rfl⟩ : syracuseStep 3064175 = 4596263) B4596263
theorem B11780777 : Blo 906576 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B1360667 : Blo 906576 1360667 := bstep (se 1 (by rfl) ⟨1020500, by rfl⟩ : syracuseStep 1360667 = 2041001) B2041001
theorem B3728879 : Blo 906576 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B3442459 : Blo 906576 3442459 := bstep (se 1 (by rfl) ⟨2581844, by rfl⟩ : syracuseStep 3442459 = 5163689) B5163689
theorem B1362047 : Blo 906576 1362047 := bstep (se 1 (by rfl) ⟨1021535, by rfl⟩ : syracuseStep 1362047 = 2043071) B2043071
theorem B15501455 : Blo 906576 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B1362089 : Blo 906576 1362089 := bstep (se 2 (by rfl) ⟨510783, by rfl⟩ : syracuseStep 1362089 = 1021567) B1021567
theorem B2042063 : Blo 906576 2042063 := bstep (se 1 (by rfl) ⟨1531547, by rfl⟩ : syracuseStep 2042063 = 3063095) B3063095
theorem B12585239 : Blo 906576 12585239 := bstep (se 1 (by rfl) ⟨9438929, by rfl⟩ : syracuseStep 12585239 = 18877859) B18877859
theorem B3066335 : Blo 906576 3066335 := bstep (se 1 (by rfl) ⟨2299751, by rfl⟩ : syracuseStep 3066335 = 4599503) B4599503
theorem B9955817 : Blo 906576 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B3492571 : Blo 906576 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B3443431 : Blo 906576 3443431 := bstep (se 1 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 3443431 = 5165147) B5165147
theorem B1362665 : Blo 906576 1362665 := bstep (se 2 (by rfl) ⟨510999, by rfl⟩ : syracuseStep 1362665 = 1021999) B1021999
theorem B2452207 : Blo 906576 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B2042963 : Blo 906576 2042963 := bstep (se 1 (by rfl) ⟨1532222, by rfl⟩ : syracuseStep 2042963 = 3064445) B3064445
theorem B2043143 : Blo 906576 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B5164397 : Blo 906576 5164397 := bstep (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) B1936649
theorem B9817649 : Blo 906576 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B2043503 : Blo 906576 2043503 := bstep (se 1 (by rfl) ⟨1532627, by rfl⟩ : syracuseStep 2043503 = 3065255) B3065255
theorem B3928105 : Blo 906576 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B1290991 : Blo 906576 1290991 := bstep (se 1 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 1290991 = 1936487) B1936487
theorem B44192641 : Blo 906576 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B1020955 : Blo 906576 1020955 := bstep (se 1 (by rfl) ⟨765716, by rfl⟩ : syracuseStep 1020955 = 1531433) B1531433
theorem B39244985 : Blo 906576 39244985 := bstep (se 2 (by rfl) ⟨14716869, by rfl⟩ : syracuseStep 39244985 = 29433739) B29433739
theorem B906599 : Blo 906576 906599 := bstep (se 1 (by rfl) ⟨679949, by rfl⟩ : syracuseStep 906599 = 1359899) B1359899
theorem B4593347 : Blo 906576 4593347 := bstep (se 1 (by rfl) ⟨3445010, by rfl⟩ : syracuseStep 4593347 = 6890021) B6890021
theorem B1939135 : Blo 906576 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B6887591 : Blo 906576 6887591 := bstep (se 1 (by rfl) ⟨5165693, by rfl⟩ : syracuseStep 6887591 = 10331387) B10331387
theorem B907711 : Blo 906576 907711 := bstep (se 1 (by rfl) ⟨680783, by rfl⟩ : syracuseStep 907711 = 1361567) B1361567
theorem B1530319 : Blo 906576 1530319 := bstep (se 1 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 1530319 = 2295479) B2295479
theorem B907775 : Blo 906576 907775 := bstep (se 1 (by rfl) ⟨680831, by rfl⟩ : syracuseStep 907775 = 1361663) B1361663
theorem B14719603 : Blo 906576 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B908007 : Blo 906576 908007 := bstep (se 1 (by rfl) ⟨681005, by rfl⟩ : syracuseStep 908007 = 1362011) B1362011
theorem B1530623 : Blo 906576 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B10337219 : Blo 906576 10337219 := bstep (se 1 (by rfl) ⟨7752914, by rfl⟩ : syracuseStep 10337219 = 15505829) B15505829
theorem B6536335 : Blo 906576 6536335 := bstep (se 1 (by rfl) ⟨4902251, by rfl⟩ : syracuseStep 6536335 = 9804503) B9804503
theorem B908479 : Blo 906576 908479 := bstep (se 1 (by rfl) ⟨681359, by rfl⟩ : syracuseStep 908479 = 1362719) B1362719
theorem B1531183 : Blo 906576 1531183 := bstep (se 1 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 1531183 = 2296775) B2296775
theorem B5521607 : Blo 906576 5521607 := bstep (se 1 (by rfl) ⟨4141205, by rfl⟩ : syracuseStep 5521607 = 8282411) B8282411
theorem B4358441 : Blo 906576 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2040425 : Blo 906576 2040425 := bstep (se 2 (by rfl) ⟨765159, by rfl⟩ : syracuseStep 2040425 = 1530319) B1530319
theorem B1721321 : Blo 906576 1721321 := bstep (se 2 (by rfl) ⟨645495, by rfl⟩ : syracuseStep 1721321 = 1290991) B1290991
theorem B3269609 : Blo 906576 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B1361273 : Blo 906576 1361273 := bstep (se 2 (by rfl) ⟨510477, by rfl⟩ : syracuseStep 1361273 = 1020955) B1020955
theorem B1361375 : Blo 906576 1361375 := bstep (se 1 (by rfl) ⟨1021031, by rfl⟩ : syracuseStep 1361375 = 2042063) B2042063
theorem B8390159 : Blo 906576 8390159 := bstep (se 1 (by rfl) ⟨6292619, by rfl⟩ : syracuseStep 8390159 = 12585239) B12585239
theorem B6637211 : Blo 906576 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B2041577 : Blo 906576 2041577 := bstep (se 2 (by rfl) ⟨765591, by rfl⟩ : syracuseStep 2041577 = 1531183) B1531183
theorem B6891479 : Blo 906576 6891479 := bstep (se 1 (by rfl) ⟨5168609, by rfl⟩ : syracuseStep 6891479 = 10337219) B10337219
theorem B1361975 : Blo 906576 1361975 := bstep (se 1 (by rfl) ⟨1021481, by rfl⟩ : syracuseStep 1361975 = 2042963) B2042963
theorem B1362095 : Blo 906576 1362095 := bstep (se 1 (by rfl) ⟨1021571, by rfl⟩ : syracuseStep 1362095 = 2043143) B2043143
theorem B3442931 : Blo 906576 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B4589945 : Blo 906576 4589945 := bstep (se 2 (by rfl) ⟨1721229, by rfl⟩ : syracuseStep 4589945 = 3442459) B3442459
theorem B1362335 : Blo 906576 1362335 := bstep (se 1 (by rfl) ⟨1021751, by rfl⟩ : syracuseStep 1362335 = 2043503) B2043503
theorem B5237473 : Blo 906576 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B2042783 : Blo 906576 2042783 := bstep (se 1 (by rfl) ⟨1532087, by rfl⟩ : syracuseStep 2042783 = 3064175) B3064175
theorem B4656761 : Blo 906576 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B4591241 : Blo 906576 4591241 := bstep (se 2 (by rfl) ⟨1721715, by rfl⟩ : syracuseStep 4591241 = 3443431) B3443431
theorem B2485919 : Blo 906576 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B10334303 : Blo 906576 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B4591727 : Blo 906576 4591727 := bstep (se 1 (by rfl) ⟨3443795, by rfl⟩ : syracuseStep 4591727 = 6887591) B6887591
theorem B2044223 : Blo 906576 2044223 := bstep (se 1 (by rfl) ⟨1533167, by rfl⟩ : syracuseStep 2044223 = 3066335) B3066335
theorem B1020415 : Blo 906576 1020415 := bstep (se 1 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 1020415 = 1530623) B1530623
theorem B2585513 : Blo 906576 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B7853851 : Blo 906576 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B907111 : Blo 906576 907111 := bstep (se 1 (by rfl) ⟨680333, by rfl⟩ : syracuseStep 907111 = 1360667) B1360667
theorem B26163323 : Blo 906576 26163323 := bstep (se 1 (by rfl) ⟨19622492, by rfl⟩ : syracuseStep 26163323 = 39244985) B39244985
theorem B19626137 : Blo 906576 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B3062231 : Blo 906576 3062231 := bstep (se 1 (by rfl) ⟨2296673, by rfl⟩ : syracuseStep 3062231 = 4593347) B4593347
theorem B58923521 : Blo 906576 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B908031 : Blo 906576 908031 := bstep (se 1 (by rfl) ⟨681023, by rfl⟩ : syracuseStep 908031 = 1362047) B1362047
theorem B908059 : Blo 906576 908059 := bstep (se 1 (by rfl) ⟨681044, by rfl⟩ : syracuseStep 908059 = 1362089) B1362089
theorem B8715113 : Blo 906576 8715113 := bstep (se 2 (by rfl) ⟨3268167, by rfl⟩ : syracuseStep 8715113 = 6536335) B6536335
theorem B908443 : Blo 906576 908443 := bstep (se 1 (by rfl) ⟨681332, by rfl⟩ : syracuseStep 908443 = 1362665) B1362665
theorem B6545099 : Blo 906576 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B6889535 : Blo 906576 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1360283 : Blo 906576 1360283 := bstep (se 1 (by rfl) ⟨1020212, by rfl⟩ : syracuseStep 1360283 = 2040425) B2040425
theorem B1147547 : Blo 906576 1147547 := bstep (se 1 (by rfl) ⟨860660, by rfl⟩ : syracuseStep 1147547 = 1721321) B1721321
theorem B2179739 : Blo 906576 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B1360553 : Blo 906576 1360553 := bstep (se 2 (by rfl) ⟨510207, by rfl⟩ : syracuseStep 1360553 = 1020415) B1020415
theorem B4424807 : Blo 906576 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B1361051 : Blo 906576 1361051 := bstep (se 1 (by rfl) ⟨1020788, by rfl⟩ : syracuseStep 1361051 = 2041577) B2041577
theorem B17442215 : Blo 906576 17442215 := bstep (se 1 (by rfl) ⟨13081661, by rfl⟩ : syracuseStep 17442215 = 26163323) B26163323
theorem B13084091 : Blo 906576 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B2295287 : Blo 906576 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B2041487 : Blo 906576 2041487 := bstep (se 1 (by rfl) ⟨1531115, by rfl⟩ : syracuseStep 2041487 = 3062231) B3062231
theorem B39282347 : Blo 906576 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B5810075 : Blo 906576 5810075 := bstep (se 1 (by rfl) ⟨4357556, by rfl⟩ : syracuseStep 5810075 = 8715113) B8715113
theorem B1361855 : Blo 906576 1361855 := bstep (se 1 (by rfl) ⟨1021391, by rfl⟩ : syracuseStep 1361855 = 2042783) B2042783
theorem B10471801 : Blo 906576 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B1657279 : Blo 906576 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B3681071 : Blo 906576 3681071 := bstep (se 1 (by rfl) ⟨2760803, by rfl⟩ : syracuseStep 3681071 = 5521607) B5521607
theorem B1362815 : Blo 906576 1362815 := bstep (se 1 (by rfl) ⟨1022111, by rfl⟩ : syracuseStep 1362815 = 2044223) B2044223
theorem B1723675 : Blo 906576 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B6983297 : Blo 906576 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B3059963 : Blo 906576 3059963 := bstep (se 1 (by rfl) ⟨2294972, by rfl⟩ : syracuseStep 3059963 = 4589945) B4589945
theorem B3060827 : Blo 906576 3060827 := bstep (se 1 (by rfl) ⟨2295620, by rfl⟩ : syracuseStep 3060827 = 4591241) B4591241
theorem B4363399 : Blo 906576 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B3061151 : Blo 906576 3061151 := bstep (se 1 (by rfl) ⟨2295863, by rfl⟩ : syracuseStep 3061151 = 4591727) B4591727
theorem B2905627 : Blo 906576 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B907515 : Blo 906576 907515 := bstep (se 1 (by rfl) ⟨680636, by rfl⟩ : syracuseStep 907515 = 1361273) B1361273
theorem B907583 : Blo 906576 907583 := bstep (se 1 (by rfl) ⟨680687, by rfl⟩ : syracuseStep 907583 = 1361375) B1361375
theorem B5593439 : Blo 906576 5593439 := bstep (se 1 (by rfl) ⟨4195079, by rfl⟩ : syracuseStep 5593439 = 8390159) B8390159
theorem B4594319 : Blo 906576 4594319 := bstep (se 1 (by rfl) ⟨3445739, by rfl⟩ : syracuseStep 4594319 = 6891479) B6891479
theorem B907983 : Blo 906576 907983 := bstep (se 1 (by rfl) ⟨680987, by rfl⟩ : syracuseStep 907983 = 1361975) B1361975
theorem B908063 : Blo 906576 908063 := bstep (se 1 (by rfl) ⟨681047, by rfl⟩ : syracuseStep 908063 = 1362095) B1362095
theorem B908223 : Blo 906576 908223 := bstep (se 1 (by rfl) ⟨681167, by rfl⟩ : syracuseStep 908223 = 1362335) B1362335
theorem B3104507 : Blo 906576 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B2039975 : Blo 906576 2039975 := bstep (se 1 (by rfl) ⟨1529981, by rfl⟩ : syracuseStep 2039975 = 3059963) B3059963
theorem B2040551 : Blo 906576 2040551 := bstep (se 1 (by rfl) ⟨1530413, by rfl⟩ : syracuseStep 2040551 = 3060827) B3060827
theorem B2949871 : Blo 906576 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B2040767 : Blo 906576 2040767 := bstep (se 1 (by rfl) ⟨1530575, by rfl⟩ : syracuseStep 2040767 = 3061151) B3061151
theorem B1360991 : Blo 906576 1360991 := bstep (se 1 (by rfl) ⟨1020743, by rfl⟩ : syracuseStep 1360991 = 2041487) B2041487
theorem B5817865 : Blo 906576 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B3728959 : Blo 906576 3728959 := bstep (se 1 (by rfl) ⟨2796719, by rfl⟩ : syracuseStep 3728959 = 5593439) B5593439
theorem B4655531 : Blo 906576 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B1453159 : Blo 906576 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B13962401 : Blo 906576 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B11628143 : Blo 906576 11628143 := bstep (se 1 (by rfl) ⟨8721107, by rfl⟩ : syracuseStep 11628143 = 17442215) B17442215
theorem B2298233 : Blo 906576 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B3060125 : Blo 906576 3060125 := bstep (se 3 (by rfl) ⟨573773, by rfl⟩ : syracuseStep 3060125 = 1147547) B1147547
theorem B2454047 : Blo 906576 2454047 := bstep (se 1 (by rfl) ⟨1840535, by rfl⟩ : syracuseStep 2454047 = 3681071) B3681071
theorem B8278685 : Blo 906576 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B4593023 : Blo 906576 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B906855 : Blo 906576 906855 := bstep (se 1 (by rfl) ⟨680141, by rfl⟩ : syracuseStep 906855 = 1360283) B1360283
theorem B907035 : Blo 906576 907035 := bstep (se 1 (by rfl) ⟨680276, by rfl⟩ : syracuseStep 907035 = 1360553) B1360553
theorem B907367 : Blo 906576 907367 := bstep (se 1 (by rfl) ⟨680525, by rfl⟩ : syracuseStep 907367 = 1361051) B1361051
theorem B8722727 : Blo 906576 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B1530191 : Blo 906576 1530191 := bstep (se 1 (by rfl) ⟨1147643, by rfl⟩ : syracuseStep 1530191 = 2295287) B2295287
theorem B26188231 : Blo 906576 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B3873383 : Blo 906576 3873383 := bstep (se 1 (by rfl) ⟨2905037, by rfl⟩ : syracuseStep 3873383 = 5810075) B5810075
theorem B907903 : Blo 906576 907903 := bstep (se 1 (by rfl) ⟨680927, by rfl⟩ : syracuseStep 907903 = 1361855) B1361855
theorem B3062879 : Blo 906576 3062879 := bstep (se 1 (by rfl) ⟨2297159, by rfl⟩ : syracuseStep 3062879 = 4594319) B4594319
theorem B908543 : Blo 906576 908543 := bstep (se 1 (by rfl) ⟨681407, by rfl⟩ : syracuseStep 908543 = 1362815) B1362815
theorem B3874169 : Blo 906576 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B8838821 : Blo 906576 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B1359983 : Blo 906576 1359983 := bstep (se 1 (by rfl) ⟨1019987, by rfl⟩ : syracuseStep 1359983 = 2039975) B2039975
theorem B1532155 : Blo 906576 1532155 := bstep (se 1 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 1532155 = 2298233) B2298233
theorem B2040083 : Blo 906576 2040083 := bstep (se 1 (by rfl) ⟨1530062, by rfl⟩ : syracuseStep 2040083 = 3060125) B3060125
theorem B1360367 : Blo 906576 1360367 := bstep (se 1 (by rfl) ⟨1020275, by rfl⟩ : syracuseStep 1360367 = 2040551) B2040551
theorem B7750181 : Blo 906576 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B1360511 : Blo 906576 1360511 := bstep (se 1 (by rfl) ⟨1020383, by rfl⟩ : syracuseStep 1360511 = 2040767) B2040767
theorem B3933161 : Blo 906576 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B2582255 : Blo 906576 2582255 := bstep (se 1 (by rfl) ⟨1936691, by rfl⟩ : syracuseStep 2582255 = 3873383) B3873383
theorem B23570189 : Blo 906576 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B2041919 : Blo 906576 2041919 := bstep (se 1 (by rfl) ⟨1531439, by rfl⟩ : syracuseStep 2041919 = 3062879) B3062879
theorem B9308267 : Blo 906576 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B2582779 : Blo 906576 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B7752095 : Blo 906576 7752095 := bstep (se 1 (by rfl) ⟨5814071, by rfl⟩ : syracuseStep 7752095 = 11628143) B11628143
theorem B34917641 : Blo 906576 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B1020127 : Blo 906576 1020127 := bstep (se 1 (by rfl) ⟨765095, by rfl⟩ : syracuseStep 1020127 = 1530191) B1530191
theorem B19887781 : Blo 906576 19887781 := bstep (se 4 (by rfl) ⟨1864479, by rfl⟩ : syracuseStep 19887781 = 3728959) B3728959
theorem B1636031 : Blo 906576 1636031 := bstep (se 1 (by rfl) ⟨1227023, by rfl⟩ : syracuseStep 1636031 = 2454047) B2454047
theorem B5519123 : Blo 906576 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B907327 : Blo 906576 907327 := bstep (se 1 (by rfl) ⟨680495, by rfl⟩ : syracuseStep 907327 = 1360991) B1360991
theorem B3062015 : Blo 906576 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B5815151 : Blo 906576 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B3103687 : Blo 906576 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B7757153 : Blo 906576 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B1360055 : Blo 906576 1360055 := bstep (se 1 (by rfl) ⟨1020041, by rfl⟩ : syracuseStep 1360055 = 2040083) B2040083
theorem B1360169 : Blo 906576 1360169 := bstep (se 2 (by rfl) ⟨510063, by rfl⟩ : syracuseStep 1360169 = 1020127) B1020127
theorem B2622107 : Blo 906576 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B1090687 : Blo 906576 1090687 := bstep (se 1 (by rfl) ⟨818015, by rfl⟩ : syracuseStep 1090687 = 1636031) B1636031
theorem B1721503 : Blo 906576 1721503 := bstep (se 1 (by rfl) ⟨1291127, by rfl⟩ : syracuseStep 1721503 = 2582255) B2582255
theorem B15713459 : Blo 906576 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B3679415 : Blo 906576 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B4138249 : Blo 906576 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B1361279 : Blo 906576 1361279 := bstep (se 1 (by rfl) ⟨1020959, by rfl⟩ : syracuseStep 1361279 = 2041919) B2041919
theorem B2041343 : Blo 906576 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B3876767 : Blo 906576 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B5171435 : Blo 906576 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B3443705 : Blo 906576 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B2042873 : Blo 906576 2042873 := bstep (se 2 (by rfl) ⟨766077, by rfl⟩ : syracuseStep 2042873 = 1532155) B1532155
theorem B6205511 : Blo 906576 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B23278427 : Blo 906576 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B906655 : Blo 906576 906655 := bstep (se 1 (by rfl) ⟨679991, by rfl⟩ : syracuseStep 906655 = 1359983) B1359983
theorem B906911 : Blo 906576 906911 := bstep (se 1 (by rfl) ⟨680183, by rfl⟩ : syracuseStep 906911 = 1360367) B1360367
theorem B5166787 : Blo 906576 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B907007 : Blo 906576 907007 := bstep (se 1 (by rfl) ⟨680255, by rfl⟩ : syracuseStep 907007 = 1360511) B1360511
theorem B5168063 : Blo 906576 5168063 := bstep (se 1 (by rfl) ⟨3876047, by rfl⟩ : syracuseStep 5168063 = 7752095) B7752095
theorem B26517041 : Blo 906576 26517041 := bstep (se 2 (by rfl) ⟨9943890, by rfl⟩ : syracuseStep 26517041 = 19887781) B19887781
theorem B4137007 : Blo 906576 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B1360895 : Blo 906576 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B2295337 : Blo 906576 2295337 := bstep (se 2 (by rfl) ⟨860751, by rfl⟩ : syracuseStep 2295337 = 1721503) B1721503
theorem B2295803 : Blo 906576 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B1361915 : Blo 906576 1361915 := bstep (se 1 (by rfl) ⟨1021436, by rfl⟩ : syracuseStep 1361915 = 2042873) B2042873
theorem B1748071 : Blo 906576 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B15518951 : Blo 906576 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B2452943 : Blo 906576 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B2584511 : Blo 906576 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B1454249 : Blo 906576 1454249 := bstep (se 2 (by rfl) ⟨545343, by rfl⟩ : syracuseStep 1454249 = 1090687) B1090687
theorem B5517665 : Blo 906576 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B3445375 : Blo 906576 3445375 := bstep (se 1 (by rfl) ⟨2584031, by rfl⟩ : syracuseStep 3445375 = 5168063) B5168063
theorem B906703 : Blo 906576 906703 := bstep (se 1 (by rfl) ⟨680027, by rfl⟩ : syracuseStep 906703 = 1360055) B1360055
theorem B906779 : Blo 906576 906779 := bstep (se 1 (by rfl) ⟨680084, by rfl⟩ : syracuseStep 906779 = 1360169) B1360169
theorem B10475639 : Blo 906576 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B907519 : Blo 906576 907519 := bstep (se 1 (by rfl) ⟨680639, by rfl⟩ : syracuseStep 907519 = 1361279) B1361279
theorem B3447623 : Blo 906576 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B6889049 : Blo 906576 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B17678027 : Blo 906576 17678027 := bstep (se 1 (by rfl) ⟨13258520, by rfl⟩ : syracuseStep 17678027 = 26517041) B26517041
theorem B3678443 : Blo 906576 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B9323045 : Blo 906576 9323045 := bstep (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) B1748071
theorem B1723007 : Blo 906576 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B5516009 : Blo 906576 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B969499 : Blo 906576 969499 := bstep (se 1 (by rfl) ⟨727124, by rfl⟩ : syracuseStep 969499 = 1454249) B1454249
theorem B6541181 : Blo 906576 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B6983759 : Blo 906576 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B2298415 : Blo 906576 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B3060449 : Blo 906576 3060449 := bstep (se 2 (by rfl) ⟨1147668, by rfl⟩ : syracuseStep 3060449 = 2295337) B2295337
theorem B4592699 : Blo 906576 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B11785351 : Blo 906576 11785351 := bstep (se 1 (by rfl) ⟨8839013, by rfl⟩ : syracuseStep 11785351 = 17678027) B17678027
theorem B907263 : Blo 906576 907263 := bstep (se 1 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 907263 = 1360895) B1360895
theorem B4593833 : Blo 906576 4593833 := bstep (se 2 (by rfl) ⟨1722687, by rfl⟩ : syracuseStep 4593833 = 3445375) B3445375
theorem B1530535 : Blo 906576 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B907943 : Blo 906576 907943 := bstep (se 1 (by rfl) ⟨680957, by rfl⟩ : syracuseStep 907943 = 1361915) B1361915
theorem B10345967 : Blo 906576 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B2040299 : Blo 906576 2040299 := bstep (se 1 (by rfl) ⟨1530224, by rfl⟩ : syracuseStep 2040299 = 3060449) B3060449
theorem B3064553 : Blo 906576 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B2040713 : Blo 906576 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B5170661 : Blo 906576 5170661 := bstep (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) B969499
theorem B15713801 : Blo 906576 15713801 := bstep (se 2 (by rfl) ⟨5892675, by rfl⟩ : syracuseStep 15713801 = 11785351) B11785351
theorem B1148671 : Blo 906576 1148671 := bstep (se 1 (by rfl) ⟨861503, by rfl⟩ : syracuseStep 1148671 = 1723007) B1723007
theorem B4360787 : Blo 906576 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B4655839 : Blo 906576 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B2452295 : Blo 906576 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B6215363 : Blo 906576 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B3061799 : Blo 906576 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B3062555 : Blo 906576 3062555 := bstep (se 1 (by rfl) ⟨2296916, by rfl⟩ : syracuseStep 3062555 = 4593833) B4593833
theorem B3677339 : Blo 906576 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B6897311 : Blo 906576 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B1360199 : Blo 906576 1360199 := bstep (se 1 (by rfl) ⟨1020149, by rfl⟩ : syracuseStep 1360199 = 2040299) B2040299
theorem B1360475 : Blo 906576 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B2041199 : Blo 906576 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B2041703 : Blo 906576 2041703 := bstep (se 1 (by rfl) ⟨1531277, by rfl⟩ : syracuseStep 2041703 = 3062555) B3062555
theorem B2451559 : Blo 906576 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B4598207 : Blo 906576 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B2043035 : Blo 906576 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B1634863 : Blo 906576 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B6207785 : Blo 906576 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B3447107 : Blo 906576 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B10475867 : Blo 906576 10475867 := bstep (se 1 (by rfl) ⟨7856900, by rfl⟩ : syracuseStep 10475867 = 15713801) B15713801
theorem B4143575 : Blo 906576 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B2907191 : Blo 906576 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B1531561 : Blo 906576 1531561 := bstep (se 2 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 1531561 = 1148671) B1148671
theorem B3268745 : Blo 906576 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B2179817 : Blo 906576 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B1360799 : Blo 906576 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B1361135 : Blo 906576 1361135 := bstep (se 1 (by rfl) ⟨1020851, by rfl⟩ : syracuseStep 1361135 = 2041703) B2041703
theorem B4138523 : Blo 906576 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B3065471 : Blo 906576 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B2762383 : Blo 906576 2762383 := bstep (se 1 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 2762383 = 4143575) B4143575
theorem B1362023 : Blo 906576 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B2042081 : Blo 906576 2042081 := bstep (se 2 (by rfl) ⟨765780, by rfl⟩ : syracuseStep 2042081 = 1531561) B1531561
theorem B2298071 : Blo 906576 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B6983911 : Blo 906576 6983911 := bstep (se 1 (by rfl) ⟨5237933, by rfl⟩ : syracuseStep 6983911 = 10475867) B10475867
theorem B1938127 : Blo 906576 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B906799 : Blo 906576 906799 := bstep (se 1 (by rfl) ⟨680099, by rfl⟩ : syracuseStep 906799 = 1360199) B1360199
theorem B906983 : Blo 906576 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B2179163 : Blo 906576 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B1532047 : Blo 906576 1532047 := bstep (se 1 (by rfl) ⟨1149035, by rfl⟩ : syracuseStep 1532047 = 2298071) B2298071
theorem B1361387 : Blo 906576 1361387 := bstep (se 1 (by rfl) ⟨1021040, by rfl⟩ : syracuseStep 1361387 = 2042081) B2042081
theorem B1453211 : Blo 906576 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B2584169 : Blo 906576 2584169 := bstep (se 2 (by rfl) ⟨969063, by rfl⟩ : syracuseStep 2584169 = 1938127) B1938127
theorem B2043647 : Blo 906576 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B3683177 : Blo 906576 3683177 := bstep (se 2 (by rfl) ⟨1381191, by rfl⟩ : syracuseStep 3683177 = 2762383) B2762383
theorem B9311881 : Blo 906576 9311881 := bstep (se 2 (by rfl) ⟨3491955, by rfl⟩ : syracuseStep 9311881 = 6983911) B6983911
theorem B907199 : Blo 906576 907199 := bstep (se 1 (by rfl) ⟨680399, by rfl⟩ : syracuseStep 907199 = 1360799) B1360799
theorem B907423 : Blo 906576 907423 := bstep (se 1 (by rfl) ⟨680567, by rfl⟩ : syracuseStep 907423 = 1361135) B1361135
theorem B2759015 : Blo 906576 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B908015 : Blo 906576 908015 := bstep (se 1 (by rfl) ⟨681011, by rfl⟩ : syracuseStep 908015 = 1362023) B1362023
theorem B968807 : Blo 906576 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B1722779 : Blo 906576 1722779 := bstep (se 1 (by rfl) ⟨1292084, by rfl⟩ : syracuseStep 1722779 = 2584169) B2584169
theorem B1362431 : Blo 906576 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B2042729 : Blo 906576 2042729 := bstep (se 2 (by rfl) ⟨766023, by rfl⟩ : syracuseStep 2042729 = 1532047) B1532047
theorem B5811101 : Blo 906576 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B1839343 : Blo 906576 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B12415841 : Blo 906576 12415841 := bstep (se 2 (by rfl) ⟨4655940, by rfl⟩ : syracuseStep 12415841 = 9311881) B9311881
theorem B2455451 : Blo 906576 2455451 := bstep (se 1 (by rfl) ⟨1841588, by rfl⟩ : syracuseStep 2455451 = 3683177) B3683177
theorem B907591 : Blo 906576 907591 := bstep (se 1 (by rfl) ⟨680693, by rfl⟩ : syracuseStep 907591 = 1361387) B1361387
theorem B1148519 : Blo 906576 1148519 := bstep (se 1 (by rfl) ⟨861389, by rfl⟩ : syracuseStep 1148519 = 1722779) B1722779
theorem B1361819 : Blo 906576 1361819 := bstep (se 1 (by rfl) ⟨1021364, by rfl⟩ : syracuseStep 1361819 = 2042729) B2042729
theorem B2583485 : Blo 906576 2583485 := bstep (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) B968807
theorem B2452457 : Blo 906576 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B8277227 : Blo 906576 8277227 := bstep (se 1 (by rfl) ⟨6207920, by rfl⟩ : syracuseStep 8277227 = 12415841) B12415841
theorem B1636967 : Blo 906576 1636967 := bstep (se 1 (by rfl) ⟨1227725, by rfl⟩ : syracuseStep 1636967 = 2455451) B2455451
theorem B908287 : Blo 906576 908287 := bstep (se 1 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 908287 = 1362431) B1362431
theorem B3874067 : Blo 906576 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B1722323 : Blo 906576 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B2582711 : Blo 906576 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B1634971 : Blo 906576 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B5518151 : Blo 906576 5518151 := bstep (se 1 (by rfl) ⟨4138613, by rfl⟩ : syracuseStep 5518151 = 8277227) B8277227
theorem B907879 : Blo 906576 907879 := bstep (se 1 (by rfl) ⟨680909, by rfl⟩ : syracuseStep 907879 = 1361819) B1361819
theorem B3062717 : Blo 906576 3062717 := bstep (se 3 (by rfl) ⟨574259, by rfl⟩ : syracuseStep 3062717 = 1148519) B1148519
theorem B4365245 : Blo 906576 4365245 := bstep (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) B1636967
theorem B3678767 : Blo 906576 3678767 := bstep (se 1 (by rfl) ⟨2759075, by rfl⟩ : syracuseStep 3678767 = 5518151) B5518151
theorem B2179961 : Blo 906576 2179961 := bstep (se 2 (by rfl) ⟨817485, by rfl⟩ : syracuseStep 2179961 = 1634971) B1634971
theorem B1721807 : Blo 906576 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B2041811 : Blo 906576 2041811 := bstep (se 1 (by rfl) ⟨1531358, by rfl⟩ : syracuseStep 2041811 = 3062717) B3062717
theorem B2910163 : Blo 906576 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B4592861 : Blo 906576 4592861 := bstep (se 3 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 4592861 = 1722323) B1722323
theorem B1147871 : Blo 906576 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B1361207 : Blo 906576 1361207 := bstep (se 1 (by rfl) ⟨1020905, by rfl⟩ : syracuseStep 1361207 = 2041811) B2041811
theorem B2452511 : Blo 906576 2452511 := bstep (se 1 (by rfl) ⟨1839383, by rfl⟩ : syracuseStep 2452511 = 3678767) B3678767
theorem B1453307 : Blo 906576 1453307 := bstep (se 1 (by rfl) ⟨1089980, by rfl⟩ : syracuseStep 1453307 = 2179961) B2179961
theorem B3880217 : Blo 906576 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B3061907 : Blo 906576 3061907 := bstep (se 1 (by rfl) ⟨2296430, by rfl⟩ : syracuseStep 3061907 = 4592861) B4592861
theorem B3875485 : Blo 906576 3875485 := bstep (se 3 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 3875485 = 1453307) B1453307
theorem B2041271 : Blo 906576 2041271 := bstep (se 1 (by rfl) ⟨1530953, by rfl⟩ : syracuseStep 2041271 = 3061907) B3061907
theorem B1635007 : Blo 906576 1635007 := bstep (se 1 (by rfl) ⟨1226255, by rfl⟩ : syracuseStep 1635007 = 2452511) B2452511
theorem B3060989 : Blo 906576 3060989 := bstep (se 3 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 3060989 = 1147871) B1147871
theorem B2586811 : Blo 906576 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B907471 : Blo 906576 907471 := bstep (se 1 (by rfl) ⟨680603, by rfl⟩ : syracuseStep 907471 = 1361207) B1361207
theorem B3449081 : Blo 906576 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B2040659 : Blo 906576 2040659 := bstep (se 1 (by rfl) ⟨1530494, by rfl⟩ : syracuseStep 2040659 = 3060989) B3060989
theorem B2180009 : Blo 906576 2180009 := bstep (se 2 (by rfl) ⟨817503, by rfl⟩ : syracuseStep 2180009 = 1635007) B1635007
theorem B1360847 : Blo 906576 1360847 := bstep (se 1 (by rfl) ⟨1020635, by rfl⟩ : syracuseStep 1360847 = 2041271) B2041271
theorem B5167313 : Blo 906576 5167313 := bstep (se 2 (by rfl) ⟨1937742, by rfl⟩ : syracuseStep 5167313 = 3875485) B3875485
theorem B1360439 : Blo 906576 1360439 := bstep (se 1 (by rfl) ⟨1020329, by rfl⟩ : syracuseStep 1360439 = 2040659) B2040659
theorem B1453339 : Blo 906576 1453339 := bstep (se 1 (by rfl) ⟨1090004, by rfl⟩ : syracuseStep 1453339 = 2180009) B2180009
theorem B3444875 : Blo 906576 3444875 := bstep (se 1 (by rfl) ⟨2583656, by rfl⟩ : syracuseStep 3444875 = 5167313) B5167313
theorem B2299387 : Blo 906576 2299387 := bstep (se 1 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 2299387 = 3449081) B3449081
theorem B907231 : Blo 906576 907231 := bstep (se 1 (by rfl) ⟨680423, by rfl⟩ : syracuseStep 907231 = 1360847) B1360847
theorem B3065849 : Blo 906576 3065849 := bstep (se 2 (by rfl) ⟨1149693, by rfl⟩ : syracuseStep 3065849 = 2299387) B2299387
theorem B2296583 : Blo 906576 2296583 := bstep (se 1 (by rfl) ⟨1722437, by rfl⟩ : syracuseStep 2296583 = 3444875) B3444875
theorem B1937785 : Blo 906576 1937785 := bstep (se 2 (by rfl) ⟨726669, by rfl⟩ : syracuseStep 1937785 = 1453339) B1453339
theorem B906959 : Blo 906576 906959 := bstep (se 1 (by rfl) ⟨680219, by rfl⟩ : syracuseStep 906959 = 1360439) B1360439
theorem B2583713 : Blo 906576 2583713 := bstep (se 2 (by rfl) ⟨968892, by rfl⟩ : syracuseStep 2583713 = 1937785) B1937785
theorem B2043899 : Blo 906576 2043899 := bstep (se 1 (by rfl) ⟨1532924, by rfl⟩ : syracuseStep 2043899 = 3065849) B3065849
theorem B1531055 : Blo 906576 1531055 := bstep (se 1 (by rfl) ⟨1148291, by rfl⟩ : syracuseStep 1531055 = 2296583) B2296583
theorem B1722475 : Blo 906576 1722475 := bstep (se 1 (by rfl) ⟨1291856, by rfl⟩ : syracuseStep 1722475 = 2583713) B2583713
theorem B1362599 : Blo 906576 1362599 := bstep (se 1 (by rfl) ⟨1021949, by rfl⟩ : syracuseStep 1362599 = 2043899) B2043899
theorem B1020703 : Blo 906576 1020703 := bstep (se 1 (by rfl) ⟨765527, by rfl⟩ : syracuseStep 1020703 = 1531055) B1531055
theorem B1360937 : Blo 906576 1360937 := bstep (se 2 (by rfl) ⟨510351, by rfl⟩ : syracuseStep 1360937 = 1020703) B1020703
theorem B2296633 : Blo 906576 2296633 := bstep (se 2 (by rfl) ⟨861237, by rfl⟩ : syracuseStep 2296633 = 1722475) B1722475
theorem B908399 : Blo 906576 908399 := bstep (se 1 (by rfl) ⟨681299, by rfl⟩ : syracuseStep 908399 = 1362599) B1362599
theorem B907291 : Blo 906576 907291 := bstep (se 1 (by rfl) ⟨680468, by rfl⟩ : syracuseStep 907291 = 1360937) B1360937
theorem B3062177 : Blo 906576 3062177 := bstep (se 2 (by rfl) ⟨1148316, by rfl⟩ : syracuseStep 3062177 = 2296633) B2296633
theorem B2041451 : Blo 906576 2041451 := bstep (se 1 (by rfl) ⟨1531088, by rfl⟩ : syracuseStep 2041451 = 3062177) B3062177
theorem B1360967 : Blo 906576 1360967 := bstep (se 1 (by rfl) ⟨1020725, by rfl⟩ : syracuseStep 1360967 = 2041451) B2041451
theorem B907311 : Blo 906576 907311 := bstep (se 1 (by rfl) ⟨680483, by rfl⟩ : syracuseStep 907311 = 1360967) B1360967

theorem C0 (j : ℕ) (h1 : 226644 ≤ j) (h2 : j ≤ 227143) : Blo 906576 (4 * j + 3) := by
  interval_cases j
  · exact B906579
  · exact B906583
  · exact B906587
  · exact B906591
  · exact B906595
  · exact B906599
  · exact B906603
  · exact B906607
  · exact B906611
  · exact B906615
  · exact B906619
  · exact B906623
  · exact B906627
  · exact B906631
  · exact B906635
  · exact B906639
  · exact B906643
  · exact B906647
  · exact B906651
  · exact B906655
  · exact B906659
  · exact B906663
  · exact B906667
  · exact B906671
  · exact B906675
  · exact B906679
  · exact B906683
  · exact B906687
  · exact B906691
  · exact B906695
  · exact B906699
  · exact B906703
  · exact B906707
  · exact B906711
  · exact B906715
  · exact B906719
  · exact B906723
  · exact B906727
  · exact B906731
  · exact B906735
  · exact B906739
  · exact B906743
  · exact B906747
  · exact B906751
  · exact B906755
  · exact B906759
  · exact B906763
  · exact B906767
  · exact B906771
  · exact B906775
  · exact B906779
  · exact B906783
  · exact B906787
  · exact B906791
  · exact B906795
  · exact B906799
  · exact B906803
  · exact B906807
  · exact B906811
  · exact B906815
  · exact B906819
  · exact B906823
  · exact B906827
  · exact B906831
  · exact B906835
  · exact B906839
  · exact B906843
  · exact B906847
  · exact B906851
  · exact B906855
  · exact B906859
  · exact B906863
  · exact B906867
  · exact B906871
  · exact B906875
  · exact B906879
  · exact B906883
  · exact B906887
  · exact B906891
  · exact B906895
  · exact B906899
  · exact B906903
  · exact B906907
  · exact B906911
  · exact B906915
  · exact B906919
  · exact B906923
  · exact B906927
  · exact B906931
  · exact B906935
  · exact B906939
  · exact B906943
  · exact B906947
  · exact B906951
  · exact B906955
  · exact B906959
  · exact B906963
  · exact B906967
  · exact B906971
  · exact B906975
  · exact B906979
  · exact B906983
  · exact B906987
  · exact B906991
  · exact B906995
  · exact B906999
  · exact B907003
  · exact B907007
  · exact B907011
  · exact B907015
  · exact B907019
  · exact B907023
  · exact B907027
  · exact B907031
  · exact B907035
  · exact B907039
  · exact B907043
  · exact B907047
  · exact B907051
  · exact B907055
  · exact B907059
  · exact B907063
  · exact B907067
  · exact B907071
  · exact B907075
  · exact B907079
  · exact B907083
  · exact B907087
  · exact B907091
  · exact B907095
  · exact B907099
  · exact B907103
  · exact B907107
  · exact B907111
  · exact B907115
  · exact B907119
  · exact B907123
  · exact B907127
  · exact B907131
  · exact B907135
  · exact B907139
  · exact B907143
  · exact B907147
  · exact B907151
  · exact B907155
  · exact B907159
  · exact B907163
  · exact B907167
  · exact B907171
  · exact B907175
  · exact B907179
  · exact B907183
  · exact B907187
  · exact B907191
  · exact B907195
  · exact B907199
  · exact B907203
  · exact B907207
  · exact B907211
  · exact B907215
  · exact B907219
  · exact B907223
  · exact B907227
  · exact B907231
  · exact B907235
  · exact B907239
  · exact B907243
  · exact B907247
  · exact B907251
  · exact B907255
  · exact B907259
  · exact B907263
  · exact B907267
  · exact B907271
  · exact B907275
  · exact B907279
  · exact B907283
  · exact B907287
  · exact B907291
  · exact B907295
  · exact B907299
  · exact B907303
  · exact B907307
  · exact B907311
  · exact B907315
  · exact B907319
  · exact B907323
  · exact B907327
  · exact B907331
  · exact B907335
  · exact B907339
  · exact B907343
  · exact B907347
  · exact B907351
  · exact B907355
  · exact B907359
  · exact B907363
  · exact B907367
  · exact B907371
  · exact B907375
  · exact B907379
  · exact B907383
  · exact B907387
  · exact B907391
  · exact B907395
  · exact B907399
  · exact B907403
  · exact B907407
  · exact B907411
  · exact B907415
  · exact B907419
  · exact B907423
  · exact B907427
  · exact B907431
  · exact B907435
  · exact B907439
  · exact B907443
  · exact B907447
  · exact B907451
  · exact B907455
  · exact B907459
  · exact B907463
  · exact B907467
  · exact B907471
  · exact B907475
  · exact B907479
  · exact B907483
  · exact B907487
  · exact B907491
  · exact B907495
  · exact B907499
  · exact B907503
  · exact B907507
  · exact B907511
  · exact B907515
  · exact B907519
  · exact B907523
  · exact B907527
  · exact B907531
  · exact B907535
  · exact B907539
  · exact B907543
  · exact B907547
  · exact B907551
  · exact B907555
  · exact B907559
  · exact B907563
  · exact B907567
  · exact B907571
  · exact B907575
  · exact B907579
  · exact B907583
  · exact B907587
  · exact B907591
  · exact B907595
  · exact B907599
  · exact B907603
  · exact B907607
  · exact B907611
  · exact B907615
  · exact B907619
  · exact B907623
  · exact B907627
  · exact B907631
  · exact B907635
  · exact B907639
  · exact B907643
  · exact B907647
  · exact B907651
  · exact B907655
  · exact B907659
  · exact B907663
  · exact B907667
  · exact B907671
  · exact B907675
  · exact B907679
  · exact B907683
  · exact B907687
  · exact B907691
  · exact B907695
  · exact B907699
  · exact B907703
  · exact B907707
  · exact B907711
  · exact B907715
  · exact B907719
  · exact B907723
  · exact B907727
  · exact B907731
  · exact B907735
  · exact B907739
  · exact B907743
  · exact B907747
  · exact B907751
  · exact B907755
  · exact B907759
  · exact B907763
  · exact B907767
  · exact B907771
  · exact B907775
  · exact B907779
  · exact B907783
  · exact B907787
  · exact B907791
  · exact B907795
  · exact B907799
  · exact B907803
  · exact B907807
  · exact B907811
  · exact B907815
  · exact B907819
  · exact B907823
  · exact B907827
  · exact B907831
  · exact B907835
  · exact B907839
  · exact B907843
  · exact B907847
  · exact B907851
  · exact B907855
  · exact B907859
  · exact B907863
  · exact B907867
  · exact B907871
  · exact B907875
  · exact B907879
  · exact B907883
  · exact B907887
  · exact B907891
  · exact B907895
  · exact B907899
  · exact B907903
  · exact B907907
  · exact B907911
  · exact B907915
  · exact B907919
  · exact B907923
  · exact B907927
  · exact B907931
  · exact B907935
  · exact B907939
  · exact B907943
  · exact B907947
  · exact B907951
  · exact B907955
  · exact B907959
  · exact B907963
  · exact B907967
  · exact B907971
  · exact B907975
  · exact B907979
  · exact B907983
  · exact B907987
  · exact B907991
  · exact B907995
  · exact B907999
  · exact B908003
  · exact B908007
  · exact B908011
  · exact B908015
  · exact B908019
  · exact B908023
  · exact B908027
  · exact B908031
  · exact B908035
  · exact B908039
  · exact B908043
  · exact B908047
  · exact B908051
  · exact B908055
  · exact B908059
  · exact B908063
  · exact B908067
  · exact B908071
  · exact B908075
  · exact B908079
  · exact B908083
  · exact B908087
  · exact B908091
  · exact B908095
  · exact B908099
  · exact B908103
  · exact B908107
  · exact B908111
  · exact B908115
  · exact B908119
  · exact B908123
  · exact B908127
  · exact B908131
  · exact B908135
  · exact B908139
  · exact B908143
  · exact B908147
  · exact B908151
  · exact B908155
  · exact B908159
  · exact B908163
  · exact B908167
  · exact B908171
  · exact B908175
  · exact B908179
  · exact B908183
  · exact B908187
  · exact B908191
  · exact B908195
  · exact B908199
  · exact B908203
  · exact B908207
  · exact B908211
  · exact B908215
  · exact B908219
  · exact B908223
  · exact B908227
  · exact B908231
  · exact B908235
  · exact B908239
  · exact B908243
  · exact B908247
  · exact B908251
  · exact B908255
  · exact B908259
  · exact B908263
  · exact B908267
  · exact B908271
  · exact B908275
  · exact B908279
  · exact B908283
  · exact B908287
  · exact B908291
  · exact B908295
  · exact B908299
  · exact B908303
  · exact B908307
  · exact B908311
  · exact B908315
  · exact B908319
  · exact B908323
  · exact B908327
  · exact B908331
  · exact B908335
  · exact B908339
  · exact B908343
  · exact B908347
  · exact B908351
  · exact B908355
  · exact B908359
  · exact B908363
  · exact B908367
  · exact B908371
  · exact B908375
  · exact B908379
  · exact B908383
  · exact B908387
  · exact B908391
  · exact B908395
  · exact B908399
  · exact B908403
  · exact B908407
  · exact B908411
  · exact B908415
  · exact B908419
  · exact B908423
  · exact B908427
  · exact B908431
  · exact B908435
  · exact B908439
  · exact B908443
  · exact B908447
  · exact B908451
  · exact B908455
  · exact B908459
  · exact B908463
  · exact B908467
  · exact B908471
  · exact B908475
  · exact B908479
  · exact B908483
  · exact B908487
  · exact B908491
  · exact B908495
  · exact B908499
  · exact B908503
  · exact B908507
  · exact B908511
  · exact B908515
  · exact B908519
  · exact B908523
  · exact B908527
  · exact B908531
  · exact B908535
  · exact B908539
  · exact B908543
  · exact B908547
  · exact B908551
  · exact B908555
  · exact B908559
  · exact B908563
  · exact B908567
  · exact B908571
  · exact B908575

theorem solution (m : ℕ) (hlo : 906576 ≤ m) (hhi : m ≤ 908575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 226644 ≤ j := by omega
    have hj2 : j ≤ 227143 := by omega
    have hb : Blo 906576 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
