-- Prove2me | solution 1 for syracuse_descends_range_1768085_1770085
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:41:08.703108+00:00
-- url     : https://prove2.me/submissions/cc3dcc3d-c64e-4b17-8897-a9bd0405f9d7

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


theorem B2654213 : Blo 1768085 2654213 := bbase (se 4 (by rfl) ⟨248832, by rfl⟩ : syracuseStep 2654213 = 497665) (by norm_num)
theorem B1990669 : Blo 1768085 1990669 := bbase (se 3 (by rfl) ⟨373250, by rfl⟩ : syracuseStep 1990669 = 746501) (by norm_num)
theorem B3498013 : Blo 1768085 3498013 := bbase (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) (by norm_num)
theorem B2654237 : Blo 1768085 2654237 := bbase (se 3 (by rfl) ⟨497669, by rfl⟩ : syracuseStep 2654237 = 995339) (by norm_num)
theorem B3776557 : Blo 1768085 3776557 := bbase (se 3 (by rfl) ⟨708104, by rfl⟩ : syracuseStep 3776557 = 1416209) (by norm_num)
theorem B1990705 : Blo 1768085 1990705 := bbase (se 2 (by rfl) ⟨746514, by rfl⟩ : syracuseStep 1990705 = 1493029) (by norm_num)
theorem B5972021 : Blo 1768085 5972021 := bbase (se 5 (by rfl) ⟨279938, by rfl⟩ : syracuseStep 5972021 = 559877) (by norm_num)
theorem B3981365 : Blo 1768085 3981365 := bbase (se 5 (by rfl) ⟨186626, by rfl⟩ : syracuseStep 3981365 = 373253) (by norm_num)
theorem B2654261 : Blo 1768085 2654261 := bbase (se 5 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 2654261 = 248837) (by norm_num)
theorem B2654285 : Blo 1768085 2654285 := bbase (se 3 (by rfl) ⟨497678, by rfl⟩ : syracuseStep 2654285 = 995357) (by norm_num)
theorem B3186773 : Blo 1768085 3186773 := bbase (se 8 (by rfl) ⟨18672, by rfl⟩ : syracuseStep 3186773 = 37345) (by norm_num)
theorem B1990741 : Blo 1768085 1990741 := bbase (se 8 (by rfl) ⟨11664, by rfl⟩ : syracuseStep 1990741 = 23329) (by norm_num)
theorem B2654309 : Blo 1768085 2654309 := bbase (se 4 (by rfl) ⟨248841, by rfl⟩ : syracuseStep 2654309 = 497683) (by norm_num)
theorem B3358837 : Blo 1768085 3358837 := bbase (se 5 (by rfl) ⟨157445, by rfl⟩ : syracuseStep 3358837 = 314891) (by norm_num)
theorem B1990777 : Blo 1768085 1990777 := bbase (se 2 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 1990777 = 1493083) (by norm_num)
theorem B3981437 : Blo 1768085 3981437 := bbase (se 3 (by rfl) ⟨746519, by rfl⟩ : syracuseStep 3981437 = 1493039) (by norm_num)
theorem B2654333 : Blo 1768085 2654333 := bbase (se 3 (by rfl) ⟨497687, by rfl⟩ : syracuseStep 2654333 = 995375) (by norm_num)
theorem B2834557 : Blo 1768085 2834557 := bbase (se 3 (by rfl) ⟨531479, by rfl⟩ : syracuseStep 2834557 = 1062959) (by norm_num)
theorem B2654357 : Blo 1768085 2654357 := bbase (se 6 (by rfl) ⟨62211, by rfl⟩ : syracuseStep 2654357 = 124423) (by norm_num)
theorem B4538525 : Blo 1768085 4538525 := bbase (se 3 (by rfl) ⟨850973, by rfl⟩ : syracuseStep 4538525 = 1701947) (by norm_num)
theorem B1990813 : Blo 1768085 1990813 := bbase (se 3 (by rfl) ⟨373277, by rfl⟩ : syracuseStep 1990813 = 746555) (by norm_num)
theorem B4087973 : Blo 1768085 4087973 := bbase (se 4 (by rfl) ⟨383247, by rfl⟩ : syracuseStep 4087973 = 766495) (by norm_num)
theorem B2654381 : Blo 1768085 2654381 := bbase (se 3 (by rfl) ⟨497696, by rfl⟩ : syracuseStep 2654381 = 995393) (by norm_num)
theorem B1990849 : Blo 1768085 1990849 := bbase (se 2 (by rfl) ⟨746568, by rfl⟩ : syracuseStep 1990849 = 1493137) (by norm_num)
theorem B3981509 : Blo 1768085 3981509 := bbase (se 4 (by rfl) ⟨373266, by rfl⟩ : syracuseStep 3981509 = 746533) (by norm_num)
theorem B2654405 : Blo 1768085 2654405 := bbase (se 4 (by rfl) ⟨248850, by rfl⟩ : syracuseStep 2654405 = 497701) (by norm_num)
theorem B2654429 : Blo 1768085 2654429 := bbase (se 3 (by rfl) ⟨497705, by rfl⟩ : syracuseStep 2654429 = 995411) (by norm_num)
theorem B1990885 : Blo 1768085 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B5038325 : Blo 1768085 5038325 := bbase (se 5 (by rfl) ⟨236171, by rfl⟩ : syracuseStep 5038325 = 472343) (by norm_num)
theorem B2654453 : Blo 1768085 2654453 := bbase (se 5 (by rfl) ⟨124427, by rfl⟩ : syracuseStep 2654453 = 248855) (by norm_num)
theorem B7176437 : Blo 1768085 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B1990921 : Blo 1768085 1990921 := bbase (se 2 (by rfl) ⟨746595, by rfl⟩ : syracuseStep 1990921 = 1493191) (by norm_num)
theorem B3981581 : Blo 1768085 3981581 := bbase (se 3 (by rfl) ⟨746546, by rfl⟩ : syracuseStep 3981581 = 1493093) (by norm_num)
theorem B2654477 : Blo 1768085 2654477 := bbase (se 3 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 2654477 = 995429) (by norm_num)
theorem B2654501 : Blo 1768085 2654501 := bbase (se 4 (by rfl) ⟨248859, by rfl⟩ : syracuseStep 2654501 = 497719) (by norm_num)
theorem B1990957 : Blo 1768085 1990957 := bbase (se 3 (by rfl) ⟨373304, by rfl⟩ : syracuseStep 1990957 = 746609) (by norm_num)
theorem B2654525 : Blo 1768085 2654525 := bbase (se 3 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 2654525 = 995447) (by norm_num)
theorem B4538693 : Blo 1768085 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B1990993 : Blo 1768085 1990993 := bbase (se 2 (by rfl) ⟨746622, by rfl⟩ : syracuseStep 1990993 = 1493245) (by norm_num)
theorem B3981653 : Blo 1768085 3981653 := bbase (se 10 (by rfl) ⟨5832, by rfl⟩ : syracuseStep 3981653 = 11665) (by norm_num)
theorem B2654549 : Blo 1768085 2654549 := bbase (se 10 (by rfl) ⟨3888, by rfl⟩ : syracuseStep 2654549 = 7777) (by norm_num)
theorem B2654573 : Blo 1768085 2654573 := bbase (se 3 (by rfl) ⟨497732, by rfl⟩ : syracuseStep 2654573 = 995465) (by norm_num)
theorem B1991029 : Blo 1768085 1991029 := bbase (se 5 (by rfl) ⟨93329, by rfl⟩ : syracuseStep 1991029 = 186659) (by norm_num)
theorem B8069509 : Blo 1768085 8069509 := bbase (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) (by norm_num)
theorem B2654597 : Blo 1768085 2654597 := bbase (se 4 (by rfl) ⟨248868, by rfl⟩ : syracuseStep 2654597 = 497737) (by norm_num)
theorem B1991065 : Blo 1768085 1991065 := bbase (se 2 (by rfl) ⟨746649, by rfl⟩ : syracuseStep 1991065 = 1493299) (by norm_num)
theorem B3981725 : Blo 1768085 3981725 := bbase (se 3 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 3981725 = 1493147) (by norm_num)
theorem B2654621 : Blo 1768085 2654621 := bbase (se 3 (by rfl) ⟨497741, by rfl⟩ : syracuseStep 2654621 = 995483) (by norm_num)
theorem B3359141 : Blo 1768085 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B2654645 : Blo 1768085 2654645 := bbase (se 5 (by rfl) ⟨124436, by rfl⟩ : syracuseStep 2654645 = 248873) (by norm_num)
theorem B1991101 : Blo 1768085 1991101 := bbase (se 3 (by rfl) ⟨373331, by rfl⟩ : syracuseStep 1991101 = 746663) (by norm_num)
theorem B2654669 : Blo 1768085 2654669 := bbase (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) (by norm_num)
theorem B4538845 : Blo 1768085 4538845 := bbase (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) (by norm_num)
theorem B2154973 : Blo 1768085 2154973 := bbase (se 3 (by rfl) ⟨404057, by rfl⟩ : syracuseStep 2154973 = 808115) (by norm_num)
theorem B1991137 : Blo 1768085 1991137 := bbase (se 2 (by rfl) ⟨746676, by rfl⟩ : syracuseStep 1991137 = 1493353) (by norm_num)
theorem B5972453 : Blo 1768085 5972453 := bbase (se 4 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 5972453 = 1119835) (by norm_num)
theorem B3981797 : Blo 1768085 3981797 := bbase (se 4 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 3981797 = 746587) (by norm_num)
theorem B2654693 : Blo 1768085 2654693 := bbase (se 4 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 2654693 = 497755) (by norm_num)
theorem B2654717 : Blo 1768085 2654717 := bbase (se 3 (by rfl) ⟨497759, by rfl⟩ : syracuseStep 2654717 = 995519) (by norm_num)
theorem B1991173 : Blo 1768085 1991173 := bbase (se 4 (by rfl) ⟨186672, by rfl⟩ : syracuseStep 1991173 = 373345) (by norm_num)
theorem B2654741 : Blo 1768085 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B1991209 : Blo 1768085 1991209 := bbase (se 2 (by rfl) ⟨746703, by rfl⟩ : syracuseStep 1991209 = 1493407) (by norm_num)
theorem B3981869 : Blo 1768085 3981869 := bbase (se 3 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 3981869 = 1493201) (by norm_num)
theorem B2654765 : Blo 1768085 2654765 := bbase (se 3 (by rfl) ⟨497768, by rfl⟩ : syracuseStep 2654765 = 995537) (by norm_num)
theorem B2654789 : Blo 1768085 2654789 := bbase (se 4 (by rfl) ⟨248886, by rfl⟩ : syracuseStep 2654789 = 497773) (by norm_num)
theorem B2835013 : Blo 1768085 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B1991245 : Blo 1768085 1991245 := bbase (se 3 (by rfl) ⟨373358, by rfl⟩ : syracuseStep 1991245 = 746717) (by norm_num)
theorem B2654813 : Blo 1768085 2654813 := bbase (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) (by norm_num)
theorem B1991281 : Blo 1768085 1991281 := bbase (se 2 (by rfl) ⟨746730, by rfl⟩ : syracuseStep 1991281 = 1493461) (by norm_num)
theorem B3981941 : Blo 1768085 3981941 := bbase (se 5 (by rfl) ⟨186653, by rfl⟩ : syracuseStep 3981941 = 373307) (by norm_num)
theorem B2654837 : Blo 1768085 2654837 := bbase (se 5 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 2654837 = 248891) (by norm_num)
theorem B6718085 : Blo 1768085 6718085 := bbase (se 4 (by rfl) ⟨629820, by rfl⟩ : syracuseStep 6718085 = 1259641) (by norm_num)
theorem B2654861 : Blo 1768085 2654861 := bbase (se 3 (by rfl) ⟨497786, by rfl⟩ : syracuseStep 2654861 = 995573) (by norm_num)
theorem B1991317 : Blo 1768085 1991317 := bbase (se 6 (by rfl) ⟨46671, by rfl⟩ : syracuseStep 1991317 = 93343) (by norm_num)
theorem B5038757 : Blo 1768085 5038757 := bbase (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) (by norm_num)
theorem B2654885 : Blo 1768085 2654885 := bbase (se 4 (by rfl) ⟨248895, by rfl⟩ : syracuseStep 2654885 = 497791) (by norm_num)
theorem B8954549 : Blo 1768085 8954549 := bbase (se 5 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 8954549 = 839489) (by norm_num)
theorem B3982013 : Blo 1768085 3982013 := bbase (se 3 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 3982013 = 1493255) (by norm_num)
theorem B2654909 : Blo 1768085 2654909 := bbase (se 3 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 2654909 = 995591) (by norm_num)
theorem B2654933 : Blo 1768085 2654933 := bbase (se 7 (by rfl) ⟨31112, by rfl⟩ : syracuseStep 2654933 = 62225) (by norm_num)
theorem B2654957 : Blo 1768085 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B3982085 : Blo 1768085 3982085 := bbase (se 4 (by rfl) ⟨373320, by rfl⟩ : syracuseStep 3982085 = 746641) (by norm_num)
theorem B2654981 : Blo 1768085 2654981 := bbase (se 4 (by rfl) ⟨248904, by rfl⟩ : syracuseStep 2654981 = 497809) (by norm_num)
theorem B30237461 : Blo 1768085 30237461 := bbase (se 6 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 30237461 = 1417381) (by norm_num)
theorem B2655005 : Blo 1768085 2655005 := bbase (se 3 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 2655005 = 995627) (by norm_num)
theorem B2655029 : Blo 1768085 2655029 := bbase (se 5 (by rfl) ⟨124454, by rfl⟩ : syracuseStep 2655029 = 248909) (by norm_num)
theorem B3982157 : Blo 1768085 3982157 := bbase (se 3 (by rfl) ⟨746654, by rfl⟩ : syracuseStep 3982157 = 1493309) (by norm_num)
theorem B2655053 : Blo 1768085 2655053 := bbase (se 3 (by rfl) ⟨497822, by rfl⟩ : syracuseStep 2655053 = 995645) (by norm_num)
theorem B2655077 : Blo 1768085 2655077 := bbase (se 4 (by rfl) ⟨248913, by rfl⟩ : syracuseStep 2655077 = 497827) (by norm_num)
theorem B2655101 : Blo 1768085 2655101 := bbase (se 3 (by rfl) ⟨497831, by rfl⟩ : syracuseStep 2655101 = 995663) (by norm_num)
theorem B5972885 : Blo 1768085 5972885 := bbase (se 6 (by rfl) ⟨139989, by rfl⟩ : syracuseStep 5972885 = 279979) (by norm_num)
theorem B3982229 : Blo 1768085 3982229 := bbase (se 6 (by rfl) ⟨93333, by rfl⟩ : syracuseStep 3982229 = 186667) (by norm_num)
theorem B2655125 : Blo 1768085 2655125 := bbase (se 6 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 2655125 = 124459) (by norm_num)
theorem B3777445 : Blo 1768085 3777445 := bbase (se 4 (by rfl) ⟨354135, by rfl⟩ : syracuseStep 3777445 = 708271) (by norm_num)
theorem B6718373 : Blo 1768085 6718373 := bbase (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) (by norm_num)
theorem B3982301 : Blo 1768085 3982301 := bbase (se 3 (by rfl) ⟨746681, by rfl⟩ : syracuseStep 3982301 = 1493363) (by norm_num)
theorem B3982373 : Blo 1768085 3982373 := bbase (se 4 (by rfl) ⟨373347, by rfl⟩ : syracuseStep 3982373 = 746695) (by norm_num)
theorem B3982445 : Blo 1768085 3982445 := bbase (se 3 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 3982445 = 1493417) (by norm_num)
theorem B3359893 : Blo 1768085 3359893 := bbase (se 6 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 3359893 = 157495) (by norm_num)
theorem B5670037 : Blo 1768085 5670037 := bbase (se 6 (by rfl) ⟨132891, by rfl⟩ : syracuseStep 5670037 = 265783) (by norm_num)
theorem B3982517 : Blo 1768085 3982517 := bbase (se 5 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 3982517 = 373361) (by norm_num)
theorem B7554293 : Blo 1768085 7554293 := bbase (se 5 (by rfl) ⟨354107, by rfl⟩ : syracuseStep 7554293 = 708215) (by norm_num)
theorem B2073853 : Blo 1768085 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B3982589 : Blo 1768085 3982589 := bbase (se 3 (by rfl) ⟨746735, by rfl⟩ : syracuseStep 3982589 = 1493471) (by norm_num)
theorem B3360037 : Blo 1768085 3360037 := bbase (se 4 (by rfl) ⟨315003, by rfl⟩ : syracuseStep 3360037 = 630007) (by norm_num)
theorem B16999733 : Blo 1768085 16999733 := bbase (se 5 (by rfl) ⟨796862, by rfl⟩ : syracuseStep 16999733 = 1593725) (by norm_num)
theorem B4252981 : Blo 1768085 4252981 := bbase (se 5 (by rfl) ⟨199358, by rfl⟩ : syracuseStep 4252981 = 398717) (by norm_num)
theorem B5973317 : Blo 1768085 5973317 := bbase (se 4 (by rfl) ⟨559998, by rfl⟩ : syracuseStep 5973317 = 1119997) (by norm_num)
theorem B3982661 : Blo 1768085 3982661 := bbase (se 4 (by rfl) ⟨373374, by rfl⟩ : syracuseStep 3982661 = 746749) (by norm_num)
theorem B8496485 : Blo 1768085 8496485 := bbase (se 4 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 8496485 = 1593091) (by norm_num)
theorem B2237797 : Blo 1768085 2237797 := bbase (se 4 (by rfl) ⟨209793, by rfl⟩ : syracuseStep 2237797 = 419587) (by norm_num)
theorem B3777941 : Blo 1768085 3777941 := bbase (se 6 (by rfl) ⟨88545, by rfl⟩ : syracuseStep 3777941 = 177091) (by norm_num)
theorem B5039509 : Blo 1768085 5039509 := bbase (se 6 (by rfl) ⟨118113, by rfl⟩ : syracuseStep 5039509 = 236227) (by norm_num)
theorem B2016685 : Blo 1768085 2016685 := bbase (se 3 (by rfl) ⟨378128, by rfl⟩ : syracuseStep 2016685 = 756257) (by norm_num)
theorem B3360197 : Blo 1768085 3360197 := bbase (se 4 (by rfl) ⟨315018, by rfl⟩ : syracuseStep 3360197 = 630037) (by norm_num)
theorem B11331029 : Blo 1768085 11331029 := bbase (se 7 (by rfl) ⟨132785, by rfl⟩ : syracuseStep 11331029 = 265571) (by norm_num)
theorem B2237969 : Blo 1768085 2237969 := bbase (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) (by norm_num)
theorem B8496677 : Blo 1768085 8496677 := bbase (se 4 (by rfl) ⟨796563, by rfl⟩ : syracuseStep 8496677 = 1593127) (by norm_num)
theorem B6809141 : Blo 1768085 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B2238025 : Blo 1768085 2238025 := bbase (se 2 (by rfl) ⟨839259, by rfl⟩ : syracuseStep 2238025 = 1678519) (by norm_num)
theorem B3360341 : Blo 1768085 3360341 := bbase (se 8 (by rfl) ⟨19689, by rfl⟩ : syracuseStep 3360341 = 39379) (by norm_num)
theorem B2238121 : Blo 1768085 2238121 := bbase (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) (by norm_num)
theorem B5973749 : Blo 1768085 5973749 := bbase (se 5 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 5973749 = 560039) (by norm_num)
theorem B2983709 : Blo 1768085 2983709 := bbase (se 3 (by rfl) ⟨559445, by rfl⟩ : syracuseStep 2983709 = 1118891) (by norm_num)
theorem B2238293 : Blo 1768085 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B9561941 : Blo 1768085 9561941 := bbase (se 9 (by rfl) ⟨28013, by rfl⟩ : syracuseStep 9561941 = 56027) (by norm_num)
theorem B2238349 : Blo 1768085 2238349 := bbase (se 3 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 2238349 = 839381) (by norm_num)
theorem B20703125 : Blo 1768085 20703125 := bbase (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) (by norm_num)
theorem B11495317 : Blo 1768085 11495317 := bbase (se 6 (by rfl) ⟨269421, by rfl⟩ : syracuseStep 11495317 = 538843) (by norm_num)
theorem B2983837 : Blo 1768085 2983837 := bbase (se 3 (by rfl) ⟨559469, by rfl⟩ : syracuseStep 2983837 = 1118939) (by norm_num)
theorem B8497061 : Blo 1768085 8497061 := bbase (se 4 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 8497061 = 1593199) (by norm_num)
theorem B8955845 : Blo 1768085 8955845 := bbase (se 4 (by rfl) ⟨839610, by rfl⟩ : syracuseStep 8955845 = 1679221) (by norm_num)
theorem B4032485 : Blo 1768085 4032485 := bbase (se 4 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 4032485 = 756091) (by norm_num)
theorem B2238445 : Blo 1768085 2238445 := bbase (se 3 (by rfl) ⟨419708, by rfl⟩ : syracuseStep 2238445 = 839417) (by norm_num)
theorem B2983925 : Blo 1768085 2983925 := bbase (se 5 (by rfl) ⟨139871, by rfl⟩ : syracuseStep 2983925 = 279743) (by norm_num)
theorem B6719557 : Blo 1768085 6719557 := bbase (se 4 (by rfl) ⟨629958, by rfl⟩ : syracuseStep 6719557 = 1259917) (by norm_num)
theorem B3188813 : Blo 1768085 3188813 := bbase (se 3 (by rfl) ⟨597902, by rfl⟩ : syracuseStep 3188813 = 1195805) (by norm_num)
theorem B2984053 : Blo 1768085 2984053 := bbase (se 5 (by rfl) ⟨139877, by rfl⟩ : syracuseStep 2984053 = 279755) (by norm_num)
theorem B2238617 : Blo 1768085 2238617 := bbase (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) (by norm_num)
theorem B2984141 : Blo 1768085 2984141 := bbase (se 3 (by rfl) ⟨559526, by rfl⟩ : syracuseStep 2984141 = 1119053) (by norm_num)
theorem B2689229 : Blo 1768085 2689229 := bbase (se 3 (by rfl) ⟨504230, by rfl⟩ : syracuseStep 2689229 = 1008461) (by norm_num)
theorem B2238673 : Blo 1768085 2238673 := bbase (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) (by norm_num)
theorem B2689253 : Blo 1768085 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B7555301 : Blo 1768085 7555301 := bbase (se 4 (by rfl) ⟨708309, by rfl⟩ : syracuseStep 7555301 = 1416619) (by norm_num)
theorem B3778829 : Blo 1768085 3778829 := bbase (se 3 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 3778829 = 1417061) (by norm_num)
theorem B2238769 : Blo 1768085 2238769 := bbase (se 2 (by rfl) ⟨839538, by rfl⟩ : syracuseStep 2238769 = 1679077) (by norm_num)
theorem B2984269 : Blo 1768085 2984269 := bbase (se 3 (by rfl) ⟨559550, by rfl⟩ : syracuseStep 2984269 = 1119101) (by norm_num)
theorem B6719861 : Blo 1768085 6719861 := bbase (se 5 (by rfl) ⟨314993, by rfl⟩ : syracuseStep 6719861 = 629987) (by norm_num)
theorem B3778949 : Blo 1768085 3778949 := bbase (se 4 (by rfl) ⟨354276, by rfl⟩ : syracuseStep 3778949 = 708553) (by norm_num)
theorem B8505749 : Blo 1768085 8505749 := bbase (se 6 (by rfl) ⟨199353, by rfl⟩ : syracuseStep 8505749 = 398707) (by norm_num)
theorem B2984357 : Blo 1768085 2984357 := bbase (se 4 (by rfl) ⟨279783, by rfl⟩ : syracuseStep 2984357 = 559567) (by norm_num)
theorem B8620453 : Blo 1768085 8620453 := bbase (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) (by norm_num)
theorem B2238941 : Blo 1768085 2238941 := bbase (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) (by norm_num)
theorem B7170565 : Blo 1768085 7170565 := bbase (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) (by norm_num)
theorem B2238997 : Blo 1768085 2238997 := bbase (se 6 (by rfl) ⟨52476, by rfl⟩ : syracuseStep 2238997 = 104953) (by norm_num)
theorem B2017813 : Blo 1768085 2017813 := bbase (se 6 (by rfl) ⟨47292, by rfl⟩ : syracuseStep 2017813 = 94585) (by norm_num)
theorem B2984485 : Blo 1768085 2984485 := bbase (se 4 (by rfl) ⟨279795, by rfl⟩ : syracuseStep 2984485 = 559591) (by norm_num)
theorem B3025493 : Blo 1768085 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B2239093 : Blo 1768085 2239093 := bbase (se 5 (by rfl) ⟨104957, by rfl⟩ : syracuseStep 2239093 = 209915) (by norm_num)
theorem B2984573 : Blo 1768085 2984573 := bbase (se 3 (by rfl) ⟨559607, by rfl⟩ : syracuseStep 2984573 = 1119215) (by norm_num)
theorem B4475533 : Blo 1768085 4475533 := bbase (se 3 (by rfl) ⟨839162, by rfl⟩ : syracuseStep 4475533 = 1678325) (by norm_num)
theorem B7170725 : Blo 1768085 7170725 := bbase (se 4 (by rfl) ⟨672255, by rfl⟩ : syracuseStep 7170725 = 1344511) (by norm_num)
theorem B2124457 : Blo 1768085 2124457 := bbase (se 2 (by rfl) ⟨796671, by rfl⟩ : syracuseStep 2124457 = 1593343) (by norm_num)
theorem B2517733 : Blo 1768085 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B4475645 : Blo 1768085 4475645 := bbase (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) (by norm_num)
theorem B2984701 : Blo 1768085 2984701 := bbase (se 3 (by rfl) ⟨559631, by rfl⟩ : syracuseStep 2984701 = 1119263) (by norm_num)
theorem B2239265 : Blo 1768085 2239265 := bbase (se 2 (by rfl) ⟨839724, by rfl⟩ : syracuseStep 2239265 = 1679449) (by norm_num)
theorem B2984789 : Blo 1768085 2984789 := bbase (se 9 (by rfl) ⟨8744, by rfl⟩ : syracuseStep 2984789 = 17489) (by norm_num)
theorem B2239321 : Blo 1768085 2239321 := bbase (se 2 (by rfl) ⟨839745, by rfl⟩ : syracuseStep 2239321 = 1679491) (by norm_num)
theorem B5376901 : Blo 1768085 5376901 := bbase (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) (by norm_num)
theorem B2239417 : Blo 1768085 2239417 := bbase (se 2 (by rfl) ⟨839781, by rfl⟩ : syracuseStep 2239417 = 1679563) (by norm_num)
theorem B4475837 : Blo 1768085 4475837 := bbase (se 3 (by rfl) ⟨839219, by rfl⟩ : syracuseStep 4475837 = 1678439) (by norm_num)
theorem B2984917 : Blo 1768085 2984917 := bbase (se 7 (by rfl) ⟨34979, by rfl⟩ : syracuseStep 2984917 = 69959) (by norm_num)
theorem B4090861 : Blo 1768085 4090861 := bbase (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) (by norm_num)
theorem B13618165 : Blo 1768085 13618165 := bbase (se 5 (by rfl) ⟨638351, by rfl⟩ : syracuseStep 13618165 = 1276703) (by norm_num)
theorem B3779581 : Blo 1768085 3779581 := bbase (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) (by norm_num)
theorem B2985005 : Blo 1768085 2985005 := bbase (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) (by norm_num)
theorem B2518069 : Blo 1768085 2518069 := bbase (se 5 (by rfl) ⟨118034, by rfl⟩ : syracuseStep 2518069 = 236069) (by norm_num)
theorem B4598869 : Blo 1768085 4598869 := bbase (se 8 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 4598869 = 53893) (by norm_num)
theorem B2239589 : Blo 1768085 2239589 := bbase (se 4 (by rfl) ⟨209961, by rfl⟩ : syracuseStep 2239589 = 419923) (by norm_num)
theorem B2239645 : Blo 1768085 2239645 := bbase (se 3 (by rfl) ⟨419933, by rfl⟩ : syracuseStep 2239645 = 839867) (by norm_num)
theorem B2985133 : Blo 1768085 2985133 := bbase (se 3 (by rfl) ⟨559712, by rfl⟩ : syracuseStep 2985133 = 1119425) (by norm_num)
theorem B8957141 : Blo 1768085 8957141 := bbase (se 7 (by rfl) ⟨104966, by rfl⟩ : syracuseStep 8957141 = 209933) (by norm_num)
theorem B2239741 : Blo 1768085 2239741 := bbase (se 3 (by rfl) ⟨419951, by rfl⟩ : syracuseStep 2239741 = 839903) (by norm_num)
theorem B2985221 : Blo 1768085 2985221 := bbase (se 4 (by rfl) ⟨279864, by rfl⟩ : syracuseStep 2985221 = 559729) (by norm_num)
theorem B2518285 : Blo 1768085 2518285 := bbase (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) (by norm_num)
theorem B10071317 : Blo 1768085 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B4476181 : Blo 1768085 4476181 := bbase (se 6 (by rfl) ⟨104910, by rfl⟩ : syracuseStep 4476181 = 209821) (by norm_num)
theorem B4476293 : Blo 1768085 4476293 := bbase (se 4 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 4476293 = 839305) (by norm_num)
theorem B2985349 : Blo 1768085 2985349 := bbase (se 4 (by rfl) ⟨279876, by rfl⟩ : syracuseStep 2985349 = 559753) (by norm_num)
theorem B2239913 : Blo 1768085 2239913 := bbase (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) (by norm_num)
theorem B2985437 : Blo 1768085 2985437 := bbase (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) (by norm_num)
theorem B2239969 : Blo 1768085 2239969 := bbase (se 2 (by rfl) ⟨839988, by rfl⟩ : syracuseStep 2239969 = 1679977) (by norm_num)
theorem B2125337 : Blo 1768085 2125337 := bbase (se 2 (by rfl) ⟨797001, by rfl⟩ : syracuseStep 2125337 = 1594003) (by norm_num)
theorem B2240065 : Blo 1768085 2240065 := bbase (se 2 (by rfl) ⟨840024, by rfl⟩ : syracuseStep 2240065 = 1680049) (by norm_num)
theorem B4476485 : Blo 1768085 4476485 := bbase (se 4 (by rfl) ⟨419670, by rfl⟩ : syracuseStep 4476485 = 839341) (by norm_num)
theorem B2985565 : Blo 1768085 2985565 := bbase (se 3 (by rfl) ⟨559793, by rfl⟩ : syracuseStep 2985565 = 1119587) (by norm_num)
theorem B2518661 : Blo 1768085 2518661 := bbase (se 4 (by rfl) ⟨236124, by rfl⟩ : syracuseStep 2518661 = 472249) (by norm_num)
theorem B2125453 : Blo 1768085 2125453 := bbase (se 3 (by rfl) ⟨398522, by rfl⟩ : syracuseStep 2125453 = 797045) (by norm_num)
theorem B2985653 : Blo 1768085 2985653 := bbase (se 5 (by rfl) ⟨139952, by rfl⟩ : syracuseStep 2985653 = 279905) (by norm_num)
theorem B2240237 : Blo 1768085 2240237 := bbase (se 3 (by rfl) ⟨420044, by rfl⟩ : syracuseStep 2240237 = 840089) (by norm_num)
theorem B4034317 : Blo 1768085 4034317 := bbase (se 3 (by rfl) ⟨756434, by rfl⟩ : syracuseStep 4034317 = 1512869) (by norm_num)
theorem B7171861 : Blo 1768085 7171861 := bbase (se 6 (by rfl) ⟨168090, by rfl⟩ : syracuseStep 7171861 = 336181) (by norm_num)
theorem B6377237 : Blo 1768085 6377237 := bbase (se 6 (by rfl) ⟨149466, by rfl⟩ : syracuseStep 6377237 = 298933) (by norm_num)
theorem B2985781 : Blo 1768085 2985781 := bbase (se 5 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 2985781 = 279917) (by norm_num)
theorem B2125649 : Blo 1768085 2125649 := bbase (se 2 (by rfl) ⟨797118, by rfl⟩ : syracuseStep 2125649 = 1594237) (by norm_num)
theorem B5967701 : Blo 1768085 5967701 := bbase (se 9 (by rfl) ⟨17483, by rfl⟩ : syracuseStep 5967701 = 34967) (by norm_num)
theorem B2985869 : Blo 1768085 2985869 := bbase (se 3 (by rfl) ⟨559850, by rfl⟩ : syracuseStep 2985869 = 1119701) (by norm_num)
theorem B4476829 : Blo 1768085 4476829 := bbase (se 3 (by rfl) ⟨839405, by rfl⟩ : syracuseStep 4476829 = 1678811) (by norm_num)
theorem B7557077 : Blo 1768085 7557077 := bbase (se 7 (by rfl) ⟨88559, by rfl⟩ : syracuseStep 7557077 = 177119) (by norm_num)
theorem B4476941 : Blo 1768085 4476941 := bbase (se 3 (by rfl) ⟨839426, by rfl⟩ : syracuseStep 4476941 = 1678853) (by norm_num)
theorem B2985997 : Blo 1768085 2985997 := bbase (se 3 (by rfl) ⟨559874, by rfl⟩ : syracuseStep 2985997 = 1119749) (by norm_num)
theorem B5378069 : Blo 1768085 5378069 := bbase (se 6 (by rfl) ⟨126048, by rfl⟩ : syracuseStep 5378069 = 252097) (by norm_num)
theorem B6377525 : Blo 1768085 6377525 := bbase (se 5 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 6377525 = 597893) (by norm_num)
theorem B1888321 : Blo 1768085 1888321 := bbase (se 2 (by rfl) ⟨708120, by rfl⟩ : syracuseStep 1888321 = 1416241) (by norm_num)
theorem B2986085 : Blo 1768085 2986085 := bbase (se 4 (by rfl) ⟨279945, by rfl⟩ : syracuseStep 2986085 = 559891) (by norm_num)
theorem B1888381 : Blo 1768085 1888381 := bbase (se 3 (by rfl) ⟨354071, by rfl⟩ : syracuseStep 1888381 = 708143) (by norm_num)
theorem B28692629 : Blo 1768085 28692629 := bbase (se 6 (by rfl) ⟨672483, by rfl⟩ : syracuseStep 28692629 = 1344967) (by norm_num)
theorem B6377669 : Blo 1768085 6377669 := bbase (se 4 (by rfl) ⟨597906, by rfl⟩ : syracuseStep 6377669 = 1195813) (by norm_num)
theorem B4477133 : Blo 1768085 4477133 := bbase (se 3 (by rfl) ⟨839462, by rfl⟩ : syracuseStep 4477133 = 1678925) (by norm_num)
theorem B2986213 : Blo 1768085 2986213 := bbase (se 4 (by rfl) ⟨279957, by rfl⟩ : syracuseStep 2986213 = 559915) (by norm_num)
theorem B5968133 : Blo 1768085 5968133 := bbase (se 4 (by rfl) ⟨559512, by rfl⟩ : syracuseStep 5968133 = 1119025) (by norm_num)
theorem B2986301 : Blo 1768085 2986301 := bbase (se 3 (by rfl) ⟨559931, by rfl⟩ : syracuseStep 2986301 = 1119863) (by norm_num)
theorem B2126197 : Blo 1768085 2126197 := bbase (se 5 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 2126197 = 199331) (by norm_num)
theorem B1888697 : Blo 1768085 1888697 := bbase (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) (by norm_num)
theorem B2986429 : Blo 1768085 2986429 := bbase (se 3 (by rfl) ⟨559955, by rfl⟩ : syracuseStep 2986429 = 1119911) (by norm_num)
theorem B8958437 : Blo 1768085 8958437 := bbase (se 4 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 8958437 = 1679707) (by norm_num)
theorem B2126341 : Blo 1768085 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B2986517 : Blo 1768085 2986517 := bbase (se 6 (by rfl) ⟨69996, by rfl⟩ : syracuseStep 2986517 = 139993) (by norm_num)
theorem B4477477 : Blo 1768085 4477477 := bbase (se 4 (by rfl) ⟨419763, by rfl⟩ : syracuseStep 4477477 = 839527) (by norm_num)
theorem B4477589 : Blo 1768085 4477589 := bbase (se 6 (by rfl) ⟨104943, by rfl⟩ : syracuseStep 4477589 = 209887) (by norm_num)
theorem B2986645 : Blo 1768085 2986645 := bbase (se 6 (by rfl) ⟨69999, by rfl⟩ : syracuseStep 2986645 = 139999) (by norm_num)
theorem B5968565 : Blo 1768085 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B2986733 : Blo 1768085 2986733 := bbase (se 3 (by rfl) ⟨560012, by rfl⟩ : syracuseStep 2986733 = 1120025) (by norm_num)
theorem B6714197 : Blo 1768085 6714197 := bbase (se 9 (by rfl) ⟨19670, by rfl⟩ : syracuseStep 6714197 = 39341) (by norm_num)
theorem B4780885 : Blo 1768085 4780885 := bbase (se 9 (by rfl) ⟨14006, by rfl⟩ : syracuseStep 4780885 = 28013) (by norm_num)
theorem B4477781 : Blo 1768085 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B3232613 : Blo 1768085 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B2986861 : Blo 1768085 2986861 := bbase (se 3 (by rfl) ⟨560036, by rfl⟩ : syracuseStep 2986861 = 1120073) (by norm_num)
theorem B1889141 : Blo 1768085 1889141 := bbase (se 5 (by rfl) ⟨88553, by rfl⟩ : syracuseStep 1889141 = 177107) (by norm_num)
theorem B4248445 : Blo 1768085 4248445 := bbase (se 3 (by rfl) ⟨796583, by rfl⟩ : syracuseStep 4248445 = 1593167) (by norm_num)
theorem B1889201 : Blo 1768085 1889201 := bbase (se 2 (by rfl) ⟨708450, by rfl⟩ : syracuseStep 1889201 = 1416901) (by norm_num)
theorem B2986949 : Blo 1768085 2986949 := bbase (se 4 (by rfl) ⟨280026, by rfl⟩ : syracuseStep 2986949 = 560053) (by norm_num)
theorem B3978197 : Blo 1768085 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B2520085 : Blo 1768085 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B3978269 : Blo 1768085 3978269 := bbase (se 3 (by rfl) ⟨745925, by rfl⟩ : syracuseStep 3978269 = 1491851) (by norm_num)
theorem B1889329 : Blo 1768085 1889329 := bbase (se 2 (by rfl) ⟨708498, by rfl⟩ : syracuseStep 1889329 = 1416997) (by norm_num)
theorem B3978341 : Blo 1768085 3978341 := bbase (se 4 (by rfl) ⟨372969, by rfl⟩ : syracuseStep 3978341 = 745939) (by norm_num)
theorem B5968997 : Blo 1768085 5968997 := bbase (se 4 (by rfl) ⟨559593, by rfl⟩ : syracuseStep 5968997 = 1119187) (by norm_num)
theorem B6714485 : Blo 1768085 6714485 := bbase (se 5 (by rfl) ⟨314741, by rfl⟩ : syracuseStep 6714485 = 629483) (by norm_num)
theorem B5665925 : Blo 1768085 5665925 := bbase (se 4 (by rfl) ⟨531180, by rfl⟩ : syracuseStep 5665925 = 1062361) (by norm_num)
theorem B3978413 : Blo 1768085 3978413 := bbase (se 3 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 3978413 = 1491905) (by norm_num)
theorem B4478125 : Blo 1768085 4478125 := bbase (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) (by norm_num)
theorem B3978485 : Blo 1768085 3978485 := bbase (se 5 (by rfl) ⟨186491, by rfl⟩ : syracuseStep 3978485 = 372983) (by norm_num)
theorem B4478237 : Blo 1768085 4478237 := bbase (se 3 (by rfl) ⟨839669, by rfl⟩ : syracuseStep 4478237 = 1679339) (by norm_num)
theorem B3978557 : Blo 1768085 3978557 := bbase (se 3 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 3978557 = 1491959) (by norm_num)
theorem B3978629 : Blo 1768085 3978629 := bbase (se 4 (by rfl) ⟨372996, by rfl⟩ : syracuseStep 3978629 = 745993) (by norm_num)
theorem B13620629 : Blo 1768085 13620629 := bbase (se 6 (by rfl) ⟨319233, by rfl⟩ : syracuseStep 13620629 = 638467) (by norm_num)
theorem B2045345 : Blo 1768085 2045345 := bbase (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) (by norm_num)
theorem B3978701 : Blo 1768085 3978701 := bbase (se 3 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 3978701 = 1492013) (by norm_num)
theorem B3585493 : Blo 1768085 3585493 := bbase (se 7 (by rfl) ⟨42017, by rfl⟩ : syracuseStep 3585493 = 84035) (by norm_num)
theorem B4478429 : Blo 1768085 4478429 := bbase (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) (by norm_num)
theorem B4249061 : Blo 1768085 4249061 := bbase (se 4 (by rfl) ⟨398349, by rfl⟩ : syracuseStep 4249061 = 796699) (by norm_num)
theorem B1889773 : Blo 1768085 1889773 := bbase (se 3 (by rfl) ⟨354332, by rfl⟩ : syracuseStep 1889773 = 708665) (by norm_num)
theorem B3585541 : Blo 1768085 3585541 := bbase (se 4 (by rfl) ⟨336144, by rfl⟩ : syracuseStep 3585541 = 672289) (by norm_num)
theorem B3978773 : Blo 1768085 3978773 := bbase (se 6 (by rfl) ⟨93252, by rfl⟩ : syracuseStep 3978773 = 186505) (by norm_num)
theorem B5969429 : Blo 1768085 5969429 := bbase (se 6 (by rfl) ⟨139908, by rfl⟩ : syracuseStep 5969429 = 279817) (by norm_num)
theorem B10909205 : Blo 1768085 10909205 := bbase (se 6 (by rfl) ⟨255684, by rfl⟩ : syracuseStep 10909205 = 511369) (by norm_num)
theorem B3978845 : Blo 1768085 3978845 := bbase (se 3 (by rfl) ⟨746033, by rfl⟩ : syracuseStep 3978845 = 1492067) (by norm_num)
theorem B1889893 : Blo 1768085 1889893 := bbase (se 4 (by rfl) ⟨177177, by rfl⟩ : syracuseStep 1889893 = 354355) (by norm_num)
theorem B9082469 : Blo 1768085 9082469 := bbase (se 4 (by rfl) ⟨851481, by rfl⟩ : syracuseStep 9082469 = 1702963) (by norm_num)
theorem B4781717 : Blo 1768085 4781717 := bbase (se 6 (by rfl) ⟨112071, by rfl⟩ : syracuseStep 4781717 = 224143) (by norm_num)
theorem B3978917 : Blo 1768085 3978917 := bbase (se 4 (by rfl) ⟨373023, by rfl⟩ : syracuseStep 3978917 = 746047) (by norm_num)
theorem B3978989 : Blo 1768085 3978989 := bbase (se 3 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 3978989 = 1492121) (by norm_num)
theorem B8959733 : Blo 1768085 8959733 := bbase (se 5 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 8959733 = 839975) (by norm_num)
theorem B3979061 : Blo 1768085 3979061 := bbase (se 5 (by rfl) ⟨186518, by rfl⟩ : syracuseStep 3979061 = 373037) (by norm_num)
theorem B4478773 : Blo 1768085 4478773 := bbase (se 5 (by rfl) ⟨209942, by rfl⟩ : syracuseStep 4478773 = 419885) (by norm_num)
theorem B1890145 : Blo 1768085 1890145 := bbase (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) (by norm_num)
theorem B1890149 : Blo 1768085 1890149 := bbase (se 4 (by rfl) ⟨177201, by rfl⟩ : syracuseStep 1890149 = 354403) (by norm_num)
theorem B15734645 : Blo 1768085 15734645 := bbase (se 5 (by rfl) ⟨737561, by rfl⟩ : syracuseStep 15734645 = 1475123) (by norm_num)
theorem B3979133 : Blo 1768085 3979133 := bbase (se 3 (by rfl) ⟨746087, by rfl⟩ : syracuseStep 3979133 = 1492175) (by norm_num)
theorem B4478885 : Blo 1768085 4478885 := bbase (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) (by norm_num)
theorem B3979205 : Blo 1768085 3979205 := bbase (se 4 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 3979205 = 746101) (by norm_num)
theorem B5969861 : Blo 1768085 5969861 := bbase (se 4 (by rfl) ⟨559674, by rfl⟩ : syracuseStep 5969861 = 1119349) (by norm_num)
theorem B2652149 : Blo 1768085 2652149 := bbase (se 5 (by rfl) ⟨124319, by rfl⟩ : syracuseStep 2652149 = 248639) (by norm_num)
theorem B2652173 : Blo 1768085 2652173 := bbase (se 3 (by rfl) ⟨497282, by rfl⟩ : syracuseStep 2652173 = 994565) (by norm_num)
theorem B3979277 : Blo 1768085 3979277 := bbase (se 3 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 3979277 = 1492229) (by norm_num)
theorem B2652197 : Blo 1768085 2652197 := bbase (se 4 (by rfl) ⟨248643, by rfl⟩ : syracuseStep 2652197 = 497287) (by norm_num)
theorem B5036069 : Blo 1768085 5036069 := bbase (se 4 (by rfl) ⟨472131, by rfl⟩ : syracuseStep 5036069 = 944263) (by norm_num)
theorem B2652221 : Blo 1768085 2652221 := bbase (se 3 (by rfl) ⟨497291, by rfl⟩ : syracuseStep 2652221 = 994583) (by norm_num)
theorem B3356741 : Blo 1768085 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B2652245 : Blo 1768085 2652245 := bbase (se 8 (by rfl) ⟨15540, by rfl⟩ : syracuseStep 2652245 = 31081) (by norm_num)
theorem B3979349 : Blo 1768085 3979349 := bbase (se 8 (by rfl) ⟨23316, by rfl⟩ : syracuseStep 3979349 = 46633) (by norm_num)
theorem B4479077 : Blo 1768085 4479077 := bbase (se 4 (by rfl) ⟨419913, by rfl⟩ : syracuseStep 4479077 = 839827) (by norm_num)
theorem B2652269 : Blo 1768085 2652269 := bbase (se 3 (by rfl) ⟨497300, by rfl⟩ : syracuseStep 2652269 = 994601) (by norm_num)
theorem B8501365 : Blo 1768085 8501365 := bbase (se 5 (by rfl) ⟨398501, by rfl⟩ : syracuseStep 8501365 = 797003) (by norm_num)
theorem B2652293 : Blo 1768085 2652293 := bbase (se 4 (by rfl) ⟨248652, by rfl⟩ : syracuseStep 2652293 = 497305) (by norm_num)
theorem B8951957 : Blo 1768085 8951957 := bbase (se 6 (by rfl) ⟨209811, by rfl⟩ : syracuseStep 8951957 = 419623) (by norm_num)
theorem B2652317 : Blo 1768085 2652317 := bbase (se 3 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 2652317 = 994619) (by norm_num)
theorem B3979421 : Blo 1768085 3979421 := bbase (se 3 (by rfl) ⟨746141, by rfl⟩ : syracuseStep 3979421 = 1492283) (by norm_num)
theorem B2652341 : Blo 1768085 2652341 := bbase (se 5 (by rfl) ⟨124328, by rfl⟩ : syracuseStep 2652341 = 248657) (by norm_num)
theorem B5667013 : Blo 1768085 5667013 := bbase (se 4 (by rfl) ⟨531282, by rfl⟩ : syracuseStep 5667013 = 1062565) (by norm_num)
theorem B2652365 : Blo 1768085 2652365 := bbase (se 3 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 2652365 = 994637) (by norm_num)
theorem B3356893 : Blo 1768085 3356893 := bbase (se 3 (by rfl) ⟨629417, by rfl⟩ : syracuseStep 3356893 = 1258835) (by norm_num)
theorem B2652389 : Blo 1768085 2652389 := bbase (se 4 (by rfl) ⟨248661, by rfl⟩ : syracuseStep 2652389 = 497323) (by norm_num)
theorem B3979493 : Blo 1768085 3979493 := bbase (se 4 (by rfl) ⟨373077, by rfl⟩ : syracuseStep 3979493 = 746155) (by norm_num)
theorem B4249837 : Blo 1768085 4249837 := bbase (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) (by norm_num)
theorem B2652413 : Blo 1768085 2652413 := bbase (se 3 (by rfl) ⟨497327, by rfl⟩ : syracuseStep 2652413 = 994655) (by norm_num)
theorem B2652437 : Blo 1768085 2652437 := bbase (se 6 (by rfl) ⟨62166, by rfl⟩ : syracuseStep 2652437 = 124333) (by norm_num)
theorem B2832661 : Blo 1768085 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B6715669 : Blo 1768085 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B13441301 : Blo 1768085 13441301 := bbase (se 6 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 13441301 = 630061) (by norm_num)
theorem B2652461 : Blo 1768085 2652461 := bbase (se 3 (by rfl) ⟨497336, by rfl⟩ : syracuseStep 2652461 = 994673) (by norm_num)
theorem B2390317 : Blo 1768085 2390317 := bbase (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) (by norm_num)
theorem B3979565 : Blo 1768085 3979565 := bbase (se 3 (by rfl) ⟨746168, by rfl⟩ : syracuseStep 3979565 = 1492337) (by norm_num)
theorem B2652485 : Blo 1768085 2652485 := bbase (se 4 (by rfl) ⟨248670, by rfl⟩ : syracuseStep 2652485 = 497341) (by norm_num)
theorem B1792345 : Blo 1768085 1792345 := bbase (se 2 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 1792345 = 1344259) (by norm_num)
theorem B2652509 : Blo 1768085 2652509 := bbase (se 3 (by rfl) ⟨497345, by rfl⟩ : syracuseStep 2652509 = 994691) (by norm_num)
theorem B2652533 : Blo 1768085 2652533 := bbase (se 5 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 2652533 = 248675) (by norm_num)
theorem B3979637 : Blo 1768085 3979637 := bbase (se 5 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 3979637 = 373091) (by norm_num)
theorem B5970293 : Blo 1768085 5970293 := bbase (se 5 (by rfl) ⟨279857, by rfl⟩ : syracuseStep 5970293 = 559715) (by norm_num)
theorem B2652557 : Blo 1768085 2652557 := bbase (se 3 (by rfl) ⟨497354, by rfl⟩ : syracuseStep 2652557 = 994709) (by norm_num)
theorem B2652581 : Blo 1768085 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B2652605 : Blo 1768085 2652605 := bbase (se 3 (by rfl) ⟨497363, by rfl⟩ : syracuseStep 2652605 = 994727) (by norm_num)
theorem B3979709 : Blo 1768085 3979709 := bbase (se 3 (by rfl) ⟨746195, by rfl⟩ : syracuseStep 3979709 = 1492391) (by norm_num)
theorem B4479421 : Blo 1768085 4479421 := bbase (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) (by norm_num)
theorem B2652629 : Blo 1768085 2652629 := bbase (se 7 (by rfl) ⟨31085, by rfl⟩ : syracuseStep 2652629 = 62171) (by norm_num)
theorem B2652653 : Blo 1768085 2652653 := bbase (se 3 (by rfl) ⟨497372, by rfl⟩ : syracuseStep 2652653 = 994745) (by norm_num)
theorem B2726389 : Blo 1768085 2726389 := bbase (se 5 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 2726389 = 255599) (by norm_num)
theorem B3635701 : Blo 1768085 3635701 := bbase (se 5 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 3635701 = 340847) (by norm_num)
theorem B1989121 : Blo 1768085 1989121 := bbase (se 2 (by rfl) ⟨745920, by rfl⟩ : syracuseStep 1989121 = 1491841) (by norm_num)
theorem B2652677 : Blo 1768085 2652677 := bbase (se 4 (by rfl) ⟨248688, by rfl⟩ : syracuseStep 2652677 = 497377) (by norm_num)
theorem B3979781 : Blo 1768085 3979781 := bbase (se 4 (by rfl) ⟨373104, by rfl⟩ : syracuseStep 3979781 = 746209) (by norm_num)
theorem B3357197 : Blo 1768085 3357197 := bbase (se 3 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 3357197 = 1258949) (by norm_num)
theorem B2652701 : Blo 1768085 2652701 := bbase (se 3 (by rfl) ⟨497381, by rfl⟩ : syracuseStep 2652701 = 994763) (by norm_num)
theorem B1989157 : Blo 1768085 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B4479533 : Blo 1768085 4479533 := bbase (se 3 (by rfl) ⟨839912, by rfl⟩ : syracuseStep 4479533 = 1679825) (by norm_num)
theorem B2652725 : Blo 1768085 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B6715973 : Blo 1768085 6715973 := bbase (se 4 (by rfl) ⟨629622, by rfl⟩ : syracuseStep 6715973 = 1259245) (by norm_num)
theorem B1989193 : Blo 1768085 1989193 := bbase (se 2 (by rfl) ⟨745947, by rfl⟩ : syracuseStep 1989193 = 1491895) (by norm_num)
theorem B2652749 : Blo 1768085 2652749 := bbase (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) (by norm_num)
theorem B3979853 : Blo 1768085 3979853 := bbase (se 3 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 3979853 = 1492445) (by norm_num)
theorem B2652773 : Blo 1768085 2652773 := bbase (se 4 (by rfl) ⟨248697, by rfl⟩ : syracuseStep 2652773 = 497395) (by norm_num)
theorem B1989229 : Blo 1768085 1989229 := bbase (se 3 (by rfl) ⟨372980, by rfl⟩ : syracuseStep 1989229 = 745961) (by norm_num)
theorem B2652797 : Blo 1768085 2652797 := bbase (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) (by norm_num)
theorem B1989265 : Blo 1768085 1989265 := bbase (se 2 (by rfl) ⟨745974, by rfl⟩ : syracuseStep 1989265 = 1491949) (by norm_num)
theorem B2652821 : Blo 1768085 2652821 := bbase (se 6 (by rfl) ⟨62175, by rfl⟩ : syracuseStep 2652821 = 124351) (by norm_num)
theorem B3979925 : Blo 1768085 3979925 := bbase (se 6 (by rfl) ⟨93279, by rfl⟩ : syracuseStep 3979925 = 186559) (by norm_num)
theorem B8182421 : Blo 1768085 8182421 := bbase (se 6 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 8182421 = 383551) (by norm_num)
theorem B2652845 : Blo 1768085 2652845 := bbase (se 3 (by rfl) ⟨497408, by rfl⟩ : syracuseStep 2652845 = 994817) (by norm_num)
theorem B1989301 : Blo 1768085 1989301 := bbase (se 5 (by rfl) ⟨93248, by rfl⟩ : syracuseStep 1989301 = 186497) (by norm_num)
theorem B13433525 : Blo 1768085 13433525 := bbase (se 5 (by rfl) ⟨629696, by rfl⟩ : syracuseStep 13433525 = 1259393) (by norm_num)
theorem B2652869 : Blo 1768085 2652869 := bbase (se 4 (by rfl) ⟨248706, by rfl⟩ : syracuseStep 2652869 = 497413) (by norm_num)
theorem B1989337 : Blo 1768085 1989337 := bbase (se 2 (by rfl) ⟨746001, by rfl⟩ : syracuseStep 1989337 = 1492003) (by norm_num)
theorem B2652893 : Blo 1768085 2652893 := bbase (se 3 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 2652893 = 994835) (by norm_num)
theorem B3979997 : Blo 1768085 3979997 := bbase (se 3 (by rfl) ⟨746249, by rfl⟩ : syracuseStep 3979997 = 1492499) (by norm_num)
theorem B2652917 : Blo 1768085 2652917 := bbase (se 5 (by rfl) ⟨124355, by rfl⟩ : syracuseStep 2652917 = 248711) (by norm_num)
theorem B4479725 : Blo 1768085 4479725 := bbase (se 3 (by rfl) ⟨839948, by rfl⟩ : syracuseStep 4479725 = 1679897) (by norm_num)
theorem B2153209 : Blo 1768085 2153209 := bbase (se 2 (by rfl) ⟨807453, by rfl⟩ : syracuseStep 2153209 = 1614907) (by norm_num)
theorem B1989373 : Blo 1768085 1989373 := bbase (se 3 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 1989373 = 746015) (by norm_num)
theorem B2652941 : Blo 1768085 2652941 := bbase (se 3 (by rfl) ⟨497426, by rfl⟩ : syracuseStep 2652941 = 994853) (by norm_num)
theorem B15104789 : Blo 1768085 15104789 := bbase (se 6 (by rfl) ⟨354018, by rfl⟩ : syracuseStep 15104789 = 708037) (by norm_num)
theorem B1989409 : Blo 1768085 1989409 := bbase (se 2 (by rfl) ⟨746028, by rfl⟩ : syracuseStep 1989409 = 1492057) (by norm_num)
theorem B2652965 : Blo 1768085 2652965 := bbase (se 4 (by rfl) ⟨248715, by rfl⟩ : syracuseStep 2652965 = 497431) (by norm_num)
theorem B3980069 : Blo 1768085 3980069 := bbase (se 4 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 3980069 = 746263) (by norm_num)
theorem B5970725 : Blo 1768085 5970725 := bbase (se 4 (by rfl) ⟨559755, by rfl⟩ : syracuseStep 5970725 = 1119511) (by norm_num)
theorem B2652989 : Blo 1768085 2652989 := bbase (se 3 (by rfl) ⟨497435, by rfl⟩ : syracuseStep 2652989 = 994871) (by norm_num)
theorem B1989445 : Blo 1768085 1989445 := bbase (se 4 (by rfl) ⟨186510, by rfl⟩ : syracuseStep 1989445 = 373021) (by norm_num)
theorem B2653013 : Blo 1768085 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B1989481 : Blo 1768085 1989481 := bbase (se 2 (by rfl) ⟨746055, by rfl⟩ : syracuseStep 1989481 = 1492111) (by norm_num)
theorem B2653037 : Blo 1768085 2653037 := bbase (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) (by norm_num)
theorem B3980141 : Blo 1768085 3980141 := bbase (se 3 (by rfl) ⟨746276, by rfl⟩ : syracuseStep 3980141 = 1492553) (by norm_num)
theorem B2653061 : Blo 1768085 2653061 := bbase (se 4 (by rfl) ⟨248724, by rfl⟩ : syracuseStep 2653061 = 497449) (by norm_num)
theorem B1989517 : Blo 1768085 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B2653085 : Blo 1768085 2653085 := bbase (se 3 (by rfl) ⟨497453, by rfl⟩ : syracuseStep 2653085 = 994907) (by norm_num)
theorem B1989553 : Blo 1768085 1989553 := bbase (se 2 (by rfl) ⟨746082, by rfl⟩ : syracuseStep 1989553 = 1492165) (by norm_num)
theorem B2653109 : Blo 1768085 2653109 := bbase (se 5 (by rfl) ⟨124364, by rfl⟩ : syracuseStep 2653109 = 248729) (by norm_num)
theorem B3980213 : Blo 1768085 3980213 := bbase (se 5 (by rfl) ⟨186572, by rfl⟩ : syracuseStep 3980213 = 373145) (by norm_num)
theorem B4250549 : Blo 1768085 4250549 := bbase (se 5 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 4250549 = 398489) (by norm_num)
theorem B2653133 : Blo 1768085 2653133 := bbase (se 3 (by rfl) ⟨497462, by rfl⟩ : syracuseStep 2653133 = 994925) (by norm_num)
theorem B1989589 : Blo 1768085 1989589 := bbase (se 7 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 1989589 = 46631) (by norm_num)
theorem B2833373 : Blo 1768085 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B2653157 : Blo 1768085 2653157 := bbase (se 4 (by rfl) ⟨248733, by rfl⟩ : syracuseStep 2653157 = 497467) (by norm_num)
theorem B1989625 : Blo 1768085 1989625 := bbase (se 2 (by rfl) ⟨746109, by rfl⟩ : syracuseStep 1989625 = 1492219) (by norm_num)
theorem B2653181 : Blo 1768085 2653181 := bbase (se 3 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 2653181 = 994943) (by norm_num)
theorem B3980285 : Blo 1768085 3980285 := bbase (se 3 (by rfl) ⟨746303, by rfl⟩ : syracuseStep 3980285 = 1492607) (by norm_num)
theorem B8961029 : Blo 1768085 8961029 := bbase (se 4 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 8961029 = 1680193) (by norm_num)
theorem B2653205 : Blo 1768085 2653205 := bbase (se 6 (by rfl) ⟨62184, by rfl⟩ : syracuseStep 2653205 = 124369) (by norm_num)
theorem B1989661 : Blo 1768085 1989661 := bbase (se 3 (by rfl) ⟨373061, by rfl⟩ : syracuseStep 1989661 = 746123) (by norm_num)
theorem B2653229 : Blo 1768085 2653229 := bbase (se 3 (by rfl) ⟨497480, by rfl⟩ : syracuseStep 2653229 = 994961) (by norm_num)
theorem B1866817 : Blo 1768085 1866817 := bbase (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) (by norm_num)
theorem B1989697 : Blo 1768085 1989697 := bbase (se 2 (by rfl) ⟨746136, by rfl⟩ : syracuseStep 1989697 = 1492273) (by norm_num)
theorem B2653253 : Blo 1768085 2653253 := bbase (se 4 (by rfl) ⟨248742, by rfl⟩ : syracuseStep 2653253 = 497485) (by norm_num)
theorem B3980357 : Blo 1768085 3980357 := bbase (se 4 (by rfl) ⟨373158, by rfl⟩ : syracuseStep 3980357 = 746317) (by norm_num)
theorem B4480069 : Blo 1768085 4480069 := bbase (se 4 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 4480069 = 840013) (by norm_num)
theorem B2653277 : Blo 1768085 2653277 := bbase (se 3 (by rfl) ⟨497489, by rfl⟩ : syracuseStep 2653277 = 994979) (by norm_num)
theorem B1989733 : Blo 1768085 1989733 := bbase (se 4 (by rfl) ⟨186537, by rfl⟩ : syracuseStep 1989733 = 373075) (by norm_num)
theorem B2653301 : Blo 1768085 2653301 := bbase (se 5 (by rfl) ⟨124373, by rfl⟩ : syracuseStep 2653301 = 248747) (by norm_num)
theorem B1989769 : Blo 1768085 1989769 := bbase (se 2 (by rfl) ⟨746163, by rfl⟩ : syracuseStep 1989769 = 1492327) (by norm_num)
theorem B2653325 : Blo 1768085 2653325 := bbase (se 3 (by rfl) ⟨497498, by rfl⟩ : syracuseStep 2653325 = 994997) (by norm_num)
theorem B3980429 : Blo 1768085 3980429 := bbase (se 3 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 3980429 = 1492661) (by norm_num)
theorem B2653349 : Blo 1768085 2653349 := bbase (se 4 (by rfl) ⟨248751, by rfl⟩ : syracuseStep 2653349 = 497503) (by norm_num)
theorem B1989805 : Blo 1768085 1989805 := bbase (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) (by norm_num)
theorem B4480181 : Blo 1768085 4480181 := bbase (se 5 (by rfl) ⟨210008, by rfl⟩ : syracuseStep 4480181 = 420017) (by norm_num)
theorem B2653373 : Blo 1768085 2653373 := bbase (se 3 (by rfl) ⟨497507, by rfl⟩ : syracuseStep 2653373 = 995015) (by norm_num)
theorem B1989841 : Blo 1768085 1989841 := bbase (se 2 (by rfl) ⟨746190, by rfl⟩ : syracuseStep 1989841 = 1492381) (by norm_num)
theorem B2653397 : Blo 1768085 2653397 := bbase (se 7 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 2653397 = 62189) (by norm_num)
theorem B3980501 : Blo 1768085 3980501 := bbase (se 7 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 3980501 = 93293) (by norm_num)
theorem B5971157 : Blo 1768085 5971157 := bbase (se 7 (by rfl) ⟨69974, by rfl⟩ : syracuseStep 5971157 = 139949) (by norm_num)
theorem B3587285 : Blo 1768085 3587285 := bbase (se 7 (by rfl) ⟨42038, by rfl⟩ : syracuseStep 3587285 = 84077) (by norm_num)
theorem B14351573 : Blo 1768085 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B2653421 : Blo 1768085 2653421 := bbase (se 3 (by rfl) ⟨497516, by rfl⟩ : syracuseStep 2653421 = 995033) (by norm_num)
theorem B1989877 : Blo 1768085 1989877 := bbase (se 5 (by rfl) ⟨93275, by rfl⟩ : syracuseStep 1989877 = 186551) (by norm_num)
theorem B3357949 : Blo 1768085 3357949 := bbase (se 3 (by rfl) ⟨629615, by rfl⟩ : syracuseStep 3357949 = 1259231) (by norm_num)
theorem B2653445 : Blo 1768085 2653445 := bbase (se 4 (by rfl) ⟨248760, by rfl⟩ : syracuseStep 2653445 = 497521) (by norm_num)
theorem B7175429 : Blo 1768085 7175429 := bbase (se 4 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 7175429 = 1345393) (by norm_num)
theorem B20159765 : Blo 1768085 20159765 := bbase (se 6 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 20159765 = 944989) (by norm_num)
theorem B1989913 : Blo 1768085 1989913 := bbase (se 2 (by rfl) ⟨746217, by rfl⟩ : syracuseStep 1989913 = 1492435) (by norm_num)
theorem B2653469 : Blo 1768085 2653469 := bbase (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) (by norm_num)
theorem B3980573 : Blo 1768085 3980573 := bbase (se 3 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 3980573 = 1492715) (by norm_num)
theorem B2653493 : Blo 1768085 2653493 := bbase (se 5 (by rfl) ⟨124382, by rfl⟩ : syracuseStep 2653493 = 248765) (by norm_num)
theorem B1989949 : Blo 1768085 1989949 := bbase (se 3 (by rfl) ⟨373115, by rfl⟩ : syracuseStep 1989949 = 746231) (by norm_num)
theorem B2653517 : Blo 1768085 2653517 := bbase (se 3 (by rfl) ⟨497534, by rfl⟩ : syracuseStep 2653517 = 995069) (by norm_num)
theorem B5668181 : Blo 1768085 5668181 := bbase (se 11 (by rfl) ⟨4151, by rfl⟩ : syracuseStep 5668181 = 8303) (by norm_num)
theorem B1989985 : Blo 1768085 1989985 := bbase (se 2 (by rfl) ⟨746244, by rfl⟩ : syracuseStep 1989985 = 1492489) (by norm_num)
theorem B2653541 : Blo 1768085 2653541 := bbase (se 4 (by rfl) ⟨248769, by rfl⟩ : syracuseStep 2653541 = 497539) (by norm_num)
theorem B3980645 : Blo 1768085 3980645 := bbase (se 4 (by rfl) ⟨373185, by rfl⟩ : syracuseStep 3980645 = 746371) (by norm_num)
theorem B4480373 : Blo 1768085 4480373 := bbase (se 5 (by rfl) ⟨210017, by rfl⟩ : syracuseStep 4480373 = 420035) (by norm_num)
theorem B2653565 : Blo 1768085 2653565 := bbase (se 3 (by rfl) ⟨497543, by rfl⟩ : syracuseStep 2653565 = 995087) (by norm_num)
theorem B1990021 : Blo 1768085 1990021 := bbase (se 4 (by rfl) ⟨186564, by rfl⟩ : syracuseStep 1990021 = 373129) (by norm_num)
theorem B3358093 : Blo 1768085 3358093 := bbase (se 3 (by rfl) ⟨629642, by rfl⟩ : syracuseStep 3358093 = 1259285) (by norm_num)
theorem B2653589 : Blo 1768085 2653589 := bbase (se 6 (by rfl) ⟨62193, by rfl⟩ : syracuseStep 2653589 = 124387) (by norm_num)
theorem B8953253 : Blo 1768085 8953253 := bbase (se 4 (by rfl) ⟨839367, by rfl⟩ : syracuseStep 8953253 = 1678735) (by norm_num)
theorem B1990057 : Blo 1768085 1990057 := bbase (se 2 (by rfl) ⟨746271, by rfl⟩ : syracuseStep 1990057 = 1492543) (by norm_num)
theorem B2653613 : Blo 1768085 2653613 := bbase (se 3 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 2653613 = 995105) (by norm_num)
theorem B3980717 : Blo 1768085 3980717 := bbase (se 3 (by rfl) ⟨746384, by rfl⟩ : syracuseStep 3980717 = 1492769) (by norm_num)
theorem B2653637 : Blo 1768085 2653637 := bbase (se 4 (by rfl) ⟨248778, by rfl⟩ : syracuseStep 2653637 = 497557) (by norm_num)
theorem B1990093 : Blo 1768085 1990093 := bbase (se 3 (by rfl) ⟨373142, by rfl⟩ : syracuseStep 1990093 = 746285) (by norm_num)
theorem B2653661 : Blo 1768085 2653661 := bbase (se 3 (by rfl) ⟨497561, by rfl⟩ : syracuseStep 2653661 = 995123) (by norm_num)
theorem B1990129 : Blo 1768085 1990129 := bbase (se 2 (by rfl) ⟨746298, by rfl⟩ : syracuseStep 1990129 = 1492597) (by norm_num)
theorem B2653685 : Blo 1768085 2653685 := bbase (se 5 (by rfl) ⟨124391, by rfl⟩ : syracuseStep 2653685 = 248783) (by norm_num)
theorem B3980789 : Blo 1768085 3980789 := bbase (se 5 (by rfl) ⟨186599, by rfl⟩ : syracuseStep 3980789 = 373199) (by norm_num)
theorem B2653709 : Blo 1768085 2653709 := bbase (se 3 (by rfl) ⟨497570, by rfl⟩ : syracuseStep 2653709 = 995141) (by norm_num)
theorem B1793549 : Blo 1768085 1793549 := bbase (se 3 (by rfl) ⟨336290, by rfl⟩ : syracuseStep 1793549 = 672581) (by norm_num)
theorem B1990165 : Blo 1768085 1990165 := bbase (se 6 (by rfl) ⟨46644, by rfl⟩ : syracuseStep 1990165 = 93289) (by norm_num)
theorem B2653733 : Blo 1768085 2653733 := bbase (se 4 (by rfl) ⟨248787, by rfl⟩ : syracuseStep 2653733 = 497575) (by norm_num)
theorem B3358253 : Blo 1768085 3358253 := bbase (se 3 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 3358253 = 1259345) (by norm_num)
theorem B1990201 : Blo 1768085 1990201 := bbase (se 2 (by rfl) ⟨746325, by rfl⟩ : syracuseStep 1990201 = 1492651) (by norm_num)
theorem B2653757 : Blo 1768085 2653757 := bbase (se 3 (by rfl) ⟨497579, by rfl⟩ : syracuseStep 2653757 = 995159) (by norm_num)
theorem B3980861 : Blo 1768085 3980861 := bbase (se 3 (by rfl) ⟨746411, by rfl⟩ : syracuseStep 3980861 = 1492823) (by norm_num)
theorem B8175173 : Blo 1768085 8175173 := bbase (se 4 (by rfl) ⟨766422, by rfl⟩ : syracuseStep 8175173 = 1532845) (by norm_num)
theorem B5037653 : Blo 1768085 5037653 := bbase (se 8 (by rfl) ⟨29517, by rfl⟩ : syracuseStep 5037653 = 59035) (by norm_num)
theorem B2653781 : Blo 1768085 2653781 := bbase (se 8 (by rfl) ⟨15549, by rfl⟩ : syracuseStep 2653781 = 31099) (by norm_num)
theorem B4251221 : Blo 1768085 4251221 := bbase (se 8 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 4251221 = 49819) (by norm_num)
theorem B1990237 : Blo 1768085 1990237 := bbase (se 3 (by rfl) ⟨373169, by rfl⟩ : syracuseStep 1990237 = 746339) (by norm_num)
theorem B3636829 : Blo 1768085 3636829 := bbase (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) (by norm_num)
theorem B2653805 : Blo 1768085 2653805 := bbase (se 3 (by rfl) ⟨497588, by rfl⟩ : syracuseStep 2653805 = 995177) (by norm_num)
theorem B2834045 : Blo 1768085 2834045 := bbase (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) (by norm_num)
theorem B1990273 : Blo 1768085 1990273 := bbase (se 2 (by rfl) ⟨746352, by rfl⟩ : syracuseStep 1990273 = 1492705) (by norm_num)
theorem B2653829 : Blo 1768085 2653829 := bbase (se 4 (by rfl) ⟨248796, by rfl⟩ : syracuseStep 2653829 = 497593) (by norm_num)
theorem B3980933 : Blo 1768085 3980933 := bbase (se 4 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 3980933 = 746425) (by norm_num)
theorem B5971589 : Blo 1768085 5971589 := bbase (se 4 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 5971589 = 1119673) (by norm_num)
theorem B2391701 : Blo 1768085 2391701 := bbase (se 6 (by rfl) ⟨56055, by rfl⟩ : syracuseStep 2391701 = 112111) (by norm_num)
theorem B2653853 : Blo 1768085 2653853 := bbase (se 3 (by rfl) ⟨497597, by rfl⟩ : syracuseStep 2653853 = 995195) (by norm_num)
theorem B1990309 : Blo 1768085 1990309 := bbase (se 4 (by rfl) ⟨186591, by rfl⟩ : syracuseStep 1990309 = 373183) (by norm_num)
theorem B2653877 : Blo 1768085 2653877 := bbase (se 5 (by rfl) ⟨124400, by rfl⟩ : syracuseStep 2653877 = 248801) (by norm_num)
theorem B6053557 : Blo 1768085 6053557 := bbase (se 5 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 6053557 = 567521) (by norm_num)
theorem B3358397 : Blo 1768085 3358397 := bbase (se 3 (by rfl) ⟨629699, by rfl⟩ : syracuseStep 3358397 = 1259399) (by norm_num)
theorem B1990345 : Blo 1768085 1990345 := bbase (se 2 (by rfl) ⟨746379, by rfl⟩ : syracuseStep 1990345 = 1492759) (by norm_num)
theorem B2653901 : Blo 1768085 2653901 := bbase (se 3 (by rfl) ⟨497606, by rfl⟩ : syracuseStep 2653901 = 995213) (by norm_num)
theorem B3981005 : Blo 1768085 3981005 := bbase (se 3 (by rfl) ⟨746438, by rfl⟩ : syracuseStep 3981005 = 1492877) (by norm_num)
theorem B6135509 : Blo 1768085 6135509 := bbase (se 7 (by rfl) ⟨71900, by rfl⟩ : syracuseStep 6135509 = 143801) (by norm_num)
theorem B2268893 : Blo 1768085 2268893 := bbase (se 3 (by rfl) ⟨425417, by rfl⟩ : syracuseStep 2268893 = 850835) (by norm_num)
theorem B2653925 : Blo 1768085 2653925 := bbase (se 4 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 2653925 = 497611) (by norm_num)
theorem B1990381 : Blo 1768085 1990381 := bbase (se 3 (by rfl) ⟨373196, by rfl⟩ : syracuseStep 1990381 = 746393) (by norm_num)
theorem B1793773 : Blo 1768085 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B2653949 : Blo 1768085 2653949 := bbase (se 3 (by rfl) ⟨497615, by rfl⟩ : syracuseStep 2653949 = 995231) (by norm_num)
theorem B1990417 : Blo 1768085 1990417 := bbase (se 2 (by rfl) ⟨746406, by rfl⟩ : syracuseStep 1990417 = 1492813) (by norm_num)
theorem B2653973 : Blo 1768085 2653973 := bbase (se 6 (by rfl) ⟨62202, by rfl⟩ : syracuseStep 2653973 = 124405) (by norm_num)
theorem B3981077 : Blo 1768085 3981077 := bbase (se 6 (by rfl) ⟨93306, by rfl⟩ : syracuseStep 3981077 = 186613) (by norm_num)
theorem B2653997 : Blo 1768085 2653997 := bbase (se 3 (by rfl) ⟨497624, by rfl⟩ : syracuseStep 2653997 = 995249) (by norm_num)
theorem B1990453 : Blo 1768085 1990453 := bbase (se 5 (by rfl) ⟨93302, by rfl⟩ : syracuseStep 1990453 = 186605) (by norm_num)
theorem B2654021 : Blo 1768085 2654021 := bbase (se 4 (by rfl) ⟨248814, by rfl⟩ : syracuseStep 2654021 = 497629) (by norm_num)
theorem B174407509 : Blo 1768085 174407509 := bbase (se 9 (by rfl) ⟨510959, by rfl⟩ : syracuseStep 174407509 = 1021919) (by norm_num)
theorem B1990489 : Blo 1768085 1990489 := bbase (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) (by norm_num)
theorem B2654045 : Blo 1768085 2654045 := bbase (se 3 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 2654045 = 995267) (by norm_num)
theorem B3981149 : Blo 1768085 3981149 := bbase (se 3 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 3981149 = 1492931) (by norm_num)
theorem B2654069 : Blo 1768085 2654069 := bbase (se 5 (by rfl) ⟨124409, by rfl⟩ : syracuseStep 2654069 = 248819) (by norm_num)
theorem B1990525 : Blo 1768085 1990525 := bbase (se 3 (by rfl) ⟨373223, by rfl⟩ : syracuseStep 1990525 = 746447) (by norm_num)
theorem B2654093 : Blo 1768085 2654093 := bbase (se 3 (by rfl) ⟨497642, by rfl⟩ : syracuseStep 2654093 = 995285) (by norm_num)
theorem B1990561 : Blo 1768085 1990561 := bbase (se 2 (by rfl) ⟨746460, by rfl⟩ : syracuseStep 1990561 = 1492921) (by norm_num)
theorem B2654117 : Blo 1768085 2654117 := bbase (se 4 (by rfl) ⟨248823, by rfl⟩ : syracuseStep 2654117 = 497647) (by norm_num)
theorem B3981221 : Blo 1768085 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B2654141 : Blo 1768085 2654141 := bbase (se 3 (by rfl) ⟨497651, by rfl⟩ : syracuseStep 2654141 = 995303) (by norm_num)
theorem B1990597 : Blo 1768085 1990597 := bbase (se 4 (by rfl) ⟨186618, by rfl⟩ : syracuseStep 1990597 = 373237) (by norm_num)
theorem B2654165 : Blo 1768085 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B3358685 : Blo 1768085 3358685 := bbase (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) (by norm_num)
theorem B1990633 : Blo 1768085 1990633 := bbase (se 2 (by rfl) ⟨746487, by rfl⟩ : syracuseStep 1990633 = 1492975) (by norm_num)
theorem B2654189 : Blo 1768085 2654189 := bbase (se 3 (by rfl) ⟨497660, by rfl⟩ : syracuseStep 2654189 = 995321) (by norm_num)
theorem B3981293 : Blo 1768085 3981293 := bbase (se 3 (by rfl) ⟨746492, by rfl⟩ : syracuseStep 3981293 = 1492985) (by norm_num)
theorem B1769475 : Blo 1768085 1769475 := bstep (se 1 (by rfl) ⟨1327106, by rfl⟩ : syracuseStep 1769475 = 2654213) B2654213
theorem B3981329 : Blo 1768085 3981329 := bstep (se 2 (by rfl) ⟨1492998, by rfl⟩ : syracuseStep 3981329 = 2985997) B2985997
theorem B2654225 : Blo 1768085 2654225 := bstep (se 2 (by rfl) ⟨995334, by rfl⟩ : syracuseStep 2654225 = 1990669) B1990669
theorem B1769491 : Blo 1768085 1769491 := bstep (se 1 (by rfl) ⟨1327118, by rfl⟩ : syracuseStep 1769491 = 2654237) B2654237
theorem B3981347 : Blo 1768085 3981347 := bstep (se 1 (by rfl) ⟨2986010, by rfl⟩ : syracuseStep 3981347 = 5972021) B5972021
theorem B2654243 : Blo 1768085 2654243 := bstep (se 1 (by rfl) ⟨1990682, by rfl⟩ : syracuseStep 2654243 = 3981365) B3981365
theorem B1769507 : Blo 1768085 1769507 := bstep (se 1 (by rfl) ⟨1327130, by rfl⟩ : syracuseStep 1769507 = 2654261) B2654261
theorem B4251683 : Blo 1768085 4251683 := bstep (se 1 (by rfl) ⟨3188762, by rfl⟩ : syracuseStep 4251683 = 6377525) B6377525
theorem B1769523 : Blo 1768085 1769523 := bstep (se 1 (by rfl) ⟨1327142, by rfl⟩ : syracuseStep 1769523 = 2654285) B2654285
theorem B2654273 : Blo 1768085 2654273 := bstep (se 2 (by rfl) ⟨995352, by rfl⟩ : syracuseStep 2654273 = 1990705) B1990705
theorem B1990723 : Blo 1768085 1990723 := bstep (se 1 (by rfl) ⟨1493042, by rfl⟩ : syracuseStep 1990723 = 2986085) B2986085
theorem B1769539 : Blo 1768085 1769539 := bstep (se 1 (by rfl) ⟨1327154, by rfl⟩ : syracuseStep 1769539 = 2654309) B2654309
theorem B2654291 : Blo 1768085 2654291 := bstep (se 1 (by rfl) ⟨1990718, by rfl⟩ : syracuseStep 2654291 = 3981437) B3981437
theorem B1769555 : Blo 1768085 1769555 := bstep (se 1 (by rfl) ⟨1327166, by rfl⟩ : syracuseStep 1769555 = 2654333) B2654333
theorem B19128419 : Blo 1768085 19128419 := bstep (se 1 (by rfl) ⟨14346314, by rfl⟩ : syracuseStep 19128419 = 28692629) B28692629
theorem B1769571 : Blo 1768085 1769571 := bstep (se 1 (by rfl) ⟨1327178, by rfl⟩ : syracuseStep 1769571 = 2654357) B2654357
theorem B2654321 : Blo 1768085 2654321 := bstep (se 2 (by rfl) ⟨995370, by rfl⟩ : syracuseStep 2654321 = 1990741) B1990741
theorem B1769587 : Blo 1768085 1769587 := bstep (se 1 (by rfl) ⟨1327190, by rfl⟩ : syracuseStep 1769587 = 2654381) B2654381
theorem B2654339 : Blo 1768085 2654339 := bstep (se 1 (by rfl) ⟨1990754, by rfl⟩ : syracuseStep 2654339 = 3981509) B3981509
theorem B4251779 : Blo 1768085 4251779 := bstep (se 1 (by rfl) ⟨3188834, by rfl⟩ : syracuseStep 4251779 = 6377669) B6377669
theorem B1769603 : Blo 1768085 1769603 := bstep (se 1 (by rfl) ⟨1327202, by rfl⟩ : syracuseStep 1769603 = 2654405) B2654405
theorem B1769619 : Blo 1768085 1769619 := bstep (se 1 (by rfl) ⟨1327214, by rfl⟩ : syracuseStep 1769619 = 2654429) B2654429
theorem B3358883 : Blo 1768085 3358883 := bstep (se 1 (by rfl) ⟨2519162, by rfl⟩ : syracuseStep 3358883 = 5038325) B5038325
theorem B2654369 : Blo 1768085 2654369 := bstep (se 2 (by rfl) ⟨995388, by rfl⟩ : syracuseStep 2654369 = 1990777) B1990777
theorem B1769635 : Blo 1768085 1769635 := bstep (se 1 (by rfl) ⟨1327226, by rfl⟩ : syracuseStep 1769635 = 2654453) B2654453
theorem B4784291 : Blo 1768085 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B2654387 : Blo 1768085 2654387 := bstep (se 1 (by rfl) ⟨1990790, by rfl⟩ : syracuseStep 2654387 = 3981581) B3981581
theorem B1769651 : Blo 1768085 1769651 := bstep (se 1 (by rfl) ⟨1327238, by rfl⟩ : syracuseStep 1769651 = 2654477) B2654477
theorem B1769667 : Blo 1768085 1769667 := bstep (se 1 (by rfl) ⟨1327250, by rfl⟩ : syracuseStep 1769667 = 2654501) B2654501
theorem B8503501 : Blo 1768085 8503501 := bstep (se 3 (by rfl) ⟨1594406, by rfl⟩ : syracuseStep 8503501 = 3188813) B3188813
theorem B2654417 : Blo 1768085 2654417 := bstep (se 2 (by rfl) ⟨995406, by rfl⟩ : syracuseStep 2654417 = 1990813) B1990813
theorem B1990867 : Blo 1768085 1990867 := bstep (se 1 (by rfl) ⟨1493150, by rfl⟩ : syracuseStep 1990867 = 2986301) B2986301
theorem B1769683 : Blo 1768085 1769683 := bstep (se 1 (by rfl) ⟨1327262, by rfl⟩ : syracuseStep 1769683 = 2654525) B2654525
theorem B2654435 : Blo 1768085 2654435 := bstep (se 1 (by rfl) ⟨1990826, by rfl⟩ : syracuseStep 2654435 = 3981653) B3981653
theorem B1769699 : Blo 1768085 1769699 := bstep (se 1 (by rfl) ⟨1327274, by rfl⟩ : syracuseStep 1769699 = 2654549) B2654549
theorem B1769715 : Blo 1768085 1769715 := bstep (se 1 (by rfl) ⟨1327286, by rfl⟩ : syracuseStep 1769715 = 2654573) B2654573
theorem B2654465 : Blo 1768085 2654465 := bstep (se 2 (by rfl) ⟨995424, by rfl⟩ : syracuseStep 2654465 = 1990849) B1990849
theorem B1769731 : Blo 1768085 1769731 := bstep (se 1 (by rfl) ⟨1327298, by rfl⟩ : syracuseStep 1769731 = 2654597) B2654597
theorem B5972237 : Blo 1768085 5972237 := bstep (se 3 (by rfl) ⟨1119794, by rfl⟩ : syracuseStep 5972237 = 2239589) B2239589
theorem B2654483 : Blo 1768085 2654483 := bstep (se 1 (by rfl) ⟨1990862, by rfl⟩ : syracuseStep 2654483 = 3981725) B3981725
theorem B1769747 : Blo 1768085 1769747 := bstep (se 1 (by rfl) ⟨1327310, by rfl⟩ : syracuseStep 1769747 = 2654621) B2654621
theorem B1769763 : Blo 1768085 1769763 := bstep (se 1 (by rfl) ⟨1327322, by rfl⟩ : syracuseStep 1769763 = 2654645) B2654645
theorem B3981617 : Blo 1768085 3981617 := bstep (se 2 (by rfl) ⟨1493106, by rfl⟩ : syracuseStep 3981617 = 2986213) B2986213
theorem B2654513 : Blo 1768085 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B1769779 : Blo 1768085 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B5972291 : Blo 1768085 5972291 := bstep (se 1 (by rfl) ⟨4479218, by rfl⟩ : syracuseStep 5972291 = 8958437) B8958437
theorem B3981635 : Blo 1768085 3981635 := bstep (se 1 (by rfl) ⟨2986226, by rfl⟩ : syracuseStep 3981635 = 5972453) B5972453
theorem B2654531 : Blo 1768085 2654531 := bstep (se 1 (by rfl) ⟨1990898, by rfl⟩ : syracuseStep 2654531 = 3981797) B3981797
theorem B1769795 : Blo 1768085 1769795 := bstep (se 1 (by rfl) ⟨1327346, by rfl⟩ : syracuseStep 1769795 = 2654693) B2654693
theorem B1769811 : Blo 1768085 1769811 := bstep (se 1 (by rfl) ⟨1327358, by rfl⟩ : syracuseStep 1769811 = 2654717) B2654717
theorem B2654561 : Blo 1768085 2654561 := bstep (se 2 (by rfl) ⟨995460, by rfl⟩ : syracuseStep 2654561 = 1990921) B1990921
theorem B1991011 : Blo 1768085 1991011 := bstep (se 1 (by rfl) ⟨1493258, by rfl⟩ : syracuseStep 1991011 = 2986517) B2986517
theorem B1769827 : Blo 1768085 1769827 := bstep (se 1 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 1769827 = 2654741) B2654741
theorem B3776881 : Blo 1768085 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B8954225 : Blo 1768085 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B2654579 : Blo 1768085 2654579 := bstep (se 1 (by rfl) ⟨1990934, by rfl⟩ : syracuseStep 2654579 = 3981869) B3981869
theorem B1769843 : Blo 1768085 1769843 := bstep (se 1 (by rfl) ⟨1327382, by rfl⟩ : syracuseStep 1769843 = 2654765) B2654765
theorem B1769859 : Blo 1768085 1769859 := bstep (se 1 (by rfl) ⟨1327394, by rfl⟩ : syracuseStep 1769859 = 2654789) B2654789
theorem B2654609 : Blo 1768085 2654609 := bstep (se 2 (by rfl) ⟨995478, by rfl⟩ : syracuseStep 2654609 = 1990957) B1990957
theorem B1769875 : Blo 1768085 1769875 := bstep (se 1 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 1769875 = 2654813) B2654813
theorem B2654627 : Blo 1768085 2654627 := bstep (se 1 (by rfl) ⟨1990970, by rfl⟩ : syracuseStep 2654627 = 3981941) B3981941
theorem B1769891 : Blo 1768085 1769891 := bstep (se 1 (by rfl) ⟨1327418, by rfl⟩ : syracuseStep 1769891 = 2654837) B2654837
theorem B1769907 : Blo 1768085 1769907 := bstep (se 1 (by rfl) ⟨1327430, by rfl⟩ : syracuseStep 1769907 = 2654861) B2654861
theorem B2654657 : Blo 1768085 2654657 := bstep (se 2 (by rfl) ⟨995496, by rfl⟩ : syracuseStep 2654657 = 1990993) B1990993
theorem B3359171 : Blo 1768085 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B1769923 : Blo 1768085 1769923 := bstep (se 1 (by rfl) ⟨1327442, by rfl⟩ : syracuseStep 1769923 = 2654885) B2654885
theorem B2654675 : Blo 1768085 2654675 := bstep (se 1 (by rfl) ⟨1991006, by rfl⟩ : syracuseStep 2654675 = 3982013) B3982013
theorem B1769939 : Blo 1768085 1769939 := bstep (se 1 (by rfl) ⟨1327454, by rfl⟩ : syracuseStep 1769939 = 2654909) B2654909
theorem B1769955 : Blo 1768085 1769955 := bstep (se 1 (by rfl) ⟨1327466, by rfl⟩ : syracuseStep 1769955 = 2654933) B2654933
theorem B2654705 : Blo 1768085 2654705 := bstep (se 2 (by rfl) ⟨995514, by rfl⟩ : syracuseStep 2654705 = 1991029) B1991029
theorem B2834929 : Blo 1768085 2834929 := bstep (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) B2126197
theorem B1991155 : Blo 1768085 1991155 := bstep (se 1 (by rfl) ⟨1493366, by rfl⟩ : syracuseStep 1991155 = 2986733) B2986733
theorem B1769971 : Blo 1768085 1769971 := bstep (se 1 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 1769971 = 2654957) B2654957
theorem B2654723 : Blo 1768085 2654723 := bstep (se 1 (by rfl) ⟨1991042, by rfl⟩ : syracuseStep 2654723 = 3982085) B3982085
theorem B1769987 : Blo 1768085 1769987 := bstep (se 1 (by rfl) ⟨1327490, by rfl⟩ : syracuseStep 1769987 = 2654981) B2654981
theorem B1770003 : Blo 1768085 1770003 := bstep (se 1 (by rfl) ⟨1327502, by rfl⟩ : syracuseStep 1770003 = 2655005) B2655005
theorem B2654753 : Blo 1768085 2654753 := bstep (se 2 (by rfl) ⟨995532, by rfl⟩ : syracuseStep 2654753 = 1991065) B1991065
theorem B1770019 : Blo 1768085 1770019 := bstep (se 1 (by rfl) ⟨1327514, by rfl⟩ : syracuseStep 1770019 = 2655029) B2655029
theorem B11493937 : Blo 1768085 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B2654771 : Blo 1768085 2654771 := bstep (se 1 (by rfl) ⟨1991078, by rfl⟩ : syracuseStep 2654771 = 3982157) B3982157
theorem B1770035 : Blo 1768085 1770035 := bstep (se 1 (by rfl) ⟨1327526, by rfl⟩ : syracuseStep 1770035 = 2655053) B2655053
theorem B2155075 : Blo 1768085 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B1770051 : Blo 1768085 1770051 := bstep (se 1 (by rfl) ⟨1327538, by rfl⟩ : syracuseStep 1770051 = 2655077) B2655077
theorem B5972561 : Blo 1768085 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B3981905 : Blo 1768085 3981905 := bstep (se 2 (by rfl) ⟨1493214, by rfl⟩ : syracuseStep 3981905 = 2986429) B2986429
theorem B2654801 : Blo 1768085 2654801 := bstep (se 2 (by rfl) ⟨995550, by rfl⟩ : syracuseStep 2654801 = 1991101) B1991101
theorem B1770067 : Blo 1768085 1770067 := bstep (se 1 (by rfl) ⟨1327550, by rfl⟩ : syracuseStep 1770067 = 2655101) B2655101
theorem B3981923 : Blo 1768085 3981923 := bstep (se 1 (by rfl) ⟨2986442, by rfl⟩ : syracuseStep 3981923 = 5972885) B5972885
theorem B2654819 : Blo 1768085 2654819 := bstep (se 1 (by rfl) ⟨1991114, by rfl⟩ : syracuseStep 2654819 = 3982229) B3982229
theorem B1770083 : Blo 1768085 1770083 := bstep (se 1 (by rfl) ⟨1327562, by rfl⟩ : syracuseStep 1770083 = 2655125) B2655125
theorem B2654849 : Blo 1768085 2654849 := bstep (se 2 (by rfl) ⟨995568, by rfl⟩ : syracuseStep 2654849 = 1991137) B1991137
theorem B1991299 : Blo 1768085 1991299 := bstep (se 1 (by rfl) ⟨1493474, by rfl⟩ : syracuseStep 1991299 = 2986949) B2986949
theorem B2654867 : Blo 1768085 2654867 := bstep (se 1 (by rfl) ⟨1991150, by rfl⟩ : syracuseStep 2654867 = 3982301) B3982301
theorem B9560753 : Blo 1768085 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B2654897 : Blo 1768085 2654897 := bstep (se 2 (by rfl) ⟨995586, by rfl⟩ : syracuseStep 2654897 = 1991173) B1991173
theorem B2654915 : Blo 1768085 2654915 := bstep (se 1 (by rfl) ⟨1991186, by rfl⟩ : syracuseStep 2654915 = 3982373) B3982373
theorem B2654945 : Blo 1768085 2654945 := bstep (se 2 (by rfl) ⟨995604, by rfl⟩ : syracuseStep 2654945 = 1991209) B1991209
theorem B2654963 : Blo 1768085 2654963 := bstep (se 1 (by rfl) ⟨1991222, by rfl⟩ : syracuseStep 2654963 = 3982445) B3982445
theorem B3777283 : Blo 1768085 3777283 := bstep (se 1 (by rfl) ⟨2832962, by rfl⟩ : syracuseStep 3777283 = 5665925) B5665925
theorem B2654993 : Blo 1768085 2654993 := bstep (se 2 (by rfl) ⟨995622, by rfl⟩ : syracuseStep 2654993 = 1991245) B1991245
theorem B2655011 : Blo 1768085 2655011 := bstep (se 1 (by rfl) ⟨1991258, by rfl⟩ : syracuseStep 2655011 = 3982517) B3982517
theorem B2655041 : Blo 1768085 2655041 := bstep (se 2 (by rfl) ⟨995640, by rfl⟩ : syracuseStep 2655041 = 1991281) B1991281
theorem B2655059 : Blo 1768085 2655059 := bstep (se 1 (by rfl) ⟨1991294, by rfl⟩ : syracuseStep 2655059 = 3982589) B3982589
theorem B3982193 : Blo 1768085 3982193 := bstep (se 2 (by rfl) ⟨1493322, by rfl⟩ : syracuseStep 3982193 = 2986645) B2986645
theorem B2655089 : Blo 1768085 2655089 := bstep (se 2 (by rfl) ⟨995658, by rfl⟩ : syracuseStep 2655089 = 1991317) B1991317
theorem B3982211 : Blo 1768085 3982211 := bstep (se 1 (by rfl) ⟨2986658, by rfl⟩ : syracuseStep 3982211 = 5973317) B5973317
theorem B11330437 : Blo 1768085 11330437 := bstep (se 4 (by rfl) ⟨1062228, by rfl⟩ : syracuseStep 11330437 = 2124457) B2124457
theorem B2655107 : Blo 1768085 2655107 := bstep (se 1 (by rfl) ⟨1991330, by rfl⟩ : syracuseStep 2655107 = 3982661) B3982661
theorem B7554019 : Blo 1768085 7554019 := bstep (se 1 (by rfl) ⟨5665514, by rfl⟩ : syracuseStep 7554019 = 11331029) B11331029
theorem B3187811 : Blo 1768085 3187811 := bstep (se 1 (by rfl) ⟨2390858, by rfl⟩ : syracuseStep 3187811 = 4781717) B4781717
theorem B5973101 : Blo 1768085 5973101 := bstep (se 3 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 5973101 = 2239913) B2239913
theorem B6374513 : Blo 1768085 6374513 := bstep (se 2 (by rfl) ⟨2390442, by rfl⟩ : syracuseStep 6374513 = 4780885) B4780885
theorem B3982481 : Blo 1768085 3982481 := bstep (se 2 (by rfl) ⟨1493430, by rfl⟩ : syracuseStep 3982481 = 2986861) B2986861
theorem B5973155 : Blo 1768085 5973155 := bstep (se 1 (by rfl) ⟨4479866, by rfl⟩ : syracuseStep 5973155 = 8959733) B8959733
theorem B3982499 : Blo 1768085 3982499 := bstep (se 1 (by rfl) ⟨2986874, by rfl⟩ : syracuseStep 3982499 = 5973749) B5973749
theorem B7169201 : Blo 1768085 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B6374627 : Blo 1768085 6374627 := bstep (se 1 (by rfl) ⟨4780970, by rfl⟩ : syracuseStep 6374627 = 9561941) B9561941
theorem B2688323 : Blo 1768085 2688323 := bstep (se 1 (by rfl) ⟨2016242, by rfl⟩ : syracuseStep 2688323 = 4032485) B4032485
theorem B11060549 : Blo 1768085 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B5039441 : Blo 1768085 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B3360113 : Blo 1768085 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B5973425 : Blo 1768085 5973425 := bstep (se 2 (by rfl) ⟨2240034, by rfl⟩ : syracuseStep 5973425 = 4480069) B4480069
theorem B21800461 : Blo 1768085 21800461 := bstep (se 3 (by rfl) ⟨4087586, by rfl⟩ : syracuseStep 21800461 = 8175173) B8175173
theorem B12748357 : Blo 1768085 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B5670499 : Blo 1768085 5670499 := bstep (se 1 (by rfl) ⟨4252874, by rfl⟩ : syracuseStep 5670499 = 8505749) B8505749
theorem B2238131 : Blo 1768085 2238131 := bstep (se 1 (by rfl) ⟨1678598, by rfl⟩ : syracuseStep 2238131 = 3357197) B3357197
theorem B2016995 : Blo 1768085 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B5670641 : Blo 1768085 5670641 := bstep (se 2 (by rfl) ⟨2126490, by rfl⟩ : syracuseStep 5670641 = 4252981) B4252981
theorem B19121933 : Blo 1768085 19121933 := bstep (se 3 (by rfl) ⟨3585362, by rfl⟩ : syracuseStep 19121933 = 7170725) B7170725
theorem B8955683 : Blo 1768085 8955683 := bstep (se 1 (by rfl) ⟨6716762, by rfl⟩ : syracuseStep 8955683 = 13433525) B13433525
theorem B2983729 : Blo 1768085 2983729 := bstep (se 2 (by rfl) ⟨1118898, by rfl⟩ : syracuseStep 2983729 = 2237797) B2237797
theorem B2983763 : Blo 1768085 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B10069859 : Blo 1768085 10069859 := bstep (se 1 (by rfl) ⟨7552394, by rfl⟩ : syracuseStep 10069859 = 15104789) B15104789
theorem B6719345 : Blo 1768085 6719345 := bstep (se 2 (by rfl) ⟨2519754, by rfl⟩ : syracuseStep 6719345 = 5039509) B5039509
theorem B16361357 : Blo 1768085 16361357 := bstep (se 3 (by rfl) ⟨3067754, by rfl⟩ : syracuseStep 16361357 = 6135509) B6135509
theorem B2688913 : Blo 1768085 2688913 := bstep (se 2 (by rfl) ⟨1008342, by rfl⟩ : syracuseStep 2688913 = 2016685) B2016685
theorem B5973965 : Blo 1768085 5973965 := bstep (se 3 (by rfl) ⟨1120118, by rfl⟩ : syracuseStep 5973965 = 2240237) B2240237
theorem B2983891 : Blo 1768085 2983891 := bstep (se 1 (by rfl) ⟨2237918, by rfl⟩ : syracuseStep 2983891 = 4475837) B4475837
theorem B5974019 : Blo 1768085 5974019 := bstep (se 1 (by rfl) ⟨4480514, by rfl⟩ : syracuseStep 5974019 = 8961029) B8961029
theorem B2984033 : Blo 1768085 2984033 := bstep (se 2 (by rfl) ⟨1119012, by rfl⟩ : syracuseStep 2984033 = 2238025) B2238025
theorem B2984161 : Blo 1768085 2984161 := bstep (se 2 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 2984161 = 2238121) B2238121
theorem B3778787 : Blo 1768085 3778787 := bstep (se 1 (by rfl) ⟨2834090, by rfl⟩ : syracuseStep 3778787 = 5668181) B5668181
theorem B8071409 : Blo 1768085 8071409 := bstep (se 2 (by rfl) ⟨3026778, by rfl⟩ : syracuseStep 8071409 = 6053557) B6053557
theorem B2984195 : Blo 1768085 2984195 := bstep (se 1 (by rfl) ⟨2238146, by rfl⟩ : syracuseStep 2984195 = 4476293) B4476293
theorem B5040397 : Blo 1768085 5040397 := bstep (se 3 (by rfl) ⟨945074, by rfl⟩ : syracuseStep 5040397 = 1890149) B1890149
theorem B9562481 : Blo 1768085 9562481 := bstep (se 2 (by rfl) ⟨3585930, by rfl⟩ : syracuseStep 9562481 = 7171861) B7171861
theorem B2238835 : Blo 1768085 2238835 := bstep (se 1 (by rfl) ⟨1679126, by rfl⟩ : syracuseStep 2238835 = 3358253) B3358253
theorem B2984323 : Blo 1768085 2984323 := bstep (se 1 (by rfl) ⟨2238242, by rfl⟩ : syracuseStep 2984323 = 4476485) B4476485
theorem B2238931 : Blo 1768085 2238931 := bstep (se 1 (by rfl) ⟨1679198, by rfl⟩ : syracuseStep 2238931 = 3358397) B3358397
theorem B2984465 : Blo 1768085 2984465 := bstep (se 2 (by rfl) ⟨1119174, by rfl⟩ : syracuseStep 2984465 = 2238349) B2238349
theorem B10078789 : Blo 1768085 10078789 := bstep (se 4 (by rfl) ⟨944886, by rfl⟩ : syracuseStep 10078789 = 1889773) B1889773
theorem B8956493 : Blo 1768085 8956493 := bstep (se 3 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 8956493 = 3358685) B3358685
theorem B2984593 : Blo 1768085 2984593 := bstep (se 2 (by rfl) ⟨1119222, by rfl⟩ : syracuseStep 2984593 = 2238445) B2238445
theorem B2984627 : Blo 1768085 2984627 := bstep (se 1 (by rfl) ⟨2238470, by rfl⟩ : syracuseStep 2984627 = 4476941) B4476941
theorem B11340485 : Blo 1768085 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B4664017 : Blo 1768085 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B2124515 : Blo 1768085 2124515 := bstep (se 1 (by rfl) ⟨1593386, by rfl⟩ : syracuseStep 2124515 = 3186773) B3186773
theorem B2517761 : Blo 1768085 2517761 := bstep (se 2 (by rfl) ⟨944160, by rfl⟩ : syracuseStep 2517761 = 1888321) B1888321
theorem B2984755 : Blo 1768085 2984755 := bstep (se 1 (by rfl) ⟨2238566, by rfl⟩ : syracuseStep 2984755 = 4477133) B4477133
theorem B2517841 : Blo 1768085 2517841 := bstep (se 2 (by rfl) ⟨944190, by rfl⟩ : syracuseStep 2517841 = 1888381) B1888381
theorem B3025795 : Blo 1768085 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B7556017 : Blo 1768085 7556017 := bstep (se 2 (by rfl) ⟨2833506, by rfl⟩ : syracuseStep 7556017 = 5667013) B5667013
theorem B2984897 : Blo 1768085 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B2239427 : Blo 1768085 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B4475857 : Blo 1768085 4475857 := bstep (se 2 (by rfl) ⟨1678446, by rfl⟩ : syracuseStep 4475857 = 3356893) B3356893
theorem B9956357 : Blo 1768085 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B2985025 : Blo 1768085 2985025 := bstep (se 2 (by rfl) ⟨1119384, by rfl⟩ : syracuseStep 2985025 = 2238769) B2238769
theorem B12102733 : Blo 1768085 12102733 := bstep (se 3 (by rfl) ⟨2269262, by rfl⟩ : syracuseStep 12102733 = 4538525) B4538525
theorem B2985059 : Blo 1768085 2985059 := bstep (se 1 (by rfl) ⟨2238794, by rfl⟩ : syracuseStep 2985059 = 4477589) B4477589
theorem B4476131 : Blo 1768085 4476131 := bstep (se 1 (by rfl) ⟨3357098, by rfl⟩ : syracuseStep 4476131 = 6714197) B6714197
theorem B2985187 : Blo 1768085 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B15117637 : Blo 1768085 15117637 := bstep (se 4 (by rfl) ⟨1417278, by rfl⟩ : syracuseStep 15117637 = 2834557) B2834557
theorem B2985329 : Blo 1768085 2985329 := bstep (se 2 (by rfl) ⟨1119498, by rfl⟩ : syracuseStep 2985329 = 2238997) B2238997
theorem B2690417 : Blo 1768085 2690417 := bstep (se 2 (by rfl) ⟨1008906, by rfl⟩ : syracuseStep 2690417 = 2017813) B2017813
theorem B4476323 : Blo 1768085 4476323 := bstep (se 1 (by rfl) ⟨3357242, by rfl⟩ : syracuseStep 4476323 = 6714485) B6714485
theorem B3780017 : Blo 1768085 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B2985457 : Blo 1768085 2985457 := bstep (se 2 (by rfl) ⟨1119546, by rfl⟩ : syracuseStep 2985457 = 2239093) B2239093
theorem B5967377 : Blo 1768085 5967377 := bstep (se 2 (by rfl) ⟨2237766, by rfl⟩ : syracuseStep 5967377 = 4475533) B4475533
theorem B2985491 : Blo 1768085 2985491 := bstep (se 1 (by rfl) ⟨2239118, by rfl⟩ : syracuseStep 2985491 = 4478237) B4478237
theorem B11333155 : Blo 1768085 11333155 := bstep (se 1 (by rfl) ⟨8499866, by rfl⟩ : syracuseStep 11333155 = 16999733) B16999733
theorem B5664323 : Blo 1768085 5664323 := bstep (se 1 (by rfl) ⟨4248242, by rfl⟩ : syracuseStep 5664323 = 8496485) B8496485
theorem B2518627 : Blo 1768085 2518627 := bstep (se 1 (by rfl) ⟨1888970, by rfl⟩ : syracuseStep 2518627 = 3777941) B3777941
theorem B9080419 : Blo 1768085 9080419 := bstep (se 1 (by rfl) ⟨6810314, by rfl⟩ : syracuseStep 9080419 = 13620629) B13620629
theorem B2240131 : Blo 1768085 2240131 := bstep (se 1 (by rfl) ⟨1680098, by rfl⟩ : syracuseStep 2240131 = 3360197) B3360197
theorem B2985619 : Blo 1768085 2985619 := bstep (se 1 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 2985619 = 4478429) B4478429
theorem B2870945 : Blo 1768085 2870945 := bstep (se 2 (by rfl) ⟨1076604, by rfl⟩ : syracuseStep 2870945 = 2153209) B2153209
theorem B5664451 : Blo 1768085 5664451 := bstep (se 1 (by rfl) ⟨4248338, by rfl⟩ : syracuseStep 5664451 = 8496677) B8496677
theorem B2240227 : Blo 1768085 2240227 := bstep (se 1 (by rfl) ⟨1680170, by rfl⟩ : syracuseStep 2240227 = 3360341) B3360341
theorem B2985761 : Blo 1768085 2985761 := bstep (se 2 (by rfl) ⟨1119660, by rfl⟩ : syracuseStep 2985761 = 2239321) B2239321
theorem B5664593 : Blo 1768085 5664593 := bstep (se 2 (by rfl) ⟨2124222, by rfl⟩ : syracuseStep 5664593 = 4248445) B4248445
theorem B2985889 : Blo 1768085 2985889 := bstep (se 2 (by rfl) ⟨1119708, by rfl⟩ : syracuseStep 2985889 = 2239417) B2239417
theorem B10489763 : Blo 1768085 10489763 := bstep (se 1 (by rfl) ⟨7867322, by rfl⟩ : syracuseStep 10489763 = 15734645) B15734645
theorem B5664707 : Blo 1768085 5664707 := bstep (se 1 (by rfl) ⟨4248530, by rfl⟩ : syracuseStep 5664707 = 8497061) B8497061
theorem B2985923 : Blo 1768085 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B18157553 : Blo 1768085 18157553 := bstep (se 2 (by rfl) ⟨6809082, by rfl⟩ : syracuseStep 18157553 = 13618165) B13618165
theorem B5967917 : Blo 1768085 5967917 := bstep (se 3 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 5967917 = 2237969) B2237969
theorem B2519105 : Blo 1768085 2519105 := bstep (se 2 (by rfl) ⟨944664, by rfl⟩ : syracuseStep 2519105 = 1889329) B1889329
theorem B2986051 : Blo 1768085 2986051 := bstep (se 1 (by rfl) ⟨2239538, by rfl⟩ : syracuseStep 2986051 = 4479077) B4479077
theorem B5967971 : Blo 1768085 5967971 := bstep (se 1 (by rfl) ⟨4475978, by rfl⟩ : syracuseStep 5967971 = 8951957) B8951957
theorem B6131825 : Blo 1768085 6131825 := bstep (se 2 (by rfl) ⟨2299434, by rfl⟩ : syracuseStep 6131825 = 4598869) B4598869
theorem B18157709 : Blo 1768085 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B2519219 : Blo 1768085 2519219 := bstep (se 1 (by rfl) ⟨1889414, by rfl⟩ : syracuseStep 2519219 = 3778829) B3778829
theorem B2986193 : Blo 1768085 2986193 := bstep (se 2 (by rfl) ⟨1119822, by rfl⟩ : syracuseStep 2986193 = 2239645) B2239645
theorem B2519299 : Blo 1768085 2519299 := bstep (se 1 (by rfl) ⟨1889474, by rfl⟩ : syracuseStep 2519299 = 3778949) B3778949
theorem B24219917 : Blo 1768085 24219917 := bstep (se 3 (by rfl) ⟨4541234, by rfl⟩ : syracuseStep 24219917 = 9082469) B9082469
theorem B4477265 : Blo 1768085 4477265 := bstep (se 2 (by rfl) ⟨1678974, by rfl⟩ : syracuseStep 4477265 = 3357949) B3357949
theorem B2986321 : Blo 1768085 2986321 := bstep (se 2 (by rfl) ⟨1119870, by rfl⟩ : syracuseStep 2986321 = 2239741) B2239741
theorem B5968241 : Blo 1768085 5968241 := bstep (se 2 (by rfl) ⟨2238090, by rfl⟩ : syracuseStep 5968241 = 4476181) B4476181
theorem B2986355 : Blo 1768085 2986355 := bstep (se 1 (by rfl) ⟨2239766, by rfl⟩ : syracuseStep 2986355 = 4479533) B4479533
theorem B4477315 : Blo 1768085 4477315 := bstep (se 1 (by rfl) ⟨3357986, by rfl⟩ : syracuseStep 4477315 = 6715973) B6715973
theorem B6377869 : Blo 1768085 6377869 := bstep (se 3 (by rfl) ⟨1195850, by rfl⟩ : syracuseStep 6377869 = 2391701) B2391701
theorem B2986483 : Blo 1768085 2986483 := bstep (se 1 (by rfl) ⟨2239862, by rfl⟩ : syracuseStep 2986483 = 4479725) B4479725
theorem B10080773 : Blo 1768085 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B4477457 : Blo 1768085 4477457 := bstep (se 2 (by rfl) ⟨1679046, by rfl⟩ : syracuseStep 4477457 = 3358093) B3358093
theorem B6050381 : Blo 1768085 6050381 := bstep (se 3 (by rfl) ⟨1134446, by rfl⟩ : syracuseStep 6050381 = 2268893) B2268893
theorem B4780657 : Blo 1768085 4780657 := bstep (se 2 (by rfl) ⟨1792746, by rfl⟩ : syracuseStep 4780657 = 3585493) B3585493
theorem B2986625 : Blo 1768085 2986625 := bstep (se 2 (by rfl) ⟨1119984, by rfl⟩ : syracuseStep 2986625 = 2239969) B2239969
theorem B1888915 : Blo 1768085 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B4780721 : Blo 1768085 4780721 := bstep (se 2 (by rfl) ⟨1792770, by rfl⟩ : syracuseStep 4780721 = 3585541) B3585541
theorem B43037381 : Blo 1768085 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B2986753 : Blo 1768085 2986753 := bstep (se 2 (by rfl) ⟨1120032, by rfl⟩ : syracuseStep 2986753 = 2240065) B2240065
theorem B2986787 : Blo 1768085 2986787 := bstep (se 1 (by rfl) ⟨2240090, by rfl⟩ : syracuseStep 2986787 = 4480181) B4480181
theorem B2519857 : Blo 1768085 2519857 := bstep (se 2 (by rfl) ⟨944946, by rfl⟩ : syracuseStep 2519857 = 1889893) B1889893
theorem B6714211 : Blo 1768085 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B13439843 : Blo 1768085 13439843 := bstep (se 1 (by rfl) ⟨10079882, by rfl⟩ : syracuseStep 13439843 = 20159765) B20159765
theorem B5968781 : Blo 1768085 5968781 := bstep (se 3 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 5968781 = 2238293) B2238293
theorem B2986915 : Blo 1768085 2986915 := bstep (se 1 (by rfl) ⟨2240186, by rfl⟩ : syracuseStep 2986915 = 4480373) B4480373
theorem B5968835 : Blo 1768085 5968835 := bstep (se 1 (by rfl) ⟨4476626, by rfl⟩ : syracuseStep 5968835 = 8953253) B8953253
theorem B5379089 : Blo 1768085 5379089 := bstep (se 2 (by rfl) ⟨2017158, by rfl⟩ : syracuseStep 5379089 = 4034317) B4034317
theorem B1889363 : Blo 1768085 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B232543345 : Blo 1768085 232543345 := bstep (se 2 (by rfl) ⟨87203754, by rfl⟩ : syracuseStep 232543345 = 174407509) B174407509
theorem B3978449 : Blo 1768085 3978449 := bstep (se 2 (by rfl) ⟨1491918, by rfl⟩ : syracuseStep 3978449 = 2983837) B2983837
theorem B5969105 : Blo 1768085 5969105 := bstep (se 2 (by rfl) ⟨2238414, by rfl⟩ : syracuseStep 5969105 = 4476829) B4476829
theorem B3978467 : Blo 1768085 3978467 := bstep (se 1 (by rfl) ⟨2983850, by rfl⟩ : syracuseStep 3978467 = 5967701) B5967701
theorem B3585379 : Blo 1768085 3585379 := bstep (se 1 (by rfl) ⟨2689034, by rfl⟩ : syracuseStep 3585379 = 5378069) B5378069
theorem B5035409 : Blo 1768085 5035409 := bstep (se 2 (by rfl) ⟨1888278, by rfl⟩ : syracuseStep 5035409 = 3776557) B3776557
theorem B8959409 : Blo 1768085 8959409 := bstep (se 2 (by rfl) ⟨3359778, by rfl⟩ : syracuseStep 8959409 = 6719557) B6719557
theorem B2725315 : Blo 1768085 2725315 := bstep (se 1 (by rfl) ⟨2043986, by rfl⟩ : syracuseStep 2725315 = 4087973) B4087973
theorem B3978737 : Blo 1768085 3978737 := bstep (se 2 (by rfl) ⟨1492026, by rfl⟩ : syracuseStep 3978737 = 2984053) B2984053
theorem B11335153 : Blo 1768085 11335153 := bstep (se 2 (by rfl) ⟨4250682, by rfl⟩ : syracuseStep 11335153 = 8501365) B8501365
theorem B4478449 : Blo 1768085 4478449 := bstep (se 2 (by rfl) ⟨1679418, by rfl⟩ : syracuseStep 4478449 = 3358837) B3358837
theorem B3978755 : Blo 1768085 3978755 := bstep (se 1 (by rfl) ⟨2984066, by rfl⟩ : syracuseStep 3978755 = 5968133) B5968133
theorem B8951309 : Blo 1768085 8951309 := bstep (se 3 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 8951309 = 3356741) B3356741
theorem B5666449 : Blo 1768085 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B5969645 : Blo 1768085 5969645 := bstep (se 3 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 5969645 = 2238617) B2238617
theorem B4478723 : Blo 1768085 4478723 := bstep (se 1 (by rfl) ⟨3359042, by rfl⟩ : syracuseStep 4478723 = 6718085) B6718085
theorem B3979025 : Blo 1768085 3979025 := bstep (se 2 (by rfl) ⟨1492134, by rfl⟩ : syracuseStep 3979025 = 2984269) B2984269
theorem B2389793 : Blo 1768085 2389793 := bstep (se 2 (by rfl) ⟨896172, by rfl⟩ : syracuseStep 2389793 = 1792345) B1792345
theorem B3979043 : Blo 1768085 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B5969699 : Blo 1768085 5969699 := bstep (se 1 (by rfl) ⟨4477274, by rfl⟩ : syracuseStep 5969699 = 8954549) B8954549
theorem B19396421 : Blo 1768085 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B20158307 : Blo 1768085 20158307 := bstep (se 1 (by rfl) ⟨15118730, by rfl⟩ : syracuseStep 20158307 = 30237461) B30237461
theorem B9566093 : Blo 1768085 9566093 := bstep (se 3 (by rfl) ⟨1793642, by rfl⟩ : syracuseStep 9566093 = 3587285) B3587285
theorem B4478915 : Blo 1768085 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B2873297 : Blo 1768085 2873297 := bstep (se 2 (by rfl) ⟨1077486, by rfl⟩ : syracuseStep 2873297 = 2154973) B2154973
theorem B2652131 : Blo 1768085 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B2652161 : Blo 1768085 2652161 := bstep (se 2 (by rfl) ⟨994560, by rfl⟩ : syracuseStep 2652161 = 1989121) B1989121
theorem B2652179 : Blo 1768085 2652179 := bstep (se 1 (by rfl) ⟨1989134, by rfl⟩ : syracuseStep 2652179 = 3978269) B3978269
theorem B2652209 : Blo 1768085 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B3979313 : Blo 1768085 3979313 := bstep (se 2 (by rfl) ⟨1492242, by rfl⟩ : syracuseStep 3979313 = 2984485) B2984485
theorem B5969969 : Blo 1768085 5969969 := bstep (se 2 (by rfl) ⟨2238738, by rfl⟩ : syracuseStep 5969969 = 4477477) B4477477
theorem B2652227 : Blo 1768085 2652227 := bstep (se 1 (by rfl) ⟨1989170, by rfl⟩ : syracuseStep 2652227 = 3978341) B3978341
theorem B3979331 : Blo 1768085 3979331 := bstep (se 1 (by rfl) ⟨2984498, by rfl⟩ : syracuseStep 3979331 = 5968997) B5968997
theorem B2652257 : Blo 1768085 2652257 := bstep (se 2 (by rfl) ⟨994596, by rfl⟩ : syracuseStep 2652257 = 1989193) B1989193
theorem B2652275 : Blo 1768085 2652275 := bstep (se 1 (by rfl) ⟨1989206, by rfl⟩ : syracuseStep 2652275 = 3978413) B3978413
theorem B2652305 : Blo 1768085 2652305 := bstep (se 2 (by rfl) ⟨994614, by rfl⟩ : syracuseStep 2652305 = 1989229) B1989229
theorem B2652323 : Blo 1768085 2652323 := bstep (se 1 (by rfl) ⟨1989242, by rfl⟩ : syracuseStep 2652323 = 3978485) B3978485
theorem B5036195 : Blo 1768085 5036195 := bstep (se 1 (by rfl) ⟨3777146, by rfl⟩ : syracuseStep 5036195 = 7554293) B7554293
theorem B2652353 : Blo 1768085 2652353 := bstep (se 2 (by rfl) ⟨994632, by rfl⟩ : syracuseStep 2652353 = 1989265) B1989265
theorem B2652371 : Blo 1768085 2652371 := bstep (se 1 (by rfl) ⟨1989278, by rfl⟩ : syracuseStep 2652371 = 3978557) B3978557
theorem B2652401 : Blo 1768085 2652401 := bstep (se 2 (by rfl) ⟨994650, by rfl⟩ : syracuseStep 2652401 = 1989301) B1989301
theorem B2652419 : Blo 1768085 2652419 := bstep (se 1 (by rfl) ⟨1989314, by rfl⟩ : syracuseStep 2652419 = 3978629) B3978629
theorem B2652449 : Blo 1768085 2652449 := bstep (se 2 (by rfl) ⟨994668, by rfl⟩ : syracuseStep 2652449 = 1989337) B1989337
theorem B3356977 : Blo 1768085 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B2652467 : Blo 1768085 2652467 := bstep (se 1 (by rfl) ⟨1989350, by rfl⟩ : syracuseStep 2652467 = 3978701) B3978701
theorem B2832707 : Blo 1768085 2832707 := bstep (se 1 (by rfl) ⟨2124530, by rfl⟩ : syracuseStep 2832707 = 4249061) B4249061
theorem B2652497 : Blo 1768085 2652497 := bstep (se 2 (by rfl) ⟨994686, by rfl⟩ : syracuseStep 2652497 = 1989373) B1989373
theorem B3979601 : Blo 1768085 3979601 := bstep (se 2 (by rfl) ⟨1492350, by rfl⟩ : syracuseStep 3979601 = 2984701) B2984701
theorem B2652515 : Blo 1768085 2652515 := bstep (se 1 (by rfl) ⟨1989386, by rfl⟩ : syracuseStep 2652515 = 3978773) B3978773
theorem B3979619 : Blo 1768085 3979619 := bstep (se 1 (by rfl) ⟨2984714, by rfl⟩ : syracuseStep 3979619 = 5969429) B5969429
theorem B7272803 : Blo 1768085 7272803 := bstep (se 1 (by rfl) ⟨5454602, by rfl⟩ : syracuseStep 7272803 = 10909205) B10909205
theorem B2652545 : Blo 1768085 2652545 := bstep (se 2 (by rfl) ⟨994704, by rfl⟩ : syracuseStep 2652545 = 1989409) B1989409
theorem B2652563 : Blo 1768085 2652563 := bstep (se 1 (by rfl) ⟨1989422, by rfl⟩ : syracuseStep 2652563 = 3978845) B3978845
theorem B5454253 : Blo 1768085 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B2652593 : Blo 1768085 2652593 := bstep (se 2 (by rfl) ⟨994722, by rfl⟩ : syracuseStep 2652593 = 1989445) B1989445
theorem B2652611 : Blo 1768085 2652611 := bstep (se 1 (by rfl) ⟨1989458, by rfl⟩ : syracuseStep 2652611 = 3978917) B3978917
theorem B2652641 : Blo 1768085 2652641 := bstep (se 2 (by rfl) ⟨994740, by rfl⟩ : syracuseStep 2652641 = 1989481) B1989481
theorem B5036525 : Blo 1768085 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B2652659 : Blo 1768085 2652659 := bstep (se 1 (by rfl) ⟨1989494, by rfl⟩ : syracuseStep 2652659 = 3978989) B3978989
theorem B2652689 : Blo 1768085 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B1989139 : Blo 1768085 1989139 := bstep (se 1 (by rfl) ⟨1491854, by rfl⟩ : syracuseStep 1989139 = 2983709) B2983709
theorem B2652707 : Blo 1768085 2652707 := bstep (se 1 (by rfl) ⟨1989530, by rfl⟩ : syracuseStep 2652707 = 3979061) B3979061
theorem B5036593 : Blo 1768085 5036593 := bstep (se 2 (by rfl) ⟨1888722, by rfl⟩ : syracuseStep 5036593 = 3777445) B3777445
theorem B2652737 : Blo 1768085 2652737 := bstep (se 2 (by rfl) ⟨994776, by rfl⟩ : syracuseStep 2652737 = 1989553) B1989553
theorem B5970509 : Blo 1768085 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B2652755 : Blo 1768085 2652755 := bstep (se 1 (by rfl) ⟨1989566, by rfl⟩ : syracuseStep 2652755 = 3979133) B3979133
theorem B13802083 : Blo 1768085 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B2652785 : Blo 1768085 2652785 := bstep (se 2 (by rfl) ⟨994794, by rfl⟩ : syracuseStep 2652785 = 1989589) B1989589
theorem B3979889 : Blo 1768085 3979889 := bstep (se 2 (by rfl) ⟨1492458, by rfl⟩ : syracuseStep 3979889 = 2984917) B2984917
theorem B2652803 : Blo 1768085 2652803 := bstep (se 1 (by rfl) ⟨1989602, by rfl⟩ : syracuseStep 2652803 = 3979205) B3979205
theorem B3979907 : Blo 1768085 3979907 := bstep (se 1 (by rfl) ⟨2984930, by rfl⟩ : syracuseStep 3979907 = 5969861) B5969861
theorem B5970563 : Blo 1768085 5970563 := bstep (se 1 (by rfl) ⟨4477922, by rfl⟩ : syracuseStep 5970563 = 8955845) B8955845
theorem B5454481 : Blo 1768085 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B2652833 : Blo 1768085 2652833 := bstep (se 2 (by rfl) ⟨994812, by rfl⟩ : syracuseStep 2652833 = 1989625) B1989625
theorem B1768099 : Blo 1768085 1768099 := bstep (se 1 (by rfl) ⟨1326074, by rfl⟩ : syracuseStep 1768099 = 2652149) B2652149
theorem B1989283 : Blo 1768085 1989283 := bstep (se 1 (by rfl) ⟨1491962, by rfl⟩ : syracuseStep 1989283 = 2983925) B2983925
theorem B1768115 : Blo 1768085 1768115 := bstep (se 1 (by rfl) ⟨1326086, by rfl⟩ : syracuseStep 1768115 = 2652173) B2652173
theorem B2652851 : Blo 1768085 2652851 := bstep (se 1 (by rfl) ⟨1989638, by rfl⟩ : syracuseStep 2652851 = 3979277) B3979277
theorem B1768131 : Blo 1768085 1768131 := bstep (se 1 (by rfl) ⟨1326098, by rfl⟩ : syracuseStep 1768131 = 2652197) B2652197
theorem B3357379 : Blo 1768085 3357379 := bstep (se 1 (by rfl) ⟨2518034, by rfl⟩ : syracuseStep 3357379 = 5036069) B5036069
theorem B4782797 : Blo 1768085 4782797 := bstep (se 3 (by rfl) ⟨896774, by rfl⟩ : syracuseStep 4782797 = 1793549) B1793549
theorem B2652881 : Blo 1768085 2652881 := bstep (se 2 (by rfl) ⟨994830, by rfl⟩ : syracuseStep 2652881 = 1989661) B1989661
theorem B1768147 : Blo 1768085 1768147 := bstep (se 1 (by rfl) ⟨1326110, by rfl⟩ : syracuseStep 1768147 = 2652221) B2652221
theorem B1768163 : Blo 1768085 1768163 := bstep (se 1 (by rfl) ⟨1326122, by rfl⟩ : syracuseStep 1768163 = 2652245) B2652245
theorem B2652899 : Blo 1768085 2652899 := bstep (se 1 (by rfl) ⟨1989674, by rfl⟩ : syracuseStep 2652899 = 3979349) B3979349
theorem B5667565 : Blo 1768085 5667565 := bstep (se 3 (by rfl) ⟨1062668, by rfl⟩ : syracuseStep 5667565 = 2125337) B2125337
theorem B3357425 : Blo 1768085 3357425 := bstep (se 2 (by rfl) ⟨1259034, by rfl⟩ : syracuseStep 3357425 = 2518069) B2518069
theorem B1768179 : Blo 1768085 1768179 := bstep (se 1 (by rfl) ⟨1326134, by rfl⟩ : syracuseStep 1768179 = 2652269) B2652269
theorem B2652929 : Blo 1768085 2652929 := bstep (se 2 (by rfl) ⟨994848, by rfl⟩ : syracuseStep 2652929 = 1989697) B1989697
theorem B1768195 : Blo 1768085 1768195 := bstep (se 1 (by rfl) ⟨1326146, by rfl⟩ : syracuseStep 1768195 = 2652293) B2652293
theorem B1768211 : Blo 1768085 1768211 := bstep (se 1 (by rfl) ⟨1326158, by rfl⟩ : syracuseStep 1768211 = 2652317) B2652317
theorem B2652947 : Blo 1768085 2652947 := bstep (se 1 (by rfl) ⟨1989710, by rfl⟩ : syracuseStep 2652947 = 3979421) B3979421
theorem B1768227 : Blo 1768085 1768227 := bstep (se 1 (by rfl) ⟨1326170, by rfl⟩ : syracuseStep 1768227 = 2652341) B2652341
theorem B2652977 : Blo 1768085 2652977 := bstep (se 2 (by rfl) ⟨994866, by rfl⟩ : syracuseStep 2652977 = 1989733) B1989733
theorem B1768243 : Blo 1768085 1768243 := bstep (se 1 (by rfl) ⟨1326182, by rfl⟩ : syracuseStep 1768243 = 2652365) B2652365
theorem B1989427 : Blo 1768085 1989427 := bstep (se 1 (by rfl) ⟨1492070, by rfl⟩ : syracuseStep 1989427 = 2984141) B2984141
theorem B1792819 : Blo 1768085 1792819 := bstep (se 1 (by rfl) ⟨1344614, by rfl⟩ : syracuseStep 1792819 = 2689229) B2689229
theorem B1768259 : Blo 1768085 1768259 := bstep (se 1 (by rfl) ⟨1326194, by rfl⟩ : syracuseStep 1768259 = 2652389) B2652389
theorem B2652995 : Blo 1768085 2652995 := bstep (se 1 (by rfl) ⟨1989746, by rfl⟩ : syracuseStep 2652995 = 3979493) B3979493
theorem B1792835 : Blo 1768085 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B5036867 : Blo 1768085 5036867 := bstep (se 1 (by rfl) ⟨3777650, by rfl⟩ : syracuseStep 5036867 = 7555301) B7555301
theorem B1768275 : Blo 1768085 1768275 := bstep (se 1 (by rfl) ⟨1326206, by rfl⟩ : syracuseStep 1768275 = 2652413) B2652413
theorem B2653025 : Blo 1768085 2653025 := bstep (se 2 (by rfl) ⟨994884, by rfl⟩ : syracuseStep 2653025 = 1989769) B1989769
theorem B1768291 : Blo 1768085 1768291 := bstep (se 1 (by rfl) ⟨1326218, by rfl⟩ : syracuseStep 1768291 = 2652437) B2652437
theorem B8960867 : Blo 1768085 8960867 := bstep (se 1 (by rfl) ⟨6720650, by rfl⟩ : syracuseStep 8960867 = 13441301) B13441301
theorem B4479857 : Blo 1768085 4479857 := bstep (se 2 (by rfl) ⟨1679946, by rfl⟩ : syracuseStep 4479857 = 3359893) B3359893
theorem B1768307 : Blo 1768085 1768307 := bstep (se 1 (by rfl) ⟨1326230, by rfl⟩ : syracuseStep 1768307 = 2652461) B2652461
theorem B2653043 : Blo 1768085 2653043 := bstep (se 1 (by rfl) ⟨1989782, by rfl⟩ : syracuseStep 2653043 = 3979565) B3979565
theorem B7560049 : Blo 1768085 7560049 := bstep (se 2 (by rfl) ⟨2835018, by rfl⟩ : syracuseStep 7560049 = 5670037) B5670037
theorem B1768323 : Blo 1768085 1768323 := bstep (se 1 (by rfl) ⟨1326242, by rfl⟩ : syracuseStep 1768323 = 2652485) B2652485
theorem B2653073 : Blo 1768085 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B3980177 : Blo 1768085 3980177 := bstep (se 2 (by rfl) ⟨1492566, by rfl⟩ : syracuseStep 3980177 = 2985133) B2985133
theorem B1768339 : Blo 1768085 1768339 := bstep (se 1 (by rfl) ⟨1326254, by rfl⟩ : syracuseStep 1768339 = 2652509) B2652509
theorem B5970833 : Blo 1768085 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B1768355 : Blo 1768085 1768355 := bstep (se 1 (by rfl) ⟨1326266, by rfl⟩ : syracuseStep 1768355 = 2652533) B2652533
theorem B2653091 : Blo 1768085 2653091 := bstep (se 1 (by rfl) ⟨1989818, by rfl⟩ : syracuseStep 2653091 = 3979637) B3979637
theorem B3980195 : Blo 1768085 3980195 := bstep (se 1 (by rfl) ⟨2985146, by rfl⟩ : syracuseStep 3980195 = 5970293) B5970293
theorem B4479907 : Blo 1768085 4479907 := bstep (se 1 (by rfl) ⟨3359930, by rfl⟩ : syracuseStep 4479907 = 6719861) B6719861
theorem B1768371 : Blo 1768085 1768371 := bstep (se 1 (by rfl) ⟨1326278, by rfl⟩ : syracuseStep 1768371 = 2652557) B2652557
theorem B2653121 : Blo 1768085 2653121 := bstep (se 2 (by rfl) ⟨994920, by rfl⟩ : syracuseStep 2653121 = 1989841) B1989841
theorem B1768387 : Blo 1768085 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B1989571 : Blo 1768085 1989571 := bstep (se 1 (by rfl) ⟨1492178, by rfl⟩ : syracuseStep 1989571 = 2984357) B2984357
theorem B1768403 : Blo 1768085 1768403 := bstep (se 1 (by rfl) ⟨1326302, by rfl⟩ : syracuseStep 1768403 = 2652605) B2652605
theorem B2653139 : Blo 1768085 2653139 := bstep (se 1 (by rfl) ⟨1989854, by rfl⟩ : syracuseStep 2653139 = 3979709) B3979709
theorem B1768419 : Blo 1768085 1768419 := bstep (se 1 (by rfl) ⟨1326314, by rfl⟩ : syracuseStep 1768419 = 2652629) B2652629
theorem B2653169 : Blo 1768085 2653169 := bstep (se 2 (by rfl) ⟨994938, by rfl⟩ : syracuseStep 2653169 = 1989877) B1989877
theorem B1768435 : Blo 1768085 1768435 := bstep (se 1 (by rfl) ⟨1326326, by rfl⟩ : syracuseStep 1768435 = 2652653) B2652653
theorem B1768451 : Blo 1768085 1768451 := bstep (se 1 (by rfl) ⟨1326338, by rfl⟩ : syracuseStep 1768451 = 2652677) B2652677
theorem B2653187 : Blo 1768085 2653187 := bstep (se 1 (by rfl) ⟨1989890, by rfl⟩ : syracuseStep 2653187 = 3979781) B3979781
theorem B6716429 : Blo 1768085 6716429 := bstep (se 3 (by rfl) ⟨1259330, by rfl⟩ : syracuseStep 6716429 = 2518661) B2518661
theorem B3357713 : Blo 1768085 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B1768467 : Blo 1768085 1768467 := bstep (se 1 (by rfl) ⟨1326350, by rfl⟩ : syracuseStep 1768467 = 2652701) B2652701
theorem B2653217 : Blo 1768085 2653217 := bstep (se 2 (by rfl) ⟨994956, by rfl⟩ : syracuseStep 2653217 = 1989913) B1989913
theorem B1768483 : Blo 1768085 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B4480049 : Blo 1768085 4480049 := bstep (se 2 (by rfl) ⟨1680018, by rfl⟩ : syracuseStep 4480049 = 3360037) B3360037
theorem B1768499 : Blo 1768085 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B2653235 : Blo 1768085 2653235 := bstep (se 1 (by rfl) ⟨1989926, by rfl⟩ : syracuseStep 2653235 = 3979853) B3979853
theorem B1768515 : Blo 1768085 1768515 := bstep (se 1 (by rfl) ⟨1326386, by rfl⟩ : syracuseStep 1768515 = 2652773) B2652773
theorem B2653265 : Blo 1768085 2653265 := bstep (se 2 (by rfl) ⟨994974, by rfl⟩ : syracuseStep 2653265 = 1989949) B1989949
theorem B1768531 : Blo 1768085 1768531 := bstep (se 1 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 1768531 = 2652797) B2652797
theorem B1989715 : Blo 1768085 1989715 := bstep (se 1 (by rfl) ⟨1492286, by rfl⟩ : syracuseStep 1989715 = 2984573) B2984573
theorem B1768547 : Blo 1768085 1768547 := bstep (se 1 (by rfl) ⟨1326410, by rfl⟩ : syracuseStep 1768547 = 2652821) B2652821
theorem B2653283 : Blo 1768085 2653283 := bstep (se 1 (by rfl) ⟨1989962, by rfl⟩ : syracuseStep 2653283 = 3979925) B3979925
theorem B5454947 : Blo 1768085 5454947 := bstep (se 1 (by rfl) ⟨4091210, by rfl⟩ : syracuseStep 5454947 = 8182421) B8182421
theorem B1768563 : Blo 1768085 1768563 := bstep (se 1 (by rfl) ⟨1326422, by rfl⟩ : syracuseStep 1768563 = 2652845) B2652845
theorem B2653313 : Blo 1768085 2653313 := bstep (se 2 (by rfl) ⟨994992, by rfl⟩ : syracuseStep 2653313 = 1989985) B1989985
theorem B1768579 : Blo 1768085 1768579 := bstep (se 1 (by rfl) ⟨1326434, by rfl⟩ : syracuseStep 1768579 = 2652869) B2652869
theorem B1768595 : Blo 1768085 1768595 := bstep (se 1 (by rfl) ⟨1326446, by rfl⟩ : syracuseStep 1768595 = 2652893) B2652893
theorem B2653331 : Blo 1768085 2653331 := bstep (se 1 (by rfl) ⟨1989998, by rfl⟩ : syracuseStep 2653331 = 3979997) B3979997
theorem B1768611 : Blo 1768085 1768611 := bstep (se 1 (by rfl) ⟨1326458, by rfl⟩ : syracuseStep 1768611 = 2652917) B2652917
theorem B2653361 : Blo 1768085 2653361 := bstep (se 2 (by rfl) ⟨995010, by rfl⟩ : syracuseStep 2653361 = 1990021) B1990021
theorem B3980465 : Blo 1768085 3980465 := bstep (se 2 (by rfl) ⟨1492674, by rfl⟩ : syracuseStep 3980465 = 2985349) B2985349
theorem B1768627 : Blo 1768085 1768627 := bstep (se 1 (by rfl) ⟨1326470, by rfl⟩ : syracuseStep 1768627 = 2652941) B2652941
theorem B1768643 : Blo 1768085 1768643 := bstep (se 1 (by rfl) ⟨1326482, by rfl⟩ : syracuseStep 1768643 = 2652965) B2652965
theorem B2653379 : Blo 1768085 2653379 := bstep (se 1 (by rfl) ⟨1990034, by rfl⟩ : syracuseStep 2653379 = 3980069) B3980069
theorem B3980483 : Blo 1768085 3980483 := bstep (se 1 (by rfl) ⟨2985362, by rfl⟩ : syracuseStep 3980483 = 5970725) B5970725
theorem B1768659 : Blo 1768085 1768659 := bstep (se 1 (by rfl) ⟨1326494, by rfl⟩ : syracuseStep 1768659 = 2652989) B2652989
theorem B2653409 : Blo 1768085 2653409 := bstep (se 2 (by rfl) ⟨995028, by rfl⟩ : syracuseStep 2653409 = 1990057) B1990057
theorem B1768675 : Blo 1768085 1768675 := bstep (se 1 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 1768675 = 2653013) B2653013
theorem B1989859 : Blo 1768085 1989859 := bstep (se 1 (by rfl) ⟨1492394, by rfl⟩ : syracuseStep 1989859 = 2984789) B2984789
theorem B1768691 : Blo 1768085 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B2653427 : Blo 1768085 2653427 := bstep (se 1 (by rfl) ⟨1990070, by rfl⟩ : syracuseStep 2653427 = 3980141) B3980141
theorem B1768707 : Blo 1768085 1768707 := bstep (se 1 (by rfl) ⟨1326530, by rfl⟩ : syracuseStep 1768707 = 2653061) B2653061
theorem B2653457 : Blo 1768085 2653457 := bstep (se 2 (by rfl) ⟨995046, by rfl⟩ : syracuseStep 2653457 = 1990093) B1990093
theorem B1768723 : Blo 1768085 1768723 := bstep (se 1 (by rfl) ⟨1326542, by rfl⟩ : syracuseStep 1768723 = 2653085) B2653085
theorem B1768739 : Blo 1768085 1768739 := bstep (se 1 (by rfl) ⟨1326554, by rfl⟩ : syracuseStep 1768739 = 2653109) B2653109
theorem B2653475 : Blo 1768085 2653475 := bstep (se 1 (by rfl) ⟨1990106, by rfl⟩ : syracuseStep 2653475 = 3980213) B3980213
theorem B2833699 : Blo 1768085 2833699 := bstep (se 1 (by rfl) ⟨2125274, by rfl⟩ : syracuseStep 2833699 = 4250549) B4250549
theorem B1768755 : Blo 1768085 1768755 := bstep (se 1 (by rfl) ⟨1326566, by rfl⟩ : syracuseStep 1768755 = 2653133) B2653133
theorem B2653505 : Blo 1768085 2653505 := bstep (se 2 (by rfl) ⟨995064, by rfl⟩ : syracuseStep 2653505 = 1990129) B1990129
theorem B1768771 : Blo 1768085 1768771 := bstep (se 1 (by rfl) ⟨1326578, by rfl⟩ : syracuseStep 1768771 = 2653157) B2653157
theorem B1768787 : Blo 1768085 1768787 := bstep (se 1 (by rfl) ⟨1326590, by rfl⟩ : syracuseStep 1768787 = 2653181) B2653181
theorem B2653523 : Blo 1768085 2653523 := bstep (se 1 (by rfl) ⟨1990142, by rfl⟩ : syracuseStep 2653523 = 3980285) B3980285
theorem B1768803 : Blo 1768085 1768803 := bstep (se 1 (by rfl) ⟨1326602, by rfl⟩ : syracuseStep 1768803 = 2653205) B2653205
theorem B2653553 : Blo 1768085 2653553 := bstep (se 2 (by rfl) ⟨995082, by rfl⟩ : syracuseStep 2653553 = 1990165) B1990165
theorem B1768819 : Blo 1768085 1768819 := bstep (se 1 (by rfl) ⟨1326614, by rfl⟩ : syracuseStep 1768819 = 2653229) B2653229
theorem B1990003 : Blo 1768085 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B1768835 : Blo 1768085 1768835 := bstep (se 1 (by rfl) ⟨1326626, by rfl⟩ : syracuseStep 1768835 = 2653253) B2653253
theorem B2653571 : Blo 1768085 2653571 := bstep (se 1 (by rfl) ⟨1990178, by rfl⟩ : syracuseStep 2653571 = 3980357) B3980357
theorem B1768851 : Blo 1768085 1768851 := bstep (se 1 (by rfl) ⟨1326638, by rfl⟩ : syracuseStep 1768851 = 2653277) B2653277
theorem B2653601 : Blo 1768085 2653601 := bstep (se 2 (by rfl) ⟨995100, by rfl⟩ : syracuseStep 2653601 = 1990201) B1990201
theorem B1768867 : Blo 1768085 1768867 := bstep (se 1 (by rfl) ⟨1326650, by rfl⟩ : syracuseStep 1768867 = 2653301) B2653301
theorem B5971373 : Blo 1768085 5971373 := bstep (se 3 (by rfl) ⟨1119632, by rfl⟩ : syracuseStep 5971373 = 2239265) B2239265
theorem B1768883 : Blo 1768085 1768883 := bstep (se 1 (by rfl) ⟨1326662, by rfl⟩ : syracuseStep 1768883 = 2653325) B2653325
theorem B2653619 : Blo 1768085 2653619 := bstep (se 1 (by rfl) ⟨1990214, by rfl⟩ : syracuseStep 2653619 = 3980429) B3980429
theorem B1768899 : Blo 1768085 1768899 := bstep (se 1 (by rfl) ⟨1326674, by rfl⟩ : syracuseStep 1768899 = 2653349) B2653349
theorem B2653649 : Blo 1768085 2653649 := bstep (se 2 (by rfl) ⟨995118, by rfl⟩ : syracuseStep 2653649 = 1990237) B1990237
theorem B3980753 : Blo 1768085 3980753 := bstep (se 2 (by rfl) ⟨1492782, by rfl⟩ : syracuseStep 3980753 = 2985565) B2985565
theorem B1768915 : Blo 1768085 1768915 := bstep (se 1 (by rfl) ⟨1326686, by rfl⟩ : syracuseStep 1768915 = 2653373) B2653373
theorem B1768931 : Blo 1768085 1768931 := bstep (se 1 (by rfl) ⟨1326698, by rfl⟩ : syracuseStep 1768931 = 2653397) B2653397
theorem B2653667 : Blo 1768085 2653667 := bstep (se 1 (by rfl) ⟨1990250, by rfl⟩ : syracuseStep 2653667 = 3980501) B3980501
theorem B3980771 : Blo 1768085 3980771 := bstep (se 1 (by rfl) ⟨2985578, by rfl⟩ : syracuseStep 3980771 = 5971157) B5971157
theorem B5971427 : Blo 1768085 5971427 := bstep (se 1 (by rfl) ⟨4478570, by rfl⟩ : syracuseStep 5971427 = 8957141) B8957141
theorem B9567715 : Blo 1768085 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B1768947 : Blo 1768085 1768947 := bstep (se 1 (by rfl) ⟨1326710, by rfl⟩ : syracuseStep 1768947 = 2653421) B2653421
theorem B2653697 : Blo 1768085 2653697 := bstep (se 2 (by rfl) ⟨995136, by rfl⟩ : syracuseStep 2653697 = 1990273) B1990273
theorem B1768963 : Blo 1768085 1768963 := bstep (se 1 (by rfl) ⟨1326722, by rfl⟩ : syracuseStep 1768963 = 2653445) B2653445
theorem B1990147 : Blo 1768085 1990147 := bstep (se 1 (by rfl) ⟨1492610, by rfl⟩ : syracuseStep 1990147 = 2985221) B2985221
theorem B4783619 : Blo 1768085 4783619 := bstep (se 1 (by rfl) ⟨3587714, by rfl⟩ : syracuseStep 4783619 = 7175429) B7175429
theorem B2833937 : Blo 1768085 2833937 := bstep (se 2 (by rfl) ⟨1062726, by rfl⟩ : syracuseStep 2833937 = 2125453) B2125453
theorem B1768979 : Blo 1768085 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B2653715 : Blo 1768085 2653715 := bstep (se 1 (by rfl) ⟨1990286, by rfl⟩ : syracuseStep 2653715 = 3980573) B3980573
theorem B1768995 : Blo 1768085 1768995 := bstep (se 1 (by rfl) ⟨1326746, by rfl⟩ : syracuseStep 1768995 = 2653493) B2653493
theorem B2653745 : Blo 1768085 2653745 := bstep (se 2 (by rfl) ⟨995154, by rfl⟩ : syracuseStep 2653745 = 1990309) B1990309
theorem B1769011 : Blo 1768085 1769011 := bstep (se 1 (by rfl) ⟨1326758, by rfl⟩ : syracuseStep 1769011 = 2653517) B2653517
theorem B5668397 : Blo 1768085 5668397 := bstep (se 3 (by rfl) ⟨1062824, by rfl⟩ : syracuseStep 5668397 = 2125649) B2125649
theorem B1769027 : Blo 1768085 1769027 := bstep (se 1 (by rfl) ⟨1326770, by rfl⟩ : syracuseStep 1769027 = 2653541) B2653541
theorem B2653763 : Blo 1768085 2653763 := bstep (se 1 (by rfl) ⟨1990322, by rfl⟩ : syracuseStep 2653763 = 3980645) B3980645
theorem B1769043 : Blo 1768085 1769043 := bstep (se 1 (by rfl) ⟨1326782, by rfl⟩ : syracuseStep 1769043 = 2653565) B2653565
theorem B2653793 : Blo 1768085 2653793 := bstep (se 2 (by rfl) ⟨995172, by rfl⟩ : syracuseStep 2653793 = 1990345) B1990345
theorem B1769059 : Blo 1768085 1769059 := bstep (se 1 (by rfl) ⟨1326794, by rfl⟩ : syracuseStep 1769059 = 2653589) B2653589
theorem B1769075 : Blo 1768085 1769075 := bstep (se 1 (by rfl) ⟨1326806, by rfl⟩ : syracuseStep 1769075 = 2653613) B2653613
theorem B2653811 : Blo 1768085 2653811 := bstep (se 1 (by rfl) ⟨1990358, by rfl⟩ : syracuseStep 2653811 = 3980717) B3980717
theorem B1769091 : Blo 1768085 1769091 := bstep (se 1 (by rfl) ⟨1326818, by rfl⟩ : syracuseStep 1769091 = 2653637) B2653637
theorem B5037709 : Blo 1768085 5037709 := bstep (se 3 (by rfl) ⟨944570, by rfl⟩ : syracuseStep 5037709 = 1889141) B1889141
theorem B2653841 : Blo 1768085 2653841 := bstep (se 2 (by rfl) ⟨995190, by rfl⟩ : syracuseStep 2653841 = 1990381) B1990381
theorem B2391697 : Blo 1768085 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B1769107 : Blo 1768085 1769107 := bstep (se 1 (by rfl) ⟨1326830, by rfl⟩ : syracuseStep 1769107 = 2653661) B2653661
theorem B1990291 : Blo 1768085 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B1769123 : Blo 1768085 1769123 := bstep (se 1 (by rfl) ⟨1326842, by rfl⟩ : syracuseStep 1769123 = 2653685) B2653685
theorem B2653859 : Blo 1768085 2653859 := bstep (se 1 (by rfl) ⟨1990394, by rfl⟩ : syracuseStep 2653859 = 3980789) B3980789
theorem B1769139 : Blo 1768085 1769139 := bstep (se 1 (by rfl) ⟨1326854, by rfl⟩ : syracuseStep 1769139 = 2653709) B2653709
theorem B2653889 : Blo 1768085 2653889 := bstep (se 2 (by rfl) ⟨995208, by rfl⟩ : syracuseStep 2653889 = 1990417) B1990417
theorem B1769155 : Blo 1768085 1769155 := bstep (se 1 (by rfl) ⟨1326866, by rfl⟩ : syracuseStep 1769155 = 2653733) B2653733
theorem B1769171 : Blo 1768085 1769171 := bstep (se 1 (by rfl) ⟨1326878, by rfl⟩ : syracuseStep 1769171 = 2653757) B2653757
theorem B2653907 : Blo 1768085 2653907 := bstep (se 1 (by rfl) ⟨1990430, by rfl⟩ : syracuseStep 2653907 = 3980861) B3980861
theorem B3358435 : Blo 1768085 3358435 := bstep (se 1 (by rfl) ⟨2518826, by rfl⟩ : syracuseStep 3358435 = 5037653) B5037653
theorem B1769187 : Blo 1768085 1769187 := bstep (se 1 (by rfl) ⟨1326890, by rfl⟩ : syracuseStep 1769187 = 2653781) B2653781
theorem B2834147 : Blo 1768085 2834147 := bstep (se 1 (by rfl) ⟨2125610, by rfl⟩ : syracuseStep 2834147 = 4251221) B4251221
theorem B2653937 : Blo 1768085 2653937 := bstep (se 2 (by rfl) ⟨995226, by rfl⟩ : syracuseStep 2653937 = 1990453) B1990453
theorem B3981041 : Blo 1768085 3981041 := bstep (se 2 (by rfl) ⟨1492890, by rfl⟩ : syracuseStep 3981041 = 2985781) B2985781
theorem B1769203 : Blo 1768085 1769203 := bstep (se 1 (by rfl) ⟨1326902, by rfl⟩ : syracuseStep 1769203 = 2653805) B2653805
theorem B5971697 : Blo 1768085 5971697 := bstep (se 2 (by rfl) ⟨2239386, by rfl⟩ : syracuseStep 5971697 = 4478773) B4478773
theorem B1769219 : Blo 1768085 1769219 := bstep (se 1 (by rfl) ⟨1326914, by rfl⟩ : syracuseStep 1769219 = 2653829) B2653829
theorem B2653955 : Blo 1768085 2653955 := bstep (se 1 (by rfl) ⟨1990466, by rfl⟩ : syracuseStep 2653955 = 3980933) B3980933
theorem B3981059 : Blo 1768085 3981059 := bstep (se 1 (by rfl) ⟨2985794, by rfl⟩ : syracuseStep 3981059 = 5971589) B5971589
theorem B1769235 : Blo 1768085 1769235 := bstep (se 1 (by rfl) ⟨1326926, by rfl⟩ : syracuseStep 1769235 = 2653853) B2653853
theorem B77561621 : Blo 1768085 77561621 := bstep (se 6 (by rfl) ⟨1817850, by rfl⟩ : syracuseStep 77561621 = 3635701) B3635701
theorem B2653985 : Blo 1768085 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B1769251 : Blo 1768085 1769251 := bstep (se 1 (by rfl) ⟨1326938, by rfl⟩ : syracuseStep 1769251 = 2653877) B2653877
theorem B1990435 : Blo 1768085 1990435 := bstep (se 1 (by rfl) ⟨1492826, by rfl⟩ : syracuseStep 1990435 = 2985653) B2985653
theorem B5037869 : Blo 1768085 5037869 := bstep (se 3 (by rfl) ⟨944600, by rfl⟩ : syracuseStep 5037869 = 1889201) B1889201
theorem B1769267 : Blo 1768085 1769267 := bstep (se 1 (by rfl) ⟨1326950, by rfl⟩ : syracuseStep 1769267 = 2653901) B2653901
theorem B2654003 : Blo 1768085 2654003 := bstep (se 1 (by rfl) ⟨1990502, by rfl⟩ : syracuseStep 2654003 = 3981005) B3981005
theorem B1769283 : Blo 1768085 1769283 := bstep (se 1 (by rfl) ⟨1326962, by rfl⟩ : syracuseStep 1769283 = 2653925) B2653925
theorem B24207173 : Blo 1768085 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B2654033 : Blo 1768085 2654033 := bstep (se 2 (by rfl) ⟨995262, by rfl⟩ : syracuseStep 2654033 = 1990525) B1990525
theorem B1769299 : Blo 1768085 1769299 := bstep (se 1 (by rfl) ⟨1326974, by rfl⟩ : syracuseStep 1769299 = 2653949) B2653949
theorem B1769315 : Blo 1768085 1769315 := bstep (se 1 (by rfl) ⟨1326986, by rfl⟩ : syracuseStep 1769315 = 2653973) B2653973
theorem B2654051 : Blo 1768085 2654051 := bstep (se 1 (by rfl) ⟨1990538, by rfl⟩ : syracuseStep 2654051 = 3981077) B3981077
theorem B4251491 : Blo 1768085 4251491 := bstep (se 1 (by rfl) ⟨3188618, by rfl⟩ : syracuseStep 4251491 = 6377237) B6377237
theorem B15327089 : Blo 1768085 15327089 := bstep (se 2 (by rfl) ⟨5747658, by rfl⟩ : syracuseStep 15327089 = 11495317) B11495317
theorem B1769331 : Blo 1768085 1769331 := bstep (se 1 (by rfl) ⟨1326998, by rfl⟩ : syracuseStep 1769331 = 2653997) B2653997
theorem B2654081 : Blo 1768085 2654081 := bstep (se 2 (by rfl) ⟨995280, by rfl⟩ : syracuseStep 2654081 = 1990561) B1990561
theorem B1769347 : Blo 1768085 1769347 := bstep (se 1 (by rfl) ⟨1327010, by rfl⟩ : syracuseStep 1769347 = 2654021) B2654021
theorem B1769363 : Blo 1768085 1769363 := bstep (se 1 (by rfl) ⟨1327022, by rfl⟩ : syracuseStep 1769363 = 2654045) B2654045
theorem B2654099 : Blo 1768085 2654099 := bstep (se 1 (by rfl) ⟨1990574, by rfl⟩ : syracuseStep 2654099 = 3981149) B3981149
theorem B1769379 : Blo 1768085 1769379 := bstep (se 1 (by rfl) ⟨1327034, by rfl⟩ : syracuseStep 1769379 = 2654069) B2654069
theorem B2654129 : Blo 1768085 2654129 := bstep (se 2 (by rfl) ⟨995298, by rfl⟩ : syracuseStep 2654129 = 1990597) B1990597
theorem B1769395 : Blo 1768085 1769395 := bstep (se 1 (by rfl) ⟨1327046, by rfl⟩ : syracuseStep 1769395 = 2654093) B2654093
theorem B1990579 : Blo 1768085 1990579 := bstep (se 1 (by rfl) ⟨1492934, by rfl⟩ : syracuseStep 1990579 = 2985869) B2985869
theorem B1769411 : Blo 1768085 1769411 := bstep (se 1 (by rfl) ⟨1327058, by rfl⟩ : syracuseStep 1769411 = 2654117) B2654117
theorem B2654147 : Blo 1768085 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B14540741 : Blo 1768085 14540741 := bstep (se 4 (by rfl) ⟨1363194, by rfl⟩ : syracuseStep 14540741 = 2726389) B2726389
theorem B1769427 : Blo 1768085 1769427 := bstep (se 1 (by rfl) ⟨1327070, by rfl⟩ : syracuseStep 1769427 = 2654141) B2654141
theorem B2654177 : Blo 1768085 2654177 := bstep (se 2 (by rfl) ⟨995316, by rfl⟩ : syracuseStep 2654177 = 1990633) B1990633
theorem B5038051 : Blo 1768085 5038051 := bstep (se 1 (by rfl) ⟨3778538, by rfl⟩ : syracuseStep 5038051 = 7557077) B7557077
theorem B1769443 : Blo 1768085 1769443 := bstep (se 1 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 1769443 = 2654165) B2654165
theorem B1769459 : Blo 1768085 1769459 := bstep (se 1 (by rfl) ⟨1327094, by rfl⟩ : syracuseStep 1769459 = 2654189) B2654189
theorem B2654195 : Blo 1768085 2654195 := bstep (se 1 (by rfl) ⟨1990646, by rfl⟩ : syracuseStep 2654195 = 3981293) B3981293
theorem B2654219 : Blo 1768085 2654219 := bstep (se 1 (by rfl) ⟨1990664, by rfl⟩ : syracuseStep 2654219 = 3981329) B3981329
theorem B1769483 : Blo 1768085 1769483 := bstep (se 1 (by rfl) ⟨1327112, by rfl⟩ : syracuseStep 1769483 = 2654225) B2654225
theorem B2654231 : Blo 1768085 2654231 := bstep (se 1 (by rfl) ⟨1990673, by rfl⟩ : syracuseStep 2654231 = 3981347) B3981347
theorem B1769495 : Blo 1768085 1769495 := bstep (se 1 (by rfl) ⟨1327121, by rfl⟩ : syracuseStep 1769495 = 2654243) B2654243
theorem B2834455 : Blo 1768085 2834455 := bstep (se 1 (by rfl) ⟨2125841, by rfl⟩ : syracuseStep 2834455 = 4251683) B4251683
theorem B1769515 : Blo 1768085 1769515 := bstep (se 1 (by rfl) ⟨1327136, by rfl⟩ : syracuseStep 1769515 = 2654273) B2654273
theorem B8953901 : Blo 1768085 8953901 := bstep (se 3 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 8953901 = 3357713) B3357713
theorem B14344237 : Blo 1768085 14344237 := bstep (se 3 (by rfl) ⟨2689544, by rfl⟩ : syracuseStep 14344237 = 5379089) B5379089
theorem B1769527 : Blo 1768085 1769527 := bstep (se 1 (by rfl) ⟨1327145, by rfl⟩ : syracuseStep 1769527 = 2654291) B2654291
theorem B4087883 : Blo 1768085 4087883 := bstep (se 1 (by rfl) ⟨3065912, by rfl⟩ : syracuseStep 4087883 = 6131825) B6131825
theorem B1769547 : Blo 1768085 1769547 := bstep (se 1 (by rfl) ⟨1327160, by rfl⟩ : syracuseStep 1769547 = 2654321) B2654321
theorem B1769559 : Blo 1768085 1769559 := bstep (se 1 (by rfl) ⟨1327169, by rfl⟩ : syracuseStep 1769559 = 2654339) B2654339
theorem B2834519 : Blo 1768085 2834519 := bstep (se 1 (by rfl) ⟨2125889, by rfl⟩ : syracuseStep 2834519 = 4251779) B4251779
theorem B3981401 : Blo 1768085 3981401 := bstep (se 2 (by rfl) ⟨1493025, by rfl⟩ : syracuseStep 3981401 = 2986051) B2986051
theorem B2654297 : Blo 1768085 2654297 := bstep (se 2 (by rfl) ⟨995361, by rfl⟩ : syracuseStep 2654297 = 1990723) B1990723
theorem B1769579 : Blo 1768085 1769579 := bstep (se 1 (by rfl) ⟨1327184, by rfl⟩ : syracuseStep 1769579 = 2654369) B2654369
theorem B1769591 : Blo 1768085 1769591 := bstep (se 1 (by rfl) ⟨1327193, by rfl⟩ : syracuseStep 1769591 = 2654387) B2654387
theorem B1990795 : Blo 1768085 1990795 := bstep (se 1 (by rfl) ⟨1493096, by rfl⟩ : syracuseStep 1990795 = 2986193) B2986193
theorem B1769611 : Blo 1768085 1769611 := bstep (se 1 (by rfl) ⟨1327208, by rfl⟩ : syracuseStep 1769611 = 2654417) B2654417
theorem B1769623 : Blo 1768085 1769623 := bstep (se 1 (by rfl) ⟨1327217, by rfl⟩ : syracuseStep 1769623 = 2654435) B2654435
theorem B6717613 : Blo 1768085 6717613 := bstep (se 3 (by rfl) ⟨1259552, by rfl⟩ : syracuseStep 6717613 = 2519105) B2519105
theorem B1769643 : Blo 1768085 1769643 := bstep (se 1 (by rfl) ⟨1327232, by rfl⟩ : syracuseStep 1769643 = 2654465) B2654465
theorem B3981491 : Blo 1768085 3981491 := bstep (se 1 (by rfl) ⟨2986118, by rfl⟩ : syracuseStep 3981491 = 5972237) B5972237
theorem B1769655 : Blo 1768085 1769655 := bstep (se 1 (by rfl) ⟨1327241, by rfl⟩ : syracuseStep 1769655 = 2654483) B2654483
theorem B16146611 : Blo 1768085 16146611 := bstep (se 1 (by rfl) ⟨12109958, by rfl⟩ : syracuseStep 16146611 = 24219917) B24219917
theorem B2654411 : Blo 1768085 2654411 := bstep (se 1 (by rfl) ⟨1990808, by rfl⟩ : syracuseStep 2654411 = 3981617) B3981617
theorem B1769675 : Blo 1768085 1769675 := bstep (se 1 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 1769675 = 2654513) B2654513
theorem B3981527 : Blo 1768085 3981527 := bstep (se 1 (by rfl) ⟨2986145, by rfl⟩ : syracuseStep 3981527 = 5972291) B5972291
theorem B2654423 : Blo 1768085 2654423 := bstep (se 1 (by rfl) ⟨1990817, by rfl⟩ : syracuseStep 2654423 = 3981635) B3981635
theorem B1769687 : Blo 1768085 1769687 := bstep (se 1 (by rfl) ⟨1327265, by rfl⟩ : syracuseStep 1769687 = 2654531) B2654531
theorem B5038301 : Blo 1768085 5038301 := bstep (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) B1889363
theorem B1769707 : Blo 1768085 1769707 := bstep (se 1 (by rfl) ⟨1327280, by rfl⟩ : syracuseStep 1769707 = 2654561) B2654561
theorem B1990903 : Blo 1768085 1990903 := bstep (se 1 (by rfl) ⟨1493177, by rfl⟩ : syracuseStep 1990903 = 2986355) B2986355
theorem B1769719 : Blo 1768085 1769719 := bstep (se 1 (by rfl) ⟨1327289, by rfl⟩ : syracuseStep 1769719 = 2654579) B2654579
theorem B1769739 : Blo 1768085 1769739 := bstep (se 1 (by rfl) ⟨1327304, by rfl⟩ : syracuseStep 1769739 = 2654609) B2654609
theorem B11338001 : Blo 1768085 11338001 := bstep (se 2 (by rfl) ⟨4251750, by rfl⟩ : syracuseStep 11338001 = 8503501) B8503501
theorem B1769751 : Blo 1768085 1769751 := bstep (se 1 (by rfl) ⟨1327313, by rfl⟩ : syracuseStep 1769751 = 2654627) B2654627
theorem B2654489 : Blo 1768085 2654489 := bstep (se 2 (by rfl) ⟨995433, by rfl⟩ : syracuseStep 2654489 = 1990867) B1990867
theorem B1769771 : Blo 1768085 1769771 := bstep (se 1 (by rfl) ⟨1327328, by rfl⟩ : syracuseStep 1769771 = 2654657) B2654657
theorem B1769783 : Blo 1768085 1769783 := bstep (se 1 (by rfl) ⟨1327337, by rfl⟩ : syracuseStep 1769783 = 2654675) B2654675
theorem B1769803 : Blo 1768085 1769803 := bstep (se 1 (by rfl) ⟨1327352, by rfl⟩ : syracuseStep 1769803 = 2654705) B2654705
theorem B1769815 : Blo 1768085 1769815 := bstep (se 1 (by rfl) ⟨1327361, by rfl⟩ : syracuseStep 1769815 = 2654723) B2654723
theorem B3359065 : Blo 1768085 3359065 := bstep (se 2 (by rfl) ⟨1259649, by rfl⟩ : syracuseStep 3359065 = 2519299) B2519299
theorem B11493733 : Blo 1768085 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B1769835 : Blo 1768085 1769835 := bstep (se 1 (by rfl) ⟨1327376, by rfl⟩ : syracuseStep 1769835 = 2654753) B2654753
theorem B1769847 : Blo 1768085 1769847 := bstep (se 1 (by rfl) ⟨1327385, by rfl⟩ : syracuseStep 1769847 = 2654771) B2654771
theorem B3981707 : Blo 1768085 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B2654603 : Blo 1768085 2654603 := bstep (se 1 (by rfl) ⟨1990952, by rfl⟩ : syracuseStep 2654603 = 3981905) B3981905
theorem B1769867 : Blo 1768085 1769867 := bstep (se 1 (by rfl) ⟨1327400, by rfl⟩ : syracuseStep 1769867 = 2654801) B2654801
theorem B2654615 : Blo 1768085 2654615 := bstep (se 1 (by rfl) ⟨1990961, by rfl⟩ : syracuseStep 2654615 = 3981923) B3981923
theorem B1769879 : Blo 1768085 1769879 := bstep (se 1 (by rfl) ⟨1327409, by rfl⟩ : syracuseStep 1769879 = 2654819) B2654819
theorem B1991083 : Blo 1768085 1991083 := bstep (se 1 (by rfl) ⟨1493312, by rfl⟩ : syracuseStep 1991083 = 2986625) B2986625
theorem B1769899 : Blo 1768085 1769899 := bstep (se 1 (by rfl) ⟨1327424, by rfl⟩ : syracuseStep 1769899 = 2654849) B2654849
theorem B1769911 : Blo 1768085 1769911 := bstep (se 1 (by rfl) ⟨1327433, by rfl⟩ : syracuseStep 1769911 = 2654867) B2654867
theorem B3981761 : Blo 1768085 3981761 := bstep (se 2 (by rfl) ⟨1493160, by rfl⟩ : syracuseStep 3981761 = 2986321) B2986321
theorem B6373835 : Blo 1768085 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B1769931 : Blo 1768085 1769931 := bstep (se 1 (by rfl) ⟨1327448, by rfl⟩ : syracuseStep 1769931 = 2654897) B2654897
theorem B1769943 : Blo 1768085 1769943 := bstep (se 1 (by rfl) ⟨1327457, by rfl⟩ : syracuseStep 1769943 = 2654915) B2654915
theorem B2654681 : Blo 1768085 2654681 := bstep (se 2 (by rfl) ⟨995505, by rfl⟩ : syracuseStep 2654681 = 1991011) B1991011
theorem B6717917 : Blo 1768085 6717917 := bstep (se 3 (by rfl) ⟨1259609, by rfl⟩ : syracuseStep 6717917 = 2519219) B2519219
theorem B1769963 : Blo 1768085 1769963 := bstep (se 1 (by rfl) ⟨1327472, by rfl⟩ : syracuseStep 1769963 = 2654945) B2654945
theorem B1769975 : Blo 1768085 1769975 := bstep (se 1 (by rfl) ⟨1327481, by rfl⟩ : syracuseStep 1769975 = 2654963) B2654963
theorem B1769995 : Blo 1768085 1769995 := bstep (se 1 (by rfl) ⟨1327496, by rfl⟩ : syracuseStep 1769995 = 2654993) B2654993
theorem B1991191 : Blo 1768085 1991191 := bstep (se 1 (by rfl) ⟨1493393, by rfl⟩ : syracuseStep 1991191 = 2986787) B2986787
theorem B1770007 : Blo 1768085 1770007 := bstep (se 1 (by rfl) ⟨1327505, by rfl⟩ : syracuseStep 1770007 = 2655011) B2655011
theorem B1770027 : Blo 1768085 1770027 := bstep (se 1 (by rfl) ⟨1327520, by rfl⟩ : syracuseStep 1770027 = 2655041) B2655041
theorem B1770039 : Blo 1768085 1770039 := bstep (se 1 (by rfl) ⟨1327529, by rfl⟩ : syracuseStep 1770039 = 2655059) B2655059
theorem B2654795 : Blo 1768085 2654795 := bstep (se 1 (by rfl) ⟨1991096, by rfl⟩ : syracuseStep 2654795 = 3982193) B3982193
theorem B1770059 : Blo 1768085 1770059 := bstep (se 1 (by rfl) ⟨1327544, by rfl⟩ : syracuseStep 1770059 = 2655089) B2655089
theorem B2654807 : Blo 1768085 2654807 := bstep (se 1 (by rfl) ⟨1991105, by rfl⟩ : syracuseStep 2654807 = 3982211) B3982211
theorem B1770071 : Blo 1768085 1770071 := bstep (se 1 (by rfl) ⟨1327553, by rfl⟩ : syracuseStep 1770071 = 2655107) B2655107
theorem B3981977 : Blo 1768085 3981977 := bstep (se 2 (by rfl) ⟨1493241, by rfl⟩ : syracuseStep 3981977 = 2986483) B2986483
theorem B2654873 : Blo 1768085 2654873 := bstep (se 2 (by rfl) ⟨995577, by rfl⟩ : syracuseStep 2654873 = 1991155) B1991155
theorem B3982067 : Blo 1768085 3982067 := bstep (se 1 (by rfl) ⟨2986550, by rfl⟩ : syracuseStep 3982067 = 5973101) B5973101
theorem B2654987 : Blo 1768085 2654987 := bstep (se 1 (by rfl) ⟨1991240, by rfl⟩ : syracuseStep 2654987 = 3982481) B3982481
theorem B3982103 : Blo 1768085 3982103 := bstep (se 1 (by rfl) ⟨2986577, by rfl⟩ : syracuseStep 3982103 = 5973155) B5973155
theorem B2654999 : Blo 1768085 2654999 := bstep (se 1 (by rfl) ⟨1991249, by rfl⟩ : syracuseStep 2654999 = 3982499) B3982499
theorem B6374209 : Blo 1768085 6374209 := bstep (se 2 (by rfl) ⟨2390328, by rfl⟩ : syracuseStep 6374209 = 4780657) B4780657
theorem B2655065 : Blo 1768085 2655065 := bstep (se 2 (by rfl) ⟨995649, by rfl⟩ : syracuseStep 2655065 = 1991299) B1991299
theorem B7168861 : Blo 1768085 7168861 := bstep (se 3 (by rfl) ⟨1344161, by rfl⟩ : syracuseStep 7168861 = 2688323) B2688323
theorem B7373699 : Blo 1768085 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B3359627 : Blo 1768085 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B6218689 : Blo 1768085 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B5972939 : Blo 1768085 5972939 := bstep (se 1 (by rfl) ⟨4479704, by rfl⟩ : syracuseStep 5972939 = 8959409) B8959409
theorem B3982283 : Blo 1768085 3982283 := bstep (se 1 (by rfl) ⟨2986712, by rfl⟩ : syracuseStep 3982283 = 5973425) B5973425
theorem B3982337 : Blo 1768085 3982337 := bstep (se 2 (by rfl) ⟨1493376, by rfl⟩ : syracuseStep 3982337 = 2986753) B2986753
theorem B3359809 : Blo 1768085 3359809 := bstep (se 2 (by rfl) ⟨1259928, by rfl⟩ : syracuseStep 3359809 = 2519857) B2519857
theorem B15107249 : Blo 1768085 15107249 := bstep (se 2 (by rfl) ⟨5665218, by rfl⟩ : syracuseStep 15107249 = 11330437) B11330437
theorem B12747955 : Blo 1768085 12747955 := bstep (se 1 (by rfl) ⟨9560966, by rfl⟩ : syracuseStep 12747955 = 19121933) B19121933
theorem B5973209 : Blo 1768085 5973209 := bstep (se 2 (by rfl) ⟨2239953, by rfl⟩ : syracuseStep 5973209 = 4479907) B4479907
theorem B3982553 : Blo 1768085 3982553 := bstep (se 2 (by rfl) ⟨1493457, by rfl⟩ : syracuseStep 3982553 = 2986915) B2986915
theorem B3982643 : Blo 1768085 3982643 := bstep (se 1 (by rfl) ⟨2986982, by rfl⟩ : syracuseStep 3982643 = 5973965) B5973965
theorem B3982679 : Blo 1768085 3982679 := bstep (se 1 (by rfl) ⟨2987009, by rfl⟩ : syracuseStep 3982679 = 5974019) B5974019
theorem B6374987 : Blo 1768085 6374987 := bstep (se 1 (by rfl) ⟨4781240, by rfl⟩ : syracuseStep 6374987 = 9562481) B9562481
theorem B9561701 : Blo 1768085 9561701 := bstep (se 4 (by rfl) ⟨896409, by rfl⟩ : syracuseStep 9561701 = 1792819) B1792819
theorem B3778265 : Blo 1768085 3778265 := bstep (se 2 (by rfl) ⟨1416849, by rfl⟩ : syracuseStep 3778265 = 2833699) B2833699
theorem B12748589 : Blo 1768085 12748589 := bstep (se 3 (by rfl) ⟨2390360, by rfl⟩ : syracuseStep 12748589 = 4780721) B4780721
theorem B3188531 : Blo 1768085 3188531 := bstep (se 1 (by rfl) ⟨2391398, by rfl⟩ : syracuseStep 3188531 = 4782797) B4782797
theorem B2238283 : Blo 1768085 2238283 := bstep (se 1 (by rfl) ⟨1678712, by rfl⟩ : syracuseStep 2238283 = 3357425) B3357425
theorem B5973911 : Blo 1768085 5973911 := bstep (se 1 (by rfl) ⟨4480433, by rfl⟩ : syracuseStep 5973911 = 8960867) B8960867
theorem B12756953 : Blo 1768085 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B6637571 : Blo 1768085 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B29067281 : Blo 1768085 29067281 := bstep (se 2 (by rfl) ⟨10900230, by rfl⟩ : syracuseStep 29067281 = 21800461) B21800461
theorem B34015301 : Blo 1768085 34015301 := bstep (se 4 (by rfl) ⟨3188934, by rfl⟩ : syracuseStep 34015301 = 6377869) B6377869
theorem B2984087 : Blo 1768085 2984087 := bstep (se 1 (by rfl) ⟨2238065, by rfl⟩ : syracuseStep 2984087 = 4476131) B4476131
theorem B7555265 : Blo 1768085 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B3188929 : Blo 1768085 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B2984215 : Blo 1768085 2984215 := bstep (se 1 (by rfl) ⟨2238161, by rfl⟩ : syracuseStep 2984215 = 4476323) B4476323
theorem B3189079 : Blo 1768085 3189079 := bstep (se 1 (by rfl) ⟨2391809, by rfl⟩ : syracuseStep 3189079 = 4783619) B4783619
theorem B14535013 : Blo 1768085 14535013 := bstep (se 4 (by rfl) ⟨1362657, by rfl⟩ : syracuseStep 14535013 = 2725315) B2725315
theorem B3778931 : Blo 1768085 3778931 := bstep (se 1 (by rfl) ⟨2834198, by rfl⟩ : syracuseStep 3778931 = 5668397) B5668397
theorem B10218059 : Blo 1768085 10218059 := bstep (se 1 (by rfl) ⟨7663544, by rfl⟩ : syracuseStep 10218059 = 15327089) B15327089
theorem B9693827 : Blo 1768085 9693827 := bstep (se 1 (by rfl) ⟨7270370, by rfl⟩ : syracuseStep 9693827 = 14540741) B14540741
theorem B2239255 : Blo 1768085 2239255 := bstep (se 1 (by rfl) ⟨1679441, by rfl⟩ : syracuseStep 2239255 = 3358883) B3358883
theorem B3189527 : Blo 1768085 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B2984843 : Blo 1768085 2984843 := bstep (se 1 (by rfl) ⟨2238632, by rfl⟩ : syracuseStep 2984843 = 4477265) B4477265
theorem B6720515 : Blo 1768085 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B2984971 : Blo 1768085 2984971 := bstep (se 1 (by rfl) ⟨2238728, by rfl⟩ : syracuseStep 2984971 = 4477457) B4477457
theorem B6720529 : Blo 1768085 6720529 := bstep (se 2 (by rfl) ⟨2520198, by rfl⟩ : syracuseStep 6720529 = 5040397) B5040397
theorem B4475969 : Blo 1768085 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B28691587 : Blo 1768085 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B2985113 : Blo 1768085 2985113 := bstep (se 2 (by rfl) ⟨1119417, by rfl⟩ : syracuseStep 2985113 = 2238835) B2238835
theorem B2985241 : Blo 1768085 2985241 := bstep (se 2 (by rfl) ⟨1119465, by rfl⟩ : syracuseStep 2985241 = 2238931) B2238931
theorem B19123573 : Blo 1768085 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B2125207 : Blo 1768085 2125207 := bstep (se 1 (by rfl) ⟨1593905, by rfl⟩ : syracuseStep 2125207 = 3187811) B3187811
theorem B13438385 : Blo 1768085 13438385 := bstep (se 2 (by rfl) ⟨5039394, by rfl⟩ : syracuseStep 13438385 = 10078789) B10078789
theorem B4779467 : Blo 1768085 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B2518553 : Blo 1768085 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B2240075 : Blo 1768085 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B4476505 : Blo 1768085 4476505 := bstep (se 2 (by rfl) ⟨1678689, by rfl⟩ : syracuseStep 4476505 = 3357379) B3357379
theorem B7556753 : Blo 1768085 7556753 := bstep (se 2 (by rfl) ⟨2833782, by rfl⟩ : syracuseStep 7556753 = 5667565) B5667565
theorem B5967539 : Blo 1768085 5967539 := bstep (se 1 (by rfl) ⟨4475654, by rfl⟩ : syracuseStep 5967539 = 8951309) B8951309
theorem B10080065 : Blo 1768085 10080065 := bstep (se 2 (by rfl) ⟨3780024, by rfl⟩ : syracuseStep 10080065 = 7560049) B7560049
theorem B3780427 : Blo 1768085 3780427 := bstep (se 1 (by rfl) ⟨2835320, by rfl⟩ : syracuseStep 3780427 = 5670641) B5670641
theorem B2985815 : Blo 1768085 2985815 := bstep (se 1 (by rfl) ⟨2239361, by rfl⟩ : syracuseStep 2985815 = 4478723) B4478723
theorem B4034393 : Blo 1768085 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B8957789 : Blo 1768085 8957789 := bstep (se 3 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 8957789 = 3359171) B3359171
theorem B12930947 : Blo 1768085 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B6713239 : Blo 1768085 6713239 := bstep (se 1 (by rfl) ⟨5034929, by rfl⟩ : syracuseStep 6713239 = 10069859) B10069859
theorem B13438871 : Blo 1768085 13438871 := bstep (se 1 (by rfl) ⟨10079153, by rfl⟩ : syracuseStep 13438871 = 20158307) B20158307
theorem B6377395 : Blo 1768085 6377395 := bstep (se 1 (by rfl) ⟨4783046, by rfl⟩ : syracuseStep 6377395 = 9566093) B9566093
theorem B5967809 : Blo 1768085 5967809 := bstep (se 2 (by rfl) ⟨2237928, by rfl⟩ : syracuseStep 5967809 = 4475857) B4475857
theorem B2985943 : Blo 1768085 2985943 := bstep (se 1 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 2985943 = 4478915) B4478915
theorem B10072025 : Blo 1768085 10072025 := bstep (se 2 (by rfl) ⟨3777009, by rfl⟩ : syracuseStep 10072025 = 7554019) B7554019
theorem B2519191 : Blo 1768085 2519191 := bstep (se 1 (by rfl) ⟨1889393, by rfl⟩ : syracuseStep 2519191 = 3778787) B3778787
theorem B16134349 : Blo 1768085 16134349 := bstep (se 3 (by rfl) ⟨3025190, by rfl⟩ : syracuseStep 16134349 = 6050381) B6050381
theorem B1888471 : Blo 1768085 1888471 := bstep (se 1 (by rfl) ⟨1416353, by rfl⟩ : syracuseStep 1888471 = 2832707) B2832707
theorem B20156849 : Blo 1768085 20156849 := bstep (se 2 (by rfl) ⟨7558818, by rfl⟩ : syracuseStep 20156849 = 15117637) B15117637
theorem B4780505 : Blo 1768085 4780505 := bstep (se 2 (by rfl) ⟨1792689, by rfl⟩ : syracuseStep 4780505 = 3585379) B3585379
theorem B5968349 : Blo 1768085 5968349 := bstep (se 3 (by rfl) ⟨1119065, by rfl⟩ : syracuseStep 5968349 = 2238131) B2238131
theorem B2986571 : Blo 1768085 2986571 := bstep (se 1 (by rfl) ⟨2239928, by rfl⟩ : syracuseStep 2986571 = 4479857) B4479857
theorem B5665373 : Blo 1768085 5665373 := bstep (se 3 (by rfl) ⟨1062257, by rfl⟩ : syracuseStep 5665373 = 2124515) B2124515
theorem B5378653 : Blo 1768085 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B7557725 : Blo 1768085 7557725 := bstep (se 3 (by rfl) ⟨1417073, by rfl⟩ : syracuseStep 7557725 = 2834147) B2834147
theorem B6714029 : Blo 1768085 6714029 := bstep (se 3 (by rfl) ⟨1258880, by rfl⟩ : syracuseStep 6714029 = 2517761) B2517761
theorem B4477619 : Blo 1768085 4477619 := bstep (se 1 (by rfl) ⟨3358214, by rfl⟩ : syracuseStep 4477619 = 6716429) B6716429
theorem B2986699 : Blo 1768085 2986699 := bstep (se 1 (by rfl) ⟨2240024, by rfl⟩ : syracuseStep 2986699 = 4480049) B4480049
theorem B15110873 : Blo 1768085 15110873 := bstep (se 2 (by rfl) ⟨5666577, by rfl⟩ : syracuseStep 15110873 = 11333155) B11333155
theorem B2986841 : Blo 1768085 2986841 := bstep (se 2 (by rfl) ⟨1120065, by rfl⟩ : syracuseStep 2986841 = 2240131) B2240131
theorem B2520011 : Blo 1768085 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B4477913 : Blo 1768085 4477913 := bstep (se 2 (by rfl) ⟨1679217, by rfl⟩ : syracuseStep 4477913 = 3358435) B3358435
theorem B2986969 : Blo 1768085 2986969 := bstep (se 2 (by rfl) ⟨1120113, by rfl⟩ : syracuseStep 2986969 = 2240227) B2240227
theorem B3978251 : Blo 1768085 3978251 := bstep (se 1 (by rfl) ⟨2983688, by rfl⟩ : syracuseStep 3978251 = 5967377) B5967377
theorem B1889291 : Blo 1768085 1889291 := bstep (se 1 (by rfl) ⟨1416968, by rfl⟩ : syracuseStep 1889291 = 2833937) B2833937
theorem B3978305 : Blo 1768085 3978305 := bstep (se 2 (by rfl) ⟨1491864, by rfl⟩ : syracuseStep 3978305 = 2983729) B2983729
theorem B27972701 : Blo 1768085 27972701 := bstep (se 3 (by rfl) ⟨5244881, by rfl⟩ : syracuseStep 27972701 = 10489763) B10489763
theorem B1913963 : Blo 1768085 1913963 := bstep (se 1 (by rfl) ⟨1435472, by rfl⟩ : syracuseStep 1913963 = 2870945) B2870945
theorem B3585217 : Blo 1768085 3585217 := bstep (se 2 (by rfl) ⟨1344456, by rfl⟩ : syracuseStep 3585217 = 2688913) B2688913
theorem B15119621 : Blo 1768085 15119621 := bstep (se 4 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 15119621 = 2834929) B2834929
theorem B3978521 : Blo 1768085 3978521 := bstep (se 2 (by rfl) ⟨1491945, by rfl⟩ : syracuseStep 3978521 = 2983891) B2983891
theorem B12105035 : Blo 1768085 12105035 := bstep (se 1 (by rfl) ⟨9078776, by rfl⟩ : syracuseStep 12105035 = 18157553) B18157553
theorem B3978611 : Blo 1768085 3978611 := bstep (se 1 (by rfl) ⟨2983958, by rfl⟩ : syracuseStep 3978611 = 5967917) B5967917
theorem B3978647 : Blo 1768085 3978647 := bstep (se 1 (by rfl) ⟨2983985, by rfl⟩ : syracuseStep 3978647 = 5967971) B5967971
theorem B12752279 : Blo 1768085 12752279 := bstep (se 1 (by rfl) ⟨9564209, by rfl⟩ : syracuseStep 12752279 = 19128419) B19128419
theorem B3978827 : Blo 1768085 3978827 := bstep (se 1 (by rfl) ⟨2984120, by rfl⟩ : syracuseStep 3978827 = 5968241) B5968241
theorem B5969483 : Blo 1768085 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B3978881 : Blo 1768085 3978881 := bstep (se 2 (by rfl) ⟨1492080, by rfl⟩ : syracuseStep 3978881 = 2984161) B2984161
theorem B25491125 : Blo 1768085 25491125 := bstep (se 5 (by rfl) ⟨1194896, by rfl⟩ : syracuseStep 25491125 = 2389793) B2389793
theorem B48420557 : Blo 1768085 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B5035841 : Blo 1768085 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B3979097 : Blo 1768085 3979097 := bstep (se 2 (by rfl) ⟨1492161, by rfl⟩ : syracuseStep 3979097 = 2984323) B2984323
theorem B5969753 : Blo 1768085 5969753 := bstep (se 2 (by rfl) ⟨2238657, by rfl⟩ : syracuseStep 5969753 = 4477315) B4477315
theorem B73611109 : Blo 1768085 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B7272337 : Blo 1768085 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B8959895 : Blo 1768085 8959895 := bstep (se 1 (by rfl) ⟨6719921, by rfl⟩ : syracuseStep 8959895 = 13439843) B13439843
theorem B3979187 : Blo 1768085 3979187 := bstep (se 1 (by rfl) ⟨2984390, by rfl⟩ : syracuseStep 3979187 = 5968781) B5968781
theorem B1769463 : Blo 1768085 1769463 := bstep (se 1 (by rfl) ⟨1327097, by rfl⟩ : syracuseStep 1769463 = 2654195) B2654195
theorem B3979223 : Blo 1768085 3979223 := bstep (se 1 (by rfl) ⟨2984417, by rfl⟩ : syracuseStep 3979223 = 5968835) B5968835
theorem B2652185 : Blo 1768085 2652185 := bstep (se 2 (by rfl) ⟨994569, by rfl⟩ : syracuseStep 2652185 = 1989139) B1989139
theorem B6715457 : Blo 1768085 6715457 := bstep (se 2 (by rfl) ⟨2518296, by rfl⟩ : syracuseStep 6715457 = 5036593) B5036593
theorem B15325249 : Blo 1768085 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B4249675 : Blo 1768085 4249675 := bstep (se 1 (by rfl) ⟨3187256, by rfl⟩ : syracuseStep 4249675 = 6374513) B6374513
theorem B2652299 : Blo 1768085 2652299 := bstep (se 1 (by rfl) ⟨1989224, by rfl⟩ : syracuseStep 2652299 = 3978449) B3978449
theorem B3979403 : Blo 1768085 3979403 := bstep (se 1 (by rfl) ⟨2984552, by rfl⟩ : syracuseStep 3979403 = 5969105) B5969105
theorem B2652311 : Blo 1768085 2652311 := bstep (se 1 (by rfl) ⟨1989233, by rfl⟩ : syracuseStep 2652311 = 3978467) B3978467
theorem B4249751 : Blo 1768085 4249751 := bstep (se 1 (by rfl) ⟨3187313, by rfl⟩ : syracuseStep 4249751 = 6374627) B6374627
theorem B3979457 : Blo 1768085 3979457 := bstep (se 2 (by rfl) ⟨1492296, by rfl⟩ : syracuseStep 3979457 = 2984593) B2984593
theorem B7272641 : Blo 1768085 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B2652377 : Blo 1768085 2652377 := bstep (se 2 (by rfl) ⟨994641, by rfl⟩ : syracuseStep 2652377 = 1989283) B1989283
theorem B3356939 : Blo 1768085 3356939 := bstep (se 1 (by rfl) ⟨2517704, by rfl⟩ : syracuseStep 3356939 = 5035409) B5035409
theorem B2652491 : Blo 1768085 2652491 := bstep (se 1 (by rfl) ⟨1989368, by rfl⟩ : syracuseStep 2652491 = 3978737) B3978737
theorem B2652503 : Blo 1768085 2652503 := bstep (se 1 (by rfl) ⟨1989377, by rfl⟩ : syracuseStep 2652503 = 3978755) B3978755
theorem B5036377 : Blo 1768085 5036377 := bstep (se 2 (by rfl) ⟨1888641, by rfl⟩ : syracuseStep 5036377 = 3777283) B3777283
theorem B2652569 : Blo 1768085 2652569 := bstep (se 2 (by rfl) ⟨994713, by rfl⟩ : syracuseStep 2652569 = 1989427) B1989427
theorem B3979673 : Blo 1768085 3979673 := bstep (se 2 (by rfl) ⟨1492377, by rfl⟩ : syracuseStep 3979673 = 2984755) B2984755
theorem B3357121 : Blo 1768085 3357121 := bstep (se 2 (by rfl) ⟨1258920, by rfl⟩ : syracuseStep 3357121 = 2517841) B2517841
theorem B8952281 : Blo 1768085 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B3979763 : Blo 1768085 3979763 := bstep (se 1 (by rfl) ⟨2984822, by rfl⟩ : syracuseStep 3979763 = 5969645) B5969645
theorem B2652683 : Blo 1768085 2652683 := bstep (se 1 (by rfl) ⟨1989512, by rfl⟩ : syracuseStep 2652683 = 3979025) B3979025
theorem B2652695 : Blo 1768085 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B3979799 : Blo 1768085 3979799 := bstep (se 1 (by rfl) ⟨2984849, by rfl⟩ : syracuseStep 3979799 = 5969699) B5969699
theorem B5970455 : Blo 1768085 5970455 := bstep (se 1 (by rfl) ⟨4477841, by rfl⟩ : syracuseStep 5970455 = 8955683) B8955683
theorem B1989175 : Blo 1768085 1989175 := bstep (se 1 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 1989175 = 2983763) B2983763
theorem B10074689 : Blo 1768085 10074689 := bstep (se 2 (by rfl) ⟨3778008, by rfl⟩ : syracuseStep 10074689 = 7556017) B7556017
theorem B4479563 : Blo 1768085 4479563 := bstep (se 1 (by rfl) ⟨3359672, by rfl⟩ : syracuseStep 4479563 = 6719345) B6719345
theorem B2652761 : Blo 1768085 2652761 := bstep (se 2 (by rfl) ⟨994785, by rfl⟩ : syracuseStep 2652761 = 1989571) B1989571
theorem B1915531 : Blo 1768085 1915531 := bstep (se 1 (by rfl) ⟨1436648, by rfl⟩ : syracuseStep 1915531 = 2873297) B2873297
theorem B1768087 : Blo 1768085 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B1768107 : Blo 1768085 1768107 := bstep (se 1 (by rfl) ⟨1326080, by rfl⟩ : syracuseStep 1768107 = 2652161) B2652161
theorem B1768119 : Blo 1768085 1768119 := bstep (se 1 (by rfl) ⟨1326089, by rfl⟩ : syracuseStep 1768119 = 2652179) B2652179
theorem B1768139 : Blo 1768085 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B2652875 : Blo 1768085 2652875 := bstep (se 1 (by rfl) ⟨1989656, by rfl⟩ : syracuseStep 2652875 = 3979313) B3979313
theorem B3979979 : Blo 1768085 3979979 := bstep (se 1 (by rfl) ⟨2984984, by rfl⟩ : syracuseStep 3979979 = 5969969) B5969969
theorem B1768151 : Blo 1768085 1768151 := bstep (se 1 (by rfl) ⟨1326113, by rfl⟩ : syracuseStep 1768151 = 2652227) B2652227
theorem B2652887 : Blo 1768085 2652887 := bstep (se 1 (by rfl) ⟨1989665, by rfl⟩ : syracuseStep 2652887 = 3979331) B3979331
theorem B1768171 : Blo 1768085 1768171 := bstep (se 1 (by rfl) ⟨1326128, by rfl⟩ : syracuseStep 1768171 = 2652257) B2652257
theorem B1989355 : Blo 1768085 1989355 := bstep (se 1 (by rfl) ⟨1492016, by rfl⟩ : syracuseStep 1989355 = 2984033) B2984033
theorem B1768183 : Blo 1768085 1768183 := bstep (se 1 (by rfl) ⟨1326137, by rfl⟩ : syracuseStep 1768183 = 2652275) B2652275
theorem B3980033 : Blo 1768085 3980033 := bstep (se 2 (by rfl) ⟨1492512, by rfl⟩ : syracuseStep 3980033 = 2985025) B2985025
theorem B1768203 : Blo 1768085 1768203 := bstep (se 1 (by rfl) ⟨1326152, by rfl⟩ : syracuseStep 1768203 = 2652305) B2652305
theorem B16136977 : Blo 1768085 16136977 := bstep (se 2 (by rfl) ⟨6051366, by rfl⟩ : syracuseStep 16136977 = 12102733) B12102733
theorem B1768215 : Blo 1768085 1768215 := bstep (se 1 (by rfl) ⟨1326161, by rfl⟩ : syracuseStep 1768215 = 2652323) B2652323
theorem B3357463 : Blo 1768085 3357463 := bstep (se 1 (by rfl) ⟨2518097, by rfl⟩ : syracuseStep 3357463 = 5036195) B5036195
theorem B2652953 : Blo 1768085 2652953 := bstep (se 2 (by rfl) ⟨994857, by rfl⟩ : syracuseStep 2652953 = 1989715) B1989715
theorem B1768235 : Blo 1768085 1768235 := bstep (se 1 (by rfl) ⟨1326176, by rfl⟩ : syracuseStep 1768235 = 2652353) B2652353
theorem B1768247 : Blo 1768085 1768247 := bstep (se 1 (by rfl) ⟨1326185, by rfl⟩ : syracuseStep 1768247 = 2652371) B2652371
theorem B310057793 : Blo 1768085 310057793 := bstep (se 2 (by rfl) ⟨116271672, by rfl⟩ : syracuseStep 310057793 = 232543345) B232543345
theorem B1768267 : Blo 1768085 1768267 := bstep (se 1 (by rfl) ⟨1326200, by rfl⟩ : syracuseStep 1768267 = 2652401) B2652401
theorem B5380939 : Blo 1768085 5380939 := bstep (se 1 (by rfl) ⟨4035704, by rfl⟩ : syracuseStep 5380939 = 8071409) B8071409
theorem B1768279 : Blo 1768085 1768279 := bstep (se 1 (by rfl) ⟨1326209, by rfl⟩ : syracuseStep 1768279 = 2652419) B2652419
theorem B1989463 : Blo 1768085 1989463 := bstep (se 1 (by rfl) ⟨1492097, by rfl⟩ : syracuseStep 1989463 = 2984195) B2984195
theorem B1768299 : Blo 1768085 1768299 := bstep (se 1 (by rfl) ⟨1326224, by rfl⟩ : syracuseStep 1768299 = 2652449) B2652449
theorem B1768311 : Blo 1768085 1768311 := bstep (se 1 (by rfl) ⟨1326233, by rfl⟩ : syracuseStep 1768311 = 2652467) B2652467
theorem B1768331 : Blo 1768085 1768331 := bstep (se 1 (by rfl) ⟨1326248, by rfl⟩ : syracuseStep 1768331 = 2652497) B2652497
theorem B2653067 : Blo 1768085 2653067 := bstep (se 1 (by rfl) ⟨1989800, by rfl⟩ : syracuseStep 2653067 = 3979601) B3979601
theorem B1768343 : Blo 1768085 1768343 := bstep (se 1 (by rfl) ⟨1326257, by rfl⟩ : syracuseStep 1768343 = 2652515) B2652515
theorem B2653079 : Blo 1768085 2653079 := bstep (se 1 (by rfl) ⟨1989809, by rfl⟩ : syracuseStep 2653079 = 3979619) B3979619
theorem B4848535 : Blo 1768085 4848535 := bstep (se 1 (by rfl) ⟨3636401, by rfl⟩ : syracuseStep 4848535 = 7272803) B7272803
theorem B1768363 : Blo 1768085 1768363 := bstep (se 1 (by rfl) ⟨1326272, by rfl⟩ : syracuseStep 1768363 = 2652545) B2652545
theorem B1768375 : Blo 1768085 1768375 := bstep (se 1 (by rfl) ⟨1326281, by rfl⟩ : syracuseStep 1768375 = 2652563) B2652563
theorem B1768395 : Blo 1768085 1768395 := bstep (se 1 (by rfl) ⟨1326296, by rfl⟩ : syracuseStep 1768395 = 2652593) B2652593
theorem B1768407 : Blo 1768085 1768407 := bstep (se 1 (by rfl) ⟨1326305, by rfl⟩ : syracuseStep 1768407 = 2652611) B2652611
theorem B2653145 : Blo 1768085 2653145 := bstep (se 2 (by rfl) ⟨994929, by rfl⟩ : syracuseStep 2653145 = 1989859) B1989859
theorem B3980249 : Blo 1768085 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B1768427 : Blo 1768085 1768427 := bstep (se 1 (by rfl) ⟨1326320, by rfl⟩ : syracuseStep 1768427 = 2652641) B2652641
theorem B3357683 : Blo 1768085 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B1768439 : Blo 1768085 1768439 := bstep (se 1 (by rfl) ⟨1326329, by rfl⟩ : syracuseStep 1768439 = 2652659) B2652659
theorem B1768459 : Blo 1768085 1768459 := bstep (se 1 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 1768459 = 2652689) B2652689
theorem B1989643 : Blo 1768085 1989643 := bstep (se 1 (by rfl) ⟨1492232, by rfl⟩ : syracuseStep 1989643 = 2984465) B2984465
theorem B1768471 : Blo 1768085 1768471 := bstep (se 1 (by rfl) ⟨1326353, by rfl⟩ : syracuseStep 1768471 = 2652707) B2652707
theorem B1768491 : Blo 1768085 1768491 := bstep (se 1 (by rfl) ⟨1326368, by rfl⟩ : syracuseStep 1768491 = 2652737) B2652737
theorem B3980339 : Blo 1768085 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B5970995 : Blo 1768085 5970995 := bstep (se 1 (by rfl) ⟨4478246, by rfl⟩ : syracuseStep 5970995 = 8956493) B8956493
theorem B1768503 : Blo 1768085 1768503 := bstep (se 1 (by rfl) ⟨1326377, by rfl⟩ : syracuseStep 1768503 = 2652755) B2652755
theorem B1768523 : Blo 1768085 1768523 := bstep (se 1 (by rfl) ⟨1326392, by rfl⟩ : syracuseStep 1768523 = 2652785) B2652785
theorem B2653259 : Blo 1768085 2653259 := bstep (se 1 (by rfl) ⟨1989944, by rfl⟩ : syracuseStep 2653259 = 3979889) B3979889
theorem B1768535 : Blo 1768085 1768535 := bstep (se 1 (by rfl) ⟨1326401, by rfl⟩ : syracuseStep 1768535 = 2652803) B2652803
theorem B2653271 : Blo 1768085 2653271 := bstep (se 1 (by rfl) ⟨1989953, by rfl⟩ : syracuseStep 2653271 = 3979907) B3979907
theorem B3980375 : Blo 1768085 3980375 := bstep (se 1 (by rfl) ⟨2985281, by rfl⟩ : syracuseStep 3980375 = 5970563) B5970563
theorem B1768555 : Blo 1768085 1768555 := bstep (se 1 (by rfl) ⟨1326416, by rfl⟩ : syracuseStep 1768555 = 2652833) B2652833
theorem B1768567 : Blo 1768085 1768567 := bstep (se 1 (by rfl) ⟨1326425, by rfl⟩ : syracuseStep 1768567 = 2652851) B2652851
theorem B1989751 : Blo 1768085 1989751 := bstep (se 1 (by rfl) ⟨1492313, by rfl⟩ : syracuseStep 1989751 = 2984627) B2984627
theorem B7560323 : Blo 1768085 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B1768587 : Blo 1768085 1768587 := bstep (se 1 (by rfl) ⟨1326440, by rfl⟩ : syracuseStep 1768587 = 2652881) B2652881
theorem B1768599 : Blo 1768085 1768599 := bstep (se 1 (by rfl) ⟨1326449, by rfl⟩ : syracuseStep 1768599 = 2652899) B2652899
theorem B2653337 : Blo 1768085 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B1768619 : Blo 1768085 1768619 := bstep (se 1 (by rfl) ⟨1326464, by rfl⟩ : syracuseStep 1768619 = 2652929) B2652929
theorem B1768631 : Blo 1768085 1768631 := bstep (se 1 (by rfl) ⟨1326473, by rfl⟩ : syracuseStep 1768631 = 2652947) B2652947
theorem B1768651 : Blo 1768085 1768651 := bstep (se 1 (by rfl) ⟨1326488, by rfl⟩ : syracuseStep 1768651 = 2652977) B2652977
theorem B1768663 : Blo 1768085 1768663 := bstep (se 1 (by rfl) ⟨1326497, by rfl⟩ : syracuseStep 1768663 = 2652995) B2652995
theorem B3357911 : Blo 1768085 3357911 := bstep (se 1 (by rfl) ⟨2518433, by rfl⟩ : syracuseStep 3357911 = 5036867) B5036867
theorem B1768683 : Blo 1768085 1768683 := bstep (se 1 (by rfl) ⟨1326512, by rfl⟩ : syracuseStep 1768683 = 2653025) B2653025
theorem B1768695 : Blo 1768085 1768695 := bstep (se 1 (by rfl) ⟨1326521, by rfl⟩ : syracuseStep 1768695 = 2653043) B2653043
theorem B1768715 : Blo 1768085 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B2653451 : Blo 1768085 2653451 := bstep (se 1 (by rfl) ⟨1990088, by rfl⟩ : syracuseStep 2653451 = 3980177) B3980177
theorem B3980555 : Blo 1768085 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B1768727 : Blo 1768085 1768727 := bstep (se 1 (by rfl) ⟨1326545, by rfl⟩ : syracuseStep 1768727 = 2653091) B2653091
theorem B2653463 : Blo 1768085 2653463 := bstep (se 1 (by rfl) ⟨1990097, by rfl⟩ : syracuseStep 2653463 = 3980195) B3980195
theorem B1768747 : Blo 1768085 1768747 := bstep (se 1 (by rfl) ⟨1326560, by rfl⟩ : syracuseStep 1768747 = 2653121) B2653121
theorem B1989931 : Blo 1768085 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B1768759 : Blo 1768085 1768759 := bstep (se 1 (by rfl) ⟨1326569, by rfl⟩ : syracuseStep 1768759 = 2653139) B2653139
theorem B15113537 : Blo 1768085 15113537 := bstep (se 2 (by rfl) ⟨5667576, by rfl⟩ : syracuseStep 15113537 = 11335153) B11335153
theorem B3980609 : Blo 1768085 3980609 := bstep (se 2 (by rfl) ⟨1492728, by rfl⟩ : syracuseStep 3980609 = 2985457) B2985457
theorem B5971265 : Blo 1768085 5971265 := bstep (se 2 (by rfl) ⟨2239224, by rfl⟩ : syracuseStep 5971265 = 4478449) B4478449
theorem B1768779 : Blo 1768085 1768779 := bstep (se 1 (by rfl) ⟨1326584, by rfl⟩ : syracuseStep 1768779 = 2653169) B2653169
theorem B1768791 : Blo 1768085 1768791 := bstep (se 1 (by rfl) ⟨1326593, by rfl⟩ : syracuseStep 1768791 = 2653187) B2653187
theorem B2653529 : Blo 1768085 2653529 := bstep (se 2 (by rfl) ⟨995073, by rfl⟩ : syracuseStep 2653529 = 1990147) B1990147
theorem B1768811 : Blo 1768085 1768811 := bstep (se 1 (by rfl) ⟨1326608, by rfl⟩ : syracuseStep 1768811 = 2653217) B2653217
theorem B1768823 : Blo 1768085 1768823 := bstep (se 1 (by rfl) ⟨1326617, by rfl⟩ : syracuseStep 1768823 = 2653235) B2653235
theorem B1768843 : Blo 1768085 1768843 := bstep (se 1 (by rfl) ⟨1326632, by rfl⟩ : syracuseStep 1768843 = 2653265) B2653265
theorem B1768855 : Blo 1768085 1768855 := bstep (se 1 (by rfl) ⟨1326641, by rfl⟩ : syracuseStep 1768855 = 2653283) B2653283
theorem B1990039 : Blo 1768085 1990039 := bstep (se 1 (by rfl) ⟨1492529, by rfl⟩ : syracuseStep 1990039 = 2985059) B2985059
theorem B3636631 : Blo 1768085 3636631 := bstep (se 1 (by rfl) ⟨2727473, by rfl⟩ : syracuseStep 3636631 = 5454947) B5454947
theorem B1768875 : Blo 1768085 1768875 := bstep (se 1 (by rfl) ⟨1326656, by rfl⟩ : syracuseStep 1768875 = 2653313) B2653313
theorem B16997809 : Blo 1768085 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B1768887 : Blo 1768085 1768887 := bstep (se 1 (by rfl) ⟨1326665, by rfl⟩ : syracuseStep 1768887 = 2653331) B2653331
theorem B1768907 : Blo 1768085 1768907 := bstep (se 1 (by rfl) ⟨1326680, by rfl⟩ : syracuseStep 1768907 = 2653361) B2653361
theorem B2653643 : Blo 1768085 2653643 := bstep (se 1 (by rfl) ⟨1990232, by rfl⟩ : syracuseStep 2653643 = 3980465) B3980465
theorem B1768919 : Blo 1768085 1768919 := bstep (se 1 (by rfl) ⟨1326689, by rfl⟩ : syracuseStep 1768919 = 2653379) B2653379
theorem B3358169 : Blo 1768085 3358169 := bstep (se 2 (by rfl) ⟨1259313, by rfl⟩ : syracuseStep 3358169 = 2518627) B2518627
theorem B2653655 : Blo 1768085 2653655 := bstep (se 1 (by rfl) ⟨1990241, by rfl⟩ : syracuseStep 2653655 = 3980483) B3980483
theorem B12107225 : Blo 1768085 12107225 := bstep (se 2 (by rfl) ⟨4540209, by rfl⟩ : syracuseStep 12107225 = 9080419) B9080419
theorem B7560665 : Blo 1768085 7560665 := bstep (se 2 (by rfl) ⟨2835249, by rfl⟩ : syracuseStep 7560665 = 5670499) B5670499
theorem B1768939 : Blo 1768085 1768939 := bstep (se 1 (by rfl) ⟨1326704, by rfl⟩ : syracuseStep 1768939 = 2653409) B2653409
theorem B1768951 : Blo 1768085 1768951 := bstep (se 1 (by rfl) ⟨1326713, by rfl⟩ : syracuseStep 1768951 = 2653427) B2653427
theorem B1768971 : Blo 1768085 1768971 := bstep (se 1 (by rfl) ⟨1326728, by rfl⟩ : syracuseStep 1768971 = 2653457) B2653457
theorem B6716945 : Blo 1768085 6716945 := bstep (se 2 (by rfl) ⟨2518854, by rfl⟩ : syracuseStep 6716945 = 5037709) B5037709
theorem B1768983 : Blo 1768085 1768983 := bstep (se 1 (by rfl) ⟨1326737, by rfl⟩ : syracuseStep 1768983 = 2653475) B2653475
theorem B2653721 : Blo 1768085 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B3980825 : Blo 1768085 3980825 := bstep (se 2 (by rfl) ⟨1492809, by rfl⟩ : syracuseStep 3980825 = 2985619) B2985619
theorem B1769003 : Blo 1768085 1769003 := bstep (se 1 (by rfl) ⟨1326752, by rfl⟩ : syracuseStep 1769003 = 2653505) B2653505
theorem B1769015 : Blo 1768085 1769015 := bstep (se 1 (by rfl) ⟨1326761, by rfl⟩ : syracuseStep 1769015 = 2653523) B2653523
theorem B1769035 : Blo 1768085 1769035 := bstep (se 1 (by rfl) ⟨1326776, by rfl⟩ : syracuseStep 1769035 = 2653553) B2653553
theorem B1990219 : Blo 1768085 1990219 := bstep (se 1 (by rfl) ⟨1492664, by rfl⟩ : syracuseStep 1990219 = 2985329) B2985329
theorem B1793611 : Blo 1768085 1793611 := bstep (se 1 (by rfl) ⟨1345208, by rfl⟩ : syracuseStep 1793611 = 2690417) B2690417
theorem B1769047 : Blo 1768085 1769047 := bstep (se 1 (by rfl) ⟨1326785, by rfl⟩ : syracuseStep 1769047 = 2653571) B2653571
theorem B7552601 : Blo 1768085 7552601 := bstep (se 2 (by rfl) ⟨2832225, by rfl⟩ : syracuseStep 7552601 = 5664451) B5664451
theorem B1769067 : Blo 1768085 1769067 := bstep (se 1 (by rfl) ⟨1326800, by rfl⟩ : syracuseStep 1769067 = 2653601) B2653601
theorem B3980915 : Blo 1768085 3980915 := bstep (se 1 (by rfl) ⟨2985686, by rfl⟩ : syracuseStep 3980915 = 5971373) B5971373
theorem B1769079 : Blo 1768085 1769079 := bstep (se 1 (by rfl) ⟨1326809, by rfl⟩ : syracuseStep 1769079 = 2653619) B2653619
theorem B1769099 : Blo 1768085 1769099 := bstep (se 1 (by rfl) ⟨1326824, by rfl⟩ : syracuseStep 1769099 = 2653649) B2653649
theorem B2653835 : Blo 1768085 2653835 := bstep (se 1 (by rfl) ⟨1990376, by rfl⟩ : syracuseStep 2653835 = 3980753) B3980753
theorem B1769111 : Blo 1768085 1769111 := bstep (se 1 (by rfl) ⟨1326833, by rfl⟩ : syracuseStep 1769111 = 2653667) B2653667
theorem B2653847 : Blo 1768085 2653847 := bstep (se 1 (by rfl) ⟨1990385, by rfl⟩ : syracuseStep 2653847 = 3980771) B3980771
theorem B3980951 : Blo 1768085 3980951 := bstep (se 1 (by rfl) ⟨2985713, by rfl⟩ : syracuseStep 3980951 = 5971427) B5971427
theorem B1769131 : Blo 1768085 1769131 := bstep (se 1 (by rfl) ⟨1326848, by rfl⟩ : syracuseStep 1769131 = 2653697) B2653697
theorem B1769143 : Blo 1768085 1769143 := bstep (se 1 (by rfl) ⟨1326857, by rfl⟩ : syracuseStep 1769143 = 2653715) B2653715
theorem B1990327 : Blo 1768085 1990327 := bstep (se 1 (by rfl) ⟨1492745, by rfl⟩ : syracuseStep 1990327 = 2985491) B2985491
theorem B1769163 : Blo 1768085 1769163 := bstep (se 1 (by rfl) ⟨1326872, by rfl⟩ : syracuseStep 1769163 = 2653745) B2653745
theorem B43630285 : Blo 1768085 43630285 := bstep (se 3 (by rfl) ⟨8180678, by rfl⟩ : syracuseStep 43630285 = 16361357) B16361357
theorem B3776215 : Blo 1768085 3776215 := bstep (se 1 (by rfl) ⟨2832161, by rfl⟩ : syracuseStep 3776215 = 5664323) B5664323
theorem B1769175 : Blo 1768085 1769175 := bstep (se 1 (by rfl) ⟨1326881, by rfl⟩ : syracuseStep 1769175 = 2653763) B2653763
theorem B2653913 : Blo 1768085 2653913 := bstep (se 2 (by rfl) ⟨995217, by rfl⟩ : syracuseStep 2653913 = 1990435) B1990435
theorem B1769195 : Blo 1768085 1769195 := bstep (se 1 (by rfl) ⟨1326896, by rfl⟩ : syracuseStep 1769195 = 2653793) B2653793
theorem B1769207 : Blo 1768085 1769207 := bstep (se 1 (by rfl) ⟨1326905, by rfl⟩ : syracuseStep 1769207 = 2653811) B2653811
theorem B1769227 : Blo 1768085 1769227 := bstep (se 1 (by rfl) ⟨1326920, by rfl⟩ : syracuseStep 1769227 = 2653841) B2653841
theorem B1769239 : Blo 1768085 1769239 := bstep (se 1 (by rfl) ⟨1326929, by rfl⟩ : syracuseStep 1769239 = 2653859) B2653859
theorem B1769259 : Blo 1768085 1769259 := bstep (se 1 (by rfl) ⟨1326944, by rfl⟩ : syracuseStep 1769259 = 2653889) B2653889
theorem B1769271 : Blo 1768085 1769271 := bstep (se 1 (by rfl) ⟨1326953, by rfl⟩ : syracuseStep 1769271 = 2653907) B2653907
theorem B1769291 : Blo 1768085 1769291 := bstep (se 1 (by rfl) ⟨1326968, by rfl⟩ : syracuseStep 1769291 = 2653937) B2653937
theorem B2654027 : Blo 1768085 2654027 := bstep (se 1 (by rfl) ⟨1990520, by rfl⟩ : syracuseStep 2654027 = 3981041) B3981041
theorem B3981131 : Blo 1768085 3981131 := bstep (se 1 (by rfl) ⟨2985848, by rfl⟩ : syracuseStep 3981131 = 5971697) B5971697
theorem B1769303 : Blo 1768085 1769303 := bstep (se 1 (by rfl) ⟨1326977, by rfl⟩ : syracuseStep 1769303 = 2653955) B2653955
theorem B2654039 : Blo 1768085 2654039 := bstep (se 1 (by rfl) ⟨1990529, by rfl⟩ : syracuseStep 2654039 = 3981059) B3981059
theorem B5971805 : Blo 1768085 5971805 := bstep (se 3 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 5971805 = 2239427) B2239427
theorem B51707747 : Blo 1768085 51707747 := bstep (se 1 (by rfl) ⟨38780810, by rfl⟩ : syracuseStep 51707747 = 77561621) B77561621
theorem B1769323 : Blo 1768085 1769323 := bstep (se 1 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 1769323 = 2653985) B2653985
theorem B1990507 : Blo 1768085 1990507 := bstep (se 1 (by rfl) ⟨1492880, by rfl⟩ : syracuseStep 1990507 = 2985761) B2985761
theorem B3358579 : Blo 1768085 3358579 := bstep (se 1 (by rfl) ⟨2518934, by rfl⟩ : syracuseStep 3358579 = 5037869) B5037869
theorem B1769335 : Blo 1768085 1769335 := bstep (se 1 (by rfl) ⟨1327001, by rfl⟩ : syracuseStep 1769335 = 2654003) B2654003
theorem B3981185 : Blo 1768085 3981185 := bstep (se 2 (by rfl) ⟨1492944, by rfl⟩ : syracuseStep 3981185 = 2985889) B2985889
theorem B16138115 : Blo 1768085 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B3776395 : Blo 1768085 3776395 := bstep (se 1 (by rfl) ⟨2832296, by rfl⟩ : syracuseStep 3776395 = 5664593) B5664593
theorem B1769355 : Blo 1768085 1769355 := bstep (se 1 (by rfl) ⟨1327016, by rfl⟩ : syracuseStep 1769355 = 2654033) B2654033
theorem B1769367 : Blo 1768085 1769367 := bstep (se 1 (by rfl) ⟨1327025, by rfl⟩ : syracuseStep 1769367 = 2654051) B2654051
theorem B2654105 : Blo 1768085 2654105 := bstep (se 2 (by rfl) ⟨995289, by rfl⟩ : syracuseStep 2654105 = 1990579) B1990579
theorem B2834327 : Blo 1768085 2834327 := bstep (se 1 (by rfl) ⟨2125745, by rfl⟩ : syracuseStep 2834327 = 4251491) B4251491
theorem B1769387 : Blo 1768085 1769387 := bstep (se 1 (by rfl) ⟨1327040, by rfl⟩ : syracuseStep 1769387 = 2654081) B2654081
theorem B1769399 : Blo 1768085 1769399 := bstep (se 1 (by rfl) ⟨1327049, by rfl⟩ : syracuseStep 1769399 = 2654099) B2654099
theorem B1769419 : Blo 1768085 1769419 := bstep (se 1 (by rfl) ⟨1327064, by rfl⟩ : syracuseStep 1769419 = 2654129) B2654129
theorem B3776471 : Blo 1768085 3776471 := bstep (se 1 (by rfl) ⟨2832353, by rfl⟩ : syracuseStep 3776471 = 5664707) B5664707
theorem B1769431 : Blo 1768085 1769431 := bstep (se 1 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 1769431 = 2654147) B2654147
theorem B6717401 : Blo 1768085 6717401 := bstep (se 2 (by rfl) ⟨2519025, by rfl⟩ : syracuseStep 6717401 = 5038051) B5038051
theorem B1990615 : Blo 1768085 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B1769451 : Blo 1768085 1769451 := bstep (se 1 (by rfl) ⟨1327088, by rfl⟩ : syracuseStep 1769451 = 2654177) B2654177
theorem B1769479 : Blo 1768085 1769479 := bstep (se 1 (by rfl) ⟨1327109, by rfl⟩ : syracuseStep 1769479 = 2654219) B2654219
theorem B1769487 : Blo 1768085 1769487 := bstep (se 1 (by rfl) ⟨1327115, by rfl⟩ : syracuseStep 1769487 = 2654231) B2654231
theorem B5038109 : Blo 1768085 5038109 := bstep (se 3 (by rfl) ⟨944645, by rfl⟩ : syracuseStep 5038109 = 1889291) B1889291
theorem B2654267 : Blo 1768085 2654267 := bstep (se 1 (by rfl) ⟨1990700, by rfl⟩ : syracuseStep 2654267 = 3981401) B3981401
theorem B1769531 : Blo 1768085 1769531 := bstep (se 1 (by rfl) ⟨1327148, by rfl⟩ : syracuseStep 1769531 = 2654297) B2654297
theorem B2654327 : Blo 1768085 2654327 := bstep (se 1 (by rfl) ⟨1990745, by rfl⟩ : syracuseStep 2654327 = 3981491) B3981491
theorem B10764407 : Blo 1768085 10764407 := bstep (se 1 (by rfl) ⟨8073305, by rfl⟩ : syracuseStep 10764407 = 16146611) B16146611
theorem B1769607 : Blo 1768085 1769607 := bstep (se 1 (by rfl) ⟨1327205, by rfl⟩ : syracuseStep 1769607 = 2654411) B2654411
theorem B2654351 : Blo 1768085 2654351 := bstep (se 1 (by rfl) ⟨1990763, by rfl⟩ : syracuseStep 2654351 = 3981527) B3981527
theorem B1769615 : Blo 1768085 1769615 := bstep (se 1 (by rfl) ⟨1327211, by rfl⟩ : syracuseStep 1769615 = 2654423) B2654423
theorem B2654393 : Blo 1768085 2654393 := bstep (se 2 (by rfl) ⟨995397, by rfl⟩ : syracuseStep 2654393 = 1990795) B1990795
theorem B1769659 : Blo 1768085 1769659 := bstep (se 1 (by rfl) ⟨1327244, by rfl⟩ : syracuseStep 1769659 = 2654489) B2654489
theorem B3358921 : Blo 1768085 3358921 := bstep (se 2 (by rfl) ⟨1259595, by rfl⟩ : syracuseStep 3358921 = 2519191) B2519191
theorem B4251905 : Blo 1768085 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B2654471 : Blo 1768085 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1769735 : Blo 1768085 1769735 := bstep (se 1 (by rfl) ⟨1327301, by rfl⟩ : syracuseStep 1769735 = 2654603) B2654603
theorem B1769743 : Blo 1768085 1769743 := bstep (se 1 (by rfl) ⟨1327307, by rfl⟩ : syracuseStep 1769743 = 2654615) B2654615
theorem B21512465 : Blo 1768085 21512465 := bstep (se 2 (by rfl) ⟨8067174, by rfl⟩ : syracuseStep 21512465 = 16134349) B16134349
theorem B5103901 : Blo 1768085 5103901 := bstep (se 3 (by rfl) ⟨956981, by rfl⟩ : syracuseStep 5103901 = 1913963) B1913963
theorem B2654507 : Blo 1768085 2654507 := bstep (se 1 (by rfl) ⟨1990880, by rfl⟩ : syracuseStep 2654507 = 3981761) B3981761
theorem B1769787 : Blo 1768085 1769787 := bstep (se 1 (by rfl) ⟨1327340, by rfl⟩ : syracuseStep 1769787 = 2654681) B2654681
theorem B2654537 : Blo 1768085 2654537 := bstep (se 2 (by rfl) ⟨995451, by rfl⟩ : syracuseStep 2654537 = 1990903) B1990903
theorem B1991047 : Blo 1768085 1991047 := bstep (se 1 (by rfl) ⟨1493285, by rfl⟩ : syracuseStep 1991047 = 2986571) B2986571
theorem B1769863 : Blo 1768085 1769863 := bstep (se 1 (by rfl) ⟨1327397, by rfl⟩ : syracuseStep 1769863 = 2654795) B2654795
theorem B1769871 : Blo 1768085 1769871 := bstep (se 1 (by rfl) ⟨1327403, by rfl⟩ : syracuseStep 1769871 = 2654807) B2654807
theorem B3776915 : Blo 1768085 3776915 := bstep (se 1 (by rfl) ⟨2832686, by rfl⟩ : syracuseStep 3776915 = 5665373) B5665373
theorem B2654651 : Blo 1768085 2654651 := bstep (se 1 (by rfl) ⟨1990988, by rfl⟩ : syracuseStep 2654651 = 3981977) B3981977
theorem B1769915 : Blo 1768085 1769915 := bstep (se 1 (by rfl) ⟨1327436, by rfl⟩ : syracuseStep 1769915 = 2654873) B2654873
theorem B4252105 : Blo 1768085 4252105 := bstep (se 2 (by rfl) ⟨1594539, by rfl⟩ : syracuseStep 4252105 = 3189079) B3189079
theorem B2654711 : Blo 1768085 2654711 := bstep (se 1 (by rfl) ⟨1991033, by rfl⟩ : syracuseStep 2654711 = 3982067) B3982067
theorem B1769991 : Blo 1768085 1769991 := bstep (se 1 (by rfl) ⟨1327493, by rfl⟩ : syracuseStep 1769991 = 2654987) B2654987
theorem B2654735 : Blo 1768085 2654735 := bstep (se 1 (by rfl) ⟨1991051, by rfl⟩ : syracuseStep 2654735 = 3982103) B3982103
theorem B1769999 : Blo 1768085 1769999 := bstep (se 1 (by rfl) ⟨1327499, by rfl⟩ : syracuseStep 1769999 = 2654999) B2654999
theorem B2654777 : Blo 1768085 2654777 := bstep (se 2 (by rfl) ⟨995541, by rfl⟩ : syracuseStep 2654777 = 1991083) B1991083
theorem B1991227 : Blo 1768085 1991227 := bstep (se 1 (by rfl) ⟨1493420, by rfl⟩ : syracuseStep 1991227 = 2986841) B2986841
theorem B1770043 : Blo 1768085 1770043 := bstep (se 1 (by rfl) ⟨1327532, by rfl⟩ : syracuseStep 1770043 = 2655065) B2655065
theorem B13435469 : Blo 1768085 13435469 := bstep (se 3 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 13435469 = 5038301) B5038301
theorem B4915799 : Blo 1768085 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B3981959 : Blo 1768085 3981959 := bstep (se 1 (by rfl) ⟨2986469, by rfl⟩ : syracuseStep 3981959 = 5972939) B5972939
theorem B2654855 : Blo 1768085 2654855 := bstep (se 1 (by rfl) ⟨1991141, by rfl⟩ : syracuseStep 2654855 = 3982283) B3982283
theorem B2654891 : Blo 1768085 2654891 := bstep (se 1 (by rfl) ⟨1991168, by rfl⟩ : syracuseStep 2654891 = 3982337) B3982337
theorem B2654921 : Blo 1768085 2654921 := bstep (se 2 (by rfl) ⟨995595, by rfl⟩ : syracuseStep 2654921 = 1991191) B1991191
theorem B10216165 : Blo 1768085 10216165 := bstep (se 4 (by rfl) ⟨957765, by rfl⟩ : syracuseStep 10216165 = 1915531) B1915531
theorem B3982139 : Blo 1768085 3982139 := bstep (se 1 (by rfl) ⟨2986604, by rfl⟩ : syracuseStep 3982139 = 5973209) B5973209
theorem B2655035 : Blo 1768085 2655035 := bstep (se 1 (by rfl) ⟨1991276, by rfl⟩ : syracuseStep 2655035 = 3982553) B3982553
theorem B2655095 : Blo 1768085 2655095 := bstep (se 1 (by rfl) ⟨1991321, by rfl⟩ : syracuseStep 2655095 = 3982643) B3982643
theorem B8070023 : Blo 1768085 8070023 := bstep (se 1 (by rfl) ⟨6052517, by rfl⟩ : syracuseStep 8070023 = 12105035) B12105035
theorem B2655119 : Blo 1768085 2655119 := bstep (se 1 (by rfl) ⟨1991339, by rfl⟩ : syracuseStep 2655119 = 3982679) B3982679
theorem B3982265 : Blo 1768085 3982265 := bstep (se 2 (by rfl) ⟨1493349, by rfl⟩ : syracuseStep 3982265 = 2986699) B2986699
theorem B10077149 : Blo 1768085 10077149 := bstep (se 3 (by rfl) ⟨1889465, by rfl⟩ : syracuseStep 10077149 = 3778931) B3778931
theorem B6374467 : Blo 1768085 6374467 := bstep (se 1 (by rfl) ⟨4780850, by rfl⟩ : syracuseStep 6374467 = 9561701) B9561701
theorem B6464713 : Blo 1768085 6464713 := bstep (se 2 (by rfl) ⟨2424267, by rfl⟩ : syracuseStep 6464713 = 4848535) B4848535
theorem B12748013 : Blo 1768085 12748013 := bstep (se 3 (by rfl) ⟨2390252, by rfl⟩ : syracuseStep 12748013 = 4780505) B4780505
theorem B8291585 : Blo 1768085 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B5973263 : Blo 1768085 5973263 := bstep (se 1 (by rfl) ⟨4479947, by rfl⟩ : syracuseStep 5973263 = 8959895) B8959895
theorem B3982607 : Blo 1768085 3982607 := bstep (se 1 (by rfl) ⟨2986955, by rfl⟩ : syracuseStep 3982607 = 5973911) B5973911
theorem B3982625 : Blo 1768085 3982625 := bstep (se 2 (by rfl) ⟨1493484, by rfl⟩ : syracuseStep 3982625 = 2986969) B2986969
theorem B8504635 : Blo 1768085 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B4425047 : Blo 1768085 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B22676867 : Blo 1768085 22676867 := bstep (se 1 (by rfl) ⟨17007650, by rfl⟩ : syracuseStep 22676867 = 34015301) B34015301
theorem B2237959 : Blo 1768085 2237959 := bstep (se 1 (by rfl) ⟨1678469, by rfl⟩ : syracuseStep 2237959 = 3356939) B3356939
theorem B5973533 : Blo 1768085 5973533 := bstep (se 3 (by rfl) ⟨1120037, by rfl⟩ : syracuseStep 5973533 = 2240075) B2240075
theorem B20153933 : Blo 1768085 20153933 := bstep (se 3 (by rfl) ⟨3778862, by rfl⟩ : syracuseStep 20153933 = 7557725) B7557725
theorem B2238455 : Blo 1768085 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B2983979 : Blo 1768085 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B5040215 : Blo 1768085 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B2238607 : Blo 1768085 2238607 := bstep (se 1 (by rfl) ⟨1678955, by rfl⟩ : syracuseStep 2238607 = 3357911) B3357911
theorem B58173713 : Blo 1768085 58173713 := bstep (se 2 (by rfl) ⟨21815142, by rfl⟩ : syracuseStep 58173713 = 43630285) B43630285
theorem B2238779 : Blo 1768085 2238779 := bstep (se 1 (by rfl) ⟨1679084, by rfl⟩ : syracuseStep 2238779 = 3358169) B3358169
theorem B8071483 : Blo 1768085 8071483 := bstep (se 1 (by rfl) ⟨6053612, by rfl⟩ : syracuseStep 8071483 = 12107225) B12107225
theorem B5040443 : Blo 1768085 5040443 := bstep (se 1 (by rfl) ⟨3780332, by rfl⟩ : syracuseStep 5040443 = 7560665) B7560665
theorem B2984377 : Blo 1768085 2984377 := bstep (se 2 (by rfl) ⟨1119141, by rfl⟩ : syracuseStep 2984377 = 2238283) B2238283
theorem B5040569 : Blo 1768085 5040569 := bstep (se 2 (by rfl) ⟨1890213, by rfl⟩ : syracuseStep 5040569 = 3780427) B3780427
theorem B6720029 : Blo 1768085 6720029 := bstep (se 3 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 6720029 = 2520011) B2520011
theorem B6720043 : Blo 1768085 6720043 := bstep (se 1 (by rfl) ⟨5040032, by rfl⟩ : syracuseStep 6720043 = 10080065) B10080065
theorem B2689595 : Blo 1768085 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B10758743 : Blo 1768085 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B8620631 : Blo 1768085 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B2517647 : Blo 1768085 2517647 := bstep (se 1 (by rfl) ⟨1888235, by rfl⟩ : syracuseStep 2517647 = 3776471) B3776471
theorem B3779273 : Blo 1768085 3779273 := bstep (se 2 (by rfl) ⟨1417227, by rfl⟩ : syracuseStep 3779273 = 2834455) B2834455
theorem B20433665 : Blo 1768085 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B8956817 : Blo 1768085 8956817 := bstep (se 2 (by rfl) ⟨3358806, by rfl⟩ : syracuseStep 8956817 = 6717613) B6717613
theorem B2517961 : Blo 1768085 2517961 := bstep (se 2 (by rfl) ⟨944235, by rfl⟩ : syracuseStep 2517961 = 1888471) B1888471
theorem B13437899 : Blo 1768085 13437899 := bstep (se 1 (by rfl) ⟨10078424, by rfl⟩ : syracuseStep 13437899 = 20156849) B20156849
theorem B11332669 : Blo 1768085 11332669 := bstep (se 3 (by rfl) ⟨2124875, by rfl⟩ : syracuseStep 11332669 = 4249751) B4249751
theorem B4476019 : Blo 1768085 4476019 := bstep (se 1 (by rfl) ⟨3357014, by rfl⟩ : syracuseStep 4476019 = 6714029) B6714029
theorem B2985079 : Blo 1768085 2985079 := bstep (se 1 (by rfl) ⟨2238809, by rfl⟩ : syracuseStep 2985079 = 4477619) B4477619
theorem B4476161 : Blo 1768085 4476161 := bstep (se 2 (by rfl) ⟨1678560, by rfl⟩ : syracuseStep 4476161 = 3357121) B3357121
theorem B2239751 : Blo 1768085 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B2985275 : Blo 1768085 2985275 := bstep (se 1 (by rfl) ⟨2238956, by rfl⟩ : syracuseStep 2985275 = 4477913) B4477913
theorem B18648467 : Blo 1768085 18648467 := bstep (se 1 (by rfl) ⟨13986350, by rfl⟩ : syracuseStep 18648467 = 27972701) B27972701
theorem B10071499 : Blo 1768085 10071499 := bstep (se 1 (by rfl) ⟨7553624, by rfl⟩ : syracuseStep 10071499 = 15107249) B15107249
theorem B10079747 : Blo 1768085 10079747 := bstep (se 1 (by rfl) ⟨7559810, by rfl⟩ : syracuseStep 10079747 = 15119621) B15119621
theorem B21515969 : Blo 1768085 21515969 := bstep (se 2 (by rfl) ⟨8068488, by rfl⟩ : syracuseStep 21515969 = 16136977) B16136977
theorem B4476617 : Blo 1768085 4476617 := bstep (se 2 (by rfl) ⟨1678731, by rfl⟩ : syracuseStep 4476617 = 3357463) B3357463
theorem B2985673 : Blo 1768085 2985673 := bstep (se 2 (by rfl) ⟨1119627, by rfl⟩ : syracuseStep 2985673 = 2239255) B2239255
theorem B8498945 : Blo 1768085 8498945 := bstep (se 2 (by rfl) ⟨3187104, by rfl⟩ : syracuseStep 8498945 = 6374209) B6374209
theorem B16994083 : Blo 1768085 16994083 := bstep (se 1 (by rfl) ⟨12745562, by rfl⟩ : syracuseStep 16994083 = 25491125) B25491125
theorem B32280371 : Blo 1768085 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B8499059 : Blo 1768085 8499059 := bstep (se 1 (by rfl) ⟨6374294, by rfl⟩ : syracuseStep 8499059 = 12748589) B12748589
theorem B19378187 : Blo 1768085 19378187 := bstep (se 1 (by rfl) ⟨14533640, by rfl⟩ : syracuseStep 19378187 = 29067281) B29067281
theorem B4476971 : Blo 1768085 4476971 := bstep (se 1 (by rfl) ⟨3357728, by rfl⟩ : syracuseStep 4476971 = 6715457) B6715457
theorem B4780289 : Blo 1768085 4780289 := bstep (se 2 (by rfl) ⟨1792608, by rfl⟩ : syracuseStep 4780289 = 3585217) B3585217
theorem B5968187 : Blo 1768085 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B2986375 : Blo 1768085 2986375 := bstep (se 1 (by rfl) ⟨2239781, by rfl⟩ : syracuseStep 2986375 = 4479563) B4479563
theorem B6812039 : Blo 1768085 6812039 := bstep (se 1 (by rfl) ⟨5109029, by rfl⟩ : syracuseStep 6812039 = 10218059) B10218059
theorem B25498097 : Blo 1768085 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B2126351 : Blo 1768085 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B206705195 : Blo 1768085 206705195 := bstep (se 1 (by rfl) ⟨155028896, by rfl⟩ : syracuseStep 206705195 = 310057793) B310057793
theorem B22663745 : Blo 1768085 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B5968673 : Blo 1768085 5968673 := bstep (se 2 (by rfl) ⟨2238252, by rfl⟩ : syracuseStep 5968673 = 4476505) B4476505
theorem B11334437 : Blo 1768085 11334437 := bstep (se 4 (by rfl) ⟨1062603, by rfl⟩ : syracuseStep 11334437 = 2125207) B2125207
theorem B5034953 : Blo 1768085 5034953 := bstep (se 2 (by rfl) ⟨1888107, by rfl⟩ : syracuseStep 5034953 = 3776215) B3776215
theorem B8958923 : Blo 1768085 8958923 := bstep (se 1 (by rfl) ⟨6719192, by rfl⟩ : syracuseStep 8958923 = 13438385) B13438385
theorem B4477963 : Blo 1768085 4477963 := bstep (se 1 (by rfl) ⟨3358472, by rfl⟩ : syracuseStep 4477963 = 6716945) B6716945
theorem B5035067 : Blo 1768085 5035067 := bstep (se 1 (by rfl) ⟨3776300, by rfl⟩ : syracuseStep 5035067 = 7552601) B7552601
theorem B3978359 : Blo 1768085 3978359 := bstep (se 1 (by rfl) ⟨2983769, by rfl⟩ : syracuseStep 3978359 = 5967539) B5967539
theorem B4478105 : Blo 1768085 4478105 := bstep (se 2 (by rfl) ⟨1679289, by rfl⟩ : syracuseStep 4478105 = 3358579) B3358579
theorem B5035193 : Blo 1768085 5035193 := bstep (se 2 (by rfl) ⟨1888197, by rfl⟩ : syracuseStep 5035193 = 3776395) B3776395
theorem B9696449 : Blo 1768085 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B8950985 : Blo 1768085 8950985 := bstep (se 2 (by rfl) ⟨3356619, by rfl⟩ : syracuseStep 8950985 = 6713239) B6713239
theorem B1889551 : Blo 1768085 1889551 := bstep (se 1 (by rfl) ⟨1417163, by rfl⟩ : syracuseStep 1889551 = 2834327) B2834327
theorem B8959247 : Blo 1768085 8959247 := bstep (se 1 (by rfl) ⟨6719435, by rfl⟩ : syracuseStep 8959247 = 13438871) B13438871
theorem B3978539 : Blo 1768085 3978539 := bstep (se 1 (by rfl) ⟨2983904, by rfl⟩ : syracuseStep 3978539 = 5967809) B5967809
theorem B6714683 : Blo 1768085 6714683 := bstep (se 1 (by rfl) ⟨5036012, by rfl⟩ : syracuseStep 6714683 = 10072025) B10072025
theorem B4478267 : Blo 1768085 4478267 := bstep (se 1 (by rfl) ⟨3358700, by rfl⟩ : syracuseStep 4478267 = 6717401) B6717401
theorem B5969267 : Blo 1768085 5969267 := bstep (se 1 (by rfl) ⟨4476950, by rfl⟩ : syracuseStep 5969267 = 8953901) B8953901
theorem B2725255 : Blo 1768085 2725255 := bstep (se 1 (by rfl) ⟨2043941, by rfl⟩ : syracuseStep 2725255 = 4087883) B4087883
theorem B19125649 : Blo 1768085 19125649 := bstep (se 2 (by rfl) ⟨7172118, by rfl⟩ : syracuseStep 19125649 = 14344237) B14344237
theorem B5666233 : Blo 1768085 5666233 := bstep (se 2 (by rfl) ⟨2124837, by rfl⟩ : syracuseStep 5666233 = 4249675) B4249675
theorem B7558667 : Blo 1768085 7558667 := bstep (se 1 (by rfl) ⟨5669000, by rfl⟩ : syracuseStep 7558667 = 11338001) B11338001
theorem B7558717 : Blo 1768085 7558717 := bstep (se 3 (by rfl) ⟨1417259, by rfl⟩ : syracuseStep 7558717 = 2834519) B2834519
theorem B4249223 : Blo 1768085 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B3978899 : Blo 1768085 3978899 := bstep (se 1 (by rfl) ⟨2984174, by rfl⟩ : syracuseStep 3978899 = 5968349) B5968349
theorem B4478611 : Blo 1768085 4478611 := bstep (se 1 (by rfl) ⟨3358958, by rfl⟩ : syracuseStep 4478611 = 6717917) B6717917
theorem B3978953 : Blo 1768085 3978953 := bstep (se 2 (by rfl) ⟨1492107, by rfl⟩ : syracuseStep 3978953 = 2984215) B2984215
theorem B6715169 : Blo 1768085 6715169 := bstep (se 2 (by rfl) ⟨2518188, by rfl⟩ : syracuseStep 6715169 = 5036377) B5036377
theorem B4478753 : Blo 1768085 4478753 := bstep (se 2 (by rfl) ⟨1679532, by rfl⟩ : syracuseStep 4478753 = 3359065) B3359065
theorem B19380017 : Blo 1768085 19380017 := bstep (se 2 (by rfl) ⟨7267506, by rfl⟩ : syracuseStep 19380017 = 14535013) B14535013
theorem B15324977 : Blo 1768085 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B10073915 : Blo 1768085 10073915 := bstep (se 1 (by rfl) ⟨7555436, by rfl⟩ : syracuseStep 10073915 = 15110873) B15110873
theorem B28686149 : Blo 1768085 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B2652167 : Blo 1768085 2652167 := bstep (se 1 (by rfl) ⟨1989125, by rfl⟩ : syracuseStep 2652167 = 3978251) B3978251
theorem B2652203 : Blo 1768085 2652203 := bstep (se 1 (by rfl) ⟨1989152, by rfl⟩ : syracuseStep 2652203 = 3978305) B3978305
theorem B2652233 : Blo 1768085 2652233 := bstep (se 2 (by rfl) ⟨994587, by rfl⟩ : syracuseStep 2652233 = 1989175) B1989175
theorem B2652347 : Blo 1768085 2652347 := bstep (se 1 (by rfl) ⟨1989260, by rfl⟩ : syracuseStep 2652347 = 3978521) B3978521
theorem B2652407 : Blo 1768085 2652407 := bstep (se 1 (by rfl) ⟨1989305, by rfl⟩ : syracuseStep 2652407 = 3978611) B3978611
theorem B2652431 : Blo 1768085 2652431 := bstep (se 1 (by rfl) ⟨1989323, by rfl⟩ : syracuseStep 2652431 = 3978647) B3978647
theorem B8501519 : Blo 1768085 8501519 := bstep (se 1 (by rfl) ⟨6376139, by rfl⟩ : syracuseStep 8501519 = 12752279) B12752279
theorem B2652473 : Blo 1768085 2652473 := bstep (se 2 (by rfl) ⟨994677, by rfl⟩ : syracuseStep 2652473 = 1989355) B1989355
theorem B2652551 : Blo 1768085 2652551 := bstep (se 1 (by rfl) ⟨1989413, by rfl⟩ : syracuseStep 2652551 = 3978827) B3978827
theorem B3979655 : Blo 1768085 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B4249991 : Blo 1768085 4249991 := bstep (se 1 (by rfl) ⟨3187493, by rfl⟩ : syracuseStep 4249991 = 6374987) B6374987
theorem B2652587 : Blo 1768085 2652587 := bstep (se 1 (by rfl) ⟨1989440, by rfl⟩ : syracuseStep 2652587 = 3978881) B3978881
theorem B7174585 : Blo 1768085 7174585 := bstep (se 2 (by rfl) ⟨2690469, by rfl⟩ : syracuseStep 7174585 = 5380939) B5380939
theorem B2652617 : Blo 1768085 2652617 := bstep (se 2 (by rfl) ⟨994731, by rfl⟩ : syracuseStep 2652617 = 1989463) B1989463
theorem B9558481 : Blo 1768085 9558481 := bstep (se 2 (by rfl) ⟨3584430, by rfl⟩ : syracuseStep 9558481 = 7168861) B7168861
theorem B3357227 : Blo 1768085 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B2652731 : Blo 1768085 2652731 := bstep (se 1 (by rfl) ⟨1989548, by rfl⟩ : syracuseStep 2652731 = 3979097) B3979097
theorem B3979835 : Blo 1768085 3979835 := bstep (se 1 (by rfl) ⟨2984876, by rfl⟩ : syracuseStep 3979835 = 5969753) B5969753
theorem B2652791 : Blo 1768085 2652791 := bstep (se 1 (by rfl) ⟨1989593, by rfl⟩ : syracuseStep 2652791 = 3979187) B3979187
theorem B2652815 : Blo 1768085 2652815 := bstep (se 1 (by rfl) ⟨1989611, by rfl⟩ : syracuseStep 2652815 = 3979223) B3979223
theorem B2652857 : Blo 1768085 2652857 := bstep (se 2 (by rfl) ⟨994821, by rfl⟩ : syracuseStep 2652857 = 1989643) B1989643
theorem B3979961 : Blo 1768085 3979961 := bstep (se 2 (by rfl) ⟨1492485, by rfl⟩ : syracuseStep 3979961 = 2984971) B2984971
theorem B1768123 : Blo 1768085 1768123 := bstep (se 1 (by rfl) ⟨1326092, by rfl⟩ : syracuseStep 1768123 = 2652185) B2652185
theorem B8960705 : Blo 1768085 8960705 := bstep (se 2 (by rfl) ⟨3360264, by rfl⟩ : syracuseStep 8960705 = 6720529) B6720529
theorem B6716141 : Blo 1768085 6716141 := bstep (se 3 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 6716141 = 2518553) B2518553
theorem B4479745 : Blo 1768085 4479745 := bstep (se 2 (by rfl) ⟨1679904, by rfl⟩ : syracuseStep 4479745 = 3359809) B3359809
theorem B1768199 : Blo 1768085 1768199 := bstep (se 1 (by rfl) ⟨1326149, by rfl⟩ : syracuseStep 1768199 = 2652299) B2652299
theorem B2652935 : Blo 1768085 2652935 := bstep (se 1 (by rfl) ⟨1989701, by rfl⟩ : syracuseStep 2652935 = 3979403) B3979403
theorem B1768207 : Blo 1768085 1768207 := bstep (se 1 (by rfl) ⟨1326155, by rfl⟩ : syracuseStep 1768207 = 2652311) B2652311
theorem B1989391 : Blo 1768085 1989391 := bstep (se 1 (by rfl) ⟨1492043, by rfl⟩ : syracuseStep 1989391 = 2984087) B2984087
theorem B2652971 : Blo 1768085 2652971 := bstep (se 1 (by rfl) ⟨1989728, by rfl⟩ : syracuseStep 2652971 = 3979457) B3979457
theorem B5036843 : Blo 1768085 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B4848427 : Blo 1768085 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B1768251 : Blo 1768085 1768251 := bstep (se 1 (by rfl) ⟨1326188, by rfl⟩ : syracuseStep 1768251 = 2652377) B2652377
theorem B2653001 : Blo 1768085 2653001 := bstep (se 2 (by rfl) ⟨994875, by rfl⟩ : syracuseStep 2653001 = 1989751) B1989751
theorem B38255449 : Blo 1768085 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B1768327 : Blo 1768085 1768327 := bstep (se 1 (by rfl) ⟨1326245, by rfl⟩ : syracuseStep 1768327 = 2652491) B2652491
theorem B1768335 : Blo 1768085 1768335 := bstep (se 1 (by rfl) ⟨1326251, by rfl⟩ : syracuseStep 1768335 = 2652503) B2652503
theorem B16997273 : Blo 1768085 16997273 := bstep (se 2 (by rfl) ⟨6373977, by rfl⟩ : syracuseStep 16997273 = 12747955) B12747955
theorem B1768379 : Blo 1768085 1768379 := bstep (se 1 (by rfl) ⟨1326284, by rfl⟩ : syracuseStep 1768379 = 2652569) B2652569
theorem B2653115 : Blo 1768085 2653115 := bstep (se 1 (by rfl) ⟨1989836, by rfl⟩ : syracuseStep 2653115 = 3979673) B3979673
theorem B2653175 : Blo 1768085 2653175 := bstep (se 1 (by rfl) ⟨1989881, by rfl⟩ : syracuseStep 2653175 = 3979763) B3979763
theorem B1768455 : Blo 1768085 1768455 := bstep (se 1 (by rfl) ⟨1326341, by rfl⟩ : syracuseStep 1768455 = 2652683) B2652683
theorem B1768463 : Blo 1768085 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B2653199 : Blo 1768085 2653199 := bstep (se 1 (by rfl) ⟨1989899, by rfl⟩ : syracuseStep 2653199 = 3979799) B3979799
theorem B3980303 : Blo 1768085 3980303 := bstep (se 1 (by rfl) ⟨2985227, by rfl⟩ : syracuseStep 3980303 = 5970455) B5970455
theorem B3980321 : Blo 1768085 3980321 := bstep (se 2 (by rfl) ⟨1492620, by rfl⟩ : syracuseStep 3980321 = 2985241) B2985241
theorem B6716459 : Blo 1768085 6716459 := bstep (se 1 (by rfl) ⟨5037344, by rfl⟩ : syracuseStep 6716459 = 10074689) B10074689
theorem B2653241 : Blo 1768085 2653241 := bstep (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) B1989931
theorem B1768507 : Blo 1768085 1768507 := bstep (se 1 (by rfl) ⟨1326380, by rfl⟩ : syracuseStep 1768507 = 2652761) B2652761
theorem B6462551 : Blo 1768085 6462551 := bstep (se 1 (by rfl) ⟨4846913, by rfl⟩ : syracuseStep 6462551 = 9693827) B9693827
theorem B1768583 : Blo 1768085 1768583 := bstep (se 1 (by rfl) ⟨1326437, by rfl⟩ : syracuseStep 1768583 = 2652875) B2652875
theorem B2653319 : Blo 1768085 2653319 := bstep (se 1 (by rfl) ⟨1989989, by rfl⟩ : syracuseStep 2653319 = 3979979) B3979979
theorem B1768591 : Blo 1768085 1768591 := bstep (se 1 (by rfl) ⟨1326443, by rfl⟩ : syracuseStep 1768591 = 2652887) B2652887
theorem B2653355 : Blo 1768085 2653355 := bstep (se 1 (by rfl) ⟨1990016, by rfl⟩ : syracuseStep 2653355 = 3980033) B3980033
theorem B1768635 : Blo 1768085 1768635 := bstep (se 1 (by rfl) ⟨1326476, by rfl⟩ : syracuseStep 1768635 = 2652953) B2652953
theorem B2653385 : Blo 1768085 2653385 := bstep (se 2 (by rfl) ⟨995019, by rfl⟩ : syracuseStep 2653385 = 1990039) B1990039
theorem B4848841 : Blo 1768085 4848841 := bstep (se 2 (by rfl) ⟨1818315, by rfl⟩ : syracuseStep 4848841 = 3636631) B3636631
theorem B10075373 : Blo 1768085 10075373 := bstep (se 3 (by rfl) ⟨1889132, by rfl⟩ : syracuseStep 10075373 = 3778265) B3778265
theorem B1768711 : Blo 1768085 1768711 := bstep (se 1 (by rfl) ⟨1326533, by rfl⟩ : syracuseStep 1768711 = 2653067) B2653067
theorem B1989895 : Blo 1768085 1989895 := bstep (se 1 (by rfl) ⟨1492421, by rfl⟩ : syracuseStep 1989895 = 2984843) B2984843
theorem B1768719 : Blo 1768085 1768719 := bstep (se 1 (by rfl) ⟨1326539, by rfl⟩ : syracuseStep 1768719 = 2653079) B2653079
theorem B1768763 : Blo 1768085 1768763 := bstep (se 1 (by rfl) ⟨1326572, by rfl⟩ : syracuseStep 1768763 = 2653145) B2653145
theorem B2653499 : Blo 1768085 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B4480343 : Blo 1768085 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B2653559 : Blo 1768085 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B3980663 : Blo 1768085 3980663 := bstep (se 1 (by rfl) ⟨2985497, by rfl⟩ : syracuseStep 3980663 = 5970995) B5970995
theorem B1768839 : Blo 1768085 1768839 := bstep (se 1 (by rfl) ⟨1326629, by rfl⟩ : syracuseStep 1768839 = 2653259) B2653259
theorem B1768847 : Blo 1768085 1768847 := bstep (se 1 (by rfl) ⟨1326635, by rfl⟩ : syracuseStep 1768847 = 2653271) B2653271
theorem B2653583 : Blo 1768085 2653583 := bstep (se 1 (by rfl) ⟨1990187, by rfl⟩ : syracuseStep 2653583 = 3980375) B3980375
theorem B2653625 : Blo 1768085 2653625 := bstep (se 2 (by rfl) ⟨995109, by rfl⟩ : syracuseStep 2653625 = 1990219) B1990219
theorem B2391481 : Blo 1768085 2391481 := bstep (se 2 (by rfl) ⟨896805, by rfl⟩ : syracuseStep 2391481 = 1793611) B1793611
theorem B1768891 : Blo 1768085 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B1990075 : Blo 1768085 1990075 := bstep (se 1 (by rfl) ⟨1492556, by rfl⟩ : syracuseStep 1990075 = 2985113) B2985113
theorem B8502749 : Blo 1768085 8502749 := bstep (se 3 (by rfl) ⟨1594265, by rfl⟩ : syracuseStep 8502749 = 3188531) B3188531
theorem B1768967 : Blo 1768085 1768967 := bstep (se 1 (by rfl) ⟨1326725, by rfl⟩ : syracuseStep 1768967 = 2653451) B2653451
theorem B2653703 : Blo 1768085 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B1768975 : Blo 1768085 1768975 := bstep (se 1 (by rfl) ⟨1326731, by rfl⟩ : syracuseStep 1768975 = 2653463) B2653463
theorem B10075691 : Blo 1768085 10075691 := bstep (se 1 (by rfl) ⟨7556768, by rfl⟩ : syracuseStep 10075691 = 15113537) B15113537
theorem B2653739 : Blo 1768085 2653739 := bstep (se 1 (by rfl) ⟨1990304, by rfl⟩ : syracuseStep 2653739 = 3980609) B3980609
theorem B3980843 : Blo 1768085 3980843 := bstep (se 1 (by rfl) ⟨2985632, by rfl⟩ : syracuseStep 3980843 = 5971265) B5971265
theorem B1769019 : Blo 1768085 1769019 := bstep (se 1 (by rfl) ⟨1326764, by rfl⟩ : syracuseStep 1769019 = 2653529) B2653529
theorem B2653769 : Blo 1768085 2653769 := bstep (se 2 (by rfl) ⟨995163, by rfl⟩ : syracuseStep 2653769 = 1990327) B1990327
theorem B3186311 : Blo 1768085 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B1769095 : Blo 1768085 1769095 := bstep (se 1 (by rfl) ⟨1326821, by rfl⟩ : syracuseStep 1769095 = 2653643) B2653643
theorem B1769103 : Blo 1768085 1769103 := bstep (se 1 (by rfl) ⟨1326827, by rfl⟩ : syracuseStep 1769103 = 2653655) B2653655
theorem B1769147 : Blo 1768085 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B2653883 : Blo 1768085 2653883 := bstep (se 1 (by rfl) ⟨1990412, by rfl⟩ : syracuseStep 2653883 = 3980825) B3980825
theorem B2653943 : Blo 1768085 2653943 := bstep (se 1 (by rfl) ⟨1990457, by rfl⟩ : syracuseStep 2653943 = 3980915) B3980915
theorem B1769223 : Blo 1768085 1769223 := bstep (se 1 (by rfl) ⟨1326917, by rfl⟩ : syracuseStep 1769223 = 2653835) B2653835
theorem B5037835 : Blo 1768085 5037835 := bstep (se 1 (by rfl) ⟨3778376, by rfl⟩ : syracuseStep 5037835 = 7556753) B7556753
theorem B1769231 : Blo 1768085 1769231 := bstep (se 1 (by rfl) ⟨1326923, by rfl⟩ : syracuseStep 1769231 = 2653847) B2653847
theorem B2653967 : Blo 1768085 2653967 := bstep (se 1 (by rfl) ⟨1990475, by rfl⟩ : syracuseStep 2653967 = 3980951) B3980951
theorem B98148145 : Blo 1768085 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B2654009 : Blo 1768085 2654009 := bstep (se 2 (by rfl) ⟨995253, by rfl⟩ : syracuseStep 2654009 = 1990507) B1990507
theorem B1769275 : Blo 1768085 1769275 := bstep (se 1 (by rfl) ⟨1326956, by rfl⟩ : syracuseStep 1769275 = 2653913) B2653913
theorem B1769351 : Blo 1768085 1769351 := bstep (se 1 (by rfl) ⟨1327013, by rfl⟩ : syracuseStep 1769351 = 2654027) B2654027
theorem B2654087 : Blo 1768085 2654087 := bstep (se 1 (by rfl) ⟨1990565, by rfl⟩ : syracuseStep 2654087 = 3981131) B3981131
theorem B1769359 : Blo 1768085 1769359 := bstep (se 1 (by rfl) ⟨1327019, by rfl⟩ : syracuseStep 1769359 = 2654039) B2654039
theorem B1990543 : Blo 1768085 1990543 := bstep (se 1 (by rfl) ⟨1492907, by rfl⟩ : syracuseStep 1990543 = 2985815) B2985815
theorem B3981203 : Blo 1768085 3981203 := bstep (se 1 (by rfl) ⟨2985902, by rfl⟩ : syracuseStep 3981203 = 5971805) B5971805
theorem B5971859 : Blo 1768085 5971859 := bstep (se 1 (by rfl) ⟨4478894, by rfl⟩ : syracuseStep 5971859 = 8957789) B8957789
theorem B34471831 : Blo 1768085 34471831 := bstep (se 1 (by rfl) ⟨25853873, by rfl⟩ : syracuseStep 34471831 = 51707747) B51707747
theorem B8503193 : Blo 1768085 8503193 := bstep (se 2 (by rfl) ⟨3188697, by rfl⟩ : syracuseStep 8503193 = 6377395) B6377395
theorem B2654123 : Blo 1768085 2654123 := bstep (se 1 (by rfl) ⟨1990592, by rfl⟩ : syracuseStep 2654123 = 3981185) B3981185
theorem B1769403 : Blo 1768085 1769403 := bstep (se 1 (by rfl) ⟨1327052, by rfl⟩ : syracuseStep 1769403 = 2654105) B2654105
theorem B2654153 : Blo 1768085 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B3981257 : Blo 1768085 3981257 := bstep (se 2 (by rfl) ⟨1492971, by rfl⟩ : syracuseStep 3981257 = 2985943) B2985943
theorem B12918791 : Blo 1768085 12918791 := bstep (se 1 (by rfl) ⟨9689093, by rfl⟩ : syracuseStep 12918791 = 19378187) B19378187
theorem B3358739 : Blo 1768085 3358739 := bstep (se 1 (by rfl) ⟨2519054, by rfl⟩ : syracuseStep 3358739 = 5038109) B5038109
theorem B1769511 : Blo 1768085 1769511 := bstep (se 1 (by rfl) ⟨1327133, by rfl⟩ : syracuseStep 1769511 = 2654267) B2654267
theorem B1769551 : Blo 1768085 1769551 := bstep (se 1 (by rfl) ⟨1327163, by rfl⟩ : syracuseStep 1769551 = 2654327) B2654327
theorem B7176271 : Blo 1768085 7176271 := bstep (se 1 (by rfl) ⟨5382203, by rfl⟩ : syracuseStep 7176271 = 10764407) B10764407
theorem B1769567 : Blo 1768085 1769567 := bstep (se 1 (by rfl) ⟨1327175, by rfl⟩ : syracuseStep 1769567 = 2654351) B2654351
theorem B1769595 : Blo 1768085 1769595 := bstep (se 1 (by rfl) ⟨1327196, by rfl⟩ : syracuseStep 1769595 = 2654393) B2654393
theorem B3186859 : Blo 1768085 3186859 := bstep (se 1 (by rfl) ⟨2390144, by rfl⟩ : syracuseStep 3186859 = 4780289) B4780289
theorem B2834603 : Blo 1768085 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B1769647 : Blo 1768085 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B1769671 : Blo 1768085 1769671 := bstep (se 1 (by rfl) ⟨1327253, by rfl⟩ : syracuseStep 1769671 = 2654507) B2654507
theorem B1769691 : Blo 1768085 1769691 := bstep (se 1 (by rfl) ⟨1327268, by rfl⟩ : syracuseStep 1769691 = 2654537) B2654537
theorem B1769767 : Blo 1768085 1769767 := bstep (se 1 (by rfl) ⟨1327325, by rfl⟩ : syracuseStep 1769767 = 2654651) B2654651
theorem B16998731 : Blo 1768085 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B1769807 : Blo 1768085 1769807 := bstep (se 1 (by rfl) ⟨1327355, by rfl⟩ : syracuseStep 1769807 = 2654711) B2654711
theorem B1769823 : Blo 1768085 1769823 := bstep (se 1 (by rfl) ⟨1327367, by rfl⟩ : syracuseStep 1769823 = 2654735) B2654735
theorem B33997157 : Blo 1768085 33997157 := bstep (se 4 (by rfl) ⟨3187233, by rfl⟩ : syracuseStep 33997157 = 6374467) B6374467
theorem B1769851 : Blo 1768085 1769851 := bstep (se 1 (by rfl) ⟨1327388, by rfl⟩ : syracuseStep 1769851 = 2654777) B2654777
theorem B3277199 : Blo 1768085 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B2654639 : Blo 1768085 2654639 := bstep (se 1 (by rfl) ⟨1990979, by rfl⟩ : syracuseStep 2654639 = 3981959) B3981959
theorem B1769903 : Blo 1768085 1769903 := bstep (se 1 (by rfl) ⟨1327427, by rfl⟩ : syracuseStep 1769903 = 2654855) B2654855
theorem B1769927 : Blo 1768085 1769927 := bstep (se 1 (by rfl) ⟨1327445, by rfl⟩ : syracuseStep 1769927 = 2654891) B2654891
theorem B1769947 : Blo 1768085 1769947 := bstep (se 1 (by rfl) ⟨1327460, by rfl⟩ : syracuseStep 1769947 = 2654921) B2654921
theorem B3981833 : Blo 1768085 3981833 := bstep (se 2 (by rfl) ⟨1493187, by rfl⟩ : syracuseStep 3981833 = 2986375) B2986375
theorem B2654729 : Blo 1768085 2654729 := bstep (se 2 (by rfl) ⟨995523, by rfl⟩ : syracuseStep 2654729 = 1991047) B1991047
theorem B2654759 : Blo 1768085 2654759 := bstep (se 1 (by rfl) ⟨1991069, by rfl⟩ : syracuseStep 2654759 = 3982139) B3982139
theorem B1770023 : Blo 1768085 1770023 := bstep (se 1 (by rfl) ⟨1327517, by rfl⟩ : syracuseStep 1770023 = 2655035) B2655035
theorem B1770063 : Blo 1768085 1770063 := bstep (se 1 (by rfl) ⟨1327547, by rfl⟩ : syracuseStep 1770063 = 2655095) B2655095
theorem B1770079 : Blo 1768085 1770079 := bstep (se 1 (by rfl) ⟨1327559, by rfl⟩ : syracuseStep 1770079 = 2655119) B2655119
theorem B2654843 : Blo 1768085 2654843 := bstep (se 1 (by rfl) ⟨1991132, by rfl⟩ : syracuseStep 2654843 = 3982265) B3982265
theorem B5972615 : Blo 1768085 5972615 := bstep (se 1 (by rfl) ⟨4479461, by rfl⟩ : syracuseStep 5972615 = 8958923) B8958923
theorem B6718099 : Blo 1768085 6718099 := bstep (se 1 (by rfl) ⟨5038574, by rfl⟩ : syracuseStep 6718099 = 10077149) B10077149
theorem B5972669 : Blo 1768085 5972669 := bstep (se 3 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 5972669 = 2239751) B2239751
theorem B2654969 : Blo 1768085 2654969 := bstep (se 2 (by rfl) ⟨995613, by rfl⟩ : syracuseStep 2654969 = 1991227) B1991227
theorem B5972831 : Blo 1768085 5972831 := bstep (se 1 (by rfl) ⟨4479623, by rfl⟩ : syracuseStep 5972831 = 8959247) B8959247
theorem B3982175 : Blo 1768085 3982175 := bstep (se 1 (by rfl) ⟨2986631, by rfl⟩ : syracuseStep 3982175 = 5973263) B5973263
theorem B2655071 : Blo 1768085 2655071 := bstep (se 1 (by rfl) ⟨1991303, by rfl⟩ : syracuseStep 2655071 = 3982607) B3982607
theorem B2655083 : Blo 1768085 2655083 := bstep (se 1 (by rfl) ⟨1991312, by rfl⟩ : syracuseStep 2655083 = 3982625) B3982625
theorem B2950031 : Blo 1768085 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B5972993 : Blo 1768085 5972993 := bstep (se 2 (by rfl) ⟨2239872, by rfl⟩ : syracuseStep 5972993 = 4479745) B4479745
theorem B5039111 : Blo 1768085 5039111 := bstep (se 1 (by rfl) ⟨3779333, by rfl⟩ : syracuseStep 5039111 = 7558667) B7558667
theorem B3982355 : Blo 1768085 3982355 := bstep (se 1 (by rfl) ⟨2986766, by rfl⟩ : syracuseStep 3982355 = 5973533) B5973533
theorem B13435955 : Blo 1768085 13435955 := bstep (se 1 (by rfl) ⟨10076966, by rfl⟩ : syracuseStep 13435955 = 20153933) B20153933
theorem B10216651 : Blo 1768085 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B5670269 : Blo 1768085 5670269 := bstep (se 3 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 5670269 = 2126351) B2126351
theorem B3360143 : Blo 1768085 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B10077605 : Blo 1768085 10077605 := bstep (se 4 (by rfl) ⟨944775, by rfl⟩ : syracuseStep 10077605 = 1889551) B1889551
theorem B38782475 : Blo 1768085 38782475 := bstep (se 1 (by rfl) ⟨29086856, by rfl⟩ : syracuseStep 38782475 = 58173713) B58173713
theorem B3360295 : Blo 1768085 3360295 := bstep (se 1 (by rfl) ⟨2520221, by rfl⟩ : syracuseStep 3360295 = 5040443) B5040443
theorem B8619617 : Blo 1768085 8619617 := bstep (se 2 (by rfl) ⟨3232356, by rfl⟩ : syracuseStep 8619617 = 6464713) B6464713
theorem B3360379 : Blo 1768085 3360379 := bstep (se 1 (by rfl) ⟨2520284, by rfl⟩ : syracuseStep 3360379 = 5040569) B5040569
theorem B8496829 : Blo 1768085 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B11339513 : Blo 1768085 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B5973803 : Blo 1768085 5973803 := bstep (se 1 (by rfl) ⟨4480352, by rfl⟩ : syracuseStep 5973803 = 8960705) B8960705
theorem B7554977 : Blo 1768085 7554977 := bstep (se 2 (by rfl) ⟨2833116, by rfl⟩ : syracuseStep 7554977 = 5666233) B5666233
theorem B3188641 : Blo 1768085 3188641 := bstep (se 2 (by rfl) ⟨1195740, by rfl⟩ : syracuseStep 3188641 = 2391481) B2391481
theorem B13428665 : Blo 1768085 13428665 := bstep (se 2 (by rfl) ⟨5035749, by rfl⟩ : syracuseStep 13428665 = 10071499) B10071499
theorem B11331515 : Blo 1768085 11331515 := bstep (se 1 (by rfl) ⟨8498636, by rfl⟩ : syracuseStep 11331515 = 16997273) B16997273
theorem B2983945 : Blo 1768085 2983945 := bstep (se 2 (by rfl) ⟨1118979, by rfl⟩ : syracuseStep 2983945 = 2237959) B2237959
theorem B10078289 : Blo 1768085 10078289 := bstep (se 2 (by rfl) ⟨3779358, by rfl⟩ : syracuseStep 10078289 = 7558717) B7558717
theorem B2984107 : Blo 1768085 2984107 := bstep (se 1 (by rfl) ⟨2238080, by rfl⟩ : syracuseStep 2984107 = 4476161) B4476161
theorem B6719831 : Blo 1768085 6719831 := bstep (se 1 (by rfl) ⟨5039873, by rfl⟩ : syracuseStep 6719831 = 10079747) B10079747
theorem B22677893 : Blo 1768085 22677893 := bstep (se 4 (by rfl) ⟨2126052, by rfl⟩ : syracuseStep 22677893 = 4252105) B4252105
theorem B2984411 : Blo 1768085 2984411 := bstep (se 1 (by rfl) ⟨2238308, by rfl⟩ : syracuseStep 2984411 = 4476617) B4476617
theorem B2984647 : Blo 1768085 2984647 := bstep (se 1 (by rfl) ⟨2238485, by rfl⟩ : syracuseStep 2984647 = 4476971) B4476971
theorem B2984809 : Blo 1768085 2984809 := bstep (se 2 (by rfl) ⟨1119303, by rfl⟩ : syracuseStep 2984809 = 2238607) B2238607
theorem B4541359 : Blo 1768085 4541359 := bstep (se 1 (by rfl) ⟨3406019, by rfl⟩ : syracuseStep 4541359 = 6812039) B6812039
theorem B15109163 : Blo 1768085 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B8956979 : Blo 1768085 8956979 := bstep (se 1 (by rfl) ⟨6717734, by rfl⟩ : syracuseStep 8956979 = 13435469) B13435469
theorem B25857197 : Blo 1768085 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B7556291 : Blo 1768085 7556291 := bstep (se 1 (by rfl) ⟨5667218, by rfl⟩ : syracuseStep 7556291 = 11334437) B11334437
theorem B2985403 : Blo 1768085 2985403 := bstep (se 1 (by rfl) ⟨2239052, by rfl⟩ : syracuseStep 2985403 = 4478105) B4478105
theorem B5967323 : Blo 1768085 5967323 := bstep (se 1 (by rfl) ⟨4475492, by rfl⟩ : syracuseStep 5967323 = 8950985) B8950985
theorem B8498675 : Blo 1768085 8498675 := bstep (se 1 (by rfl) ⟨6374006, by rfl⟩ : syracuseStep 8498675 = 12748013) B12748013
theorem B4476455 : Blo 1768085 4476455 := bstep (se 1 (by rfl) ⟨3357341, by rfl⟩ : syracuseStep 4476455 = 6714683) B6714683
theorem B2985511 : Blo 1768085 2985511 := bstep (se 1 (by rfl) ⟨2239133, by rfl⟩ : syracuseStep 2985511 = 4478267) B4478267
theorem B15117911 : Blo 1768085 15117911 := bstep (se 1 (by rfl) ⟨11338433, by rfl⟩ : syracuseStep 15117911 = 22676867) B22676867
theorem B10071773 : Blo 1768085 10071773 := bstep (se 3 (by rfl) ⟨1888457, by rfl⟩ : syracuseStep 10071773 = 3776915) B3776915
theorem B51007265 : Blo 1768085 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B4476779 : Blo 1768085 4476779 := bstep (se 1 (by rfl) ⟨3357584, by rfl⟩ : syracuseStep 4476779 = 6715169) B6715169
theorem B2985835 : Blo 1768085 2985835 := bstep (se 1 (by rfl) ⟨2239376, by rfl⟩ : syracuseStep 2985835 = 4478753) B4478753
theorem B19124099 : Blo 1768085 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B15110225 : Blo 1768085 15110225 := bstep (se 2 (by rfl) ⟨5666334, by rfl⟩ : syracuseStep 15110225 = 11332669) B11332669
theorem B5968025 : Blo 1768085 5968025 := bstep (se 2 (by rfl) ⟨2238009, by rfl⟩ : syracuseStep 5968025 = 4476019) B4476019
theorem B25858277 : Blo 1768085 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B6713725 : Blo 1768085 6713725 := bstep (se 3 (by rfl) ⟨1258823, by rfl⟩ : syracuseStep 6713725 = 2517647) B2517647
theorem B7172495 : Blo 1768085 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B5747087 : Blo 1768085 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B2519515 : Blo 1768085 2519515 := bstep (se 1 (by rfl) ⟨1889636, by rfl⟩ : syracuseStep 2519515 = 3779273) B3779273
theorem B4477427 : Blo 1768085 4477427 := bstep (se 1 (by rfl) ⟨3358070, by rfl⟩ : syracuseStep 4477427 = 6716141) B6716141
theorem B3633673 : Blo 1768085 3633673 := bstep (se 2 (by rfl) ⟨1362627, by rfl⟩ : syracuseStep 3633673 = 2725255) B2725255
theorem B8958599 : Blo 1768085 8958599 := bstep (se 1 (by rfl) ⟨6718949, by rfl⟩ : syracuseStep 8958599 = 13437899) B13437899
theorem B54489773 : Blo 1768085 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B4477639 : Blo 1768085 4477639 := bstep (se 1 (by rfl) ⟨3358229, by rfl⟩ : syracuseStep 4477639 = 6716459) B6716459
theorem B13431581 : Blo 1768085 13431581 := bstep (se 3 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 13431581 = 5036843) B5036843
theorem B51680045 : Blo 1768085 51680045 := bstep (se 3 (by rfl) ⟨9690008, by rfl⟩ : syracuseStep 51680045 = 19380017) B19380017
theorem B2986895 : Blo 1768085 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B12432311 : Blo 1768085 12432311 := bstep (se 1 (by rfl) ⟨9324233, by rfl⟩ : syracuseStep 12432311 = 18648467) B18648467
theorem B130864193 : Blo 1768085 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B5665963 : Blo 1768085 5665963 := bstep (se 1 (by rfl) ⟨4249472, by rfl⟩ : syracuseStep 5665963 = 8498945) B8498945
theorem B45962441 : Blo 1768085 45962441 := bstep (se 2 (by rfl) ⟨17235915, by rfl⟩ : syracuseStep 45962441 = 34471831) B34471831
theorem B5666039 : Blo 1768085 5666039 := bstep (se 1 (by rfl) ⟨4249529, by rfl⟩ : syracuseStep 5666039 = 8499059) B8499059
theorem B5969213 : Blo 1768085 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B14341643 : Blo 1768085 14341643 := bstep (se 1 (by rfl) ⟨10756232, by rfl⟩ : syracuseStep 14341643 = 21512465) B21512465
theorem B3978791 : Blo 1768085 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B17233469 : Blo 1768085 17233469 := bstep (se 3 (by rfl) ⟨3231275, by rfl⟩ : syracuseStep 17233469 = 6462551) B6462551
theorem B4478561 : Blo 1768085 4478561 := bstep (se 2 (by rfl) ⟨1679460, by rfl⟩ : syracuseStep 4478561 = 3358921) B3358921
theorem B137803463 : Blo 1768085 137803463 := bstep (se 1 (by rfl) ⟨103352597, by rfl⟩ : syracuseStep 137803463 = 206705195) B206705195
theorem B10761977 : Blo 1768085 10761977 := bstep (se 2 (by rfl) ⟨4035741, by rfl⟩ : syracuseStep 10761977 = 8071483) B8071483
theorem B3979115 : Blo 1768085 3979115 := bstep (se 1 (by rfl) ⟨2984336, by rfl⟩ : syracuseStep 3979115 = 5968673) B5968673
theorem B3979169 : Blo 1768085 3979169 := bstep (se 2 (by rfl) ⟨1492188, by rfl⟩ : syracuseStep 3979169 = 2984377) B2984377
theorem B9566113 : Blo 1768085 9566113 := bstep (se 2 (by rfl) ⟨3587292, by rfl⟩ : syracuseStep 9566113 = 7174585) B7174585
theorem B5380015 : Blo 1768085 5380015 := bstep (se 1 (by rfl) ⟨4035011, by rfl⟩ : syracuseStep 5380015 = 8070023) B8070023
theorem B12744641 : Blo 1768085 12744641 := bstep (se 2 (by rfl) ⟨4779240, by rfl⟩ : syracuseStep 12744641 = 9558481) B9558481
theorem B3356635 : Blo 1768085 3356635 := bstep (se 1 (by rfl) ⟨2517476, by rfl⟩ : syracuseStep 3356635 = 5034953) B5034953
theorem B3356711 : Blo 1768085 3356711 := bstep (se 1 (by rfl) ⟨2517533, by rfl⟩ : syracuseStep 3356711 = 5035067) B5035067
theorem B8960057 : Blo 1768085 8960057 := bstep (se 2 (by rfl) ⟨3360021, by rfl⟩ : syracuseStep 8960057 = 6720043) B6720043
theorem B2652239 : Blo 1768085 2652239 := bstep (se 1 (by rfl) ⟨1989179, by rfl⟩ : syracuseStep 2652239 = 3978359) B3978359
theorem B3356795 : Blo 1768085 3356795 := bstep (se 1 (by rfl) ⟨2517596, by rfl⟩ : syracuseStep 3356795 = 5035193) B5035193
theorem B5970077 : Blo 1768085 5970077 := bstep (se 3 (by rfl) ⟨1119389, by rfl⟩ : syracuseStep 5970077 = 2238779) B2238779
theorem B5527723 : Blo 1768085 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B2652359 : Blo 1768085 2652359 := bstep (se 1 (by rfl) ⟨1989269, by rfl⟩ : syracuseStep 2652359 = 3978539) B3978539
theorem B3979511 : Blo 1768085 3979511 := bstep (se 1 (by rfl) ⟨2984633, by rfl⟩ : syracuseStep 3979511 = 5969267) B5969267
theorem B13621553 : Blo 1768085 13621553 := bstep (se 2 (by rfl) ⟨5108082, by rfl⟩ : syracuseStep 13621553 = 10216165) B10216165
theorem B2652521 : Blo 1768085 2652521 := bstep (se 2 (by rfl) ⟨994695, by rfl⟩ : syracuseStep 2652521 = 1989391) B1989391
theorem B25860485 : Blo 1768085 25860485 := bstep (se 4 (by rfl) ⟨2424420, by rfl⟩ : syracuseStep 25860485 = 4848841) B4848841
theorem B2832815 : Blo 1768085 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B2652599 : Blo 1768085 2652599 := bstep (se 1 (by rfl) ⟨1989449, by rfl⟩ : syracuseStep 2652599 = 3978899) B3978899
theorem B2652635 : Blo 1768085 2652635 := bstep (se 1 (by rfl) ⟨1989476, by rfl⟩ : syracuseStep 2652635 = 3978953) B3978953
theorem B6715943 : Blo 1768085 6715943 := bstep (se 1 (by rfl) ⟨5036957, by rfl⟩ : syracuseStep 6715943 = 10073915) B10073915
theorem B3357281 : Blo 1768085 3357281 := bstep (se 2 (by rfl) ⟨1258980, by rfl⟩ : syracuseStep 3357281 = 2517961) B2517961
theorem B1768111 : Blo 1768085 1768111 := bstep (se 1 (by rfl) ⟨1326083, by rfl⟩ : syracuseStep 1768111 = 2652167) B2652167
theorem B5970617 : Blo 1768085 5970617 := bstep (se 2 (by rfl) ⟨2238981, by rfl⟩ : syracuseStep 5970617 = 4477963) B4477963
theorem B1768135 : Blo 1768085 1768135 := bstep (se 1 (by rfl) ⟨1326101, by rfl⟩ : syracuseStep 1768135 = 2652203) B2652203
theorem B1989319 : Blo 1768085 1989319 := bstep (se 1 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 1989319 = 2983979) B2983979
theorem B1768155 : Blo 1768085 1768155 := bstep (se 1 (by rfl) ⟨1326116, by rfl⟩ : syracuseStep 1768155 = 2652233) B2652233
theorem B8952605 : Blo 1768085 8952605 := bstep (se 3 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 8952605 = 3357227) B3357227
theorem B1768231 : Blo 1768085 1768231 := bstep (se 1 (by rfl) ⟨1326173, by rfl⟩ : syracuseStep 1768231 = 2652347) B2652347
theorem B27220805 : Blo 1768085 27220805 := bstep (se 4 (by rfl) ⟨2551950, by rfl⟩ : syracuseStep 27220805 = 5103901) B5103901
theorem B3980105 : Blo 1768085 3980105 := bstep (se 2 (by rfl) ⟨1492539, by rfl⟩ : syracuseStep 3980105 = 2985079) B2985079
theorem B1768271 : Blo 1768085 1768271 := bstep (se 1 (by rfl) ⟨1326203, by rfl⟩ : syracuseStep 1768271 = 2652407) B2652407
theorem B1768287 : Blo 1768085 1768287 := bstep (se 1 (by rfl) ⟨1326215, by rfl⟩ : syracuseStep 1768287 = 2652431) B2652431
theorem B5667679 : Blo 1768085 5667679 := bstep (se 1 (by rfl) ⟨4250759, by rfl⟩ : syracuseStep 5667679 = 8501519) B8501519
theorem B1768315 : Blo 1768085 1768315 := bstep (se 1 (by rfl) ⟨1326236, by rfl⟩ : syracuseStep 1768315 = 2652473) B2652473
theorem B1768367 : Blo 1768085 1768367 := bstep (se 1 (by rfl) ⟨1326275, by rfl⟩ : syracuseStep 1768367 = 2652551) B2652551
theorem B2653103 : Blo 1768085 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B2833327 : Blo 1768085 2833327 := bstep (se 1 (by rfl) ⟨2124995, by rfl⟩ : syracuseStep 2833327 = 4249991) B4249991
theorem B1768391 : Blo 1768085 1768391 := bstep (se 1 (by rfl) ⟨1326293, by rfl⟩ : syracuseStep 1768391 = 2652587) B2652587
theorem B1768411 : Blo 1768085 1768411 := bstep (se 1 (by rfl) ⟨1326308, by rfl⟩ : syracuseStep 1768411 = 2652617) B2652617
theorem B2653193 : Blo 1768085 2653193 := bstep (se 2 (by rfl) ⟨994947, by rfl⟩ : syracuseStep 2653193 = 1989895) B1989895
theorem B4480019 : Blo 1768085 4480019 := bstep (se 1 (by rfl) ⟨3360014, by rfl⟩ : syracuseStep 4480019 = 6720029) B6720029
theorem B1768487 : Blo 1768085 1768487 := bstep (se 1 (by rfl) ⟨1326365, by rfl⟩ : syracuseStep 1768487 = 2652731) B2652731
theorem B2653223 : Blo 1768085 2653223 := bstep (se 1 (by rfl) ⟨1989917, by rfl⟩ : syracuseStep 2653223 = 3979835) B3979835
theorem B1793063 : Blo 1768085 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1768527 : Blo 1768085 1768527 := bstep (se 1 (by rfl) ⟨1326395, by rfl⟩ : syracuseStep 1768527 = 2652791) B2652791
theorem B1768543 : Blo 1768085 1768543 := bstep (se 1 (by rfl) ⟨1326407, by rfl⟩ : syracuseStep 1768543 = 2652815) B2652815
theorem B1768571 : Blo 1768085 1768571 := bstep (se 1 (by rfl) ⟨1326428, by rfl⟩ : syracuseStep 1768571 = 2652857) B2652857
theorem B2653307 : Blo 1768085 2653307 := bstep (se 1 (by rfl) ⟨1989980, by rfl⟩ : syracuseStep 2653307 = 3979961) B3979961
theorem B1768623 : Blo 1768085 1768623 := bstep (se 1 (by rfl) ⟨1326467, by rfl⟩ : syracuseStep 1768623 = 2652935) B2652935
theorem B25500865 : Blo 1768085 25500865 := bstep (se 2 (by rfl) ⟨9562824, by rfl⟩ : syracuseStep 25500865 = 19125649) B19125649
theorem B1768647 : Blo 1768085 1768647 := bstep (se 1 (by rfl) ⟨1326485, by rfl⟩ : syracuseStep 1768647 = 2652971) B2652971
theorem B1768667 : Blo 1768085 1768667 := bstep (se 1 (by rfl) ⟨1326500, by rfl⟩ : syracuseStep 1768667 = 2653001) B2653001
theorem B2653433 : Blo 1768085 2653433 := bstep (se 2 (by rfl) ⟨995037, by rfl⟩ : syracuseStep 2653433 = 1990075) B1990075
theorem B5971211 : Blo 1768085 5971211 := bstep (se 1 (by rfl) ⟨4478408, by rfl⟩ : syracuseStep 5971211 = 8956817) B8956817
theorem B1768743 : Blo 1768085 1768743 := bstep (se 1 (by rfl) ⟨1326557, by rfl⟩ : syracuseStep 1768743 = 2653115) B2653115
theorem B1768783 : Blo 1768085 1768783 := bstep (se 1 (by rfl) ⟨1326587, by rfl⟩ : syracuseStep 1768783 = 2653175) B2653175
theorem B1768799 : Blo 1768085 1768799 := bstep (se 1 (by rfl) ⟨1326599, by rfl⟩ : syracuseStep 1768799 = 2653199) B2653199
theorem B2653535 : Blo 1768085 2653535 := bstep (se 1 (by rfl) ⟨1990151, by rfl⟩ : syracuseStep 2653535 = 3980303) B3980303
theorem B2653547 : Blo 1768085 2653547 := bstep (se 1 (by rfl) ⟨1990160, by rfl⟩ : syracuseStep 2653547 = 3980321) B3980321
theorem B1768827 : Blo 1768085 1768827 := bstep (se 1 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 1768827 = 2653241) B2653241
theorem B1768879 : Blo 1768085 1768879 := bstep (se 1 (by rfl) ⟨1326659, by rfl⟩ : syracuseStep 1768879 = 2653319) B2653319
theorem B1768903 : Blo 1768085 1768903 := bstep (se 1 (by rfl) ⟨1326677, by rfl⟩ : syracuseStep 1768903 = 2653355) B2653355
theorem B1768923 : Blo 1768085 1768923 := bstep (se 1 (by rfl) ⟨1326692, by rfl⟩ : syracuseStep 1768923 = 2653385) B2653385
theorem B6716915 : Blo 1768085 6716915 := bstep (se 1 (by rfl) ⟨5037686, by rfl⟩ : syracuseStep 6716915 = 10075373) B10075373
theorem B5971481 : Blo 1768085 5971481 := bstep (se 2 (by rfl) ⟨2239305, by rfl⟩ : syracuseStep 5971481 = 4478611) B4478611
theorem B1768999 : Blo 1768085 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B1990183 : Blo 1768085 1990183 := bstep (se 1 (by rfl) ⟨1492637, by rfl⟩ : syracuseStep 1990183 = 2985275) B2985275
theorem B1769039 : Blo 1768085 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B2653775 : Blo 1768085 2653775 := bstep (se 1 (by rfl) ⟨1990331, by rfl⟩ : syracuseStep 2653775 = 3980663) B3980663
theorem B1769055 : Blo 1768085 1769055 := bstep (se 1 (by rfl) ⟨1326791, by rfl⟩ : syracuseStep 1769055 = 2653583) B2653583
theorem B3980897 : Blo 1768085 3980897 := bstep (se 2 (by rfl) ⟨1492836, by rfl⟩ : syracuseStep 3980897 = 2985673) B2985673
theorem B1769083 : Blo 1768085 1769083 := bstep (se 1 (by rfl) ⟨1326812, by rfl⟩ : syracuseStep 1769083 = 2653625) B2653625
theorem B5668499 : Blo 1768085 5668499 := bstep (se 1 (by rfl) ⟨4251374, by rfl⟩ : syracuseStep 5668499 = 8502749) B8502749
theorem B1769135 : Blo 1768085 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B6717113 : Blo 1768085 6717113 := bstep (se 2 (by rfl) ⟨2518917, by rfl⟩ : syracuseStep 6717113 = 5037835) B5037835
theorem B6717127 : Blo 1768085 6717127 := bstep (se 1 (by rfl) ⟨5037845, by rfl⟩ : syracuseStep 6717127 = 10075691) B10075691
theorem B1769159 : Blo 1768085 1769159 := bstep (se 1 (by rfl) ⟨1326869, by rfl⟩ : syracuseStep 1769159 = 2653739) B2653739
theorem B2653895 : Blo 1768085 2653895 := bstep (se 1 (by rfl) ⟨1990421, by rfl⟩ : syracuseStep 2653895 = 3980843) B3980843
theorem B22658777 : Blo 1768085 22658777 := bstep (se 2 (by rfl) ⟨8497041, by rfl⟩ : syracuseStep 22658777 = 16994083) B16994083
theorem B1769179 : Blo 1768085 1769179 := bstep (se 1 (by rfl) ⟨1326884, by rfl⟩ : syracuseStep 1769179 = 2653769) B2653769
theorem B1769255 : Blo 1768085 1769255 := bstep (se 1 (by rfl) ⟨1326941, by rfl⟩ : syracuseStep 1769255 = 2653883) B2653883
theorem B14343979 : Blo 1768085 14343979 := bstep (se 1 (by rfl) ⟨10757984, by rfl⟩ : syracuseStep 14343979 = 21515969) B21515969
theorem B1769295 : Blo 1768085 1769295 := bstep (se 1 (by rfl) ⟨1326971, by rfl⟩ : syracuseStep 1769295 = 2653943) B2653943
theorem B1769311 : Blo 1768085 1769311 := bstep (se 1 (by rfl) ⟨1326983, by rfl⟩ : syracuseStep 1769311 = 2653967) B2653967
theorem B2654057 : Blo 1768085 2654057 := bstep (se 2 (by rfl) ⟨995271, by rfl⟩ : syracuseStep 2654057 = 1990543) B1990543
theorem B21520247 : Blo 1768085 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B1769339 : Blo 1768085 1769339 := bstep (se 1 (by rfl) ⟨1327004, by rfl⟩ : syracuseStep 1769339 = 2654009) B2654009
theorem B1769391 : Blo 1768085 1769391 := bstep (se 1 (by rfl) ⟨1327043, by rfl⟩ : syracuseStep 1769391 = 2654087) B2654087
theorem B2654135 : Blo 1768085 2654135 := bstep (se 1 (by rfl) ⟨1990601, by rfl⟩ : syracuseStep 2654135 = 3981203) B3981203
theorem B3981239 : Blo 1768085 3981239 := bstep (se 1 (by rfl) ⟨2985929, by rfl⟩ : syracuseStep 3981239 = 5971859) B5971859
theorem B5668795 : Blo 1768085 5668795 := bstep (se 1 (by rfl) ⟨4251596, by rfl⟩ : syracuseStep 5668795 = 8503193) B8503193
theorem B1769415 : Blo 1768085 1769415 := bstep (se 1 (by rfl) ⟨1327061, by rfl⟩ : syracuseStep 1769415 = 2654123) B2654123
theorem B1769435 : Blo 1768085 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B2654171 : Blo 1768085 2654171 := bstep (se 1 (by rfl) ⟨1990628, by rfl⟩ : syracuseStep 2654171 = 3981257) B3981257
theorem B9568361 : Blo 1768085 9568361 := bstep (se 2 (by rfl) ⟨3588135, by rfl⟩ : syracuseStep 9568361 = 7176271) B7176271
theorem B1769759 : Blo 1768085 1769759 := bstep (se 1 (by rfl) ⟨1327319, by rfl⟩ : syracuseStep 1769759 = 2654639) B2654639
theorem B2654555 : Blo 1768085 2654555 := bstep (se 1 (by rfl) ⟨1990916, by rfl⟩ : syracuseStep 2654555 = 3981833) B3981833
theorem B1769819 : Blo 1768085 1769819 := bstep (se 1 (by rfl) ⟨1327364, by rfl⟩ : syracuseStep 1769819 = 2654729) B2654729
theorem B1769839 : Blo 1768085 1769839 := bstep (se 1 (by rfl) ⟨1327379, by rfl⟩ : syracuseStep 1769839 = 2654759) B2654759
theorem B1769895 : Blo 1768085 1769895 := bstep (se 1 (by rfl) ⟨1327421, by rfl⟩ : syracuseStep 1769895 = 2654843) B2654843
theorem B5972399 : Blo 1768085 5972399 := bstep (se 1 (by rfl) ⟨4479299, by rfl⟩ : syracuseStep 5972399 = 8958599) B8958599
theorem B3981743 : Blo 1768085 3981743 := bstep (se 1 (by rfl) ⟨2986307, by rfl⟩ : syracuseStep 3981743 = 5972615) B5972615
theorem B3981779 : Blo 1768085 3981779 := bstep (se 1 (by rfl) ⟨2986334, by rfl⟩ : syracuseStep 3981779 = 5972669) B5972669
theorem B1769979 : Blo 1768085 1769979 := bstep (se 1 (by rfl) ⟨1327484, by rfl⟩ : syracuseStep 1769979 = 2654969) B2654969
theorem B8954387 : Blo 1768085 8954387 := bstep (se 1 (by rfl) ⟨6715790, by rfl⟩ : syracuseStep 8954387 = 13431581) B13431581
theorem B3981887 : Blo 1768085 3981887 := bstep (se 1 (by rfl) ⟨2986415, by rfl⟩ : syracuseStep 3981887 = 5972831) B5972831
theorem B2654783 : Blo 1768085 2654783 := bstep (se 1 (by rfl) ⟨1991087, by rfl⟩ : syracuseStep 2654783 = 3982175) B3982175
theorem B1770047 : Blo 1768085 1770047 := bstep (se 1 (by rfl) ⟨1327535, by rfl⟩ : syracuseStep 1770047 = 2655071) B2655071
theorem B1770055 : Blo 1768085 1770055 := bstep (se 1 (by rfl) ⟨1327541, by rfl⟩ : syracuseStep 1770055 = 2655083) B2655083
theorem B1966687 : Blo 1768085 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B1991263 : Blo 1768085 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B3981995 : Blo 1768085 3981995 := bstep (se 1 (by rfl) ⟨2986496, by rfl⟩ : syracuseStep 3981995 = 5972993) B5972993
theorem B3359407 : Blo 1768085 3359407 := bstep (se 1 (by rfl) ⟨2519555, by rfl⟩ : syracuseStep 3359407 = 5039111) B5039111
theorem B2654903 : Blo 1768085 2654903 := bstep (se 1 (by rfl) ⟨1991177, by rfl⟩ : syracuseStep 2654903 = 3982355) B3982355
theorem B3777359 : Blo 1768085 3777359 := bstep (se 1 (by rfl) ⟨2833019, by rfl⟩ : syracuseStep 3777359 = 5666039) B5666039
theorem B6718403 : Blo 1768085 6718403 := bstep (se 1 (by rfl) ⟨5038802, by rfl⟩ : syracuseStep 6718403 = 10077605) B10077605
theorem B9561095 : Blo 1768085 9561095 := bstep (se 1 (by rfl) ⟨7170821, by rfl⟩ : syracuseStep 9561095 = 14341643) B14341643
theorem B25854983 : Blo 1768085 25854983 := bstep (se 1 (by rfl) ⟨19391237, by rfl⟩ : syracuseStep 25854983 = 38782475) B38782475
theorem B3982535 : Blo 1768085 3982535 := bstep (se 1 (by rfl) ⟨2986901, by rfl⟩ : syracuseStep 3982535 = 5973803) B5973803
theorem B3777769 : Blo 1768085 3777769 := bstep (se 2 (by rfl) ⟨1416663, by rfl⟩ : syracuseStep 3777769 = 2833327) B2833327
theorem B6055145 : Blo 1768085 6055145 := bstep (se 2 (by rfl) ⟨2270679, by rfl⟩ : syracuseStep 6055145 = 4541359) B4541359
theorem B7554343 : Blo 1768085 7554343 := bstep (se 1 (by rfl) ⟨5665757, by rfl⟩ : syracuseStep 7554343 = 11331515) B11331515
theorem B8496427 : Blo 1768085 8496427 := bstep (se 1 (by rfl) ⟨6372320, by rfl⟩ : syracuseStep 8496427 = 12744641) B12744641
theorem B2237807 : Blo 1768085 2237807 := bstep (se 1 (by rfl) ⟨1678355, by rfl⟩ : syracuseStep 2237807 = 3356711) B3356711
theorem B5973371 : Blo 1768085 5973371 := bstep (se 1 (by rfl) ⟨4480028, by rfl⟩ : syracuseStep 5973371 = 8960057) B8960057
theorem B6718859 : Blo 1768085 6718859 := bstep (se 1 (by rfl) ⟨5039144, by rfl⟩ : syracuseStep 6718859 = 10078289) B10078289
theorem B2237863 : Blo 1768085 2237863 := bstep (se 1 (by rfl) ⟨1678397, by rfl⟩ : syracuseStep 2237863 = 3356795) B3356795
theorem B7554617 : Blo 1768085 7554617 := bstep (se 2 (by rfl) ⟨2832981, by rfl⟩ : syracuseStep 7554617 = 5665963) B5665963
theorem B15115997 : Blo 1768085 15115997 := bstep (se 3 (by rfl) ⟨2834249, by rfl⟩ : syracuseStep 15115997 = 5668499) B5668499
theorem B2238187 : Blo 1768085 2238187 := bstep (se 1 (by rfl) ⟨1678640, by rfl⟩ : syracuseStep 2238187 = 3357281) B3357281
theorem B18147203 : Blo 1768085 18147203 := bstep (se 1 (by rfl) ⟨13610402, by rfl⟩ : syracuseStep 18147203 = 27220805) B27220805
theorem B17238131 : Blo 1768085 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B8956169 : Blo 1768085 8956169 := bstep (se 2 (by rfl) ⟨3358563, by rfl⟩ : syracuseStep 8956169 = 6717127) B6717127
theorem B57387325 : Blo 1768085 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B2984303 : Blo 1768085 2984303 := bstep (se 1 (by rfl) ⟨2238227, by rfl⟩ : syracuseStep 2984303 = 4476455) B4476455
theorem B10078607 : Blo 1768085 10078607 := bstep (se 1 (by rfl) ⟨7558955, by rfl⟩ : syracuseStep 10078607 = 15117911) B15117911
theorem B13437413 : Blo 1768085 13437413 := bstep (se 4 (by rfl) ⟨1259757, by rfl⟩ : syracuseStep 13437413 = 2519515) B2519515
theorem B2984519 : Blo 1768085 2984519 := bstep (se 1 (by rfl) ⟨2238389, by rfl⟩ : syracuseStep 2984519 = 4476779) B4476779
theorem B12749399 : Blo 1768085 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B4475513 : Blo 1768085 4475513 := bstep (se 2 (by rfl) ⟨1678317, by rfl⟩ : syracuseStep 4475513 = 3356635) B3356635
theorem B8612527 : Blo 1768085 8612527 := bstep (se 1 (by rfl) ⟨6459395, by rfl⟩ : syracuseStep 8612527 = 12918791) B12918791
theorem B2239159 : Blo 1768085 2239159 := bstep (se 1 (by rfl) ⟨1679369, by rfl⟩ : syracuseStep 2239159 = 3358739) B3358739
theorem B17238851 : Blo 1768085 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B11332487 : Blo 1768085 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B2984951 : Blo 1768085 2984951 := bstep (se 1 (by rfl) ⟨2238713, by rfl⟩ : syracuseStep 2984951 = 4477427) B4477427
theorem B36326515 : Blo 1768085 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B4844897 : Blo 1768085 4844897 := bstep (se 2 (by rfl) ⟨1816836, by rfl⟩ : syracuseStep 4844897 = 3633673) B3633673
theorem B8957303 : Blo 1768085 8957303 := bstep (se 1 (by rfl) ⟨6717977, by rfl⟩ : syracuseStep 8957303 = 13435955) B13435955
theorem B30641627 : Blo 1768085 30641627 := bstep (se 1 (by rfl) ⟨22981220, by rfl⟩ : syracuseStep 30641627 = 45962441) B45962441
theorem B8957465 : Blo 1768085 8957465 := bstep (se 2 (by rfl) ⟨3359049, by rfl⟩ : syracuseStep 8957465 = 6718099) B6718099
theorem B3780179 : Blo 1768085 3780179 := bstep (se 1 (by rfl) ⟨2835134, by rfl⟩ : syracuseStep 3780179 = 5670269) B5670269
theorem B11488979 : Blo 1768085 11488979 := bstep (se 1 (by rfl) ⟨8616734, by rfl⟩ : syracuseStep 11488979 = 17233469) B17233469
theorem B2985707 : Blo 1768085 2985707 := bstep (se 1 (by rfl) ⟨2239280, by rfl⟩ : syracuseStep 2985707 = 4478561) B4478561
theorem B5746411 : Blo 1768085 5746411 := bstep (se 1 (by rfl) ⟨4309808, by rfl⟩ : syracuseStep 5746411 = 8619617) B8619617
theorem B7556905 : Blo 1768085 7556905 := bstep (se 2 (by rfl) ⟨2833839, by rfl⟩ : syracuseStep 7556905 = 5667679) B5667679
theorem B91868975 : Blo 1768085 91868975 := bstep (se 1 (by rfl) ⟨68901731, by rfl⟩ : syracuseStep 91868975 = 137803463) B137803463
theorem B9081035 : Blo 1768085 9081035 := bstep (se 1 (by rfl) ⟨6810776, by rfl⟩ : syracuseStep 9081035 = 13621553) B13621553
theorem B34001153 : Blo 1768085 34001153 := bstep (se 2 (by rfl) ⟨12750432, by rfl⟩ : syracuseStep 34001153 = 25500865) B25500865
theorem B17240323 : Blo 1768085 17240323 := bstep (se 1 (by rfl) ⟨12930242, by rfl⟩ : syracuseStep 17240323 = 25860485) B25860485
theorem B15118595 : Blo 1768085 15118595 := bstep (se 1 (by rfl) ⟨11338946, by rfl⟩ : syracuseStep 15118595 = 22677893) B22677893
theorem B1888543 : Blo 1768085 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B4477295 : Blo 1768085 4477295 := bstep (se 1 (by rfl) ⟨3357971, by rfl⟩ : syracuseStep 4477295 = 6715943) B6715943
theorem B5968403 : Blo 1768085 5968403 := bstep (se 1 (by rfl) ⟨4476302, by rfl⟩ : syracuseStep 5968403 = 8952605) B8952605
theorem B2986679 : Blo 1768085 2986679 := bstep (se 1 (by rfl) ⟨2240009, by rfl⟩ : syracuseStep 2986679 = 4480019) B4480019
theorem B10072775 : Blo 1768085 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B3978215 : Blo 1768085 3978215 := bstep (se 1 (by rfl) ⟨2983661, by rfl⟩ : syracuseStep 3978215 = 5967323) B5967323
theorem B5665783 : Blo 1768085 5665783 := bstep (se 1 (by rfl) ⟨4249337, by rfl⟩ : syracuseStep 5665783 = 8498675) B8498675
theorem B4477943 : Blo 1768085 4477943 := bstep (se 1 (by rfl) ⟨3358457, by rfl⟩ : syracuseStep 4477943 = 6716915) B6716915
theorem B19125305 : Blo 1768085 19125305 := bstep (se 2 (by rfl) ⟨7171989, by rfl⟩ : syracuseStep 19125305 = 14343979) B14343979
theorem B4478075 : Blo 1768085 4478075 := bstep (se 1 (by rfl) ⟨3358556, by rfl⟩ : syracuseStep 4478075 = 6717113) B6717113
theorem B6714515 : Blo 1768085 6714515 := bstep (se 1 (by rfl) ⟨5035886, by rfl⟩ : syracuseStep 6714515 = 10071773) B10071773
theorem B7173353 : Blo 1768085 7173353 := bstep (se 2 (by rfl) ⟨2690007, by rfl⟩ : syracuseStep 7173353 = 5380015) B5380015
theorem B7558393 : Blo 1768085 7558393 := bstep (se 2 (by rfl) ⟨2834397, by rfl⟩ : syracuseStep 7558393 = 5668795) B5668795
theorem B3978593 : Blo 1768085 3978593 := bstep (se 2 (by rfl) ⟨1491972, by rfl⟩ : syracuseStep 3978593 = 2983945) B2983945
theorem B10073483 : Blo 1768085 10073483 := bstep (se 1 (by rfl) ⟨7555112, by rfl⟩ : syracuseStep 10073483 = 15110225) B15110225
theorem B3978683 : Blo 1768085 3978683 := bstep (se 1 (by rfl) ⟨2984012, by rfl⟩ : syracuseStep 3978683 = 5968025) B5968025
theorem B4781501 : Blo 1768085 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B1889735 : Blo 1768085 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B3978809 : Blo 1768085 3978809 := bstep (se 2 (by rfl) ⟨1492053, by rfl⟩ : syracuseStep 3978809 = 2984107) B2984107
theorem B4249145 : Blo 1768085 4249145 := bstep (se 2 (by rfl) ⟨1593429, by rfl⟩ : syracuseStep 4249145 = 3186859) B3186859
theorem B7370297 : Blo 1768085 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B22664771 : Blo 1768085 22664771 := bstep (se 1 (by rfl) ⟨16998578, by rfl⟩ : syracuseStep 22664771 = 33997157) B33997157
theorem B4781663 : Blo 1768085 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B3831391 : Blo 1768085 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B8951633 : Blo 1768085 8951633 := bstep (se 2 (by rfl) ⟨3356862, by rfl⟩ : syracuseStep 8951633 = 6713725) B6713725
theorem B34453363 : Blo 1768085 34453363 := bstep (se 1 (by rfl) ⟨25840022, by rfl⟩ : syracuseStep 34453363 = 51680045) B51680045
theorem B8288207 : Blo 1768085 8288207 := bstep (se 1 (by rfl) ⟨6216155, by rfl⟩ : syracuseStep 8288207 = 12432311) B12432311
theorem B87242795 : Blo 1768085 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B3979475 : Blo 1768085 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B2652425 : Blo 1768085 2652425 := bstep (se 2 (by rfl) ⟨994659, by rfl⟩ : syracuseStep 2652425 = 1989319) B1989319
theorem B3979529 : Blo 1768085 3979529 := bstep (se 2 (by rfl) ⟨1492323, by rfl⟩ : syracuseStep 3979529 = 2984647) B2984647
theorem B5970185 : Blo 1768085 5970185 := bstep (se 2 (by rfl) ⟨2238819, by rfl⟩ : syracuseStep 5970185 = 4477639) B4477639
theorem B2652527 : Blo 1768085 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B8960381 : Blo 1768085 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B8739197 : Blo 1768085 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B3979745 : Blo 1768085 3979745 := bstep (se 2 (by rfl) ⟨1492404, by rfl⟩ : syracuseStep 3979745 = 2984809) B2984809
theorem B7174651 : Blo 1768085 7174651 := bstep (se 1 (by rfl) ⟨5380988, by rfl⟩ : syracuseStep 7174651 = 10761977) B10761977
theorem B7559675 : Blo 1768085 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B2652743 : Blo 1768085 2652743 := bstep (se 1 (by rfl) ⟨1989557, by rfl⟩ : syracuseStep 2652743 = 3979115) B3979115
theorem B2652779 : Blo 1768085 2652779 := bstep (se 1 (by rfl) ⟨1989584, by rfl⟩ : syracuseStep 2652779 = 3979169) B3979169
theorem B5036651 : Blo 1768085 5036651 := bstep (se 1 (by rfl) ⟨3777488, by rfl⟩ : syracuseStep 5036651 = 7554977) B7554977
theorem B8952443 : Blo 1768085 8952443 := bstep (se 1 (by rfl) ⟨6714332, by rfl⟩ : syracuseStep 8952443 = 13428665) B13428665
theorem B1768159 : Blo 1768085 1768159 := bstep (se 1 (by rfl) ⟨1326119, by rfl⟩ : syracuseStep 1768159 = 2652239) B2652239
theorem B3980051 : Blo 1768085 3980051 := bstep (se 1 (by rfl) ⟨2985038, by rfl⟩ : syracuseStep 3980051 = 5970077) B5970077
theorem B1768239 : Blo 1768085 1768239 := bstep (se 1 (by rfl) ⟨1326179, by rfl⟩ : syracuseStep 1768239 = 2652359) B2652359
theorem B2653007 : Blo 1768085 2653007 := bstep (se 1 (by rfl) ⟨1989755, by rfl⟩ : syracuseStep 2653007 = 3979511) B3979511
theorem B4479887 : Blo 1768085 4479887 := bstep (se 1 (by rfl) ⟨3359915, by rfl⟩ : syracuseStep 4479887 = 6719831) B6719831
theorem B1768347 : Blo 1768085 1768347 := bstep (se 1 (by rfl) ⟨1326260, by rfl⟩ : syracuseStep 1768347 = 2652521) B2652521
theorem B13622201 : Blo 1768085 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B1768399 : Blo 1768085 1768399 := bstep (se 1 (by rfl) ⟨1326299, by rfl⟩ : syracuseStep 1768399 = 2652599) B2652599
theorem B1768423 : Blo 1768085 1768423 := bstep (se 1 (by rfl) ⟨1326317, by rfl⟩ : syracuseStep 1768423 = 2652635) B2652635
theorem B1989607 : Blo 1768085 1989607 := bstep (se 1 (by rfl) ⟨1492205, by rfl⟩ : syracuseStep 1989607 = 2984411) B2984411
theorem B3980411 : Blo 1768085 3980411 := bstep (se 1 (by rfl) ⟨2985308, by rfl⟩ : syracuseStep 3980411 = 5970617) B5970617
theorem B2653403 : Blo 1768085 2653403 := bstep (se 1 (by rfl) ⟨1990052, by rfl⟩ : syracuseStep 2653403 = 3980105) B3980105
theorem B3980537 : Blo 1768085 3980537 := bstep (se 2 (by rfl) ⟨1492701, by rfl⟩ : syracuseStep 3980537 = 2985403) B2985403
theorem B1768735 : Blo 1768085 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B1768795 : Blo 1768085 1768795 := bstep (se 1 (by rfl) ⟨1326596, by rfl⟩ : syracuseStep 1768795 = 2653193) B2653193
theorem B1768815 : Blo 1768085 1768815 := bstep (se 1 (by rfl) ⟨1326611, by rfl⟩ : syracuseStep 1768815 = 2653223) B2653223
theorem B5971319 : Blo 1768085 5971319 := bstep (se 1 (by rfl) ⟨4478489, by rfl⟩ : syracuseStep 5971319 = 8956979) B8956979
theorem B2653577 : Blo 1768085 2653577 := bstep (se 2 (by rfl) ⟨995091, by rfl⟩ : syracuseStep 2653577 = 1990183) B1990183
theorem B3980681 : Blo 1768085 3980681 := bstep (se 2 (by rfl) ⟨1492755, by rfl⟩ : syracuseStep 3980681 = 2985511) B2985511
theorem B4480393 : Blo 1768085 4480393 := bstep (se 2 (by rfl) ⟨1680147, by rfl⟩ : syracuseStep 4480393 = 3360295) B3360295
theorem B1768871 : Blo 1768085 1768871 := bstep (se 1 (by rfl) ⟨1326653, by rfl⟩ : syracuseStep 1768871 = 2653307) B2653307
theorem B5037527 : Blo 1768085 5037527 := bstep (se 1 (by rfl) ⟨3778145, by rfl⟩ : syracuseStep 5037527 = 7556291) B7556291
theorem B4480505 : Blo 1768085 4480505 := bstep (se 2 (by rfl) ⟨1680189, by rfl⟩ : syracuseStep 4480505 = 3360379) B3360379
theorem B1768955 : Blo 1768085 1768955 := bstep (se 1 (by rfl) ⟨1326716, by rfl⟩ : syracuseStep 1768955 = 2653433) B2653433
theorem B3980807 : Blo 1768085 3980807 := bstep (se 1 (by rfl) ⟨2985605, by rfl⟩ : syracuseStep 3980807 = 5971211) B5971211
theorem B1769023 : Blo 1768085 1769023 := bstep (se 1 (by rfl) ⟨1326767, by rfl⟩ : syracuseStep 1769023 = 2653535) B2653535
theorem B1769031 : Blo 1768085 1769031 := bstep (se 1 (by rfl) ⟨1326773, by rfl⟩ : syracuseStep 1769031 = 2653547) B2653547
theorem B11329105 : Blo 1768085 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B3980987 : Blo 1768085 3980987 := bstep (se 1 (by rfl) ⟨2985740, by rfl⟩ : syracuseStep 3980987 = 5971481) B5971481
theorem B1769183 : Blo 1768085 1769183 := bstep (se 1 (by rfl) ⟨1326887, by rfl⟩ : syracuseStep 1769183 = 2653775) B2653775
theorem B2653931 : Blo 1768085 2653931 := bstep (se 1 (by rfl) ⟨1990448, by rfl⟩ : syracuseStep 2653931 = 3980897) B3980897
theorem B1769263 : Blo 1768085 1769263 := bstep (se 1 (by rfl) ⟨1326947, by rfl⟩ : syracuseStep 1769263 = 2653895) B2653895
theorem B3981113 : Blo 1768085 3981113 := bstep (se 2 (by rfl) ⟨1492917, by rfl⟩ : syracuseStep 3981113 = 2985835) B2985835
theorem B15105851 : Blo 1768085 15105851 := bstep (se 1 (by rfl) ⟨11329388, by rfl⟩ : syracuseStep 15105851 = 22658777) B22658777
theorem B34004843 : Blo 1768085 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B4251521 : Blo 1768085 4251521 := bstep (se 2 (by rfl) ⟨1594320, by rfl⟩ : syracuseStep 4251521 = 3188641) B3188641
theorem B12754817 : Blo 1768085 12754817 := bstep (se 2 (by rfl) ⟨4783056, by rfl⟩ : syracuseStep 12754817 = 9566113) B9566113
theorem B1769371 : Blo 1768085 1769371 := bstep (se 1 (by rfl) ⟨1327028, by rfl⟩ : syracuseStep 1769371 = 2654057) B2654057
theorem B1769423 : Blo 1768085 1769423 := bstep (se 1 (by rfl) ⟨1327067, by rfl⟩ : syracuseStep 1769423 = 2654135) B2654135
theorem B2654159 : Blo 1768085 2654159 := bstep (se 1 (by rfl) ⟨1990619, by rfl⟩ : syracuseStep 2654159 = 3981239) B3981239
theorem B1769447 : Blo 1768085 1769447 := bstep (se 1 (by rfl) ⟨1327085, by rfl⟩ : syracuseStep 1769447 = 2654171) B2654171
theorem B6054023 : Blo 1768085 6054023 := bstep (se 1 (by rfl) ⟨4540517, by rfl⟩ : syracuseStep 6054023 = 9081035) B9081035
theorem B22667435 : Blo 1768085 22667435 := bstep (se 1 (by rfl) ⟨17000576, by rfl⟩ : syracuseStep 22667435 = 34001153) B34001153
theorem B1769703 : Blo 1768085 1769703 := bstep (se 1 (by rfl) ⟨1327277, by rfl⟩ : syracuseStep 1769703 = 2654555) B2654555
theorem B3981599 : Blo 1768085 3981599 := bstep (se 1 (by rfl) ⟨2986199, by rfl⟩ : syracuseStep 3981599 = 5972399) B5972399
theorem B2654495 : Blo 1768085 2654495 := bstep (se 1 (by rfl) ⟨1990871, by rfl⟩ : syracuseStep 2654495 = 3981743) B3981743
theorem B2654519 : Blo 1768085 2654519 := bstep (se 1 (by rfl) ⟨1990889, by rfl⟩ : syracuseStep 2654519 = 3981779) B3981779
theorem B22987097 : Blo 1768085 22987097 := bstep (se 2 (by rfl) ⟨8620161, by rfl⟩ : syracuseStep 22987097 = 17240323) B17240323
theorem B2654591 : Blo 1768085 2654591 := bstep (se 1 (by rfl) ⟨1990943, by rfl⟩ : syracuseStep 2654591 = 3981887) B3981887
theorem B1769855 : Blo 1768085 1769855 := bstep (se 1 (by rfl) ⟨1327391, by rfl⟩ : syracuseStep 1769855 = 2654783) B2654783
theorem B2654663 : Blo 1768085 2654663 := bstep (se 1 (by rfl) ⟨1990997, by rfl⟩ : syracuseStep 2654663 = 3981995) B3981995
theorem B1991119 : Blo 1768085 1991119 := bstep (se 1 (by rfl) ⟨1493339, by rfl⟩ : syracuseStep 1991119 = 2986679) B2986679
theorem B1769935 : Blo 1768085 1769935 := bstep (se 1 (by rfl) ⟨1327451, by rfl⟩ : syracuseStep 1769935 = 2654903) B2654903
theorem B6374063 : Blo 1768085 6374063 := bstep (se 1 (by rfl) ⟨4780547, by rfl⟩ : syracuseStep 6374063 = 9561095) B9561095
theorem B17236655 : Blo 1768085 17236655 := bstep (se 1 (by rfl) ⟨12927491, by rfl⟩ : syracuseStep 17236655 = 25854983) B25854983
theorem B2655017 : Blo 1768085 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B2655023 : Blo 1768085 2655023 := bstep (se 1 (by rfl) ⟨1991267, by rfl⟩ : syracuseStep 2655023 = 3982535) B3982535
theorem B3982247 : Blo 1768085 3982247 := bstep (se 1 (by rfl) ⟨2986685, by rfl⟩ : syracuseStep 3982247 = 5973371) B5973371
theorem B3187667 : Blo 1768085 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B3187775 : Blo 1768085 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B10077331 : Blo 1768085 10077331 := bstep (se 1 (by rfl) ⟨7557998, by rfl⟩ : syracuseStep 10077331 = 15115997) B15115997
theorem B5039293 : Blo 1768085 5039293 := bstep (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) B1889735
theorem B7554377 : Blo 1768085 7554377 := bstep (se 2 (by rfl) ⟨2832891, by rfl⟩ : syracuseStep 7554377 = 5665783) B5665783
theorem B11331053 : Blo 1768085 11331053 := bstep (se 3 (by rfl) ⟨2124572, by rfl⟩ : syracuseStep 11331053 = 4249145) B4249145
theorem B5973587 : Blo 1768085 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B5826131 : Blo 1768085 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B6719071 : Blo 1768085 6719071 := bstep (se 1 (by rfl) ⟨5039303, by rfl⟩ : syracuseStep 6719071 = 10078607) B10078607
theorem B10077857 : Blo 1768085 10077857 := bstep (se 2 (by rfl) ⟨3779196, by rfl⟩ : syracuseStep 10077857 = 7558393) B7558393
theorem B5039783 : Blo 1768085 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B2983675 : Blo 1768085 2983675 := bstep (se 1 (by rfl) ⟨2237756, by rfl⟩ : syracuseStep 2983675 = 4475513) B4475513
theorem B5973857 : Blo 1768085 5973857 := bstep (se 2 (by rfl) ⟨2240196, by rfl⟩ : syracuseStep 5973857 = 4480393) B4480393
theorem B2983817 : Blo 1768085 2983817 := bstep (se 2 (by rfl) ⟨1118931, by rfl⟩ : syracuseStep 2983817 = 2237863) B2237863
theorem B3229931 : Blo 1768085 3229931 := bstep (se 1 (by rfl) ⟨2422448, by rfl⟩ : syracuseStep 3229931 = 4844897) B4844897
theorem B2984249 : Blo 1768085 2984249 := bstep (se 2 (by rfl) ⟨1119093, by rfl⟩ : syracuseStep 2984249 = 2238187) B2238187
theorem B7661881 : Blo 1768085 7661881 := bstep (se 2 (by rfl) ⟨2873205, by rfl⟩ : syracuseStep 7661881 = 5746411) B5746411
theorem B61245983 : Blo 1768085 61245983 := bstep (se 1 (by rfl) ⟨45934487, by rfl⟩ : syracuseStep 61245983 = 91868975) B91868975
theorem B10070567 : Blo 1768085 10070567 := bstep (se 1 (by rfl) ⟨7552925, by rfl⟩ : syracuseStep 10070567 = 15105851) B15105851
theorem B22669895 : Blo 1768085 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B10079063 : Blo 1768085 10079063 := bstep (se 1 (by rfl) ⟨7559297, by rfl⟩ : syracuseStep 10079063 = 15118595) B15118595
theorem B2984863 : Blo 1768085 2984863 := bstep (se 1 (by rfl) ⟨2238647, by rfl⟩ : syracuseStep 2984863 = 4477295) B4477295
theorem B2518057 : Blo 1768085 2518057 := bstep (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) B1888543
theorem B76516433 : Blo 1768085 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B10488997 : Blo 1768085 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B2985295 : Blo 1768085 2985295 := bstep (se 1 (by rfl) ⟨2238971, by rfl⟩ : syracuseStep 2985295 = 4477943) B4477943
theorem B12750203 : Blo 1768085 12750203 := bstep (se 1 (by rfl) ⟨9562652, by rfl⟩ : syracuseStep 12750203 = 19125305) B19125305
theorem B2985383 : Blo 1768085 2985383 := bstep (se 1 (by rfl) ⟨2239037, by rfl⟩ : syracuseStep 2985383 = 4478075) B4478075
theorem B4476343 : Blo 1768085 4476343 := bstep (se 1 (by rfl) ⟨3357257, by rfl⟩ : syracuseStep 4476343 = 6714515) B6714515
theorem B2985545 : Blo 1768085 2985545 := bstep (se 2 (by rfl) ⟨1119579, by rfl⟩ : syracuseStep 2985545 = 2239159) B2239159
theorem B5967485 : Blo 1768085 5967485 := bstep (se 3 (by rfl) ⟨1118903, by rfl⟩ : syracuseStep 5967485 = 2237807) B2237807
theorem B15109847 : Blo 1768085 15109847 := bstep (se 1 (by rfl) ⟨11332385, by rfl⟩ : syracuseStep 15109847 = 22664771) B22664771
theorem B183873397 : Blo 1768085 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B20148101 : Blo 1768085 20148101 := bstep (se 4 (by rfl) ⟨1888884, by rfl⟩ : syracuseStep 20148101 = 3777769) B3777769
theorem B5967755 : Blo 1768085 5967755 := bstep (se 1 (by rfl) ⟨4475816, by rfl⟩ : syracuseStep 5967755 = 8951633) B8951633
theorem B5525471 : Blo 1768085 5525471 := bstep (se 1 (by rfl) ⟨4144103, by rfl⟩ : syracuseStep 5525471 = 8288207) B8288207
theorem B48435353 : Blo 1768085 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B8958275 : Blo 1768085 8958275 := bstep (se 1 (by rfl) ⟨6718706, by rfl⟩ : syracuseStep 8958275 = 13437413) B13437413
theorem B10072457 : Blo 1768085 10072457 := bstep (se 2 (by rfl) ⟨3777171, by rfl⟩ : syracuseStep 10072457 = 7554343) B7554343
theorem B8499599 : Blo 1768085 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B5968295 : Blo 1768085 5968295 := bstep (se 1 (by rfl) ⟨4476221, by rfl⟩ : syracuseStep 5968295 = 8952443) B8952443
theorem B2986591 : Blo 1768085 2986591 := bstep (se 1 (by rfl) ⟨2239943, by rfl⟩ : syracuseStep 2986591 = 4479887) B4479887
theorem B9081467 : Blo 1768085 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B5971643 : Blo 1768085 5971643 := bstep (se 1 (by rfl) ⟨4478732, by rfl⟩ : syracuseStep 5971643 = 8957465) B8957465
theorem B5108521 : Blo 1768085 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B10072957 : Blo 1768085 10072957 := bstep (se 3 (by rfl) ⟨1888679, by rfl⟩ : syracuseStep 10072957 = 3777359) B3777359
theorem B20427751 : Blo 1768085 20427751 := bstep (se 1 (by rfl) ⟨15320813, by rfl⟩ : syracuseStep 20427751 = 30641627) B30641627
theorem B2987003 : Blo 1768085 2987003 := bstep (se 1 (by rfl) ⟨2240252, by rfl⟩ : syracuseStep 2987003 = 4480505) B4480505
theorem B2520119 : Blo 1768085 2520119 := bstep (se 1 (by rfl) ⟨1890089, by rfl⟩ : syracuseStep 2520119 = 3780179) B3780179
theorem B45937817 : Blo 1768085 45937817 := bstep (se 2 (by rfl) ⟨17226681, by rfl⟩ : syracuseStep 45937817 = 34453363) B34453363
theorem B6378907 : Blo 1768085 6378907 := bstep (se 1 (by rfl) ⟨4784180, by rfl⟩ : syracuseStep 6378907 = 9568361) B9568361
theorem B3978935 : Blo 1768085 3978935 := bstep (se 1 (by rfl) ⟨2984201, by rfl⟩ : syracuseStep 3978935 = 5968403) B5968403
theorem B5969591 : Blo 1768085 5969591 := bstep (se 1 (by rfl) ⟨4477193, by rfl⟩ : syracuseStep 5969591 = 8954387) B8954387
theorem B6715183 : Blo 1768085 6715183 := bstep (se 1 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 6715183 = 10072775) B10072775
theorem B4478935 : Blo 1768085 4478935 := bstep (se 1 (by rfl) ⟨3359201, by rfl⟩ : syracuseStep 4478935 = 6718403) B6718403
theorem B2652143 : Blo 1768085 2652143 := bstep (se 1 (by rfl) ⟨1989107, by rfl⟩ : syracuseStep 2652143 = 3978215) B3978215
theorem B9566201 : Blo 1768085 9566201 := bstep (se 2 (by rfl) ⟨3587325, by rfl⟩ : syracuseStep 9566201 = 7174651) B7174651
theorem B4782235 : Blo 1768085 4782235 := bstep (se 1 (by rfl) ⟨3586676, by rfl⟩ : syracuseStep 4782235 = 7173353) B7173353
theorem B4036763 : Blo 1768085 4036763 := bstep (se 1 (by rfl) ⟨3027572, by rfl⟩ : syracuseStep 4036763 = 6055145) B6055145
theorem B11483369 : Blo 1768085 11483369 := bstep (se 2 (by rfl) ⟨4306263, by rfl⟩ : syracuseStep 11483369 = 8612527) B8612527
theorem B4479209 : Blo 1768085 4479209 := bstep (se 2 (by rfl) ⟨1679703, by rfl⟩ : syracuseStep 4479209 = 3359407) B3359407
theorem B2652395 : Blo 1768085 2652395 := bstep (se 1 (by rfl) ⟨1989296, by rfl⟩ : syracuseStep 2652395 = 3978593) B3978593
theorem B6715655 : Blo 1768085 6715655 := bstep (se 1 (by rfl) ⟨5036741, by rfl⟩ : syracuseStep 6715655 = 10073483) B10073483
theorem B4479239 : Blo 1768085 4479239 := bstep (se 1 (by rfl) ⟨3359429, by rfl⟩ : syracuseStep 4479239 = 6718859) B6718859
theorem B2652455 : Blo 1768085 2652455 := bstep (se 1 (by rfl) ⟨1989341, by rfl⟩ : syracuseStep 2652455 = 3978683) B3978683
theorem B2652539 : Blo 1768085 2652539 := bstep (se 1 (by rfl) ⟨1989404, by rfl⟩ : syracuseStep 2652539 = 3978809) B3978809
theorem B5036411 : Blo 1768085 5036411 := bstep (se 1 (by rfl) ⟨3777308, by rfl⟩ : syracuseStep 5036411 = 7554617) B7554617
theorem B4913531 : Blo 1768085 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B12098135 : Blo 1768085 12098135 := bstep (se 1 (by rfl) ⟨9073601, by rfl⟩ : syracuseStep 12098135 = 18147203) B18147203
theorem B2652809 : Blo 1768085 2652809 := bstep (se 2 (by rfl) ⟨994803, by rfl⟩ : syracuseStep 2652809 = 1989607) B1989607
theorem B58161863 : Blo 1768085 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B2652983 : Blo 1768085 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B1768283 : Blo 1768085 1768283 := bstep (se 1 (by rfl) ⟨1326212, by rfl⟩ : syracuseStep 1768283 = 2652425) B2652425
theorem B2653019 : Blo 1768085 2653019 := bstep (se 1 (by rfl) ⟨1989764, by rfl⟩ : syracuseStep 2653019 = 3979529) B3979529
theorem B3980123 : Blo 1768085 3980123 := bstep (se 1 (by rfl) ⟨2985092, by rfl⟩ : syracuseStep 3980123 = 5970185) B5970185
theorem B5970779 : Blo 1768085 5970779 := bstep (se 1 (by rfl) ⟨4478084, by rfl⟩ : syracuseStep 5970779 = 8956169) B8956169
theorem B1768351 : Blo 1768085 1768351 := bstep (se 1 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 1768351 = 2652527) B2652527
theorem B1989535 : Blo 1768085 1989535 := bstep (se 1 (by rfl) ⟨1492151, by rfl⟩ : syracuseStep 1989535 = 2984303) B2984303
theorem B2653163 : Blo 1768085 2653163 := bstep (se 1 (by rfl) ⟨1989872, by rfl⟩ : syracuseStep 2653163 = 3979745) B3979745
theorem B1768495 : Blo 1768085 1768495 := bstep (se 1 (by rfl) ⟨1326371, by rfl⟩ : syracuseStep 1768495 = 2652743) B2652743
theorem B1989679 : Blo 1768085 1989679 := bstep (se 1 (by rfl) ⟨1492259, by rfl⟩ : syracuseStep 1989679 = 2984519) B2984519
theorem B11328569 : Blo 1768085 11328569 := bstep (se 2 (by rfl) ⟨4248213, by rfl⟩ : syracuseStep 11328569 = 8496427) B8496427
theorem B1768519 : Blo 1768085 1768519 := bstep (se 1 (by rfl) ⟨1326389, by rfl⟩ : syracuseStep 1768519 = 2652779) B2652779
theorem B3357767 : Blo 1768085 3357767 := bstep (se 1 (by rfl) ⟨2518325, by rfl⟩ : syracuseStep 3357767 = 5036651) B5036651
theorem B2653367 : Blo 1768085 2653367 := bstep (se 1 (by rfl) ⟨1990025, by rfl⟩ : syracuseStep 2653367 = 3980051) B3980051
theorem B11492567 : Blo 1768085 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B1768671 : Blo 1768085 1768671 := bstep (se 1 (by rfl) ⟨1326503, by rfl⟩ : syracuseStep 1768671 = 2653007) B2653007
theorem B1989967 : Blo 1768085 1989967 := bstep (se 1 (by rfl) ⟨1492475, by rfl⟩ : syracuseStep 1989967 = 2984951) B2984951
theorem B2653607 : Blo 1768085 2653607 := bstep (se 1 (by rfl) ⟨1990205, by rfl⟩ : syracuseStep 2653607 = 3980411) B3980411
theorem B15105473 : Blo 1768085 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B1768935 : Blo 1768085 1768935 := bstep (se 1 (by rfl) ⟨1326701, by rfl⟩ : syracuseStep 1768935 = 2653403) B2653403
theorem B2653691 : Blo 1768085 2653691 := bstep (se 1 (by rfl) ⟨1990268, by rfl⟩ : syracuseStep 2653691 = 3980537) B3980537
theorem B3980879 : Blo 1768085 3980879 := bstep (se 1 (by rfl) ⟨2985659, by rfl⟩ : syracuseStep 3980879 = 5971319) B5971319
theorem B5971535 : Blo 1768085 5971535 := bstep (se 1 (by rfl) ⟨4478651, by rfl⟩ : syracuseStep 5971535 = 8957303) B8957303
theorem B1769051 : Blo 1768085 1769051 := bstep (se 1 (by rfl) ⟨1326788, by rfl⟩ : syracuseStep 1769051 = 2653577) B2653577
theorem B2653787 : Blo 1768085 2653787 := bstep (se 1 (by rfl) ⟨1990340, by rfl⟩ : syracuseStep 2653787 = 3980681) B3980681
theorem B3358351 : Blo 1768085 3358351 := bstep (se 1 (by rfl) ⟨2518763, by rfl⟩ : syracuseStep 3358351 = 5037527) B5037527
theorem B2653871 : Blo 1768085 2653871 := bstep (se 1 (by rfl) ⟨1990403, by rfl⟩ : syracuseStep 2653871 = 3980807) B3980807
theorem B30219965 : Blo 1768085 30219965 := bstep (se 3 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 30219965 = 11332487) B11332487
theorem B10075873 : Blo 1768085 10075873 := bstep (se 2 (by rfl) ⟨3778452, by rfl⟩ : syracuseStep 10075873 = 7556905) B7556905
theorem B2653991 : Blo 1768085 2653991 := bstep (se 1 (by rfl) ⟨1990493, by rfl⟩ : syracuseStep 2653991 = 3980987) B3980987
theorem B7659319 : Blo 1768085 7659319 := bstep (se 1 (by rfl) ⟨5744489, by rfl⟩ : syracuseStep 7659319 = 11488979) B11488979
theorem B1769287 : Blo 1768085 1769287 := bstep (se 1 (by rfl) ⟨1326965, by rfl⟩ : syracuseStep 1769287 = 2653931) B2653931
theorem B1990471 : Blo 1768085 1990471 := bstep (se 1 (by rfl) ⟨1492853, by rfl⟩ : syracuseStep 1990471 = 2985707) B2985707
theorem B2654075 : Blo 1768085 2654075 := bstep (se 1 (by rfl) ⟨1990556, by rfl⟩ : syracuseStep 2654075 = 3981113) B3981113
theorem B2834347 : Blo 1768085 2834347 := bstep (se 1 (by rfl) ⟨2125760, by rfl⟩ : syracuseStep 2834347 = 4251521) B4251521
theorem B8503211 : Blo 1768085 8503211 := bstep (se 1 (by rfl) ⟨6377408, by rfl⟩ : syracuseStep 8503211 = 12754817) B12754817
theorem B1769439 : Blo 1768085 1769439 := bstep (se 1 (by rfl) ⟨1327079, by rfl⟩ : syracuseStep 1769439 = 2654159) B2654159
theorem B2654399 : Blo 1768085 2654399 := bstep (se 1 (by rfl) ⟨1990799, by rfl⟩ : syracuseStep 2654399 = 3981599) B3981599
theorem B1769663 : Blo 1768085 1769663 := bstep (se 1 (by rfl) ⟨1327247, by rfl⟩ : syracuseStep 1769663 = 2654495) B2654495
theorem B1769679 : Blo 1768085 1769679 := bstep (se 1 (by rfl) ⟨1327259, by rfl⟩ : syracuseStep 1769679 = 2654519) B2654519
theorem B5972183 : Blo 1768085 5972183 := bstep (se 1 (by rfl) ⟨4479137, by rfl⟩ : syracuseStep 5972183 = 8958275) B8958275
theorem B1769727 : Blo 1768085 1769727 := bstep (se 1 (by rfl) ⟨1327295, by rfl⟩ : syracuseStep 1769727 = 2654591) B2654591
theorem B1769775 : Blo 1768085 1769775 := bstep (se 1 (by rfl) ⟨1327331, by rfl⟩ : syracuseStep 1769775 = 2654663) B2654663
theorem B10215841 : Blo 1768085 10215841 := bstep (se 2 (by rfl) ⟨3830940, by rfl⟩ : syracuseStep 10215841 = 7661881) B7661881
theorem B6054311 : Blo 1768085 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B1770011 : Blo 1768085 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B1770015 : Blo 1768085 1770015 := bstep (se 1 (by rfl) ⟨1327511, by rfl⟩ : syracuseStep 1770015 = 2655023) B2655023
theorem B2654825 : Blo 1768085 2654825 := bstep (se 2 (by rfl) ⟨995559, by rfl⟩ : syracuseStep 2654825 = 1991119) B1991119
theorem B2654831 : Blo 1768085 2654831 := bstep (se 1 (by rfl) ⟨1991123, by rfl⟩ : syracuseStep 2654831 = 3982247) B3982247
theorem B1991335 : Blo 1768085 1991335 := bstep (se 1 (by rfl) ⟨1493501, by rfl⟩ : syracuseStep 1991335 = 2987003) B2987003
theorem B3982121 : Blo 1768085 3982121 := bstep (se 2 (by rfl) ⟨1493295, by rfl⟩ : syracuseStep 3982121 = 2986591) B2986591
theorem B7554035 : Blo 1768085 7554035 := bstep (se 1 (by rfl) ⟨5665526, by rfl⟩ : syracuseStep 7554035 = 11331053) B11331053
theorem B3982391 : Blo 1768085 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B3884087 : Blo 1768085 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B6718571 : Blo 1768085 6718571 := bstep (se 1 (by rfl) ⟨5038928, by rfl⟩ : syracuseStep 6718571 = 10077857) B10077857
theorem B3359855 : Blo 1768085 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B3982571 : Blo 1768085 3982571 := bstep (se 1 (by rfl) ⟨2986928, by rfl⟩ : syracuseStep 3982571 = 5973857) B5973857
theorem B13436441 : Blo 1768085 13436441 := bstep (se 2 (by rfl) ⟨5038665, by rfl⟩ : syracuseStep 13436441 = 10077331) B10077331
theorem B13985329 : Blo 1768085 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B6719057 : Blo 1768085 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B40830655 : Blo 1768085 40830655 := bstep (se 1 (by rfl) ⟨30622991, by rfl⟩ : syracuseStep 40830655 = 61245983) B61245983
theorem B38774575 : Blo 1768085 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B8505209 : Blo 1768085 8505209 := bstep (se 2 (by rfl) ⟨3189453, by rfl⟩ : syracuseStep 8505209 = 6378907) B6378907
theorem B6719375 : Blo 1768085 6719375 := bstep (se 1 (by rfl) ⟨5039531, by rfl⟩ : syracuseStep 6719375 = 10079063) B10079063
theorem B2238511 : Blo 1768085 2238511 := bstep (se 1 (by rfl) ⟨1678883, by rfl⟩ : syracuseStep 2238511 = 3357767) B3357767
theorem B7661711 : Blo 1768085 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B10070315 : Blo 1768085 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B20146643 : Blo 1768085 20146643 := bstep (se 1 (by rfl) ⟨15109982, by rfl⟩ : syracuseStep 20146643 = 30219965) B30219965
theorem B245164529 : Blo 1768085 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B3779129 : Blo 1768085 3779129 := bstep (se 2 (by rfl) ⟨1417173, by rfl⟩ : syracuseStep 3779129 = 2834347) B2834347
theorem B6720317 : Blo 1768085 6720317 := bstep (se 3 (by rfl) ⟨1260059, by rfl⟩ : syracuseStep 6720317 = 2520119) B2520119
theorem B6376313 : Blo 1768085 6376313 := bstep (se 2 (by rfl) ⟨2391117, by rfl⟩ : syracuseStep 6376313 = 4782235) B4782235
theorem B13429637 : Blo 1768085 13429637 := bstep (se 4 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 13429637 = 2518057) B2518057
theorem B2125111 : Blo 1768085 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B30625211 : Blo 1768085 30625211 := bstep (se 1 (by rfl) ⟨22968908, by rfl⟩ : syracuseStep 30625211 = 45937817) B45937817
theorem B6811361 : Blo 1768085 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B13430609 : Blo 1768085 13430609 := bstep (se 2 (by rfl) ⟨5036478, by rfl⟩ : syracuseStep 13430609 = 10072957) B10072957
theorem B6377467 : Blo 1768085 6377467 := bstep (se 1 (by rfl) ⟨4783100, by rfl⟩ : syracuseStep 6377467 = 9566201) B9566201
theorem B2691175 : Blo 1768085 2691175 := bstep (se 1 (by rfl) ⟨2018381, by rfl⟩ : syracuseStep 2691175 = 4036763) B4036763
theorem B7655579 : Blo 1768085 7655579 := bstep (se 1 (by rfl) ⟨5741684, by rfl⟩ : syracuseStep 7655579 = 11483369) B11483369
theorem B2986139 : Blo 1768085 2986139 := bstep (se 1 (by rfl) ⟨2239604, by rfl⟩ : syracuseStep 2986139 = 4479209) B4479209
theorem B4477103 : Blo 1768085 4477103 := bstep (se 1 (by rfl) ⟨3357827, by rfl⟩ : syracuseStep 4477103 = 6715655) B6715655
theorem B2986159 : Blo 1768085 2986159 := bstep (se 1 (by rfl) ⟨2239619, by rfl⟩ : syracuseStep 2986159 = 4479239) B4479239
theorem B6713711 : Blo 1768085 6713711 := bstep (se 1 (by rfl) ⟨5035283, by rfl⟩ : syracuseStep 6713711 = 10070567) B10070567
theorem B8065423 : Blo 1768085 8065423 := bstep (se 1 (by rfl) ⟨6049067, by rfl⟩ : syracuseStep 8065423 = 12098135) B12098135
theorem B5968457 : Blo 1768085 5968457 := bstep (se 2 (by rfl) ⟨2238171, by rfl⟩ : syracuseStep 5968457 = 4476343) B4476343
theorem B8958761 : Blo 1768085 8958761 := bstep (se 2 (by rfl) ⟨3359535, by rfl⟩ : syracuseStep 8958761 = 6719071) B6719071
theorem B4477801 : Blo 1768085 4477801 := bstep (se 2 (by rfl) ⟨1679175, by rfl⟩ : syracuseStep 4477801 = 3358351) B3358351
theorem B8500135 : Blo 1768085 8500135 := bstep (se 1 (by rfl) ⟨6375101, by rfl⟩ : syracuseStep 8500135 = 12750203) B12750203
theorem B3978233 : Blo 1768085 3978233 := bstep (se 2 (by rfl) ⟨1491837, by rfl⟩ : syracuseStep 3978233 = 2983675) B2983675
theorem B10212425 : Blo 1768085 10212425 := bstep (se 2 (by rfl) ⟨3829659, by rfl⟩ : syracuseStep 10212425 = 7659319) B7659319
theorem B3978323 : Blo 1768085 3978323 := bstep (se 1 (by rfl) ⟨2983742, by rfl⟩ : syracuseStep 3978323 = 5967485) B5967485
theorem B10073231 : Blo 1768085 10073231 := bstep (se 1 (by rfl) ⟨7554923, by rfl⟩ : syracuseStep 10073231 = 15109847) B15109847
theorem B13432067 : Blo 1768085 13432067 := bstep (se 1 (by rfl) ⟨10074050, by rfl⟩ : syracuseStep 13432067 = 20148101) B20148101
theorem B3978503 : Blo 1768085 3978503 := bstep (se 1 (by rfl) ⟨2983877, by rfl⟩ : syracuseStep 3978503 = 5967755) B5967755
theorem B3683647 : Blo 1768085 3683647 := bstep (se 1 (by rfl) ⟨2762735, by rfl⟩ : syracuseStep 3683647 = 5525471) B5525471
theorem B4036015 : Blo 1768085 4036015 := bstep (se 1 (by rfl) ⟨3027011, by rfl⟩ : syracuseStep 4036015 = 6054023) B6054023
theorem B32290235 : Blo 1768085 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B15111623 : Blo 1768085 15111623 := bstep (se 1 (by rfl) ⟨11333717, by rfl⟩ : syracuseStep 15111623 = 22667435) B22667435
theorem B8500733 : Blo 1768085 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B15324731 : Blo 1768085 15324731 := bstep (se 1 (by rfl) ⟨11493548, by rfl⟩ : syracuseStep 15324731 = 22987097) B22987097
theorem B6714971 : Blo 1768085 6714971 := bstep (se 1 (by rfl) ⟨5036228, by rfl⟩ : syracuseStep 6714971 = 10072457) B10072457
theorem B5666399 : Blo 1768085 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B3978863 : Blo 1768085 3978863 := bstep (se 1 (by rfl) ⟨2984147, by rfl⟩ : syracuseStep 3978863 = 5968295) B5968295
theorem B11491103 : Blo 1768085 11491103 := bstep (se 1 (by rfl) ⟨8618327, by rfl⟩ : syracuseStep 11491103 = 17236655) B17236655
theorem B5036251 : Blo 1768085 5036251 := bstep (se 1 (by rfl) ⟨3777188, by rfl⟩ : syracuseStep 5036251 = 7554377) B7554377
theorem B2652623 : Blo 1768085 2652623 := bstep (se 1 (by rfl) ⟨1989467, by rfl⟩ : syracuseStep 2652623 = 3978935) B3978935
theorem B3979727 : Blo 1768085 3979727 := bstep (se 1 (by rfl) ⟨2984795, by rfl⟩ : syracuseStep 3979727 = 5969591) B5969591
theorem B2652713 : Blo 1768085 2652713 := bstep (se 2 (by rfl) ⟨994767, by rfl⟩ : syracuseStep 2652713 = 1989535) B1989535
theorem B3979817 : Blo 1768085 3979817 := bstep (se 2 (by rfl) ⟨1492431, by rfl⟩ : syracuseStep 3979817 = 2984863) B2984863
theorem B1989211 : Blo 1768085 1989211 := bstep (se 1 (by rfl) ⟨1491908, by rfl⟩ : syracuseStep 1989211 = 2983817) B2983817
theorem B27237001 : Blo 1768085 27237001 := bstep (se 2 (by rfl) ⟨10213875, by rfl⟩ : syracuseStep 27237001 = 20427751) B20427751
theorem B1768095 : Blo 1768085 1768095 := bstep (se 1 (by rfl) ⟨1326071, by rfl⟩ : syracuseStep 1768095 = 2652143) B2652143
theorem B2652905 : Blo 1768085 2652905 := bstep (se 2 (by rfl) ⟨994839, by rfl⟩ : syracuseStep 2652905 = 1989679) B1989679
theorem B2153287 : Blo 1768085 2153287 := bstep (se 1 (by rfl) ⟨1614965, by rfl⟩ : syracuseStep 2153287 = 3229931) B3229931
theorem B1768263 : Blo 1768085 1768263 := bstep (se 1 (by rfl) ⟨1326197, by rfl⟩ : syracuseStep 1768263 = 2652395) B2652395
theorem B1768303 : Blo 1768085 1768303 := bstep (se 1 (by rfl) ⟨1326227, by rfl⟩ : syracuseStep 1768303 = 2652455) B2652455
theorem B1989499 : Blo 1768085 1989499 := bstep (se 1 (by rfl) ⟨1492124, by rfl⟩ : syracuseStep 1989499 = 2984249) B2984249
theorem B1768359 : Blo 1768085 1768359 := bstep (se 1 (by rfl) ⟨1326269, by rfl⟩ : syracuseStep 1768359 = 2652539) B2652539
theorem B3357607 : Blo 1768085 3357607 := bstep (se 1 (by rfl) ⟨2518205, by rfl⟩ : syracuseStep 3357607 = 5036411) B5036411
theorem B3275687 : Blo 1768085 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B15113263 : Blo 1768085 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B1768539 : Blo 1768085 1768539 := bstep (se 1 (by rfl) ⟨1326404, by rfl⟩ : syracuseStep 1768539 = 2652809) B2652809
theorem B2653289 : Blo 1768085 2653289 := bstep (se 2 (by rfl) ⟨994983, by rfl⟩ : syracuseStep 2653289 = 1989967) B1989967
theorem B3980393 : Blo 1768085 3980393 := bstep (se 2 (by rfl) ⟨1492647, by rfl⟩ : syracuseStep 3980393 = 2985295) B2985295
theorem B16997501 : Blo 1768085 16997501 := bstep (se 3 (by rfl) ⟨3187031, by rfl⟩ : syracuseStep 16997501 = 6374063) B6374063
theorem B1768655 : Blo 1768085 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B1768679 : Blo 1768085 1768679 := bstep (se 1 (by rfl) ⟨1326509, by rfl⟩ : syracuseStep 1768679 = 2653019) B2653019
theorem B2653415 : Blo 1768085 2653415 := bstep (se 1 (by rfl) ⟨1990061, by rfl⟩ : syracuseStep 2653415 = 3980123) B3980123
theorem B3980519 : Blo 1768085 3980519 := bstep (se 1 (by rfl) ⟨2985389, by rfl⟩ : syracuseStep 3980519 = 5970779) B5970779
theorem B1768775 : Blo 1768085 1768775 := bstep (se 1 (by rfl) ⟨1326581, by rfl⟩ : syracuseStep 1768775 = 2653163) B2653163
theorem B7552379 : Blo 1768085 7552379 := bstep (se 1 (by rfl) ⟨5664284, by rfl⟩ : syracuseStep 7552379 = 11328569) B11328569
theorem B51010955 : Blo 1768085 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B1768911 : Blo 1768085 1768911 := bstep (se 1 (by rfl) ⟨1326683, by rfl⟩ : syracuseStep 1768911 = 2653367) B2653367
theorem B1769071 : Blo 1768085 1769071 := bstep (se 1 (by rfl) ⟨1326803, by rfl⟩ : syracuseStep 1769071 = 2653607) B2653607
theorem B1990255 : Blo 1768085 1990255 := bstep (se 1 (by rfl) ⟨1492691, by rfl⟩ : syracuseStep 1990255 = 2985383) B2985383
theorem B13434497 : Blo 1768085 13434497 := bstep (se 2 (by rfl) ⟨5037936, by rfl⟩ : syracuseStep 13434497 = 10075873) B10075873
theorem B1769127 : Blo 1768085 1769127 := bstep (se 1 (by rfl) ⟨1326845, by rfl⟩ : syracuseStep 1769127 = 2653691) B2653691
theorem B1990363 : Blo 1768085 1990363 := bstep (se 1 (by rfl) ⟨1492772, by rfl⟩ : syracuseStep 1990363 = 2985545) B2985545
theorem B2653919 : Blo 1768085 2653919 := bstep (se 1 (by rfl) ⟨1990439, by rfl⟩ : syracuseStep 2653919 = 3980879) B3980879
theorem B3981023 : Blo 1768085 3981023 := bstep (se 1 (by rfl) ⟨2985767, by rfl⟩ : syracuseStep 3981023 = 5971535) B5971535
theorem B1769191 : Blo 1768085 1769191 := bstep (se 1 (by rfl) ⟨1326893, by rfl⟩ : syracuseStep 1769191 = 2653787) B2653787
theorem B8953577 : Blo 1768085 8953577 := bstep (se 2 (by rfl) ⟨3357591, by rfl⟩ : syracuseStep 8953577 = 6715183) B6715183
theorem B2653961 : Blo 1768085 2653961 := bstep (se 2 (by rfl) ⟨995235, by rfl⟩ : syracuseStep 2653961 = 1990471) B1990471
theorem B1769247 : Blo 1768085 1769247 := bstep (se 1 (by rfl) ⟨1326935, by rfl⟩ : syracuseStep 1769247 = 2653871) B2653871
theorem B3981095 : Blo 1768085 3981095 := bstep (se 1 (by rfl) ⟨2985821, by rfl⟩ : syracuseStep 3981095 = 5971643) B5971643
theorem B1769327 : Blo 1768085 1769327 := bstep (se 1 (by rfl) ⟨1326995, by rfl⟩ : syracuseStep 1769327 = 2653991) B2653991
theorem B1769383 : Blo 1768085 1769383 := bstep (se 1 (by rfl) ⟨1327037, by rfl⟩ : syracuseStep 1769383 = 2654075) B2654075
theorem B5668807 : Blo 1768085 5668807 := bstep (se 1 (by rfl) ⟨4251605, by rfl⟩ : syracuseStep 5668807 = 8503211) B8503211
theorem B5971913 : Blo 1768085 5971913 := bstep (se 2 (by rfl) ⟨2239467, by rfl⟩ : syracuseStep 5971913 = 4478935) B4478935
theorem B5103719 : Blo 1768085 5103719 := bstep (se 1 (by rfl) ⟨3827789, by rfl⟩ : syracuseStep 5103719 = 7655579) B7655579
theorem B1990759 : Blo 1768085 1990759 := bstep (se 1 (by rfl) ⟨1493069, by rfl⟩ : syracuseStep 1990759 = 2986139) B2986139
theorem B1769599 : Blo 1768085 1769599 := bstep (se 1 (by rfl) ⟨1327199, by rfl⟩ : syracuseStep 1769599 = 2654399) B2654399
theorem B3588233 : Blo 1768085 3588233 := bstep (se 2 (by rfl) ⟨1345587, by rfl⟩ : syracuseStep 3588233 = 2691175) B2691175
theorem B3981455 : Blo 1768085 3981455 := bstep (se 1 (by rfl) ⟨2986091, by rfl⟩ : syracuseStep 3981455 = 5972183) B5972183
theorem B3981545 : Blo 1768085 3981545 := bstep (se 2 (by rfl) ⟨1493079, by rfl⟩ : syracuseStep 3981545 = 2986159) B2986159
theorem B1769883 : Blo 1768085 1769883 := bstep (se 1 (by rfl) ⟨1327412, by rfl⟩ : syracuseStep 1769883 = 2654825) B2654825
theorem B1769887 : Blo 1768085 1769887 := bstep (se 1 (by rfl) ⟨1327415, by rfl⟩ : syracuseStep 1769887 = 2654831) B2654831
theorem B5972507 : Blo 1768085 5972507 := bstep (se 1 (by rfl) ⟨4479380, by rfl⟩ : syracuseStep 5972507 = 8958761) B8958761
theorem B2654747 : Blo 1768085 2654747 := bstep (se 1 (by rfl) ⟨1991060, by rfl⟩ : syracuseStep 2654747 = 3982121) B3982121
theorem B2654927 : Blo 1768085 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B2589391 : Blo 1768085 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B6808283 : Blo 1768085 6808283 := bstep (se 1 (by rfl) ⟨5106212, by rfl⟩ : syracuseStep 6808283 = 10212425) B10212425
theorem B2655047 : Blo 1768085 2655047 := bstep (se 1 (by rfl) ⟨1991285, by rfl⟩ : syracuseStep 2655047 = 3982571) B3982571
theorem B8954711 : Blo 1768085 8954711 := bstep (se 1 (by rfl) ⟨6716033, by rfl⟩ : syracuseStep 8954711 = 13432067) B13432067
theorem B36316001 : Blo 1768085 36316001 := bstep (se 2 (by rfl) ⟨13618500, by rfl⟩ : syracuseStep 36316001 = 27237001) B27237001
theorem B2655113 : Blo 1768085 2655113 := bstep (se 2 (by rfl) ⟨995667, by rfl⟩ : syracuseStep 2655113 = 1991335) B1991335
theorem B10216487 : Blo 1768085 10216487 := bstep (se 1 (by rfl) ⟨7662365, by rfl⟩ : syracuseStep 10216487 = 15324731) B15324731
theorem B3777599 : Blo 1768085 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B18647105 : Blo 1768085 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B11331667 : Blo 1768085 11331667 := bstep (se 1 (by rfl) ⟨8498750, by rfl⟩ : syracuseStep 11331667 = 16997501) B16997501
theorem B34007303 : Blo 1768085 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B20416807 : Blo 1768085 20416807 := bstep (se 1 (by rfl) ⟨15312605, by rfl⟩ : syracuseStep 20416807 = 30625211) B30625211
theorem B8956331 : Blo 1768085 8956331 := bstep (se 1 (by rfl) ⟨6717248, by rfl⟩ : syracuseStep 8956331 = 13434497) B13434497
theorem B4540907 : Blo 1768085 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B2984681 : Blo 1768085 2984681 := bstep (se 2 (by rfl) ⟨1119255, by rfl⟩ : syracuseStep 2984681 = 2238511) B2238511
theorem B2984735 : Blo 1768085 2984735 := bstep (se 1 (by rfl) ⟨2238551, by rfl⟩ : syracuseStep 2984735 = 4477103) B4477103
theorem B4475807 : Blo 1768085 4475807 := bstep (se 1 (by rfl) ⟨3356855, by rfl⟩ : syracuseStep 4475807 = 6713711) B6713711
theorem B2239903 : Blo 1768085 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B8503289 : Blo 1768085 8503289 := bstep (se 2 (by rfl) ⟨3188733, by rfl⟩ : syracuseStep 8503289 = 6377467) B6377467
theorem B8957627 : Blo 1768085 8957627 := bstep (se 1 (by rfl) ⟨6718220, by rfl⟩ : syracuseStep 8957627 = 13436441) B13436441
theorem B4476647 : Blo 1768085 4476647 := bstep (se 1 (by rfl) ⟨3357485, by rfl⟩ : syracuseStep 4476647 = 6714971) B6714971
theorem B2871049 : Blo 1768085 2871049 := bstep (se 2 (by rfl) ⟨1076643, by rfl⟩ : syracuseStep 2871049 = 2153287) B2153287
theorem B11333513 : Blo 1768085 11333513 := bstep (se 2 (by rfl) ⟨4250067, by rfl⟩ : syracuseStep 11333513 = 8500135) B8500135
theorem B4476809 : Blo 1768085 4476809 := bstep (se 2 (by rfl) ⟨1678803, by rfl⟩ : syracuseStep 4476809 = 3357607) B3357607
theorem B5107807 : Blo 1768085 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B6713543 : Blo 1768085 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B13431095 : Blo 1768085 13431095 := bstep (se 1 (by rfl) ⟨10073321, by rfl⟩ : syracuseStep 13431095 = 20146643) B20146643
theorem B163443019 : Blo 1768085 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B2519419 : Blo 1768085 2519419 := bstep (se 1 (by rfl) ⟨1889564, by rfl⟩ : syracuseStep 2519419 = 3779129) B3779129
theorem B4911529 : Blo 1768085 4911529 := bstep (se 2 (by rfl) ⟨1841823, by rfl⟩ : syracuseStep 4911529 = 3683647) B3683647
theorem B2183791 : Blo 1768085 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B30642941 : Blo 1768085 30642941 := bstep (se 3 (by rfl) ⟨5745551, by rfl⟩ : syracuseStep 30642941 = 11491103) B11491103
theorem B4480211 : Blo 1768085 4480211 := bstep (se 1 (by rfl) ⟨3360158, by rfl⟩ : syracuseStep 4480211 = 6720317) B6720317
theorem B5034919 : Blo 1768085 5034919 := bstep (se 1 (by rfl) ⟨3776189, by rfl⟩ : syracuseStep 5034919 = 7552379) B7552379
theorem B54440873 : Blo 1768085 54440873 := bstep (se 2 (by rfl) ⟨20415327, by rfl⟩ : syracuseStep 54440873 = 40830655) B40830655
theorem B22680557 : Blo 1768085 22680557 := bstep (se 3 (by rfl) ⟨4252604, by rfl⟩ : syracuseStep 22680557 = 8505209) B8505209
theorem B5969051 : Blo 1768085 5969051 := bstep (se 1 (by rfl) ⟨4476788, by rfl⟩ : syracuseStep 5969051 = 8953577) B8953577
theorem B7558409 : Blo 1768085 7558409 := bstep (se 2 (by rfl) ⟨2834403, by rfl⟩ : syracuseStep 7558409 = 5668807) B5668807
theorem B6715001 : Blo 1768085 6715001 := bstep (se 2 (by rfl) ⟨2518125, by rfl⟩ : syracuseStep 6715001 = 5036251) B5036251
theorem B3978971 : Blo 1768085 3978971 := bstep (se 1 (by rfl) ⟨2984228, by rfl⟩ : syracuseStep 3978971 = 5968457) B5968457
theorem B10753897 : Blo 1768085 10753897 := bstep (se 2 (by rfl) ⟨4032711, by rfl⟩ : syracuseStep 10753897 = 8065423) B8065423
theorem B13621121 : Blo 1768085 13621121 := bstep (se 2 (by rfl) ⟨5107920, by rfl⟩ : syracuseStep 13621121 = 10215841) B10215841
theorem B5036023 : Blo 1768085 5036023 := bstep (se 1 (by rfl) ⟨3777017, by rfl⟩ : syracuseStep 5036023 = 7554035) B7554035
theorem B2652155 : Blo 1768085 2652155 := bstep (se 1 (by rfl) ⟨1989116, by rfl⟩ : syracuseStep 2652155 = 3978233) B3978233
theorem B2652215 : Blo 1768085 2652215 := bstep (se 1 (by rfl) ⟨1989161, by rfl⟩ : syracuseStep 2652215 = 3978323) B3978323
theorem B4479047 : Blo 1768085 4479047 := bstep (se 1 (by rfl) ⟨3359285, by rfl⟩ : syracuseStep 4479047 = 6718571) B6718571
theorem B6715487 : Blo 1768085 6715487 := bstep (se 1 (by rfl) ⟨5036615, by rfl⟩ : syracuseStep 6715487 = 10073231) B10073231
theorem B2652281 : Blo 1768085 2652281 := bstep (se 2 (by rfl) ⟨994605, by rfl⟩ : syracuseStep 2652281 = 1989211) B1989211
theorem B2652335 : Blo 1768085 2652335 := bstep (se 1 (by rfl) ⟨1989251, by rfl⟩ : syracuseStep 2652335 = 3978503) B3978503
theorem B21526823 : Blo 1768085 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B10074415 : Blo 1768085 10074415 := bstep (se 1 (by rfl) ⟨7555811, by rfl⟩ : syracuseStep 10074415 = 15111623) B15111623
theorem B5667155 : Blo 1768085 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B4479371 : Blo 1768085 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B2652575 : Blo 1768085 2652575 := bstep (se 1 (by rfl) ⟨1989431, by rfl⟩ : syracuseStep 2652575 = 3978863) B3978863
theorem B16144829 : Blo 1768085 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B5970401 : Blo 1768085 5970401 := bstep (se 2 (by rfl) ⟨2238900, by rfl⟩ : syracuseStep 5970401 = 4477801) B4477801
theorem B2652665 : Blo 1768085 2652665 := bstep (se 2 (by rfl) ⟨994749, by rfl⟩ : syracuseStep 2652665 = 1989499) B1989499
theorem B4479583 : Blo 1768085 4479583 := bstep (se 1 (by rfl) ⟨3359687, by rfl⟩ : syracuseStep 4479583 = 6719375) B6719375
theorem B20151017 : Blo 1768085 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B1768415 : Blo 1768085 1768415 := bstep (se 1 (by rfl) ⟨1326311, by rfl⟩ : syracuseStep 1768415 = 2652623) B2652623
theorem B2653151 : Blo 1768085 2653151 := bstep (se 1 (by rfl) ⟨1989863, by rfl⟩ : syracuseStep 2653151 = 3979727) B3979727
theorem B1768475 : Blo 1768085 1768475 := bstep (se 1 (by rfl) ⟨1326356, by rfl⟩ : syracuseStep 1768475 = 2652713) B2652713
theorem B2653211 : Blo 1768085 2653211 := bstep (se 1 (by rfl) ⟨1989908, by rfl⟩ : syracuseStep 2653211 = 3979817) B3979817
theorem B2833481 : Blo 1768085 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1768603 : Blo 1768085 1768603 := bstep (se 1 (by rfl) ⟨1326452, by rfl⟩ : syracuseStep 1768603 = 2652905) B2652905
theorem B5381353 : Blo 1768085 5381353 := bstep (se 2 (by rfl) ⟨2018007, by rfl⟩ : syracuseStep 5381353 = 4036015) B4036015
theorem B4250875 : Blo 1768085 4250875 := bstep (se 1 (by rfl) ⟨3188156, by rfl⟩ : syracuseStep 4250875 = 6376313) B6376313
theorem B8953091 : Blo 1768085 8953091 := bstep (se 1 (by rfl) ⟨6714818, by rfl⟩ : syracuseStep 8953091 = 13429637) B13429637
theorem B1768859 : Blo 1768085 1768859 := bstep (se 1 (by rfl) ⟨1326644, by rfl⟩ : syracuseStep 1768859 = 2653289) B2653289
theorem B2653595 : Blo 1768085 2653595 := bstep (se 1 (by rfl) ⟨1990196, by rfl⟩ : syracuseStep 2653595 = 3980393) B3980393
theorem B2653673 : Blo 1768085 2653673 := bstep (se 2 (by rfl) ⟨995127, by rfl⟩ : syracuseStep 2653673 = 1990255) B1990255
theorem B1768943 : Blo 1768085 1768943 := bstep (se 1 (by rfl) ⟨1326707, by rfl⟩ : syracuseStep 1768943 = 2653415) B2653415
theorem B2653679 : Blo 1768085 2653679 := bstep (se 1 (by rfl) ⟨1990259, by rfl⟩ : syracuseStep 2653679 = 3980519) B3980519
theorem B2653817 : Blo 1768085 2653817 := bstep (se 2 (by rfl) ⟨995181, by rfl⟩ : syracuseStep 2653817 = 1990363) B1990363
theorem B51699433 : Blo 1768085 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B1769279 : Blo 1768085 1769279 := bstep (se 1 (by rfl) ⟨1326959, by rfl⟩ : syracuseStep 1769279 = 2653919) B2653919
theorem B2654015 : Blo 1768085 2654015 := bstep (se 1 (by rfl) ⟨1990511, by rfl⟩ : syracuseStep 2654015 = 3981023) B3981023
theorem B1769307 : Blo 1768085 1769307 := bstep (se 1 (by rfl) ⟨1326980, by rfl⟩ : syracuseStep 1769307 = 2653961) B2653961
theorem B2654063 : Blo 1768085 2654063 := bstep (se 1 (by rfl) ⟨1990547, by rfl⟩ : syracuseStep 2654063 = 3981095) B3981095
theorem B8953739 : Blo 1768085 8953739 := bstep (se 1 (by rfl) ⟨6715304, by rfl⟩ : syracuseStep 8953739 = 13430609) B13430609
theorem B3981275 : Blo 1768085 3981275 := bstep (se 1 (by rfl) ⟨2985956, by rfl⟩ : syracuseStep 3981275 = 5971913) B5971913
theorem B2654303 : Blo 1768085 2654303 := bstep (se 1 (by rfl) ⟨1990727, by rfl⟩ : syracuseStep 2654303 = 3981455) B3981455
theorem B2654345 : Blo 1768085 2654345 := bstep (se 2 (by rfl) ⟨995379, by rfl⟩ : syracuseStep 2654345 = 1990759) B1990759
theorem B2654363 : Blo 1768085 2654363 := bstep (se 1 (by rfl) ⟨1990772, by rfl⟩ : syracuseStep 2654363 = 3981545) B3981545
theorem B49725613 : Blo 1768085 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B8954063 : Blo 1768085 8954063 := bstep (se 1 (by rfl) ⟨6715547, by rfl⟩ : syracuseStep 8954063 = 13431095) B13431095
theorem B3981671 : Blo 1768085 3981671 := bstep (se 1 (by rfl) ⟨2986253, by rfl⟩ : syracuseStep 3981671 = 5972507) B5972507
theorem B1769831 : Blo 1768085 1769831 := bstep (se 1 (by rfl) ⟨1327373, by rfl⟩ : syracuseStep 1769831 = 2654747) B2654747
theorem B9568621 : Blo 1768085 9568621 := bstep (se 3 (by rfl) ⟨1794116, by rfl⟩ : syracuseStep 9568621 = 3588233) B3588233
theorem B27222409 : Blo 1768085 27222409 := bstep (se 2 (by rfl) ⟨10208403, by rfl⟩ : syracuseStep 27222409 = 20416807) B20416807
theorem B217924025 : Blo 1768085 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1769951 : Blo 1768085 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B4538855 : Blo 1768085 4538855 := bstep (se 1 (by rfl) ⟨3404141, by rfl⟩ : syracuseStep 4538855 = 6808283) B6808283
theorem B3359225 : Blo 1768085 3359225 := bstep (se 2 (by rfl) ⟨1259709, by rfl⟩ : syracuseStep 3359225 = 2519419) B2519419
theorem B1770031 : Blo 1768085 1770031 := bstep (se 1 (by rfl) ⟨1327523, by rfl⟩ : syracuseStep 1770031 = 2655047) B2655047
theorem B1770075 : Blo 1768085 1770075 := bstep (se 1 (by rfl) ⟨1327556, by rfl⟩ : syracuseStep 1770075 = 2655113) B2655113
theorem B5972777 : Blo 1768085 5972777 := bstep (se 2 (by rfl) ⟨2239791, by rfl⟩ : syracuseStep 5972777 = 4479583) B4479583
theorem B5038939 : Blo 1768085 5038939 := bstep (se 1 (by rfl) ⟨3779204, by rfl⟩ : syracuseStep 5038939 = 7558409) B7558409
theorem B12109085 : Blo 1768085 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B3778103 : Blo 1768085 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B2983871 : Blo 1768085 2983871 := bstep (se 1 (by rfl) ⟨2237903, by rfl⟩ : syracuseStep 2983871 = 4475807) B4475807
theorem B3828065 : Blo 1768085 3828065 := bstep (se 2 (by rfl) ⟨1435524, by rfl⟩ : syracuseStep 3828065 = 2871049) B2871049
theorem B14338529 : Blo 1768085 14338529 := bstep (se 2 (by rfl) ⟨5376948, by rfl⟩ : syracuseStep 14338529 = 10753897) B10753897
theorem B2984431 : Blo 1768085 2984431 := bstep (se 1 (by rfl) ⟨2238323, by rfl⟩ : syracuseStep 2984431 = 4476647) B4476647
theorem B2984539 : Blo 1768085 2984539 := bstep (se 1 (by rfl) ⟨2238404, by rfl⟩ : syracuseStep 2984539 = 4476809) B4476809
theorem B7555675 : Blo 1768085 7555675 := bstep (se 1 (by rfl) ⟨5666756, by rfl⟩ : syracuseStep 7555675 = 11333513) B11333513
theorem B3402479 : Blo 1768085 3402479 := bstep (se 1 (by rfl) ⟨2551859, by rfl⟩ : syracuseStep 3402479 = 5103719) B5103719
theorem B15108889 : Blo 1768085 15108889 := bstep (se 2 (by rfl) ⟨5665833, by rfl⟩ : syracuseStep 15108889 = 11331667) B11331667
theorem B6810409 : Blo 1768085 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B4475695 : Blo 1768085 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B7555949 : Blo 1768085 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B6548705 : Blo 1768085 6548705 := bstep (se 2 (by rfl) ⟨2455764, by rfl⟩ : syracuseStep 6548705 = 4911529) B4911529
theorem B24210667 : Blo 1768085 24210667 := bstep (se 1 (by rfl) ⟨18158000, by rfl⟩ : syracuseStep 24210667 = 36316001) B36316001
theorem B36293915 : Blo 1768085 36293915 := bstep (se 1 (by rfl) ⟨27220436, by rfl⟩ : syracuseStep 36293915 = 54440873) B54440873
theorem B2518399 : Blo 1768085 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B2911721 : Blo 1768085 2911721 := bstep (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) B2183791
theorem B4476667 : Blo 1768085 4476667 := bstep (se 1 (by rfl) ⟨3357500, by rfl⟩ : syracuseStep 4476667 = 6715001) B6715001
theorem B6713225 : Blo 1768085 6713225 := bstep (se 2 (by rfl) ⟨2517459, by rfl⟩ : syracuseStep 6713225 = 5034919) B5034919
theorem B9080747 : Blo 1768085 9080747 := bstep (se 1 (by rfl) ⟨6810560, by rfl⟩ : syracuseStep 9080747 = 13621121) B13621121
theorem B2986031 : Blo 1768085 2986031 := bstep (se 1 (by rfl) ⟨2239523, by rfl⟩ : syracuseStep 2986031 = 4479047) B4479047
theorem B4476991 : Blo 1768085 4476991 := bstep (se 1 (by rfl) ⟨3357743, by rfl⟩ : syracuseStep 4476991 = 6715487) B6715487
theorem B22671535 : Blo 1768085 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B2986247 : Blo 1768085 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B2986537 : Blo 1768085 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B2986807 : Blo 1768085 2986807 := bstep (se 1 (by rfl) ⟨2240105, by rfl⟩ : syracuseStep 2986807 = 4480211) B4480211
theorem B5968727 : Blo 1768085 5968727 := bstep (se 1 (by rfl) ⟨4476545, by rfl⟩ : syracuseStep 5968727 = 8953091) B8953091
theorem B68932577 : Blo 1768085 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B5668859 : Blo 1768085 5668859 := bstep (se 1 (by rfl) ⟨4251644, by rfl⟩ : syracuseStep 5668859 = 8503289) B8503289
theorem B5969159 : Blo 1768085 5969159 := bstep (se 1 (by rfl) ⟨4476869, by rfl⟩ : syracuseStep 5969159 = 8953739) B8953739
theorem B6714697 : Blo 1768085 6714697 := bstep (se 2 (by rfl) ⟨2518011, by rfl⟩ : syracuseStep 6714697 = 5036023) B5036023
theorem B27243965 : Blo 1768085 27243965 := bstep (se 3 (by rfl) ⟨5108243, by rfl⟩ : syracuseStep 27243965 = 10216487) B10216487
theorem B13432553 : Blo 1768085 13432553 := bstep (se 2 (by rfl) ⟨5037207, by rfl⟩ : syracuseStep 13432553 = 10074415) B10074415
theorem B20428627 : Blo 1768085 20428627 := bstep (se 1 (by rfl) ⟨15321470, by rfl⟩ : syracuseStep 20428627 = 30642941) B30642941
theorem B5969807 : Blo 1768085 5969807 := bstep (se 1 (by rfl) ⟨4477355, by rfl⟩ : syracuseStep 5969807 = 8954711) B8954711
theorem B15120371 : Blo 1768085 15120371 := bstep (se 1 (by rfl) ⟨11340278, by rfl⟩ : syracuseStep 15120371 = 22680557) B22680557
theorem B3979367 : Blo 1768085 3979367 := bstep (se 1 (by rfl) ⟨2984525, by rfl⟩ : syracuseStep 3979367 = 5969051) B5969051
theorem B13810085 : Blo 1768085 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B2652647 : Blo 1768085 2652647 := bstep (se 1 (by rfl) ⟨1989485, by rfl⟩ : syracuseStep 2652647 = 3978971) B3978971
theorem B1768103 : Blo 1768085 1768103 := bstep (se 1 (by rfl) ⟨1326077, by rfl⟩ : syracuseStep 1768103 = 2652155) B2652155
theorem B1768143 : Blo 1768085 1768143 := bstep (se 1 (by rfl) ⟨1326107, by rfl⟩ : syracuseStep 1768143 = 2652215) B2652215
theorem B1768187 : Blo 1768085 1768187 := bstep (se 1 (by rfl) ⟨1326140, by rfl⟩ : syracuseStep 1768187 = 2652281) B2652281
theorem B1768223 : Blo 1768085 1768223 := bstep (se 1 (by rfl) ⟨1326167, by rfl⟩ : syracuseStep 1768223 = 2652335) B2652335
theorem B14351215 : Blo 1768085 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B1768383 : Blo 1768085 1768383 := bstep (se 1 (by rfl) ⟨1326287, by rfl⟩ : syracuseStep 1768383 = 2652575) B2652575
theorem B5970887 : Blo 1768085 5970887 := bstep (se 1 (by rfl) ⟨4478165, by rfl⟩ : syracuseStep 5970887 = 8956331) B8956331
theorem B10763219 : Blo 1768085 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B7175137 : Blo 1768085 7175137 := bstep (se 2 (by rfl) ⟨2690676, by rfl⟩ : syracuseStep 7175137 = 5381353) B5381353
theorem B3980267 : Blo 1768085 3980267 := bstep (se 1 (by rfl) ⟨2985200, by rfl⟩ : syracuseStep 3980267 = 5970401) B5970401
theorem B5667833 : Blo 1768085 5667833 := bstep (se 2 (by rfl) ⟨2125437, by rfl⟩ : syracuseStep 5667833 = 4250875) B4250875
theorem B1768443 : Blo 1768085 1768443 := bstep (se 1 (by rfl) ⟨1326332, by rfl⟩ : syracuseStep 1768443 = 2652665) B2652665
theorem B1989787 : Blo 1768085 1989787 := bstep (se 1 (by rfl) ⟨1492340, by rfl⟩ : syracuseStep 1989787 = 2984681) B2984681
theorem B13434011 : Blo 1768085 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B1989823 : Blo 1768085 1989823 := bstep (se 1 (by rfl) ⟨1492367, by rfl⟩ : syracuseStep 1989823 = 2984735) B2984735
theorem B1768767 : Blo 1768085 1768767 := bstep (se 1 (by rfl) ⟨1326575, by rfl⟩ : syracuseStep 1768767 = 2653151) B2653151
theorem B1768807 : Blo 1768085 1768807 := bstep (se 1 (by rfl) ⟨1326605, by rfl⟩ : syracuseStep 1768807 = 2653211) B2653211
theorem B1769063 : Blo 1768085 1769063 := bstep (se 1 (by rfl) ⟨1326797, by rfl⟩ : syracuseStep 1769063 = 2653595) B2653595
theorem B1769115 : Blo 1768085 1769115 := bstep (se 1 (by rfl) ⟨1326836, by rfl⟩ : syracuseStep 1769115 = 2653673) B2653673
theorem B1769119 : Blo 1768085 1769119 := bstep (se 1 (by rfl) ⟨1326839, by rfl⟩ : syracuseStep 1769119 = 2653679) B2653679
theorem B1769211 : Blo 1768085 1769211 := bstep (se 1 (by rfl) ⟨1326908, by rfl⟩ : syracuseStep 1769211 = 2653817) B2653817
theorem B5971751 : Blo 1768085 5971751 := bstep (se 1 (by rfl) ⟨4478813, by rfl⟩ : syracuseStep 5971751 = 8957627) B8957627
theorem B1769343 : Blo 1768085 1769343 := bstep (se 1 (by rfl) ⟨1327007, by rfl⟩ : syracuseStep 1769343 = 2654015) B2654015
theorem B1769375 : Blo 1768085 1769375 := bstep (se 1 (by rfl) ⟨1327031, by rfl⟩ : syracuseStep 1769375 = 2654063) B2654063
theorem B2654183 : Blo 1768085 2654183 := bstep (se 1 (by rfl) ⟨1990637, by rfl⟩ : syracuseStep 2654183 = 3981275) B3981275
theorem B1990687 : Blo 1768085 1990687 := bstep (se 1 (by rfl) ⟨1493015, by rfl⟩ : syracuseStep 1990687 = 2986031) B2986031
theorem B1769535 : Blo 1768085 1769535 := bstep (se 1 (by rfl) ⟨1327151, by rfl⟩ : syracuseStep 1769535 = 2654303) B2654303
theorem B1769563 : Blo 1768085 1769563 := bstep (se 1 (by rfl) ⟨1327172, by rfl⟩ : syracuseStep 1769563 = 2654345) B2654345
theorem B1769575 : Blo 1768085 1769575 := bstep (se 1 (by rfl) ⟨1327181, by rfl⟩ : syracuseStep 1769575 = 2654363) B2654363
theorem B1990831 : Blo 1768085 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B30228713 : Blo 1768085 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B2654447 : Blo 1768085 2654447 := bstep (se 1 (by rfl) ⟨1990835, by rfl⟩ : syracuseStep 2654447 = 3981671) B3981671
theorem B3981851 : Blo 1768085 3981851 := bstep (se 1 (by rfl) ⟨2986388, by rfl⟩ : syracuseStep 3981851 = 5972777) B5972777
theorem B3982049 : Blo 1768085 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B18162643 : Blo 1768085 18162643 := bstep (se 1 (by rfl) ⟨13621982, by rfl⟩ : syracuseStep 18162643 = 27243965) B27243965
theorem B20145185 : Blo 1768085 20145185 := bstep (se 2 (by rfl) ⟨7554444, by rfl⟩ : syracuseStep 20145185 = 15108889) B15108889
theorem B3982409 : Blo 1768085 3982409 := bstep (se 2 (by rfl) ⟨1493403, by rfl⟩ : syracuseStep 3982409 = 2986807) B2986807
theorem B6718585 : Blo 1768085 6718585 := bstep (se 2 (by rfl) ⟨2519469, by rfl⟩ : syracuseStep 6718585 = 5038939) B5038939
theorem B8955035 : Blo 1768085 8955035 := bstep (se 1 (by rfl) ⟨6716276, by rfl⟩ : syracuseStep 8955035 = 13432553) B13432553
theorem B129123557 : Blo 1768085 129123557 := bstep (se 4 (by rfl) ⟨12105333, by rfl⟩ : syracuseStep 129123557 = 24210667) B24210667
theorem B8956007 : Blo 1768085 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B4475483 : Blo 1768085 4475483 := bstep (se 1 (by rfl) ⟨3356612, by rfl⟩ : syracuseStep 4475483 = 6713225) B6713225
theorem B3779239 : Blo 1768085 3779239 := bstep (se 1 (by rfl) ⟨2834429, by rfl⟩ : syracuseStep 3779239 = 5668859) B5668859
theorem B66300817 : Blo 1768085 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B3025903 : Blo 1768085 3025903 := bstep (se 1 (by rfl) ⟨2269427, by rfl⟩ : syracuseStep 3025903 = 4538855) B4538855
theorem B2239483 : Blo 1768085 2239483 := bstep (se 1 (by rfl) ⟨1679612, by rfl⟩ : syracuseStep 2239483 = 3359225) B3359225
theorem B12758161 : Blo 1768085 12758161 := bstep (se 2 (by rfl) ⟨4784310, by rfl⟩ : syracuseStep 12758161 = 9568621) B9568621
theorem B8072723 : Blo 1768085 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B40832693 : Blo 1768085 40832693 := bstep (se 5 (by rfl) ⟨1914032, by rfl⟩ : syracuseStep 40832693 = 3828065) B3828065
theorem B9080545 : Blo 1768085 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B5967593 : Blo 1768085 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B10080247 : Blo 1768085 10080247 := bstep (se 1 (by rfl) ⟨7560185, by rfl⟩ : syracuseStep 10080247 = 15120371) B15120371
theorem B24195943 : Blo 1768085 24195943 := bstep (se 1 (by rfl) ⟨18146957, by rfl⟩ : syracuseStep 24195943 = 36293915) B36293915
theorem B5968889 : Blo 1768085 5968889 := bstep (se 2 (by rfl) ⟨2238333, by rfl⟩ : syracuseStep 5968889 = 4476667) B4476667
theorem B5969321 : Blo 1768085 5969321 := bstep (se 2 (by rfl) ⟨2238495, by rfl⟩ : syracuseStep 5969321 = 4476991) B4476991
theorem B5969375 : Blo 1768085 5969375 := bstep (se 1 (by rfl) ⟨4477031, by rfl⟩ : syracuseStep 5969375 = 8954063) B8954063
theorem B36296545 : Blo 1768085 36296545 := bstep (se 2 (by rfl) ⟨13611204, by rfl⟩ : syracuseStep 36296545 = 27222409) B27222409
theorem B3979151 : Blo 1768085 3979151 := bstep (se 1 (by rfl) ⟨2984363, by rfl⟩ : syracuseStep 3979151 = 5968727) B5968727
theorem B3979241 : Blo 1768085 3979241 := bstep (se 2 (by rfl) ⟨1492215, by rfl⟩ : syracuseStep 3979241 = 2984431) B2984431
theorem B3979385 : Blo 1768085 3979385 := bstep (se 2 (by rfl) ⟨1492269, by rfl⟩ : syracuseStep 3979385 = 2984539) B2984539
theorem B10074233 : Blo 1768085 10074233 := bstep (se 2 (by rfl) ⟨3777837, by rfl⟩ : syracuseStep 10074233 = 7555675) B7555675
theorem B3979439 : Blo 1768085 3979439 := bstep (se 1 (by rfl) ⟨2984579, by rfl⟩ : syracuseStep 3979439 = 5969159) B5969159
theorem B19134953 : Blo 1768085 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B581130733 : Blo 1768085 581130733 := bstep (se 3 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 581130733 = 217924025) B217924025
theorem B3979871 : Blo 1768085 3979871 := bstep (se 1 (by rfl) ⟨2984903, by rfl⟩ : syracuseStep 3979871 = 5969807) B5969807
theorem B7764589 : Blo 1768085 7764589 := bstep (se 3 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 7764589 = 2911721) B2911721
theorem B1989247 : Blo 1768085 1989247 := bstep (se 1 (by rfl) ⟨1491935, by rfl⟩ : syracuseStep 1989247 = 2983871) B2983871
theorem B9566849 : Blo 1768085 9566849 := bstep (se 2 (by rfl) ⟨3587568, by rfl⟩ : syracuseStep 9566849 = 7175137) B7175137
theorem B2652911 : Blo 1768085 2652911 := bstep (se 1 (by rfl) ⟨1989683, by rfl⟩ : syracuseStep 2652911 = 3979367) B3979367
theorem B10074941 : Blo 1768085 10074941 := bstep (se 3 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 10074941 = 3778103) B3778103
theorem B2653049 : Blo 1768085 2653049 := bstep (se 2 (by rfl) ⟨994893, by rfl⟩ : syracuseStep 2653049 = 1989787) B1989787
theorem B2653097 : Blo 1768085 2653097 := bstep (se 2 (by rfl) ⟨994911, by rfl⟩ : syracuseStep 2653097 = 1989823) B1989823
theorem B9206723 : Blo 1768085 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B9559019 : Blo 1768085 9559019 := bstep (se 1 (by rfl) ⟨7169264, by rfl⟩ : syracuseStep 9559019 = 14338529) B14338529
theorem B1768431 : Blo 1768085 1768431 := bstep (se 1 (by rfl) ⟨1326323, by rfl⟩ : syracuseStep 1768431 = 2652647) B2652647
theorem B8952929 : Blo 1768085 8952929 := bstep (se 2 (by rfl) ⟨3357348, by rfl⟩ : syracuseStep 8952929 = 6714697) B6714697
theorem B2268319 : Blo 1768085 2268319 := bstep (se 1 (by rfl) ⟨1701239, by rfl⟩ : syracuseStep 2268319 = 3402479) B3402479
theorem B3357865 : Blo 1768085 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B5037299 : Blo 1768085 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B3980591 : Blo 1768085 3980591 := bstep (se 1 (by rfl) ⟨2985443, by rfl⟩ : syracuseStep 3980591 = 5970887) B5970887
theorem B7175479 : Blo 1768085 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B2653511 : Blo 1768085 2653511 := bstep (se 1 (by rfl) ⟨1990133, by rfl⟩ : syracuseStep 2653511 = 3980267) B3980267
theorem B4365803 : Blo 1768085 4365803 := bstep (se 1 (by rfl) ⟨3274352, by rfl⟩ : syracuseStep 4365803 = 6548705) B6548705
theorem B27238169 : Blo 1768085 27238169 := bstep (se 2 (by rfl) ⟨10214313, by rfl⟩ : syracuseStep 27238169 = 20428627) B20428627
theorem B3981167 : Blo 1768085 3981167 := bstep (se 1 (by rfl) ⟨2985875, by rfl⟩ : syracuseStep 3981167 = 5971751) B5971751
theorem B183820205 : Blo 1768085 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B6053831 : Blo 1768085 6053831 := bstep (se 1 (by rfl) ⟨4540373, by rfl⟩ : syracuseStep 6053831 = 9080747) B9080747
theorem B15114221 : Blo 1768085 15114221 := bstep (se 3 (by rfl) ⟨2833916, by rfl⟩ : syracuseStep 15114221 = 5667833) B5667833
theorem B1769455 : Blo 1768085 1769455 := bstep (se 1 (by rfl) ⟨1327091, by rfl⟩ : syracuseStep 1769455 = 2654183) B2654183
theorem B2654249 : Blo 1768085 2654249 := bstep (se 2 (by rfl) ⟨995343, by rfl⟩ : syracuseStep 2654249 = 1990687) B1990687
theorem B20152475 : Blo 1768085 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B1769631 : Blo 1768085 1769631 := bstep (se 1 (by rfl) ⟨1327223, by rfl⟩ : syracuseStep 1769631 = 2654447) B2654447
theorem B2654441 : Blo 1768085 2654441 := bstep (se 2 (by rfl) ⟨995415, by rfl⟩ : syracuseStep 2654441 = 1990831) B1990831
theorem B2654567 : Blo 1768085 2654567 := bstep (se 1 (by rfl) ⟨1990925, by rfl⟩ : syracuseStep 2654567 = 3981851) B3981851
theorem B2654699 : Blo 1768085 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B774840977 : Blo 1768085 774840977 := bstep (se 2 (by rfl) ⟨290565366, by rfl⟩ : syracuseStep 774840977 = 581130733) B581130733
theorem B2654939 : Blo 1768085 2654939 := bstep (se 1 (by rfl) ⟨1991204, by rfl⟩ : syracuseStep 2654939 = 3982409) B3982409
theorem B86082371 : Blo 1768085 86082371 := bstep (se 1 (by rfl) ⟨64561778, by rfl⟩ : syracuseStep 86082371 = 129123557) B129123557
theorem B5038985 : Blo 1768085 5038985 := bstep (se 2 (by rfl) ⟨1889619, by rfl⟩ : syracuseStep 5038985 = 3779239) B3779239
theorem B32261257 : Blo 1768085 32261257 := bstep (se 2 (by rfl) ⟨12097971, by rfl⟩ : syracuseStep 32261257 = 24195943) B24195943
theorem B88401089 : Blo 1768085 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B24216857 : Blo 1768085 24216857 := bstep (se 2 (by rfl) ⟨9081321, by rfl⟩ : syracuseStep 24216857 = 18162643) B18162643
theorem B3024425 : Blo 1768085 3024425 := bstep (se 2 (by rfl) ⟨1134159, by rfl⟩ : syracuseStep 3024425 = 2268319) B2268319
theorem B12756635 : Blo 1768085 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B25511597 : Blo 1768085 25511597 := bstep (se 3 (by rfl) ⟨4783424, by rfl⟩ : syracuseStep 25511597 = 9566849) B9566849
theorem B2983655 : Blo 1768085 2983655 := bstep (se 1 (by rfl) ⟨2237741, by rfl⟩ : syracuseStep 2983655 = 4475483) B4475483
theorem B2910535 : Blo 1768085 2910535 := bstep (se 1 (by rfl) ⟨2182901, by rfl⟩ : syracuseStep 2910535 = 4365803) B4365803
theorem B122546803 : Blo 1768085 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B5381815 : Blo 1768085 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B13430123 : Blo 1768085 13430123 := bstep (se 1 (by rfl) ⟨10072592, by rfl⟩ : syracuseStep 13430123 = 20145185) B20145185
theorem B4034537 : Blo 1768085 4034537 := bstep (se 2 (by rfl) ⟨1512951, by rfl⟩ : syracuseStep 4034537 = 3025903) B3025903
theorem B2985977 : Blo 1768085 2985977 := bstep (se 2 (by rfl) ⟨1119741, by rfl⟩ : syracuseStep 2985977 = 2239483) B2239483
theorem B8958113 : Blo 1768085 8958113 := bstep (se 2 (by rfl) ⟨3359292, by rfl⟩ : syracuseStep 8958113 = 6718585) B6718585
theorem B17010881 : Blo 1768085 17010881 := bstep (se 2 (by rfl) ⟨6379080, by rfl⟩ : syracuseStep 17010881 = 12758161) B12758161
theorem B4477153 : Blo 1768085 4477153 := bstep (se 2 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 4477153 = 3357865) B3357865
theorem B5968619 : Blo 1768085 5968619 := bstep (se 1 (by rfl) ⟨4476464, by rfl⟩ : syracuseStep 5968619 = 8952929) B8952929
theorem B48395393 : Blo 1768085 48395393 := bstep (se 2 (by rfl) ⟨18148272, by rfl⟩ : syracuseStep 48395393 = 36296545) B36296545
theorem B3978395 : Blo 1768085 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B18158779 : Blo 1768085 18158779 := bstep (se 1 (by rfl) ⟨13619084, by rfl⟩ : syracuseStep 18158779 = 27238169) B27238169
theorem B4035887 : Blo 1768085 4035887 := bstep (se 1 (by rfl) ⟨3026915, by rfl⟩ : syracuseStep 4035887 = 6053831) B6053831
theorem B13440329 : Blo 1768085 13440329 := bstep (se 2 (by rfl) ⟨5040123, by rfl⟩ : syracuseStep 13440329 = 10080247) B10080247
theorem B3979259 : Blo 1768085 3979259 := bstep (se 1 (by rfl) ⟨2984444, by rfl⟩ : syracuseStep 3979259 = 5968889) B5968889
theorem B5970023 : Blo 1768085 5970023 := bstep (se 1 (by rfl) ⟨4477517, by rfl⟩ : syracuseStep 5970023 = 8955035) B8955035
theorem B10352785 : Blo 1768085 10352785 := bstep (se 2 (by rfl) ⟨3882294, by rfl⟩ : syracuseStep 10352785 = 7764589) B7764589
theorem B2652329 : Blo 1768085 2652329 := bstep (se 2 (by rfl) ⟨994623, by rfl⟩ : syracuseStep 2652329 = 1989247) B1989247
theorem B3979547 : Blo 1768085 3979547 := bstep (se 1 (by rfl) ⟨2984660, by rfl⟩ : syracuseStep 3979547 = 5969321) B5969321
theorem B3979583 : Blo 1768085 3979583 := bstep (se 1 (by rfl) ⟨2984687, by rfl⟩ : syracuseStep 3979583 = 5969375) B5969375
theorem B2652767 : Blo 1768085 2652767 := bstep (se 1 (by rfl) ⟨1989575, by rfl⟩ : syracuseStep 2652767 = 3979151) B3979151
theorem B2652827 : Blo 1768085 2652827 := bstep (se 1 (by rfl) ⟨1989620, by rfl⟩ : syracuseStep 2652827 = 3979241) B3979241
theorem B5970671 : Blo 1768085 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B6716155 : Blo 1768085 6716155 := bstep (se 1 (by rfl) ⟨5037116, by rfl⟩ : syracuseStep 6716155 = 10074233) B10074233
theorem B2652923 : Blo 1768085 2652923 := bstep (se 1 (by rfl) ⟨1989692, by rfl⟩ : syracuseStep 2652923 = 3979385) B3979385
theorem B2652959 : Blo 1768085 2652959 := bstep (se 1 (by rfl) ⟨1989719, by rfl⟩ : syracuseStep 2652959 = 3979439) B3979439
theorem B2653247 : Blo 1768085 2653247 := bstep (se 1 (by rfl) ⟨1989935, by rfl⟩ : syracuseStep 2653247 = 3979871) B3979871
theorem B9567305 : Blo 1768085 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B1768607 : Blo 1768085 1768607 := bstep (se 1 (by rfl) ⟨1326455, by rfl⟩ : syracuseStep 1768607 = 2652911) B2652911
theorem B6716627 : Blo 1768085 6716627 := bstep (se 1 (by rfl) ⟨5037470, by rfl⟩ : syracuseStep 6716627 = 10074941) B10074941
theorem B1768699 : Blo 1768085 1768699 := bstep (se 1 (by rfl) ⟨1326524, by rfl⟩ : syracuseStep 1768699 = 2653049) B2653049
theorem B1768731 : Blo 1768085 1768731 := bstep (se 1 (by rfl) ⟨1326548, by rfl⟩ : syracuseStep 1768731 = 2653097) B2653097
theorem B6372679 : Blo 1768085 6372679 := bstep (se 1 (by rfl) ⟨4779509, by rfl⟩ : syracuseStep 6372679 = 9559019) B9559019
theorem B3358199 : Blo 1768085 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B2653727 : Blo 1768085 2653727 := bstep (se 1 (by rfl) ⟨1990295, by rfl⟩ : syracuseStep 2653727 = 3980591) B3980591
theorem B1769007 : Blo 1768085 1769007 := bstep (se 1 (by rfl) ⟨1326755, by rfl⟩ : syracuseStep 1769007 = 2653511) B2653511
theorem B12107393 : Blo 1768085 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B27221795 : Blo 1768085 27221795 := bstep (se 1 (by rfl) ⟨20416346, by rfl⟩ : syracuseStep 27221795 = 40832693) B40832693
theorem B24551261 : Blo 1768085 24551261 := bstep (se 3 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 24551261 = 9206723) B9206723
theorem B2654111 : Blo 1768085 2654111 := bstep (se 1 (by rfl) ⟨1990583, by rfl⟩ : syracuseStep 2654111 = 3981167) B3981167
theorem B10076147 : Blo 1768085 10076147 := bstep (se 1 (by rfl) ⟨7557110, by rfl⟩ : syracuseStep 10076147 = 15114221) B15114221
theorem B1769499 : Blo 1768085 1769499 := bstep (se 1 (by rfl) ⟨1327124, by rfl⟩ : syracuseStep 1769499 = 2654249) B2654249
theorem B13434983 : Blo 1768085 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B5972075 : Blo 1768085 5972075 := bstep (se 1 (by rfl) ⟨4479056, by rfl⟩ : syracuseStep 5972075 = 8958113) B8958113
theorem B1769627 : Blo 1768085 1769627 := bstep (se 1 (by rfl) ⟨1327220, by rfl⟩ : syracuseStep 1769627 = 2654441) B2654441
theorem B13803713 : Blo 1768085 13803713 := bstep (se 2 (by rfl) ⟨5176392, by rfl⟩ : syracuseStep 13803713 = 10352785) B10352785
theorem B1769711 : Blo 1768085 1769711 := bstep (se 1 (by rfl) ⟨1327283, by rfl⟩ : syracuseStep 1769711 = 2654567) B2654567
theorem B1769799 : Blo 1768085 1769799 := bstep (se 1 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 1769799 = 2654699) B2654699
theorem B1769959 : Blo 1768085 1769959 := bstep (se 1 (by rfl) ⟨1327469, by rfl⟩ : syracuseStep 1769959 = 2654939) B2654939
theorem B3359323 : Blo 1768085 3359323 := bstep (se 1 (by rfl) ⟨2519492, by rfl⟩ : syracuseStep 3359323 = 5038985) B5038985
theorem B8954873 : Blo 1768085 8954873 := bstep (se 2 (by rfl) ⟨3358077, by rfl⟩ : syracuseStep 8954873 = 6716155) B6716155
theorem B8504423 : Blo 1768085 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B17007731 : Blo 1768085 17007731 := bstep (se 1 (by rfl) ⟨12755798, by rfl⟩ : syracuseStep 17007731 = 25511597) B25511597
theorem B8955197 : Blo 1768085 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B8496905 : Blo 1768085 8496905 := bstep (se 2 (by rfl) ⟨3186339, by rfl⟩ : syracuseStep 8496905 = 6372679) B6372679
theorem B8071595 : Blo 1768085 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B18147863 : Blo 1768085 18147863 := bstep (se 1 (by rfl) ⟨13610897, by rfl⟩ : syracuseStep 18147863 = 27221795) B27221795
theorem B2689691 : Blo 1768085 2689691 := bstep (se 1 (by rfl) ⟨2017268, by rfl⟩ : syracuseStep 2689691 = 4034537) B4034537
theorem B11340587 : Blo 1768085 11340587 := bstep (se 1 (by rfl) ⟨8505440, by rfl⟩ : syracuseStep 11340587 = 17010881) B17010881
theorem B16367507 : Blo 1768085 16367507 := bstep (se 1 (by rfl) ⟨12275630, by rfl⟩ : syracuseStep 16367507 = 24551261) B24551261
theorem B235736237 : Blo 1768085 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B57388247 : Blo 1768085 57388247 := bstep (se 1 (by rfl) ⟨43041185, by rfl⟩ : syracuseStep 57388247 = 86082371) B86082371
theorem B32263595 : Blo 1768085 32263595 := bstep (se 1 (by rfl) ⟨24197696, by rfl⟩ : syracuseStep 32263595 = 48395393) B48395393
theorem B2690591 : Blo 1768085 2690591 := bstep (se 1 (by rfl) ⟨2017943, by rfl⟩ : syracuseStep 2690591 = 4035887) B4035887
theorem B8065133 : Blo 1768085 8065133 := bstep (se 3 (by rfl) ⟨1512212, by rfl⟩ : syracuseStep 8065133 = 3024425) B3024425
theorem B24211705 : Blo 1768085 24211705 := bstep (se 2 (by rfl) ⟨9079389, by rfl⟩ : syracuseStep 24211705 = 18158779) B18158779
theorem B6378203 : Blo 1768085 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B1990651 : Blo 1768085 1990651 := bstep (se 1 (by rfl) ⟨1492988, by rfl⟩ : syracuseStep 1990651 = 2985977) B2985977
theorem B4477751 : Blo 1768085 4477751 := bstep (se 1 (by rfl) ⟨3358313, by rfl⟩ : syracuseStep 4477751 = 6716627) B6716627
theorem B5969537 : Blo 1768085 5969537 := bstep (se 2 (by rfl) ⟨2238576, by rfl⟩ : syracuseStep 5969537 = 4477153) B4477153
theorem B516560651 : Blo 1768085 516560651 := bstep (se 1 (by rfl) ⟨387420488, by rfl⟩ : syracuseStep 516560651 = 774840977) B774840977
theorem B3979079 : Blo 1768085 3979079 := bstep (se 1 (by rfl) ⟨2984309, by rfl⟩ : syracuseStep 3979079 = 5968619) B5968619
theorem B2652263 : Blo 1768085 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B163395737 : Blo 1768085 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B16144571 : Blo 1768085 16144571 := bstep (se 1 (by rfl) ⟨12108428, by rfl⟩ : syracuseStep 16144571 = 24216857) B24216857
theorem B8960219 : Blo 1768085 8960219 := bstep (se 1 (by rfl) ⟨6720164, by rfl⟩ : syracuseStep 8960219 = 13440329) B13440329
theorem B1989103 : Blo 1768085 1989103 := bstep (se 1 (by rfl) ⟨1491827, by rfl⟩ : syracuseStep 1989103 = 2983655) B2983655
theorem B2652839 : Blo 1768085 2652839 := bstep (se 1 (by rfl) ⟨1989629, by rfl⟩ : syracuseStep 2652839 = 3979259) B3979259
theorem B3980015 : Blo 1768085 3980015 := bstep (se 1 (by rfl) ⟨2985011, by rfl⟩ : syracuseStep 3980015 = 5970023) B5970023
theorem B1768219 : Blo 1768085 1768219 := bstep (se 1 (by rfl) ⟨1326164, by rfl⟩ : syracuseStep 1768219 = 2652329) B2652329
theorem B43015009 : Blo 1768085 43015009 := bstep (se 2 (by rfl) ⟨16130628, by rfl⟩ : syracuseStep 43015009 = 32261257) B32261257
theorem B2653031 : Blo 1768085 2653031 := bstep (se 1 (by rfl) ⟨1989773, by rfl⟩ : syracuseStep 2653031 = 3979547) B3979547
theorem B2653055 : Blo 1768085 2653055 := bstep (se 1 (by rfl) ⟨1989791, by rfl⟩ : syracuseStep 2653055 = 3979583) B3979583
theorem B15522853 : Blo 1768085 15522853 := bstep (se 4 (by rfl) ⟨1455267, by rfl⟩ : syracuseStep 15522853 = 2910535) B2910535
theorem B1768511 : Blo 1768085 1768511 := bstep (se 1 (by rfl) ⟨1326383, by rfl⟩ : syracuseStep 1768511 = 2652767) B2652767
theorem B1768551 : Blo 1768085 1768551 := bstep (se 1 (by rfl) ⟨1326413, by rfl⟩ : syracuseStep 1768551 = 2652827) B2652827
theorem B3980447 : Blo 1768085 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B1768615 : Blo 1768085 1768615 := bstep (se 1 (by rfl) ⟨1326461, by rfl⟩ : syracuseStep 1768615 = 2652923) B2652923
theorem B1768639 : Blo 1768085 1768639 := bstep (se 1 (by rfl) ⟨1326479, by rfl⟩ : syracuseStep 1768639 = 2652959) B2652959
theorem B1768831 : Blo 1768085 1768831 := bstep (se 1 (by rfl) ⟨1326623, by rfl⟩ : syracuseStep 1768831 = 2653247) B2653247
theorem B8953415 : Blo 1768085 8953415 := bstep (se 1 (by rfl) ⟨6715061, by rfl⟩ : syracuseStep 8953415 = 13430123) B13430123
theorem B7175753 : Blo 1768085 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B1769151 : Blo 1768085 1769151 := bstep (se 1 (by rfl) ⟨1326863, by rfl⟩ : syracuseStep 1769151 = 2653727) B2653727
theorem B1769407 : Blo 1768085 1769407 := bstep (se 1 (by rfl) ⟨1327055, by rfl⟩ : syracuseStep 1769407 = 2654111) B2654111
theorem B6717431 : Blo 1768085 6717431 := bstep (se 1 (by rfl) ⟨5038073, by rfl⟩ : syracuseStep 6717431 = 10076147) B10076147
theorem B3981383 : Blo 1768085 3981383 := bstep (se 1 (by rfl) ⟨2986037, by rfl⟩ : syracuseStep 3981383 = 5972075) B5972075
theorem B5669615 : Blo 1768085 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B11338487 : Blo 1768085 11338487 := bstep (se 1 (by rfl) ⟨8503865, by rfl⟩ : syracuseStep 11338487 = 17007731) B17007731
theorem B57353345 : Blo 1768085 57353345 := bstep (se 2 (by rfl) ⟨21507504, by rfl⟩ : syracuseStep 57353345 = 43015009) B43015009
theorem B108930491 : Blo 1768085 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B5973479 : Blo 1768085 5973479 := bstep (se 1 (by rfl) ⟨4480109, by rfl⟩ : syracuseStep 5973479 = 8960219) B8960219
theorem B28690037 : Blo 1768085 28690037 := bstep (se 5 (by rfl) ⟨1344845, by rfl⟩ : syracuseStep 28690037 = 2689691) B2689691
theorem B17008541 : Blo 1768085 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B157157491 : Blo 1768085 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B38258831 : Blo 1768085 38258831 := bstep (se 1 (by rfl) ⟨28694123, by rfl⟩ : syracuseStep 38258831 = 57388247) B57388247
theorem B8956655 : Blo 1768085 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B5376755 : Blo 1768085 5376755 := bstep (se 1 (by rfl) ⟨4032566, by rfl⟩ : syracuseStep 5376755 = 8065133) B8065133
theorem B9202475 : Blo 1768085 9202475 := bstep (se 1 (by rfl) ⟨6901856, by rfl⟩ : syracuseStep 9202475 = 13803713) B13803713
theorem B2985167 : Blo 1768085 2985167 := bstep (se 1 (by rfl) ⟨2238875, by rfl⟩ : syracuseStep 2985167 = 4477751) B4477751
theorem B20697137 : Blo 1768085 20697137 := bstep (se 2 (by rfl) ⟨7761426, by rfl⟩ : syracuseStep 20697137 = 15522853) B15522853
theorem B21509063 : Blo 1768085 21509063 := bstep (se 1 (by rfl) ⟨16131797, by rfl⟩ : syracuseStep 21509063 = 32263595) B32263595
theorem B5968943 : Blo 1768085 5968943 := bstep (se 1 (by rfl) ⟨4476707, by rfl⟩ : syracuseStep 5968943 = 8953415) B8953415
theorem B4478287 : Blo 1768085 4478287 := bstep (se 1 (by rfl) ⟨3358715, by rfl⟩ : syracuseStep 4478287 = 6717431) B6717431
theorem B32282273 : Blo 1768085 32282273 := bstep (se 2 (by rfl) ⟨12105852, by rfl⟩ : syracuseStep 32282273 = 24211705) B24211705
theorem B2652137 : Blo 1768085 2652137 := bstep (se 2 (by rfl) ⟨994551, by rfl⟩ : syracuseStep 2652137 = 1989103) B1989103
theorem B5969915 : Blo 1768085 5969915 := bstep (se 1 (by rfl) ⟨4477436, by rfl⟩ : syracuseStep 5969915 = 8954873) B8954873
theorem B4479097 : Blo 1768085 4479097 := bstep (se 2 (by rfl) ⟨1679661, by rfl⟩ : syracuseStep 4479097 = 3359323) B3359323
theorem B5970131 : Blo 1768085 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B3979691 : Blo 1768085 3979691 := bstep (se 1 (by rfl) ⟨2984768, by rfl⟩ : syracuseStep 3979691 = 5969537) B5969537
theorem B344373767 : Blo 1768085 344373767 := bstep (se 1 (by rfl) ⟨258280325, by rfl⟩ : syracuseStep 344373767 = 516560651) B516560651
theorem B2652719 : Blo 1768085 2652719 := bstep (se 1 (by rfl) ⟨1989539, by rfl⟩ : syracuseStep 2652719 = 3979079) B3979079
theorem B1768175 : Blo 1768085 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B7174909 : Blo 1768085 7174909 := bstep (se 3 (by rfl) ⟨1345295, by rfl⟩ : syracuseStep 7174909 = 2690591) B2690591
theorem B10763047 : Blo 1768085 10763047 := bstep (se 1 (by rfl) ⟨8072285, by rfl⟩ : syracuseStep 10763047 = 16144571) B16144571
theorem B5381063 : Blo 1768085 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B12098575 : Blo 1768085 12098575 := bstep (se 1 (by rfl) ⟨9073931, by rfl⟩ : syracuseStep 12098575 = 18147863) B18147863
theorem B1768559 : Blo 1768085 1768559 := bstep (se 1 (by rfl) ⟨1326419, by rfl⟩ : syracuseStep 1768559 = 2652839) B2652839
theorem B2653343 : Blo 1768085 2653343 := bstep (se 1 (by rfl) ⟨1990007, by rfl⟩ : syracuseStep 2653343 = 3980015) B3980015
theorem B7560391 : Blo 1768085 7560391 := bstep (se 1 (by rfl) ⟨5670293, by rfl⟩ : syracuseStep 7560391 = 11340587) B11340587
theorem B1768687 : Blo 1768085 1768687 := bstep (se 1 (by rfl) ⟨1326515, by rfl⟩ : syracuseStep 1768687 = 2653031) B2653031
theorem B1768703 : Blo 1768085 1768703 := bstep (se 1 (by rfl) ⟨1326527, by rfl⟩ : syracuseStep 1768703 = 2653055) B2653055
theorem B22658413 : Blo 1768085 22658413 := bstep (se 3 (by rfl) ⟨4248452, by rfl⟩ : syracuseStep 22658413 = 8496905) B8496905
theorem B2653631 : Blo 1768085 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B4783835 : Blo 1768085 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B10911671 : Blo 1768085 10911671 := bstep (se 1 (by rfl) ⟨8183753, by rfl⟩ : syracuseStep 10911671 = 16367507) B16367507
theorem B2654201 : Blo 1768085 2654201 := bstep (se 2 (by rfl) ⟨995325, by rfl⟩ : syracuseStep 2654201 = 1990651) B1990651
theorem B2654255 : Blo 1768085 2654255 := bstep (se 1 (by rfl) ⟨1990691, by rfl⟩ : syracuseStep 2654255 = 3981383) B3981383
theorem B209543321 : Blo 1768085 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B5972129 : Blo 1768085 5972129 := bstep (se 2 (by rfl) ⟨2239548, by rfl⟩ : syracuseStep 5972129 = 4479097) B4479097
theorem B3982319 : Blo 1768085 3982319 := bstep (se 1 (by rfl) ⟨2986739, by rfl⟩ : syracuseStep 3982319 = 5973479) B5973479
theorem B11339027 : Blo 1768085 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B38266181 : Blo 1768085 38266181 := bstep (se 4 (by rfl) ⟨3587454, by rfl⟩ : syracuseStep 38266181 = 7174909) B7174909
theorem B16131433 : Blo 1768085 16131433 := bstep (se 2 (by rfl) ⟨6049287, by rfl⟩ : syracuseStep 16131433 = 12098575) B12098575
theorem B229582511 : Blo 1768085 229582511 := bstep (se 1 (by rfl) ⟨172186883, by rfl⟩ : syracuseStep 229582511 = 344373767) B344373767
theorem B3189223 : Blo 1768085 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B13798091 : Blo 1768085 13798091 := bstep (se 1 (by rfl) ⟨10348568, by rfl⟩ : syracuseStep 13798091 = 20697137) B20697137
theorem B14339375 : Blo 1768085 14339375 := bstep (se 1 (by rfl) ⟨10754531, by rfl⟩ : syracuseStep 14339375 = 21509063) B21509063
theorem B38235563 : Blo 1768085 38235563 := bstep (se 1 (by rfl) ⟨28676672, by rfl⟩ : syracuseStep 38235563 = 57353345) B57353345
theorem B25505887 : Blo 1768085 25505887 := bstep (se 1 (by rfl) ⟨19129415, by rfl⟩ : syracuseStep 25505887 = 38258831) B38258831
theorem B10080521 : Blo 1768085 10080521 := bstep (se 2 (by rfl) ⟨3780195, by rfl⟩ : syracuseStep 10080521 = 7560391) B7560391
theorem B86086061 : Blo 1768085 86086061 := bstep (se 3 (by rfl) ⟨16141136, by rfl⟩ : syracuseStep 86086061 = 32282273) B32282273
theorem B3584503 : Blo 1768085 3584503 := bstep (se 1 (by rfl) ⟨2688377, by rfl⟩ : syracuseStep 3584503 = 5376755) B5376755
theorem B15118973 : Blo 1768085 15118973 := bstep (se 3 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 15118973 = 5669615) B5669615
theorem B7558991 : Blo 1768085 7558991 := bstep (se 1 (by rfl) ⟨5669243, by rfl⟩ : syracuseStep 7558991 = 11338487) B11338487
theorem B3979295 : Blo 1768085 3979295 := bstep (se 1 (by rfl) ⟨2984471, by rfl⟩ : syracuseStep 3979295 = 5968943) B5968943
theorem B72620327 : Blo 1768085 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B14350729 : Blo 1768085 14350729 := bstep (se 2 (by rfl) ⟨5381523, by rfl⟩ : syracuseStep 14350729 = 10763047) B10763047
theorem B19126691 : Blo 1768085 19126691 := bstep (se 1 (by rfl) ⟨14345018, by rfl⟩ : syracuseStep 19126691 = 28690037) B28690037
theorem B1768091 : Blo 1768085 1768091 := bstep (se 1 (by rfl) ⟨1326068, by rfl⟩ : syracuseStep 1768091 = 2652137) B2652137
theorem B3979943 : Blo 1768085 3979943 := bstep (se 1 (by rfl) ⟨2984957, by rfl⟩ : syracuseStep 3979943 = 5969915) B5969915
theorem B3980087 : Blo 1768085 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B2653127 : Blo 1768085 2653127 := bstep (se 1 (by rfl) ⟨1989845, by rfl⟩ : syracuseStep 2653127 = 3979691) B3979691
theorem B1768479 : Blo 1768085 1768479 := bstep (se 1 (by rfl) ⟨1326359, by rfl⟩ : syracuseStep 1768479 = 2652719) B2652719
theorem B5971049 : Blo 1768085 5971049 := bstep (se 2 (by rfl) ⟨2239143, by rfl⟩ : syracuseStep 5971049 = 4478287) B4478287
theorem B30211217 : Blo 1768085 30211217 := bstep (se 2 (by rfl) ⟨11329206, by rfl⟩ : syracuseStep 30211217 = 22658413) B22658413
theorem B5971103 : Blo 1768085 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B6134983 : Blo 1768085 6134983 := bstep (se 1 (by rfl) ⟨4601237, by rfl⟩ : syracuseStep 6134983 = 9202475) B9202475
theorem B3587375 : Blo 1768085 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B1768895 : Blo 1768085 1768895 := bstep (se 1 (by rfl) ⟨1326671, by rfl⟩ : syracuseStep 1768895 = 2653343) B2653343
theorem B1990111 : Blo 1768085 1990111 := bstep (se 1 (by rfl) ⟨1492583, by rfl⟩ : syracuseStep 1990111 = 2985167) B2985167
theorem B1769087 : Blo 1768085 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B7274447 : Blo 1768085 7274447 := bstep (se 1 (by rfl) ⟨5455835, by rfl⟩ : syracuseStep 7274447 = 10911671) B10911671
theorem B1769467 : Blo 1768085 1769467 := bstep (se 1 (by rfl) ⟨1327100, by rfl⟩ : syracuseStep 1769467 = 2654201) B2654201
theorem B1769503 : Blo 1768085 1769503 := bstep (se 1 (by rfl) ⟨1327127, by rfl⟩ : syracuseStep 1769503 = 2654255) B2654255
theorem B3981419 : Blo 1768085 3981419 := bstep (se 1 (by rfl) ⟨2986064, by rfl⟩ : syracuseStep 3981419 = 5972129) B5972129
theorem B2654879 : Blo 1768085 2654879 := bstep (se 1 (by rfl) ⟨1991159, by rfl⟩ : syracuseStep 2654879 = 3982319) B3982319
theorem B25510787 : Blo 1768085 25510787 := bstep (se 1 (by rfl) ⟨19133090, by rfl⟩ : syracuseStep 25510787 = 38266181) B38266181
theorem B32719909 : Blo 1768085 32719909 := bstep (se 4 (by rfl) ⟨3067491, by rfl⟩ : syracuseStep 32719909 = 6134983) B6134983
theorem B5039327 : Blo 1768085 5039327 := bstep (se 1 (by rfl) ⟨3779495, by rfl⟩ : syracuseStep 5039327 = 7558991) B7558991
theorem B17009189 : Blo 1768085 17009189 := bstep (se 4 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 17009189 = 3189223) B3189223
theorem B34007849 : Blo 1768085 34007849 := bstep (se 2 (by rfl) ⟨12752943, by rfl⟩ : syracuseStep 34007849 = 25505887) B25505887
theorem B6720347 : Blo 1768085 6720347 := bstep (se 1 (by rfl) ⟨5040260, by rfl⟩ : syracuseStep 6720347 = 10080521) B10080521
theorem B10079315 : Blo 1768085 10079315 := bstep (se 1 (by rfl) ⟨7559486, by rfl⟩ : syracuseStep 10079315 = 15118973) B15118973
theorem B4779337 : Blo 1768085 4779337 := bstep (se 2 (by rfl) ⟨1792251, by rfl⟩ : syracuseStep 4779337 = 3584503) B3584503
theorem B153055007 : Blo 1768085 153055007 := bstep (se 1 (by rfl) ⟨114791255, by rfl⟩ : syracuseStep 153055007 = 229582511) B229582511
theorem B12751127 : Blo 1768085 12751127 := bstep (se 1 (by rfl) ⟨9563345, by rfl⟩ : syracuseStep 12751127 = 19126691) B19126691
theorem B21508577 : Blo 1768085 21508577 := bstep (se 2 (by rfl) ⟨8065716, by rfl⟩ : syracuseStep 21508577 = 16131433) B16131433
theorem B20140811 : Blo 1768085 20140811 := bstep (se 1 (by rfl) ⟨15105608, by rfl⟩ : syracuseStep 20140811 = 30211217) B30211217
theorem B25490375 : Blo 1768085 25490375 := bstep (se 1 (by rfl) ⟨19117781, by rfl⟩ : syracuseStep 25490375 = 38235563) B38235563
theorem B139695547 : Blo 1768085 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B57390707 : Blo 1768085 57390707 := bstep (se 1 (by rfl) ⟨43043030, by rfl⟩ : syracuseStep 57390707 = 86086061) B86086061
theorem B19134305 : Blo 1768085 19134305 := bstep (se 2 (by rfl) ⟨7175364, by rfl⟩ : syracuseStep 19134305 = 14350729) B14350729
theorem B9566333 : Blo 1768085 9566333 := bstep (se 3 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 9566333 = 3587375) B3587375
theorem B7559351 : Blo 1768085 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B2652863 : Blo 1768085 2652863 := bstep (se 1 (by rfl) ⟨1989647, by rfl⟩ : syracuseStep 2652863 = 3979295) B3979295
theorem B48413551 : Blo 1768085 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B2653295 : Blo 1768085 2653295 := bstep (se 1 (by rfl) ⟨1989971, by rfl⟩ : syracuseStep 2653295 = 3979943) B3979943
theorem B9198727 : Blo 1768085 9198727 := bstep (se 1 (by rfl) ⟨6899045, by rfl⟩ : syracuseStep 9198727 = 13798091) B13798091
theorem B2653391 : Blo 1768085 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B2653481 : Blo 1768085 2653481 := bstep (se 2 (by rfl) ⟨995055, by rfl⟩ : syracuseStep 2653481 = 1990111) B1990111
theorem B1768751 : Blo 1768085 1768751 := bstep (se 1 (by rfl) ⟨1326563, by rfl⟩ : syracuseStep 1768751 = 2653127) B2653127
theorem B3980699 : Blo 1768085 3980699 := bstep (se 1 (by rfl) ⟨2985524, by rfl⟩ : syracuseStep 3980699 = 5971049) B5971049
theorem B3980735 : Blo 1768085 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B9559583 : Blo 1768085 9559583 := bstep (se 1 (by rfl) ⟨7169687, by rfl⟩ : syracuseStep 9559583 = 14339375) B14339375
theorem B4849631 : Blo 1768085 4849631 := bstep (se 1 (by rfl) ⟨3637223, by rfl⟩ : syracuseStep 4849631 = 7274447) B7274447
theorem B2654279 : Blo 1768085 2654279 := bstep (se 1 (by rfl) ⟨1990709, by rfl⟩ : syracuseStep 2654279 = 3981419) B3981419
theorem B196239509 : Blo 1768085 196239509 := bstep (se 6 (by rfl) ⟨4599363, by rfl⟩ : syracuseStep 196239509 = 9198727) B9198727
theorem B1769919 : Blo 1768085 1769919 := bstep (se 1 (by rfl) ⟨1327439, by rfl⟩ : syracuseStep 1769919 = 2654879) B2654879
theorem B13427207 : Blo 1768085 13427207 := bstep (se 1 (by rfl) ⟨10070405, by rfl⟩ : syracuseStep 13427207 = 20140811) B20140811
theorem B17007191 : Blo 1768085 17007191 := bstep (se 1 (by rfl) ⟨12755393, by rfl⟩ : syracuseStep 17007191 = 25510787) B25510787
theorem B3359551 : Blo 1768085 3359551 := bstep (se 1 (by rfl) ⟨2519663, by rfl⟩ : syracuseStep 3359551 = 5039327) B5039327
theorem B12756203 : Blo 1768085 12756203 := bstep (se 1 (by rfl) ⟨9567152, by rfl⟩ : syracuseStep 12756203 = 19134305) B19134305
theorem B5039567 : Blo 1768085 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B11339459 : Blo 1768085 11339459 := bstep (se 1 (by rfl) ⟨8504594, by rfl⟩ : syracuseStep 11339459 = 17009189) B17009189
theorem B6719543 : Blo 1768085 6719543 := bstep (se 1 (by rfl) ⟨5039657, by rfl⟩ : syracuseStep 6719543 = 10079315) B10079315
theorem B14339051 : Blo 1768085 14339051 := bstep (se 1 (by rfl) ⟨10754288, by rfl⟩ : syracuseStep 14339051 = 21508577) B21508577
theorem B16993583 : Blo 1768085 16993583 := bstep (se 1 (by rfl) ⟨12745187, by rfl⟩ : syracuseStep 16993583 = 25490375) B25490375
theorem B38260471 : Blo 1768085 38260471 := bstep (se 1 (by rfl) ⟨28695353, by rfl⟩ : syracuseStep 38260471 = 57390707) B57390707
theorem B43626545 : Blo 1768085 43626545 := bstep (se 2 (by rfl) ⟨16359954, by rfl⟩ : syracuseStep 43626545 = 32719909) B32719909
theorem B6377555 : Blo 1768085 6377555 := bstep (se 1 (by rfl) ⟨4783166, by rfl⟩ : syracuseStep 6377555 = 9566333) B9566333
theorem B22671899 : Blo 1768085 22671899 := bstep (se 1 (by rfl) ⟨17003924, by rfl⟩ : syracuseStep 22671899 = 34007849) B34007849
theorem B102036671 : Blo 1768085 102036671 := bstep (se 1 (by rfl) ⟨76527503, by rfl⟩ : syracuseStep 102036671 = 153055007) B153055007
theorem B3233087 : Blo 1768085 3233087 := bstep (se 1 (by rfl) ⟨2424815, by rfl⟩ : syracuseStep 3233087 = 4849631) B4849631
theorem B8500751 : Blo 1768085 8500751 := bstep (se 1 (by rfl) ⟨6375563, by rfl⟩ : syracuseStep 8500751 = 12751127) B12751127
theorem B64551401 : Blo 1768085 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B6372449 : Blo 1768085 6372449 := bstep (se 2 (by rfl) ⟨2389668, by rfl⟩ : syracuseStep 6372449 = 4779337) B4779337
theorem B1768575 : Blo 1768085 1768575 := bstep (se 1 (by rfl) ⟨1326431, by rfl⟩ : syracuseStep 1768575 = 2652863) B2652863
theorem B4480231 : Blo 1768085 4480231 := bstep (se 1 (by rfl) ⟨3360173, by rfl⟩ : syracuseStep 4480231 = 6720347) B6720347
theorem B186260729 : Blo 1768085 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B1768863 : Blo 1768085 1768863 := bstep (se 1 (by rfl) ⟨1326647, by rfl⟩ : syracuseStep 1768863 = 2653295) B2653295
theorem B1768927 : Blo 1768085 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B1768987 : Blo 1768085 1768987 := bstep (se 1 (by rfl) ⟨1326740, by rfl⟩ : syracuseStep 1768987 = 2653481) B2653481
theorem B2653799 : Blo 1768085 2653799 := bstep (se 1 (by rfl) ⟨1990349, by rfl⟩ : syracuseStep 2653799 = 3980699) B3980699
theorem B2653823 : Blo 1768085 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B6373055 : Blo 1768085 6373055 := bstep (se 1 (by rfl) ⟨4779791, by rfl⟩ : syracuseStep 6373055 = 9559583) B9559583
theorem B1769519 : Blo 1768085 1769519 := bstep (se 1 (by rfl) ⟨1327139, by rfl⟩ : syracuseStep 1769519 = 2654279) B2654279
theorem B4251703 : Blo 1768085 4251703 := bstep (se 1 (by rfl) ⟨3188777, by rfl⟩ : syracuseStep 4251703 = 6377555) B6377555
theorem B130826339 : Blo 1768085 130826339 := bstep (se 1 (by rfl) ⟨98119754, by rfl⟩ : syracuseStep 130826339 = 196239509) B196239509
theorem B15114599 : Blo 1768085 15114599 := bstep (se 1 (by rfl) ⟨11335949, by rfl⟩ : syracuseStep 15114599 = 22671899) B22671899
theorem B11338127 : Blo 1768085 11338127 := bstep (se 1 (by rfl) ⟨8503595, by rfl⟩ : syracuseStep 11338127 = 17007191) B17007191
theorem B8504135 : Blo 1768085 8504135 := bstep (se 1 (by rfl) ⟨6378101, by rfl⟩ : syracuseStep 8504135 = 12756203) B12756203
theorem B2155391 : Blo 1768085 2155391 := bstep (se 1 (by rfl) ⟨1616543, by rfl⟩ : syracuseStep 2155391 = 3233087) B3233087
theorem B3359711 : Blo 1768085 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B5973641 : Blo 1768085 5973641 := bstep (se 2 (by rfl) ⟨2240115, by rfl⟩ : syracuseStep 5973641 = 4480231) B4480231
theorem B43034267 : Blo 1768085 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B51013961 : Blo 1768085 51013961 := bstep (se 2 (by rfl) ⟨19130235, by rfl⟩ : syracuseStep 51013961 = 38260471) B38260471
theorem B29084363 : Blo 1768085 29084363 := bstep (se 1 (by rfl) ⟨21813272, by rfl⟩ : syracuseStep 29084363 = 43626545) B43626545
theorem B4248299 : Blo 1768085 4248299 := bstep (se 1 (by rfl) ⟨3186224, by rfl⟩ : syracuseStep 4248299 = 6372449) B6372449
theorem B4248703 : Blo 1768085 4248703 := bstep (se 1 (by rfl) ⟨3186527, by rfl⟩ : syracuseStep 4248703 = 6373055) B6373055
theorem B8951471 : Blo 1768085 8951471 := bstep (se 1 (by rfl) ⟨6713603, by rfl⟩ : syracuseStep 8951471 = 13427207) B13427207
theorem B496695277 : Blo 1768085 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B68024447 : Blo 1768085 68024447 := bstep (se 1 (by rfl) ⟨51018335, by rfl⟩ : syracuseStep 68024447 = 102036671) B102036671
theorem B5667167 : Blo 1768085 5667167 := bstep (se 1 (by rfl) ⟨4250375, by rfl⟩ : syracuseStep 5667167 = 8500751) B8500751
theorem B4479401 : Blo 1768085 4479401 := bstep (se 2 (by rfl) ⟨1679775, by rfl⟩ : syracuseStep 4479401 = 3359551) B3359551
theorem B7559639 : Blo 1768085 7559639 := bstep (se 1 (by rfl) ⟨5669729, by rfl⟩ : syracuseStep 7559639 = 11339459) B11339459
theorem B4479695 : Blo 1768085 4479695 := bstep (se 1 (by rfl) ⟨3359771, by rfl⟩ : syracuseStep 4479695 = 6719543) B6719543
theorem B9559367 : Blo 1768085 9559367 := bstep (se 1 (by rfl) ⟨7169525, by rfl⟩ : syracuseStep 9559367 = 14339051) B14339051
theorem B11329055 : Blo 1768085 11329055 := bstep (se 1 (by rfl) ⟨8496791, by rfl⟩ : syracuseStep 11329055 = 16993583) B16993583
theorem B1769199 : Blo 1768085 1769199 := bstep (se 1 (by rfl) ⟨1326899, by rfl⟩ : syracuseStep 1769199 = 2653799) B2653799
theorem B1769215 : Blo 1768085 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B5668937 : Blo 1768085 5668937 := bstep (se 2 (by rfl) ⟨2125851, by rfl⟩ : syracuseStep 5668937 = 4251703) B4251703
theorem B10076399 : Blo 1768085 10076399 := bstep (se 1 (by rfl) ⟨7557299, by rfl⟩ : syracuseStep 10076399 = 15114599) B15114599
theorem B5669423 : Blo 1768085 5669423 := bstep (se 1 (by rfl) ⟨4252067, by rfl⟩ : syracuseStep 5669423 = 8504135) B8504135
theorem B22659749 : Blo 1768085 22659749 := bstep (se 4 (by rfl) ⟨2124351, by rfl⟩ : syracuseStep 22659749 = 4248703) B4248703
theorem B3982427 : Blo 1768085 3982427 := bstep (se 1 (by rfl) ⟨2986820, by rfl⟩ : syracuseStep 3982427 = 5973641) B5973641
theorem B28689511 : Blo 1768085 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B3778111 : Blo 1768085 3778111 := bstep (se 1 (by rfl) ⟨2833583, by rfl⟩ : syracuseStep 3778111 = 5667167) B5667167
theorem B5039759 : Blo 1768085 5039759 := bstep (se 1 (by rfl) ⟨3779819, by rfl⟩ : syracuseStep 5039759 = 7559639) B7559639
theorem B662260369 : Blo 1768085 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B2239807 : Blo 1768085 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B5967647 : Blo 1768085 5967647 := bstep (se 1 (by rfl) ⟨4475735, by rfl⟩ : syracuseStep 5967647 = 8951471) B8951471
theorem B22990837 : Blo 1768085 22990837 := bstep (se 5 (by rfl) ⟨1077695, by rfl⟩ : syracuseStep 22990837 = 2155391) B2155391
theorem B34009307 : Blo 1768085 34009307 := bstep (se 1 (by rfl) ⟨25506980, by rfl⟩ : syracuseStep 34009307 = 51013961) B51013961
theorem B2986267 : Blo 1768085 2986267 := bstep (se 1 (by rfl) ⟨2239700, by rfl⟩ : syracuseStep 2986267 = 4479401) B4479401
theorem B2986463 : Blo 1768085 2986463 := bstep (se 1 (by rfl) ⟨2239847, by rfl⟩ : syracuseStep 2986463 = 4479695) B4479695
theorem B87217559 : Blo 1768085 87217559 := bstep (se 1 (by rfl) ⟨65413169, by rfl⟩ : syracuseStep 87217559 = 130826339) B130826339
theorem B7558751 : Blo 1768085 7558751 := bstep (se 1 (by rfl) ⟨5669063, by rfl⟩ : syracuseStep 7558751 = 11338127) B11338127
theorem B45349631 : Blo 1768085 45349631 := bstep (se 1 (by rfl) ⟨34012223, by rfl⟩ : syracuseStep 45349631 = 68024447) B68024447
theorem B19389575 : Blo 1768085 19389575 := bstep (se 1 (by rfl) ⟨14542181, by rfl⟩ : syracuseStep 19389575 = 29084363) B29084363
theorem B11328797 : Blo 1768085 11328797 := bstep (se 3 (by rfl) ⟨2124149, by rfl⟩ : syracuseStep 11328797 = 4248299) B4248299
theorem B6372911 : Blo 1768085 6372911 := bstep (se 1 (by rfl) ⟨4779683, by rfl⟩ : syracuseStep 6372911 = 9559367) B9559367
theorem B7552703 : Blo 1768085 7552703 := bstep (se 1 (by rfl) ⟨5664527, by rfl⟩ : syracuseStep 7552703 = 11329055) B11329055
theorem B6717599 : Blo 1768085 6717599 := bstep (se 1 (by rfl) ⟨5038199, by rfl⟩ : syracuseStep 6717599 = 10076399) B10076399
theorem B1990975 : Blo 1768085 1990975 := bstep (se 1 (by rfl) ⟨1493231, by rfl⟩ : syracuseStep 1990975 = 2986463) B2986463
theorem B3981689 : Blo 1768085 3981689 := bstep (se 2 (by rfl) ⟨1493133, by rfl⟩ : syracuseStep 3981689 = 2986267) B2986267
theorem B15106499 : Blo 1768085 15106499 := bstep (se 1 (by rfl) ⟨11329874, by rfl⟩ : syracuseStep 15106499 = 22659749) B22659749
theorem B2654951 : Blo 1768085 2654951 := bstep (se 1 (by rfl) ⟨1991213, by rfl⟩ : syracuseStep 2654951 = 3982427) B3982427
theorem B5039167 : Blo 1768085 5039167 := bstep (se 1 (by rfl) ⟨3779375, by rfl⟩ : syracuseStep 5039167 = 7558751) B7558751
theorem B3779291 : Blo 1768085 3779291 := bstep (se 1 (by rfl) ⟨2834468, by rfl⟩ : syracuseStep 3779291 = 5668937) B5668937
theorem B3779615 : Blo 1768085 3779615 := bstep (se 1 (by rfl) ⟨2834711, by rfl⟩ : syracuseStep 3779615 = 5669423) B5669423
theorem B38252681 : Blo 1768085 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B13439357 : Blo 1768085 13439357 := bstep (se 3 (by rfl) ⟨2519879, by rfl⟩ : syracuseStep 13439357 = 5039759) B5039759
theorem B2986409 : Blo 1768085 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B30233087 : Blo 1768085 30233087 := bstep (se 1 (by rfl) ⟨22674815, by rfl⟩ : syracuseStep 30233087 = 45349631) B45349631
theorem B4248607 : Blo 1768085 4248607 := bstep (se 1 (by rfl) ⟨3186455, by rfl⟩ : syracuseStep 4248607 = 6372911) B6372911
theorem B5035135 : Blo 1768085 5035135 := bstep (se 1 (by rfl) ⟨3776351, by rfl⟩ : syracuseStep 5035135 = 7552703) B7552703
theorem B3978431 : Blo 1768085 3978431 := bstep (se 1 (by rfl) ⟨2983823, by rfl⟩ : syracuseStep 3978431 = 5967647) B5967647
theorem B22672871 : Blo 1768085 22672871 := bstep (se 1 (by rfl) ⟨17004653, by rfl⟩ : syracuseStep 22672871 = 34009307) B34009307
theorem B51705533 : Blo 1768085 51705533 := bstep (se 3 (by rfl) ⟨9694787, by rfl⟩ : syracuseStep 51705533 = 19389575) B19389575
theorem B883013825 : Blo 1768085 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B58145039 : Blo 1768085 58145039 := bstep (se 1 (by rfl) ⟨43608779, by rfl⟩ : syracuseStep 58145039 = 87217559) B87217559
theorem B5037481 : Blo 1768085 5037481 := bstep (se 2 (by rfl) ⟨1889055, by rfl⟩ : syracuseStep 5037481 = 3778111) B3778111
theorem B7552531 : Blo 1768085 7552531 := bstep (se 1 (by rfl) ⟨5664398, by rfl⟩ : syracuseStep 7552531 = 11328797) B11328797
theorem B30654449 : Blo 1768085 30654449 := bstep (se 2 (by rfl) ⟨11495418, by rfl⟩ : syracuseStep 30654449 = 22990837) B22990837
theorem B25501787 : Blo 1768085 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B2654459 : Blo 1768085 2654459 := bstep (se 1 (by rfl) ⟨1990844, by rfl⟩ : syracuseStep 2654459 = 3981689) B3981689
theorem B1990939 : Blo 1768085 1990939 := bstep (se 1 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 1990939 = 2986409) B2986409
theorem B2654633 : Blo 1768085 2654633 := bstep (se 2 (by rfl) ⟨995487, by rfl⟩ : syracuseStep 2654633 = 1990975) B1990975
theorem B1769967 : Blo 1768085 1769967 := bstep (se 1 (by rfl) ⟨1327475, by rfl⟩ : syracuseStep 1769967 = 2654951) B2654951
theorem B15115247 : Blo 1768085 15115247 := bstep (se 1 (by rfl) ⟨11336435, by rfl⟩ : syracuseStep 15115247 = 22672871) B22672871
theorem B6718889 : Blo 1768085 6718889 := bstep (se 2 (by rfl) ⟨2519583, by rfl⟩ : syracuseStep 6718889 = 5039167) B5039167
theorem B10070041 : Blo 1768085 10070041 := bstep (se 2 (by rfl) ⟨3776265, by rfl⟩ : syracuseStep 10070041 = 7552531) B7552531
theorem B10070999 : Blo 1768085 10070999 := bstep (se 1 (by rfl) ⟨7553249, by rfl⟩ : syracuseStep 10070999 = 15106499) B15106499
theorem B20155391 : Blo 1768085 20155391 := bstep (se 1 (by rfl) ⟨15116543, by rfl⟩ : syracuseStep 20155391 = 30233087) B30233087
theorem B5664809 : Blo 1768085 5664809 := bstep (se 2 (by rfl) ⟨2124303, by rfl⟩ : syracuseStep 5664809 = 4248607) B4248607
theorem B6713513 : Blo 1768085 6713513 := bstep (se 2 (by rfl) ⟨2517567, by rfl⟩ : syracuseStep 6713513 = 5035135) B5035135
theorem B2519527 : Blo 1768085 2519527 := bstep (se 1 (by rfl) ⟨1889645, by rfl⟩ : syracuseStep 2519527 = 3779291) B3779291
theorem B2519743 : Blo 1768085 2519743 := bstep (se 1 (by rfl) ⟨1889807, by rfl⟩ : syracuseStep 2519743 = 3779615) B3779615
theorem B20436299 : Blo 1768085 20436299 := bstep (se 1 (by rfl) ⟨15327224, by rfl⟩ : syracuseStep 20436299 = 30654449) B30654449
theorem B4478399 : Blo 1768085 4478399 := bstep (se 1 (by rfl) ⟨3358799, by rfl⟩ : syracuseStep 4478399 = 6717599) B6717599
theorem B8959571 : Blo 1768085 8959571 := bstep (se 1 (by rfl) ⟨6719678, by rfl⟩ : syracuseStep 8959571 = 13439357) B13439357
theorem B2652287 : Blo 1768085 2652287 := bstep (se 1 (by rfl) ⟨1989215, by rfl⟩ : syracuseStep 2652287 = 3978431) B3978431
theorem B34470355 : Blo 1768085 34470355 := bstep (se 1 (by rfl) ⟨25852766, by rfl⟩ : syracuseStep 34470355 = 51705533) B51705533
theorem B588675883 : Blo 1768085 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B38763359 : Blo 1768085 38763359 := bstep (se 1 (by rfl) ⟨29072519, by rfl⟩ : syracuseStep 38763359 = 58145039) B58145039
theorem B6716641 : Blo 1768085 6716641 := bstep (se 2 (by rfl) ⟨2518740, by rfl⟩ : syracuseStep 6716641 = 5037481) B5037481
theorem B3776539 : Blo 1768085 3776539 := bstep (se 1 (by rfl) ⟨2832404, by rfl⟩ : syracuseStep 3776539 = 5664809) B5664809
theorem B13426721 : Blo 1768085 13426721 := bstep (se 2 (by rfl) ⟨5035020, by rfl⟩ : syracuseStep 13426721 = 10070041) B10070041
theorem B1769639 : Blo 1768085 1769639 := bstep (se 1 (by rfl) ⟨1327229, by rfl⟩ : syracuseStep 1769639 = 2654459) B2654459
theorem B1769755 : Blo 1768085 1769755 := bstep (se 1 (by rfl) ⟨1327316, by rfl⟩ : syracuseStep 1769755 = 2654633) B2654633
theorem B2654585 : Blo 1768085 2654585 := bstep (se 2 (by rfl) ⟨995469, by rfl⟩ : syracuseStep 2654585 = 1990939) B1990939
theorem B3359369 : Blo 1768085 3359369 := bstep (se 2 (by rfl) ⟨1259763, by rfl⟩ : syracuseStep 3359369 = 2519527) B2519527
theorem B10076831 : Blo 1768085 10076831 := bstep (se 1 (by rfl) ⟨7557623, by rfl⟩ : syracuseStep 10076831 = 15115247) B15115247
theorem B13624199 : Blo 1768085 13624199 := bstep (se 1 (by rfl) ⟨10218149, by rfl⟩ : syracuseStep 13624199 = 20436299) B20436299
theorem B3359657 : Blo 1768085 3359657 := bstep (se 2 (by rfl) ⟨1259871, by rfl⟩ : syracuseStep 3359657 = 2519743) B2519743
theorem B5973047 : Blo 1768085 5973047 := bstep (se 1 (by rfl) ⟨4479785, by rfl⟩ : syracuseStep 5973047 = 8959571) B8959571
theorem B784901177 : Blo 1768085 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B8955521 : Blo 1768085 8955521 := bstep (se 2 (by rfl) ⟨3358320, by rfl⟩ : syracuseStep 8955521 = 6716641) B6716641
theorem B13436927 : Blo 1768085 13436927 := bstep (se 1 (by rfl) ⟨10077695, by rfl⟩ : syracuseStep 13436927 = 20155391) B20155391
theorem B17001191 : Blo 1768085 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B4475675 : Blo 1768085 4475675 := bstep (se 1 (by rfl) ⟨3356756, by rfl⟩ : syracuseStep 4475675 = 6713513) B6713513
theorem B45960473 : Blo 1768085 45960473 := bstep (se 2 (by rfl) ⟨17235177, by rfl⟩ : syracuseStep 45960473 = 34470355) B34470355
theorem B2985599 : Blo 1768085 2985599 := bstep (se 1 (by rfl) ⟨2239199, by rfl⟩ : syracuseStep 2985599 = 4478399) B4478399
theorem B25842239 : Blo 1768085 25842239 := bstep (se 1 (by rfl) ⟨19381679, by rfl⟩ : syracuseStep 25842239 = 38763359) B38763359
theorem B6713999 : Blo 1768085 6713999 := bstep (se 1 (by rfl) ⟨5035499, by rfl⟩ : syracuseStep 6713999 = 10070999) B10070999
theorem B4479259 : Blo 1768085 4479259 := bstep (se 1 (by rfl) ⟨3359444, by rfl⟩ : syracuseStep 4479259 = 6718889) B6718889
theorem B1768191 : Blo 1768085 1768191 := bstep (se 1 (by rfl) ⟨1326143, by rfl⟩ : syracuseStep 1768191 = 2652287) B2652287
theorem B1769723 : Blo 1768085 1769723 := bstep (se 1 (by rfl) ⟨1327292, by rfl⟩ : syracuseStep 1769723 = 2654585) B2654585
theorem B5972345 : Blo 1768085 5972345 := bstep (se 2 (by rfl) ⟨2239629, by rfl⟩ : syracuseStep 5972345 = 4479259) B4479259
theorem B17228159 : Blo 1768085 17228159 := bstep (se 1 (by rfl) ⟨12921119, by rfl⟩ : syracuseStep 17228159 = 25842239) B25842239
theorem B6717887 : Blo 1768085 6717887 := bstep (se 1 (by rfl) ⟨5038415, by rfl⟩ : syracuseStep 6717887 = 10076831) B10076831
theorem B3982031 : Blo 1768085 3982031 := bstep (se 1 (by rfl) ⟨2986523, by rfl⟩ : syracuseStep 3982031 = 5973047) B5973047
theorem B2983783 : Blo 1768085 2983783 := bstep (se 1 (by rfl) ⟨2237837, by rfl⟩ : syracuseStep 2983783 = 4475675) B4475675
theorem B45336509 : Blo 1768085 45336509 := bstep (se 3 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 45336509 = 17001191) B17001191
theorem B30640315 : Blo 1768085 30640315 := bstep (se 1 (by rfl) ⟨22980236, by rfl⟩ : syracuseStep 30640315 = 45960473) B45960473
theorem B2239579 : Blo 1768085 2239579 := bstep (se 1 (by rfl) ⟨1679684, by rfl⟩ : syracuseStep 2239579 = 3359369) B3359369
theorem B4475999 : Blo 1768085 4475999 := bstep (se 1 (by rfl) ⟨3356999, by rfl⟩ : syracuseStep 4475999 = 6713999) B6713999
theorem B523267451 : Blo 1768085 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B8957951 : Blo 1768085 8957951 := bstep (se 1 (by rfl) ⟨6718463, by rfl⟩ : syracuseStep 8957951 = 13436927) B13436927
theorem B8959085 : Blo 1768085 8959085 := bstep (se 3 (by rfl) ⟨1679828, by rfl⟩ : syracuseStep 8959085 = 3359657) B3359657
theorem B8951147 : Blo 1768085 8951147 := bstep (se 1 (by rfl) ⟨6713360, by rfl⟩ : syracuseStep 8951147 = 13426721) B13426721
theorem B5035385 : Blo 1768085 5035385 := bstep (se 2 (by rfl) ⟨1888269, by rfl⟩ : syracuseStep 5035385 = 3776539) B3776539
theorem B9082799 : Blo 1768085 9082799 := bstep (se 1 (by rfl) ⟨6812099, by rfl⟩ : syracuseStep 9082799 = 13624199) B13624199
theorem B5970347 : Blo 1768085 5970347 := bstep (se 1 (by rfl) ⟨4477760, by rfl⟩ : syracuseStep 5970347 = 8955521) B8955521
theorem B1990399 : Blo 1768085 1990399 := bstep (se 1 (by rfl) ⟨1492799, by rfl⟩ : syracuseStep 1990399 = 2985599) B2985599
theorem B40853753 : Blo 1768085 40853753 := bstep (se 2 (by rfl) ⟨15320157, by rfl⟩ : syracuseStep 40853753 = 30640315) B30640315
theorem B3981563 : Blo 1768085 3981563 := bstep (se 1 (by rfl) ⟨2986172, by rfl⟩ : syracuseStep 3981563 = 5972345) B5972345
theorem B11485439 : Blo 1768085 11485439 := bstep (se 1 (by rfl) ⟨8614079, by rfl⟩ : syracuseStep 11485439 = 17228159) B17228159
theorem B2654687 : Blo 1768085 2654687 := bstep (se 1 (by rfl) ⟨1991015, by rfl⟩ : syracuseStep 2654687 = 3982031) B3982031
theorem B5972723 : Blo 1768085 5972723 := bstep (se 1 (by rfl) ⟨4479542, by rfl⟩ : syracuseStep 5972723 = 8959085) B8959085
theorem B13427693 : Blo 1768085 13427693 := bstep (se 3 (by rfl) ⟨2517692, by rfl⟩ : syracuseStep 13427693 = 5035385) B5035385
theorem B6055199 : Blo 1768085 6055199 := bstep (se 1 (by rfl) ⟨4541399, by rfl⟩ : syracuseStep 6055199 = 9082799) B9082799
theorem B2983999 : Blo 1768085 2983999 := bstep (se 1 (by rfl) ⟨2237999, by rfl⟩ : syracuseStep 2983999 = 4475999) B4475999
theorem B5967431 : Blo 1768085 5967431 := bstep (se 1 (by rfl) ⟨4475573, by rfl⟩ : syracuseStep 5967431 = 8951147) B8951147
theorem B30224339 : Blo 1768085 30224339 := bstep (se 1 (by rfl) ⟨22668254, by rfl⟩ : syracuseStep 30224339 = 45336509) B45336509
theorem B2986105 : Blo 1768085 2986105 := bstep (se 2 (by rfl) ⟨1119789, by rfl⟩ : syracuseStep 2986105 = 2239579) B2239579
theorem B348844967 : Blo 1768085 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B3978377 : Blo 1768085 3978377 := bstep (se 2 (by rfl) ⟨1491891, by rfl⟩ : syracuseStep 3978377 = 2983783) B2983783
theorem B4478591 : Blo 1768085 4478591 := bstep (se 1 (by rfl) ⟨3358943, by rfl⟩ : syracuseStep 4478591 = 6717887) B6717887
theorem B5971967 : Blo 1768085 5971967 := bstep (se 1 (by rfl) ⟨4478975, by rfl⟩ : syracuseStep 5971967 = 8957951) B8957951
theorem B3980231 : Blo 1768085 3980231 := bstep (se 1 (by rfl) ⟨2985173, by rfl⟩ : syracuseStep 3980231 = 5970347) B5970347
theorem B2653865 : Blo 1768085 2653865 := bstep (se 2 (by rfl) ⟨995199, by rfl⟩ : syracuseStep 2653865 = 1990399) B1990399
theorem B3981473 : Blo 1768085 3981473 := bstep (se 2 (by rfl) ⟨1493052, by rfl⟩ : syracuseStep 3981473 = 2986105) B2986105
theorem B2654375 : Blo 1768085 2654375 := bstep (se 1 (by rfl) ⟨1990781, by rfl⟩ : syracuseStep 2654375 = 3981563) B3981563
theorem B1769791 : Blo 1768085 1769791 := bstep (se 1 (by rfl) ⟨1327343, by rfl⟩ : syracuseStep 1769791 = 2654687) B2654687
theorem B3981815 : Blo 1768085 3981815 := bstep (se 1 (by rfl) ⟨2986361, by rfl⟩ : syracuseStep 3981815 = 5972723) B5972723
theorem B232563311 : Blo 1768085 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B3981311 : Blo 1768085 3981311 := bstep (se 1 (by rfl) ⟨2985983, by rfl⟩ : syracuseStep 3981311 = 5971967) B5971967
theorem B2985727 : Blo 1768085 2985727 := bstep (se 1 (by rfl) ⟨2239295, by rfl⟩ : syracuseStep 2985727 = 4478591) B4478591
theorem B3978287 : Blo 1768085 3978287 := bstep (se 1 (by rfl) ⟨2983715, by rfl⟩ : syracuseStep 3978287 = 5967431) B5967431
theorem B20149559 : Blo 1768085 20149559 := bstep (se 1 (by rfl) ⟨15112169, by rfl⟩ : syracuseStep 20149559 = 30224339) B30224339
theorem B3978665 : Blo 1768085 3978665 := bstep (se 2 (by rfl) ⟨1491999, by rfl⟩ : syracuseStep 3978665 = 2983999) B2983999
theorem B27235835 : Blo 1768085 27235835 := bstep (se 1 (by rfl) ⟨20426876, by rfl⟩ : syracuseStep 27235835 = 40853753) B40853753
theorem B7656959 : Blo 1768085 7656959 := bstep (se 1 (by rfl) ⟨5742719, by rfl⟩ : syracuseStep 7656959 = 11485439) B11485439
theorem B8951795 : Blo 1768085 8951795 := bstep (se 1 (by rfl) ⟨6713846, by rfl⟩ : syracuseStep 8951795 = 13427693) B13427693
theorem B2652251 : Blo 1768085 2652251 := bstep (se 1 (by rfl) ⟨1989188, by rfl⟩ : syracuseStep 2652251 = 3978377) B3978377
theorem B4036799 : Blo 1768085 4036799 := bstep (se 1 (by rfl) ⟨3027599, by rfl⟩ : syracuseStep 4036799 = 6055199) B6055199
theorem B2653487 : Blo 1768085 2653487 := bstep (se 1 (by rfl) ⟨1990115, by rfl⟩ : syracuseStep 2653487 = 3980231) B3980231
theorem B1769243 : Blo 1768085 1769243 := bstep (se 1 (by rfl) ⟨1326932, by rfl⟩ : syracuseStep 1769243 = 2653865) B2653865
theorem B2654315 : Blo 1768085 2654315 := bstep (se 1 (by rfl) ⟨1990736, by rfl⟩ : syracuseStep 2654315 = 3981473) B3981473
theorem B1769583 : Blo 1768085 1769583 := bstep (se 1 (by rfl) ⟨1327187, by rfl⟩ : syracuseStep 1769583 = 2654375) B2654375
theorem B2654543 : Blo 1768085 2654543 := bstep (se 1 (by rfl) ⟨1990907, by rfl⟩ : syracuseStep 2654543 = 3981815) B3981815
theorem B155042207 : Blo 1768085 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B2654207 : Blo 1768085 2654207 := bstep (se 1 (by rfl) ⟨1990655, by rfl⟩ : syracuseStep 2654207 = 3981311) B3981311
theorem B5104639 : Blo 1768085 5104639 := bstep (se 1 (by rfl) ⟨3828479, by rfl⟩ : syracuseStep 5104639 = 7656959) B7656959
theorem B18157223 : Blo 1768085 18157223 := bstep (se 1 (by rfl) ⟨13617917, by rfl⟩ : syracuseStep 18157223 = 27235835) B27235835
theorem B5967863 : Blo 1768085 5967863 := bstep (se 1 (by rfl) ⟨4475897, by rfl⟩ : syracuseStep 5967863 = 8951795) B8951795
theorem B2691199 : Blo 1768085 2691199 := bstep (se 1 (by rfl) ⟨2018399, by rfl⟩ : syracuseStep 2691199 = 4036799) B4036799
theorem B2652191 : Blo 1768085 2652191 := bstep (se 1 (by rfl) ⟨1989143, by rfl⟩ : syracuseStep 2652191 = 3978287) B3978287
theorem B13433039 : Blo 1768085 13433039 := bstep (se 1 (by rfl) ⟨10074779, by rfl⟩ : syracuseStep 13433039 = 20149559) B20149559
theorem B2652443 : Blo 1768085 2652443 := bstep (se 1 (by rfl) ⟨1989332, by rfl⟩ : syracuseStep 2652443 = 3978665) B3978665
theorem B1768167 : Blo 1768085 1768167 := bstep (se 1 (by rfl) ⟨1326125, by rfl⟩ : syracuseStep 1768167 = 2652251) B2652251
theorem B1768991 : Blo 1768085 1768991 := bstep (se 1 (by rfl) ⟨1326743, by rfl⟩ : syracuseStep 1768991 = 2653487) B2653487
theorem B3980969 : Blo 1768085 3980969 := bstep (se 2 (by rfl) ⟨1492863, by rfl⟩ : syracuseStep 3980969 = 2985727) B2985727
theorem B1769543 : Blo 1768085 1769543 := bstep (se 1 (by rfl) ⟨1327157, by rfl⟩ : syracuseStep 1769543 = 2654315) B2654315
theorem B1769695 : Blo 1768085 1769695 := bstep (se 1 (by rfl) ⟨1327271, by rfl⟩ : syracuseStep 1769695 = 2654543) B2654543
theorem B8955359 : Blo 1768085 8955359 := bstep (se 1 (by rfl) ⟨6716519, by rfl⟩ : syracuseStep 8955359 = 13433039) B13433039
theorem B27224741 : Blo 1768085 27224741 := bstep (se 4 (by rfl) ⟨2552319, by rfl⟩ : syracuseStep 27224741 = 5104639) B5104639
theorem B103361471 : Blo 1768085 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B12104815 : Blo 1768085 12104815 := bstep (se 1 (by rfl) ⟨9078611, by rfl⟩ : syracuseStep 12104815 = 18157223) B18157223
theorem B3978575 : Blo 1768085 3978575 := bstep (se 1 (by rfl) ⟨2983931, by rfl⟩ : syracuseStep 3978575 = 5967863) B5967863
theorem B3588265 : Blo 1768085 3588265 := bstep (se 2 (by rfl) ⟨1345599, by rfl⟩ : syracuseStep 3588265 = 2691199) B2691199
theorem B1768127 : Blo 1768085 1768127 := bstep (se 1 (by rfl) ⟨1326095, by rfl⟩ : syracuseStep 1768127 = 2652191) B2652191
theorem B1768295 : Blo 1768085 1768295 := bstep (se 1 (by rfl) ⟨1326221, by rfl⟩ : syracuseStep 1768295 = 2652443) B2652443
theorem B2653979 : Blo 1768085 2653979 := bstep (se 1 (by rfl) ⟨1990484, by rfl⟩ : syracuseStep 2653979 = 3980969) B3980969
theorem B1769471 : Blo 1768085 1769471 := bstep (se 1 (by rfl) ⟨1327103, by rfl⟩ : syracuseStep 1769471 = 2654207) B2654207
theorem B4784353 : Blo 1768085 4784353 := bstep (se 2 (by rfl) ⟨1794132, by rfl⟩ : syracuseStep 4784353 = 3588265) B3588265
theorem B16139753 : Blo 1768085 16139753 := bstep (se 2 (by rfl) ⟨6052407, by rfl⟩ : syracuseStep 16139753 = 12104815) B12104815
theorem B18149827 : Blo 1768085 18149827 := bstep (se 1 (by rfl) ⟨13612370, by rfl⟩ : syracuseStep 18149827 = 27224741) B27224741
theorem B68907647 : Blo 1768085 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B2652383 : Blo 1768085 2652383 := bstep (se 1 (by rfl) ⟨1989287, by rfl⟩ : syracuseStep 2652383 = 3978575) B3978575
theorem B5970239 : Blo 1768085 5970239 := bstep (se 1 (by rfl) ⟨4477679, by rfl⟩ : syracuseStep 5970239 = 8955359) B8955359
theorem B1769319 : Blo 1768085 1769319 := bstep (se 1 (by rfl) ⟨1326989, by rfl⟩ : syracuseStep 1769319 = 2653979) B2653979
theorem B24199769 : Blo 1768085 24199769 := bstep (se 2 (by rfl) ⟨9074913, by rfl⟩ : syracuseStep 24199769 = 18149827) B18149827
theorem B10759835 : Blo 1768085 10759835 := bstep (se 1 (by rfl) ⟨8069876, by rfl⟩ : syracuseStep 10759835 = 16139753) B16139753
theorem B45938431 : Blo 1768085 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B25516549 : Blo 1768085 25516549 := bstep (se 4 (by rfl) ⟨2392176, by rfl⟩ : syracuseStep 25516549 = 4784353) B4784353
theorem B1768255 : Blo 1768085 1768255 := bstep (se 1 (by rfl) ⟨1326191, by rfl⟩ : syracuseStep 1768255 = 2652383) B2652383
theorem B3980159 : Blo 1768085 3980159 := bstep (se 1 (by rfl) ⟨2985119, by rfl⟩ : syracuseStep 3980159 = 5970239) B5970239
theorem B34022065 : Blo 1768085 34022065 := bstep (se 2 (by rfl) ⟨12758274, by rfl⟩ : syracuseStep 34022065 = 25516549) B25516549
theorem B16133179 : Blo 1768085 16133179 := bstep (se 1 (by rfl) ⟨12099884, by rfl⟩ : syracuseStep 16133179 = 24199769) B24199769
theorem B28692893 : Blo 1768085 28692893 := bstep (se 3 (by rfl) ⟨5379917, by rfl⟩ : syracuseStep 28692893 = 10759835) B10759835
theorem B2653439 : Blo 1768085 2653439 := bstep (se 1 (by rfl) ⟨1990079, by rfl⟩ : syracuseStep 2653439 = 3980159) B3980159
theorem B61251241 : Blo 1768085 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B19128595 : Blo 1768085 19128595 := bstep (se 1 (by rfl) ⟨14346446, by rfl⟩ : syracuseStep 19128595 = 28692893) B28692893
theorem B81668321 : Blo 1768085 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B45362753 : Blo 1768085 45362753 := bstep (se 2 (by rfl) ⟨17011032, by rfl⟩ : syracuseStep 45362753 = 34022065) B34022065
theorem B21510905 : Blo 1768085 21510905 := bstep (se 2 (by rfl) ⟨8066589, by rfl⟩ : syracuseStep 21510905 = 16133179) B16133179
theorem B1768959 : Blo 1768085 1768959 := bstep (se 1 (by rfl) ⟨1326719, by rfl⟩ : syracuseStep 1768959 = 2653439) B2653439
theorem B54445547 : Blo 1768085 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B57362413 : Blo 1768085 57362413 := bstep (se 3 (by rfl) ⟨10755452, by rfl⟩ : syracuseStep 57362413 = 21510905) B21510905
theorem B25504793 : Blo 1768085 25504793 := bstep (se 2 (by rfl) ⟨9564297, by rfl⟩ : syracuseStep 25504793 = 19128595) B19128595
theorem B30241835 : Blo 1768085 30241835 := bstep (se 1 (by rfl) ⟨22681376, by rfl⟩ : syracuseStep 30241835 = 45362753) B45362753
theorem B20161223 : Blo 1768085 20161223 := bstep (se 1 (by rfl) ⟨15120917, by rfl⟩ : syracuseStep 20161223 = 30241835) B30241835
theorem B76483217 : Blo 1768085 76483217 := bstep (se 2 (by rfl) ⟨28681206, by rfl⟩ : syracuseStep 76483217 = 57362413) B57362413
theorem B17003195 : Blo 1768085 17003195 := bstep (se 1 (by rfl) ⟨12752396, by rfl⟩ : syracuseStep 17003195 = 25504793) B25504793
theorem B36297031 : Blo 1768085 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B50988811 : Blo 1768085 50988811 := bstep (se 1 (by rfl) ⟨38241608, by rfl⟩ : syracuseStep 50988811 = 76483217) B76483217
theorem B48396041 : Blo 1768085 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B11335463 : Blo 1768085 11335463 := bstep (se 1 (by rfl) ⟨8501597, by rfl⟩ : syracuseStep 11335463 = 17003195) B17003195
theorem B13440815 : Blo 1768085 13440815 := bstep (se 1 (by rfl) ⟨10080611, by rfl⟩ : syracuseStep 13440815 = 20161223) B20161223
theorem B32264027 : Blo 1768085 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B7556975 : Blo 1768085 7556975 := bstep (se 1 (by rfl) ⟨5667731, by rfl⟩ : syracuseStep 7556975 = 11335463) B11335463
theorem B8960543 : Blo 1768085 8960543 := bstep (se 1 (by rfl) ⟨6720407, by rfl⟩ : syracuseStep 8960543 = 13440815) B13440815
theorem B67985081 : Blo 1768085 67985081 := bstep (se 2 (by rfl) ⟨25494405, by rfl⟩ : syracuseStep 67985081 = 50988811) B50988811
theorem B5973695 : Blo 1768085 5973695 := bstep (se 1 (by rfl) ⟨4480271, by rfl⟩ : syracuseStep 5973695 = 8960543) B8960543
theorem B45323387 : Blo 1768085 45323387 := bstep (se 1 (by rfl) ⟨33992540, by rfl⟩ : syracuseStep 45323387 = 67985081) B67985081
theorem B21509351 : Blo 1768085 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B5037983 : Blo 1768085 5037983 := bstep (se 1 (by rfl) ⟨3778487, by rfl⟩ : syracuseStep 5037983 = 7556975) B7556975
theorem B3982463 : Blo 1768085 3982463 := bstep (se 1 (by rfl) ⟨2986847, by rfl⟩ : syracuseStep 3982463 = 5973695) B5973695
theorem B30215591 : Blo 1768085 30215591 := bstep (se 1 (by rfl) ⟨22661693, by rfl⟩ : syracuseStep 30215591 = 45323387) B45323387
theorem B14339567 : Blo 1768085 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B3358655 : Blo 1768085 3358655 := bstep (se 1 (by rfl) ⟨2518991, by rfl⟩ : syracuseStep 3358655 = 5037983) B5037983
theorem B2654975 : Blo 1768085 2654975 := bstep (se 1 (by rfl) ⟨1991231, by rfl⟩ : syracuseStep 2654975 = 3982463) B3982463
theorem B2239103 : Blo 1768085 2239103 := bstep (se 1 (by rfl) ⟨1679327, by rfl⟩ : syracuseStep 2239103 = 3358655) B3358655
theorem B20143727 : Blo 1768085 20143727 := bstep (se 1 (by rfl) ⟨15107795, by rfl⟩ : syracuseStep 20143727 = 30215591) B30215591
theorem B9559711 : Blo 1768085 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B1769983 : Blo 1768085 1769983 := bstep (se 1 (by rfl) ⟨1327487, by rfl⟩ : syracuseStep 1769983 = 2654975) B2654975
theorem B13429151 : Blo 1768085 13429151 := bstep (se 1 (by rfl) ⟨10071863, by rfl⟩ : syracuseStep 13429151 = 20143727) B20143727
theorem B5970941 : Blo 1768085 5970941 := bstep (se 3 (by rfl) ⟨1119551, by rfl⟩ : syracuseStep 5970941 = 2239103) B2239103
theorem B12746281 : Blo 1768085 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B16995041 : Blo 1768085 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B8952767 : Blo 1768085 8952767 := bstep (se 1 (by rfl) ⟨6714575, by rfl⟩ : syracuseStep 8952767 = 13429151) B13429151
theorem B3980627 : Blo 1768085 3980627 := bstep (se 1 (by rfl) ⟨2985470, by rfl⟩ : syracuseStep 3980627 = 5970941) B5970941
theorem B11330027 : Blo 1768085 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B5968511 : Blo 1768085 5968511 := bstep (se 1 (by rfl) ⟨4476383, by rfl⟩ : syracuseStep 5968511 = 8952767) B8952767
theorem B2653751 : Blo 1768085 2653751 := bstep (se 1 (by rfl) ⟨1990313, by rfl⟩ : syracuseStep 2653751 = 3980627) B3980627
theorem B7553351 : Blo 1768085 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B3979007 : Blo 1768085 3979007 := bstep (se 1 (by rfl) ⟨2984255, by rfl⟩ : syracuseStep 3979007 = 5968511) B5968511
theorem B1769167 : Blo 1768085 1769167 := bstep (se 1 (by rfl) ⟨1326875, by rfl⟩ : syracuseStep 1769167 = 2653751) B2653751
theorem B20142269 : Blo 1768085 20142269 := bstep (se 3 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 20142269 = 7553351) B7553351
theorem B2652671 : Blo 1768085 2652671 := bstep (se 1 (by rfl) ⟨1989503, by rfl⟩ : syracuseStep 2652671 = 3979007) B3979007
theorem B13428179 : Blo 1768085 13428179 := bstep (se 1 (by rfl) ⟨10071134, by rfl⟩ : syracuseStep 13428179 = 20142269) B20142269
theorem B1768447 : Blo 1768085 1768447 := bstep (se 1 (by rfl) ⟨1326335, by rfl⟩ : syracuseStep 1768447 = 2652671) B2652671
theorem B8952119 : Blo 1768085 8952119 := bstep (se 1 (by rfl) ⟨6714089, by rfl⟩ : syracuseStep 8952119 = 13428179) B13428179
theorem B5968079 : Blo 1768085 5968079 := bstep (se 1 (by rfl) ⟨4476059, by rfl⟩ : syracuseStep 5968079 = 8952119) B8952119
theorem B3978719 : Blo 1768085 3978719 := bstep (se 1 (by rfl) ⟨2984039, by rfl⟩ : syracuseStep 3978719 = 5968079) B5968079
theorem B2652479 : Blo 1768085 2652479 := bstep (se 1 (by rfl) ⟨1989359, by rfl⟩ : syracuseStep 2652479 = 3978719) B3978719
theorem B1768319 : Blo 1768085 1768319 := bstep (se 1 (by rfl) ⟨1326239, by rfl⟩ : syracuseStep 1768319 = 2652479) B2652479

theorem C0 (j : ℕ) (h1 : 442021 ≤ j) (h2 : j ≤ 442520) : Blo 1768085 (4 * j + 3) := by
  interval_cases j
  · exact B1768087
  · exact B1768091
  · exact B1768095
  · exact B1768099
  · exact B1768103
  · exact B1768107
  · exact B1768111
  · exact B1768115
  · exact B1768119
  · exact B1768123
  · exact B1768127
  · exact B1768131
  · exact B1768135
  · exact B1768139
  · exact B1768143
  · exact B1768147
  · exact B1768151
  · exact B1768155
  · exact B1768159
  · exact B1768163
  · exact B1768167
  · exact B1768171
  · exact B1768175
  · exact B1768179
  · exact B1768183
  · exact B1768187
  · exact B1768191
  · exact B1768195
  · exact B1768199
  · exact B1768203
  · exact B1768207
  · exact B1768211
  · exact B1768215
  · exact B1768219
  · exact B1768223
  · exact B1768227
  · exact B1768231
  · exact B1768235
  · exact B1768239
  · exact B1768243
  · exact B1768247
  · exact B1768251
  · exact B1768255
  · exact B1768259
  · exact B1768263
  · exact B1768267
  · exact B1768271
  · exact B1768275
  · exact B1768279
  · exact B1768283
  · exact B1768287
  · exact B1768291
  · exact B1768295
  · exact B1768299
  · exact B1768303
  · exact B1768307
  · exact B1768311
  · exact B1768315
  · exact B1768319
  · exact B1768323
  · exact B1768327
  · exact B1768331
  · exact B1768335
  · exact B1768339
  · exact B1768343
  · exact B1768347
  · exact B1768351
  · exact B1768355
  · exact B1768359
  · exact B1768363
  · exact B1768367
  · exact B1768371
  · exact B1768375
  · exact B1768379
  · exact B1768383
  · exact B1768387
  · exact B1768391
  · exact B1768395
  · exact B1768399
  · exact B1768403
  · exact B1768407
  · exact B1768411
  · exact B1768415
  · exact B1768419
  · exact B1768423
  · exact B1768427
  · exact B1768431
  · exact B1768435
  · exact B1768439
  · exact B1768443
  · exact B1768447
  · exact B1768451
  · exact B1768455
  · exact B1768459
  · exact B1768463
  · exact B1768467
  · exact B1768471
  · exact B1768475
  · exact B1768479
  · exact B1768483
  · exact B1768487
  · exact B1768491
  · exact B1768495
  · exact B1768499
  · exact B1768503
  · exact B1768507
  · exact B1768511
  · exact B1768515
  · exact B1768519
  · exact B1768523
  · exact B1768527
  · exact B1768531
  · exact B1768535
  · exact B1768539
  · exact B1768543
  · exact B1768547
  · exact B1768551
  · exact B1768555
  · exact B1768559
  · exact B1768563
  · exact B1768567
  · exact B1768571
  · exact B1768575
  · exact B1768579
  · exact B1768583
  · exact B1768587
  · exact B1768591
  · exact B1768595
  · exact B1768599
  · exact B1768603
  · exact B1768607
  · exact B1768611
  · exact B1768615
  · exact B1768619
  · exact B1768623
  · exact B1768627
  · exact B1768631
  · exact B1768635
  · exact B1768639
  · exact B1768643
  · exact B1768647
  · exact B1768651
  · exact B1768655
  · exact B1768659
  · exact B1768663
  · exact B1768667
  · exact B1768671
  · exact B1768675
  · exact B1768679
  · exact B1768683
  · exact B1768687
  · exact B1768691
  · exact B1768695
  · exact B1768699
  · exact B1768703
  · exact B1768707
  · exact B1768711
  · exact B1768715
  · exact B1768719
  · exact B1768723
  · exact B1768727
  · exact B1768731
  · exact B1768735
  · exact B1768739
  · exact B1768743
  · exact B1768747
  · exact B1768751
  · exact B1768755
  · exact B1768759
  · exact B1768763
  · exact B1768767
  · exact B1768771
  · exact B1768775
  · exact B1768779
  · exact B1768783
  · exact B1768787
  · exact B1768791
  · exact B1768795
  · exact B1768799
  · exact B1768803
  · exact B1768807
  · exact B1768811
  · exact B1768815
  · exact B1768819
  · exact B1768823
  · exact B1768827
  · exact B1768831
  · exact B1768835
  · exact B1768839
  · exact B1768843
  · exact B1768847
  · exact B1768851
  · exact B1768855
  · exact B1768859
  · exact B1768863
  · exact B1768867
  · exact B1768871
  · exact B1768875
  · exact B1768879
  · exact B1768883
  · exact B1768887
  · exact B1768891
  · exact B1768895
  · exact B1768899
  · exact B1768903
  · exact B1768907
  · exact B1768911
  · exact B1768915
  · exact B1768919
  · exact B1768923
  · exact B1768927
  · exact B1768931
  · exact B1768935
  · exact B1768939
  · exact B1768943
  · exact B1768947
  · exact B1768951
  · exact B1768955
  · exact B1768959
  · exact B1768963
  · exact B1768967
  · exact B1768971
  · exact B1768975
  · exact B1768979
  · exact B1768983
  · exact B1768987
  · exact B1768991
  · exact B1768995
  · exact B1768999
  · exact B1769003
  · exact B1769007
  · exact B1769011
  · exact B1769015
  · exact B1769019
  · exact B1769023
  · exact B1769027
  · exact B1769031
  · exact B1769035
  · exact B1769039
  · exact B1769043
  · exact B1769047
  · exact B1769051
  · exact B1769055
  · exact B1769059
  · exact B1769063
  · exact B1769067
  · exact B1769071
  · exact B1769075
  · exact B1769079
  · exact B1769083
  · exact B1769087
  · exact B1769091
  · exact B1769095
  · exact B1769099
  · exact B1769103
  · exact B1769107
  · exact B1769111
  · exact B1769115
  · exact B1769119
  · exact B1769123
  · exact B1769127
  · exact B1769131
  · exact B1769135
  · exact B1769139
  · exact B1769143
  · exact B1769147
  · exact B1769151
  · exact B1769155
  · exact B1769159
  · exact B1769163
  · exact B1769167
  · exact B1769171
  · exact B1769175
  · exact B1769179
  · exact B1769183
  · exact B1769187
  · exact B1769191
  · exact B1769195
  · exact B1769199
  · exact B1769203
  · exact B1769207
  · exact B1769211
  · exact B1769215
  · exact B1769219
  · exact B1769223
  · exact B1769227
  · exact B1769231
  · exact B1769235
  · exact B1769239
  · exact B1769243
  · exact B1769247
  · exact B1769251
  · exact B1769255
  · exact B1769259
  · exact B1769263
  · exact B1769267
  · exact B1769271
  · exact B1769275
  · exact B1769279
  · exact B1769283
  · exact B1769287
  · exact B1769291
  · exact B1769295
  · exact B1769299
  · exact B1769303
  · exact B1769307
  · exact B1769311
  · exact B1769315
  · exact B1769319
  · exact B1769323
  · exact B1769327
  · exact B1769331
  · exact B1769335
  · exact B1769339
  · exact B1769343
  · exact B1769347
  · exact B1769351
  · exact B1769355
  · exact B1769359
  · exact B1769363
  · exact B1769367
  · exact B1769371
  · exact B1769375
  · exact B1769379
  · exact B1769383
  · exact B1769387
  · exact B1769391
  · exact B1769395
  · exact B1769399
  · exact B1769403
  · exact B1769407
  · exact B1769411
  · exact B1769415
  · exact B1769419
  · exact B1769423
  · exact B1769427
  · exact B1769431
  · exact B1769435
  · exact B1769439
  · exact B1769443
  · exact B1769447
  · exact B1769451
  · exact B1769455
  · exact B1769459
  · exact B1769463
  · exact B1769467
  · exact B1769471
  · exact B1769475
  · exact B1769479
  · exact B1769483
  · exact B1769487
  · exact B1769491
  · exact B1769495
  · exact B1769499
  · exact B1769503
  · exact B1769507
  · exact B1769511
  · exact B1769515
  · exact B1769519
  · exact B1769523
  · exact B1769527
  · exact B1769531
  · exact B1769535
  · exact B1769539
  · exact B1769543
  · exact B1769547
  · exact B1769551
  · exact B1769555
  · exact B1769559
  · exact B1769563
  · exact B1769567
  · exact B1769571
  · exact B1769575
  · exact B1769579
  · exact B1769583
  · exact B1769587
  · exact B1769591
  · exact B1769595
  · exact B1769599
  · exact B1769603
  · exact B1769607
  · exact B1769611
  · exact B1769615
  · exact B1769619
  · exact B1769623
  · exact B1769627
  · exact B1769631
  · exact B1769635
  · exact B1769639
  · exact B1769643
  · exact B1769647
  · exact B1769651
  · exact B1769655
  · exact B1769659
  · exact B1769663
  · exact B1769667
  · exact B1769671
  · exact B1769675
  · exact B1769679
  · exact B1769683
  · exact B1769687
  · exact B1769691
  · exact B1769695
  · exact B1769699
  · exact B1769703
  · exact B1769707
  · exact B1769711
  · exact B1769715
  · exact B1769719
  · exact B1769723
  · exact B1769727
  · exact B1769731
  · exact B1769735
  · exact B1769739
  · exact B1769743
  · exact B1769747
  · exact B1769751
  · exact B1769755
  · exact B1769759
  · exact B1769763
  · exact B1769767
  · exact B1769771
  · exact B1769775
  · exact B1769779
  · exact B1769783
  · exact B1769787
  · exact B1769791
  · exact B1769795
  · exact B1769799
  · exact B1769803
  · exact B1769807
  · exact B1769811
  · exact B1769815
  · exact B1769819
  · exact B1769823
  · exact B1769827
  · exact B1769831
  · exact B1769835
  · exact B1769839
  · exact B1769843
  · exact B1769847
  · exact B1769851
  · exact B1769855
  · exact B1769859
  · exact B1769863
  · exact B1769867
  · exact B1769871
  · exact B1769875
  · exact B1769879
  · exact B1769883
  · exact B1769887
  · exact B1769891
  · exact B1769895
  · exact B1769899
  · exact B1769903
  · exact B1769907
  · exact B1769911
  · exact B1769915
  · exact B1769919
  · exact B1769923
  · exact B1769927
  · exact B1769931
  · exact B1769935
  · exact B1769939
  · exact B1769943
  · exact B1769947
  · exact B1769951
  · exact B1769955
  · exact B1769959
  · exact B1769963
  · exact B1769967
  · exact B1769971
  · exact B1769975
  · exact B1769979
  · exact B1769983
  · exact B1769987
  · exact B1769991
  · exact B1769995
  · exact B1769999
  · exact B1770003
  · exact B1770007
  · exact B1770011
  · exact B1770015
  · exact B1770019
  · exact B1770023
  · exact B1770027
  · exact B1770031
  · exact B1770035
  · exact B1770039
  · exact B1770043
  · exact B1770047
  · exact B1770051
  · exact B1770055
  · exact B1770059
  · exact B1770063
  · exact B1770067
  · exact B1770071
  · exact B1770075
  · exact B1770079
  · exact B1770083

theorem solution (m : ℕ) (hlo : 1768085 ≤ m) (hhi : m ≤ 1770085) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 442021 ≤ j := by omega
    have hj2 : j ≤ 442520 := by omega
    have hb : Blo 1768085 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
